/*
 * Copyright 2008 The Closure Compiler Authors.
 * 
 * Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 * in compliance with the License. You may obtain a copy of the License at
 * 
 * http://www.apache.org/licenses/LICENSE-2.0
 * 
 * Unless required by applicable law or agreed to in writing, software distributed under the License
 * is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
 * or implied. See the License for the specific language governing permissions and limitations under
 * the License.
 */

package com.google.javascript.jscomp;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

import com.google.common.base.MoreObjects;
import com.google.common.base.MoreObjects.ToStringHelper;
import com.google.common.base.Optional;
import com.google.common.collect.Ordering;
import com.google.javascript.jscomp.CodingConvention.SubclassRelationship;
import com.google.javascript.jscomp.NodeTraversal.Callback;
import com.google.javascript.rhino.IR;
import com.google.javascript.rhino.Node;
import com.google.javascript.rhino.Token;
import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;
import java.util.logging.Logger;

/**
 * A {@link Compiler} pass for moving code to a deeper module if possible.
 * 
 * <p>
 * A "definition" for "Foo" includes all of the following kinds of statements. <code><pre>
 * function F() {}
 * F.prototype.foo = function() {};
 * goog.inherits(F, BaseClass);
 * </pre></code>
 * 
 * <p>
 * The basic algorithm, ignoring some details is this:
 * 
 * <ol>
 * <li>Traverse the AST once recording:
 * <ul>
 * <li>The location of all global-value defining statements.
 * <li>The global name references that are contained in those definitions.
 * <li>The global name references that follow, and thus depend on, the definitions. NOTE: This will
 * make later definitions depend on earlier ones, which ensures they will be kept in order.
 * </ul>
 * <li>Iterate over a set of all the definitions.
 * <ul>
 * <li>If the definition is safely movable, find the deepest common module for all of the references
 * that depend on it.
 * <li>If such a module exists and also depends on the module the definition is currently in, move
 * the definition to the beginning of the deeper module.
 * <li>If the definition moved,
 * <ul>
 * <li>Update the modules recorded for all of the references it contains.
 * <li>Add definitions those references refer to to the end of the list/set we're iterating over, so
 * we'll try to move it again later.
 * </ul>
 * </ul>
 * </ol>
 * 
 * This algorithm will complete all possible moves in O(n) time where n is the number of global
 * definitions.
 */
class CrossModuleCodeMotion implements CompilerPass {

  private static final Logger logger = Logger.getLogger(CrossModuleCodeMotion.class.getName());

  private final AbstractCompiler compiler;
  private final JSModuleGraph graph;
  private final boolean parentModuleCanSeeSymbolsDeclaredInChildren;

  private static int runNumber = 0;

  /**
   * Creates an instance.
   * 
   * @param compiler The compiler
   */
  CrossModuleCodeMotion(AbstractCompiler compiler, JSModuleGraph graph,
      boolean parentModuleCanSeeSymbolsDeclaredInChildren) {
    this.compiler = compiler;
    this.graph = graph;
    this.parentModuleCanSeeSymbolsDeclaredInChildren = parentModuleCanSeeSymbolsDeclaredInChildren;
  }

  @Override
  public void process(Node externs, Node root) {
    logger.fine("Moving functions + variable into deeper modules");

    // If there are <2 modules, then we will never move anything, so we're done
    if (graph != null && graph.getModuleCount() > 1) {
      moveDefinitionsAsDeepAsPossible(root);
    }
  }

  private void moveDefinitionsAsDeepAsPossible(Node root) {
    System.out.println(String.format("==== CrossModuleCodeMotion Run # %s ====", runNumber++));
    DefinitionMoverFactory definitionMoverFactory = new DefinitionMoverFactory();
    DefinitionMover definitionMover = definitionMoverFactory.createDefinitionMover(root);
    System.out.println("==> Trying to move code");
    long movesMade = definitionMover.moveDefinitionsAsDeepAsPossible();
    System.out.println("==> Asserting no code can move further with new mover");
  }

  private final class UnexpectedMoveMessage {
    private final Optional<PossibleMove> move;
    private final DefinitionMover oldMover;

    UnexpectedMoveMessage(DefinitionMover oldMover, Optional<PossibleMove> move) {
      this.oldMover = oldMover;
      this.move = move;
    }

    @Override
    public String toString() {
      Definition definition = move.get().definition;
      Definition oldDefinition =
          oldMover.findDefinitionForNode(definition.varName, definition.definitionNode);
      return String.format("Found move after retraversal: %s\nold definition was: %s", move.get(),
          oldDefinition);
    }
  }

  /** Moves definitions into the deepest possible modules. */
  private final class DefinitionMover {
    final Set<Definition> movableDefinitions;
    final Map<JSModule, ModuleRecord> moduleRecordMap;
    final Map<String, SortedSet<Definition>> definitionsForName;
    final Deque<ModuleRecord> moduleRecords;

    long movesMade = 0;

    DefinitionMover(Set<Definition> movableDefinitions,
        Map<String, SortedSet<Definition>> definitionsForName,
        Map<JSModule, ModuleRecord> moduleRecordMap, Deque<ModuleRecord> moduleRecords) {
      this.movableDefinitions = movableDefinitions;
      this.definitionsForName = definitionsForName;
      this.moduleRecordMap = moduleRecordMap;
      this.moduleRecords = moduleRecords;
    }

    long moveDefinitionsAsDeepAsPossible() {
      boolean useOldWay = false;
      if (useOldWay) {
        SortedSet<PossibleMove> possibleMoves = new TreeSet<>(DEEPEST_MOVE_FIRST);
        Map<Definition, PossibleMove> moveForDefinition = new HashMap<>();
        for (Definition d : movableDefinitions) {
          Optional<PossibleMove> possibleMove = findPossibleMove(d);
          if (possibleMove.isPresent()) {
            possibleMoves.add(possibleMove.get());
            moveForDefinition.put(d, possibleMove.get());
          }
        }
        while (!possibleMoves.isEmpty()) {
          PossibleMove move = possibleMoves.first();
          possibleMoves.remove(move);
          final PossibleMove removedMove = moveForDefinition.remove(move.definition);
          checkState(move.equals(removedMove), "Expected %s got %s", move, removedMove);
          Set<Definition> definitionsToReconsider =
              moveDefinition(move.definition, move.destination);
          compiler.reportCodeChange();
          for (Definition d : definitionsToReconsider) {
            if (moveForDefinition.containsKey(d)) {
              PossibleMove knownMove = moveForDefinition.get(d);
              Optional<PossibleMove> optBetterMove = findPossibleMove(d);
              checkState(optBetterMove.isPresent(),
                  "After move %s failed to find already known good move: %s", move, knownMove);
              PossibleMove betterMove = optBetterMove.get();
              if (betterMove.destination.isDeeperThan(knownMove.destination)) {
                possibleMoves.remove(knownMove);
                possibleMoves.add(betterMove);
                moveForDefinition.put(d, betterMove);
              } else {
                checkState(betterMove.equals(knownMove),
                    "After move %s better move %s is actually worse than %s", move, betterMove,
                    knownMove);
              }
            } else {
              Optional<PossibleMove> optNewMove = findPossibleMove(d);
              if (optNewMove.isPresent()) {
                PossibleMove newMove = optNewMove.get();
                possibleMoves.add(newMove);
                moveForDefinition.put(d, newMove);
              }
            }
          }
        }
      } else {
        Deque<ModuleSubtree> moduleSubtreeStack = buildModuleSubtreeStack(moduleRecords);
        for (ModuleSubtree subtree : moduleSubtreeStack) {
          pullRequiredDefinitionsDown(subtree);
        }
      }
      return movesMade;
    }

    private void pullRequiredDefinitionsDown(ModuleSubtree subtree) {
      checkState(subtree.requiredDefinitions.isEmpty(), "subtree considered multiple times: %s",
          subtree);
      for (ModuleSubtree child : subtree.children) {
        subtree.requiredDefinitions.addAll(child.requiredDefinitions);
      }
      subtree.requiredDefinitions.removeAll(subtree.head.getContainedDefinitions());
      SortedSet<Definition> definitionsToTry = new TreeSet<>(DEEPEST_DEFINITION_FIRST);
      for (Definition d : subtree.requiredDefinitions) {
        if (d.isMovable()) {
          definitionsToTry.add(d);
        }
      }
      definitionsToTry.addAll(subtree.requiredDefinitions);
      while (!definitionsToTry.isEmpty()) {
        final Definition d = definitionsToTry.first();
        definitionsToTry.remove(d);
        if (canPullDefinitionDown(subtree, d)) {
          pullDefinitionDown(subtree, d);
          for (Reference movedReference : d.statement.containedReferences) {
            if (movedReference.referencedDefinition.isPresent()) {
              // (Re)consider moving definitions whose dependent references have moved here.
              definitionsToTry.add(movedReference.referencedDefinition.get());
            }
          }
        }
      }
    }

    private boolean canPullDefinitionDown(ModuleSubtree subtree, Definition d) {
      if (!d.isMovable()) {
        return false;
      } else {
        for (Reference r : d.dependentsShallowestFirst) {
          ModuleRecord mr = r.statement.moduleRecord;
          if (!subtree.contains(mr)) {
            return false;
          }
        }
        return true;
      }
    }

    private void pullDefinitionDown(ModuleSubtree subtree, Definition definition) {
      guardPassedOverInstanceOfReferences(definition, subtree.head);
      // Move definition in the AST
      final Node newParent = compiler.getNodeForCodeInsertion(subtree.head.module);
      definition.definitionNode.detach();
      newParent.addChildToFront(definition.definitionNode);
      compiler.reportCodeChange();
      // Update statement's position in our model
      subtree.head.prependStatement(definition.statement);
      for (Reference r : definition.statement.containedReferences) {
        if (r.referencedDefinition.isPresent()) {
          Definition d = r.referencedDefinition.get();
          subtree.requiredDefinitions.add(d);
          d.dependentsShallowestFirst.remove(r);
          d.dependentsShallowestFirst.add(r);
        }
      }
      // Update all definitions
    }

    private Deque<ModuleSubtree> buildModuleSubtreeStack(Deque<ModuleRecord> moduleRecords) {
      final Deque<ModuleSubtree> moduleSubtreeStack = new ArrayDeque<>();
      final Map<String, ModuleSubtree> moduleNameToSubtree = new HashMap<>();
      for (ModuleRecord subtreeHead : moduleRecords) {
        final ModuleSubtree subtree = new ModuleSubtree(subtreeHead);
        moduleNameToSubtree.put(subtreeHead.module.getName(), subtree);
        moduleSubtreeStack.push(subtree);
        for (JSModule module : subtreeHead.module.getDependencies()) {
          ModuleSubtree parent = checkNotNull(moduleNameToSubtree.get(module.getName()));
          parent.children.add(subtree);
        }
      }
      for (ModuleSubtree subtree : moduleSubtreeStack) {
        for (ModuleSubtree child : subtree.children) {
          subtree.moduleRecords.add(child.head);
        }
        subtree.moduleRecords.add(subtree.head);
      }
      return moduleSubtreeStack;
    }

    Optional<PossibleMove> findPossibleMove(Definition definition) {
      checkState(definition.isMovable());

      final ModuleRecord currentModuleRecord = definition.getModuleRecord();
      // Find all modules that contain references to the definition,
      // possibly separating out some special cases we can ignore.
      Set<JSModule> modulesWithReferences = new HashSet<>();
      Set<ModuleRecord> dependentModules = new HashSet<>();
      for (Reference ref : definition.dependentsShallowestFirst) {
        final ModuleRecord refModuleRecord = ref.getModuleRecord();
        if (refModuleRecord.equals(currentModuleRecord)) {
          // We cannot find anything better if there's a reference in the current module.
          return Optional.<PossibleMove>absent();
        }
        dependentModules.add(refModuleRecord);
        modulesWithReferences.add(refModuleRecord.module);
      }

      if (modulesWithReferences.isEmpty()) {
        // No references found, so we have no way to choose a destination module.
        return Optional.<PossibleMove>absent();
      } else {
        JSModule newModule =
            checkNotNull(graph.getDeepestCommonDependencyInclusive(modulesWithReferences));
        if (newModule.getDepth() > currentModuleRecord.module.getDepth()) {
          final ModuleRecord betterModuleRecord = moduleRecordMap.get(newModule);
          checkState(definition.originalModuleRecord.equals(definition.getModuleRecord()),
              "Definition %s already moved, but better module found %s", definition,
              betterModuleRecord);
          return Optional.of(new PossibleMove(definition, betterModuleRecord, dependentModules));
        } else {
          return Optional.<PossibleMove>absent();
        }
      }
    }

    Optional<PossibleMove> findPossibleMove() {
      for (Definition d : movableDefinitions) {
        Optional<PossibleMove> possibleMove = findPossibleMove(d);
        if (possibleMove.isPresent()) {
          return possibleMove;
        }
      }
      return Optional.<PossibleMove>absent();
    }

    private Optional<ModuleRecord> findBetterModuleRecord(Definition definition) {
      checkState(definition.isMovable());

      final ModuleRecord currentModuleRecord = definition.getModuleRecord();
      // Find all modules that contain references to the definition,
      // possibly separating out some special cases we can ignore.
      Set<JSModule> modulesWithReferences = new HashSet<>();
      for (Reference ref : definition.dependentsShallowestFirst) {
        final ModuleRecord refModuleRecord = ref.getModuleRecord();
        if (refModuleRecord.equals(currentModuleRecord)) {
          // We cannot find anything better if there's a reference in the current module.
          return Optional.<ModuleRecord>absent();
        }
        modulesWithReferences.add(refModuleRecord.module);
      }

      if (modulesWithReferences.isEmpty()) {
        // No references found, so we have no way to choose a destination module.
        return Optional.<ModuleRecord>absent();
      } else {
        JSModule newModule =
            checkNotNull(graph.getDeepestCommonDependencyInclusive(modulesWithReferences));
        if (newModule.getDepth() > currentModuleRecord.module.getDepth()) {
          final ModuleRecord betterModuleRecord = moduleRecordMap.get(newModule);
          checkState(definition.originalModuleRecord.equals(definition.getModuleRecord()),
              "Definition %s already moved, but better module found %s", definition,
              betterModuleRecord);
          return Optional.of(betterModuleRecord);
        } else {
          return Optional.<ModuleRecord>absent();
        }
      }
    }

    /**
     * Moves a definition to a new module.
     * 
     * @param definition The definition to be moved.
     * @param dstModuleRecord Record for the module where we're putting it.
     * @return Set of definitions to reconsider after this move
     */
    private Set<Definition> moveDefinition(Definition definition, ModuleRecord dstModuleRecord) {
      JSModule newModule = dstModuleRecord.module;

      System.out.println(String.format("Moving %s to %s", definition, dstModuleRecord));
      // Add guards to any instanceof usages that will now be above the definition.
      guardPassedOverInstanceOfReferences(definition, dstModuleRecord);
      // Move definition in the AST
      final Node newParent = compiler.getNodeForCodeInsertion(newModule);
      definition.definitionNode.detach();
      newParent.addChildToFront(definition.definitionNode);

      final SortedSet<Definition> sortedDefinitions =
          checkNotNull(definitionsForName.get(definition.varName));
      sortedDefinitions.remove(definition);
      definition.statement.moduleRecord = dstModuleRecord;
      definition.statement.modulePositionIndex = dstModuleRecord.nextPrependStatementIndex--;
      sortedDefinitions.add(definition);

      // Update all the references contained in the moved definition.
      HashSet<Definition> definitionsToReconsider = new HashSet<>();
      for (Reference ref : definition.statement.containedReferences) {
        // Recalculate the definitions to which the moved references refer.
        // TODO: Explain why the recalculation is needed.
        Optional<Definition> oldDefinition = ref.referencedDefinition;
        Optional<Definition> newDefinition = findBestDefinitionForReference(ref);

        // Update definition dependents
        if (!oldDefinition.equals(newDefinition)) {
          ref.referencedDefinition = newDefinition;
          if (oldDefinition.isPresent()) {
            oldDefinition.get().dependentsShallowestFirst.remove(ref);
          }
          if (newDefinition.isPresent()) {
            newDefinition.get().dependentsShallowestFirst.add(ref);
          }
        }

        // Reconsider moving affected definitions.
        if (oldDefinition.isPresent() && oldDefinition.get().isMovable()) {
          definitionsToReconsider.add(oldDefinition.get());
        }
        if (newDefinition.isPresent() && newDefinition.get().isMovable()) {
          definitionsToReconsider.add(newDefinition.get());
        }
      }
      return definitionsToReconsider;
    }

    private void guardPassedOverInstanceOfReferences(Definition definition,
        ModuleRecord dstModuleRecord) {
      final Iterator<Reference> unguardedInstanceofIterator =
          definition.unguardedInstanceOfReferences.iterator();
      while (unguardedInstanceofIterator.hasNext()) {
        Reference instanceofReference = unguardedInstanceofIterator.next();
        if (!dependsOn(instanceofReference.getModuleRecord(), dstModuleRecord)) {
          addUndefinedTypeofGuard(instanceofReference.referenceNode);
          unguardedInstanceofIterator.remove();
        }
      }
    }

    private Optional<Definition> findBestDefinitionForReference(Reference ref) {
      String varName = ref.getVarName();
      for (Definition candidate : definitionsForName.get(varName)) {
        if (dependsOn(ref.getModuleRecord(), candidate.getModuleRecord())) {
          return Optional.of(candidate);
        } else if (ref.getModuleRecord().equals(candidate.getModuleRecord())
            && candidate.statement.isAbove(ref.statement)) {
          return Optional.of(candidate);
        }
      }
      return Optional.<Definition>absent();
    }

    Definition findDefinitionForNode(String varName, Node n) {
      Definition definition = null;
      for (Definition d : definitionsForName.get(varName)) {
        if (d.definitionNode == n) {
          definition = d;
          break;
        }
      }
      return checkNotNull(definition, "No definition found for %s: %s", varName, n);
    }
  }

  private static final class ModuleSubtree {
    final ModuleRecord head;
    final Set<ModuleSubtree> children = new HashSet<>();
    final Set<ModuleRecord> moduleRecords = new HashSet<>();
    final Set<Definition> requiredDefinitions = new HashSet<>();

    ModuleSubtree(ModuleRecord head) {
      this.head = head;
    }

    public boolean contains(ModuleRecord moduleRecord) {
      return moduleRecords.contains(moduleRecord);
    }
  }

  private final class PossibleMove {
    private final Definition definition;
    private final ModuleRecord destination;
    private final Set<ModuleRecord> dependentModules;

    PossibleMove(Definition definition, ModuleRecord destination, Set<ModuleRecord> dependentModules) {
      checkState(definition.isUnconditional());
      this.definition = definition;
      this.destination = destination;
      this.dependentModules = dependentModules;
    }

    @Override
    public boolean equals(Object o) {
      if (this == o) {
        return true;
      } else if (o == null || getClass() != o.getClass()) {
        return false;
      } else {
        PossibleMove other = (PossibleMove) o;
        return Objects.equals(definition, other.definition)
            && Objects.equals(destination, other.destination);
      }
    }

    @Override
    public int hashCode() {
      return Objects.hash(definition, destination);
    }

    @Override
    public String toString() {
      return MoreObjects.toStringHelper(this).add("definition", definition)
          .add("destination", destination).add("dependentModules", dependentModules).toString();
    }
  }

  private static final Ordering<PossibleMove> DEEPEST_MOVE_FIRST = new Ordering<PossibleMove>() {
    @Override
    public int compare(PossibleMove left, PossibleMove right) {
      checkNotNull(left);
      checkNotNull(right);
      if (left.equals(right)) {
        return 0;
      } else {
        checkState(!left.definition.equals(right.definition),
            "Comparing two different moves for the same definition:\n%s\n%s", left, right);
        // Deepest destination module first.
        int result = -left.destination.compareAbsoluteDepth(right.destination);
        if (result == 0) {
          checkState(left.destination.equals(right.destination),
              "Different ModuleRecords have the same absolute depth:\n%s\nand\n%s", left, right);
          // When moving 2 definitions to the same module, prefer to keep them in the same
          // absolute order by moving the deepest one first.
          result = -left.definition.compareAbsoluteDepth(right.definition);
        }
        return result;
      }
    }
  };

  private static final Ordering<Definition> DEEPEST_DEFINITION_FIRST = new Ordering<Definition>() {
    @Override
    public int compare(Definition left, Definition right) {
      checkNotNull(left);
      checkNotNull(right);
      if (left == right) {
        return 0;
      } else {
        checkState(left.definitionNode != right.definitionNode,
            "Two definitions refer to the same node: %s and %s", left, right);
        if (left.statement == right.statement) {
          // Two definitions on the same statement.
          // At least one of them must be conditional.
          checkState(!(right.isUnconditional() && left.isUnconditional()),
              "Two unconditional definitions in the same statement: %s and %s", left, right);
          // A statement containing any conditional definitions is immovable,
          // so it doesn't matter which one we consider to be deeper than the other.
          return 0;
        } else {
          final AbsoluteStatementDepth leftStatementDepth = left.statement.getAbsoluteDepth();
          final AbsoluteStatementDepth rightStatementDepth = right.statement.getAbsoluteDepth();
          // Invert comparison because we want deepest to come first.
          return -leftStatementDepth.compareTo(rightStatementDepth);
        }
      }
    }
  };

  private boolean isUndefinedTypeofGuardReference(Node reference) {
    Node typeofReference = reference.getParent();
    if (!typeofReference.isTypeOf()) {
      return false;
    }
    Node notEquals = typeofReference.getParent();
    if (!(notEquals.isNE() && notEquals.getLastChild() == typeofReference)) {
      return false;
    }
    Node undefinedString = notEquals.getFirstChild();
    if (!(undefinedString.isString() && undefinedString.getString().equals("undefined"))) {
      return false;
    }
    Node andNode = notEquals.getParent();
    if (!(andNode.isAnd() && andNode.getFirstChild() == notEquals)) {
      return false;
    }
    Node instanceofNode = andNode.getLastChild();
    if (!(instanceofNode.isInstanceOf())) {
      return false;
    }
    return reference.isEquivalentTo(instanceofNode.getLastChild());
  }

  private boolean isInstanceofReference(Node reference) {
    Node instanceofNode = reference.getParent();
    return instanceofNode.isInstanceOf() && instanceofNode.getLastChild() == reference;
  }

  private boolean hasUndefinedTypeofGuard(Node reference) {
    Node instanceofNode = reference.getParent();
    checkState(reference.isName() && instanceofNode.getLastChild() == reference);
    Node andNode = instanceofNode.getParent();
    if (!(andNode.isAnd() && andNode.getLastChild() == instanceofNode)) {
      return false;
    }
    Node neNode = andNode.getFirstChild();
    if (!neNode.isNE()) {
      return false;
    }
    Node undefinedNode = neNode.getFirstChild();
    if (!(undefinedNode.isString() && undefinedNode.getString().equals("undefined"))) {
      return false;
    }
    Node typeofNode = neNode.getLastChild();
    if (!typeofNode.isTypeOf()) {
      return false;
    }
    Node nameNode = typeofNode.getFirstChild();
    return nameNode.isEquivalentTo(reference);
  }

  private void addUndefinedTypeofGuard(Node reference) {
    checkState(isInstanceofReference(reference));
    Node instanceofNode = reference.getParent();
    Node typeofReference = new Node(Token.TYPEOF, reference.cloneNode());
    Node undefinedString = IR.string("undefined");
    Node undefinedNotEqualTypeOfReference = IR.ne(undefinedString, typeofReference);
    Node tmp = IR.trueNode();
    Node andNode = IR.and(undefinedNotEqualTypeOfReference, tmp);
    andNode.useSourceInfoFromForTree(instanceofNode);
    instanceofNode.replaceWith(andNode);
    tmp.replaceWith(instanceofNode);
  }

  private boolean dependsOn(ModuleRecord a, ModuleRecord b) {
    return graph.dependsOn(a.module, b.module);
  }

  /**
   * Traverses the AST gathering up all global definitions and references. Keeps track of which
   * references depend on which definitions based on both AST order and the module graph.
   */
  private final class DefinitionMoverFactory implements Callback {
    private int nextDefinitionIndex = 0;
    private ModuleRecord currentModuleRecord = null;
    private GlobalStatement currentStatement = null;
    private final Map<JSModule, ModuleRecord> moduleRecordMap = new HashMap<>();
    private final Deque<ModuleRecord> moduleRecords = new ArrayDeque<>();
    private final Map<String, SortedSet<Definition>> definitionsForName = new HashMap<>();
    // Stack of all definitions for all global variables found in the AST.
    private final Deque<Definition> allDefinitionsStack = new ArrayDeque<>();

    DefinitionMover createDefinitionMover(Node root) {
      checkState(moduleRecords.isEmpty(), "DefinitionMoverFactory used more than once");
      NodeTraversal.traverseEs6(compiler, root, this);
      // Cannot correctly determine movability until all definitions are known.
      Set<Definition> movableDefinitions = new HashSet<>();
      for (Definition d : allDefinitionsStack) {
        if (isMovableDefinition(d)) {
          d.movability = DefinitionMovability.MOVABLE;
          movableDefinitions.add(d);
        } else {
          d.movability = DefinitionMovability.IMMOVABLE;
        }
      }
      return new DefinitionMover(movableDefinitions, definitionsForName, moduleRecordMap,
          moduleRecords);
    }

    @Override
    public boolean shouldTraverse(NodeTraversal t, Node n, Node parent) {
      ModuleRecord currentModuleRecord = moduleRecords.peekLast();
      if (NodeUtil.isTopLevel(n)) {
        // Check for change of module when we move to a new script.
        final CompilerInput input = t.getInput();
        final JSModule module = (input == null) ? null : input.getModule();
        if (module == null) {
          checkState(currentModuleRecord == null, "null input seen after first module");
        } else {
          if (currentModuleRecord == null || currentModuleRecord.module != module) {
            currentModuleRecord = new ModuleRecord(moduleRecords.size(), module);
            moduleRecords.add(currentModuleRecord);
            moduleRecordMap.put(module, currentModuleRecord);
          }
        }
      } else {
        // Check for beginning of a statement and/or definition.
        // We cannot do anything useful with statements that aren't inside modules.
        if (currentModuleRecord != null) {
          if (currentStatement == null) {
            // New global statement.
            currentStatement = currentModuleRecord.appendNewStatementForNode(n);
            Optional<Definition> possibleDefinition = possibleGlobalDefinition(t.getScope(), n);
            currentStatement.unconditionalDefinition = possibleDefinition;
            if (possibleDefinition.isPresent()) {
              addDefinitionForName(possibleDefinition.get());
              currentStatement.containedDefinitions.add(possibleDefinition.get());
              allDefinitionsStack.push(possibleDefinition.get());
            }
          } else {
            // Somewhere within a new global statement.
            // Check for a conditional definition.
            Optional<Definition> possibleDefinition = possibleGlobalDefinition(t.getScope(), n);
            if (possibleDefinition.isPresent()) {
              Definition conditionalDefinition = possibleDefinition.get();
              // Ignore conditional definitions that occur inside of an unconditional one for the
              // same name. There are known good cases for this, so we'll trust the developer not
              // to have done anything really wacky.
              if (currentStatement.hasUnconditionalDefinitionForName(conditionalDefinition.varName)) {
                addDefinitionForName(conditionalDefinition);
                currentStatement.containedDefinitions.add(conditionalDefinition);
              }
            }
          }
        }
      }
      return true;
    }

    @Override
    public void visit(NodeTraversal t, Node n, Node parent) {
      if (currentModuleRecord == null) {
        // We're currently parsing bootstrap, non-module code.
        return;
      }
      if (currentStatement != null && currentStatement.node == n) {
        // Finished traversing this statement. Start looking for the next one.
        currentStatement = null;
      } else if (n.isName() || (n.isStringKey() && !n.hasChildren())) {
        // We may have found a global name reference.
        final String varName = n.getString();
        if (isNonExportedGlobalName(varName, t.getScope())) {
          Optional<Definition> referencedDefinition =
              findReferencedDefinition(varName, currentStatement);

          final Reference reference = new Reference(currentStatement, n, referencedDefinition);

          if (referencedDefinition.isPresent()) {
            if (!parentModuleCanSeeSymbolsDeclaredInChildren) {
              currentStatement.containedReferences.add(reference);
              referencedDefinition.get().dependentsShallowestFirst.add(reference);
            } else {
              if (isUndefinedTypeofGuardReference(n)) {
                return; // Ignore these special guard references.
              } else if (isInstanceofReference(n)) {
                if (hasUndefinedTypeofGuard(n)) {
                  return; // Ignore already guarded reference
                } else {
                  // record the existence of this reference so it can be guarded if we move
                  // its referenced definition after it.
                  referencedDefinition.get().unguardedInstanceOfReferences.add(reference);
                }
              } else {
                currentStatement.containedReferences.add(reference);
                referencedDefinition.get().dependentsShallowestFirst.add(reference);
              }
            }
          }
        }
      }
    }

    private void addDefinitionForName(Definition newDefinition) {
      getDefinitionsForNameDeepestFirst(newDefinition.varName).add(newDefinition);
    }

    private SortedSet<Definition> getDefinitionsForNameDeepestFirst(final String varName) {
      SortedSet<Definition> definitions = definitionsForName.get(varName);
      if (definitions == null) {
        definitions = new TreeSet<>(DEEPEST_DEFINITION_FIRST);
        definitionsForName.put(varName, definitions);
      }
      return definitions;
    }

    private Optional<Definition> findReferencedDefinition(String varName,
        GlobalStatement referringStatement) {
      SortedSet<Definition> definitions = getDefinitionsForNameDeepestFirst(varName);
      ModuleRecord referringModule = referringStatement.moduleRecord;
      for (Definition d : definitions) {
        ModuleRecord definitionModule = d.getModuleRecord();
        if (dependsOn(referringModule, definitionModule)) {
          return Optional.of(d);
        } else if (referringModule.equals(definitionModule)) {
          if (d.statement.isAbove(referringStatement)) {
            return Optional.of(d);
          }
        }
      }
      return Optional.absent();
    }

    /**
     * If possibleDefinition represents a statement that defines a global variable, this method
     * creates a new IncompleteGlobalDefinition to represent it.
     */
    private Optional<Definition> possibleGlobalDefinition(Scope scope, Node possibleDefinition) {
      checkNotNull(currentStatement);
      if (scope.isGlobal() && possibleDefinition.isVar()) {
        checkState(possibleDefinition.hasOneChild(), "AST not normalized.");
        Node nameNode = possibleDefinition.getFirstChild();
        if (nameNode.hasChildren()) {
          // var NAME = VALUE;
          return Optional.of(createDefinition(DefinitionKind.VARIABLE_DECLARATION,
              nameNode.getString(), possibleDefinition, nameNode.getFirstChild()));
        } else {
          // var NAME;
          return Optional.of(createDefinition(DefinitionKind.VARIABLE_DECLARATION,
              nameNode.getString(), possibleDefinition));
        }
      } else if (scope.isGlobal() && NodeUtil.isFunctionDeclaration(possibleDefinition)) {
        // function NAME() {}
        Node functionNode =
            possibleDefinition.isFunction() ? possibleDefinition : possibleDefinition
                .getFirstChild();
        return Optional.of(createDefinition(DefinitionKind.FUNCTION_DECLARATION, functionNode
            .getFirstChild().getString(), possibleDefinition));
      } else if (NodeUtil.isExprAssign(possibleDefinition)) {
        Node assignNode = possibleDefinition.getFirstChild();
        Node nameNode = assignNode.getFirstChild();
        DefinitionKind kind = DefinitionKind.VARIABLE_ASSIGNMENT;
        if (nameNode.isGetProp()) {
          kind = DefinitionKind.PROPERTY_ASSIGNMENT;
          while (nameNode.isGetProp()) {
            nameNode = nameNode.getFirstChild();
          }
        }
        if (nameNode.isName()) {
          // NAME = ...
          // OR
          // NAME.some.possibly.long.path = ...
          String varName = nameNode.getString();
          Var v = scope.getVar(varName);
          if (v != null && v.isGlobal()) {
            final Node valueNode = assignNode.getSecondChild();
            return Optional.of(createDefinition(kind, varName, possibleDefinition, valueNode));
          }
        }
      } else if (NodeUtil.isExprCall(possibleDefinition)) {
        // Check for inheritance set-up calls like this one, since they must be moved with the
        // classes they modify.
        // goog.inherits(SubClass, Foo);
        Node callNode = possibleDefinition.getFirstChild();
        SubclassRelationship relationship =
            compiler.getCodingConvention().getClassesDefinedByCall(callNode);
        if (relationship != null) {
          String varName = relationship.subclassName;
          Var v = scope.getVar(varName);
          if (v != null && v.isGlobal()) {
            return Optional.of(createDefinition(DefinitionKind.INHERITANCE_SETUP, varName,
                possibleDefinition));
          }
        }
      }
      return Optional.<Definition>absent();
    }

    private Definition createDefinition(DefinitionKind kind, String varName, Node node,
        final Node valueNode) {
      return new Definition(currentStatement, kind, nextDefinitionIndex++, node, varName, valueNode);
    }

    private Definition createDefinition(final DefinitionKind kind, String varName, Node node) {
      return new Definition(currentStatement, kind, nextDefinitionIndex++, node, varName);
    }

    private boolean isMovableDefinition(Definition def) {
      if (compiler.getCodingConvention().isExported(def.varName)) {
        return false;
      } else if (def.isUnconditional()) {
        // If the definition is an assignment or initialized variable declaration,
        // the assigned value itself must be safe to move.
        return !def.assignedValue.isPresent() || canMoveValue(def.assignedValue.get());
      } else {
        return false;
      }
    }

    private boolean canMoveValue(Node value) {
      if (NodeUtil.isLiteralValue(value, /* includeFunctions */true)) {
        return true;
      } else if (value.isCall() && value.getFirstChild().isName()) {
        // Special case for stubs created by CrossModuleMethodMotion.
        String functionName = value.getFirstChild().getString();
        return functionName.equals(CrossModuleMethodMotion.STUB_METHOD_NAME)
            || functionName.equals(CrossModuleMethodMotion.UNSTUB_METHOD_NAME);
      } else if (value.isName()) {
        // Direct assignment of a name is movable only if it is a global that is defined only once,
        // unconditionally, and in the global scope.
        final Set<Definition> definitions = definitionsForName.get(value.getString());
        if (definitions == null) {
          return false; // No definitions found, so we cannot tell if it's safe to move.
        }
        Definition oneAndOnlyDefinition = null;
        for (Definition d : definitions) {
          switch (d.kind) {
            case FUNCTION_DECLARATION:
            case VARIABLE_DECLARATION:
            case VARIABLE_ASSIGNMENT:
              if (oneAndOnlyDefinition == null) {
                oneAndOnlyDefinition = d;
              } else {
                return false;
              }
              break;
            default:
              // Setting properties and setting up inheritance are not considered to be definitions
              // here.
              break;
          }
        }
        return oneAndOnlyDefinition != null && oneAndOnlyDefinition.isUnconditional();
      } else if (value.isArrayLit()) {
        for (Node child = value.getFirstChild(); child != null; child = child.getNext()) {
          if (!canMoveValue(child)) {
            return false;
          }
        }
        return true; // All array elements are movable.
      } else if (value.isObjectLit()) {
        for (Node child = value.getFirstChild(); child != null; child = child.getNext()) {
          if (!canMoveValue(child.getFirstChild())) {
            return false;
          }
        }
        return true; // All object elements are movable.
      } else {
        return false;
      }
    }
  }

  private static final class ModuleRecord {
    final int astIndex;
    final JSModule module;
    final Deque<GlobalStatement> statements = new ArrayDeque<>();
    int nextPrependStatementIndex = -1;

    ModuleRecord(int orderIndex, JSModule module) {
      this.astIndex = orderIndex;
      this.module = module;
    }

    boolean isDeeperThan(ModuleRecord other) {
      final int otherDepth = other.module.getDepth();
      final int thisDepth = module.getDepth();
      if (otherDepth == thisDepth) {
        return astIndex > other.astIndex;
      } else {
        return thisDepth > otherDepth;
      }
    }

    GlobalStatement appendNewStatementForNode(Node n) {
      int statementIndex = statements.isEmpty() ? 0 : statements.getLast().modulePositionIndex + 1;
      GlobalStatement newStatement = new GlobalStatement(n, this, statementIndex);
      statements.add(newStatement);
      return newStatement;
    }

    void prependStatement(GlobalStatement statement) {
      statement.moduleRecord = this;
      statement.modulePositionIndex =
          statements.isEmpty() ? -1 : statements.getFirst().modulePositionIndex - 1;
    }

    Set<Definition> getContainedDefinitions() {
      final Set<Definition> containedDefinitions = new HashSet<>();
      for (GlobalStatement statement : statements) {
        containedDefinitions.addAll(statement.containedDefinitions);
      }
      return containedDefinitions;
    }

    Set<Definition> getReferencedDefinitions() {
      final Set<Definition> referencedDefinitions = new HashSet<>();
      for (GlobalStatement s : statements) {
        for (Reference r : s.containedReferences) {
          if (r.referencedDefinition.isPresent()) {
            referencedDefinitions.add(r.referencedDefinition.get());
          }
        }
      }
      return referencedDefinitions;
    }

    int compareAbsoluteDepth(ModuleRecord other) {
      return getAbsoluteDepth().compareTo(other.getAbsoluteDepth());
    }

    AbsoluteModuleDepth getAbsoluteDepth() {
      return new AbsoluteModuleDepth(this);
    }

    @Override
    public boolean equals(Object o) {
      if (this == o) {
        return true;
      } else if (o == null || o.getClass() != getClass()) {
        return false;
      } else {
        ModuleRecord other = (ModuleRecord) o;
        checkState(this.module != other.module,
            "Two ModuleRecords exist for the same module: %s and %s", this, other);
        return false;
      }
    }

    @Override
    public int hashCode() {
      return Objects.hash(astIndex, module);
    }

    @Override
    public String toString() {
      return MoreObjects.toStringHelper(this).add("module", module).add("depth", module.getDepth())
          .add("orderIndex", astIndex).toString();
    }
  }

  private static final class AbsoluteModuleDepth implements Comparable<AbsoluteModuleDepth> {
    final int moduleDepth;
    final int astIndex;

    AbsoluteModuleDepth(ModuleRecord moduleRecord) {
      this.moduleDepth = moduleRecord.module.getDepth();
      this.astIndex = moduleRecord.astIndex;
    }

    @Override
    public int compareTo(AbsoluteModuleDepth o) {
      if (o == this) {
        return 0;
      } else if (moduleDepth != o.moduleDepth) {
        return moduleDepth - o.moduleDepth;
      } else {
        return astIndex - o.astIndex;
      }
    }

    @Override
    public String toString() {
      return MoreObjects.toStringHelper(this).add("moduleDepth", moduleDepth)
          .add("astIndex", astIndex).toString();
    }
  }

  private static final class GlobalStatement {
    final Node node;
    final Set<Reference> containedReferences = new HashSet<>();
    final Set<Definition> containedDefinitions = new HashSet<>();
    Optional<Definition> unconditionalDefinition;
    ModuleRecord moduleRecord;
    int modulePositionIndex;

    GlobalStatement(Node node, ModuleRecord moduleRecord, int modulePositionIndex) {
      this.node = node;
      this.moduleRecord = moduleRecord;
      this.modulePositionIndex = modulePositionIndex;
    }

    boolean hasUnconditionalDefinitionForName(String varName) {
      return unconditionalDefinition.isPresent()
          && unconditionalDefinition.get().varName.equals(varName);
    }

    public boolean isAbove(GlobalStatement other) {
      return this.getAbsoluteDepth().compareTo(other.getAbsoluteDepth()) < 0;
    }

    int compareAbsoluteDepth(GlobalStatement other) {
      return getAbsoluteDepth().compareTo(other.getAbsoluteDepth());
    }

    AbsoluteStatementDepth getAbsoluteDepth() {
      return new AbsoluteStatementDepth(this);
    }

    @Override
    public String toString() {
      final ToStringHelper toStringHelper =
          MoreObjects.toStringHelper(this).add("moduleRecord", moduleRecord)
              .add("modulePositionIndex", modulePositionIndex);
      if (unconditionalDefinition.isPresent()) {
        toStringHelper.add("defines", unconditionalDefinition.get().varName);
      } else {
        toStringHelper.add("defines", "<nothing>");
      }
      return toStringHelper.toString();
    }
  }

  private static final class AbsoluteStatementDepth implements Comparable<AbsoluteStatementDepth> {
    final AbsoluteModuleDepth absoluteModuleDepth;
    final int modulePositionIndex;

    AbsoluteStatementDepth(GlobalStatement statement) {
      this.absoluteModuleDepth = new AbsoluteModuleDepth(statement.moduleRecord);
      this.modulePositionIndex = statement.modulePositionIndex;
    }

    @Override
    public int compareTo(AbsoluteStatementDepth o) {
      if (o == this) {
        return 0;
      } else {
        int result = absoluteModuleDepth.compareTo(o.absoluteModuleDepth);
        if (result == 0) {
          result = modulePositionIndex - o.modulePositionIndex;
        }
        return result;
      }
    }

    @Override
    public String toString() {
      return MoreObjects.toStringHelper(this).add("absoluteModuleDepth", absoluteModuleDepth)
          .add("modulePositionIndex", modulePositionIndex).toString();
    }
  }

  /**
   * Represents a statement that defines a global variable.
   * 
   * <p>
   * This could be a partial definition. e.g. all of the following statements are considered to be
   * definitions for `F`. <code><pre>
   *   function F() {};
   *   F.prototype.a = 1;
   *   F.prototype.b = function() {};
   * </pre></code> This object is created when traversal of the definition is complete. Dependent
   * references are added to it as they are discovered during continued processing of the AST.
   */
  private static final class Definition {
    final GlobalStatement statement;
    final DefinitionKind kind;
    final int orderIndex;
    // The definition statement.
    final Node definitionNode;
    final String varName;
    // The node representing the value being assigned to the global name.
    // Only present when the assignment operator is actually used, not for function declarations
    // or the special-case class defining method calls.
    final Optional<Node> assignedValue;
    // References that depend on this global definition.
    final SortedSet<Reference> dependentsShallowestFirst = new TreeSet<Reference>(
        SHALLOWEST_REFERENCE_FIRST);
    final Set<Reference> unguardedInstanceOfReferences = new HashSet<>();
    final ModuleRecord originalModuleRecord;
    DefinitionMovability movability;

    Definition(GlobalStatement statement, DefinitionKind kind, int orderIndex, Node definitionNode,
        String varName, Optional<Node> assignedValue) {
      this.statement = statement;
      this.originalModuleRecord = statement.moduleRecord;
      this.kind = kind;
      this.orderIndex = orderIndex;
      this.definitionNode = definitionNode;
      this.varName = varName;
      this.assignedValue = assignedValue;
      this.movability = DefinitionMovability.UNKNOWN;
    }

    Definition(GlobalStatement statement, DefinitionKind kind, int orderIndex, Node definitionNode,
        String varName) {
      this(statement, kind, orderIndex, definitionNode, varName, Optional.<Node>absent());
    }

    Definition(GlobalStatement statement, DefinitionKind kind, int orderIndex, Node definitionNode,
        String varName, Node assignedValue) {
      this(statement, kind, orderIndex, definitionNode, varName, Optional.of(assignedValue));
    }

    ModuleRecord getModuleRecord() {
      return statement.moduleRecord;
    }

    boolean isUnconditional() {
      return statement.node == definitionNode;
    }

    boolean isMovable() {
      return movability == DefinitionMovability.MOVABLE;
    }

    int compareAbsoluteDepth(Definition other) {
      return statement.compareAbsoluteDepth(other.statement);
    }

    @Override
    public String toString() {
      return MoreObjects.toStringHelper(this).add("varName", varName).add("orderIndex", orderIndex)
          .add("originalModuleRecord", originalModuleRecord).add("statment", statement).toString();
    }
  }

  private static enum DefinitionKind {
    VARIABLE_DECLARATION, // var A | let A
    FUNCTION_DECLARATION, // function A() {
    VARIABLE_ASSIGNMENT, // A =
    INHERITANCE_SETUP, // goog.inherit(A, B)
    PROPERTY_ASSIGNMENT; // A.prototype.foo =
  }

  private static enum DefinitionMovability {
    UNKNOWN, MOVABLE, IMMOVABLE;
  }

  /** Represents all types of references to global variables. */
  private static final class Reference {
    final GlobalStatement statement;
    // The node containing the global variable's name.
    final Node referenceNode;
    // As we move code around, it can happen that the global definition being referenced changes
    // and must be updated. This is because module dependencies don't always reflect true code
    // dependencies.
    Optional<Definition> referencedDefinition;

    Reference(GlobalStatement statement, Node referenceNode,
        Optional<Definition> referencedDefinition) {
      this.statement = checkNotNull(statement);
      this.referenceNode = checkNotNull(referenceNode);
      this.referencedDefinition = checkNotNull(referencedDefinition);
    }

    String getVarName() {
      return referenceNode.getString();
    }

    ModuleRecord getModuleRecord() {
      return statement.moduleRecord;
    }

    @Override
    public String toString() {
      return MoreObjects.toStringHelper(this).add("varName", referenceNode.toString())
          .add("statement", statement).toString();
    }
  }

  private static final Ordering<Reference> SHALLOWEST_REFERENCE_FIRST = new Ordering<Reference>() {

    @Override
    public int compare(Reference left, Reference right) {
      checkNotNull(left);
      checkNotNull(right);
      return left.statement.getAbsoluteDepth().compareTo(right.statement.getAbsoluteDepth());
    }
  };

  private boolean isNonExportedGlobalName(String name, Scope scope) {
    Var v = scope.getVar(name);
    return v != null && v.isGlobal() && !compiler.getCodingConvention().isExported(name);
  }
}
