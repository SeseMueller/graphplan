import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Disjoint
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype

namespace STRIPS

-- A STRIPS operator is a 4-tuple, where each set is a set of propositional variables.
structure STRIPS_Operator (Props : Type) where
  -- The preconditions that must be satisfied to apply the operator
  preconditions : List Props
  -- The preconditions that must not be satisfied to apply the operator
  neg_preconditions : List Props
  -- The effects that will be added to the state after applying the operator
  add_effects : List Props
  -- The effects that will be removed from the state after applying the operator
  del_effects : List Props
  deriving DecidableEq

-- We define a STRIPS planning problem as a structure
-- consisting of a set of propositions, a set of actions,
-- an initial state, and a goal state.
structure STRIPS_Plan where
  -- The propositional variables in the planning problem
  Props : Type
  -- props_finite : Fintype Props
  -- We don't need Fintype for now, but we do need hashable for HashMap for efficient serach.
  prop_hashable : Hashable Props
  prop_decidable : DecidableEq Props
  -- prop_set_decidable : DecidableEq (Finset Props)
  -- The actions that can be performed in the planning problem
  Actions : Array (STRIPS_Operator Props)
  -- The current state of the planning problem
  current_state : List Props
  -- The valid goal states of the planning problem
  goal_states : List (List Props)





-- Whether or not an action is applicable, only based on the state and the action itself
def is_applicable' {sp : STRIPS_Plan} (state : List sp.Props)
    (a : STRIPS_Operator sp.Props) : Prop :=
  -- The action is applicable if all its positive preconditions are in the state
  -- and none of its negative preconditions are in the state
  -- a.preconditions ⊆ state ∧ Disjoint a.neg_preconditions state
  -- (∀ p ∈ a.preconditions, p ∈ state) ∧ Disjoint a.neg_preconditions state
  (∀ p ∈ a.preconditions, p ∈ state) ∧
    (∀ p ∈ a.neg_preconditions, p ∉ state)


-- Whether or not an action is applicable in a given state
def is_applicable {sp : STRIPS_Plan} (a : STRIPS_Operator sp.Props) : Prop :=
  -- The action is applicable if all its positive preconditions are in the state
  -- and none of its negative preconditions are in the state
  -- a.preconditions ⊆ sp.current_state ∧ Disjoint a.neg_preconditions sp.current_state
  -- (∀ p ∈ a.preconditions, p ∈ sp.current_state) ∧ Disjoint a.neg_preconditions sp.current_state
  (∀ p ∈ a.preconditions, p ∈ sp.current_state) ∧
    (∀ p ∈ a.neg_preconditions, p ∉ sp.current_state)

-- All is_applicable proofs are decidable
instance {sp : STRIPS_Plan} (a : STRIPS_Operator sp.Props) : Decidable (is_applicable a) := by
  let _ := sp.prop_decidable
  unfold is_applicable
  exact instDecidableAnd

instance {sp : STRIPS_Plan} (state : List sp.Props)
    (a : STRIPS_Operator sp.Props) : Decidable (is_applicable' state a) := by
  let _ := sp.prop_decidable
  unfold is_applicable'
  exact instDecidableAnd

-- -- Applies an action to a given state, returning the new state
-- def apply_action {sp : STRIPS_Plan} (a : STRIPS_Operator sp.Props) : List sp.Props :=
--   -- The new state is the current state with the effects of the action applied
--   let _ := sp.prop_decidable
--   -- (sp.current_state \ a.del_effects) ∪ a.add_effects
--   ((sp.current_state.filter (¬ a.del_effects.contains ·)) ++ a.add_effects).dedup


-- Applies the action, given a proof that it is applicable
def apply_action_with_proof (sp : STRIPS_Plan) (a : STRIPS_Operator sp.Props)
    (_ : is_applicable a) : List sp.Props :=
  -- apply_action a
  let _ := sp.prop_decidable
  ((sp.current_state.filter (¬ a.del_effects.contains ·)) ++ a.add_effects).dedup

-- Applies an action, but only if it is applicable
def apply_action_if_applicable (sp : STRIPS_Plan) (a : STRIPS_Operator sp.Props) : List sp.Props :=
  let _ := sp.prop_decidable
  let _ : (Decidable (is_applicable a)) := by -- Proof that is_applicable is decidable
    unfold is_applicable
    exact instDecidableAnd
  if h : is_applicable a then
    apply_action_with_proof sp a h
  else
    sp.current_state -- Does nothing if not applicable

-- Applies the action, given a proof, returning the new state
def apply_action' (sp : STRIPS_Plan) (a : STRIPS_Operator sp.Props)
    (h : is_applicable a) : STRIPS_Plan :=
  { sp with current_state := apply_action_with_proof sp a h}
  -- Wait, this is a monad, right?

-- Applied the action if applicable, returning the new state
def apply_action_if_applicable' (sp : STRIPS_Plan) (a : STRIPS_Operator sp.Props) : STRIPS_Plan :=
  let new_list := apply_action_if_applicable sp a
  { sp with current_state := new_list }

-- DSL syntax for applying an action to a STRIPS plan
syntax:10 (name := applyMove) term " >- " term : term
macro_rules
  -- This is a bit more complicated, because we basically want opposite parsing order
  -- than is given. In the example "start_state >- Move A B >- MoveBox B C", the second
  -- ">-" takes in both Moves, but we want to parse it as
  -- "start_state >- Move A B" and then " >- MoveBox B C"
  -- So we instead only take the term to the right of ">-", and construct a function
  -- that maps a STRIPS_Plan to the result of applying that action to it.
  | `( $a:term >- $sp:term) =>
    `(apply_action' $sp $a (by decide))
    -- `((fun sp : STRIPS_Plan =>
    --     apply_action' sp $a (by decide)))



end STRIPS
