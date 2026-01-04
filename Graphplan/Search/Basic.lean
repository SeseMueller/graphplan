-- This file is for describing the search strategies used for STRIPS.
-- The implementations will be in separate files.

import Graphplan.Basic
import Std.Data.HashMap

open STRIPS

namespace Search

-- A proof that a given sequence of actions is a valid plan for a STRIPS planning problem.
def is_valid_plan {α : Type} (P : STRIPS_Plan α) (actions : List (STRIPS_Operator α)) : Bool :=
  -- let final_state := actions.foldl (fun state op =>
  --   apply_action_if_applicable P op) P.current_state

  -- Because I don't really know how to proove that the state has the same type as P.Props,
  -- I will try a different approach.
  let _ := P.prop_decidable -- Proof that Props are decidable
  let _ : BEq α := instBEqOfDecidableEq -- Proof that Props are comparable

  -- let final_state := do

  let final_state : List α := do
    let mut state := P.current_state
    for op in actions do
      state := apply_action_if_applicable { P with current_state := state } op
    state

  -- Check if any of the goals is fully satisfied in the final state
  P.goal_states.any (fun goal => goal.all (fun p => final_state.contains p))

-- A helper function that generates the last state after applying a list of actions
def final_state_after_actions {α : Type} (P : STRIPS_Plan α)
    (actions : List (STRIPS_Operator α)) : List α :=
  let _ := P.prop_decidable -- Proof that Props are decidable
  let _ : BEq α := instBEqOfDecidableEq -- Proof that Props are comparable
  let final_state : List α := do
    let mut state := P.current_state
    for op in actions do
      state := apply_action_if_applicable { P with current_state := state } op
    state
  final_state
  -- with recursion (same result)
  -- match actions with
  -- | [] => P.current_state
  -- | this :: tail =>
  --   final_state_after_actions { P with current_state := apply_action_if_applicable P this } tail

def is_valid_plan' {α : Type} (P : STRIPS_Plan α)
    (actions : List (STRIPS_Operator α)) : Prop :=
  let final_state := final_state_after_actions P actions
  ∃ goal_state ∈ P.goal_states, goal_state ⊆ final_state

-- Theorem: both definitions of is_valid_plan are equivalent
theorem is_valid_plan_equiv {α : Type} (P : STRIPS_Plan α)
    (actions : List (STRIPS_Operator α)) :
    is_valid_plan P actions = true ↔ is_valid_plan' P actions := by {
  unfold is_valid_plan is_valid_plan' final_state_after_actions
  let _ := P.prop_decidable
  let _ : BEq α := instBEqOfDecidableEq
  simp_all
  constructor
  {
    intro h_valid
    obtain ⟨goal_state, h_goal_in_goals, h_goal_subset⟩ := h_valid
    use goal_state
    simp_all

    intro goal_state h_goal_in_goals
    exact List.mem_flatten.mpr (h_goal_subset goal_state h_goal_in_goals)
  }
  {
    intro h_valid
    obtain ⟨goal_state, h_goal_in_goals, h_goal_subset⟩ := h_valid
    use goal_state
    simp_all

    intro x h_x_in_goal
    exact List.exists_of_mem_flatten (h_goal_subset h_x_in_goal)
  }
}

-- Simple helper lemma: if a plan is valid, then another plan, that is identical
-- but with an one less action at the end that leads to a new state, is also valid if the
-- new plan has that one new state as its final state.
theorem valid_plan_extend' {α : Type} (P1 : STRIPS_Plan α)
    (additional_action : STRIPS_Operator α)
    (P2 : STRIPS_Plan α := { P1 with
      current_state := STRIPS.apply_action_if_applicable P1 (additional_action) })
    (actions1 : List (STRIPS_Operator α))
    (actions2 : List (STRIPS_Operator α))
    (h_plan_eq : P2 = { P1 with current_state := STRIPS.apply_action_if_applicable P1 additional_action })
    (h_actions_eq : actions1 = [additional_action] ++ actions2)
    (h_valid : is_valid_plan' P2 actions2 = true) :
    is_valid_plan' P1 actions1 = true := by {


      -- simp_all [is_valid_plan, apply_action_if_applicable, apply_action_with_proof]
      simp_all [is_valid_plan']
      -- Dig deep into the definitions
      obtain ⟨goal_state, h_goal_in_goals, h_goal_subset⟩ := h_valid
      use goal_state
      simp_all

      unfold final_state_after_actions at *
      simp_all
    }

-- A search solution is a sequence of actions that achieves the goal from the initial state.
structure Solution {α : Type} (P : STRIPS_Plan α) where
  actions : List (STRIPS_Operator α)

  is_valid : is_valid_plan P actions = true

structure partial_Solution {α : Type} (P : STRIPS_Plan α) where
  actions : List (STRIPS_Operator α)


-- A helper function that returns all possible actions from the current state.
def possible_actions {α : Type} {P : STRIPS_Plan α} : Array (STRIPS_Operator α) :=
  P.Actions.filter (fun a => is_applicable P a)


-- A possible way to represent the search state.
structure SearchState (α : Type) where
  -- The main plan of the search
  plan : STRIPS_Plan α
  -- The list of next steps to consider
  steps_to_consider : List (List α) -- Note that List is a linked list
  -- to allow for efficient removal of the head action.

  -- The fact that a list of props (a step) is decidable for equality
  step_decidable : DecidableEq (List α)
  -- The fact that the List of steps is BEq, that is, it can be compared for equality
  steps_beq : BEq (List α)
  -- The fact that a step is hashable
  step_hashable : Hashable (List α)
  -- The hashmap that maps all known states to their previous state and the action that led to them
  known_steps : Std.HashMap (List α) ((List α) × (STRIPS_Operator α))

-- Constructing search states in an easier way
def mk_search_state {α : Type} (P : STRIPS_Plan α) :
    SearchState α :=
  let plan := P
  let steps_to_consider := [P.current_state]

  -- We need to prove BEq and Hashable for the step type (List plan.Props)
  let prop_decidable := P.prop_decidable
  let step_decidable : DecidableEq (List α) := by
    infer_instance
  let steps_beq : BEq (List α) := by infer_instance

  let prop_hashable := P.prop_hashable
  let step_hashable : Hashable (List α) := by
    infer_instance

  let known_steps := Std.HashMap.emptyWithCapacity 10
  { plan := P,
    steps_to_consider := steps_to_consider,
    known_steps := known_steps
    step_decidable := step_decidable
    steps_beq := steps_beq
    step_hashable := step_hashable
  }

-- Whether the goal was reached in the search state
-- Note that not the entire goal state has to match,
-- the state only has to contain all the props in one of the goal states.
def is_goal_reached {α : Type} (s : SearchState α) (state : List α) : Bool :=
  let _ := s.plan.prop_decidable
  ∃ goal_state ∈ s.plan.goal_states, goal_state ⊆ state


-- Helper function that searches the given HashMap for a Value, returning none if not found.
-- This is very slow, but it should only be done once a solution is found, and only once.
def find_in_hashmap? {K V : Type} [BEq K] [Hashable K]
    (hm : Std.HashMap K V) (key : K) : Option V := do
  for (k, v) in hm do
    if k == key then
      return  v
  none

-- Helper function: if is_goal_reached is true, construct a trivial solution:
-- no actions needed, current state is goal state.
def trivial_solution_if_goal_reached {α : Type} (s : SearchState α)
    (h_goal_reached : is_goal_reached s s.plan.current_state = true) :
    Search.Solution s.plan := by {
      let _ := s.plan.prop_decidable
      -- Because the goal is already reached, no actions are needed.
      let actions : List (STRIPS_Operator α) := []
      have h_actions : actions = [] := by rfl
      have h_valid : is_valid_plan s.plan actions = true := by {
        -- Because the current state already satisfies the goal, the empty action list is valid.
        simp_all [is_valid_plan, is_goal_reached]
        obtain ⟨goal_state, h_goal_in_goals, h_goal_subset⟩ := h_goal_reached
        use goal_state
        simp_all
        intro x h_x_in_goal
        exact h_goal_subset h_x_in_goal
      }
      exact { actions := actions, is_valid := h_valid }
    }


end Search
