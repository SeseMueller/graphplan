-- This file is for describing the search strategies used for STRIPS.
-- The implementations will be in separate files.

import Graphplan.Basic
import Std.Data.HashMap

open STRIPS

namespace Search

-- A proof that a given sequence of actions is a valid plan for a STRIPS planning problem.
def is_valid_plan (P : STRIPS_Plan) (actions : List (STRIPS_Operator P.Props)) : Bool :=
  -- let final_state := actions.foldl (fun state op =>
  --   apply_action_if_applicable P op) P.current_state

  -- Because I don't really know how to proove that the state has the same type as P.Props,
  -- I will try a different approach.
  let _ := P.prop_decidable -- Proof that Props are decidable
  let _ : BEq P.Props := instBEqOfDecidableEq -- Proof that Props are comparable
  let final_state := do
    let mut state := P.current_state
    for op in actions do
      state := apply_action_if_applicable { P with current_state := state } op
    state

  -- Check if any of the goals is fully satisfied in the final state
  P.goal_states.any (fun goal => goal.all (fun p => final_state.contains p))


-- A search solution is a sequence of actions that achieves the goal from the initial state.
structure Solution (P : STRIPS_Plan) where
  actions : List (STRIPS_Operator P.Props)

  is_valid : is_valid_plan P actions = true

structure partial_Solution (P : STRIPS_Plan) where
  actions : List (STRIPS_Operator P.Props)


-- A helper function that returns all possible actions from the current state.
def possible_actions {P : STRIPS_Plan} : Array (STRIPS_Operator P.Props) :=
  P.Actions.filter (fun a => is_applicable a)


-- A possible way to represent the search state.
structure SearchState where
  -- The main plan of the search
  plan : STRIPS_Plan
  -- The list of next steps to consider
  steps_to_consider : List (List plan.Props) -- Note that List is a linked list
  -- to allow for efficient removal of the head action.

  -- The fact that a list of props (a step) is decidable for equality
  step_decidable : DecidableEq (List plan.Props)
  -- The fact that the List of steps is BEq, that is, it can be compared for equality
  steps_beq : BEq (List plan.Props)
  -- The fact that a step is hashable
  step_hashable : Hashable (List plan.Props)

  -- The hashmap that maps all known states to their previous state and the action that led to them
  known_steps : Std.HashMap (List plan.Props) ((List plan.Props) × (STRIPS_Operator plan.Props))

-- Constructing search states in an easier way
def mk_search_state (P : STRIPS_Plan) :
    SearchState :=
  let plan := P
  let steps_to_consider := [P.current_state]

  -- We need to prove BEq and Hashable for the step type (List plan.Props)
  let prop_decidable := P.prop_decidable
  let step_decidable : DecidableEq (List plan.Props) := by
    infer_instance
  let steps_beq : BEq (List plan.Props) := by infer_instance

  let prop_hashable := P.prop_hashable
  let step_hashable : Hashable (List plan.Props) := by
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
def is_goal_reached (s : SearchState) (state : List s.plan.Props) : Bool :=
  let _ := s.plan.prop_decidable
  ∃ goal_state ∈ s.plan.goal_states, goal_state ⊆ state

end Search
