-- This file is for describing the search strategies used for STRIPS.
-- The implementations will be in separate files.

import Graphplan.Basic

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


end Search
