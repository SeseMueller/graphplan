import Mathlib.Data.Set.Basic


-- A STRIPS operator is a 4-tuple, where each set is a set of propositional variables.
structure STRIPS_Operator (Props : Type) where
  -- The preconditions that must be satisfied to apply the operator
  preconditions : Set Props
  -- The preconditions that must not be satisfied to apply the operator
  neg_preconditions : Set Props
  -- The effects that will be added to the state after applying the operator
  add_effects : Set Props
  -- The effects that will be removed from the state after applying the operator
  del_effects : Set Props


-- We define a STRIPS planning problem as a structure
-- consisting of a set of propositions, a set of actions,
-- an initial state, and a goal state.
structure STRIPS_Plan where
  -- The propositional variables in the planning problem
  Props : Type
  -- The actions that can be performed in the planning problem
  Actions : Set (STRIPS_Operator Props)
  -- The initial state of the planning problem
  initial_state : Set Props
  -- The goal state of the planning problem
  goal_state : Set Props
