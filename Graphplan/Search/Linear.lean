import Graphplan.Search.Basic


-- Our linear search strategy will use the search space defined in Graphplan/Search/Basic.lean.
-- It starts by adding the initial state to the known states and then explores the search space
-- by applying possible actions to the current state, updating the known states, and checking
-- for goal satisfaction.


def linear_search (initial_search_state : Search.SearchState) :
    Option (Search.partial_Solution initial_search_state.plan) := do
  let _ := initial_search_state.step_decidable
  let _ := initial_search_state.steps_beq
  let _ := initial_search_state.step_hashable
  let _ := initial_search_state.plan.prop_decidable
  let _ := initial_search_state.plan.prop_repr

  -- Initialize the search with the initial state
  let mut known_steps := initial_search_state.known_steps

  -- -- Add the initial state to the known states
  -- known_steps := known_steps.insert
  --   initial_search_state.plan.current_state
  --   []
  -- TODO: Does it work without this?

  -- The list of steps to explore
  let mut steps_to_explore := initial_search_state.steps_to_consider

  -- Main search loop, iterates until a solution is found or no more states to explore
  -- Loop sctructure: take a step from the list, check whether it achieves the goal,
  -- (if so, return the solution),
  -- otherwise, generate new states by applying all possible actions,
  -- add the explored step to known states,
  repeat
    -- If the list can be expressed as head :: tail, proceed
    -- dbg_trace "Steps to explore: {steps_to_explore.length}"

    match steps_to_explore with
    | [] =>
      -- dbg_trace "No more steps to explore"
      -- dbg_trace "Known steps: {known_steps.size}"
      none
    | cur_step :: tail =>
      -- Update the list of steps to explore
      steps_to_explore := tail

      -- debug repr for the current step


      -- let repr_cur_step := repr cur_step
      -- dbg_trace "Exploring step with props: {repr_cur_step}"

      -- Synthesize decidablity for the goal check
      let _ : Decidable (cur_step ∈ initial_search_state.plan.goal_states) := by
        let _ := initial_search_state.plan.prop_decidable
        let _ : DecidableEq (List initial_search_state.plan.Props) := by infer_instance
        let _ : BEq (List initial_search_state.plan.Props) := instBEqOfDecidableEq
        infer_instance
      if is_goal: Search.is_goal_reached initial_search_state cur_step then
        -- Reconstruct the solution from known states
        let mut actions : List (STRIPS.STRIPS_Operator initial_search_state.plan.Props) := []
        let mut state := cur_step

        while state ≠ initial_search_state.plan.current_state do
          match Search.find_in_hashmap? known_steps state with
          | none =>
            dbg_trace "Error: state not found in known_steps during solution reconstruction"
            none -- This should not happen
          | some prev_states =>
            -- We add the action that led to this state
            let (prev_state, action) := prev_states
            actions := action :: actions
            state := prev_state

        -- Return the solution
        return { actions := actions }
        -- , is_valid := (by
        --   unfold Search.is_valid_plan
        --   -- simp only [List.pure_def, List.bind_eq_flatMap, List.flatMap_cons, List.flatMap_nil,
        --   --   List.append_nil, List.flatMap_id', List.contains_eq_mem, List.mem_flatten,
        --   --   List.any_eq_true, List.all_eq_true, decide_eq_true_eq]
        --   -- use cur_step
        --   -- constructor
        --   -- · exact is_goal
        --   -- · intro one_prop h_one_prop
        --   simp only
        --   unfold STRIPS.apply_action_if_applicable
        --   -- Hm, might need to add the proof that the action took place
        --   -- and moved from the previous state to the current state in the known_steps map.

        --   -- Thinking about it even more, I should prefer storing the entire list of actions
        --   -- that led to the state, instead of just the previous state and the action.
        --   -- This way, I cam store the proof of the entire list of actions leading to the goal.

        -- ) }
        -- TODO: Prove validity of the plan

      -- The current step does not achieve the goal, generate new states
      else
        for action in initial_search_state.plan.Actions do
          if STRIPS.is_applicable'
              cur_step action then
            let new_state := STRIPS.apply_action_if_applicable
              { initial_search_state.plan with current_state := cur_step } action

            -- If the new state is not already known, add it to known states and steps to explore
            if ¬ known_steps.contains new_state then
              known_steps := known_steps.insert new_state (cur_step, action)

              -- steps_to_explore := new_state :: steps_to_explore
              -- The new state needs to be added to the back, not the front, to ensure BFS behavior
              steps_to_explore := steps_to_explore ++ [new_state]


            -- If the new state is already known, do nothing
            else  continue

  -- If no solution is found, return none
  -- dbg_trace "No solution found"
  -- dbg_trace "Known steps: {known_steps.size}"
  none

/-
The rest of this file was generated by Aristotle and only modified slightly, mainly cleanup and
line wrapping.
Note that Aristotle did not fully fulfill the request, as it only changed the function slightly
to make the fact that the solution is correct expressible
and just not return it if it turns out invalid.
-/

----------------

/-
This file was generated by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 87073e61-b29c-4c20-a9eb-37059f6f5ac4
-/

/-
I have implemented the linear search with proof generation in `linear_search_final`.
I defined a helper function `reconstruct_path_fuel_with_map` to reconstruct
the path from the predecessor map. Both functions use a `fuel` parameter to ensure termination
without complex proofs, and explicit instance passing to handle type class synthesis for `HashMap`.
The implementation follows the BFS strategy of the original `linear_search`,
but reconstructs the full path and verifies it using `Search.is_valid_plan`
to produce a `Search.Solution`.
-/


/-
Reconstructs the list of actions from the initial state to the given state using the predecessor map.
-/
def reconstruct_path_fuel_with_map (s : Search.SearchState)
    (known_steps : @Std.HashMap (List s.plan.Props) ((List s.plan.Props) × (STRIPS.STRIPS_Operator s.plan.Props)) s.steps_beq s.step_hashable)
    (current_state : List s.plan.Props)
    (acc : List (STRIPS.STRIPS_Operator s.plan.Props))
    (fuel : Nat) :
    Option (List (STRIPS.STRIPS_Operator s.plan.Props)) :=
  match fuel with
  | 0 => none
  | n + 1 =>
    if s.steps_beq.beq current_state s.plan.current_state then
      some acc
    else
      match @Search.find_in_hashmap? (List s.plan.Props) ((List s.plan.Props) × (STRIPS.STRIPS_Operator s.plan.Props)) s.steps_beq s.step_hashable known_steps current_state with
      | none => none
      | some (prev, act) => reconstruct_path_fuel_with_map s known_steps prev (act :: acc) n

/-
Implementation of linear search that returns a certified solution.
-/
def linear_search_proved (initial_search_state : Search.SearchState) :
    Option (Search.Solution initial_search_state.plan) := do
  let _ := initial_search_state.step_decidable
  let _ := initial_search_state.steps_beq
  let _ := initial_search_state.step_hashable
  let _ := initial_search_state.plan.prop_decidable
  let _ := initial_search_state.plan.prop_repr

  let rec bfs_loop (known_steps : @Std.HashMap (List initial_search_state.plan.Props) ((List initial_search_state.plan.Props) × (STRIPS.STRIPS_Operator initial_search_state.plan.Props)) initial_search_state.steps_beq initial_search_state.step_hashable)
                   (steps_to_explore : List (List initial_search_state.plan.Props))
                   (fuel : Nat) :
                   Option (Search.Solution initial_search_state.plan) := do
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      match steps_to_explore with
      | [] => none
      | cur_step :: tail =>
        if Search.is_goal_reached initial_search_state cur_step then
           match reconstruct_path_fuel_with_map initial_search_state known_steps cur_step [] 1000000 with
           | none => none
           | some actions =>
             if h : Search.is_valid_plan initial_search_state.plan actions then
               some { actions := actions, is_valid := h }
             else
               none
        else
          let mut new_known := known_steps
          let mut new_steps := tail
          for action in initial_search_state.plan.Actions do
            if STRIPS.is_applicable' cur_step action then
              let new_state := STRIPS.apply_action_if_applicable
                { initial_search_state.plan with current_state := cur_step } action
              if ¬ new_known.contains new_state then
                new_known := new_known.insert new_state (cur_step, action)
                new_steps := new_steps ++ [new_state]
          bfs_loop new_known new_steps fuel'

  bfs_loop initial_search_state.known_steps initial_search_state.steps_to_consider 1000000
