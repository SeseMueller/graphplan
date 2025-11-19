import Graphplan.Search.Basic


-- Our linear search strategy will use the search space defined in Graphplan/Search/Basic.lean.
-- It starts by adding the initial state to the known states and then explores the search space
-- by applying possible actions to the current state, updating the known states, and checking
-- for goal satisfaction.


-- Helper function that searches the given HashMap for a Value, returning none if not found.
-- This is very slow, but it should only be done once a solution is found, and only once.
def find_in_hashmap? {K V : Type} [BEq K] [Hashable K]
    (hm : Std.HashMap K V) (key : K) : Option V := do
  for (k, v) in hm do
    if k == key then
      return  v
  none

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
          match find_in_hashmap? known_steps state with
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
