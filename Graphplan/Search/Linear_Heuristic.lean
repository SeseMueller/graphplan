import Graphplan.Search.Basic


-- Our linear search strategy will use the search space defined in Graphplan/Search/Basic.lean.
-- It starts by adding the initial state to the known states and then explores the search space
-- by applying possible actions to the current state, updating the known states, and checking
-- for goal satisfaction.

-- Heuristic to sort the states to explore by.
-- Currently, it is just the number of satisfied goal propositions.
def state_heuristic (search_state : Search.SearchState)
(state : List search_state.plan.Props) : Nat :=
  let _ := search_state.plan.prop_decidable -- So the Props can be compared
  let filtered_goals := search_state.plan.goal_states.map
    (fun goal => goal.filter (fun p => state.contains p))
  -- The filteres goals are all goals with only the propositions
  -- that are satisfied in the current state
  -- Convert to a list of their lengths
  let goal_lengths := filtered_goals.map (fun g => g.length)
  -- For now, take the maximum length as the heuristic value
  goal_lengths.foldl Nat.max 0

-- Insert a step into a queue ordered by descending `state_heuristic`.
-- If heuristic values are identical, we insert *after* existing equal-valued steps,
-- preserving breadth-first (FIFO) behavior within each heuristic bucket.
def insert_step_by_heuristic
    (search_state : Search.SearchState)
    (step : List search_state.plan.Props)
    (queue : List (List search_state.plan.Props)) : List (List search_state.plan.Props) :=
  let hStep := state_heuristic search_state step
  match queue with
  | [] => [step]
  | qHead :: qTail =>
      let hHead := state_heuristic search_state qHead
      if hHead < hStep then
        step :: qHead :: qTail
      else
        qHead :: insert_step_by_heuristic search_state step qTail

-- TODO: Instead of building a new list every time,
-- use a list of list, where every sublist has the same heuristic value.
-- Then we don't need to rebuild the entire list on every insertion.

-- Stable sort (via repeated stable insertion) by descending `state_heuristic`.
def sort_steps_by_heuristic
    (search_state : Search.SearchState)
    (steps : List (List search_state.plan.Props)) : List (List search_state.plan.Props) :=
  steps.foldl (fun acc s => insert_step_by_heuristic search_state s acc) []

def heuristic_search (initial_search_state : Search.SearchState) :
    Option (Search.partial_Solution initial_search_state.plan) := do
  let _ := initial_search_state.step_decidable
  let _ := initial_search_state.steps_beq
  let _ := initial_search_state.step_hashable
  let _ := initial_search_state.plan.prop_decidable
  let _ := initial_search_state.plan.prop_repr

  -- Initialize the search with the initial state
  let mut known_steps := initial_search_state.known_steps

  -- The list of steps to explore
  let mut steps_to_explore :=
    sort_steps_by_heuristic initial_search_state initial_search_state.steps_to_consider

  -- Main search loop, iterates until a solution is found or no more states to explore
  -- Loop sctructure: take a step from the list, check whether it achieves the goal,
  -- (if so, return the solution),
  -- otherwise, generate new states by applying all possible actions,
  -- add the explored step to known states,
  repeat
    -- If the list can be expressed as head :: tail, proceed

    match steps_to_explore with
    | [] =>
      none
    | cur_step :: tail =>
      -- Update the list of steps to explore
      steps_to_explore := tail

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

              -- Insert by heuristic; keep FIFO order when heuristic values tie.
              steps_to_explore :=
                insert_step_by_heuristic initial_search_state new_state steps_to_explore


            -- If the new state is already known, do nothing
            else continue

  -- If no solution is found, return none
  none
