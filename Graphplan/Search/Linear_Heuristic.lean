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

abbrev Step (s : Search.SearchState) := List s.plan.Props

-- Heuristic buckets: each bucket stores a FIFO queue of steps (as an Array)
-- together with the bucket's heuristic value.
-- Invariant: buckets are ordered by descending heuristic value.
abbrev HeuristicBuckets (s : Search.SearchState) := Array (Array (Step s) × Nat)

-- Drop the first element of an array.
-- (Used to pop from the front of a FIFO queue implemented with an Array.)
def array_drop_first {α : Type} (a : Array α) : Array α :=
  Id.run do
    let mut out : Array α := #[]
    let mut first := true
    for el in a do
      if first then
        first := false
      else
        out := out.push el
    return out

-- Insert an element into an array at a given index.
-- If the index is out of bounds, inserts at the end.
def array_insert_at {α : Type} (a : Array α) (idx : Nat) (x : α) : Array α :=
  Id.run do
    let mut out : Array α := #[]
    let mut inserted := false
    let mut i := 0
    for el in a do
      if (i == idx) && (inserted == false) then
        out := out.push x
        inserted := true
      out := out.push el
      i := i + 1
    if inserted == false then
      out := out.push x
    return out

-- Insert a step into the heuristic buckets.
-- - Buckets are kept in descending heuristic order.
-- - Within a bucket of equal heuristic, we append to preserve FIFO.
def insert_step_by_heuristic
    (search_state : Search.SearchState)
    (step : Step search_state)
    (buckets : HeuristicBuckets search_state) : HeuristicBuckets search_state :=
  let hStep := state_heuristic search_state step
  Id.run do
    let mut i := 0
    let mut bs := buckets

    while i < bs.size do
      match bs[i]? with
      | none =>
        -- Should not happen due to the loop condition, but keeps the function total.
        i := bs.size
      | some (bucketSteps, hBucket) =>
        if hBucket == hStep then
          bs := bs.set! i (bucketSteps.push step, hBucket)
          return bs
        else if hBucket < hStep then
          bs := array_insert_at bs i (#[step], hStep)
          return bs
        else
          i := i + 1

    -- No matching bucket and no smaller bucket found: append at the end.
    return bs.push (#[step], hStep)

-- Convert an initial list of steps into heuristic buckets.
def bucketize_steps
    (search_state : Search.SearchState)
    (steps : List (Step search_state)) : HeuristicBuckets search_state :=
  steps.foldl (fun acc s => insert_step_by_heuristic search_state s acc) #[]

-- Pop the next step to explore, prioritizing higher-heuristic buckets.
-- Preserves FIFO order within each bucket.
def pop_next_step?
    (search_state : Search.SearchState)
    (buckets : HeuristicBuckets search_state)
    : Option (Step search_state × HeuristicBuckets search_state) :=
  Id.run do
    let mut bs := buckets
    repeat
      match bs[0]? with
      | none =>
        return none
      | some (bucketSteps, hBucket) =>
        match bucketSteps[0]? with
        | none =>
          -- Empty bucket: drop it and continue.
          bs := array_drop_first bs
        | some step =>
          let rest := array_drop_first bucketSteps
          if rest.size == 0 then
            bs := array_drop_first bs
          else
            bs := bs.set! 0 (rest, hBucket)
          return some (step, bs)
    -- If we reach here, all buckets were empty.
    return none

def heuristic_search (initial_search_state : Search.SearchState) :
    Option (Search.partial_Solution initial_search_state.plan) := do
  let _ := initial_search_state.step_decidable
  let _ := initial_search_state.steps_beq
  let _ := initial_search_state.step_hashable
  let _ := initial_search_state.plan.prop_decidable
  let _ := initial_search_state.plan.prop_repr

  -- Initialize the search with the initial state
  let mut known_steps := initial_search_state.known_steps

  -- The heuristic buckets of steps to explore.
  -- Higher heuristic buckets are explored first; within a bucket we preserve FIFO order.
  let mut steps_to_explore : HeuristicBuckets initial_search_state :=
    bucketize_steps initial_search_state initial_search_state.steps_to_consider

  -- Main search loop, iterates until a solution is found or no more states to explore
  -- Loop sctructure: take a step from the list, check whether it achieves the goal,
  -- (if so, return the solution),
  -- otherwise, generate new states by applying all possible actions,
  -- add the explored step to known states,
  repeat
    -- If the list can be expressed as head :: tail, proceed

    match pop_next_step? initial_search_state steps_to_explore with
    | none =>
      none
    | some (cur_step, tailBuckets) =>
      -- Update the buckets of steps to explore
      steps_to_explore := tailBuckets

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
