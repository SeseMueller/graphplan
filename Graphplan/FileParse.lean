import Graphplan.Basic

import Regex

-- This file is responsible for parsing STRIPS planning problems from files.
-- We'll handle the file as a string.


set_option linter.style.longLine false

def example_input : String := "Initial state: At(Tower1), BlockAt(A, Tower1), BlockAt(D, Tower1), On(D, A), OnBottom(A), OnTop(D), BlockAt(B, Tower2), BlockAt(C, Tower2), On(B, C), OnBottom(C), OnTop(B), Empty(Tower3)
Goal state:     On(A, B), On(B, C), OnTop(A), OnBottom(C)

Actions:
        Go(From, To)
        Preconditions: At(From), !At(To)
        Postconditions: At(To), !At(From)

        PlaceOn(Block1, Block2, Tower)
        Preconditions: At(Tower), Holding(Block1), BlockAt(Block2, Tower), OnTop(Block2)
        Postconditions: !Holding(Block1), !OnTop(Block2), BlockAt(Block1, Tower), OnTop(Block1), On(Block1, Block2)

        PlaceOnEmpty(Block1, Tower)
        Preconditions: At(Tower), Holding(Block1), Empty(Tower)
        Postconditions: !Holding(Block1), OnTop(Block1), BlockAt(Block1, Tower), OnBottom(Block1), !Empty(Tower)

        PickUp(Block1, Block2, Tower)
        Preconditions: At(Tower), OnTop(Block1), BlockAt(Block1, Tower), BlockAt(Block2, Tower), On(Block1, Block2)
        Postconditions: Holding(Block1), !OnTop(Block1), !BlockAt(Block1, Tower), !On(Block1, Block2), OnTop(Block2)

        PickUpLast(Block1, Tower)
        Preconditions: At(Tower), BlockAt(Block1, Tower), OnTop(Block1), OnBottom(Block1)
        Postconditions: Holding(Block1), !BlockAt(Block1, Tower), !OnTop(Block1), !OnBottom(Block1), Empty(Tower)"


-- Helper function for splitting while respecting parantheses
def split_commas_respecting_parens (state : String) : List String :=
let returnval := do
  let mut result : List String := []
  let mut current_literal := ""
  let mut paren_count := 0
  for c in state.toList do
    if c = '(' then
      paren_count := paren_count + 1
      current_literal := current_literal.push c
    else if c = ')' then
      paren_count := paren_count - 1
      current_literal := current_literal.push c
    else if c = ',' ∧ paren_count = 0 then
      result := result.concat current_literal.trim
      current_literal := ""
    else
      current_literal := current_literal.push c
  -- Add the last literal if not empty
  if current_literal ≠ "" then
    result := result.concat current_literal.trim
  result
returnval

-- Helper function for parsing a single condition into a name and list of parameters.
def parse_condition (condition : String) : (String × List String) :=
  match condition.split (fun c => c = '(' ∨ c = ')') with
    | [name_part, params_part, ""] =>
      let params := params_part.splitOn "," |>.map String.trim
      (name_part.trim, params)
    | _ => panic! "Condition definition not formatted correctly, expected 'Name(param1, param2)', but got: " ++ condition


-- First function: split the string into the three components:
-- Initial State, Goal State, and Actions.
def parse_strips_file (file_content : String) : (List String × List String × List (String × String × String)) :=
  -- I would really like to use a String.splitOnce, because \n\n is part of the Actions too.
  -- Instead, I just expect (for now) for the file to be formatted correctly.

  let lines := file_content.splitOn "\n"
  -- The initial state is expected to be on the first line.
  let first_and_rest_lines := lines.next?
  let initial_state_splitted :=
    -- Remove the "Initial state: " prefix
    match first_and_rest_lines with
    | some (line, _rest_lines) => (line.splitOn ": ").tail
    | none => panic! "File is empty, expected initial state line."
  -- Extract the (hopefully only) element from the tail
  -- let initial_state :=
  --   match initial_state_splitted with
  --   | [state] => (state.splitOn ",").map String.trim
  --   | _ => panic! "Initial state line not formatted correctly.\
  --   Expected 'Initial state: ...' followed by the state literals separated by commas."

  -- The above code sadly matches on "(A, B)", which is not what we want.
  -- We need to respect the parantheses.
  let initial_state :=
    match initial_state_splitted with
    | [state] =>
      split_commas_respecting_parens state
    | _ => panic! "Initial state line not formatted correctly.\
    Expected 'Initial state:    ...' followed by the state literals separated by commas."

  -- That is the first part, the initial state, done.
  -- The goal state is on the next line.

  let second_line :=
    match first_and_rest_lines with
    | some (_, rest_lines) =>
      match rest_lines.next? with
      | some (line, _rest_lines2) => line
      | none => panic! "File ended unexpectedly, expected goal state line.\
      (Does the file have at least two lines?)"
    | none => panic! "File is empty, expected initial state line."

  let goal_state_splitted :=
    -- Remove the "Goal state: " prefix
    (second_line.splitOn ": ").tail
  let goal_state :=
    match goal_state_splitted with
    -- | [state] => (state.splitOn ",").map String.trim
    | [state] =>
      split_commas_respecting_parens state
    | _ => panic! "Goal state line not formatted correctly.\
    Expected 'Goal state:    ...' followed by the goal literals separated by commas."

  -- Finally, the actions are all the remaining lines.
  -- (Note that there is a blank line between the goal state and the actions.)

  -- Thus, the actions start from the fifth line (index 4).
  let actions_lines := do
    match first_and_rest_lines with
    | some (_, second_lines) =>
      let mut lines_iter := second_lines
      -- Skip the goal state line (1) and the blank line (1)
      lines_iter := match lines_iter.next? with | some (_, rest) => rest | none => panic! "File ended unexpectedly, expected actions."
      lines_iter := match lines_iter.next? with | some (_, rest) => rest | none => panic! "File ended unexpectedly, expected actions."
      lines_iter := match lines_iter.next? with | some (_, rest) => rest | none => panic! "File ended unexpectedly, expected actions."
      -- Now lines_iter should start from the actions
      lines_iter.map String.trim
    | none => panic! "File is empty, expected initial state line."


  -- To actually get the actions, we need to split the action lines by \n\n
  -- and then remove the preconditions and postconditions from their lines.
  let actions :=
    let actions_str := String.intercalate "\n" actions_lines
    let action_blocks := actions_str.splitOn "\n\n"
    let action_blocks_trimmed := action_blocks.map String.trim
    -- Now we need to make sure there are exactly three lines, and remove the prefixes.
    action_blocks_trimmed.map fun block =>
      let block_lines := block.splitOn "\n"
      match block_lines with
      | [action_line, preconditions_line, postconditions_line] =>
        let action_name := action_line.trim
        let preconditions :=
          let preconditions_splitted := (preconditions_line.splitOn ": ").tail
          match preconditions_splitted with
          | [conds] => conds.trim
          | _ => panic! "Preconditions line not formatted correctly for action: " ++ action_name
        let postconditions :=
          let postconditions_splitted := (postconditions_line.splitOn ": ").tail
          match postconditions_splitted with
          | [conds] => conds.trim
          | _ => panic! "Postconditions line not formatted correctly for action: " ++ action_name
        (action_name, preconditions, postconditions)
      | _ => panic! "Action block not formatted correctly. Expected three lines per action. Found: " ++ block



  (initial_state, goal_state, actions)


-- Next, we need to extract the names of all Actions and props. Actions first.
def names_of_actions (actions : List (String × String × String)) : List String :=
  let defs := actions.map fun (name, _, _) => name
  -- The name of the action is what comes before the first '('
  defs.map fun d =>
    match d.splitOn "(" with
    | [name_part, _] => name_part.trim
    | _ => panic! "Action definition not formatted correctly: " ++ d


-- Next, we need to extract the names of all variables.
-- We do this by finding all closed parantheses in the first two lines,
-- and extracting the var name from there. (The first two lines contain the initial and goal states.)
def names_of_vars (line_content : String) : Array String :=
  -- We use Regex to find all occurrences of the pattern "(...)" in the file content."

  let pattern := re! "\\(([^()]+)\\)"
  let matchs := (pattern.captureAll line_content).map (·.get 1)
  -- The matchs contain the startPos and stopPos of each match.
  -- We extract the matched strings.
  -- First filter out none matches.
  let filtered_matchs := matchs.filterMap id
  let var_lists := filtered_matchs.map (fun m => m.str.extract m.startPos m.stopPos)

  -- Each item in var_lists is now a string like "A" or "B, A, Tower1".
  -- We need to split by commas and trim.
  let vars := var_lists.map (fun pl =>
    (((pl.splitOn ", ").toArray).map String.trim))

  -- Now we need to flatten the list of lists.
  let vars_list := vars.flatten

  -- Lastly, we need to remove duplicates. Sadly, Array doesn't have a dedup method.
  -- But List has, so we convert to List and back.
  let vars_dedup := (vars_list.toList).dedup

  vars_dedup.toArray
  -- Yes, this is inefficient, but this is only the parsing,
  -- so because it's still polynomial time, it's acceptable.


-- Next, we need to write a parser that extracts the positive and negative (pre/post)conditions from the strings.
def parse_conditions_pos_neg (conditions_str : String) : (List String × List String) :=
  -- The conditions are separated by commas.
  let conditions := split_commas_respecting_parens conditions_str
  -- Now, we separate positive and negative conditions.
  let (pos, neg) := Id.run do
    let mut pos_conditions : List String := []
    let mut neg_conditions : List String := []
    for cond in conditions do
      if cond.startsWith "!" then
        neg_conditions := neg_conditions.concat (cond.drop 1).trim
      else
        pos_conditions := pos_conditions.concat cond.trim
    (pos_conditions, neg_conditions)
  (pos, neg)



-- Now we apply that to the actions parsed from the file, returning a 2x2 tuple of Lists, containing the positive and negative preconditions and postconditions.
def parse_actions_conditions (actions : List (String × String × String)) :
  List (String × (List String × List String) × (List String × List String)) :=
  actions.map fun (name, preconds_str, postconds_str) =>
    let (pre_pos, pre_neg) := parse_conditions_pos_neg preconds_str
    let (post_pos, post_neg) := parse_conditions_pos_neg postconds_str
    (name, (pre_pos, pre_neg), (post_pos, post_neg))


-- We also need a function to generate the lean function corresponsing to a single action.
-- Note that a bound variable is expressed by having it names like a known prop.
def action_to_lean_code (action : String × (List String × List String) × (List String × List String))
(known_vars : List String) (var_name : String) (prop_name : String) : String :=
  -- The output should look like this:
-- def ClimbUp (p : <PROPNAME>) : STRIPS_Operator MonkeyBoxProp where
--   preconditions := {At p, BoxAt p, Low}
--   neg_preconditions := {}
--   add_effects := {High}
--   del_effects := {Low}

  let (name, (pre_pos, pre_neg), (post_pos, post_neg)) := action

  -- The proper name of the action, and the parameters.
  let (name_only, free_params) := parse_condition name

  -- Now, we need to convert the preconditions and postconditions to proper Lean code.
  -- From a list of conditions like ["At(p)", "BoxAt(p)", "Low"], we need to generate
  -- the set of conditions and effects, like {At p, BoxAt p, Low}.
  let format_conditions (conds : List String) : String :=
    if conds.isEmpty then
      "{}"
    else
      let parsed_conds := conds.map parse_condition
      let conds_code := parsed_conds.map fun (cond_name, cond_params) =>
        -- It should be enough to just join the name and parameters with spaces.
        let params_code := String.intercalate " " cond_params
        let name_and_params :=
          if cond_params.isEmpty then
            cond_name
          else
            cond_name ++ " " ++ params_code
        name_and_params
      "{ " ++ String.intercalate ", " conds_code ++ " }"

  -- Now, crucially, we need to drop all known props from the free_params.
  let free_params_filtered := free_params.filter fun p => ¬ known_vars.contains p

  -- This ensures that only actual free variables are included as parameters.

  let returnval := Id.run do
    let mut code : String := "def"
    code := code ++ " " ++ name_only
    -- Add parameters if any.
    let param_list :=
      if free_params_filtered.isEmpty then
        ""
      else
      let param_list := free_params_filtered.map fun p => "(" ++ p ++ " : " ++ var_name ++ ")"
      " " ++ String.intercalate " " param_list
    code := code ++ param_list
    code := code ++ " : STRIPS_Operator " ++ prop_name ++ " where\n"
    -- Now, in order, the preconditions, neg_preconditions, add_effects, del_effects.
    code := code ++ "  preconditions := " ++ format_conditions pre_pos ++ "\n"
    code := code ++ "  neg_preconditions := " ++ format_conditions pre_neg ++ "\n"
    code := code ++ "  add_effects := " ++ format_conditions post_pos ++ "\n"
    code := code ++ "  del_effects := " ++ format_conditions post_neg ++ "\n"
    code

  returnval

-- Lastly, we need to parse the propositions, in that we need to know which props there are
-- and how many parameters they have. By construction, all props need to be on the first two lines
-- of the file (initial and goal states).
def extract_props_with_params (line_content : String) : Array (String × Nat) :=
  let pattern := re! "([A-Za-z0-9_]+)\\(([^()]+)\\)"
  let matchs := (pattern.captureAll line_content).map (·.get 0)
  -- The matchs contain the startPos and stopPos of each match.
  -- We extract the matched strings.
  -- First filter out none matches.
  let filtered_matchs := matchs.filterMap id
  let prop_lists := filtered_matchs.map (fun m => m.str.extract m.startPos m.stopPos)

  -- Each item in prop_lists is now a string like "At(A)" or "On(A, B)".
  -- We need to parse them into (name, number_of_params).
  let props_with_params := prop_lists.map fun pl =>
    let (name, params) := parse_condition pl
    (name, params.length)

  -- Lastly, we need to remove duplicates.
  let props_dedup := (props_with_params.toList).dedup
  props_dedup.toArray


def parsed_example := parse_strips_file example_input

-- #eval parsed_example

-- #eval names_of_actions (parsed_example).2.2

-- #eval names_of_vars (String.intercalate " " (parsed_example).1)

-- #eval parse_conditions_pos_neg (String.intercalate ", " (parsed_example).2.1)

-- #eval parse_actions_conditions (parsed_example).2.2

-- #eval extract_props_with_params (String.intercalate " " (parsed_example).1 ++ " " ++ String.intercalate " " (parsed_example).2.1)

-- At the end, we want to be able to output Lean source code to define the STRIPS planning problem from the file.

def file_to_lean (file_content : String) (file_name : String) : String :=
  -- First, parse the file.
  let (initial_state, goal_state, actions) := parse_strips_file file_content

  let parsed_actions := parse_actions_conditions actions

  -- For further processing, we need everything that could contain conditions.
  let candidate_strings := String.intercalate " " (initial_state ++ goal_state) ++ " " ++
    (String.intercalate " " (actions.map fun (_, pre, post) => pre ++ " " ++ post))

  -- The names of the variables.
  let var_names := names_of_vars (String.intercalate " " (initial_state ++ goal_state))
  -- let var_names := names_of_vars candidate_strings

  -- The name of the inductive type for the props.
  let prop_type_name := file_name ++ "Prop"
  -- The name of the inductive type for the variables.
  let var_type_name := file_name ++ "Var"


  -- We can start to generate the code here.
  let lean_code := Id.run do

    -- At the very top, the imports.
    let mut code : String := "import Graphplan.Basic\nimport Mathlib.Tactic.DeriveFintype\n\n"

    -- The vars as an inductive type.
    code := code ++ "inductive " ++ var_type_name ++ " \n"
    -- Add all vars as constructors.
    for var_name in var_names do
      code := code ++ "  | " ++ var_name ++ "\n"

    -- Add the "deriving DecidableEq, Repr, Fintype" line.
    code := code ++ "  deriving DecidableEq, Repr, Fintype\n"

    -- Then, the props as an inductive type.
    -- Note that some of them can have parameters.
    -- let props_with_params := extract_props_with_params (String.intercalate " " (initial_state ++ goal_state))
    let props_with_params := extract_props_with_params candidate_strings

    -- Same for actions, just take their names.
    let actions_with_params := extract_props_with_params (String.intercalate ", " (actions.map fun (name, _, _) => name))

    let mut props_code : String := "inductive " ++ prop_type_name ++ " \n"
    for (name, param_count) in props_with_params do
      -- props_code := props_code ++ "  | " ++ name ++ (if param_count > 0 then "(" ++ String.intercalate ", " (List.range param_count |>.map (fun i => "P" ++  (i.toDigits 10))) ++ ")" else "") ++ "\n"
      props_code := props_code ++ "  | " ++ name
      if param_count > 0 then
        let param_list := List.range param_count |>.map (fun i => "p" ++ (i.repr))
        props_code := props_code ++ "(" ++ String.intercalate " " param_list ++ " : " ++ var_type_name ++ ")"
      props_code := props_code ++ "\n"
    props_code := props_code ++ "  deriving DecidableEq, Repr, Fintype\n"

    code := code ++ "\n" ++ props_code ++ "\n"

    code := code ++ "\nopen " ++ prop_type_name ++ " " ++ var_type_name ++ " STRIPS\n\n"

    -- Now, add all actions as functions.
    for action in parsed_actions do
      let action_code := action_to_lean_code action var_names.toList var_type_name prop_type_name
      code := code ++ action_code ++ "\n\n"

    -- Second last thing: the set of all actions.
    -- Basically, take all Actions, and construct:
    -- { e : STRIPS_Operator SimpleBlocksProp | ∃ p1 p2 : SimpleBlocksVar, m = Actionname p1 p2 }
    let mapped_props := actions_with_params.map fun (name, param_count) =>
      if param_count = 0 then
        "{ m : STRIPS_Operator " ++ prop_type_name ++ " | m = " ++ name ++ " }"
      else
        let param_list := List.range param_count |>.map (fun i : ℕ => "p" ++ (i.repr))
        "{ m : STRIPS_Operator " ++ prop_type_name ++ " | ∃ " ++
        String.intercalate " " param_list ++ " : " ++ var_type_name ++
        ", m = " ++ name ++ " " ++ String.intercalate " " param_list ++ " }"

    -- Combine them all using ∪
    let all_actions_set := String.intercalate " ∪\n  " mapped_props.toList

    code := code ++ "def All_" ++ file_name ++ "_Actions : Set (STRIPS_Operator " ++ prop_type_name ++ ") :=\n  " ++ all_actions_set ++ "\n\n"

    -- Lastly, the complete STRIPS planning problem.
    -- We first need to construct the current_state as a list of props. and the goal_states as a set of list of props.

    -- For that, we basically need to run parse_condition on each condition in the initial_state and goal_state.
    let parsed_initial_state := (initial_state.map fun cond =>
      let (name, params) := (parse_condition cond)
      -- This should just be the name and parameters joined with spaces.
      let params_code := String.intercalate " " params
      if params.isEmpty then
        name
      else
        name ++ " " ++ params_code
      )
    let parsed_goal_state := (goal_state.map fun cond =>
      -- Same as above
      let (name, params) := (parse_condition cond)
      let params_code := String.intercalate " " params
      if params.isEmpty then
        name
      else
        name ++ " " ++ params_code
      )
    -- TODO!: As per the python standard, this STRIPS does not support multiple goal states.

    -- Finally, construct the STRIPS_Plan definition.
    code := code ++ "def " ++ file_name ++ "_STRIPS_Plan : STRIPS_Plan where\n"
    code := code ++ "  Props := " ++ prop_type_name
    code := code ++ "\n  prop_decidable := instDecidableEq" ++ prop_type_name ++ "\n" -- Auto-generated decidable instance
    code := code ++ "  Actions := All_" ++ file_name ++ "_Actions\n"
    code := code ++ "  current_state := { " ++ String.intercalate ", " parsed_initial_state ++ " }\n"
    code := code ++ "  goal_states := {{ " ++ String.intercalate ", " parsed_goal_state ++ " }}\n"

    code

  lean_code


def file_parse_result := (file_to_lean example_input "SimpleBlocks")

-- #eval file_parse_result
