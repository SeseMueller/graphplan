import Graphplan.Basic
import Graphplan.FileParse
import Graphplan.Search.Basic
import Graphplan.Search.Linear
import Graphplan.Search.Graphplan

-- We use the definition in the Basic module to construct the example
-- for a STRIPS planning problem from the Wikipedia article on STRIPS.

-- The enum of positional variables
inductive Position
  | A
  | B
  | C
  deriving DecidableEq, Repr, Fintype
def Position.all : List Position := [Position.A, Position.B, Position.C]

-- Whether the monkey is currently high or low
inductive Height
  | High
  | Low
  deriving DecidableEq, Repr, Fintype
def Height.all : List Height := [Height.High, Height.Low]

-- The Enum of propositional variables
inductive MonkeyBoxProp
  | At (p : Position) -- The monkey is at position p
  | BoxAt (p : Position) -- The box is at position p
  | BananaAt (p : Position) -- The banana is at position p
  | Level (h : Height) -- The monkey is at height h
  | HasBanana -- The monkey has the banana
  deriving DecidableEq, Repr, Fintype

open MonkeyBoxProp Position Height STRIPS

-- The Move Operator. Requires the monkey to be low and at some position p1.
def Move (p1 : Position) (p2 : Position) : STRIPS_Operator MonkeyBoxProp where
  preconditions := {At p1, Level Low}
  neg_preconditions := {}
  add_effects := {At p2}
  del_effects := {At p1}

-- The ClimbUp Operator. Requires the monkey to be at the same position as the box and be low.
def ClimbUp (p : Position) : STRIPS_Operator MonkeyBoxProp where
  preconditions := {At p, BoxAt p, Level Low}
  neg_preconditions := {}
  add_effects := {Level High}
  del_effects := {Level Low}

-- The ClimbDown Operator. Requires the monkey to be high (and at the same position as the box).
def ClimbDown (p : Position) : STRIPS_Operator MonkeyBoxProp where
  preconditions := {At p, BoxAt p, Level High}
  neg_preconditions := {}
  add_effects := {Level Low}
  del_effects := {Level High}

-- The MoveBox Operator. Requires the monkey to be low and at the same position as the box.
def MoveBox (p1 : Position) (p2 : Position) : STRIPS_Operator MonkeyBoxProp where
  preconditions := {At p1, BoxAt p1, Level Low}
  neg_preconditions := {}
  add_effects := {BoxAt p2, At p2}
  del_effects := {BoxAt p1, At p1}

-- The TakeBananas Operator. Requires the monkey to be high and at the same position as the bananas.
def TakeBananas (p : Position) : STRIPS_Operator MonkeyBoxProp where
  preconditions := {At p, BananaAt p, Level High}
  neg_preconditions := {}
  add_effects := {HasBanana}
  del_effects := {}


-- -- Because the actions have free variables (the positions),
-- -- we need to instantiate them for all possible values.
-- def All_MonkeyBox_Actions :  (STRIPS_Operator MonkeyBoxProp) :=
--   { m : STRIPS_Operator MonkeyBoxProp | ∃ p1 p2 : Position, m = Move p1 p2 } ∪
--   { m : STRIPS_Operator MonkeyBoxProp | ∃ p : Position, m = ClimbUp p } ∪
--   { m : STRIPS_Operator MonkeyBoxProp | ∃ p : Position, m = ClimbDown p } ∪
--   { m : STRIPS_Operator MonkeyBoxProp | ∃ p1 p2 : Position, m = MoveBox p1 p2 } ∪
--   { m : STRIPS_Operator MonkeyBoxProp | ∃ p : Position, m = TakeBananas p }

-- The definition changed, we need it as an Array now (Set membership is not decidable)
-- So to make it easier, we just construct the array directly.
def All_MonkeyBox_Actions : Array (STRIPS_Operator MonkeyBoxProp × String) :=
  let out_array := Id.run do
    let mut arr := #[]
    -- Add all Move actions
    for p1 in Position.all do
      for p2 in Position.all do
        if p1 ≠ p2 then
          arr := arr.push (Move p1 p2, s!"Move {repr p1} {repr p2}")
    -- Add all ClimbUp actions
    for p in Position.all do
      arr := arr.push (ClimbUp p, s!"ClimbUp {repr p}")
    -- Add all ClimbDown actions
    for p in Position.all do
      arr := arr.push (ClimbDown p, s!"ClimbDown {repr p}")
    -- Add all MoveBox actions
    for p1 in Position.all do
      for p2 in Position.all do
        if p1 ≠ p2 then
          arr := arr.push (MoveBox p1 p2, s!"MoveBox {repr p1} {repr p2}")
    -- Add all TakeBananas actions
    for p in Position.all do
      arr := arr.push (TakeBananas p, s!"TakeBananas {repr p}")
    arr
  out_array

-- Returns the canonical name of an action
def action_name (op : STRIPS_Operator MonkeyBoxProp) : Option String :=
  let found := All_MonkeyBox_Actions.find? (fun x => x.fst = op)
  found.map (fun x => x.snd)

-- The complete STRIPS planning problem for the monkey and bananas example.
def MonkeyBox_STRIPS_Plan : STRIPS_Plan MonkeyBoxProp where
  prop_decidable := instDecidableEqMonkeyBoxProp
  prop_repr := instReprMonkeyBoxProp
  Actions := All_MonkeyBox_Actions.map (fun x => x.fst)
  current_state := {At A, BoxAt B, BananaAt C, Level Low}
  goal_states := {{HasBanana}}
  prop_hashable := by {
    refine { hash := ?_ }
    intro p
    match p with
    | At A => exact 1
    | At B => exact 2
    | At C => exact 3
    | BoxAt A => exact 4
    | BoxAt B => exact 5
    | BoxAt C => exact 6
    | BananaAt A => exact 7
    | BananaAt B => exact 8
    | BananaAt C => exact 9
    | Level Low => exact 10
    | Level High => exact 11
    | HasBanana => exact 12
  }

-- The same example, but using the DSL operator `>-`
def Example_Simulation_End_state_DSL : STRIPS_Plan MonkeyBoxProp :=
  MonkeyBox_STRIPS_Plan
  >- Move A B
  >- MoveBox B C
  >- ClimbUp C
  >- TakeBananas C

#eval Search.is_valid_plan Example_Simulation_End_state_DSL []

def main : IO Unit := do
  IO.println file_parse_result


-- The list of actions defined above
def solution_actions : List (STRIPS_Operator MonkeyBoxProp) :=
  [ Move A B,
    MoveBox B C,
    ClimbUp C,
    TakeBananas C
  ]

#eval Search.is_valid_plan MonkeyBox_STRIPS_Plan solution_actions

-- Apply the linear search to the MonkeyBox_STRIPS_Plan
def initial_search_state := Search.mk_search_state MonkeyBox_STRIPS_Plan

-- def solution := linear_search initial_search_state
def solution := linear_search_proved initial_search_state
-- def solution := graphplan_search initial_search_state

def solution_repr :=
  let _ := initial_search_state.plan.prop_repr
  let op_rep : Repr (STRIPS_Operator MonkeyBoxProp) := by infer_instance
  let _ : Repr (List (STRIPS_Operator MonkeyBoxProp)) := instReprList
  solution.map (fun sol => sol.actions.map (fun op => repr op))

def new_solution_actions :=
  solution.map (fun sol => sol.actions)

#eval Search.is_valid_plan MonkeyBox_STRIPS_Plan new_solution_actions.get!

def solution_names :=
  solution.map (fun sol =>
    sol.actions.map (fun op =>
      match action_name op with
      | some name => name
      | none => "Unknown Action"))

#eval solution_names
