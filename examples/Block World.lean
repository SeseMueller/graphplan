import Graphplan.Basic
import Mathlib.Tactic.DeriveFintype
import Graphplan.Search.Linear


inductive BWBlock
  | A
  | B
  | C
  deriving DecidableEq, Repr, Fintype, Hashable

def BWBlock.all : List BWBlock :=
[BWBlock.A, BWBlock.B, BWBlock.C]

inductive BWPos
  | x
  | y
  | z
  deriving DecidableEq, Repr, Fintype, Hashable

def BWPos.all : List BWPos :=
[BWPos.x, BWPos.y, BWPos.z]

inductive BWVar
  | Block (b : BWBlock)
  | Table
  | Pos (p : BWPos)
  deriving DecidableEq, Repr, Fintype, Hashable

open BWBlock BWPos BWVar

def BWVar.all : List BWVar :=
  let outlist := Id.run do
    let mut vars : List BWVar := [BWVar.Table]
    for b in BWBlock.all do
      vars := vars.concat (BWVar.Block b)
    for p in BWPos.all do
      vars := vars.concat (BWVar.Pos p)
    vars

  outlist

inductive BWProp
  | On(b: BWBlock) (p : BWVar)
  | Clear(p0 : BWVar)
  deriving DecidableEq, Repr, Fintype, Hashable


open BWProp BWVar STRIPS

def Move (blk : BWBlock) (From To : BWVar) :
STRIPS_Operator BWProp where
  preconditions := { On blk From, Clear (Block blk), Clear To }
  neg_preconditions := {}
  add_effects := { On blk To, Clear From }
  del_effects := { On blk From, Clear To }


def MoveToTable (blk : BWBlock) (From : BWVar) :
STRIPS_Operator BWProp where
  preconditions := { On blk From, Clear (Block blk) }
  neg_preconditions := {}
  add_effects := { On blk Table, Clear From }
  del_effects := { On blk From }

def All_SimpleBlocks_Actions : Array (STRIPS_Operator BWProp × String) :=
  let outarray := Id.run do
    let mut actions : Array (STRIPS_Operator BWProp × String) := #[]

    for b in BWBlock.all do
      for p1 in BWVar.all do
        for p2 in BWVar.all do
          actions := actions.push ((Move b p1 p2), s!"Move {repr b} from {repr p1} to {repr p2}")
      for p in BWVar.all do
        if p != Table then
          actions := actions.push ((MoveToTable b p), s!"Move {repr b} to Table")
    actions

  outarray

def SimpleBlocks_STRIPS_Plan : STRIPS_Plan BWProp where
  prop_decidable := instDecidableEqBWProp
  Actions := All_SimpleBlocks_Actions.map (fun x => x.fst)
  prop_hashable := instHashableBWProp
  prop_repr := instReprBWProp

  current_state :=
    [ On A Table,
      On B Table,
      On C Table,
      Clear (Block A),
      Clear (Block B),
      Clear (Block C),
    ]
  goal_states :=
    [ [ On A (Block B), On B (Block C) ] ]


-- Returns the canonical name of an action
def action_name (op : STRIPS_Operator BWProp) : Option String :=
  let found := All_SimpleBlocks_Actions.find? (fun x => x.fst = op)
  found.map (fun x => x.snd)


-- Now use linear search to solve the planning problem
def initial_search_state := Search.mk_search_state SimpleBlocks_STRIPS_Plan
def solution :=
  linear_search initial_search_state


def solution_repr :=
  let _ := initial_search_state.plan.prop_repr
  let op_rep : Repr (STRIPS_Operator BWProp) := by infer_instance
  let _ : Repr (List (STRIPS_Operator BWProp)) := instReprList
  solution.map (fun sol => sol.actions.map (fun op => repr op))

def solution_names :=
  solution.map (fun sol =>
    sol.actions.map (fun op =>
      match action_name op with
      | some name => name
      | none => "Unknown Action"))

#eval solution_names

#eval solution.map (fun sol => sol.actions.length)



-- Sussman Anomaly example
def SussmanAnomaly_STRIPS_Plan : STRIPS_Plan BWProp where
  prop_decidable := instDecidableEqBWProp
  Actions := All_SimpleBlocks_Actions.map (fun x => x.fst)
  prop_hashable := instHashableBWProp
  prop_repr := instReprBWProp
  current_state :=
    [ On A Table,
      On B Table,
      On C (Block A),
      Clear (Block B),
      Clear (Block C),
    ]
  goal_states :=
    [ [ On A (Block B), On B (Block C) ] ]

-- Now use linear search to solve the planning problem
def initial_search_state_Sussman := Search.mk_search_state SussmanAnomaly_STRIPS_Plan
def solution_Sussman :=
  linear_search initial_search_state_Sussman

def solution_Sussman_names :=
  solution_Sussman.map (fun sol =>
    sol.actions.map (fun op =>
      match action_name op with
      | some name => name
      | none => "Unknown Action"))

#eval solution_Sussman_names
#eval solution_Sussman.map (fun sol => sol.actions.length)
