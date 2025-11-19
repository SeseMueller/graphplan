import Graphplan.Basic
import Mathlib.Tactic.DeriveFintype
import Graphplan.Search.Linear


inductive ACTAirport
  | JFK
  | SFO
  deriving DecidableEq, Repr, Fintype, Hashable

def ACTAirport.all : List ACTAirport :=
[ACTAirport.JFK, ACTAirport.SFO]

inductive ACTCargo
  | C1
  | C2
  deriving DecidableEq, Repr, Fintype, Hashable

def ACTCargo.all : List ACTCargo :=
[ACTCargo.C1, ACTCargo.C2]

inductive ACTPlane
  | P1
  | P2
  deriving DecidableEq, Repr, Fintype, Hashable
def ACTPlane.all : List ACTPlane :=
[ACTPlane.P1, ACTPlane.P2]

inductive ACTVar
  | Airport (a : ACTAirport)
  | Plane (p : ACTPlane)
  | Cargo (c : ACTCargo)
  deriving DecidableEq, Repr, Fintype, Hashable

open ACTAirport ACTPlane ACTCargo ACTVar

def ACTVar.all : List ACTVar :=
  let outlist := Id.run do
    let mut vars : List ACTVar := []
    for a in ACTAirport.all do
      vars := vars.concat (ACTVar.Airport a)
    for p in ACTPlane.all do
      vars := vars.concat (ACTVar.Plane p)
    for c in ACTCargo.all do
      vars := vars.concat (ACTVar.Cargo c)
    vars

  outlist

inductive ACTProp
  | At (x : ACTVar) (a : ACTAirport) -- Cargo c/Plane p is at airport a
  | In (c : ACTCargo) (p : ACTPlane) -- Cargo c is in plane p
  deriving DecidableEq, Repr, Fintype, Hashable
  -- Empty should be derivable automatically


open ACTProp ACTVar STRIPS

def Load (c : ACTCargo) (p : ACTPlane) (a : ACTAirport) :
STRIPS_Operator ACTProp where
  preconditions := { At (Cargo c) a, At (Plane p) a }
  neg_preconditions := {}
  add_effects := { In c p }
  del_effects := { At (Cargo c) a }

def Unload (c : ACTCargo) (p : ACTPlane) (a : ACTAirport) :
STRIPS_Operator ACTProp where
  preconditions := { In c p, At (Plane p) a }
  neg_preconditions := {}
  add_effects := { At (Cargo c) a }
  del_effects := { In c p }

def Fly (p : ACTPlane) (f t : ACTAirport) : -- (both from and to are reserved words)
STRIPS_Operator ACTProp where
  preconditions := { At (Plane p) f }
  neg_preconditions := {}
  add_effects := { At (Plane p) t }
  del_effects := { At (Plane p) f }

def All_ACT_Actions : Array (STRIPS_Operator ACTProp × String) :=
  let outarray := Id.run do
    let mut actions : Array (STRIPS_Operator ACTProp × String) := #[]
    for c in ACTCargo.all do
      for p in ACTPlane.all do
        for a in ACTAirport.all do
          actions := actions.push (Load c p a, s!"Load {repr c} {repr p} {repr a}")
          actions := actions.push (Unload c p a, s!"Unload {repr c} {repr p} {repr a}")
    for p in ACTPlane.all do
      for f in ACTAirport.all do
        for t in ACTAirport.all do
          if f ≠ t then
            actions := actions.push (Fly p f t, s!"Fly {repr p} from {repr f} to {repr t}")
    actions
  outarray

def ACT_STRIPS_Plan : STRIPS_Plan where
  Props := ACTProp
  prop_decidable := instDecidableEqACTProp
  Actions := All_ACT_Actions.map (fun x => x.fst)
  prop_hashable := instHashableACTProp
  prop_repr := instReprACTProp

  current_state :=
    [ At (Cargo ACTCargo.C1) ACTAirport.SFO,
      At (Cargo ACTCargo.C2) ACTAirport.JFK,
      At (Plane ACTPlane.P1) ACTAirport.SFO,
      At (Plane ACTPlane.P2) ACTAirport.JFK
    ]
  goal_states :=
    [ [ At (Cargo ACTCargo.C1) ACTAirport.JFK,
        At (Cargo ACTCargo.C2) ACTAirport.SFO
      ]
    ]


-- Returns the canonical name of an action
def action_name (op : STRIPS_Operator ACTProp) : Option String :=
  let found := All_ACT_Actions.find? (fun x => x.fst = op)
  found.map (fun x => x.snd)


-- Now use linear search to solve the planning problem
def initial_search_state := Search.mk_search_state ACT_STRIPS_Plan
def solution :=
  linear_search initial_search_state


def solution_repr :=
  let _ := initial_search_state.plan.prop_repr
  let op_rep : Repr (STRIPS_Operator initial_search_state.plan.Props) := by infer_instance
  let _ : Repr (List (STRIPS_Operator initial_search_state.plan.Props)) := instReprList
  solution.map (fun sol => sol.actions.map (fun op => repr op))

def solution_names :=
  solution.map (fun sol =>
    sol.actions.map (fun op =>
      match action_name op with
      | some name => name
      | none => "Unknown Action"))

#eval solution_names

#eval solution.map (fun sol => sol.actions.length)
