import Graphplan.Basic
import Mathlib.Tactic.DeriveFintype
import Graphplan.Search.Graphplan
import Graphplan.Search.Linear
import Graphplan.Search.Linear_Heuristic

-- This examples takes from the rocket_facts4 example from the graphplan paper:

inductive Place
  | London
  | Paris
  | JFK
  deriving DecidableEq, Repr, Fintype, Hashable
def Place.all : List Place := [Place.London, Place.Paris, Place.JFK]


inductive Rocket
  | Rocket1
  | Rocket2
  deriving DecidableEq, Repr, Fintype, Hashable
def Rocket.all : List Rocket := [Rocket.Rocket1, Rocket.Rocket2]

inductive Cargo
  | Alex
  | Jason
  | Pencil
  | Paper
  | Desk
  | Chair
  | Laptop
  deriving DecidableEq, Repr, Fintype, Hashable
def Cargo.all : List Cargo :=
  [Cargo.Alex, Cargo.Jason, Cargo.Pencil, Cargo.Paper, Cargo.Desk, Cargo.Chair, Cargo.Laptop]


inductive RocketVar
  | Place (p : Place)
  | Rocket (r : Rocket)
  | Cargo (c : Cargo)
  deriving DecidableEq, Repr, Fintype, Hashable

open Place Rocket Cargo RocketVar STRIPS

def RocketVar.all : List RocketVar :=
  let outlist := Id.run do
    let mut vars : List RocketVar := []
    for p in Place.all do
      vars := vars.concat (RocketVar.Place p)
    for r in Rocket.all do
      vars := vars.concat (RocketVar.Rocket r)
    for c in Cargo.all do
      vars := vars.concat (RocketVar.Cargo c)
    vars

  outlist

inductive RocketProp
  | At (r : RocketVar) (p : Place) -- Rocket/Cargo r is at place p
  | In (c : Cargo) (r : Rocket) -- Cargo c is in rocket r
  | HasFuel (r : Rocket) -- Rocket r has fuel
  deriving DecidableEq, Repr, Fintype, Hashable

open RocketProp RocketVar

def load (c : Cargo) (r : Rocket) (p : Place) :
STRIPS_Operator RocketProp where
  preconditions := {At (RocketVar.Cargo c) p, At (RocketVar.Rocket r) p}
  neg_preconditions := {}
  add_effects := {In c r}
  del_effects := {At (RocketVar.Cargo c) p}

def unload (c : Cargo) (r : Rocket) (p : Place) :
STRIPS_Operator RocketProp where
  preconditions := {In c r, At (RocketVar.Rocket r) p}
  neg_preconditions := {}
  add_effects := {At (RocketVar.Cargo c) p}
  del_effects := {In c r}

def move (r : Rocket) (p1 : Place) (p2 : Place) :
STRIPS_Operator RocketProp where
  preconditions := {At (RocketVar.Rocket r) p1, HasFuel r}
  neg_preconditions := {}
  add_effects := {At (RocketVar.Rocket r) p2}
  del_effects := {At (RocketVar.Rocket r) p1, HasFuel r}

def All_Actions : Array (STRIPS_Operator RocketProp × String) :=
  let outarray := Id.run do
    let mut actions : Array (STRIPS_Operator RocketProp × String) := #[]
    for c in Cargo.all do
      for r in Rocket.all do
        for p in Place.all do
          actions := actions.push (load c r p, s!"Load {repr c} into {repr r} at {repr p}")
          actions := actions.push (unload c r p, s!"Unload {repr c} from {repr r} at {repr p}")
    for r in Rocket.all do
      for p1 in Place.all do
        for p2 in Place.all do
          if p1 != p2 then
            actions := actions.push (move r p1 p2, s!"Move {repr r} from {repr p1} to {repr p2}")
    actions
  outarray


-- The whole plan
def Rocket_STRIPS_Plan : STRIPS_Plan where

    Props := RocketProp
    prop_decidable := by infer_instance
    prop_hashable := by infer_instance
    prop_repr := by infer_instance

    Actions := All_Actions.map (·.1)

    current_state :=
      { At (RocketVar.Cargo Cargo.Alex) Place.London,
        At (RocketVar.Cargo Cargo.Jason) Place.London,
        At (RocketVar.Cargo Cargo.Pencil) Place.London,
        At (RocketVar.Cargo Cargo.Paper) Place.London,
        At (RocketVar.Cargo Cargo.Desk) Place.London,
        At (RocketVar.Cargo Cargo.Chair) Place.London,
        At (RocketVar.Cargo Cargo.Laptop) Place.London,
        At (RocketVar.Rocket Rocket.Rocket1) Place.London,
        At (RocketVar.Rocket Rocket.Rocket2) Place.London,
        HasFuel Rocket.Rocket1,
        HasFuel Rocket.Rocket2
      }

    goal_states :=
      [ {
        At (RocketVar.Cargo Cargo.Alex) Place.Paris,
        At (RocketVar.Cargo Cargo.Jason) Place.JFK ,
        -- At (RocketVar.Cargo Cargo.Pencil) Place.Paris ,
        -- At (RocketVar.Cargo Cargo.Paper) Place.JFK,
        -- At (RocketVar.Cargo Cargo.Desk) Place.Paris,
        -- At (RocketVar.Cargo Cargo.Chair) Place.JFK,
        At (RocketVar.Cargo Cargo.Laptop) Place.Paris

        } ]

-- Returns the canonical name of an action
def action_name (op : STRIPS_Operator RocketProp) : Option String :=
  let found := All_Actions.find? (fun x => x.fst = op)
  found.map (fun x => x.snd)

-- Use Graphplan search to solve the Rocket_STRIPS_Plan
def initial_search_state := Search.mk_search_state Rocket_STRIPS_Plan
def solution := graphplan_search initial_search_state
-- def solution := heuristic_search initial_search_state
-- def solution := linear_search initial_search_state

set_option trace.profiler true

-- Is the solution valid?
def solution_valid :=
  match solution with
  | none => false
  | some sol => Search.is_valid_plan Rocket_STRIPS_Plan sol.actions
#eval solution_valid

set_option trace.profiler false


def solution_names :=
  solution.map (fun sol =>
    sol.actions.map (fun op =>
      match action_name op with
      | some name => name
      | none => "Unknown Action"))

-- #eval solution_names
#eval solution.map (fun sol => sol.actions.length)

-- The path the solution takes, as a list of states it "visits"
def solution_states :=
  match solution with
  | none => none
  | some sol =>
    let output := Id.run do
      let mut states : List (List RocketProp) := []
      let mut state := Rocket_STRIPS_Plan.current_state
      states := states.concat state
      for op in sol.actions do
        state := apply_action_if_applicable { Rocket_STRIPS_Plan with current_state := state } op
        states := states.concat state
      some states
    output

-- #eval solution_states
