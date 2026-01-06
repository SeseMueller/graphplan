import Graphplan.Basic
import Mathlib.Tactic.DeriveFintype
import Graphplan.Search.Graphplan
import Graphplan.Search.Linear
import Graphplan.Search.Linear_Heuristic

-- This examples takes from the rocket_facts4 example from the graphplan paper:

inductive Place
  | S -- Start
  | D1 -- Destination 1
  | D2 -- Destination 2
  deriving DecidableEq, Repr, Fintype, Hashable
def Place.all : List Place := [Place.S, Place.D1, Place.D2]


inductive Rocket
  | Rocket1
  | Rocket2
  deriving DecidableEq, Repr, Fintype, Hashable
def Rocket.all : List Rocket := [Rocket.Rocket1, Rocket.Rocket2]

-- inductive Cargo
--   | Alex
--   | Jason
--   | Pencil
--   | Paper
--   | Desk
--   | Chair
--   | Laptop
--   deriving DecidableEq, Repr, Fintype, Hashable
-- def Cargo.all : List Cargo :=
--   [Cargo.Alex, Cargo.Jason, Cargo.Pencil, Cargo.Paper, Cargo.Desk, Cargo.Chair, Cargo.Laptop]
def Cargo (n : Nat) := Fin n
  deriving DecidableEq, Repr, Fintype, Hashable
def Cargo.all (n : Nat) : List (Cargo n) := List.finRange n


inductive RocketVar (n : Nat)
  | Place (p : Place)
  | Rocket (r : Rocket)
  | Cargo (c : Cargo n)
  deriving DecidableEq, Repr, Fintype, Hashable

open Place Rocket Cargo RocketVar STRIPS

def RocketVar.all (n : Nat) : List (RocketVar n) :=
  let outlist := Id.run do
    let mut vars : List (RocketVar n) := []
    for p in Place.all do
      vars := vars.concat (RocketVar.Place p)
    for r in Rocket.all do
      vars := vars.concat (RocketVar.Rocket r)
    for c in Cargo.all n do
      vars := vars.concat (RocketVar.Cargo c)
    vars

  outlist

inductive RocketProp (n : Nat)
  | At (r : RocketVar n) (p : Place) -- Rocket/Cargo r is at place p
  | In (c : Cargo n) (r : Rocket) -- Cargo c is in rocket r
  | HasFuel (r : Rocket) -- Rocket r has fuel
  deriving DecidableEq, Repr, Fintype, Hashable

open RocketProp RocketVar

def load {n : Nat} (c : Cargo n) (r : Rocket) (p : Place) :
STRIPS_Operator (RocketProp n) where
  preconditions := {At (RocketVar.Cargo c) p, At (RocketVar.Rocket r) p}
  neg_preconditions := {}
  add_effects := {In c r}
  del_effects := {At (RocketVar.Cargo c) p}

def unload {n : Nat} (c : Cargo n) (r : Rocket) (p : Place) :
STRIPS_Operator (RocketProp n) where
  preconditions := {In c r, At (RocketVar.Rocket r) p}
  neg_preconditions := {}
  add_effects := {At (RocketVar.Cargo c) p}
  del_effects := {In c r}

def move {n : Nat} (r : Rocket) (p1 : Place) (p2 : Place) :
STRIPS_Operator (RocketProp n) where
  preconditions := {At (RocketVar.Rocket r) p1, HasFuel r}
  neg_preconditions := {}
  add_effects := {At (RocketVar.Rocket r) p2}
  del_effects := {At (RocketVar.Rocket r) p1, HasFuel r}

def All_Actions (n : Nat) : Array (STRIPS_Operator (RocketProp n) × String) :=
  let outarray := Id.run do
    let mut actions : Array (STRIPS_Operator (RocketProp n) × String) := #[]
    for c in Cargo.all n do
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
def Rocket_Problem (n : Nat) : STRIPS_Plan (RocketProp n) where

    prop_decidable := by infer_instance
    prop_hashable := by infer_instance
    prop_repr := by infer_instance

    Actions := (All_Actions n).map (·.1)

    current_state :=
      (
      -- At (RocketVar.Cargo Cargo.Alex) Place.London,
      --   At (RocketVar.Cargo Cargo.Jason) Place.London,
      --   At (RocketVar.Cargo Cargo.Pencil) Place.London,
      --   At (RocketVar.Cargo Cargo.Paper) Place.London,
      --   At (RocketVar.Cargo Cargo.Desk) Place.London,
      --   At (RocketVar.Cargo Cargo.Chair) Place.London,
      --   At (RocketVar.Cargo Cargo.Laptop) Place.London,
      --   At (RocketVar.Rocket Rocket.Rocket1) Place.London,
      --   At (RocketVar.Rocket Rocket.Rocket2) Place.London,
      --   HasFuel Rocket.Rocket1,
      --   HasFuel Rocket.Rocket2

      -- Both rockets have fuel, both start at S
      -- and the cargo wants to go to D1 and D2 alternatingly, but it starts at S
        let base :=
          [ At (RocketVar.Rocket Rocket.Rocket1) Place.S,
            At (RocketVar.Rocket Rocket.Rocket2) Place.S,
            HasFuel Rocket.Rocket1,
            HasFuel Rocket.Rocket2
          ]
        let cargo_props :=
          Cargo.all n |>.foldl (fun acc c =>
            acc.concat (At (RocketVar.Cargo c) Place.S)
          ) []

        let all_props := base.append cargo_props
        all_props
      )

    goal_states :=
    [
        -- At (RocketVar.Cargo Cargo.Alex) Place.Paris,
        -- At (RocketVar.Cargo Cargo.Jason) Place.JFK ,
        -- -- At (RocketVar.Cargo Cargo.Pencil) Place.Paris ,
        -- -- At (RocketVar.Cargo Cargo.Paper) Place.JFK,
        -- -- At (RocketVar.Cargo Cargo.Desk) Place.Paris,
        -- -- At (RocketVar.Cargo Cargo.Chair) Place.JFK,
        -- At (RocketVar.Cargo Cargo.Laptop) Place.Paris

        let get_place_by_index (i : Nat) : Place :=
          match i % 2 with
          | 0 => Place.D1
          | 1 => Place.D2
          | _ => Place.S -- unreachable

        Cargo.all n |>.foldl (fun acc c =>
          acc.concat (At (RocketVar.Cargo c) (get_place_by_index (c.val)))
        ) []
    ]


-- Returns the canonical name of an action
def action_name {n : Nat} (op : STRIPS_Operator (RocketProp n)) : Option String :=
  let found := (All_Actions n).find? (fun x => x.fst = op)
  found.map (fun x => x.snd)


def measure_runtime_solver_rocket (n : Nat) : IO (Std.Time.Nanosecond.Offset × Bool) := do

  -- Start time measurement
  let this_time := ← Std.Time.Timestamp.now

  -- Use Graphplan search to solve the Towers of Hanoi problem with n disks
  let initial_search_state :=
    Search.mk_search_state (Rocket_Problem n)

  let solution := graphplan_search (initial_search_state)
  -- let solution := heuristic_search (initial_search_state)
  -- let solution := linear_search_proved (initial_search_state)
  -- let solution := linear_search (initial_search_state)

  -- dbg_trace s!"Solved Rocket with {n} cargos. Solution:
  --   {repr (solution.map fun s => s.actions.map action_name)}"

  -- Is the solution valid?
  let solution_valid :=
    match solution with
    | none => false
    | some sol => Search.is_valid_plan (Rocket_Problem n) sol.actions

  -- End time measurement
  let end_time := ← Std.Time.Timestamp.now
  let start_nano := this_time.toNanosecondsSinceUnixEpoch
  let end_nano := end_time.toNanosecondsSinceUnixEpoch
  let duration_ns := end_nano - start_nano

  return (duration_ns, solution_valid)

#eval measure_runtime_solver_rocket 10

def measure_runtime_solver_rocket_multiple_times (n : Nat) (tries : Nat) :
    IO (Std.Time.Nanosecond.Offset × Bool) := do

  let mut total_time : Std.Time.Nanosecond.Offset  := 0
  let mut total_valid := true

  -- Iterate for tries times
  for _ in List.finRange tries do
    let (measure, sol_valid) := ← measure_runtime_solver_rocket n
    total_time := total_time + measure
    total_valid := total_valid && sol_valid

  return (total_time, total_valid)


def run_with (n : Nat) (tries : Nat) : IO Unit := do
  -- let n := 15 -- Number of cargos
  -- let tries := 100 -- Number of times to run the solver

  let (total_time, all_valid) := ← measure_runtime_solver_rocket_multiple_times n tries

  let total_ms := total_time.toMilliseconds
  let avg_time := total_time.toMilliseconds.1 / tries

  IO.println s!"Rocket problem with {n} cargos solved {tries} times."
  IO.println s!"Total time: {total_ms} milliseconds."
  IO.println s!"Average time per run: {avg_time} milliseconds."
  IO.println s!"All solutions valid: {all_valid}."

def main : IO Unit := do

  let tries := 10

  for n in List.finRange 100 do
    run_with n tries
