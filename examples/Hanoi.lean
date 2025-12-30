import Graphplan.Basic
import Mathlib.Tactic.DeriveFintype
import Graphplan.Search.Graphplan
import Graphplan.Search.Linear
import Graphplan.Search.Linear_Heuristic

-- This example models the classic Towers of Hanoi problem using the Graphplan framework.

inductive Peg
  | A
  | B
  | C
  deriving DecidableEq, Repr, Fintype, Hashable
def Peg.all : List Peg := [Peg.A, Peg.B, Peg.C]

-- There are n disks, numbered from 0 (smallest) to n-1 (largest)
inductive Disk (n : Nat)
  | mk (i : Fin n)
  deriving DecidableEq, Repr, Fintype, Hashable
def Disk.all {n : Nat} : List (Disk n) := (List.finRange n).map Disk.mk

inductive HanoiVar (n : Nat)
  | Peg (p : Peg)
  | Disk (d : Disk n)
  deriving DecidableEq, Repr, Fintype, Hashable

open Peg Disk HanoiVar STRIPS

def HanoiVar.all {n : Nat} : List (HanoiVar n) :=
  let outlist := Id.run do
    let mut vars : List (HanoiVar n) := []
    for p in Peg.all do
      vars := vars.concat (HanoiVar.Peg p)
    for d in Disk.all do
      vars := vars.concat (HanoiVar.Disk d)
    vars

  outlist

inductive HanoiProp (n : Nat)
  | On (d : Disk n) (v : HanoiVar n) -- Disk d is on peg/disk p
  | Clear (v : HanoiVar n) -- The top of peg or disk o is clear
  deriving DecidableEq, Repr, Fintype, Hashable
  -- TODO: Add a seperate Hanoi implementation that, instead of encoding
  -- the "smaller" relation in the actions, encodes it in the propositions.

open HanoiProp HanoiVar

def move {n : Nat} (d : Disk n) (src dst : HanoiVar n) : STRIPS_Operator (HanoiProp n) :=
  {
    preconditions := { On d src, Clear (Disk d), Clear dst }
    neg_preconditions := { }
    add_effects := { On d dst, Clear src }
    del_effects := { On d src, Clear dst }
  }

def All_Actions {n : Nat} : Array (STRIPS_Operator (HanoiProp n) × String) :=
  let outarray := Id.run do
    let mut actions : Array (STRIPS_Operator (HanoiProp n) × String) := #[]
    for d in Disk.all do
      for src in HanoiVar.all do
        for dst in HanoiVar.all do
          if src != dst then
          -- If dst is a disk, ensure it is larger than d
            match dst with
            | HanoiVar.Disk d2 =>
              if d.1 < d2.1 then
                actions := actions.push
                  (move d src dst, s!"Move disk {repr d} from {repr src} to {repr dst}")
            | HanoiVar.Peg _ =>
            actions := actions.push
              (move d src dst, s!"Move disk {repr d} from {repr src} to {repr dst}")
    actions
  outarray

-- The whole planning problem for Towers of Hanoi with n disks
def Hanoi_Problem (n : Nat) : STRIPS_Plan where
  Props := HanoiProp n
  prop_decidable := by infer_instance
  prop_hashable := by infer_instance
  prop_repr := by infer_instance
  current_state :=
    Id.run do
    let mut init : List (HanoiProp n) := {}
    -- All disks are on peg A, largest at bottom
    if h : n > 0 then
      init := init.insert (On (Disk.mk (Fin.mk (n-1) (Nat.sub_one_lt_of_lt h)))
            (HanoiVar.Peg Peg.A))
      for i in List.finRange n do
        let d := Disk.mk i
        match i with
        | ⟨0, _⟩ =>
          init := init.insert (Clear (HanoiVar.Disk d))
        | ⟨i, isLt⟩ =>
          let smaller := Disk.mk (Fin.mk (i - 1) (Nat.sub_lt_of_lt isLt))
          init := init.insert (On smaller (Disk d))


      -- Pegs B and C are clear
      init := init.insert (Clear (HanoiVar.Peg Peg.B))
      init := init.insert (Clear (HanoiVar.Peg Peg.C))
      init
    else
      return init
  goal_states :=
    [ Id.run do
        let mut goal : List (HanoiProp n) := {}
        -- All disks are on peg C, largest at bottom
        if h : n > 0 then
          for i in List.finRange n do
            let d := Disk.mk i
            -- if i > 0 then
            --   let smaller := Disk.mk (d.1.pred)
            --   goal := goal.insert (On smaller (Disk d))
            match i with
            | ⟨0, _⟩ => ()
            | ⟨i, isLt⟩ =>
              let smaller := Disk.mk (Fin.mk (i - 1) (Nat.sub_lt_of_lt isLt))
              goal := goal.insert (On smaller (Disk d))

          -- And the largest disk is on peg C
          let largest := Disk.mk (Fin.mk (Nat.pred n) (Nat.pred_lt_of_lt h))
          goal := goal.insert (On largest (HanoiVar.Peg Peg.C))

          goal := goal.insert (Clear (HanoiVar.Peg Peg.A))
          goal := goal.insert (Clear (HanoiVar.Peg Peg.B))
          goal

        else
          return goal ]
  Actions := All_Actions.map (·.1)

-- Returns the canonical name of an action
def action_name {n : Nat} (action : STRIPS_Operator (HanoiProp n)) : Option String :=
  let action_array := All_Actions
  action_array.find? (fun (op, _) => op == action) |>.map (·.2)

-- Use Graphplan search to solve the Towers of Hanoi problem with n disks
def initial_search_state (n : Nat) :=
  Search.mk_search_state (Hanoi_Problem n)
def size := 5
def solution := graphplan_search (initial_search_state size)
-- def solution := heuristic_search (initial_search_state size)

-- Is the solution valid?
def solution_valid :=
  match solution with
  | none => false
  | some sol => Search.is_valid_plan (Hanoi_Problem size) sol.actions
#eval solution_valid


def solution_names :=
  solution.map (fun sol =>
    sol.actions.map (fun op =>
      match action_name op with
      | some name => name
      | none => "Unknown Action"))

-- #eval solution_names
#eval solution.map (fun sol => sol.actions.length)
