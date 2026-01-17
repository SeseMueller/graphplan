import Graphplan.Basic
import Mathlib.Tactic.DeriveFintype
import Graphplan.Search.Graphplan
import Graphplan.Search.Linear
import Graphplan.Search.Linear_Heuristic

/-
STRIPS encoding of the 15-puzzle (4x4 sliding numbers puzzle).

State is represented with propositions:
- At t p: tile t is at position p
- Empty p: the hole is at position p
- Adj p q: positions p and q are adjacent (static facts; never changed by actions)

Action schema:
- Slide t from to
  Preconditions: At t from, Empty to, Adj from to
  Add: At t to, Empty from
  Del: At t from, Empty to
-/

open STRIPS

abbrev Pos := Fin 16      -- 0..15
abbrev Tile := Fin 15     -- 0..14 represents tiles 1..15 via (val+1)

def Pos.all : List Pos := List.finRange 16

def Tile.all : List Tile := List.finRange 15

-- 0..15 linear index -> (row, col)
def posRow (p : Pos) : Nat := p.val / 4

def posCol (p : Pos) : Nat := p.val % 4

-- Boolean adjacency on the 4x4 grid.
-- Adjacent means Manhattan distance 1.
def adjacent (p q : Pos) : Bool :=
  let pr := posRow p
  let pc := posCol p
  let qr := posRow q
  let qc := posCol q
  ((pr == qr) && ((pc + 1 == qc) || (qc + 1 == pc))) ||
  ((pc == qc) && ((pr + 1 == qr) || (qr + 1 == pr)))

inductive SlidingProp
  | At (t : Tile) (p : Pos)
  | Empty (p : Pos)
  | Adj (p q : Pos)
  deriving DecidableEq, Repr, Fintype, Hashable

open SlidingProp

-- Add all static adjacency facts.
def adjacency_facts : List SlidingProp :=
  Id.run do
    let mut facts : List SlidingProp := []
    for p in Pos.all do
      for q in Pos.all do
        if adjacent p q then
          facts := facts.concat (Adj p q)
    return facts.dedup

-- Slide tile t from pFrom into the empty pTo.
def slide (t : Tile) (pFrom pTo : Pos) : STRIPS_Operator SlidingProp where
  preconditions := [At t pFrom, Empty pTo, Adj pFrom pTo]
  neg_preconditions := []
  add_effects := [At t pTo, Empty pFrom]
  del_effects := [At t pFrom, Empty pTo]

-- All grounded actions.
def All_Actions : Array (STRIPS_Operator SlidingProp × String) :=
  let outarray := Id.run do
    let mut actions : Array (STRIPS_Operator SlidingProp × String) := #[]
    for t in Tile.all do
      for pFrom in Pos.all do
        for pTo in Pos.all do
          if adjacent pFrom pTo then
            actions := actions.push
              (slide t pFrom pTo,
                s!"Slide tile {t.val + 1} from {pFrom.val} to {pTo.val}")
    return actions
  outarray

-- Helper: goal location for tile t in the solved configuration.
-- Tile 1 goes to pos 0, ..., tile 15 goes to pos 14, and the hole goes to pos 15.
def goal_pos_of_tile (t : Tile) : Pos :=
  ⟨t.val, by
    -- t.val < 15 < 16
    exact Nat.lt_trans t.isLt (by decide)⟩

abbrev goal_empty_pos : Pos := ⟨15, by decide⟩

-- Build a state from an explicit mapping tile -> position and a hole position.
def mk_state (tilePos : Tile → Pos) (emptyPos : Pos) : List SlidingProp :=
  Id.run do
    let mut st : List SlidingProp := []
    for t in Tile.all do
      st := st.concat (At t (tilePos t))
    st := st.concat (Empty emptyPos)
    st := st.append adjacency_facts
    return st.dedup

-- The solved goal propositions (without adjacency facts).
def goal_props : List SlidingProp :=
  Id.run do
    let mut g : List SlidingProp := []
    for t in Tile.all do
      g := g.concat (At t (goal_pos_of_tile t))
    g := g.concat (Empty goal_empty_pos)
    return g

-- A very easy, solvable instance (1 move away from the goal):
-- hole at pos 14, tile 15 at pos 15.
def Sliding_Problem_easy : STRIPS_Plan SlidingProp where
  prop_decidable := by infer_instance
  prop_hashable := by infer_instance
  prop_repr := by infer_instance

  Actions := All_Actions.map (·.1)

  current_state :=
    let tilePos : Tile → Pos := fun t =>
      if h : t.val = 14 then
        -- tile 15 is at pos 15
        ⟨15, by decide⟩
      else
        goal_pos_of_tile t
    mk_state tilePos ⟨14, by decide⟩

  goal_states := [goal_props]


-- Returns the canonical name of an action
def action_name (op : STRIPS_Operator SlidingProp) : Option String :=
  All_Actions.find? (fun x => x.fst = op) |>.map (·.snd)


/-!
Scrambling / generating harder instances

We generate an instance by starting from the solved board and applying `n` random legal moves.
To keep this reproducible (and usable in pure code), we use a simple seeded PRNG.

Note: applying `n` moves does not *guarantee* the optimal solution length is `n`
(because moves can cancel out), but it typically grows with `n`.
-/

structure Board where
  tiles : Array (Option Tile) -- length 16; `none` is the hole
  empty : Pos
  deriving Repr

-- Simple deterministic PRNG (LCG). Good enough for scrambling.
def lcgNext (seed : Nat) : Nat :=
  let m : Nat := 2147483648 -- 2^31
  (1103515245 * seed + 12345) % m

def solvedBoard : Board :=
  let tiles : Array (Option Tile) :=
    Id.run do
      let mut a : Array (Option Tile) := Array.replicate 16 none
      for p in Pos.all do
        if h : p.val < 15 then
          let t : Tile := ⟨p.val, h⟩
          a := a.set! p.val (some t)
      return a
  { tiles := tiles, empty := ⟨15, by decide⟩ }

def neighbors (p : Pos) : List Pos :=
  Pos.all.filter (fun q => adjacent p q)

-- All positions that contain a tile adjacent to the hole.
def movableTilePositions (b : Board) : List Pos :=
  (neighbors b.empty).filter (fun fromPos =>
    match b.tiles[fromPos.val]? with
    | some (some _) => true
    | _ => false)

def applyMoveFrom (b : Board) (fromPos : Pos) : Board :=
  match b.tiles[fromPos.val]? with
  | some (some t) =>
      let tiles1 := b.tiles.set! fromPos.val none
      let tiles2 := tiles1.set! b.empty.val (some t)
      { tiles := tiles2, empty := fromPos }
  | _ => b

-- Perform `n` pseudo-random moves from the solved board.
-- We avoid immediate backtracking when possible by remembering the previous hole position.
def scrambleBoard (n : Nat) (seed : Nat) : Board :=
  let rec go (k : Nat) (b : Board) (prevEmpty : Option Pos) (s : Nat) : Board :=
    match k with
    | 0 => b
    | k' + 1 =>
        let moves0 := movableTilePositions b
        let moves :=
          match prevEmpty with
          | none => moves0
          | some pe =>
              let filtered := moves0.filter (fun p => p != pe)
              if filtered.isEmpty then moves0 else filtered
        match moves.length with
        | 0 => b
        | len + 1 =>
            let s' := lcgNext s
            let idx := s' % (len + 1)
            let chosen := (moves[idx]!)
            let b' := applyMoveFrom b chosen
            go k' b' (some b.empty) s'
  go n solvedBoard none seed

def boardToState (b : Board) : List SlidingProp :=
  Id.run do
    let mut st : List SlidingProp := []
    -- Tile positions
    for i in List.finRange 16 do
      match b.tiles[i.val]? with
      | some (some t) =>
          let p : Pos := ⟨i.val, i.isLt⟩
          st := st.concat (At t p)
      | _ =>
          continue
    -- Hole position
    st := st.concat (Empty b.empty)
    -- Static adjacency facts
    st := st.append adjacency_facts
    return st.dedup

def Sliding_Problem_fromBoard (b : Board) : STRIPS_Plan SlidingProp where
  prop_decidable := by infer_instance
  prop_hashable := by infer_instance
  prop_repr := by infer_instance
  Actions := All_Actions.map (·.1)
  current_state := boardToState b
  goal_states := [goal_props]

-- Public helper: build a harder instance by scrambling the solved board with `n` moves.
-- `seed` controls the pseudo-randomness for reproducibility.
def Sliding_Problem_scrambled (n : Nat) (seed : Nat) : STRIPS_Plan SlidingProp :=
  Sliding_Problem_fromBoard (scrambleBoard n seed)

/-!
Testing harness (copied/adapted from `RocketN.lean`)

We treat the input `n` as the *scramble depth*: starting from the solved board,
apply `n` random legal moves (seeded), then solve.
-/

def measure_runtime_solver_sliding (n : Nat) (seed : Nat) :
IO (Std.Time.Nanosecond.Offset × Bool) := do

  -- Start time measurement
  let this_time := ← Std.Time.Timestamp.now

  -- Build a harder instance by scrambling with n moves.
  let plan := Sliding_Problem_scrambled n seed

  -- Solve using Graphplan (swap to heuristic_search / linear_search if desired)
  let initial_search_state := Search.mk_search_state plan
  let solution := graphplan_search initial_search_state
  -- let solution := heuristic_search initial_search_state
  -- let solution := linear_search initial_search_state
  -- let solution := linear_search_proved initial_search_state

  -- Is the solution valid?
  let solution_valid :=
    match solution with
    | none => false
    | some sol => Search.is_valid_plan plan sol.actions

  -- End time measurement
  let end_time := ← Std.Time.Timestamp.now
  let start_nano := this_time.toNanosecondsSinceUnixEpoch
  let end_nano := end_time.toNanosecondsSinceUnixEpoch
  let duration_ns := end_nano - start_nano

  return (duration_ns, solution_valid)


def measure_runtime_solver_sliding_multiple_times (n : Nat) (tries : Nat) :
    IO (Std.Time.Nanosecond.Offset × Bool) := do

  let mut total_time : Std.Time.Nanosecond.Offset := 0
  let mut total_valid := true

  -- Iterate for tries times
  for i in List.finRange tries do
    -- In order to not fall into local minima, vary the seed each time
    let (measure, sol_valid) := ← measure_runtime_solver_sliding n i
    total_time := total_time + measure
    total_valid := total_valid && sol_valid

  return (total_time, total_valid)


def run_with (n : Nat) (tries : Nat) : IO Unit := do

  let (total_time, all_valid) := ← measure_runtime_solver_sliding_multiple_times n tries

  let total_ms := total_time.toMilliseconds
  let avg_time := total_time.toMilliseconds.1 / tries

  IO.println s!"Sliding puzzle (scramble={n}) solved {tries} times."
  IO.println s!"Total time: {total_ms} milliseconds."
  IO.println s!"Average time per run: {avg_time} milliseconds."
  IO.println s!"All solutions valid: {all_valid}."


def main : IO Unit := do
  let tries := 100

  for n in List.finRange 100 do
    run_with n tries
