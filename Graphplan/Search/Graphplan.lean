import Graphplan.Search.Basic
import Std.Data.HashSet

open STRIPS

namespace GraphplanSearch

/-
  Graphplan (Blum & Furst) planning-graph algorithm.

  Adaptation note:
  - Project states are lists of *positive* propositions.
  - Operators have positive preconditions and also negative preconditions.
  - Effects are add/delete lists.

  Classic Graphplan works over literals (p and ¬p). To support negative preconditions and delete
  effects soundly, we lift propositions `P` to literals `Lit P := pos p | neg p`.
  We then lift each STRIPS operator into this literal domain.

  The exported entrypoint is `graphplan_search` (defined at the bottom of the file).
-/

inductive Lit (P : Type) where
  | pos : P -> Lit P
  | neg : P -> Lit P
  deriving DecidableEq, Repr

namespace Lit

def negate {P : Type} : Lit P -> Lit P
  | pos p => neg p
  | neg p => pos p

end Lit

instance {P : Type} [Hashable P] : Hashable (Lit P) where
  hash
    | .pos p => mixHash 1 (hash p)
    | .neg p => mixHash 2 (hash p)

instance {P : Type} [DecidableEq P] : BEq (Lit P) := instBEqOfDecidableEq

structure GPAction (P : Type) where
  op : STRIPS.STRIPS_Operator (Lit P)
  origin : Option (STRIPS.STRIPS_Operator P) := none
  deriving Repr

structure PropLevel (P : Type) [BEq (Lit P)] [Hashable (Lit P)] where
  props : Std.HashSet (Lit P)
  mutex : Std.HashSet (Lit P × Lit P)

structure ActionLevel (P : Type) [BEq (Lit P)] [Hashable (Lit P)] where
  actions : Array (GPAction P)
  mutex : Std.HashSet (Nat × Nat)
  producers : Std.HashMap (Lit P) (List Nat)

namespace Internal

def listEraseDups {α : Type} [DecidableEq α] : List α -> List α
  | [] => []
  | x :: xs =>
    let xs' := listEraseDups xs
    if xs'.contains x then xs' else x :: xs'

def insertByHash {α : Type} [Hashable α] (x : α) : List α -> List α
  | [] => [x]
  | y :: ys =>
    if (hash x) <= (hash y) then x :: y :: ys
    else y :: insertByHash x ys

def normalizeGoals {α : Type} [DecidableEq α] [Hashable α] (xs : List α) : List α :=
  let dedup := listEraseDups xs
  dedup.foldl (fun acc x => insertByHash x acc) []

def hashSetEq {α : Type} [BEq α] [Hashable α] (a b : Std.HashSet α) : Bool :=
  if a.size != b.size then
    false
  else
    a.fold (init := true) (fun ok x => ok && b.contains x)

def pairKey (i j : Nat) : Nat × Nat :=
  if i <= j then (i, j) else (j, i)

def mutexContains (m : Std.HashSet (Nat × Nat)) (i j : Nat) : Bool :=
  m.contains (pairKey i j)

def litMutexContains {P : Type} [BEq (Lit P)] [Hashable (Lit P)]
    (m : Std.HashSet (Lit P × Lit P)) (a b : Lit P) : Bool :=
  m.contains (a, b) || m.contains (b, a)

def allInPropLevel {P : Type} [BEq (Lit P)] [Hashable (Lit P)]
    (pl : PropLevel P) (ls : List (Lit P)) : Bool :=
  ls.all (fun l => pl.props.contains l)

def noMutexPairs {P : Type} [BEq (Lit P)] [Hashable (Lit P)]
    (pl : PropLevel P) (ls : List (Lit P)) : Bool :=
  let rec go : List (Lit P) -> Bool
    | [] => true
    | x :: xs =>
      (xs.all (fun y => !litMutexContains pl.mutex x y)) && go xs
  go ls

def liftOp {P : Type} (op : STRIPS.STRIPS_Operator P) : STRIPS.STRIPS_Operator (Lit P) where
  preconditions := op.preconditions.map Lit.pos ++ op.neg_preconditions.map Lit.neg
  neg_preconditions := []
  add_effects := op.add_effects.map Lit.pos ++ op.del_effects.map Lit.neg
  del_effects := op.add_effects.map Lit.neg ++ op.del_effects.map Lit.pos

def noopAction {P : Type} (l : Lit P) : GPAction P :=
  { op :=
      { preconditions := [l]
        neg_preconditions := []
        add_effects := [l]
        del_effects := [] }
    origin := none }

def anyIntersects {α : Type} [DecidableEq α] (xs ys : List α) : Bool :=
  xs.any (fun x => ys.contains x)

def inconsistentEffects {P : Type} [DecidableEq (Lit P)] (a b : GPAction P) : Bool :=
  anyIntersects a.op.add_effects b.op.del_effects ||
  anyIntersects b.op.add_effects a.op.del_effects ||
  a.op.add_effects.any (fun l => b.op.add_effects.contains (Lit.negate l))

def interference {P : Type} [DecidableEq (Lit P)] (a b : GPAction P) : Bool :=
  anyIntersects a.op.del_effects b.op.preconditions ||
  anyIntersects b.op.del_effects a.op.preconditions

def competingNeeds {P : Type} [BEq (Lit P)] [Hashable (Lit P)]
    (pl : PropLevel P) (a b : GPAction P) : Bool :=
  a.op.preconditions.any (fun p =>
    b.op.preconditions.any (fun q => litMutexContains pl.mutex p q))

def computeActionLevel {P : Type}
    [DecidableEq P] [Hashable P] [DecidableEq (Lit P)] [BEq (Lit P)] [Hashable (Lit P)]
    (ops : Array (STRIPS.STRIPS_Operator P))
    (pl : PropLevel P) : ActionLevel P :=
  let liftedReal : Array (GPAction P) :=
    ops.foldl (init := #[]) (fun acc op =>
      let lop := liftOp op
      if allInPropLevel pl lop.preconditions && noMutexPairs pl lop.preconditions then
        acc.push { op := lop, origin := some op }
      else
        acc)

  let noopArr : Array (GPAction P) :=
    pl.props.fold (init := #[]) (fun acc l => acc.push (noopAction l))

  let actions := liftedReal ++ noopArr

  let producers : Std.HashMap (Lit P) (List Nat) :=
    Id.run do
      let mut hm : Std.HashMap (Lit P) (List Nat) := Std.HashMap.emptyWithCapacity 64
      for iFin in List.finRange actions.size do
        let i := iFin.1
        let a := actions[iFin]
        for eff in a.op.add_effects do
          let cur := hm.getD eff []
          hm := hm.insert eff (i :: cur)
      hm

  let mutex : Std.HashSet (Nat × Nat) :=
    Id.run do
      let mut m : Std.HashSet (Nat × Nat) := Std.HashSet.emptyWithCapacity 256
      for iFin in List.finRange actions.size do
        for jFin in List.finRange actions.size do
          let i := iFin.1
          let j := jFin.1
          if i < j then
            let ai := actions[iFin]
            let aj := actions[jFin]
            if inconsistentEffects ai aj || interference ai aj || competingNeeds pl ai aj then
              m := m.insert (pairKey i j)
      m

  { actions := actions, mutex := mutex, producers := producers }

def computeNextPropLevel {P : Type}
    [DecidableEq P] [Hashable P] [DecidableEq (Lit P)] [BEq (Lit P)] [Hashable (Lit P)]
    (al : ActionLevel P) : Std.HashSet (Lit P) :=
  al.actions.foldl (init := Std.HashSet.emptyWithCapacity 256) (fun acc a =>
    a.op.add_effects.foldl (init := acc) (fun acc2 l => acc2.insert l))

def computePropMutex {P : Type}
    [DecidableEq P] [Hashable P] [DecidableEq (Lit P)] [BEq (Lit P)] [Hashable (Lit P)]
    (props : Std.HashSet (Lit P))
    (al : ActionLevel P) : Std.HashSet (Lit P × Lit P) :=
  Id.run do
    let mut m : Std.HashSet (Lit P × Lit P) := Std.HashSet.emptyWithCapacity 256

    -- Negated literals are mutex.
    m := props.fold (init := m) (fun acc l =>
      let nl := Lit.negate l
      if props.contains nl then
        acc.insert (l, nl) |>.insert (nl, l)
      else
        acc)

    -- Inconsistent support.
    let propArr := props.toList.toArray
    for iFin in List.finRange propArr.size do
      for jFin in List.finRange propArr.size do
        let i := iFin.1
        let j := jFin.1
        if i < j then
          let p := propArr[iFin]
          let q := propArr[jFin]
          let prodsP := al.producers.getD p []
          let prodsQ := al.producers.getD q []
          let allMutex :=
            prodsP.all (fun ai => prodsQ.all (fun aj => mutexContains al.mutex ai aj))
          if allMutex then
            m := m.insert (p, q)
            m := m.insert (q, p)
    m

def find_in_hashmap? {K V : Type} [BEq K] [Hashable K]
    (hm : Std.HashMap K V) (key : K) : Option V := do
  for (k, v) in hm do
    if k == key then
      return  v
  none


mutual

  partial def _solve {P : Type} [DecidableEq P] [Hashable P] [DecidableEq (Lit P)] [BEq (Lit P)]
  [Hashable (Lit P)] (todo : List (Lit P)) (chosen : List Nat) (al : ActionLevel P)
  (achievedByChosen : List Nat → Lit P → Bool) (propLevels : Array (PropLevel P))
  (actionLevels : Array (ActionLevel P)) (level : Nat)
  : Option (List (List (GPAction P)))
  :=
  let compatibleWith (chosen : List Nat) (i : Nat) : Bool :=
              chosen.all (fun j => !mutexContains al.mutex i j)
              match todo with
              | [] =>
                let chosenActs : List (GPAction P) := chosen.filterMap (fun i => al.actions[i]?)
                let prevGoals := (chosenActs.flatMap (fun a => a.op.preconditions))
                match extractPlan propLevels actionLevels (level - 1) prevGoals with
                | none => none
                | some prefx => some (prefx ++ [chosenActs])
              | g :: gs =>
                if achievedByChosen chosen g then
                  _solve gs chosen al achievedByChosen propLevels actionLevels level
                else
                  -- match al.producers.find? g with
                  match find_in_hashmap? al.producers g with
                  | none => none
                  | some prodList =>
                    let rec tryProds : List Nat -> Option (List (List (GPAction P)))
                      | [] => none
                      | i :: rest =>
                        match al.actions[i]? with
                        | none => tryProds rest
                        | some ai =>
                          if !compatibleWith chosen i then
                            tryProds rest
                          else
                            let remaining := gs.filter (fun h => !(ai.op.add_effects.contains h))
                            match _solve remaining (i :: chosen) al
                            achievedByChosen propLevels actionLevels level with
                            | some res => some res
                            | none => tryProds rest
                    tryProds prodList

  partial def extractPlan {P : Type}
      [DecidableEq P] [Hashable P] [DecidableEq (Lit P)] [BEq (Lit P)] [Hashable (Lit P)]
      (propLevels : Array (PropLevel P))
      (actionLevels : Array (ActionLevel P))
      (level : Nat)
      (goals : List (Lit P)) : Option (List (List (GPAction P))) :=

    let goalsN := normalizeGoals goals
    match propLevels[level]? with
    | none => none
    | some pl =>
      if !(allInPropLevel pl goalsN && noMutexPairs pl goalsN) then
        none
      else
        if level = 0 then
          some []
        else
          match actionLevels[(level - 1)]? with
          | none => none
          | some al =>
            let achievedByChosen (chosen : List Nat) (g : Lit P) : Bool :=
              chosen.any (fun i =>
                match al.actions[i]? with
                | none => false
                | some a => a.op.add_effects.contains g)


            _solve goalsN [] al achievedByChosen propLevels actionLevels level

end -- End mutual

end Internal

end GraphplanSearch

open GraphplanSearch
open GraphplanSearch.Internal

def graphplan_search (s : Search.SearchState) :
    Option (Search.partial_Solution s.plan) := do
  let _ := s.plan.prop_decidable
  let _ := s.plan.prop_hashable

  -- Finite universe for explicit negated literals.
  let mut univ : List s.plan.Props := []
  univ := univ ++ s.plan.current_state
  univ := univ ++ (s.plan.goal_states.flatMap id)
  for op in s.plan.Actions do
    univ := univ ++ op.preconditions
    univ := univ ++ op.neg_preconditions
    univ := univ ++ op.add_effects
    univ := univ ++ op.del_effects
  univ := listEraseDups univ

  let initProps : Std.HashSet (Lit s.plan.Props) :=
    univ.foldl (init := Std.HashSet.emptyWithCapacity 256) (fun acc p =>
      if s.plan.current_state.contains p then
        acc.insert (.pos p)
      else
        acc.insert (.neg p))

  let initMutex : Std.HashSet (Lit s.plan.Props × Lit s.plan.Props) :=
    univ.foldl (init := Std.HashSet.emptyWithCapacity 256) (fun acc p =>
      acc.insert ((.pos p), (.neg p)) |>.insert ((.neg p), (.pos p)))

  let mut propLevels : Array (PropLevel s.plan.Props) :=
  #[{ props := initProps, mutex := initMutex }]
  let mut actionLevels : Array (ActionLevel s.plan.Props) := #[]

  let goalSets : List (List (Lit s.plan.Props)) :=
    s.plan.goal_states.map (fun gs => gs.map Lit.pos)

  let maxLevels := 60

  for depth in [0:maxLevels] do
    match propLevels[depth]? with
    | none =>
      none
    | some pl =>
      let al := computeActionLevel (P := s.plan.Props) s.plan.Actions pl
      actionLevels := actionLevels.push al

      let nextProps := computeNextPropLevel (P := s.plan.Props) al
      let nextMutex := computePropMutex (P := s.plan.Props) nextProps al
      let nextPL : PropLevel s.plan.Props := { props := nextProps, mutex := nextMutex }
      propLevels := propLevels.push nextPL

      let curLevel := depth + 1

      let mut found : Option (List (GPAction s.plan.Props)) := none
      for goals in goalSets do
        if found.isNone then
          match extractPlan (P := s.plan.Props) propLevels actionLevels curLevel goals with
          | none => pure ()
          | some steps =>
            found := some (steps.flatMap id)

      match found with
      | some flat =>
        let actionsOut : List (STRIPS.STRIPS_Operator s.plan.Props) :=
          flat.foldr (init := []) (fun a acc =>
            match a.origin with
            | none => acc
            | some op => op :: acc)
        return { actions := actionsOut }
      | none =>
        if depth > 0 then
          if hashSetEq pl.props nextPL.props && hashSetEq pl.mutex nextPL.mutex then
            none

  none
