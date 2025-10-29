import Graphplan.Basic

-- We use the definition in the Basic module to construct the example
-- for a STRIPS planning problem from the Wikipedia article on STRIPS.

-- The enum of positional variables
inductive Position
  | A
  | B
  | C
  deriving DecidableEq, Repr, Fintype

-- Whether the monkey is currently high or low
inductive Height
  | High
  | Low
  deriving DecidableEq, Repr, Fintype

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


-- Because the actions have free variables (the positions),
-- we need to instantiate them for all possible values.
def All_MonkeyBox_Actions : Set (STRIPS_Operator MonkeyBoxProp) :=
  { m : STRIPS_Operator MonkeyBoxProp | ∃ p1 p2 : Position, m = Move p1 p2 } ∪
  { m : STRIPS_Operator MonkeyBoxProp | ∃ p : Position, m = ClimbUp p } ∪
  { m : STRIPS_Operator MonkeyBoxProp | ∃ p : Position, m = ClimbDown p } ∪
  { m : STRIPS_Operator MonkeyBoxProp | ∃ p1 p2 : Position, m = MoveBox p1 p2 } ∪
  { m : STRIPS_Operator MonkeyBoxProp | ∃ p : Position, m = TakeBananas p }


-- The complete STRIPS planning problem for the monkey and bananas example.
def MonkeyBox_STRIPS_Plan : STRIPS_Plan where
  Props := MonkeyBoxProp
  prop_decidable := instDecidableEqMonkeyBoxProp
  Actions := All_MonkeyBox_Actions
  current_state := {At A, BoxAt B, BananaAt C, Level Low}
  goal_states := {{HasBanana}}

-- The same example, but using the DSL operator `>-`
def Example_Simulation_End_state_DSL : STRIPS_Plan :=
  let test :=
    TakeBananas C
    >- ClimbUp C
    >- MoveBox B C
    >- Move A B
    >- MonkeyBox_STRIPS_Plan
  test
