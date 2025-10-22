import Graphplan.Basic

-- We use the definition in the Basic module to construct the example
-- for a STRIPS planning problem from the Wikipedia article on STRIPS.

-- The enum of positional variables
inductive Position
  | A
  | B
  | C
  deriving DecidableEq, Repr

-- Whether the monkey is currently high or low
inductive Height
  | High
  | Low
  deriving DecidableEq, Repr

-- The Enum of propositional variables
inductive MonkeyBoxProp
  | At (p : Position) -- The monkey is at position p
  | BoxAt (p : Position) -- The box is at position p
  | BananaAt (p : Position) -- The banana is at position p
  | Level (h : Height) -- The monkey is at height h
  | HasBanana -- The monkey has the banana
  deriving DecidableEq, Repr

-- The Move Operator. Requires the monkey to be low and at some position p1.
def Move (p1 : Position) (p2 : Position) : STRIPS_Operator MonkeyBoxProp where
  preconditions := {MonkeyBoxProp.At p1, MonkeyBoxProp.Level Height.Low}
  neg_preconditions := {}
  add_effects := {MonkeyBoxProp.At p2}
  del_effects := {MonkeyBoxProp.At p1}

-- The ClimbUp Operator. Requires the monkey to be at the same position as the box and be low.
def ClimbUp (p : Position) : STRIPS_Operator MonkeyBoxProp where
  preconditions := {MonkeyBoxProp.At p, MonkeyBoxProp.BoxAt p, MonkeyBoxProp.Level Height.Low}
  neg_preconditions := {}
  add_effects := {MonkeyBoxProp.Level Height.High}
  del_effects := {MonkeyBoxProp.Level Height.Low}

-- The ClimbDown Operator. Requires the monkey to be high (and at the same position as the box).
def ClimbDown (p : Position) : STRIPS_Operator MonkeyBoxProp where
  preconditions := {MonkeyBoxProp.At p, MonkeyBoxProp.BoxAt p, MonkeyBoxProp.Level Height.High}
  neg_preconditions := {}
  add_effects := {MonkeyBoxProp.Level Height.Low}
  del_effects := {MonkeyBoxProp.Level Height.High}

-- The MoveBox Operator. Requires the monkey to be low and at the same position as the box.
def MoveBox (p1 : Position) (p2 : Position) : STRIPS_Operator MonkeyBoxProp where
  preconditions := {MonkeyBoxProp.At p1, MonkeyBoxProp.BoxAt p1, MonkeyBoxProp.Level Height.Low}
  neg_preconditions := {}
  add_effects := {MonkeyBoxProp.BoxAt p2, MonkeyBoxProp.At p2}
  del_effects := {MonkeyBoxProp.BoxAt p1, MonkeyBoxProp.At p1}

-- The TakeBananas Operator. Requires the monkey to be high and at the same position as the bananas.
def TakeBananas (p : Position) : STRIPS_Operator MonkeyBoxProp where
  preconditions := {MonkeyBoxProp.At p, MonkeyBoxProp.BananaAt p, MonkeyBoxProp.Level Height.High}
  neg_preconditions := {}
  add_effects := {MonkeyBoxProp.HasBanana}
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
  Actions := All_MonkeyBox_Actions
  initial_state := {MonkeyBoxProp.At Position.A, MonkeyBoxProp.BoxAt Position.B,
    MonkeyBoxProp.BananaAt Position.C, MonkeyBoxProp.Level Height.Low}
  goal_state := {MonkeyBoxProp.HasBanana}
