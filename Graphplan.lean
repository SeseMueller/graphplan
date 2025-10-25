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
  prop_decidable := instDecidableEqMonkeyBoxProp
  Actions := All_MonkeyBox_Actions
  current_state := {MonkeyBoxProp.At Position.A, MonkeyBoxProp.BoxAt Position.B,
    MonkeyBoxProp.BananaAt Position.C, MonkeyBoxProp.Level Height.Low}
  goal_states := {{MonkeyBoxProp.HasBanana}}



open MonkeyBoxProp Position Height

-- The search is not implemented yet, but we can try to run a simulation manually.
def Example_Simulation_Step1_State : List MonkeyBoxProp :=
  -- First synthesize the move A B action
  let move_AB := Move A B;
  apply_action_if_applicable MonkeyBox_STRIPS_Plan move_AB

#eval Example_Simulation_Step1_State

-- All subsequent steps, manually inputted for now.
def Example_Simulation_End_state : List MonkeyBoxProp :=
  let next := apply MonkeyBox_STRIPS_Plan (Move A B) (by decide);
  let next := apply next (MoveBox B C) (by decide);
  let next := apply next (ClimbUp C) (by decide);
  let next := apply next (TakeBananas C) (by decide);


  -- return the result, the final state
  next.current_state


#eval Example_Simulation_End_state
