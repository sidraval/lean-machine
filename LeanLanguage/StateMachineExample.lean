-- Our possible states, modeled as a simple ADT.
inductive State where
  | notStarted
  | started
  | assignedToFamily
  | pendingSignatures
  | completed
  deriving Repr, DecidableEq

-- Events that trigger state transitions.
inductive Event where
  | start
  | sign
  | complete
  deriving Repr, DecidableEq

-- The core state machine type definition is composed of:
-- initialState: self explanatory
-- validTransition: a function that describes all the valid transitions
-- nextState: a function that produces the next state.
--
-- The cool thing here is that the type of `nextState` depends on
-- the VALUE of applying validTransition to event & state.
-- This is the first example of dependent typing we've come across:
-- a type depending on a value!
structure StateMachineType where
  initialState : State := .notStarted
  validTransition : Event → State → Bool
  nextState : (e : Event) → (s : State) → validTransition e s → State

-- Here, we define the concept of Reachability.
-- A state is reachable if:
-- 1. It's the initial state
-- 2. It's reachable via a valid transition from another reachable state
--
-- The reachable type is parameterized by a StateMachineType and a
-- State, and returns a proposition (!) that the State is reachable.
--
-- The 'proposition' here comes from the return type of Prop.
-- It's another special feature of Lean: formal verification.
-- A Prop can only be True or False
--
-- The step constructor is "universally quantified (∀)" over State & Event
-- i.e. it works for all states and events.
inductive Reachable (smt : StateMachineType) : State → Prop where
  | initial : Reachable smt smt.initialState
  | step : ∀ {s : State} {e : Event},
           Reachable smt s →
           (h : smt.validTransition e s) →
           Reachable smt (smt.nextState e s h)

-- A ValidStateMachine is constructed by providing a StateMachineType
-- and a proof that it's possible to reach the completed state.
--
-- Defining a value of this type requires that you demonstrate
-- that it's possible to reach the completed state -- or the code won't
-- compile!
structure ValidStateMachineType where
  smt : StateMachineType
  isCompleteable : Reachable smt .completed

-- Here, we define a RawSignable StateMachine type, providing the
--- validTransition and nextState functions - nothing special here.
def RawSignable : StateMachineType := {
  validTransition := λ e s => match e, s with
  | .start, .notStarted => true
  | .sign, .started => true
  | .complete, .pendingSignatures => true
  | _, _ => false

  nextState := λ e s _ => match e, s with
  | .start, .notStarted => .started
  | .sign, .started => .pendingSignatures
  | .complete, .pendingSignatures => .completed
}

-- Now, we define our 'real' Signable ValidStateMachineType.
-- Here, we need to provide a proof that we can reach the completed state.
-- We accomplish this via a special Lean feature called 'tactics mode'
-- which I think of as 'proving mode'.
--
-- In our case, the proof is simply demonstrating the path:
-- notStarted → started → pendingSignatures → completed
def Signable : ValidStateMachineType := {
  smt := RawSignable
  isCompleteable := by
    have h1 : RawSignable.validTransition .start .notStarted := rfl
    have h2 : RawSignable.validTransition .sign .started := rfl
    have h3 : RawSignable.validTransition .complete .pendingSignatures := rfl
    exact Reachable.step (Reachable.step (Reachable.step Reachable.initial h1) h2) h3
}

-- Now we define our task structure (a structure is just an inductive
-- type with a single constructor). Tasks are parameterized by their
-- state machine type, as well as a (dependent) function that tells
-- the task what Type of data it can have in each state.
structure AugustTask (smt : ValidStateMachineType) (dataForState : State → Type) where
  state : State
  data : dataForState state
  isReachable : Reachable smt.smt state

-- We define a Signatures data structure that we'll use as the
-- `dataForState` parameter above. This expresses: "In certain states,
-- an AugustTask will have signature data"
--
-- In our case, only a task in .pendingSignatures or .completed
-- can have signature data, as encoded by the hasSignatures proposition.
--
-- This gives us _compile time_ guarantees that the .notStarted state
-- cannot have signature data! Pretty cool.
structure Signatures (s : State) where
  signatures : List String
  hasSignatures :
    match s with
    | .notStarted => signatures = []
    | .started => signatures = []
    | .assignedToFamily => signatures = []
    | .pendingSignatures => True
    | .completed => True
    := by decide

-- We define transition functions, start/sign/complete that
-- progress a task through the different states.
--
-- In the start function below, the `h` parameter is a proposition
-- asserts that there is a valid transition via the .start event
-- given the task's current state.
--
-- Again, there are _compile time_ guarantees here: you can't
-- call the start function unless you can prove a valid transition
-- exists!
--
-- The { smt : StateMachineType } denotes an implicit parameter.
def start
  { smt : ValidStateMachineType }
  (task : AugustTask smt Signatures)
  (h : smt.smt.validTransition .start task.state)
  (newData : Signatures (smt.smt.nextState .start task.state h))
  : AugustTask smt Signatures := {
    state := smt.smt.nextState .start task.state h
    data := newData
    isReachable := Reachable.step task.isReachable h
  }

def sign
  { smt : ValidStateMachineType }
  (task : AugustTask smt Signatures)
  (h : smt.smt.validTransition .sign task.state)
  (newData : Signatures (smt.smt.nextState .sign task.state h))
  : AugustTask smt Signatures := {
    state := smt.smt.nextState .sign task.state h
    data := newData
    isReachable := Reachable.step task.isReachable h
  }

def complete
  { smt : ValidStateMachineType }
  (task : AugustTask smt Signatures)
  (h : smt.smt.validTransition .complete task.state)
  (newData : Signatures (smt.smt.nextState .complete task.state h))
  : AugustTask smt Signatures := {
    state := smt.smt.nextState .complete task.state h
    data := newData
    isReachable := Reachable.step task.isReachable h
  }

def initialSignableTask : AugustTask Signable Signatures := {
  state := .notStarted
  data := Signatures.mk []
  isReachable := Reachable.initial
}

-- Start the task
-- Below, the first `rfl` satisfies the `h` proposition for
-- the `start` function. `rfl` is a lean tactic.
--
-- The second `rfl` is provided as a proof that the signature
-- data, i.e. [], is valid for the task in its .started state.
def startedTask : AugustTask Signable Signatures :=
  start initialSignableTask rfl (Signatures.mk [] rfl)

-- Sign the task
def signedTask : AugustTask Signable Signatures :=
  sign startedTask rfl (Signatures.mk ["Alice", "Bob"] trivial)

-- Complete the task
def completedTask : AugustTask Signable Signatures :=
  complete signedTask rfl (Signatures.mk ["Alice", "Bob"] trivial)

-- It's not possible to construct an AugustTask in .notStarted
-- state with non-empty signatures. The hasSignatures proof requires signatures = []
-- for .notStarted, so providing ["Alice"] fails to type-check.
#check_failure ({
  state := .notStarted
  data := Signatures.mk ["Alice"] rfl
  isReachable := Reachable.initial
} : AugustTask Signable Signatures)
