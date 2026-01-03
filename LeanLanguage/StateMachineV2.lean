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

-- Here, we define the concept of Reachability. The reachable type is
-- parameterized by a StateMachineType and a State and returns a
-- proof (!) that the State is reachable.
--
-- The 'proof' here comes from the return type of Prop, which means
-- proposition. It's another special feature of Lean: formal verification.
--
-- A state is reachable if:
-- 1. It's the initial state
-- 2. It's reachable via a valid transition from another reachable state
--
-- The step constructor is "universally quantified" over State & Event
-- i.e. it works for all states and events.
inductive Reachable (smt : StateMachineType) : State → Prop where
  | initial : Reachable smt smt.initialState
  | step : ∀ {s : State} {e : Event},
           Reachable smt s →
           (h : smt.validTransition e s) →
           Reachable smt (smt.nextState e s h)

-- A ValidStateMachine is constructed by providing a StateMachineType
-- and a proof that it's possible to reach the completed state.
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
-- which I think of as 'proving mode'
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

/-!
## Task with State-Dependent Data

The task now carries a `Reachable` proof instead of list membership.
-/

structure AugustTask (smt : StateMachineType) (f : State → Type) where
  state : State
  data : f state
  isReachable : Reachable smt state

/-!
## State-Dependent Data: Signatures
-/

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

/-!
## Transition Functions

These are now trivial to implement - the reachability proof is just
`Reachable.step` applied to the existing proof.
-/

def sign
  (task : AugustTask smt Signatures)
  (h : smt.validTransition .sign task.state)
  (newData : Signatures (smt.nextState .sign task.state h))
  : AugustTask smt Signatures := {
    state := smt.nextState .sign task.state h
    data := newData
    isReachable := Reachable.step task.isReachable h  -- That's it!
  }

def start
  (task : AugustTask smt Signatures)
  (h : smt.validTransition .start task.state)
  (newData : Signatures (smt.nextState .start task.state h))
  : AugustTask smt Signatures := {
    state := smt.nextState .start task.state h
    data := newData
    isReachable := Reachable.step task.isReachable h
  }

def complete
  (task : AugustTask smt Signatures)
  (h : smt.validTransition .complete task.state)
  (newData : Signatures (smt.nextState .complete task.state h))
  : AugustTask smt Signatures := {
    state := smt.nextState .complete task.state h
    data := newData
    isReachable := Reachable.step task.isReachable h
  }

/-- Generic transition function that works for any event -/
def transition
  (task : AugustTask smt f)
  (e : Event)
  (h : smt.validTransition e task.state)
  (newData : f (smt.nextState e task.state h))
  : AugustTask smt f := {
    state := smt.nextState e task.state h
    data := newData
    isReachable := Reachable.step task.isReachable h
  }

/-!
## Example Usage
-/

def initialSignableTask : AugustTask RawSignable Signatures := {
  state := .notStarted
  data := Signatures.mk []
  isReachable := Reachable.initial
}

-- Start the task
def startedTask : AugustTask RawSignable Signatures :=
  start initialSignableTask rfl (Signatures.mk [] rfl)

-- Sign the task
def signedTask : AugustTask RawSignable Signatures :=
  sign startedTask rfl (Signatures.mk ["Alice", "Bob"] trivial)

-- Complete the task
def completedTask : AugustTask RawSignable Signatures :=
  complete signedTask rfl (Signatures.mk ["Alice", "Bob"] trivial)

#check completedTask.isReachable
-- This is a proof term showing the full path:
-- notStarted → started → pendingSignatures → completed
