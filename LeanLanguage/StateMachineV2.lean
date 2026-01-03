inductive State where
  | notStarted
  | started
  | assignedToFamily
  | pendingSignatures
  | completed
  deriving Repr, DecidableEq

inductive Event where
  | start
  | sign
  | complete
  deriving Repr, DecidableEq

/-!
## Core State Machine Definition

The key insight: instead of computing `possibleStates` as a List and requiring
membership proofs, we define `Reachable` as an inductive predicate.
This makes transition proofs trivial - just apply the `step` constructor.
-/

structure StateMachineType where
  initialState : State := .notStarted
  validTransition : Event → State → Bool
  nextState : (e : Event) → (s : State) → validTransition e s → State

/-- Inductive definition of reachability. A state is reachable if:
    1. It's the initial state, or
    2. It's reachable via a valid transition from another reachable state -/
inductive Reachable (smt : StateMachineType) : State → Prop where
  | initial : Reachable smt smt.initialState
  | step : ∀ {s : State} {e : Event},
           Reachable smt s →
           (h : smt.validTransition e s) →
           Reachable smt (smt.nextState e s h)

/-- A valid state machine can reach the completed state -/
structure ValidStateMachineType where
  smt : StateMachineType
  isCompleteable : Reachable smt .completed

/-!
## Concrete State Machines
-/

def RawAcknowledgeable : StateMachineType := {
  validTransition := λ e s => match e, s with
  | .complete, .notStarted => true
  | _, _ => false

  nextState := λ e s _ => match e, s with
  | .complete, .notStarted => .completed
}

def Acknowledgeable : ValidStateMachineType := {
  smt := RawAcknowledgeable
  isCompleteable := by
    -- notStarted → completed via .complete
    have h : RawAcknowledgeable.validTransition .complete .notStarted := rfl
    exact Reachable.step Reachable.initial h
}

def RawCompleteable : StateMachineType := {
  validTransition := λ e s => match e, s with
  | .start, .notStarted => true
  | .complete, .started => true
  | _, _ => false

  nextState := λ e s _ => match e, s with
  | .start, .notStarted => .started
  | .complete, .started => .completed
}

def Completeable : ValidStateMachineType := {
  smt := RawCompleteable
  isCompleteable := by
    -- notStarted → started → completed
    have h1 : RawCompleteable.validTransition .start .notStarted := rfl
    have h2 : RawCompleteable.validTransition .complete .started := rfl
    exact Reachable.step (Reachable.step Reachable.initial h1) h2
}

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

def Signable : ValidStateMachineType := {
  smt := RawSignable
  isCompleteable := by
    -- notStarted → started → pendingSignatures → completed
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
