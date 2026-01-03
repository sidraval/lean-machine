import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card

inductive State where
  | notStarted
  | started
  | assignedToFamily
  | pendingSignatures
  | completed
  deriving Repr, DecidableEq

instance : Fintype State where
  elems := ⟨
    [State.notStarted, State.started, State.assignedToFamily, State.pendingSignatures, State.completed],
    by simp
  ⟩
  complete := λ e => by
   cases e
   all_goals simp

def numberOfStates := Fintype.card State

inductive Event where
  | start
  | sign
  | complete
  deriving Repr, DecidableEq

instance : Fintype Event where
  elems := ⟨
    [Event.start, .sign, .complete],
    by simp
  ⟩
  complete := λ e => by
    cases e
    all_goals simp

def events : List Event := [.start, .sign, .complete]

structure StateMachineType where
  initialState : State := .notStarted
  validTransition : Event -> State -> Bool
  nextState : (e : Event) -> (s : State) -> (h : validTransition e s) -> State

def nextReachableStates : (events : List Event) -> StateMachineType -> State -> List State := λ events smt s =>
  events.foldr
    (λ el accum =>
      if hValid : (smt.validTransition el s)
      then smt.nextState el s (by exact hValid) :: accum
      else accum)
    []

def expandReachable
  (events : List Event)
  (smt : StateMachineType)
  (current: List State) : List State :=
    let nextStates := current.flatMap (nextReachableStates events smt)
    List.dedup (current ++ nextStates)
 
def allPossibleStates : (List Event) -> StateMachineType -> State -> List State := λ events smt s =>
  Nat.iterate (expandReachable events smt) (numberOfStates) [s]

structure ValidStateMachineType where
  smt : StateMachineType
  possibleStates : List State := allPossibleStates events smt smt.initialState
  isCompleteable : State.completed ∈ allPossibleStates events smt smt.initialState := by decide

def ValidStateMachineType.isShareable (vsm : ValidStateMachineType) : Bool :=
  State.assignedToFamily ∈ allPossibleStates events vsm.smt vsm.smt.initialState

def RawAcknowledgeable : StateMachineType := {
  validTransition := λ e s => match e, s with
  | .complete, .notStarted => True
  | _, _ => False

  nextState := λ e s _ => match e, s with
  | .complete, .notStarted => .completed
}

def Acknowledgeable : ValidStateMachineType := {
  smt := RawAcknowledgeable
}

def RawCompleteable : StateMachineType := {
  validTransition := λ e s => match e, s with
  | .start, .notStarted => True
  | .complete, .started => True
  | _, _ => False

  nextState := λ e s _ => match e, s with
  | .complete, .started => .completed
  | .start, .notStarted => .started
}

def Completeable : ValidStateMachineType := {
  smt := RawCompleteable
}

def RawSignable : StateMachineType := {
  validTransition := λ e s => match e, s with
  | .start, .notStarted => True
  | .sign, .started => True
  | .complete, .pendingSignatures => True
  | _, _ => False

  nextState := λ e s _ => match e, s with
  | .start, .notStarted => .started
  | .sign, .started => .pendingSignatures
  | .complete, .pendingSignatures => .completed
}

def Signable : ValidStateMachineType := {
  smt := RawSignable
}

#eval allPossibleStates events Acknowledgeable.smt State.notStarted
#eval allPossibleStates events Completeable.smt State.notStarted
#eval Acknowledgeable.isShareable

structure AugustTask (f : State -> Type) where
  state : State
  stateMachineType : ValidStateMachineType
  data : f state
  isValidState :
    state ∈ stateMachineType.possibleStates := by decide

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

def signableTask : AugustTask Signatures := AugustTask.mk .started Signable (Signatures.mk [])

#eval signableTask.stateMachineType.possibleStates

def sign
  (inTask : AugustTask Signatures)
  (h : inTask.stateMachineType.smt.validTransition .sign inTask.state)
  (newData : Signatures (inTask.stateMachineType.smt.nextState .sign inTask.state h))
  : AugustTask Signatures := {
    state := inTask.stateMachineType.smt.nextState .sign inTask.state h
    stateMachineType := inTask.stateMachineType
    data := newData
    isValidState := by
      sorry
  }
