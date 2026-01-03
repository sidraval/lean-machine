import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card

inductive State where
  | notStarted
  | started
  | assignedToFamily
  | completed
  deriving Repr, DecidableEq

instance : Fintype State where
  elems := ⟨
    [State.notStarted, State.started, State.assignedToFamily, State.completed],
    by simp
  ⟩
  complete := λ e => by
   cases e
   all_goals simp

def numberOfStates : Nat := Fintype.card State

inductive Event where
  | start
  | complete
  deriving Repr, DecidableEq

instance : Fintype Event where
  elems := ⟨
    [Event.start, Event.complete],
    by simp
  ⟩
  complete := λ e => by
    cases e
    all_goals simp

-- TODO: Fintype instance?
def events : List Event := [.start, .complete]

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

#eval allPossibleStates events Acknowledgeable.smt State.notStarted
#eval allPossibleStates events Completeable.smt State.notStarted
#eval Acknowledgeable.isShareable

structure AugustTask where
  state : State
  stateMachineType : ValidStateMachineType
  isValidState : state ∈ allPossibleStates events stateMachineType.smt stateMachineType.smt.initialState := by decide

-- Acknowledgeable state machine
#check_failure AugustTask.mk .started Acknowledgeable
#check AugustTask.mk .completed Acknowledgeable
#check AugustTask.mk .notStarted Acknowledgeable

-- Completeable state machine
#check AugustTask.mk .notStarted Completeable
#check AugustTask.mk .started Completeable
#check AugustTask.mk .completed Completeable
