inductive State where
  | notStarted
  | started
  | completed
  deriving Repr, DecidableEq

inductive Event where
  | start
  | complete
  deriving Repr, DecidableEq

def ValidTransition : Event -> State -> Prop
  | .start, .notStarted => True
  | .complete, .started => True
  | _, _ => False

-- TODO: Add decidable instance for ValidTransition

def transitionViaEvent (e : Event) (s : State) (h : ValidTransition e s) : State :=
  match e,s with
  | .start, .notStarted => .started
  | .complete, .started => .completed

#eval transitionViaEvent .start .notStarted (by simp [ValidTransition])

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

def allPossibleStates : (List Event) -> StateMachineType -> State -> List State := λ events smt s =>
  (nextReachableStates events smt s).flatMap λ nextState => allPossibleStates events smt nextState
  -- We need to track states we've already processed, so that we don't run `nextReachableStates` on them again
  -- The difference between all possible states and the states we've processed should be decreasing
  -- For example, in the 'Acknowledgeable' case, we can only process notStarted -> completed via the complete event.
  -- If we keep track that we've already processed 'notStarted', the next iteration should see that there are
  -- no valid transitions for the remaining states
  -- We need to provide termination_by and decreasing_by

def validStates : List Event -> StateMachineType -> List State
| events, smt => nextReachableStates events smt smt.initialState

def Acknowledgeable : StateMachineType := {
  validTransition := λ e s => match e, s with
  | .complete, .notStarted => True
  | _, _ => False

  nextState := λ e s _ => match e, s with
  | .complete, .notStarted => .completed
}

def Completeable : StateMachineType := {
  validTransition := λ e s => match e, s with
  | .start, .notStarted => True
  | .complete, .started => True
  | _, _ => False

  nextState := λ e s _ => match e, s with
  | .complete, .started => .completed
  | .start, .notStarted => .started
}

structure AugustTask where
  state : State
  stateMachineType : StateMachineType
  -- isValidState : state ∈ allPossibleStates events smt smt.initialState := by decide ???
