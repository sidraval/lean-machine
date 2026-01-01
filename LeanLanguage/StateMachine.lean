inductive State where
  | notStarted : State
  | started : State
  | complete : State
  deriving Repr, DecidableEq

inductive Event where
  | start : Event
  | complete : Event
  deriving Repr, DecidableEq

def ValidTransition : Event -> State -> Prop
  | .start, .notStarted => True
  | .complete, .started => True
  | _, _ => False

-- TODO: Add decidable instance for ValidTransition

def transitionViaEvent (e : Event) (s : State) (h : ValidTransition e s) : State :=
  match e,s with
  | .start, .notStarted => .started
  | .complete, .started => .complete

#eval transitionViaEvent .start .notStarted (by simp [ValidTransition])

-- Nonsense below

def transition : State → State
  | .notStarted => .started
  | .started => .complete
  | .complete => .complete

def isComplete : State → Prop := λx => x = .complete

theorem all_states_may_be_completed : 
    ∀ x : State, ∃ f : State -> State, isComplete (f x) := by
      intro a
      match a with
      | .notStarted => exists (transition ∘ transition)
      | .started => exists transition
      | .complete => exists transition

