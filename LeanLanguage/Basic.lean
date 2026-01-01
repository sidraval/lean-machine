inductive Ty where
  | nat : Ty
  | bool : Ty
  deriving Repr, DecidableEq

@[reducible] def Ty.denote : Ty -> Type
  | .nat => Nat
  | .bool => Bool

inductive Expr : Ty -> Type where
  | nat  : Nat → Expr .nat
  | bool : Bool → Expr .bool
  | add  : Expr .nat → Expr .nat → Expr .nat
  | mul  : Expr .nat → Expr .nat → Expr .nat
  | lt   : Expr .nat → Expr .nat → Expr .bool
  | eq   : Expr .nat → Expr .nat → Expr .bool
  | and  : Expr .bool → Expr .bool → Expr .bool
  | or   : Expr .bool → Expr .bool → Expr .bool
  | not  : Expr .bool → Expr .bool
  | ite  : {t : Ty} → Expr .bool → Expr t → Expr t → Expr t

def Expr.eval : {t : Ty} → Expr t → t.denote
  | _, .nat n      => n
  | _, .bool b     => b
  | _, .add e₁ e₂  => e₁.eval + e₂.eval
  | _, .mul e₁ e₂  => e₁.eval * e₂.eval
  | _, .lt e₁ e₂   => e₁.eval < e₂.eval
  | _, .eq e₁ e₂   => e₁.eval == e₂.eval
  | _, .and e₁ e₂  => e₁.eval && e₂.eval
  | _, .or e₁ e₂   => e₁.eval || e₂.eval
  | _, .not e      => !e.eval
  | _, .ite c t e  => if c.eval then t.eval else e.eval

def Expr.constFold : {t : Ty} → Expr t → Expr t
  | _, .nat n => .nat n
  | _, .bool b => .bool b
  | _, .add e₁ e₂ =>
    match e₁.constFold, e₂.constFold with
    | .nat n, .nat m => .nat (n + m)
    | e₁', e₂' => .add e₁' e₂'
  | _, .mul e₁ e₂ =>
    match e₁.constFold, e₂.constFold with
    | .nat n, .nat m => .nat (n * m)
    | e₁', e₂' => .mul e₁' e₂'
  | _, .lt e₁ e₂ => .lt e₁.constFold e₂.constFold
  | _, .eq e₁ e₂ => .eq e₁.constFold e₂.constFold
  | _, .and e₁ e₂ => .and e₁.constFold e₂.constFold
  | _, .or e₁ e₂ => .or e₁.constFold e₂.constFold
  | _, .not e => .not e.constFold
  | _, .ite c t e =>
    match c.constFold with
    | .bool true => t.constFold
    | .bool false => e.constFold
    | c' => .ite c' t.constFold e.constFold

theorem constFold_correct : ∀ {t : Ty} (e : Expr t) , e.constFold.eval = e.eval := by
  intro t e
  induction e with
  | nat => rfl
  | bool => rfl
  | add e₁ e₂ ih₁ ih₂ =>
    simp only [Expr.constFold]
    simp only [Expr.eval]
    cases he₁ : e₁.constFold <;> cases he₂ : e₂.constFold <;>
      simp only [Expr.eval, ← ih₁, ← ih₂, he₁, he₂]
  | mul e₁ e₂ ih₁ ih₂ =>
    simp only [Expr.constFold]
    simp only [Expr.eval]
    cases he₁ : e₁.constFold <;> cases he₂ : e₂.constFold <;>
      simp only [Expr.eval, ← ih₁, ← ih₂, he₁, he₂]
  | lt e₁ e₂ ih₁ ih₂ => simp only [Expr.constFold, Expr.eval, ih₁, ih₂]
  | eq e₁ e₂ ih₁ ih₂ => simp only [Expr.constFold, Expr.eval, ih₁, ih₂]
  | and e₁ e₂ ih₁ ih₂ => simp only [Expr.constFold, Expr.eval, ih₁, ih₂]
  | or e₁ e₂ ih₁ ih₂ => simp only [Expr.constFold, Expr.eval, ih₁, ih₂]
  | not e ih => simp only [Expr.constFold, Expr.eval, ih]
  | ite c t e ihc iht ihe =>
    simp only [Expr.constFold, Expr.eval]
    cases hc : c.constFold <;> simp only [Expr.eval, ← ihc, ← iht, ← ihe, hc]
    case bool b => cases b <;> rfl

-- State Machine

inductive AugustTask where
  | form603 : AugustTask
  | assessment : AugustTask

inductive Form603State where
  | notStarted : Form603State
  | started : Form603State
  | shared : Form603State
  | closed : Form603State
  | completed : Form603State
  deriving Repr, DecidableEq


inductive Form603Transition : (inState : Form603State) -> (outState : Form603State) -> Type where
  | start : Form603Transition .notStarted .started
  | share : Form603Transition .started .shared
  | completedByFamily : Form603Transition .shared .completed
  | completedByAugust : Form603Transition .started .completed
  | completedByAugustWhileShared : Form603Transition .shared .completed
  | close : Form603Transition a .closed

def performTransition : 
  (inState : Form603State) ->
  (transition : Form603Transition inState outState) -> Form603State
  := λ _ _ => outState

def X :
    (task : AugustTask) 
    -> { s // s ∈ statesForTask task }
    -> { sOut // sOut ∈ statesForTask task } 
    -> (transition : Form603Transition s sOut) -> Form603State

/- inductive Transition : (inState : State) -> (outState : State) -> Type where -/
/-   | start : Transition .notStarted .started -/
/-   | complete : Transition .started .complete -/
/--/
/- def transition : State → State -/
/-   | .notStarted => .started -/
/-   | .started => .complete -/
/-   | .complete => .complete -/
/--/
/- def isComplete : State → Prop := λx => x = .complete -/
/--/
/- theorem all_states_may_be_completed :  -/
/-     ∀ x : State, ∃ f : State -> State, isComplete (f x) := by -/
/-       intro a -/
/-       match a with -/
/-       | .notStarted => exists (transition ∘ transition) -/
/-       | .started => exists transition -/
/-       | .complete => exists transition -/
/--/
