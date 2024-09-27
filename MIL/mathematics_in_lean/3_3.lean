import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.GroupWithZero.Unbundled
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Ring.Abs

example (h : a < b) : ¬b < a := by
  intro h'
  have : a < a :=
  lt_trans h h'
  apply lt_irrefl a this

example (h : ∀ a, ∃ x, f x > a) : ¬FnHasUb f := by
  intro fnub
  rcases fnub with ⟨a, fnuba⟩
  rcases h a with ⟨x, hx⟩
  have : f x ≤ a := fnuba x linarith

example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f :=
  λ hlb, let ⟨a, ha⟩ := hlb in
  let ⟨x, hx⟩ := h a in
  lt_irrefl (f x) (ha x hx)

example : ¬FnHasUb (λ x, x) :=
  λ hub, let ⟨a, ha⟩ := hub in
  let x := a + 1 in
  not_le_of_gt (lt_add_one a) (ha x)

#check (not_le_of_gt : a > b → ¬a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬a < b)
#check (lt_of_not_ge : ¬a ≥ b → a < b)
#check (le_of_not_gt : ¬a > b → a ≤ b)

example {α β : Type*} [preorder α] [preorder β] {f : α → β} {a b : α}
  (h : monotone f) (h' : f a < f b) : a < b :=
  lt_of_not_ge (λ hab, not_lt_of_le (h hab) h')

example {α β : Type*} [preorder α] [preorder β] {f : α → β} {a b : α}
  (h : a ≤ b) (h' : f b < f a) : ¬monotone f :=
  λ hf, not_lt_of_le (hf h) h'

example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 :=
le_of_not_gt (λ hx, let h₁ := h x hx in (lt_irrefl x h₁))

example {α : Type*} (P : α → Prop) (h : ¬∃ x, P x) : ∀ x, ¬P x :=
λ x hx, h ⟨x, hx⟩

example {α : Type*} (P : α → Prop) (h : ∀ x, ¬P x) : ¬∃ x, P x :=
λ ⟨x, hx⟩, h x hx

example {α : Type*} (P : α → Prop) (h : ¬∀ x, P x) : ∃ x, ¬P x :=
classical.not_forall.mp h

example {α : Type*} (P : α → Prop) (h : ∃ x, ¬P x) : ¬∀ x, P x :=
λ h₁, let ⟨x, hx⟩ := h in hx (h₁ x)

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  show P x
  by_contra h''
  exact h' ⟨x, h''⟩

example (h : ¬¬Q) : Q :=
classical.by_contradiction h

example (h : Q) : ¬¬Q :=
λ h₁, h₁ h

example (f : ℝ → ℝ) (h : ¬ FnHasUb f) : ∀ a, ∃ x, f x > a :=
λ a, by
  intro h₁
  apply h
  use a
  exact h₁ 

example (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by 
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by 
  dsimp only [FnHasUb, FnUb] at h
  push_neg at h
  exact h

example (f : ℝ → ℝ) (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x :=
by
  push_neg at h
  rcases h with ⟨x, y, hxy, hfy⟩
  use [x, y]
  split; assumption

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by 
  contrapose! h
  exact h

example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by 
  contrapose! h
  use x / 2
  constructor <;> linarith

example (h : 0 < 0) : a > 37 := by 
  exfalso
  apply lt_irrefl 0 h

example (h : 0 < 0) : a > 37 :=
  absurd h (lt_irrefl 0)

example (h : 0 < 0) : a > 37 := by 
  have h' : ¬0 < 0 := lt_irrefl 0 
  contradiction