import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.GroupWithZero.Unbundled
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Ring.Abs

example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
by
  use 5 / 2
  norm_num

example : ∃ x : R, 2 < x ∧ x < 3 := by
  have h1 : 2 < (5 : R) / 2 := by norm_num
  have h2 : (5 : R) / 2 < 3 := by norm_num
  use 5 / 2, h1, h2

example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
have h : 2 < (5 : ℝ) / 2 ∧ (5 : ℝ) / 2 < 3 := by norm_num
use 5 / 2

example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
  have h : 2 < (5 : ℝ) / 2 ∧ (5 : ℝ) / 2 < 3 := by norm_num
  ⟨5 / 2, h⟩

example : ∃ x : ℝ 2 < x ∧ x < 3 :=
  ⟨5 / 2, by norm_num⟩

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a
def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, a ≤ f x
def FnHasUb (f : ℝ → ℝ) := ∃ a, FnUb f a
def FnHasLb (f : ℝ → ℝ) := ∃ a, FnLb f a

variable {f g : ℝ → ℝ}
example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  rcases ubf with ⟨a, ubfa⟩
  rcases ubg with ⟨b, ubgb⟩
  use a + b
  apply fnUb_add ubfa ubgb

example (lbf : FnHasLb f) (lbg : FnHasLb g) : FnHasLb fun x ↦ f x + g x :=
by
  -- lbf says there exists a lower bound lb_f such that for all x, lb_f ≤ f x
  rcases lbf with ⟨a, lbfa⟩
  -- lbg says there exists a lower bound lb_g such that for all x, lb_g ≤ g x
  rcases lbg with ⟨b, lbgb⟩
  -- We claim that a + b is a lower bound for f(x) + g(x)
  use a + b
  intro x
  -- Use the facts that lb_f ≤ f x and lb_g ≤ g x to show that lb_f + lb_g ≤ f x + g x
  apply add_le_add
  exact lbfa x
  exact lbgb x

example (c : ℝ) (ubf : FnHasUb f) (h : c ≥ 0) : FnHasUb fun x ↦ c * f x :=
by
  -- ubf says there exists an upper bound ub_f such that for all x, f x ≤ ub_f
  rcases ubf with ⟨a, ubfa⟩
  -- We claim that c * a is an upper bound for c * f x
  use c * a
  intro x
  -- Use the fact that f x ≤ a and multiply both sides by c (since c ≥ 0)
  apply mul_le_mul_of_nonneg_left
  exact ubfa x
  exact h

example : FnHasUb f → FnHasUb g → FnHasUb fun x ↦ g x := by
  rintro ⟨a, ubfa⟩ ⟨b, ubgb⟩
  exact ⟨a + b, fnUb_add ubfa ubgb⟩

example : FnHasUb f → FnHasUb g → FnHasUb fun x ↦ f x + g x :=
  fun ⟨a, ubfa⟩ ⟨b, ubgb⟩ ↦ ⟨a + b, fnUb_add ubfa ubgb⟩

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  obtain ⟨a, ubfa⟩ := ubf
  obtain ⟨b, ubgb⟩ := ubg
  exact ⟨a + b, fnUb_add ubfa ubgb⟩

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  cases ubf
  case intro a ubfa =>
    cases ubg
    case intro b ubgb =>
      exact ⟨a + b, fnUb_add ubfa ubgb⟩

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  cases ubf
  next a ubfa =>
    cases ubg
    next b ubgb =>
      exact ⟨a + b, fnUb_add ubfa ubgb⟩

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  match ubf, ubg with
    | ⟨a, ubfa⟩, ⟨b, ubgb⟩ =>
      exact ⟨a + b, fnUb_add ubfa ubgb⟩

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x :=
  match ubf, ubg with
    | ⟨a, ubfa⟩, ⟨b, ubgb⟩ =>
      ⟨a + b, fnUb_add ubfa ubgb⟩

variable {α : Type*} [CommRing α]
def SumOfSquares (x : α) :=
  ∃ a b, x = a ^ 2 + b ^ 2

theorem sumOfSquares_mul {x y : α} (sosx : SumOfSquares x) (sosy : SumOfSquares y) : SumOfSquares (x * y) := by
  rcases sosx with ⟨a, b, xeq⟩
  rcases sosy with ⟨c, d, yeq⟩
  rw [xeq, yeq]
  use a * c - b * d, a * d + b * c
  ring

theorem sumOfSquares_mul' {x y : α} (sosx : SumOfSquares x) (sosy : SumOfSquares y) : SumOfSquares (x * y) := by
  rcases sosx with ⟨a, b, rfl⟩
  rcases sosy with ⟨c, d, rfl⟩
  use a * c - b * d, a * d + b * c
  ring

example (divab : a | b) (divbc : b | c) : a | c := by
  rcases divab with ⟨d, beq⟩
  rcases divbc with ⟨e, ceq⟩
  rw [ceq, beq]
  use d * e; ring

example (a b c : ℕ) (divab : a ∣ b) (divac : a ∣ c) : a ∣ (b + c) :=
  rcases divab with ⟨k₁, rfl⟩;
  rcases divac with ⟨k₂, rfl⟩;
  ⟨k₁ + k₂, by ring⟩

example {c : ℝ} : Surjective fun x ↦ x + c := by
  intro x
  use x - c
  dsimp; ring

example {ℝ : Type*} [ring ℝ] {c : ℝ} (h : c ≠ 0) : function.surjective (λ x, c * x) :=
  intro y, ⟨y / c, by field_simp [h]⟩


example (x y : ℝ) (h : x - y ≠ 0) : (x ^ 2 - y ^ 2) / (x - y) = x + y := by
  field_simp [h]
  ring

example {f : ℝ → } (h : Surjective f) : ∃ x, f x ^ 2 = 4 := by
  rcases h 2 with ⟨x, hx⟩
  use x
  rw [hx]
  norm_num

variable {α : Type*} {β : Type*} {γ : Type*}
variable {g : β → γ} {f : α → β}

example (surjg : function.surjective g) (surjf : function.surjective f) : function.surjective (λ x, g (f x)) :=
  λ z,
  -- since g is surjective, we can find some y such that g(y) = z
  let ⟨y, hy⟩ := surjg z in
  -- since f is surjective, we can find some x such that f(x) = y
  let ⟨x, hx⟩ := surjf y in
  -- we now show that g(f(x)) = z
  ⟨x, by rw [hx, hy]⟩
