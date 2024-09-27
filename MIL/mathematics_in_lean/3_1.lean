import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.GroupWithZero.Unbundled
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Ring.Abs


-- 3.1 Implication and the Universal Quantifier
#check ∀ x : ℝ, 0 ≤ x → |x| = x

-- "For every x, y, and ε, if 0 < ε ≤ 1, the absolute value of x is less than ε, and the absolute value of y is less than ε, then the absolute value of x * y is less than ε.”
theorem my_lemma : ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
sorry

section
variable (a b δ : ℝ)
variable(h0 :0<δ)(h1 :δ≤1)
variable (ha : |a| < δ) (hb : |b| < δ)

#check my_lemma a b δ
#check my_lemma a b δ h0 h1
#check my_lemma a b δ h0 h1 ha hb
end

theorem my_lemma2 : ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
sorry

section
variable (a b δ : ℝ )
variable(h0 :0<δ)(h1 :δ≤1)
variable (ha : |a| < δ) (hb : |b| < δ)

#check my_lemma2 h0 h1 ha hb

end

-- Using tactic mode for the same theorem
theorem my_lemma3 :
  ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
  exact my_lemma x y ε epos ele1 xlt ylt

-- A version using the `calc` tactic for better readability
-- use "abs_mul, mul_le_mul, abs_nonneg, mul_lt_mul_right, and one_mul"
-- abs_mul: ∣a⋅b∣=∣a∣⋅∣b∣
-- mul_le_mul: a≤b and c≤d ⇒ a⋅c ≤ b⋅d
-- abs_nonneg: ∣a∣ ≥ 0
-- mul_lt_mul_right: a < b => a⋅c < b⋅c
-- one_mul: 1⋅a=a


theorem my_lemma4 :
∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
by
  intro x y ε epos ele1 xlt ylt
  calc
  |x * y| = |x| * |y| := by
    apply abs_mul

  _ ≤ |x| * ε := by
    apply mul_le_mul_of_nonneg_left
    apply le_of_lt ylt
    apply abs_nonneg

  _ < 1 * ε := by
    apply mul_lt_mul_of_pos_right
    apply lt_of_lt_of_le xlt ele1
    exact epos

  _ = ε := by
    apply one_mul


-- Definitions for function upper and lower bounds
def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

-- Example proof using FnUb
example (f g : ℝ → ℝ)(a b : ℝ) (hfa : FnUb f a) (hgb : FnUb g b) : FnUb (fun x ↦ f x + g x) (a + b) :=
by
  intro x
  dsimp
  apply add_le_add
  exact hfa x
  exact hgb x

example(f g : ℝ → ℝ )(a b :ℝ)(hfa : FnLb f a) (hgb : FnLb g b) : FnLb (fun x ↦ f x + g x) (a + b) :=
by
  intro x
  dsimp
  apply add_le_add
  apply hfa
  apply hgb

example (f g : ℝ → ℝ )(a b :ℝ)(nnf : FnLb f 0) (nng : FnLb g 0) : FnLb (fun x ↦ f x * g x) 0 :=
by
  intro x
  apply mul_nonneg (nnf x) (nng x)

example (f g : ℝ → ℝ )(a b :ℝ)(hfa : FnUb f a) (hgb : FnUb g b) (nng : FnLb g 0) (nna : 0 ≤ a) : FnUb (fun x ↦ f x * g x) (a * b) :=
by
  intro x
  dsimp
  apply mul_le_mul
  apply hfa
  apply hgb
  exact nng x
  exact nna

-- Working with general types and ordered structures
variable {α : Type*} {R : Type*} [OrderedCancelAddCommMonoid R]
#check add_le_add

-- A more general definition of function upper bounds
def FnUb' (f : α → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a

-- Theorem: upper bound of the sum of two functions
theorem fnUb_add {f g : α → ℝ} {a b : ℝ} (hfa : FnUb' f a) (hgb : FnUb' g b) : FnUb' (fun x ↦ f x + g x) (a + b) :=
  fun x ↦ add_le_add (hfa x) (hgb x)

example (f : ℝ → ℝ) (h : Monotone f) : ∀ {a b}, a ≤ b → f a ≤ f b := @h

example (f g : ℝ → ℝ )(mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f x + g x :=
by
  intro a b aleb
  apply add_le_add
  apply mf aleb
  apply mg aleb

example (f g : ℝ → ℝ )(mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f x + g x :=
  fun a b aleb ↦ add_le_add (mf aleb) (mg aleb)

example (f g : ℝ → ℝ ){c : ℝ} (mf : Monotone f) (nnc : 0 ≤ c) : Monotone fun x ↦ c * f x :=
by
  intro a b aleb
  apply mul_le_mul
  apply le_refl
  apply mf aleb   -- f is monotone, so f a ≤ fa
  exact le_of_lt a
  apply nnc


example (f g : ℝ → ℝ )(mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f (g x) :=
by
  intro a b aleb
  apply mf
  apply mg aleb



def FnEven (f : ℝ → ℝ) : Prop := ∀ x, f x = f (-x)
def FnOdd (f : ℝ → ℝ) : Prop := ∀ x, f x = -f (-x)
example (f g : ℝ → ℝ ) (ef : FnEven f) (eg : FnEven g) : FnEven fun x ↦ f x + g x :=
by
  intro x
  calc
    (fun x ↦ f x + g x) x = f x + g x := rfl
    _ = f (-x) + g (-x) :=
    by
      rw [ef, eg]

example (f g : ℝ → ℝ) (of : FnOdd f) (og : FnOdd g) : FnEven fun x ↦ f x * g x :=
by
  intro x
  have hx : f (-x) = -f x := of (-x)
  have hg : g (-x) = -g x := og (-x)
  rw [hx, hg]
  simp
  -- f (-x) * g (-x) = -f x * -g x = f x * g x
  exact neg_eq_of_eq_neg (neg_eq_of_eq_neg (by simp))

example (f g : ℝ → ℝ) (ef : FnEven f) (og : FnOdd g) : FnOdd fun x ↦ f x * g x :=
by
  intro x
  have h : g (-x) = -g x := og (-x)
  rw [ef (-x), h]
  simp
  -- f (-x) * g (-x) = f x * -g x = - (f x * g x)
  exact neg_eq_of_eq_neg (by simp)

example (f g : ℝ → ℝ) (ef : FnEven f) (og : FnOdd g) : FnEven fun x ↦ f (g x) :=
by
  intro x
  have hg : g (-x) = -g x := og (-x)   -- g is odd
  rw [ef (g x), hg]                    -- f is even, so f (-y) = f y for any y = g x
  -- f (g (-x)) = f (-g x) = f (g x), proving that the composition is even
  exact rfl

variable {α : Type*} (r s t : Set α)
example : s ⊆ s :=
by
  intro x xs
  exact xs
theorem Subset.refl : s ⊆ s := fun x xs ↦ xs
theorem Subset.trans : r ⊆ s → s ⊆ t → r ⊆ t :=
by
  intro hrs hst x hxr
  -- Since r ⊆ s, we have x ∈ s from x ∈ r
  have hxs : x ∈ s := hrs hxr
  -- Since s ⊆ t, we have x ∈ t from x ∈ s
  exact hst hxs

variable {α : Type*} [PartialOrder α]
variable (s : Set α) (a b : α)
def SetUb (s : Set α) (a : α) := ∀ x, x ∈ s → x ≤ a
example (h : SetUb s a) (h' : a ≤ b) : SetUb s b :=
by
  intros x hx
  -- By the definition of SetUb, h says that for all x in s, x ≤ a
  have hxa : x ≤ a := h x hx
  -- Since a ≤ b, we can use transitivity of ≤ to get x ≤ b
  exact le_trans hxa h'

open Function
example (c : R) : Injective fun x ↦ x + c :=
by
  intro x1 x2 h'
  exact (add_left_inj c).mp h'

example {c : R} (h : c ≠ 0) : Injective fun x ↦ c * x :=
by
  intros x1 x2 h'
  -- We know that c * x1 = c * x2, and we need to show that x1 = x2
  have h' : c * x1 = c * x2 := h'
  -- Since c ≠ 0, we can divide both sides by c (or multiply by the inverse of c)
  exact (mul_left_inj' h).mp h'

variable {α : Type*} {β : Type*} {γ : Type*}
variable {g : β → γ} {f : α → β}

example (injg : Injective g) (injf : Injective f) : Injective fun x ↦ g (f x) :=
by
  intros x1 x2 h
  -- g (f x1) = g (f x2), and we need to show that x1 = x2.
  -- Since g is injective, f x1 = f x2
  have hfx : f x1 = f x2 := injg h
  -- Since f is injective, x1 = x2
  exact injf hfx
