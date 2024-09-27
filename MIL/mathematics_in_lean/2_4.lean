import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Basic

example (a b : ℝ) : max a b = max b a := by
  exact max_comm a b

example (a b c : ℝ) : min (min a b) c = min a (min b c) := by
  exact min_assoc a b c

theorem aux (a b c : ℝ) : min a b + c ≤ min (a + c) (b + c) := by
  exact min_le_min (le_add_left c a) (le_add_left c b)

example (a b c : ℝ) : min a b + c = min (a + c) (b + c) := by
  by_cases ha : a ≤ b
  { simp [min_eq_left ha, min_eq_left (le_add_left c b)] }
  { simp [min_eq_right (not_le.mp ha), min_eq_right (le_add_left c a)] }

example (a b : ℝ) : |a| - |b| ≤ |a - b| := by
  exact abs_sub_le_abs_sub_left a b

example (x y z w : ℕ) (h : x ∣ w) : x ∣ (y * (x * z) + x ^ 2 + w ^ 2) := by
  apply dvd_mul_of_dvd_left

example (m n : ℕ) : Nat.gcd m n = Nat.gcd n m := by
  exact Nat.gcd_comm m n
