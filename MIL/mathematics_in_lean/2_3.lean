import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Basic

example (a b c d e : ℝ) (h0 : a ≤ b) (h1 : b < c) (h2 : c ≤ d) (h3 : d < e) : a < e := by
  apply lt_of_le_of_lt h0
  apply lt_trans h1
  apply lt_of_le_of_lt h2
  exact h3


example (a b c d e : ℝ) (h0 : d ≤ e) : c + exp (a + d) ≤ c + exp (a + e) := by
  apply add_le_add_left
  exact exp_le_exp (add_le_add_left h0 a)

example : (0 : ℝ) < 1 := by norm_num

example (a b : ℝ) (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) := by
  have h0 : 0 < 1 + exp a := by
    apply lt_add_of_pos_of_le
    norm_num
    exact exp_pos a
  apply log_le_log h0
  apply add_le_add_left
  exact exp_le_exp (add_le_add_left h a)

example (a b c : ℝ) (h : a ≤ b) : c - exp b ≤ c - exp a := by
  apply sub_le_sub_left
  exact exp_le_exp h

example (a b : ℝ) : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  have h : 2 * |a * b| ≤ a ^ 2 + b ^ 2 := by
    -- Use the identity: (a - b)² ≥ 0, which simplifies to a² + b² ≥ 2ab.
    have h_identity : (a - b) ^ 2 ≥ 0 := by
      apply sq_nonneg
    -- Expand (a - b)²
    rw [sq_sub] at h_identity
    -- Use linear arithmetic to simplify
    linarith,
  -- Now, divide both sides by 2 to obtain the desired result.
  linarith
