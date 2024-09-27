import MIL.Common

theorem addnegcancelright (a b : ℝ) : a + b + -b = a := by
  rw [add_assoc, add_comm, add_neg_cancel, zero_add]

theorem eq_neg_of_add_eq_zero {a b : ℝ} (h : a + b = 0) : a = -b := by
  rw [← add_neg_cancel b]
  rw [← add assoc]
  rw [h]
  rw [zero_add]
