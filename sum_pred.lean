import Mathlib.Computability.NFA
import Mathlib.MeasureTheory.Constructions.Prod.Basic
import Mathlib.Data.Matrix.Basic

-- update June 30, 2024

lemma sum_pred₀ (n:ℕ) : Finset.sum (Finset.range n) (λ k ↦ k-1) = (n-1)*(n-2)/2 := by
  apply Finset.sum_range_induction
  . rfl
  . intro n
    simp only [add_tsub_cancel_right, Nat.succ_sub_succ_eq_sub]
    suffices  (n * (n - 1) / 2)*2 = ((n - 1) * (n - 2) / 2 + (n - 1))*2 by
      exact Nat.mul_right_cancel (Nat.zero_lt_two) this
    rw [
      Nat.add_mul,
      Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self n),
      Nat.div_two_mul_two_of_even (by exact Nat.even_mul_pred_self (n-1)),
      ← Nat.mul_add
    ]
    cases n with
    | zero => simp
    | succ n_1 =>
      simp only [Nat.succ_sub_succ_eq_sub, tsub_zero]
      cases n_1
      . simp
      . simp only [add_tsub_cancel_right]
        ring

 theorem sum_pred (n:ℕ) : Finset.sum (Finset.range n.succ) (λ k ↦ k-1) = n*(n-1)/2 := sum_pred₀ n.succ
