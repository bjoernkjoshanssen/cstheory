import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.Basic


/-

The CSTheory question at
https://cstheory.stackexchange.com/questions/25670/algorithm-to-merge-two-incomplete-sequences-of-symbols-strings-into-a-complete
was answered in the comments in terms of longest subsequence and
https://en.wikipedia.org/wiki/Shortest_common_supersequence

Here we formalize "longest common subsequence" and show that it is computable.

-/

def subsequence (a : Fin m → Fin rm) (b : Fin n → Fin rn) (h : rm ≤ rn) : Prop :=
  ∃ f : Fin m → Fin n, Function.Injective f ∧ ∀ i,
    b (Fin.castLT (f i) ((f i).2)) = Fin.castLT (a i) (by
      calc
      (a i).1 < rm := (a i).2
      _       ≤ rn := h
    )

instance (a : Fin m → Fin rm) (b : Fin n → Fin rn) (h : rm ≤ rn) : Decidable (subsequence a b h) := by
  unfold subsequence
  exact Fintype.decidableExistsFintype

def longestCommonSubsequence {m n₀ n₁ rm rn₀ rn₁ : ℕ}
  (h₀ : rm ≤ rn₀) (h₁ : rm ≤ rn₁)
  (a : Fin m → Fin rm) (b₀ : Fin n₀ → Fin rn₀) (b₁ : Fin n₁ → Fin rn₁)
  : Prop :=
  subsequence a b₀ h₀ ∧ subsequence a b₁ h₁ ∧
    ∀ m' : Fin n₀.succ, -- giving a bound on m' to make it computable
    ∀ a' : Fin m' → Fin (min rn₀ rn₁),
      subsequence a' b₀ (Nat.min_le_left rn₀ rn₁) →
      subsequence a' b₁ (Nat.min_le_right rn₀ rn₁) → m' ≤ m

instance  {m n₀ n₁ rm rn₀ rn₁ : ℕ}
  (a : Fin m → Fin rm) (b₀ : Fin n₀ → Fin rn₀) (b₁ : Fin n₁ → Fin rn₁)
  (h₀ : rm ≤ rn₀) (h₁ : rm ≤ rn₁) :
  Decidable (longestCommonSubsequence h₀ h₁ a b₀ b₁) := by
  unfold longestCommonSubsequence
  exact instDecidableAnd

example : longestCommonSubsequence
  NeZero.one_le NeZero.one_le ![(0: Fin 1),0] ![(0: Fin 5),0,4] ![(0:Fin 4),3,0] := by
  decide
