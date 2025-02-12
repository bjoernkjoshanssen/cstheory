import Mathlib.Data.Vector.Basic
import Mathlib.Data.Nat.Digits

/-

https://cstheory.stackexchange.com/questions/31787/embedding-a-language-in-itself

"For larger alphabets this type of argument fails since there are arbitrarily long square-free words. "

-/

def squarefree {b:ℕ} (w: List (Fin b)) : Prop :=
  ∀ l:ℕ, l < w.length → ∀ v : Vector (Fin b) l,
  v.1 ≠ List.nil → ¬ List.IsInfix (v.1 ++ v.1) w


def cubefree {b:ℕ} (w: List (Fin b)) : Prop :=
  ∀ l:ℕ, l < w.length → ∀ v : Vector (Fin b) l,
  v.1 ≠ List.nil → ¬ List.IsInfix (v.1 ++ v.1 ++ v.1) w


instance (b:ℕ) (w : List (Fin b)) : Decidable (squarefree w) := by
  unfold squarefree
  exact w.length.decidableBallLT fun n _ => ∀ (v : Vector (Fin b) n), v.1 ≠ [] → ¬v.1 ++ v.1 <:+: w


instance (b:ℕ) (w : List (Fin b)) : Decidable (cubefree w) := by
  unfold cubefree
  exact
    w.length.decidableBallLT fun n _ => ∀ (v : Vector (Fin b) n), v.1 ≠ [] → ¬v.1 ++ v.1 ++ v.1 <:+: w

example : ∀ w : Vector (Fin 2) 4, ¬ squarefree w.1 := by decide

theorem suffix_squarefree (b:ℕ) (u v : List (Fin b)) (h: u <:+ v) (hu : squarefree v) : squarefree u := by
  intro lx _ x hx
  obtain ⟨t,ht⟩ := h; intro hc
  have : lx < v.length := calc
        lx  = x.1.length              := x.2.symm
        _   < x.1.length + x.1.length := Nat.lt_add_of_pos_left (List.length_pos.mpr hx)
        _   = (x.1 ++ x.1).length     := (List.length_append x.1 x.1).symm
        _   ≤ u.length                := List.IsInfix.length_le hc
        _   ≤ t.length + u.length     := by linarith
        _   = v.length                := by rw [← List.length_append t u,ht]
  let G := hu lx this x hx; unfold List.IsInfix at G
  let ⟨s₀,hs₀⟩ := hc; let ⟨s₁,hs₁⟩ := hs₀
  have : ∃ s t, s ++ (x.1 ++ x.1) ++ t = v := by use t ++ s₀; use s₁; rw [← ht,← hs₁]; simp
  exact G this

theorem suffix_cubefree (b:ℕ) (u v : List (Fin b)) (h: u <:+ v) (hu : cubefree v) : cubefree u := by
  intro lx _ x hx hc
  obtain ⟨t,ht⟩ := h
  have : lx < v.length := calc
        lx  = x.1.length                            := x.2.symm
        _   < x.1.length + x.1.length               := Nat.lt_add_of_pos_left (List.length_pos.mpr hx)
        _   ≤ x.1.length + x.1.length + x.1.length  := Nat.le_add_right _ _
        _   = (x.1 ++ x.1).length + x.1.length      := by rw[(List.length_append x.1 x.1).symm]
        _   = (x.1 ++ x.1 ++ x.1).length            := (List.length_append (x.1 ++ x.1) x.1).symm
        _   ≤ u.length                              := List.IsInfix.length_le hc
        _   ≤ t.length + u.length                   := by linarith
        _   = v.length                              := by rw [← List.length_append t u,ht]
  let G := hu lx this x hx; unfold List.IsInfix at G
  let ⟨s₀,hs₀⟩ := hc; let ⟨s₁,hs₁⟩ := hs₀
  have : ∃ s t, s ++ (x.1 ++ x.1 ++ x.1) ++ t = v := by use t ++ s₀; use s₁; rw [← ht,← hs₁]; simp
  exact G this
