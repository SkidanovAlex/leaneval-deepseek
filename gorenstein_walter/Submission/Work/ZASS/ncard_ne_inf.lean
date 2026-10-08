import Mathlib

namespace Work.ZASS

theorem ncard_ne_inf {X : Type} [Finite X] (inf : X) {q : ℕ} (h : Nat.card X = q + 1) :
    ({x : X | x ≠ inf} : Set X).ncard = q := by
  have hset : ({x : X | x ≠ inf} : Set X) = {inf}ᶜ := by
    ext x; simp [eq_comm]
  rw [hset, Set.ncard_compl, Set.ncard_singleton, h]
  omega

end Work.ZASS
