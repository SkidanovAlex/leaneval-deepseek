import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Finset

/-- The sum of `i + 1` over `i : Fin (h - 1)` equals `h * (h - 1) / 2`. -/
private lemma sum_fin_succ_eq (h : ℕ) :
    ∑ i : Fin (h - 1), (i.val + 1) = h * (h - 1) / 2 := by
  have hmul : (h - 1 + 1) * (h - 1) = h * (h - 1) := by
    rcases Nat.eq_zero_or_pos h with h0 | hpos
    · subst h0; simp
    · rw [Nat.sub_add_cancel hpos]
  have hstep : ∑ i ∈ Finset.range (h - 1), (i + 1) = ((h - 1) + 1) * (h - 1) / 2 := by
    have h1 := Finset.sum_range_succ' (fun k : ℕ => k) (h - 1)
    simp only [Nat.add_zero] at h1
    rw [Finset.sum_range_id] at h1
    rw [Nat.add_sub_cancel] at h1
    exact h1.symm
  rw [show (∑ i : Fin (h - 1), (i.val + 1)) = ∑ i ∈ Finset.range (h - 1), (i + 1) from
        Fin.sum_univ_eq_sum_range (fun j => j + 1) (h - 1), hstep, hmul]

theorem card_box_le (s h P : ℕ) (hs : 1 ≤ s) :
    (Fintype.piFinset (fun i : Fin (h - 1) => Finset.Icc s (s * P ^ (i.val + 1)))).card
      ≤ s ^ (h - 1) * P ^ (h * (h - 1) / 2) := by
  rw [Fintype.card_piFinset]
  calc ∏ i : Fin (h - 1), (Finset.Icc s (s * P ^ (i.val + 1))).card
      ≤ ∏ i : Fin (h - 1), (s * P ^ (i.val + 1)) := by
        apply Finset.prod_le_prod
        intro i _
        rw [Nat.card_Icc]
        have : s * P ^ (i.val + 1) + 1 - s ≤ s * P ^ (i.val + 1) := by omega
        exact this
    _ = s ^ (h - 1) * P ^ (h * (h - 1) / 2) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
            Finset.prod_pow_eq_pow_sum, sum_fin_succ_eq]

end Work.BMF
