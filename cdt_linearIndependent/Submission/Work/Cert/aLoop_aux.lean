import Mathlib
import Submission.Work.Cert.ThetaDefs

/-! # Auxiliary arithmetic for the `A`-loop invariant

Unscaled (division-free on the right) forms of the one-ulp rounding bounds of
`Submission.Work.Cert.ThetaDefs`, together with the one-step expansions of the budget sums `Bd`
and `BdM`.  These are the forms in which the induction step of `AInv` is consumed.
-/

namespace Work.Cert

open Complex Finset

noncomputable section

/-! ## Elementary facts about the scale -/

lemma S_ge_320 : (320 : ℝ) ≤ (S : ℝ) := by
  have h : (320 : ℤ) ≤ S := by norm_num [S]
  exact_mod_cast h

lemma S_gt_one : (1 : ℝ) < (S : ℝ) := lt_of_lt_of_le one_lt_two (le_trans (by norm_num) S_ge_320)

lemma mub_nonneg {m : ℤ} (hm : 0 ≤ m) : 0 ≤ mub m := by
  rw [mub]
  exact div_nonneg (by exact_mod_cast hm) (le_of_lt thS_pos)

lemma mub_pos {m : ℤ} (hm : 1 ≤ m) : 0 < mub m := by
  rw [mub]
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast lt_of_lt_of_le Int.zero_lt_one hm
  exact div_pos hmR thS_pos

lemma mub_le_one {m : ℤ} (hμ : mub m ≤ 79 / 100) : mub m ≤ 1 := by linarith

/-! ## Unscaled rounding bounds -/

lemma md_le' (a b : ℤ) : ((md a b : ℤ) : ℝ) ≤ (a : ℝ) * (b : ℝ) / (S : ℝ) := by
  have h := mul_le_mul_of_nonneg_right (thmd_le a b) (le_of_lt thS_pos)
  have e1 : ((md a b : ℤ) : ℝ) / (S : ℝ) * (S : ℝ) = ((md a b : ℤ) : ℝ) :=
    div_mul_cancel₀ _ thS_ne
  have e2 : (a : ℝ) / (S : ℝ) * ((b : ℝ) / (S : ℝ)) * (S : ℝ) = (a : ℝ) * (b : ℝ) / (S : ℝ) := by
    field_simp
  rw [e1, e2] at h
  exact h

lemma md_gt' (a b : ℤ) : (a : ℝ) * (b : ℝ) / (S : ℝ) - 1 < ((md a b : ℤ) : ℝ) := by
  have hS : (0 : ℤ) < S := by norm_num [S]
  have h : a * b < (md a b + 1) * S := Int.lt_ediv_add_one_mul_self (a * b) hS
  have hR : (a : ℝ) * (b : ℝ) < (((md a b : ℤ) : ℝ) + 1) * (S : ℝ) := by
    have h2 := (Int.cast_lt (R := ℝ)).mpr h
    push_cast at h2
    linarith
  rw [sub_lt_iff_lt_add, div_lt_iff₀ thS_pos]
  linarith [hR]

lemma mu_ge' (a b : ℤ) : (a : ℝ) * (b : ℝ) / (S : ℝ) ≤ ((mu a b : ℤ) : ℝ) := by
  have h := mul_le_mul_of_nonneg_right (thmu_ge a b) (le_of_lt thS_pos)
  have e1 : ((mu a b : ℤ) : ℝ) / (S : ℝ) * (S : ℝ) = ((mu a b : ℤ) : ℝ) :=
    div_mul_cancel₀ _ thS_ne
  have e2 : (a : ℝ) / (S : ℝ) * ((b : ℝ) / (S : ℝ)) * (S : ℝ) = (a : ℝ) * (b : ℝ) / (S : ℝ) := by
    field_simp
  rw [e1, e2] at h
  exact h

lemma mu_lt' (a b : ℤ) : ((mu a b : ℤ) : ℝ) < (a : ℝ) * (b : ℝ) / (S : ℝ) + 1 := by
  have hS : (0 : ℤ) < S := by norm_num [S]
  have h : -(a * b) < ((-(a * b)) / S + 1) * S := Int.lt_ediv_add_one_mul_self _ hS
  have hmu : (((-(a * b)) / S : ℤ) : ℝ) = -((mu a b : ℤ) : ℝ) := by
    have e : mu a b = -((-(a * b)) / S) := rfl
    rw [e]; push_cast; ring
  have hR : -((a : ℝ) * (b : ℝ)) < (((-(a * b)) / S : ℤ) : ℝ) * (S : ℝ) + (S : ℝ) := by
    have h2 : (-(a * b) : ℤ) < (((-(a * b)) / S : ℤ) + 1) * S := h
    have h3 : (-(a * b) : ℝ) < ((((-(a * b)) / S : ℤ) : ℝ) + 1) * (S : ℝ) := by
      exact_mod_cast h2
    push_cast at h3
    linarith
  have key : ((mu a b : ℤ) : ℝ) * (S : ℝ) < (a : ℝ) * (b : ℝ) + (S : ℝ) := by
    rw [hmu] at hR; linarith
  have h1 : ((mu a b : ℤ) : ℝ) - 1 < (a : ℝ) * (b : ℝ) / (S : ℝ) := by
    rw [lt_div_iff₀ thS_pos]; linarith
  linarith

lemma dvu_ge' (a b : ℤ) (hb : 0 < b) : (a : ℝ) * (S : ℝ) / (b : ℝ) ≤ ((dvu a b : ℤ) : ℝ) := by
  have h := mul_le_mul_of_nonneg_right (thdvu_ge a b hb) (le_of_lt thS_pos)
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have e1 : ((dvu a b : ℤ) : ℝ) / (S : ℝ) * (S : ℝ) = ((dvu a b : ℤ) : ℝ) :=
    div_mul_cancel₀ _ thS_ne
  have e2 : (a : ℝ) / (b : ℝ) * (S : ℝ) = (a : ℝ) * (S : ℝ) / (b : ℝ) := by field_simp
  rw [e1, e2] at h
  exact h

/-! ## The budget sums -/

lemma Bd_succ (k : ℕ) : Bd (k + 1) = Bd k + (((8 * tri (k + 1) + 1 : ℕ) : ℝ)) := by
  rw [Bd, Finset.sum_range_succ, Bd]

lemma BdM_succ (m rq : ℤ) (k : ℕ) :
    BdM m rq (k + 1) = BdM m rq k + ((tri (k + 1) : ℝ) * (mub m) ^ (tri (k + 1) - 1) * (rq : ℝ)) := by
  rw [BdM, Finset.sum_range_succ, BdM]

lemma Bd_nonneg (k : ℕ) : 0 ≤ Bd k := by
  rw [Bd]; positivity

lemma BdM_nonneg {m rq : ℤ} (hm : 0 ≤ mub m) (hrq : 0 ≤ rq) (k : ℕ) : 0 ≤ BdM m rq k := by
  rw [BdM]
  apply Finset.sum_nonneg
  intro j hj
  have h1 : (0 : ℝ) ≤ (tri (j + 1) : ℝ) := by positivity
  have h2 : (0 : ℝ) ≤ (mub m) ^ (tri (j + 1) - 1) := pow_nonneg hm _
  have h3 : (0 : ℝ) ≤ (rq : ℝ) := by exact_mod_cast hrq
  positivity

end

end Work.Cert
