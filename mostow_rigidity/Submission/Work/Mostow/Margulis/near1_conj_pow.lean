import Mathlib
import Submission.Work.Mostow.margulisPairDefs
import Submission.Work.Mostow.abs_mat_le_tpart_actO
import Submission.Work.Mostow.poSheet

/-!
# Conjugating an entrywise-near-identity matrix by a power of a stabiliser

If `Q ∈ O(n,1)` fixes the base point of the chart (`actO Q 0 = 0`, so `Q` lies in the compact
subgroup `O(n) × {±1}`), then every entry of `mat Q` (and of `mat Q⁻¹`) is bounded by `1`: this is
`abs_mat_le_tpart_actO` together with `tpart (actO Q 0) = tpart 0 = 1`, and the inverse is handled
by the explicit formula `mat A⁻¹ i j = pmSign i * pmSign j * mat A j i`.

Consequently conjugation by `Q ^ i` multiplies the entrywise defect of a matrix by at most the
number `(n+1)^2 = msz n ^ 2` of terms of the double sum:

`Near1 B β ⟹ Near1 (Q^i * B * (Q^i)⁻¹) ((msz n)^2 * β)`.
-/

namespace Work.Mostow.Margulis

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory Matrix

noncomputable section

variable {n : ℕ}

/-- Every entry of `mat A` is bounded by `1` when `A` fixes the base point `0`. -/
lemma abs_mat_le_one_of_actO_fix {A : Submission.Mostow.O1 n}
    (hA : Submission.Mostow.actO A (0 : Submission.Mostow.E n) = 0) (i j : Fin n ⊕ Fin 1) :
    |Submission.Mostow.mat A i j| ≤ 1 := by
  have ht0 : Submission.Mostow.tpart (0 : Submission.Mostow.E n) = 1 := by
    simp [Submission.Mostow.tpart]
  have h := Work.Mostow.abs_mat_le_tpart_actO A i j
  rw [hA, ht0] at h
  exact h

theorem near1_conj_pow (n : ℕ) (Q B : Submission.Mostow.O1 n) (β : ℝ) (i : ℕ)
    (hQ : Submission.Mostow.actO Q (0 : Submission.Mostow.E n) = 0)
    (hB : Work.Mostow.Near1 B β) :
    Work.Mostow.Near1 (Q ^ i * B * (Q ^ i)⁻¹) ((Work.Mostow.msz n) ^ 2 * β) := by
  have hβ : 0 ≤ β := hB.nonneg
  have ht0 : Submission.Mostow.tpart (0 : Submission.Mostow.E n) = 1 := by
    simp [Submission.Mostow.tpart]
  -- powers of `Q` also fix the base point
  have hQP : Submission.Mostow.actO (Q ^ i) (0 : Submission.Mostow.E n) = 0 := by
    induction i with
    | zero => simpa using Work.Mostow.poSheet_actO_one (0 : Submission.Mostow.E n)
    | succ k ih => rw [pow_succ, Work.Mostow.poSheet_actO_mul, hQ, ih]
  have hM : ∀ p q : Fin n ⊕ Fin 1, |Submission.Mostow.mat (Q ^ i) p q| ≤ 1 :=
    fun p q => abs_mat_le_one_of_actO_fix hQP p q
  have hMi : ∀ p q : Fin n ⊕ Fin 1, |Submission.Mostow.mat ((Q ^ i)⁻¹) p q| ≤ 1 := by
    intro p q
    rw [Work.Mostow.mat_inv_entry, abs_mul, abs_mul, Work.Mostow.abs_pmSign,
      Work.Mostow.abs_pmSign, one_mul, one_mul]
    exact hM q p
  have hMM' : Submission.Mostow.mat (Q ^ i) * Submission.Mostow.mat ((Q ^ i)⁻¹) = 1 := by
    have h : Submission.Mostow.mat ((Q ^ i) * (Q ^ i)⁻¹) =
        Submission.Mostow.mat (Q ^ i) * Submission.Mostow.mat ((Q ^ i)⁻¹) :=
      Work.Mostow.mat_mul_coe _ _
    rw [mul_inv_cancel, Work.Mostow.mat_one_coe] at h
    exact h.symm
  -- the conjugated matrix is the identity plus `Q^i (B - 1) (Q^i)⁻¹`
  have hgoal : Submission.Mostow.mat (Q ^ i) * (Submission.Mostow.mat B - 1) *
      Submission.Mostow.mat ((Q ^ i)⁻¹)
      = Submission.Mostow.mat (Q ^ i) * Submission.Mostow.mat B *
        Submission.Mostow.mat ((Q ^ i)⁻¹) - 1 := by
    rw [Matrix.mul_sub, Matrix.sub_mul, mul_one, hMM']
  have hL : Submission.Mostow.mat (Q ^ i * B * (Q ^ i)⁻¹)
      = Submission.Mostow.mat (Q ^ i) * Submission.Mostow.mat B *
        Submission.Mostow.mat ((Q ^ i)⁻¹) := by
    rw [Work.Mostow.mat_mul_coe, Work.Mostow.mat_mul_coe, Work.Mostow.mat_inv_coe]
  have hkey : Submission.Mostow.mat (Q ^ i * B * (Q ^ i)⁻¹) - 1
      = Submission.Mostow.mat (Q ^ i) * (Submission.Mostow.mat B - 1) *
        Submission.Mostow.mat ((Q ^ i)⁻¹) := by
    rw [hL, ← hgoal]
  have hN : ∀ l k : Fin n ⊕ Fin 1, |(Submission.Mostow.mat B - 1) l k| ≤ β := by
    intro l k
    rw [Work.Mostow.sub_one_entry B l k]
    exact hB l k
  have hβm : 0 ≤ Work.Mostow.msz n * β :=
    mul_nonneg (Work.Mostow.msz_nonneg n) hβ
  intro a b
  -- bound the entries of `Q^i (B - 1)`
  have hX : ∀ k : Fin n ⊕ Fin 1,
      |(Submission.Mostow.mat (Q ^ i) * (Submission.Mostow.mat B - 1)) a k| ≤
        Work.Mostow.msz n * β := by
    intro k
    calc |(Submission.Mostow.mat (Q ^ i) * (Submission.Mostow.mat B - 1)) a k|
        = |∑ l, Submission.Mostow.mat (Q ^ i) a l * (Submission.Mostow.mat B - 1) l k| := by
          rw [Matrix.mul_apply]
      _ ≤ ∑ l, |Submission.Mostow.mat (Q ^ i) a l * (Submission.Mostow.mat B - 1) l k| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _l, (1 : ℝ) * β := by
          refine Finset.sum_le_sum fun l _ => ?_
          rw [abs_mul]
          exact mul_le_mul (hM a l) (hN l k) (abs_nonneg _) (by norm_num)
      _ = Work.Mostow.msz n * β := by
          simp only [one_mul]
          exact Work.Mostow.sum_const_sum n β
  have hentry : Submission.Mostow.mat (Q ^ i * B * (Q ^ i)⁻¹) a b - Work.Mostow.dE n a b
      = (Submission.Mostow.mat (Q ^ i) * (Submission.Mostow.mat B - 1) *
          Submission.Mostow.mat ((Q ^ i)⁻¹)) a b := by
    rw [← Work.Mostow.sub_one_entry (Q ^ i * B * (Q ^ i)⁻¹) a b, hkey]
  rw [hentry, Matrix.mul_apply]
  calc |∑ k, (Submission.Mostow.mat (Q ^ i) * (Submission.Mostow.mat B - 1)) a k *
          Submission.Mostow.mat ((Q ^ i)⁻¹) k b|
      ≤ ∑ k, |(Submission.Mostow.mat (Q ^ i) * (Submission.Mostow.mat B - 1)) a k| *
            |Submission.Mostow.mat ((Q ^ i)⁻¹) k b| := by
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_of_eq ?_)
        exact Finset.sum_congr rfl fun k _ => abs_mul _ _
    _ ≤ ∑ _k, (Work.Mostow.msz n * β) * 1 := by
        refine Finset.sum_le_sum fun k _ => ?_
        exact mul_le_mul (hX k) (hMi k b) (abs_nonneg _) hβm
    _ = (Work.Mostow.msz n) ^ 2 * β := by
        rw [Work.Mostow.sum_const_sum]
        ring

end

end Work.Mostow.Margulis
