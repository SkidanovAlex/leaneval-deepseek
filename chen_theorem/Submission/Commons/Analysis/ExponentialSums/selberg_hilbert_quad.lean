import Mathlib
import Submission.Commons.Analysis.ExponentialSums.sum_inv_sq_le_separated
import Submission.Commons.LinearAlgebra.Matrix.selberg_eigen_identity

namespace Commons.Analysis.ExponentialSums

open scoped BigOperators
open Finset

private lemma sum_erase_eq_sum_ite {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι)
    (g : ι → ℝ) :
    (∑ j, (if i = j then 0 else g j)) = ∑ j ∈ Finset.univ.erase i, g j := by
  rw [(Finset.add_sum_erase (Finset.univ) (fun j => if i = j then 0 else g j)
        (Finset.mem_univ i)).symm]
  rw [if_pos rfl, zero_add]
  apply Finset.sum_congr rfl
  intro j hj
  have hij : ¬ (i = j) := by
    rw [Finset.mem_erase] at hj
    exact fun h => hj.1 h.symm
  rw [if_neg hij]

private lemma sum_erase_comm {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ι → ι → ℝ) :
    (∑ i, ∑ j ∈ Finset.univ.erase i, g i j) = ∑ j, ∑ i ∈ Finset.univ.erase j, g i j := by
  have h1 : ∀ i, (∑ j ∈ Finset.univ.erase i, g i j) = ∑ j, (if i = j then 0 else g i j) :=
    fun i => (sum_erase_eq_sum_ite i (fun j => g i j)).symm
  simp_rw [h1]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← sum_erase_eq_sum_ite j (fun i => g i j)]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : i = j
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun hj => h hj.symm)]

/-- Montgomery–Vaughan / Selberg quadratic form bound for the real-line Hilbert kernel.
Let `λ : ι → ℝ` be injective and `δ`-separated (`δ ≤ |λ i - λ j|` for `i ≠ j`).  Let
`U i j = (λ i - λ j)⁻¹` off the diagonal and `U i i = 0`.  If `z : ι → ℂ` is an "eigenvector" of
the associated antilinear kernel in the sense that `∑ j, U i j * z j = -(I * a) * z i` for some
real `a`, then `∑ i, ‖∑ j, U i j * z j‖ ^ 2 ≤ (π ^ 2 / δ ^ 2) * ∑ i, ‖z i‖ ^ 2`. -/
theorem selberg_hilbert_quad {ι : Type*} [Fintype ι] [DecidableEq ι] (lam : ι → ℝ) {δ : ℝ}
    (hδ : 0 < δ) (hinj : Function.Injective lam)
    (hsep : ∀ i j : ι, i ≠ j → δ ≤ |lam i - lam j|) (z : ι → ℂ) {a : ℝ}
    (hrel : ∀ i, ∑ j, (if i = j then 0 else (((lam i - lam j : ℝ) : ℂ))⁻¹) * z j
        = -(Complex.I * ((a : ℝ) : ℂ)) * z i) :
    ∑ i, ‖∑ j, (if i = j then 0 else (((lam i - lam j : ℝ) : ℂ))⁻¹) * z j‖ ^ 2
      ≤ (Real.pi ^ 2 / δ ^ 2) * ∑ i, ‖z i‖ ^ 2 := by
  classical
  have hpt : ∀ i j : ι, ‖z j‖ ^ 2 + 2 * (star (z i) * z j).re ≤ ‖z i‖ ^ 2 + 2 * ‖z j‖ ^ 2 := by
    intro i j
    have h1 : (star (z i) * z j).re ≤ ‖z i‖ * ‖z j‖ := by
      calc (star (z i) * z j).re ≤ ‖star (z i) * z j‖ := Complex.re_le_norm _
        _ = ‖star (z i)‖ * ‖z j‖ := norm_mul _ _
        _ = ‖z i‖ * ‖z j‖ := by rw [norm_star]
    nlinarith [h1, norm_nonneg (z i), norm_nonneg (z j), sq_nonneg (‖z i‖ - ‖z j‖)]
  have hrel' : ∀ i, ∑ j, (if i = j then 0 else (((lam i - lam j : ℝ) : ℂ))⁻¹) * z j
        = (Complex.I * (((-a : ℝ)) : ℂ)) * z i := by
    intro i
    rw [hrel i]
    push_cast
    ring
  have hid := Commons.LinearAlgebra.Matrix.selberg_eigen_identity lam hinj z (-a) hrel'
  have hid' : ∀ i, a ^ 2 * ‖z i‖ ^ 2
      = ∑ j ∈ Finset.univ.erase i,
          ((lam i - lam j) ^ 2)⁻¹ * (‖z j‖ ^ 2 + 2 * (star (z i) * z j).re) := by
    intro i
    have h := hid i
    rw [show (-a) ^ 2 = a ^ 2 by ring] at h
    rw [h, sum_erase_eq_sum_ite i
      (fun j => ((lam i - lam j) ^ 2)⁻¹ * (‖z j‖ ^ 2 + 2 * (star (z i) * z j).re))]
  have hbound : ∀ i, a ^ 2 * ‖z i‖ ^ 2 ≤ ‖z i‖ ^ 2 * (∑ j ∈ Finset.univ.erase i, ((lam i - lam j) ^ 2)⁻¹)
      + 2 * ∑ j ∈ Finset.univ.erase i, ((lam i - lam j) ^ 2)⁻¹ * ‖z j‖ ^ 2 := by
    intro i
    rw [hid' i]
    have step : ∑ j ∈ Finset.univ.erase i,
          ((lam i - lam j) ^ 2)⁻¹ * (‖z j‖ ^ 2 + 2 * (star (z i) * z j).re)
        ≤ ∑ j ∈ Finset.univ.erase i,
          ((lam i - lam j) ^ 2)⁻¹ * (‖z i‖ ^ 2 + 2 * ‖z j‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (hpt i j) (inv_nonneg.mpr (sq_nonneg _))
    refine step.trans (le_of_eq ?_)
    trans ∑ j ∈ Finset.univ.erase i,
          (((lam i - lam j) ^ 2)⁻¹ * ‖z i‖ ^ 2
            + 2 * (((lam i - lam j) ^ 2)⁻¹ * ‖z j‖ ^ 2))
    · apply Finset.sum_congr rfl; intro j _; ring
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
    ring
  have hsum1 : ∑ i, a ^ 2 * ‖z i‖ ^ 2
      ≤ ∑ i, (‖z i‖ ^ 2 * (∑ j ∈ Finset.univ.erase i, ((lam i - lam j) ^ 2)⁻¹)
          + 2 * ∑ j ∈ Finset.univ.erase i, ((lam i - lam j) ^ 2)⁻¹ * ‖z j‖ ^ 2) :=
    Finset.sum_le_sum (fun i _ => hbound i)
  have hdouble : ∑ i, ∑ j ∈ Finset.univ.erase i, ((lam i - lam j) ^ 2)⁻¹ * ‖z j‖ ^ 2
      = ∑ i, ‖z i‖ ^ 2 * (∑ j ∈ Finset.univ.erase i, ((lam i - lam j) ^ 2)⁻¹) := by
    rw [sum_erase_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_mul]
    rw [show (∑ i ∈ Finset.univ.erase j, ((lam i - lam j) ^ 2)⁻¹)
        = ∑ i ∈ Finset.univ.erase j, ((lam j - lam i) ^ 2)⁻¹ by
          apply Finset.sum_congr rfl
          intro i _
          rw [show (lam i - lam j) ^ 2 = (lam j - lam i) ^ 2 by ring]]
    ring
  have hsum2 : ∑ i, (‖z i‖ ^ 2 * (∑ j ∈ Finset.univ.erase i, ((lam i - lam j) ^ 2)⁻¹)
        + 2 * ∑ j ∈ Finset.univ.erase i, ((lam i - lam j) ^ 2)⁻¹ * ‖z j‖ ^ 2)
      = 3 * ∑ i, ‖z i‖ ^ 2 * (∑ j ∈ Finset.univ.erase i, ((lam i - lam j) ^ 2)⁻¹) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hdouble]
    ring
  have hR : ∀ i, (∑ j ∈ Finset.univ.erase i, ((lam i - lam j) ^ 2)⁻¹)
      ≤ Real.pi ^ 2 / (3 * δ ^ 2) := by
    intro i
    set A : Finset ℝ := (Finset.univ.erase i).image (fun j => lam i - lam j) with hA
    have h0 : ∀ a ∈ A, δ ≤ |a| := by
      intro a ha
      rw [hA, Finset.mem_image] at ha
      obtain ⟨j, hj, rfl⟩ := ha
      rw [Finset.mem_erase] at hj
      exact hsep i j (fun h => hj.1 h.symm)
    have hsep' : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → δ ≤ |a - b| := by
      intro a ha b hb hab
      rw [hA, Finset.mem_image] at ha hb
      obtain ⟨j, hj, rfl⟩ := ha
      obtain ⟨k, hk, rfl⟩ := hb
      rw [Finset.mem_erase] at hj hk
      have hjk : j ≠ k := fun h => hab (by rw [h])
      have := hsep j k hjk
      rwa [show (lam i - lam j) - (lam i - lam k) = lam k - lam j by ring, abs_sub_comm]
    have hbase := Commons.Analysis.ExponentialSums.sum_inv_sq_le_separated
      (A := A) (δ := δ) hδ h0 hsep'
    have himg : ∑ a ∈ A, (1 : ℝ) / a ^ 2 = ∑ j ∈ Finset.univ.erase i, (1 : ℝ) / (lam i - lam j) ^ 2 := by
      rw [hA, Finset.sum_image]
      intro x _ y _ hxy
      exact hinj (sub_right_inj.mp hxy)
    rw [himg] at hbase
    refine le_trans (Finset.sum_le_sum (fun j _ => ?_)) hbase
    rw [one_div]
  have hfinal : ∑ i, a ^ 2 * ‖z i‖ ^ 2 ≤ (Real.pi ^ 2 / δ ^ 2) * ∑ i, ‖z i‖ ^ 2 := by
    have h3 : (3 : ℝ) * (Real.pi ^ 2 / (3 * δ ^ 2)) = Real.pi ^ 2 / δ ^ 2 := by
      field_simp
    calc ∑ i, a ^ 2 * ‖z i‖ ^ 2
        ≤ 3 * ∑ i, ‖z i‖ ^ 2 * (∑ j ∈ Finset.univ.erase i, ((lam i - lam j) ^ 2)⁻¹) :=
          hsum1.trans hsum2.le
      _ ≤ 3 * ∑ i, ‖z i‖ ^ 2 * (Real.pi ^ 2 / (3 * δ ^ 2)) := by
          apply mul_le_mul_of_nonneg_left
          · apply Finset.sum_le_sum
            intro i _
            exact mul_le_mul_of_nonneg_left (hR i) (sq_nonneg _)
          · norm_num
      _ = (Real.pi ^ 2 / δ ^ 2) * ∑ i, ‖z i‖ ^ 2 := by
          rw [← Finset.sum_mul]
          calc 3 * ((∑ i, ‖z i‖ ^ 2) * (Real.pi ^ 2 / (3 * δ ^ 2)))
              = (∑ i, ‖z i‖ ^ 2) * (3 * (Real.pi ^ 2 / (3 * δ ^ 2))) := by ring
            _ = (∑ i, ‖z i‖ ^ 2) * (Real.pi ^ 2 / δ ^ 2) := by rw [h3]
            _ = (Real.pi ^ 2 / δ ^ 2) * (∑ i, ‖z i‖ ^ 2) := by ring
  have hLHS : ∑ i, ‖∑ j, (if i = j then 0 else (((lam i - lam j : ℝ) : ℂ))⁻¹) * z j‖ ^ 2
        = ∑ i, a ^ 2 * ‖z i‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hrel i]
    have hnorm : ‖-(Complex.I * ((a : ℝ) : ℂ)) * z i‖ = |a| * ‖z i‖ := by
      calc ‖-(Complex.I * ((a : ℝ) : ℂ)) * z i‖
          = ‖-(Complex.I * ((a : ℝ) : ℂ))‖ * ‖z i‖ := norm_mul _ _
        _ = ‖Complex.I * ((a : ℝ) : ℂ)‖ * ‖z i‖ := by rw [norm_neg]
        _ = (‖Complex.I‖ * ‖((a : ℝ) : ℂ)‖) * ‖z i‖ := by rw [norm_mul]
        _ = |a| * ‖z i‖ := by rw [Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm, mul_pow, sq_abs]
  rw [hLHS]
  exact hfinal

end Commons.Analysis.ExponentialSums
