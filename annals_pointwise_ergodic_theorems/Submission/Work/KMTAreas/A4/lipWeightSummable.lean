import Mathlib
import Submission.Work.KMTAreas.A4.lipDefs

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory

/-- The lattice majorant of `lipWeight` is summable: `m ↦ ∑_{m' ∈ [1,N']} ‖ψ (ε (m - m'))‖`.

`lipWeight` is a finite linear combination of the normed translates `m ↦ ‖ψ (ε (m - m'))‖`, and
each of those is dominated by `C ⟨ε (m - m')⟩^{-12}` (`schwartz_decay`), which is summable. -/
lemma summable_lipWeight_majorant (ψ : SchwartzR) {ε : ℝ} (hε0 : 0 < ε) {N' : ℕ} :
    Summable (fun m : ℤ => ∑ y ∈ Finset.Icc 1 N', ‖(ψ : ℝ → ℂ) (ε * ((m : ℝ) - (y : ℝ)))‖) := by
  classical
  set C : ℝ := (2 : ℝ) ^ 12 * (schwartzSeminormSum ψ + 1) with hC
  have hdecay : ∀ t : ℝ, ‖(ψ : ℝ → ℂ) t‖ ≤ C * jbDecay 12 t := fun t => by
    rw [hC]; exact schwartz_decay ψ t
  exact summable_finset_sum (Finset.Icc 1 N') (fun y _ =>
    Summable.of_nonneg_of_le (fun m => norm_nonneg _)
      (fun m => hdecay _)
      ((summable_jbDecay_twelve_shift (ε := ε) hε0 (y : ℤ)).mul_left C))

theorem lipWeightSummable (ψ : Work.Analysis.InverseTheory.SchwartzR) :
    ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → ∀ {N' : ℕ}, 1 ≤ N' →
      Summable (fun m : ℤ => ‖Work.KMTAreas.A4.lipWeight ψ ε N' m‖) := by
  intro ε hε0 hε1 N' hN'
  classical
  have hN'0 : (0 : ℝ) < (N' : ℝ) := by
    have h1 : (1 : ℝ) ≤ (N' : ℝ) := by exact_mod_cast hN'
    linarith
  have hnorm_inv : ‖(((N' : ℝ)⁻¹ : ℝ) : ℂ)‖ = (N' : ℝ)⁻¹ :=
    norm_real_coe (inv_nonneg.mpr hN'0.le)
  -- the summable majorant
  have hMsumm : Summable (fun m : ℤ =>
      ∑ y ∈ Finset.Icc 1 N', ‖(ψ : ℝ → ℂ) (ε * ((m : ℝ) - (y : ℝ)))‖) :=
    summable_lipWeight_majorant ψ hε0
  -- the pointwise bound
  have hbound : ∀ m : ℤ, ‖lipWeight ψ ε N' m‖
      ≤ (ε * (N' : ℝ)⁻¹) * ∑ y ∈ Finset.Icc 1 N', ‖(ψ : ℝ → ℂ) (ε * ((m : ℝ) - (y : ℝ)))‖ := by
    intro m
    have hsplit : ‖(ε : ℂ) * (((N' : ℝ)⁻¹ : ℝ) * ∑ m' ∈ Finset.Icc 1 N',
          (ψ (ε * ((m : ℝ) - (m' : ℝ))) : ℂ))‖
        = ε * ((N' : ℝ)⁻¹ * ‖∑ m' ∈ Finset.Icc 1 N',
            (ψ (ε * ((m : ℝ) - (m' : ℝ))) : ℂ)‖) := by
      rw [norm_mul, norm_mul, norm_real_coe hε0.le, hnorm_inv]
    have hsum_le : ‖∑ m' ∈ Finset.Icc 1 N', (ψ (ε * ((m : ℝ) - (m' : ℝ))) : ℂ)‖
        ≤ ∑ y ∈ Finset.Icc 1 N', ‖(ψ : ℝ → ℂ) (ε * ((m : ℝ) - (y : ℝ)))‖ :=
      norm_sum_le _ _
    rw [lipWeight, hsplit]
    calc ε * ((N' : ℝ)⁻¹ * ‖∑ m' ∈ Finset.Icc 1 N',
              (ψ (ε * ((m : ℝ) - (m' : ℝ))) : ℂ)‖)
        ≤ ε * ((N' : ℝ)⁻¹ * ∑ y ∈ Finset.Icc 1 N',
              ‖(ψ : ℝ → ℂ) (ε * ((m : ℝ) - (y : ℝ)))‖) := by
          refine mul_le_mul_of_nonneg_left ?_ hε0.le
          exact mul_le_mul_of_nonneg_left hsum_le (inv_nonneg.mpr hN'0.le)
      _ = (ε * (N' : ℝ)⁻¹) * ∑ y ∈ Finset.Icc 1 N',
              ‖(ψ : ℝ → ℂ) (ε * ((m : ℝ) - (y : ℝ)))‖ := by ring
  exact Summable.of_nonneg_of_le (fun m => norm_nonneg _) hbound
    (hMsumm.mul_left (ε * (N' : ℝ)⁻¹))

end Work.KMTAreas.A4
