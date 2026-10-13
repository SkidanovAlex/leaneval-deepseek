/-
# `Work.FTS.ClassC.bessel_cmode` — Bessel's inequality for the angular modes `eFam`

For every `z` and every `N`, the sum of the squared angular mode coefficients of the slice
`θ ↦ F z θ`, each normalised by the `L²(Iθ, cos θ dθ)`-norm of the Dirichlet eigenfunction
`eFam m` (`Work.FTS.PhiStar.Gegenbauer.eFam m θ = cos θ · C^{(3/2)}_{2m+1}(sin θ)`), is
bounded by the weighted `L²`-norm of the slice:

  `∑_{m ≤ N} (∫_{Iθ} F z θ · e_m θ · cos θ)² / (∫_{Iθ} e_m θ² · cos θ)`
    `≤ ∫_{Iθ} (F z θ)² · cos θ`.

This is the classical Bessel inequality for the orthogonal system `eFam m` in
`L²(Iθ, cos θ dθ)` (orthogonality `eFam_orthogonal`, norms `eFam_norm_fts`); equivalently it is
the statement that the orthogonal projection onto `span{e_0, …, e_N}` has norm `≤ 1`.

**Route.**  The whole `L²`-content is already available: the sibling
`Work.EllipticEst.ModalSolution.cmode_bessel` proves the *normalised* form

  `∑_{m ≤ N} eNorm m · (cmode m F z)² ≤ ∫⁻_θ ofReal (F z θ² · cos θ)`

(`eNorm m = ∫_{Iθ} e_m² cos`, `cmode m F z = (∫_{Iθ} F z θ e_m θ cos θ)/eNorm m`) with
Mathlib's `Orthonormal.sum_inner_products_le`.  We only have to

* turn the `ℝ≥0∞`-integral of the bound into `ENNReal.ofReal` of the real integral
  (`MeasureTheory.ofReal_integral_eq_lintegral_ofReal`, using the integrability `hint` and the
  a.e. nonnegativity of `(F z θ)² cos θ` on `Iθ`),
* identify the normalised summands with the ones of the statement: `eNorm m` *is* the
  denominator and `cmode m F z = A m / eNorm m` where `A m` is the numerator of the statement
  (`cmode_eq` plus the `√cos · √cos = cos` identification on `Iθ`).

The `ℝ≥0∞`-to-`ℝ` comparison is `ENNReal.ofReal_le_ofReal_iff`; the division algebra is
`field_simp`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_orthogonal
import Submission.Work.FTS.PhiStar.Gegenbauer.FamNormValue
import Submission.Work.EllipticEst.ModalSolution.cmode_bessel

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC

theorem bessel_cmode (F : ℝ → ℝ → ℝ) (z : ℝ) (N : ℕ)
    (hmeas : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => F z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hint : MeasureTheory.IntegrableOn (fun θ => (F z θ) ^ 2 * Real.cos θ) Work.Spaces.Iθ) :
    (∑ m ∈ Finset.range (N + 1),
        (∫ θ in Work.Spaces.Iθ,
            F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) ^ 2
          / (∫ θ in Work.Spaces.Iθ,
              Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ))
      ≤ ∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2 * Real.cos θ := by
  have hIθ_meas : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hInt : MeasureTheory.Integrable (fun θ => (F z θ) ^ 2 * Real.cos θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hint
  -- the weight `cos` is nonnegative on `Iθ`, so the slice energy is a.e. nonnegative
  have hnonneg_ae : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ => (F z θ) ^ 2 * Real.cos θ) := by
    show ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      0 ≤ (F z θ) ^ 2 * Real.cos θ
    rw [MeasureTheory.ae_restrict_iff' hIθ_meas]
    filter_upwards with θ hθ
    exact mul_nonneg (sq_nonneg _)
      (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  have hnonnegR : 0 ≤ ∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2 * Real.cos θ :=
    MeasureTheory.integral_nonneg_of_ae hnonneg_ae
  -- Bessel's inequality in its normalised `ℝ≥0∞`-form, with the bound rewritten as `ofReal`
  have hb := Work.EllipticEst.ModalSolution.cmode_bessel F z N
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (f := fun θ => (F z θ) ^ 2 * Real.cos θ) hInt hnonneg_ae] at hb
  have hmain : (∑ m ∈ Finset.range (N + 1),
      Work.EllipticEst.ModalSolution.eNorm m *
        (Work.FTS.PhiStar.Series.cmode m F z) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2 * Real.cos θ :=
    (ENNReal.ofReal_le_ofReal_iff hnonnegR).1 hb
  -- the normalised summands are the summands of the statement
  have hsum : (∑ m ∈ Finset.range (N + 1),
      Work.EllipticEst.ModalSolution.eNorm m * (Work.FTS.PhiStar.Series.cmode m F z) ^ 2)
      = ∑ m ∈ Finset.range (N + 1),
        (∫ θ in Work.Spaces.Iθ, F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) ^ 2
          / (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ) := by
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Work.EllipticEst.ModalSolution.cmode_eq m F z]
    rw [Work.EllipticEst.ModalSolution.eNorm]
    -- the `√cos · √cos` form of `bInt` is the numerator of the statement
    have hbInt : Work.EllipticEst.ModalSolution.bInt m F z
        = ∫ θ in Work.Spaces.Iθ, F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ := by
      rw [Work.EllipticEst.ModalSolution.bInt]
      refine MeasureTheory.setIntegral_congr_fun hIθ_meas (fun θ hθ => ?_)
      have hc : 0 ≤ Real.cos θ :=
        Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
      have hsq : Real.sqrt (Real.cos θ) * Real.sqrt (Real.cos θ) = Real.cos θ := by
        rw [← sq, Real.sq_sqrt hc]
      calc (Real.sqrt (Real.cos θ) * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
              * (Real.sqrt (Real.cos θ) * F z θ)
          = (Real.sqrt (Real.cos θ) * Real.sqrt (Real.cos θ))
              * (Work.FTS.PhiStar.Gegenbauer.eFam m θ * F z θ) := by ring
        _ = Real.cos θ * (Work.FTS.PhiStar.Gegenbauer.eFam m θ * F z θ) := by rw [hsq]
        _ = F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ := by ring
    rw [hbInt]
    field_simp
  rw [hsum] at hmain
  exact hmain

end Work.FTS.ClassC
