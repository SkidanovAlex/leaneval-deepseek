import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.EllipticEst.ModalSolution.cmode_bessel
import Submission.Work.FTS.ClassC.bessel_cmode
import Submission.Work.Blocks.IMC.cs_integral_mul_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.ClassCHon.CmpSupp

set_option autoImplicit false

/-- **The mode coefficients of a continuous, compactly supported source are `O(1/√(eNorm m))`.**

`cmode m F t` is the quotient `bInt m F t / eNorm m`, where `bInt` is the scalar product of the
slice `F t ·` with the mode `eFam m` in `L²(Iθ, cos θ dθ)`.  Cauchy–Schwarz bounds the numerator
by `√(∫_{Iθ} (F t θ)² cos θ) · √(eNorm m)`, and the first factor is uniformly bounded on the
compact rectangle `[a,b] × Iθ` because `F` is continuous there.  (The support hypothesis is not
needed: the estimate is uniform on any compact set.)

This is the fifth conjunct of `cmode_facts`; it is what makes the mode series
`Σ_m cmode m F z · e_m(θ)` comparable with the `L²`-normalised modes. -/
theorem cmode_abs_le_of_continuous {a b : ℝ} {F : ℝ → ℝ → ℝ}
    (hFc : Continuous (Function.uncurry F))
    (hsupp : ∀ z θ : ℝ, z ∉ Set.Icc a b → F z θ = 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ m : ℕ, ∀ t ∈ Set.Icc a b,
        |Work.FTS.PhiStar.Series.cmode m F t|
          ≤ K / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m) := by
  have hπ : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hIθ : Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) := rfl
  have hmeas : MeasurableSet Work.Spaces.Iθ := by rw [hIθ]; exact measurableSet_Icc
  have hcomp : IsCompact Work.Spaces.Iθ := by rw [hIθ]; exact isCompact_Icc
  -- the rectangle `[a,b] × Iθ` is compact and `F` is continuous there
  have hrect : IsCompact (Set.Icc a b ×ˢ Work.Spaces.Iθ) := isCompact_Icc.prod hcomp
  obtain ⟨C, hC⟩ := hrect.exists_bound_of_continuousOn hFc.continuousOn
  -- replace `C` by a nonnegative bound (`C` is only determined up to the empty-set case)
  set C' : ℝ := max C 0 with hC'def
  have hC'nn : 0 ≤ C' := le_max_right _ _
  have hC'bd : ∀ x ∈ Set.Icc a b ×ˢ Work.Spaces.Iθ, ‖Function.uncurry F x‖ ≤ C' :=
    fun x hx => le_trans (hC x hx) (le_max_left _ _)
  -- `∫_{Iθ} cos = 1`
  have hcosint : (∫ θ in Work.Spaces.Iθ, Real.cos θ) = 1 := by
    rw [hIθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hπ, integral_cos, Real.sin_pi_div_two, Real.sin_zero]
    ring
  refine ⟨C' + 1, by linarith, ?_⟩
  intro m t ht
  -- the two factors of the Cauchy–Schwarz inequality, and their continuity
  have hFt : Continuous (fun θ : ℝ => F t θ) :=
    hFc.comp (continuous_const.prodMk continuous_id)
  have hEcont : Continuous (fun θ : ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m θ) :=
    Work.EllipticEst.ModalSolution.continuous_eFam m
  have hfcont : Continuous (fun θ : ℝ => Real.sqrt (Real.cos θ) * F t θ) :=
    (Real.continuous_sqrt.comp Real.continuous_cos).mul hFt
  have hgcont : Continuous (fun θ : ℝ =>
      Real.sqrt (Real.cos θ) * Work.FTS.PhiStar.Gegenbauer.eFam m θ) :=
    (Real.continuous_sqrt.comp Real.continuous_cos).mul hEcont
  have hfasm : AEStronglyMeasurable (fun θ : ℝ => Real.sqrt (Real.cos θ) * F t θ)
      (volume.restrict Work.Spaces.Iθ) :=
    hfcont.continuousOn.aestronglyMeasurable hmeas
  have hgasm : AEStronglyMeasurable (fun θ : ℝ =>
      Real.sqrt (Real.cos θ) * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
      (volume.restrict Work.Spaces.Iθ) :=
    hgcont.continuousOn.aestronglyMeasurable hmeas
  have hfint : Integrable (fun θ : ℝ => (Real.sqrt (Real.cos θ) * F t θ) ^ 2)
      (volume.restrict Work.Spaces.Iθ) :=
    ContinuousOn.integrableOn_compact hcomp (hfcont.pow 2).continuousOn
  have hgint : Integrable (fun θ : ℝ =>
      (Real.sqrt (Real.cos θ) * Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2)
      (volume.restrict Work.Spaces.Iθ) :=
    ContinuousOn.integrableOn_compact hcomp (hgcont.pow 2).continuousOn
  -- Cauchy–Schwarz in `L²(Iθ, cos θ dθ)`
  have hCS := Work.Blocks.IMC.cs_integral_mul_le (volume.restrict Work.Spaces.Iθ)
    hgasm hfasm hgint hfint
  have hCSb : |Work.EllipticEst.ModalSolution.bInt m F t| ≤
      Real.sqrt (∫ θ in Work.Spaces.Iθ,
          (Real.sqrt (Real.cos θ) * Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ,
            (Real.sqrt (Real.cos θ) * F t θ) ^ 2) := by
    simpa only [Work.EllipticEst.ModalSolution.bInt] using hCS
  -- the two squared norms
  have hG2 : (∫ θ in Work.Spaces.Iθ,
        (Real.sqrt (Real.cos θ) * Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2)
      = Work.EllipticEst.ModalSolution.eNorm m := by
    rw [Work.EllipticEst.ModalSolution.eNorm]
    refine MeasureTheory.setIntegral_congr_fun hmeas (fun θ hθ => ?_)
    rw [hIθ] at hθ
    have hcos : 0 ≤ Real.cos θ :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    rw [mul_pow, Real.sq_sqrt hcos]
    ring
  have hF2 : (∫ θ in Work.Spaces.Iθ, (Real.sqrt (Real.cos θ) * F t θ) ^ 2)
      = ∫ θ in Work.Spaces.Iθ, (F t θ) ^ 2 * Real.cos θ := by
    refine MeasureTheory.setIntegral_congr_fun hmeas (fun θ hθ => ?_)
    rw [hIθ] at hθ
    have hcos : 0 ≤ Real.cos θ :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    rw [mul_pow, Real.sq_sqrt hcos]
    ring
  -- the slice energy is bounded by `C'²`
  have hEbound : (∫ θ in Work.Spaces.Iθ, (F t θ) ^ 2 * Real.cos θ) ≤ C' ^ 2 := by
    have hpt : ∀ θ ∈ Work.Spaces.Iθ, (F t θ) ^ 2 * Real.cos θ ≤ C' ^ 2 * Real.cos θ := by
      intro θ hθ
      have hθ' : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by rwa [← hIθ]
      have hcos : 0 ≤ Real.cos θ :=
        Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ'.1, Real.pi_pos], hθ'.2⟩
      have h1 : |F t θ| ≤ C' := by
        have h := hC'bd (t, θ) ⟨ht, hθ⟩
        simpa [Function.uncurry, Real.norm_eq_abs] using h
      have h2 : (F t θ) ^ 2 ≤ C' ^ 2 := by
        have h3 := pow_le_pow_left₀ (abs_nonneg (F t θ)) h1 2
        rwa [sq_abs] at h3
      exact mul_le_mul_of_nonneg_right h2 hcos
    have hint1 : IntegrableOn (fun θ : ℝ => (F t θ) ^ 2 * Real.cos θ) Work.Spaces.Iθ :=
      ContinuousOn.integrableOn_compact hcomp
        ((hFt.pow 2).mul Real.continuous_cos).continuousOn
    have hint2 : IntegrableOn (fun θ : ℝ => C' ^ 2 * Real.cos θ) Work.Spaces.Iθ :=
      ContinuousOn.integrableOn_compact hcomp
        (continuous_const.mul Real.continuous_cos).continuousOn
    calc (∫ θ in Work.Spaces.Iθ, (F t θ) ^ 2 * Real.cos θ)
        ≤ ∫ θ in Work.Spaces.Iθ, C' ^ 2 * Real.cos θ :=
          MeasureTheory.setIntegral_mono_on hint1 hint2 hmeas hpt
      _ = C' ^ 2 * ∫ θ in Work.Spaces.Iθ, Real.cos θ := by
          rw [MeasureTheory.integral_const_mul]
      _ = C' ^ 2 := by rw [hcosint, mul_one]
  -- the numerator bound
  have hnum : |Work.EllipticEst.ModalSolution.bInt m F t|
      ≤ C' * Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m) := by
    calc |Work.EllipticEst.ModalSolution.bInt m F t|
        ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ,
              (Real.sqrt (Real.cos θ) * Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2)
            * Real.sqrt (∫ θ in Work.Spaces.Iθ,
                (Real.sqrt (Real.cos θ) * F t θ) ^ 2) := hCSb
      _ = Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m)
            * Real.sqrt (∫ θ in Work.Spaces.Iθ, (F t θ) ^ 2 * Real.cos θ) := by
          rw [hG2, hF2, mul_comm]
      _ ≤ Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m) * C' :=
          mul_le_mul_of_nonneg_left
            (le_trans (Real.sqrt_le_sqrt hEbound) (by rw [Real.sqrt_sq hC'nn]))
            (Real.sqrt_nonneg _)
      _ = C' * Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m) := by ring
  -- division by `eNorm m > 0`
  have hNe : 0 < Work.EllipticEst.ModalSolution.eNorm m :=
    Work.EllipticEst.ModalSolution.eNorm_pos m
  have hsqne : Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hNe)
  calc |Work.FTS.PhiStar.Series.cmode m F t|
      = |Work.EllipticEst.ModalSolution.bInt m F t|
          / Work.EllipticEst.ModalSolution.eNorm m := by
        rw [Work.EllipticEst.ModalSolution.cmode_eq m F t, abs_div, abs_of_pos hNe]
    _ ≤ (C' * Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m))
          / Work.EllipticEst.ModalSolution.eNorm m :=
        div_le_div_of_nonneg_right hnum hNe.le
    _ = C' / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m) := by
        rw [div_eq_div_iff hNe.ne' hsqne]
        rw [mul_assoc, Real.mul_self_sqrt hNe.le]
    _ ≤ (C' + 1) / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m) :=
        div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)

end Work.FTS.ClassCHon.CmpSupp
