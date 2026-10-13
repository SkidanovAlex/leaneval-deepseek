import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.EllipticEst.ModalSolution.cmode_memLp
import Submission.Work.FTS.ClassC.bessel_z

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

/-- **Bessel's inequality for the mode coefficients, integrated in `z` (no radial weight).**

  `∑_{m ≤ N} ∫⁻_z eNorm m · (cmode m F z)²  ≤  ∫⁻_z ofReal (∫_θ (F z θ)² cos θ)`.

This is `Work.EllipticEst.ModalSolution.cmode_bessel` (Bessel's inequality for the angular
Dirichlet basis `eFam m` of `Lzero` in the weight `cos θ dθ`), integrated in `z` against the
unweighted Lebesgue measure: the slicewise bound is multiplied into the `z`-integral and the
finite mode sum is taken out of it (each summand is a.e. strongly measurable in `z` by
`aesm_cmode`, which is where the smoothness hypothesis is used).  The right-hand side is
`ofReal` of the honest `θ`-integral by the slice integrability hypothesis `hint`.

It is the `w ≡ 1` companion of `Work.FTS.ClassC.bessel_z` (which carries the radial weight
`w(z)² = ((1+z)²/z²)²`). -/
theorem besselZ_plain {F : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hint : ∀ z ∈ Set.Ioi (0 : ℝ), MeasureTheory.IntegrableOn
      (fun θ : ℝ => F z θ ^ 2 * Real.cos θ) Work.Spaces.Iθ) (N : ℕ) :
    (∑ m ∈ Finset.range (N + 1), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (Work.EllipticEst.ModalSolution.eNorm m *
          Work.FTS.PhiStar.Series.cmode m F z ^ 2))
      ≤ ∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, F z θ ^ 2 * Real.cos θ) := by
  -- the slicewise Bessel bound (`cmode_bessel`), with `ofReal` pushed through the finite sum
  have hpt : ∀ z : ℝ, (∑ m ∈ Finset.range (N + 1),
        ENNReal.ofReal (Work.EllipticEst.ModalSolution.eNorm m *
          (Work.FTS.PhiStar.Series.cmode m F z) ^ 2))
      ≤ ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((F z θ) ^ 2 * Real.cos θ) := by
    intro z
    have hb : ENNReal.ofReal (∑ m ∈ Finset.range (N + 1),
          Work.EllipticEst.ModalSolution.eNorm m *
            (Work.FTS.PhiStar.Series.cmode m F z) ^ 2)
        ≤ ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((F z θ) ^ 2 * Real.cos θ) :=
      Work.EllipticEst.ModalSolution.cmode_bessel F z N
    have hsplit : ENNReal.ofReal (∑ m ∈ Finset.range (N + 1),
          Work.EllipticEst.ModalSolution.eNorm m *
            (Work.FTS.PhiStar.Series.cmode m F z) ^ 2)
        = ∑ m ∈ Finset.range (N + 1), ENNReal.ofReal
            (Work.EllipticEst.ModalSolution.eNorm m *
              (Work.FTS.PhiStar.Series.cmode m F z) ^ 2) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro m _
      exact mul_nonneg (le_of_lt (Work.EllipticEst.ModalSolution.eNorm_pos m)) (sq_nonneg _)
    rwa [hsplit] at hb
  -- integrate the pointwise-in-`z` inequality
  have h1 : (∫⁻ z in Set.Ioi (0 : ℝ), (∑ m ∈ Finset.range (N + 1),
        ENNReal.ofReal (Work.EllipticEst.ModalSolution.eNorm m *
          (Work.FTS.PhiStar.Series.cmode m F z) ^ 2)))
      ≤ ∫⁻ z in Set.Ioi (0 : ℝ), (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal ((F z θ) ^ 2 * Real.cos θ)) :=
    MeasureTheory.lintegral_mono hpt
  -- the summands are a.e. measurable in `z`, so the sum comes out of the `z`-integral
  have haem : ∀ m : ℕ, AEMeasurable
      (fun z : ℝ => ENNReal.ofReal (Work.EllipticEst.ModalSolution.eNorm m *
        (Work.FTS.PhiStar.Series.cmode m F z) ^ 2))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    intro m
    have hcm : AEMeasurable (fun z : ℝ => Work.FTS.PhiStar.Series.cmode m F z)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      (Work.EllipticEst.ModalSolution.aesm_cmode hsm m).aemeasurable
    exact ((hcm.pow_const 2).const_mul (Work.EllipticEst.ModalSolution.eNorm m)).ennreal_ofReal
  have hsumsplit : (∫⁻ z in Set.Ioi (0 : ℝ), (∑ m ∈ Finset.range (N + 1),
        ENNReal.ofReal (Work.EllipticEst.ModalSolution.eNorm m *
          (Work.FTS.PhiStar.Series.cmode m F z) ^ 2)))
      = ∑ m ∈ Finset.range (N + 1), ∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (Work.EllipticEst.ModalSolution.eNorm m *
            (Work.FTS.PhiStar.Series.cmode m F z) ^ 2) := by
    refine Finset.induction_on (Finset.range (N + 1)) ?_ ?_
    · simp
    · intro a s ha ih
      have hL : (∫⁻ z in Set.Ioi (0 : ℝ), (∑ m ∈ insert a s,
            ENNReal.ofReal (Work.EllipticEst.ModalSolution.eNorm m *
              (Work.FTS.PhiStar.Series.cmode m F z) ^ 2)))
          = ∫⁻ z in Set.Ioi (0 : ℝ),
              (ENNReal.ofReal (Work.EllipticEst.ModalSolution.eNorm a *
                (Work.FTS.PhiStar.Series.cmode a F z) ^ 2)
              + ∑ m ∈ s, ENNReal.ofReal (Work.EllipticEst.ModalSolution.eNorm m *
                  (Work.FTS.PhiStar.Series.cmode m F z) ^ 2)) :=
        MeasureTheory.lintegral_congr (fun z => by
          show (∑ m ∈ insert a s, ENNReal.ofReal (Work.EllipticEst.ModalSolution.eNorm m *
              (Work.FTS.PhiStar.Series.cmode m F z) ^ 2))
            = ENNReal.ofReal (Work.EllipticEst.ModalSolution.eNorm a *
                (Work.FTS.PhiStar.Series.cmode a F z) ^ 2)
              + ∑ m ∈ s, ENNReal.ofReal (Work.EllipticEst.ModalSolution.eNorm m *
                  (Work.FTS.PhiStar.Series.cmode m F z) ^ 2)
          rw [Finset.sum_insert ha])
      rw [hL, MeasureTheory.lintegral_add_left' (haem a), ih, Finset.sum_insert ha]
  -- the RHS: `∫⁻_θ ofReal (…)` is `ofReal` of the honest `θ`-integral
  have hconv : (∫⁻ z in Set.Ioi (0 : ℝ), (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((F z θ) ^ 2 * Real.cos θ)))
      = ∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2 * Real.cos θ) := by
    refine MeasureTheory.lintegral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    have hInt : MeasureTheory.Integrable (fun θ => (F z θ) ^ 2 * Real.cos θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hint z hz
    have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun θ => (F z θ) ^ 2 * Real.cos θ) := by
      refine (MeasureTheory.ae_restrict_iff' Work.EllipticEst.ModalSolution.measurableSet_Iθ).mpr ?_
      refine Filter.Eventually.of_forall (fun θ hθ => ?_)
      have hc : 0 ≤ Real.cos θ :=
        Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
      positivity
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt hnn]
  rw [hsumsplit, hconv] at h1
  exact h1

end Work.FTS.PhiStar.Honesty
