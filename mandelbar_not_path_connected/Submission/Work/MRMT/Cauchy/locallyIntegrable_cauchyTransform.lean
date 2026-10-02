import Mathlib
import Submission.Work.MRMT.Cauchy.Defs
import Submission.Work.MRMT.Cauchy.inner_integral_bound
import Submission.Work.MRMT.Cauchy.aestronglyMeasurable_cauchyTransform

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Cauchy

open MeasureTheory Complex Function Filter
open scoped ENNReal Topology

/-- **The Cauchy transform of an `L¹` function is locally integrable.** For
`ω ∈ L¹(ℂ)`, `z ↦ Work.MRMT.cauchyTransform ω z = Work.MRMT.cauchyConst * ∫ ζ, ω ζ / (ζ - z)` has
integrable restriction to every compact set.

Hints for the prover.  Use `MeasureTheory.locallyIntegrable_iff`:
`LocallyIntegrable f volume ↔ ∀ K, IsCompact K → IntegrableOn f K volume`, and
`IntegrableOn f K volume` is `AEStronglyMeasurableOn f K volume ∧ ∫⁻ z in K, ‖f z‖ₑ < ⊤`
(`MeasureTheory.IntegrableOn`).
For a compact `K`, fix `R` with `K ⊆ Metric.ball 0 R` (`IsCompact.isBounded`, `Metric.isBounded_iff`).
For `z ∈ K` use `norm_integral_le_integral_norm`:
`‖Work.MRMT.cauchyTransform ω z‖ ≤ ‖Work.MRMT.cauchyConst‖ * ∫ ζ, ‖ω ζ / (ζ - z)‖`, and
`‖ω ζ / (ζ - z)‖ = ‖ω ζ‖ / ‖ζ - z‖` (`norm_div`).  Hence
`∫⁻ z in K, ‖cauchyTransform ω z‖ₑ ≤ ENNReal.ofReal ‖cauchyConst‖ * ∫⁻ z in K, ENNReal.ofReal (∫ ζ, ‖ω ζ‖ / ‖ζ - z‖)`
(use `ENNReal.ofReal_mul`, `MeasureTheory.lintegral_const_mul`).
The inequality `ENNReal.ofReal (∫ ζ, g ζ) ≤ ∫⁻ ζ, ENNReal.ofReal (g ζ)` holds for every nonnegative
`g : ℂ → ℝ` (with the convention that a non-integrable nonnegative function has `∫ = 0` and
`∫⁻ ofReal g = ⊤`), so
`∫⁻ z in K, ofReal (∫ ζ, ‖ω ζ‖/‖ζ - z‖) ≤ ∫⁻ z in K, ∫⁻ ζ, ofReal (‖ω ζ‖ * ‖ζ - z‖⁻¹)`.
Swap the two lintegrals with `MeasureTheory.lintegral_lintegral` and bound the inner one uniformly in
`ζ`: `∫⁻ z in K, ofReal (‖ζ - z‖⁻¹) ≤ ∫⁻ z in Metric.ball 0 R, ofReal (‖ζ - z‖⁻¹) ≤ ofReal (8 * π * R)`
(monotonicity plus the centred bound `∫⁻ w in Metric.ball c R, ofReal (‖w‖⁻¹) ≤ ofReal (8 * π * R)`
after the measure-preserving substitution `w = ζ - z`; the centred bound follows from
`Metric.ball c R ⊆ Metric.ball 0 (4 * R)` when `‖c‖ ≤ 3 * R` together with
`∫⁻ w in Metric.ball (0:ℂ) s, ofReal (‖w‖⁻¹) = ofReal (2 * π * s)` from a polar-coordinate
substitution `Complex.lintegral_comp_polarCoord_symm`, and from the pointwise bound
`ofReal (‖w‖⁻¹) ≤ ofReal (1/(2*R))` on `Metric.ball c R` when `3 * R < ‖c‖`).
So the double lintegral is at most
`ofReal ‖cauchyConst‖ * ofReal (8 * π * R) * ∫⁻ ζ, ENNReal.ofReal (‖ω ζ‖) < ⊤`
(`MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm`, `hω.hasFiniteIntegral`).
For the measurability half, `z ↦ ∫ ζ, ω ζ / (ζ - z)` is measurable as a limit of measurable
functions or by the `AEStronglyMeasurable`-closure of the Bochner integral. -/
theorem locallyIntegrable_cauchyTransform (ω : ℂ → ℂ) (hω : MeasureTheory.Integrable ω MeasureTheory.volume) :
    MeasureTheory.LocallyIntegrable (Work.MRMT.cauchyTransform ω) MeasureTheory.volume := by
  rw [MeasureTheory.locallyIntegrable_iff]
  intro K hK
  -- `K` is contained in a ball about the origin of some radius `r`, hence in `ball 0 (|r|+1)`.
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_ball (0 : ℂ)).mp hK.isBounded
  have hRpos : (0 : ℝ) ≤ |r| + 1 := by have := abs_nonneg r; linarith
  have hKsub : K ⊆ Metric.ball (0 : ℂ) (|r| + 1) := by
    intro z hz
    have h1 : ‖z‖ < r := by
      have h := hr hz
      rw [Metric.mem_ball, dist_eq_norm, sub_zero] at h
      exact h
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    linarith [le_abs_self r]
  refine ⟨(aestronglyMeasurable_cauchyTransform ω hω).restrict, ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
  -- `‖x‖ₑ = ENNReal.ofReal ‖x‖` on `ℂ`.
  have henorm : ∀ x : ℂ, ‖x‖ₑ = ENNReal.ofReal ‖x‖ := fun x => by simp [enorm_eq_nnnorm]
  -- The pointwise Cauchy-kernel identity.
  have hker : ∀ z ζ : ℂ, ‖ω ζ / (ζ - z)‖ₑ
      = ENNReal.ofReal (‖ω ζ‖) * ENNReal.ofReal (‖ζ - z‖⁻¹) := by
    intro z ζ
    rw [henorm, norm_div, div_eq_mul_inv, ENNReal.ofReal_mul (norm_nonneg (ω ζ))]
  -- The two-variable integrand is AEMeasurable for the product measure.
  have hGmeas : AEMeasurable
      (Function.uncurry (fun z ζ : ℂ => ENNReal.ofReal (‖ω ζ‖) * ENNReal.ofReal (‖ζ - z‖⁻¹)))
      ((MeasureTheory.volume.restrict K).prod MeasureTheory.volume) := by
    have hωmeas : AEStronglyMeasurable (fun ζ : ℂ => ENNReal.ofReal ‖ω ζ‖) MeasureTheory.volume :=
      ENNReal.continuous_ofReal.comp_aestronglyMeasurable (hω.aestronglyMeasurable.norm)
    have h1 : AEMeasurable (fun p : ℂ × ℂ => ENNReal.ofReal ‖ω p.2‖)
        ((MeasureTheory.volume.restrict K).prod MeasureTheory.volume) :=
      (AEStronglyMeasurable.comp_snd (μ := MeasureTheory.volume.restrict K) hωmeas).aemeasurable
    have h2 : AEMeasurable (fun p : ℂ × ℂ => ENNReal.ofReal (‖p.2 - p.1‖⁻¹))
        ((MeasureTheory.volume.restrict K).prod MeasureTheory.volume) :=
      (ENNReal.measurable_ofReal.comp
        ((measurable_norm.comp (measurable_snd.sub measurable_fst)).inv)).aemeasurable
    exact h1.mul h2
  -- `∫⁻ ζ, ofReal ‖ω ζ‖ = ofReal (∫ ζ, ‖ω ζ‖)` by `ω ∈ L¹`.
  have hlin : ∫⁻ ζ, ENNReal.ofReal ‖ω ζ‖ = ENNReal.ofReal (∫ ζ, ‖ω ζ‖) := by
    rw [MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm hω]
    apply lintegral_congr; intro ζ; rw [henorm]
  -- Pointwise bound on the Cauchy transform.
  have hpt : ∀ z : ℂ, ‖Work.MRMT.cauchyTransform ω z‖ₑ
      ≤ ‖Work.MRMT.cauchyConst‖ₑ * ∫⁻ ζ, ENNReal.ofReal (‖ω ζ‖) * ENNReal.ofReal (‖ζ - z‖⁻¹) := by
    intro z
    rw [Work.MRMT.cauchyTransform, enorm_mul]
    apply mul_le_mul_of_nonneg_left _ bot_le
    calc ‖∫ ζ, ω ζ / (ζ - z)‖ₑ ≤ ∫⁻ ζ, ‖ω ζ / (ζ - z)‖ₑ := enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ ζ, ENNReal.ofReal (‖ω ζ‖) * ENNReal.ofReal (‖ζ - z‖⁻¹) := by
            apply lintegral_congr; intro ζ; rw [hker]
  -- The whole estimate.
  have hcalc : ∫⁻ z in K, ‖Work.MRMT.cauchyTransform ω z‖ₑ
      ≤ ‖Work.MRMT.cauchyConst‖ₑ * (ENNReal.ofReal (8 * Real.pi * (|r| + 1))
          * ENNReal.ofReal (∫ ζ, ‖ω ζ‖)) := by
    calc ∫⁻ z in K, ‖Work.MRMT.cauchyTransform ω z‖ₑ
        ≤ ∫⁻ z in K, ‖Work.MRMT.cauchyConst‖ₑ
            * ∫⁻ ζ, ENNReal.ofReal (‖ω ζ‖) * ENNReal.ofReal (‖ζ - z‖⁻¹) := lintegral_mono hpt
      _ = ‖Work.MRMT.cauchyConst‖ₑ
            * ∫⁻ z in K, ∫⁻ ζ, ENNReal.ofReal (‖ω ζ‖) * ENNReal.ofReal (‖ζ - z‖⁻¹) := by
            rw [lintegral_const_mul' _ _ enorm_ne_top]
      _ = ‖Work.MRMT.cauchyConst‖ₑ
            * ∫⁻ ζ, ∫⁻ z in K, ENNReal.ofReal (‖ω ζ‖) * ENNReal.ofReal (‖ζ - z‖⁻¹) := by
            rw [lintegral_lintegral_swap (μ := MeasureTheory.volume.restrict K)
              (ν := MeasureTheory.volume) hGmeas]
      _ ≤ ‖Work.MRMT.cauchyConst‖ₑ
            * ∫⁻ ζ, ENNReal.ofReal (‖ω ζ‖) * ENNReal.ofReal (8 * Real.pi * (|r| + 1)) := by
            apply mul_le_mul_of_nonneg_left _ bot_le
            apply lintegral_mono; intro ζ; beta_reduce
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            apply mul_le_mul_of_nonneg_left _ bot_le
            exact inner_integral_bound K (|r| + 1) hRpos hKsub ζ
      _ = ‖Work.MRMT.cauchyConst‖ₑ
            * (ENNReal.ofReal (8 * Real.pi * (|r| + 1)) * ENNReal.ofReal (∫ ζ, ‖ω ζ‖)) := by
            rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, hlin]
            ring
  exact lt_of_le_of_lt hcalc
    (ENNReal.mul_lt_top enorm_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top))

end Work.MRMT.Cauchy
