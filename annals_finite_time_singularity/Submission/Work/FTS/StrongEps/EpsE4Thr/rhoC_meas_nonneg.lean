/-
Copyright: work module for the Elgindi finite-time singularity project.

# A.e. strong measurability and nonnegativity of the weight `w(z)² sin(2θ)^c`

`Work.FTS.StrongEps.EpsE4Thr.mup = (volume.restrict Iz).prod (volume.restrict Iθ)` is the
product measure on the self-similar domain `[0,∞) × [0,π/2]`.  The weight

  `ρ_c(z,θ) = w(z)² · sin(2θ)^c`

is the density used in all the `L²`-slot estimates of this chapter.  Two facts are needed
about it, and both are collected here:

* **a.e. strong measurability** for `mup`.  On the open quadrant
  `Qd = (0,∞) × (0,π/2)` the weight is continuous: `w` is a rational function with
  non-vanishing denominator and `sin 2θ > 0` there, so `θ ↦ sin(2θ)^c` is continuous on
  `Qd` by `ContinuousOn.rpow_const` (the base never vanishes).  The complement of `Qd`
  inside `Iz ×ˢ Iθ` is null, so `Work.Spaces.aesm_of_continuousOn_Qd` upgrades this to
  `AEStronglyMeasurable` for `mup`.

* **nonnegativity** `mup`-a.e.  Since `mup` is concentrated on `Iz ×ˢ Iθ` (both factors
  are restrictions to those sets), it suffices to check the pointwise statement for
  `z ∈ Iz` and `θ ∈ Iθ`: there `w(z)² = ((1+z)²/z²)² ≥ 0` is a square, and
  `sin(2θ) ≥ 0` because `2θ ∈ [0,π]`, whence `sin(2θ)^c ≥ 0` by `Real.rpow_nonneg`.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsE4Thr.WipEqIntegral
import Submission.Work.Spaces.aesm_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

/-- The weight `p ↦ w p.1 ^ 2 * sin (2 * p.2) ^ c` is continuous on the open quadrant
`(0,∞) × (0,π/2)`.  This is the input of `Work.Spaces.aesm_of_continuousOn_Qd`. -/
theorem continuousOn_rhoC (c : ℝ) :
    ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.w p.1 ^ 2 * Real.sin (2 * p.2) ^ c)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    have h : ContinuousOn (fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
      ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
        (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))
    simpa [Work.Spaces.w] using h
  refine ContinuousOn.mul (hw.pow 2) ?_
  refine ContinuousOn.rpow_const
    ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn) ?_
  intro p hp
  exact Or.inl (ne_of_gt
    (Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1]) (by linarith [hp.2.2])))

/-- `mup` is concentrated on the domain `Iz ×ˢ Iθ`: both factors are restrictions to those
sets. -/
theorem ae_mem_Iz_prod_Iθ :
    ∀ᵐ p ∂mup, p.1 ∈ Work.Spaces.Iz ∧ p.2 ∈ Work.Spaces.Iθ := by
  have hae_Iz : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), z ∈ Work.Spaces.Iz :=
    MeasureTheory.ae_restrict_mem measurableSet_Ici
  have hae_Iθ : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), θ ∈ Work.Spaces.Iθ :=
    MeasureTheory.ae_restrict_mem measurableSet_Icc
  rw [mup]
  refine (MeasureTheory.Measure.ae_prod_iff_ae_ae
    (p := fun p : ℝ × ℝ => p.1 ∈ Work.Spaces.Iz ∧ p.2 ∈ Work.Spaces.Iθ)
    ((measurableSet_Ici.preimage measurable_fst).inter
      (measurableSet_Icc.preimage measurable_snd))).mpr ?_
  filter_upwards [hae_Iz] with a ha
  filter_upwards [hae_Iθ] with b hb
  exact ⟨ha, hb⟩

theorem rhoC_meas_nonneg (c : ℝ) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.w p.1 ^ 2 * Real.sin (2 * p.2) ^ c)
      Work.FTS.StrongEps.EpsE4Thr.mup ∧
    ∀ᵐ p ∂Work.FTS.StrongEps.EpsE4Thr.mup,
      0 ≤ Work.Spaces.w p.1 ^ 2 * Real.sin (2 * p.2) ^ c := by
  refine ⟨Work.Spaces.aesm_of_continuousOn_Qd _ (continuousOn_rhoC c), ?_⟩
  refine ae_mem_Iz_prod_Iθ.mono fun p hp => ?_
  have hsin : 0 ≤ Real.sin (2 * p.2) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩
  exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin c)

end Work.FTS.StrongEps.EpsE4Thr
