/-
Copyright: work module for the Elgindi finite-time singularity project.

# Integrability of `√sliceE` and of `boundU` from the integrability of the slice energy

The pre-existing machinery of `AngAWeak.GradTraceAux`
(`integrableOn_sqrtSliceE_of_hint`, `integrableOn_boundU`) produces the local integrability of
`√ (sliceE u)` and of the dominating function `boundU u K` from the *weighted* hypothesis
`hint : IntegrableOn (fun z => w z ^ 2 * ∫_θ (z ∂_θ∂_z u)² σ) Iz`.

That weighted hypothesis is used there for one thing only: to deduce the local integrability of
`sliceE u` itself (`integrableOn_sliceE_of_hint`).  Hence the *unweighted* hypothesis
`IntegrableOn (sliceE u) Iz` suffices: on a compact `[a,b] ⊂ (0,∞)` the weight is bounded below,
so the two hypotheses are equivalent there, and only the local statement is used.

This module records that slight strengthening (the `hint`-free forms of the two lemmas) and
derives from it the requested conjunction.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.AngAWeak.aeGradTraceAe

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.GlueEnergy

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "sliceE" => Work.FTS.EllipticEst.AngAWeak.sliceE

/-- **Local integrability of `√ sliceE`.**  The `hint`-free form of
`AngAWeak.integrableOn_sqrtSliceE_of_hint`: local integrability of `sliceE u` on `Icc a b`
implies that of its square root, because `sliceE u ≥ 0` and `√x ≤ 1 + x` for `x ≥ 0`. -/
theorem integrableOn_sqrtSliceE_of_local {u : ℝ → ℝ → ℝ} {a b : ℝ}
    (hloc : MeasureTheory.IntegrableOn (sliceE u) (Set.Icc a b)) :
    MeasureTheory.IntegrableOn (fun s : ℝ => Real.sqrt (sliceE u s)) (Set.Icc a b) := by
  have hone : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc a b) :=
    MeasureTheory.integrableOn_const (s := Set.Icc a b) (C := (1 : ℝ))
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (by simp)
  refine Integrable.mono' (hloc.add hone) ?_ ?_
  · exact Real.continuous_sqrt.comp_aestronglyMeasurable hloc.1
  · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with s hs
    have h0 : 0 ≤ sliceE u s := Work.FTS.EllipticEst.AngAWeak.sliceE_nonneg u s
    have hle : Real.sqrt (sliceE u s) ≤ 1 + sliceE u s :=
      Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith [h0, sq_nonneg (sliceE u s)]⟩
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    simp only [Pi.add_apply]
    linarith [hle]

/-- **Local integrability of the dominating function `boundU`.**  The `hint`-free form of
`AngAWeak.integrableOn_boundU`: from `SmoothOpen u` (which makes `z ↦ |∂_z u(z,1)|` continuous on
`(0,∞)`) and the local integrability of `sliceE u`, the function
`boundU u K s = |∂_z u(s,1)| + M √(sliceE u s)/s` is integrable on `Icc a b` for `0 < a ≤ b`.

The proof is the one of `AngAWeak.integrableOn_boundU`, with `integrableOn_sqrtSliceE_of_local`
in place of `integrableOn_sqrtSliceE_of_hint` (so the weighted hypothesis disappears). -/
theorem integrableOn_boundU_of_local {u : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen u)
    {a b : ℝ} (hloc : MeasureTheory.IntegrableOn (sliceE u) (Set.Icc a b))
    {K : ℝ} (hK : 0 < K) (ha : 0 < a) (hab : a < b) :
    MeasureTheory.IntegrableOn (Work.FTS.EllipticEst.AngAWeak.boundU u K) (Set.Icc a b) := by
  have hθ1 : (1 : ℝ) ∈ Set.Ioo 0 (Real.pi / 2) :=
    ⟨by norm_num, by linarith [Real.pi_gt_three]⟩
  have hMnn : 0 ≤ Real.sqrt K + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)) := by
    have := Real.sqrt_nonneg K
    have := Real.sqrt_nonneg (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta))
    linarith
  have hsqrt := integrableOn_sqrtSliceE_of_local hloc
  have hboundcont : ContinuousOn (fun s : ℝ => |Work.Spaces.pz u s 1|) (Set.Icc a b) :=
    (((hS.pz).curry_z hθ1).continuousOn.abs).mono (fun s hs => lt_of_lt_of_le ha hs.1)
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hboundcont
  have hdom : ∀ s ∈ Set.Icc a b, Work.FTS.EllipticEst.AngAWeak.boundU u K s ≤ C₁
      + ((Real.sqrt K + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta))) / a)
        * Real.sqrt (sliceE u s) := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
    have h1 : |Work.Spaces.pz u s 1| ≤ C₁ := by
      simpa only [Real.norm_eq_abs, abs_abs] using hC₁ s hs
    have h2 : Real.sqrt (sliceE u s) / s ≤ Real.sqrt (sliceE u s) / a := by
      gcongr
      exact hs.1
    have h5 : 0 ≤ (Real.sqrt K + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)))
        * (Real.sqrt (sliceE u s) / s) := mul_nonneg hMnn (by positivity)
    rw [Work.FTS.EllipticEst.AngAWeak.boundU]
    have h6 : (Real.sqrt K + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)))
        * (Real.sqrt (sliceE u s) / s)
        ≤ ((Real.sqrt K + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta))) / a)
          * Real.sqrt (sliceE u s) := by
      rw [show ((Real.sqrt K + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta))) / a)
            * Real.sqrt (sliceE u s)
          = (Real.sqrt K + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)))
            * (Real.sqrt (sliceE u s) / a) by ring]
      exact mul_le_mul_of_nonneg_left h2 hMnn
    linarith
  have haesm : AEStronglyMeasurable (Work.FTS.EllipticEst.AngAWeak.boundU u K)
      (MeasureTheory.volume.restrict (Set.Icc a b)) := by
    have h1 : AEStronglyMeasurable (fun s : ℝ => |Work.Spaces.pz u s 1|)
        (MeasureTheory.volume.restrict (Set.Icc a b)) :=
      hboundcont.aestronglyMeasurable measurableSet_Icc
    have hsqrt_ae : AEStronglyMeasurable (fun s => Real.sqrt (sliceE u s))
        (MeasureTheory.volume.restrict (Set.Icc a b)) :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hloc.1
    have hinv : ContinuousOn (fun s : ℝ => s⁻¹) (Set.Icc a b) :=
      ContinuousOn.inv₀ continuousOn_id (fun s hs => ne_of_gt (lt_of_lt_of_le ha hs.1))
    have h2 : AEStronglyMeasurable (fun s : ℝ => Real.sqrt (sliceE u s) * s⁻¹)
        (MeasureTheory.volume.restrict (Set.Icc a b)) :=
      hsqrt_ae.mul (hinv.aestronglyMeasurable measurableSet_Icc)
    have h3 : AEStronglyMeasurable (fun s : ℝ => (Real.sqrt K
          + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)))
          * (Real.sqrt (sliceE u s) * s⁻¹))
        (MeasureTheory.volume.restrict (Set.Icc a b)) := h2.const_mul _
    refine AEStronglyMeasurable.congr (h1.add h3) ?_
    filter_upwards with s
    simp only [Pi.add_apply, Work.FTS.EllipticEst.AngAWeak.boundU]
    ring
  refine Integrable.mono' (g := fun s : ℝ => C₁
      + ((Real.sqrt K + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta))) / a)
        * Real.sqrt (sliceE u s)) ?_ haesm ?_
  · have hone : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc a b) :=
      MeasureTheory.integrableOn_const (s := Set.Icc a b) (C := (1 : ℝ))
        (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (by simp)
    simpa using (hone.const_mul C₁).add (hsqrt.const_mul
      ((Real.sqrt K + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta))) / a))
  · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with s hs
    have h2 : 0 ≤ Work.FTS.EllipticEst.AngAWeak.boundU u K s := by
      rw [Work.FTS.EllipticEst.AngAWeak.boundU]
      have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
      have : 0 ≤ (Real.sqrt K + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)))
          * (Real.sqrt (sliceE u s) / s) :=
        mul_nonneg hMnn (div_nonneg (Real.sqrt_nonneg _) hs0.le)
      linarith [abs_nonneg (Work.Spaces.pz u s 1)]
    rw [Real.norm_of_nonneg h2]
    exact hdom s hs

theorem integrableOn_sqrtSliceE_and_boundU_of_energy {u : ℝ → ℝ → ℝ}
    (hS : Work.FTS.EllipticEst.SmoothOpen u)
    (hE : MeasureTheory.IntegrableOn (Work.FTS.EllipticEst.AngAWeak.sliceE u) Work.Spaces.Iz)
    {K : ℝ} (hK : 0 < K) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    MeasureTheory.IntegrableOn
        (fun s : ℝ => Real.sqrt (Work.FTS.EllipticEst.AngAWeak.sliceE u s)) (Set.Icc a b) ∧
      MeasureTheory.IntegrableOn (Work.FTS.EllipticEst.AngAWeak.boundU u K) (Set.Icc a b) := by
  have hsub : Set.Icc a b ⊆ Work.Spaces.Iz := fun s hs => le_trans ha.le hs.1
  have hloc : MeasureTheory.IntegrableOn (Work.FTS.EllipticEst.AngAWeak.sliceE u)
      (Set.Icc a b) := hE.mono_set hsub
  exact ⟨integrableOn_sqrtSliceE_of_local hloc,
    integrableOn_boundU_of_local hS hloc hK ha hab⟩

end Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.GlueEnergy
