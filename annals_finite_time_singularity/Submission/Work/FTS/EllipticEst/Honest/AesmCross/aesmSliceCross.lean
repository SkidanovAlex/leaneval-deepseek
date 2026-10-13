/-
Copyright: work module for the Elgindi finite-time singularity project.

# Almost everywhere strong measurability of an angular slice of a cross term

This file proves `Work.FTS.EllipticEst.Honest.AesmCross.aesmSliceCross`: the angular slice
`θ ↦ g z θ * h z θ * w z² * σ θ` (with `σ θ = sin(2θ)^{-η}`) is a.e. strongly measurable for
the measure `volume.restrict Iθ`, for every `z ∈ Iz = [0,∞)`.

The point is that the two factors `g`, `h` are only known to be `C^∞` *off* the closed quadrant:
each of them agrees with a `C^∞` function on the open quadrant `Q0 = (0,∞) × (0,π/2)`.  A
derivative-free statement is insensitive to this: on the open interval `(0, π/2)` the slice `g z`
equals the slice `g' z` (which is continuous there), so the product of the four factors is
continuous on `(0, π/2)`; and `(0, π/2)` differs from `Iθ = [0, π/2]` by the two endpoints, a
null set.  At `z = 0` the radial weight `w 0²` vanishes and the slice is identically zero, which
is measurable.

## Contents

* `aesm_slice_of_agreeOnQ` : for `z > 0`, the slice `θ ↦ F z θ` of a function agreeing on the open
  quadrant with a `SmoothOpen` function is a.e. strongly measurable;
* `aesm_sig` : the angular weight `σ` is a.e. strongly measurable on `Iθ`;
* `aesmSliceCross` : the requested statement.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.AngSecond.Defs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest.AesmCross

/-- **A slice of a function agreeing with a `C^∞`-on-`Q0` function.**  If `F'` is `C^∞` on the
open quadrant and `F` agrees with `F'` on the open quadrant, then for every `z > 0` the angular
slice `θ ↦ F z θ` is a.e. strongly measurable for the measure `volume.restrict Iθ`.

Indeed the slice map `θ ↦ (z, θ)` sends the open interval `(0, π/2)` into the open quadrant, so on
`(0, π/2)` the slice of `F` coincides with the (continuous) slice of `F'`; and `(0, π/2)` equals
`Iθ` up to the null endpoints. -/
theorem aesm_slice_of_agreeOnQ {F F' : ℝ → ℝ → ℝ}
    (hF' : Work.FTS.EllipticEst.SmoothOpen F') (hF : Work.FTS.EllipticEst.AgreeOnQ F F')
    {z : ℝ} (hz : 0 < z) :
    MeasureTheory.AEStronglyMeasurable (fun θ => F z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  -- On the open interval the slice of `F` is the slice of `F'`, which is continuous there.
  have hcont : ContinuousOn (fun θ : ℝ => F z θ) (Set.Ioo 0 (π / 2)) :=
    (hF'.curry_θ hz).continuousOn.congr fun θ hθ => hF z θ hz hθ.1 hθ.2
  have h1 : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => F z θ)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) :=
    hcont.aestronglyMeasurable measurableSet_Ioo
  -- `(0, π/2)` and `Iθ = [0, π/2]` differ by the two null endpoints.
  have hset : (Set.Ioo (0 : ℝ) (π / 2)) =ᵐ[MeasureTheory.volume]
      (Set.Icc (0 : ℝ) (π / 2)) := MeasureTheory.Ioo_ae_eq_Icc
  have hmeas : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) :=
    (MeasureTheory.Measure.restrict_congr_set hset).symm
  rw [hmeas]
  exact h1

/-- **The angular weight `σ θ = sin(2θ)^{-η}`** is a.e. strongly measurable for the measure
`volume.restrict Iθ`: it is continuous on the open interval `(0, π/2)`, where `sin(2θ) > 0`. -/
theorem aesm_sig : MeasureTheory.AEStronglyMeasurable
    (fun θ => Work.FTS.EllipticEst.AngSecond.sig θ)
    (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have hsinpos : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), 0 < Real.sin (2 * θ) := by
    intro θ hθ
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])
  have hcont : ContinuousOn (fun θ : ℝ => Work.FTS.EllipticEst.AngSecond.sig θ)
      (Set.Ioo 0 (π / 2)) := by
    have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (π / 2)) :=
      (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
    simpa [Work.FTS.EllipticEst.AngSecond.sig] using
      hsin.rpow_const fun θ hθ => Or.inl (ne_of_gt (hsinpos θ hθ))
  have h1 : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => Work.FTS.EllipticEst.AngSecond.sig θ)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) :=
    hcont.aestronglyMeasurable measurableSet_Ioo
  have hset : (Set.Ioo (0 : ℝ) (π / 2)) =ᵐ[MeasureTheory.volume]
      (Set.Icc (0 : ℝ) (π / 2)) := MeasureTheory.Ioo_ae_eq_Icc
  have hmeas : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) :=
    (MeasureTheory.Measure.restrict_congr_set hset).symm
  rw [hmeas]
  exact h1

theorem aesmSliceCross {g h g' h' : ℝ → ℝ → ℝ} (hg' : Work.FTS.EllipticEst.SmoothOpen g')
    (hh' : Work.FTS.EllipticEst.SmoothOpen h')
    (hgg : Work.FTS.EllipticEst.AgreeOnQ g g') (hhh : Work.FTS.EllipticEst.AgreeOnQ h h') :
    ∀ z ∈ Work.Spaces.Iz,
      MeasureTheory.AEStronglyMeasurable
        (fun θ => g z θ * h z θ * Work.FTS.EllipticEst.AngSecond.w2 z
          * Work.FTS.EllipticEst.AngSecond.sig θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  intro z hz
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · -- at `z = 0` the radial weight `w 0²` vanishes, so the slice is identically zero
    subst hz0
    refine (MeasureTheory.aestronglyMeasurable_const (b := (0 : ℝ))).congr ?_
    filter_upwards with θ
    simp [Work.FTS.EllipticEst.AngSecond.w2, Work.Spaces.w]
  · -- for `z > 0` each factor is a.e. strongly measurable
    exact (((aesm_slice_of_agreeOnQ hg' hgg hzpos).mul
      (aesm_slice_of_agreeOnQ hh' hhh hzpos)).mul
      MeasureTheory.aestronglyMeasurable_const).mul aesm_sig

end Work.FTS.EllipticEst.Honest.AesmCross
