/-
Copyright: work module for the Elgindi finite-time singularity project.

# `AeGapSlices` — the a.e. slice continuity and the constrained slice gap for `AeData`

Two pieces of the weak-class (`AeData`) Step 1 of Elgindi's `prop:H2`:

* `continuousOn_Icc_of_tendsto` — continuity of a `C^1` function on the *open* interval, together
  with the two one-sided endpoint limits, gives continuity on the closed interval;
* `ae_continuousOn_slice` — for `AeData α u G` the `θ`-fibres `θ ↦ u z θ` are continuous on the
  closed angular interval for almost every `z > 0`: the right-endpoint limit is unconditional
  (`AeSliceRightTendsto`), the left one is the a.e. moment/endpoint input supplied as a
  hypothesis;
* `AeGapSlices` — hence `Gap9Open` applies on almost every fibre:
  `9 ∫_θ u(z,θ)² ≤ ∫_θ (∂_θu(z,θ))²`, `Gap9Open` being the constrained slice Poincaré inequality
  (`Work.FTS.EllipticEst.Honest.Gap9Open`), whose hypotheses are
  `C²`-on-the-open-interval, continuity on the closed one, vanishing endpoint *values*, the
  honesty of `(∂_θu)²` on the fibre and the solvability condition `∫_θ u(z,θ) sinθcos²θ = 0`.

The gap is what absorbs the `-6u` of `Lzero` in the radial energy inequality: `9 > 6`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.Honest.Gap9Open
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeSliceRightTendsto

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.AeProof

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Work.FTS.EllipticEst.Honest Work.FTS.EllipticEst.H2W.Ae

/-! ## Continuity on the closed interval from the one-sided limits -/

/-- **Continuity on `[0,c]` from continuity on `(0,c)` and the two one-sided endpoint limits.** -/
theorem continuousOn_Icc_of_tendsto {f : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hsm : ContinuousOn f (Set.Ioo 0 c))
    (hL0 : Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (f 0)))
    (hLc : Filter.Tendsto f (nhdsWithin c (Set.Iio c)) (nhds (f c))) :
    ContinuousOn f (Set.Icc 0 c) := by
  intro x hx
  rcases lt_or_eq_of_le hx.1 with hx0 | hx0
  · rcases lt_or_eq_of_le hx.2 with hxc | hxc
    · exact (hsm.continuousAt (isOpen_Ioo.mem_nhds ⟨hx0, hxc⟩)).continuousWithinAt
    · subst hxc
      exact ((continuousWithinAt_Iio_iff_Iic).mp hLc).mono (fun y hy => hy.2)
  · subst hx0
    exact ((continuousWithinAt_Ioi_iff_Ici).mp hL0).mono (fun y hy => hy.1)

/-! ## The fibres of an `AeData` datum -/

/-- **The `θ`-fibres of an `AeData` datum are continuous on `[0, π/2]`, almost everywhere in `z`.**
The right-endpoint limit is unconditional (`AeSliceRightTendsto`); the left-endpoint limit is the
a.e. input (it is proved from the moment condition in `AeSliceLeftTendstoAe`). -/
theorem ae_continuousOn_slice {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : AeData α u G)
    (hL0 : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Filter.Tendsto (fun θ => u z θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ContinuousOn (fun θ => u z θ) (Set.Icc 0 (Real.pi / 2)) := by
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi, hL0] with z hz hL0z
  refine continuousOn_Icc_of_tendsto (by linarith [Real.pi_pos]) ?_ ?_ ?_
  · exact (contDiffOn_slice u hz (h.smooth 1)).continuousOn
  · simpa [AeData.dirZero h z] using hL0z
  · have hR := (AeSliceRightTendsto α u G h z hz).1
    simpa [AeData.dirPi h z] using hR

/-- **The constrained slice gap for the fibres of `AeData` data, a.e. in `z`**:
`9 ∫_θ u(z,θ)² ≤ ∫_θ (∂_θu(z,θ))²`.  The hypotheses are exactly what `Gap9Open` consumes: on the
fibre, `C²`-regularity on `(0, π/2)` (from `AeData.smooth`), continuity on `[0, π/2]` (from the
endpoint limits), the Dirichlet values (fields of `AeData`), the honesty of `(∂_θu)²`, and the
solvability condition `∫_θ u(z,θ) sinθcos²θ = 0` (a.e. field of `AeData`). -/
theorem AeGapSlices (α : ℝ) (u G : ℝ → ℝ → ℝ) (h : AeData α u G)
    (hC : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ContinuousOn (fun θ => u z θ) (Set.Icc 0 (Real.pi / 2)))
    (hint : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pth u z θ) ^ 2) Work.Spaces.Iθ) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      9 * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth u z θ) ^ 2 := by
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi, hC, hint, AeData.momU h]
    with z hz hCz hintz hmomz
  have hcd : ContDiffOn ℝ 2 (fun θ => u z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    contDiffOn_slice u hz (h.smooth 2)
  have hgap := Gap9Open (fun θ => u z θ) hcd hCz (AeData.dirZero h z) (AeData.dirPi h z)
    (by simpa only [Work.Spaces.pth] using hintz) (by simpa only [Work.Elliptic.Fstar] using hmomz)
  simpa only [Work.Spaces.pth] using hgap

end Work.FTS.EllipticEst.H2W.AeProof
