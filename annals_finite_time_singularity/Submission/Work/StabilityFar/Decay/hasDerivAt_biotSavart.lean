/-
# `Work.StabilityFar.Decay.hasDerivAt_biotSavart` — `∂ₜ` commutes with the Biot–Savart integral

The Biot–Savart reconstruction `u(·,t) = BS(ω(·,t))` of the Lichtenstein–Günther argument is an
integral in which the time `t` enters only through the vorticity slice `y ↦ ω(y,t)`.  This file
proves that the time derivative may be taken under the integral:

  `∂ₜ (BS(ω(·,t))) = BS(∂ₜω(·,t))`  at every `t`,

i.e. `Work.StabilityFar.IsTimeBiotSavartSlice`.  This is the transport identity on the constructed
solution, read through Biot–Savart (see `Work.StabilityFar.Defs`).

## The mathematics

In the Newtonian-potential form of `Work.LWP.biotSavart`,

  `BS(ω(·,t)) x = (4π)⁻¹ ∫ y, (‖x-y‖³)⁻¹ • (ω(y,t) × (x-y)) dy`,

so the integrand is `bsK (ω · t) x`.  Differentiating in `t` is legitimate by the standard
dominated-convergence theorem for parametric integrals
(`hasDerivAt_integral_of_dominated_loc_of_deriv_le`), and the three hypotheses it needs are exactly
the ones carried by the statement:

* *the domination.*  Since `ω` is supported in the ball `B(0,R)` and bounded by `M`, the integrand
  is dominated by `C·‖x-y‖⁻²` on that ball (`Work.StabilityFar.Decay.norm_bsK_le_indicator`), and
  `‖·‖⁻²` is integrable over a ball of `ℝ³` — the borderline case `2 < 3 = dim`
  (`Work.StabilityFar.Decay.integrable_indicator_inv_sq`).  The same bound, with `M₁` in place of
  `M`, dominates the differentiated integrand: outside the ball `∂ₜω(·,s)` vanishes, because the
  slice `ω(·,s')` vanishes identically in `s'` on a whole neighbourhood of `s`
  (`Work.StabilityFar.Decay.timeDeriv_eq_zero_of_notMem_closedBall`).
* *the measurability of the derivative slice.*  This is not a hypothesis but a consequence of
  differentiability plus the measurability of the slices: `∂ₜω(·,t)` is the pointwise limit of the
  measurable difference quotients
  (`Work.StabilityFar.Decay.aestronglyMeasurable_timeDeriv_slice`).
* *the pointwise differentiation of the integrand*, i.e. the chain rule in the first slot of the
  cross product (`Work.StabilityFar.Decay.hasDerivAt_bsK`).

The signs and the `4π` normalisation need no care: `biotSavart` is *definitionally* `(4π)⁻¹`
times the integral, so the claim follows from the parametric-integral theorem by multiplying by
the constant.
-/
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.StabilityFar.Defs
import Submission.Work.LWP.Defs
import Submission.Work.LWP.BiotSavart.farField_decay_fderiv
import Submission.Work.LWP.BiotSavart.nearField_bound
import Submission.Work.StabilityFar.Decay.KernelDefs
import Submission.Work.StabilityFar.Decay.timeDeriv_eq_zero_of_notMem_closedBall
import Submission.Work.StabilityFar.Decay.aestronglyMeasurable_timeDeriv_slice
import Submission.Work.StabilityFar.Decay.integrable_indicator_inv_sq
import Submission.Work.StabilityFar.Decay.hasDerivAt_bsK
import Submission.Work.StabilityFar.Decay.norm_bsK_le_indicator

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Filter Topology MeasureTheory
open scoped Topology NNReal ENNReal

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.StabilityFar.Decay

theorem hasDerivAt_biotSavart {ω : Work.StabilityFar.R3 → ℝ → Work.StabilityFar.R3}
    {R M M₁ ε t : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M) (hM₁ : 0 ≤ M₁) (hε : 0 < ε)
    (hbdd : ∀ s ∈ Set.Ioo (t - ε) (t + ε), ∀ y, ‖ω y s‖ ≤ M)
    (hbdd' : ∀ s ∈ Set.Ioo (t - ε) (t + ε), ∀ y,
      ‖FiniteTimeSingularity.timeDeriv ω y s‖ ≤ M₁)
    (hdc : ∀ s ∈ Set.Ioo (t - ε) (t + ε), ∀ y,
      HasDerivAt (fun s' => ω y s') (FiniteTimeSingularity.timeDeriv ω y s) s)
    (hsupp : ∀ s ∈ Set.Ioo (t - ε) (t + ε), ∀ y, ω y s ≠ 0 → y ∈ Metric.closedBall 0 R)
    (hmeas : ∀ s ∈ Set.Ioo (t - ε) (t + ε),
      MeasureTheory.AEStronglyMeasurable (ω · s) volume)
    (x : Work.StabilityFar.R3) :
    HasDerivAt (fun s => Work.LWP.biotSavart (ω · s) x)
      (Work.LWP.biotSavart (fun y => FiniteTimeSingularity.timeDeriv ω y t) x) t := by
  -- `t` lies in the open window, which is therefore a neighbourhood of `t`.
  have hmem : t ∈ Set.Ioo (t - ε) (t + ε) := ⟨by linarith, by linarith⟩
  have hnhds : Set.Ioo (t - ε) (t + ε) ∈ 𝓝 t := isOpen_Ioo.mem_nhds hmem
  -- The common dominating function: `C·‖x-y‖⁻²` on the support ball, with `C = max M M₁`.
  let bd : Work.StabilityFar.R3 → ℝ := fun y =>
    (Metric.closedBall (0 : Work.StabilityFar.R3) R).indicator
      (fun y => max M M₁ * ((‖x - y‖ ^ (2 : ℕ))⁻¹)) y
  have hbd_int : Integrable bd volume :=
    integrable_indicator_inv_sq x (le_trans hM (le_max_left _ _))
  -- Measurability of the derivative slice `∂ₜω(·,t)`.
  have hmeas_dt : AEStronglyMeasurable (fun y => FiniteTimeSingularity.timeDeriv ω y t) volume :=
    aestronglyMeasurable_timeDeriv_slice hε hdc hmeas
  -- The integrand is ae strongly measurable near `t`.
  have hF_meas : ∀ᶠ s in 𝓝 t,
      AEStronglyMeasurable (fun y => Work.LWP.BiotSavart.bsK (fun z => ω z s) x y) volume := by
    filter_upwards [hnhds] with s hs
    exact Work.LWP.BiotSavart.aestronglyMeasurable_bsK (hmeas s hs) x
  -- The integrand at the base point is integrable: dominated by `bd`.
  have hF_int : Integrable (fun y => Work.LWP.BiotSavart.bsK (fun z => ω z t) x y) volume := by
    refine Integrable.mono' (g := bd) hbd_int
      (Work.LWP.BiotSavart.aestronglyMeasurable_bsK (hmeas t hmem) x) ?_
    filter_upwards with y
    exact norm_bsK_le_indicator (le_trans hM (le_max_left _ _))
      (fun z => le_trans (hbdd t hmem z) (le_max_left _ _)) (hsupp t hmem) x y
  -- The derivative integrand is ae strongly measurable.
  have hF'_meas : AEStronglyMeasurable
      (fun y => Work.LWP.BiotSavart.bsK (fun z => FiniteTimeSingularity.timeDeriv ω z t) x y)
      volume :=
    Work.LWP.BiotSavart.aestronglyMeasurable_bsK hmeas_dt x
  -- The derivative integrand is dominated by `bd` on the whole window.
  have h_bound : ∀ᵐ a ∂volume, ∀ s ∈ Set.Ioo (t - ε) (t + ε),
      ‖Work.LWP.BiotSavart.bsK (fun z => FiniteTimeSingularity.timeDeriv ω z s) x a‖ ≤ bd a := by
    filter_upwards with a s hs
    have hsupp_dt : ∀ y, FiniteTimeSingularity.timeDeriv ω y s ≠ 0 →
        y ∈ Metric.closedBall (0 : Work.StabilityFar.R3) R := by
      intro y hy
      by_contra hyy
      exact hy (timeDeriv_eq_zero_of_notMem_closedBall hdc hsupp hs hyy)
    exact norm_bsK_le_indicator (le_trans hM (le_max_left _ _))
      (fun z => le_trans (hbdd' s hs z) (le_max_right _ _)) hsupp_dt x a
  -- Pointwise differentiation of the integrand (chain rule in the first cross-product slot).
  have h_diff : ∀ᵐ a ∂volume, ∀ s ∈ Set.Ioo (t - ε) (t + ε),
      HasDerivAt (fun s' => Work.LWP.BiotSavart.bsK (fun z => ω z s') x a)
        (Work.LWP.BiotSavart.bsK (fun z => FiniteTimeSingularity.timeDeriv ω z s) x a) s := by
    filter_upwards with a s hs
    exact hasDerivAt_bsK (hdc s hs a)
  -- Differentiate under the integral.
  obtain ⟨-, hkey⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun n y => Work.LWP.BiotSavart.bsK (fun z => ω z n) x y)
    (F' := fun n y => Work.LWP.BiotSavart.bsK (fun z => FiniteTimeSingularity.timeDeriv ω z n) x y)
    (bound := bd) hnhds hF_meas hF_int hF'_meas h_bound hbd_int h_diff
  -- Transport the constant factor `(4π)⁻¹` across the derivative and read off `biotSavart`.
  have hfin : HasDerivAt (fun s => (4 * Real.pi)⁻¹ • ∫ y,
        Work.LWP.BiotSavart.bsK (fun z => ω z s) x y)
      ((4 * Real.pi)⁻¹ • ∫ y,
        Work.LWP.BiotSavart.bsK (fun z => FiniteTimeSingularity.timeDeriv ω z t) x y) t :=
    hkey.const_smul ((4 * Real.pi)⁻¹)
  simpa only [Work.LWP.BiotSavart.biotSavart_apply] using hfin

end Work.StabilityFar.Decay
