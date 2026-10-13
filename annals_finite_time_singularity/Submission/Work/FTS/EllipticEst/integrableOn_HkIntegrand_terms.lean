import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false

/-! ## Measurability of the two angular weight factors

The summands of `Work.Spaces.HkIntegrand` are squares of products `D · weight`, where the
weight is either the radial factor `w z / sin(2θ)^{η/2}` or the product weight
`Wt α z θ = w z · sin(2θ)^{-γ/2}`.  Both are measurable functions of `θ`, being built from
the measurable map `θ ↦ sin(2θ)` by `rpow`, division and multiplication by a constant. -/

/-- The angular factor `θ ↦ w z / sin(2θ)^{η/2}` is measurable. -/
private lemma measurable_wdivsin_right (z : ℝ) :
    Measurable (fun θ : ℝ => Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) := by
  have hsin : Measurable (fun θ : ℝ => Real.sin (2 * θ)) :=
    Real.measurable_sin.comp (measurable_const.mul measurable_id)
  exact measurable_const.div (hsin.pow_const _)

/-- The angular slice `θ ↦ Wt α z θ` of the product weight is measurable. -/
private lemma measurable_Wt_right (α z : ℝ) :
    Measurable (fun θ : ℝ => Work.Spaces.Wt α z θ) := by
  have hsin : Measurable (fun θ : ℝ => Real.sin (2 * θ)) :=
    Real.measurable_sin.comp (measurable_const.mul measurable_id)
  have hpow : Measurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) :=
    hsin.pow_const _
  have : Measurable (fun θ : ℝ => Work.Spaces.w z *
      (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) := measurable_const.mul hpow
  simpa [Work.Spaces.Wt, Work.Spaces.wTheta] using this

/-! ## Continuity of the angular slices of the iterated derivatives

`SmoothNbhd G` says that the uncurried `G` is `C^∞` on the open set `nbhU` of the closed
quadrant; every `D`-iterate of `G` is then smooth there too, and hence has continuous
angular slices on `Iθ`. -/

/-- For `z ∈ Iz`, the angular slice `θ ↦ D_z^i G z θ` of a `SmoothNbhd` function is
continuous on the closed interval `Iθ`. -/
private lemma continuousOn_DzIter_slice {G : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd G)
    (i : ℕ) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    ContinuousOn (fun θ : ℝ => Work.Spaces.DzIter i G z θ) Work.Spaces.Iθ := by
  have hsm' : Work.Spaces.SmoothNbhd (Work.Spaces.DzIter i G) :=
    Work.Spaces.SmoothNbhd.DzIter hsm i
  intro θ hθ
  have hcd : ContDiffAt ℝ ⊤ (Function.uncurry (Work.Spaces.DzIter i G)) (z, θ) :=
    hsm'.contDiffAt (Work.Spaces.isOpen_nbhU.mem_nhds (Work.Spaces.mem_nbhU hz hθ))
  exact (hcd.continuousAt.comp (Continuous.prodMk_right z).continuousAt).continuousWithinAt

/-- For `z ∈ Iz`, the angular slice `θ ↦ D_z^j D_θ^i G z θ` of a `SmoothNbhd` function is
continuous on the closed interval `Iθ`. -/
private lemma continuousOn_mixed_slice {G : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd G)
    (i j : ℕ) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    ContinuousOn (fun θ : ℝ => Work.Spaces.mixed j i G z θ) Work.Spaces.Iθ := by
  have hsm' : Work.Spaces.SmoothNbhd (Work.Spaces.mixed j i G) :=
    Work.Spaces.SmoothNbhd.DzIter (Work.Spaces.SmoothNbhd.DthIter hsm i) j
  intro θ hθ
  have hcd : ContDiffAt ℝ ⊤ (Function.uncurry (Work.Spaces.mixed j i G)) (z, θ) :=
    hsm'.contDiffAt (Work.Spaces.isOpen_nbhU.mem_nhds (Work.Spaces.mem_nbhU hz hθ))
  exact (hcd.continuousAt.comp (Continuous.prodMk_right z).continuousAt).continuousWithinAt

/-! ## The individual summands are integrable

Each summand is a square, hence nonnegative, and is one of the summands of the full
integrand `HkIntegrand α k G z θ`; a single term of a sum of nonnegative terms is bounded
by the sum (`Work.Spaces.sq_le_HkIntegrand_z`, `Work.Spaces.sq_le_HkIntegrand_mixed`).
Together with the a.e. strong measurability supplied by the smoothness of `G` and the
measurability of the weights, `Integrable.mono'` gives the conclusion. -/

/-- Honesty of the individual summands of the `H^k`-integrand: if `G` is smooth on an open
neighbourhood of the closed quadrant (`SmoothNbhd`) and the full integrand is integrable on the
angular interval at `z`, then so is each summand.  Both conclusions are needed for the
integrability hypotheses of the slice estimates of `theta_poincare_Hk`.

Each summand is dominated by the (nonnegative) full integrand, so only measurability is needed;
it follows from the smoothness of `θ ↦ DzIter i G z θ` and `θ ↦ mixed j i G z θ` on `Iθ`
(each is `ContDiffOn` on an open neighbourhood, hence continuous on `Iθ`, hence measurable),
together with the measurability of the `rpow`-weights.  Route: `Integrable.mono'` with the
dominating function `HkIntegrand α k G z θ`, the pointwise bound obtained from
`Finset.single_le_sum` (all summands nonnegative) and the `if`-splitting of the double sum. -/
theorem integrableOn_HkIntegrand_terms (α : ℝ) (k : ℕ) (G : ℝ → ℝ → ℝ) {z : ℝ}
    (hsm : Work.Spaces.SmoothNbhd G) (hz : z ∈ Work.Spaces.Iz)
    (h : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k G z θ)
      Work.Spaces.Iθ) :
    (∀ i ≤ k, MeasureTheory.IntegrableOn (fun θ =>
        (Work.Spaces.DzIter i G z θ * (Work.Spaces.w z
          / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) Work.Spaces.Iθ) ∧
      (∀ i j : ℕ, 1 ≤ i → i + j ≤ k → MeasureTheory.IntegrableOn (fun θ =>
        (Work.Spaces.mixed j i G z θ * Work.Spaces.Wt α z θ) ^ 2) Work.Spaces.Iθ) := by
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  refine ⟨fun i hi => ?_, fun i j hi hij => ?_⟩
  · -- the pure `D_z` summand
    have haesm1 : AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.DzIter i G z θ)
        (volume.restrict Work.Spaces.Iθ) :=
      (continuousOn_DzIter_slice hsm i hz).aestronglyMeasurable hIθ
    have haesm2 : AEStronglyMeasurable
        (fun θ : ℝ => Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
        (volume.restrict Work.Spaces.Iθ) :=
      (measurable_wdivsin_right z).aestronglyMeasurable
    have haesm : AEStronglyMeasurable (fun θ : ℝ =>
        (Work.Spaces.DzIter i G z θ * (Work.Spaces.w z
          / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        (volume.restrict Work.Spaces.Iθ) :=
      (haesm1.mul haesm2).pow 2
    refine h.mono' haesm (Eventually.of_forall fun θ => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact Work.Spaces.sq_le_HkIntegrand_z α k G z θ i hi
  · -- the mixed summand
    have haesm1 : AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.mixed j i G z θ)
        (volume.restrict Work.Spaces.Iθ) :=
      (continuousOn_mixed_slice hsm i j hz).aestronglyMeasurable hIθ
    have haesm2 : AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.Wt α z θ)
        (volume.restrict Work.Spaces.Iθ) :=
      (measurable_Wt_right α z).aestronglyMeasurable
    have haesm : AEStronglyMeasurable
        (fun θ : ℝ => (Work.Spaces.mixed j i G z θ * Work.Spaces.Wt α z θ) ^ 2)
        (volume.restrict Work.Spaces.Iθ) :=
      (haesm1.mul haesm2).pow 2
    refine h.mono' haesm (Eventually.of_forall fun θ => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact Work.Spaces.sq_le_HkIntegrand_mixed α k G z θ i j hi hij

end Work.FTS.EllipticEst
