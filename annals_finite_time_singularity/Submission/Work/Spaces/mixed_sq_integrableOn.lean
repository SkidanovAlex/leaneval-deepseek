import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
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

namespace Work.Spaces

set_option autoImplicit false

/-! ## Measurability and continuity of the two factors of the mixed summand

The summand `(D_z^j D_θ^i f · W)²` is the pointwise square of the product of
`θ ↦ D_z^j D_θ^i f z θ` and `θ ↦ W(α,z,θ)`.  The second factor has the algebraic
form `w z · sin(2θ)^{-γ/2}`, so it is (everywhere) measurable; the first factor is
continuous on `Iθ` because `f` is smooth on a neighbourhood of the closed quadrant,
hence so are all its `D`-iterates. -/

/-- The angular slice of the weight, `θ ↦ W(α,z,θ)`, is measurable. -/
private lemma measurable_Wt_right (α z : ℝ) : Measurable (fun θ : ℝ => Wt α z θ) := by
  have hsin : Measurable (fun θ : ℝ => Real.sin (2 * θ)) :=
    Real.measurable_sin.comp (measurable_const.mul measurable_id)
  have hpow : Measurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(gam α / 2))) :=
    hsin.pow_const _
  have : Measurable (fun θ : ℝ => w z * (Real.sin (2 * θ)) ^ (-(gam α / 2))) :=
    measurable_const.mul hpow
  simpa [Wt, wTheta] using this

/-- For `z ∈ Iz`, the angular slice `θ ↦ D_z^j D_θ^i f z θ` of a smooth function is
continuous on the closed interval `Iθ`. -/
private lemma continuousOn_mixed_slice {f : ℝ → ℝ → ℝ} (hsm : SmoothNbhd f) (i j : ℕ)
    {z : ℝ} (hz : z ∈ Iz) : ContinuousOn (fun θ : ℝ => mixed j i f z θ) Iθ := by
  have hsm' : SmoothNbhd (mixed j i f) := SmoothNbhd.DzIter (SmoothNbhd.DthIter hsm i) j
  intro θ hθ
  have hcd : ContDiffAt ℝ ⊤ (Function.uncurry (mixed j i f)) (z, θ) :=
    hsm'.contDiffAt (isOpen_nbhU.mem_nhds (mem_nbhU hz hθ))
  exact (hcd.continuousAt.comp (Continuous.prodMk_right z).continuousAt).continuousWithinAt

/-- The squared weighted mixed derivative `(D_z^j D_θ^i f · W)²` of an `H⁴`-function is
integrable in `θ` on `Iθ`, for `1 ≤ i` and `i + j ≤ 4`.  It is one of the summands of
`HkIntegrand α 4 f z`, which is integrable on `Iθ` by `HkMem α 4 f`. -/
theorem mixed_sq_integrableOn {α : ℝ} {f : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd f)
    (hmem : Work.Spaces.HkMem α 4 f) (i j : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) {z : ℝ}
    (hz : z ∈ Work.Spaces.Iz) :
    MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
      Work.Spaces.Iθ MeasureTheory.volume := by
  have hcont := continuousOn_mixed_slice hsm i j hz
  have haesm1 : AEStronglyMeasurable (fun θ : ℝ => mixed j i f z θ) (volume.restrict Iθ) :=
    hcont.aestronglyMeasurable (show MeasurableSet Iθ from measurableSet_Icc)
  have haesm2 : AEStronglyMeasurable (fun θ : ℝ => Wt α z θ) (volume.restrict Iθ) :=
    (measurable_Wt_right α z).aestronglyMeasurable
  have haesm : AEStronglyMeasurable (fun θ : ℝ => (mixed j i f z θ * Wt α z θ) ^ 2)
      (volume.restrict Iθ) := by
    have h : AEStronglyMeasurable (fun θ : ℝ => mixed j i f z θ * Wt α z θ)
        (volume.restrict Iθ) := haesm1.mul haesm2
    exact h.pow 2
  -- Pointwise domination by the full `H⁴`-integrand, which is integrable by hypothesis.
  refine (hmem.1 z hz).mono' haesm (Eventually.of_forall fun θ => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact sq_le_HkIntegrand_mixed α 4 f z θ i j hi hij

end Work.Spaces
