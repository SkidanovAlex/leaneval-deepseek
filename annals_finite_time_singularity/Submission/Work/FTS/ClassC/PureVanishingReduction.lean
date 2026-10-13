/-
Copyright: work module for the Elgindi finite-time singularity project.

# The pointwise slot reduction `HkIntegrand α k f ≤ (pure-`z` slots) + (vanishing slots)`

`HkMem_of_pure_and_vanishing` proves `HkMem α k f` from the level-`0` honesty of the pure
radial slots `D_z^j f` and the integrability of the vanishing-weight angular slots
`vig α f r j`.  Its proof contains, as its last (and only pointwise) step, the inequality

`HkIntegrand α k f z θ ≤ ∑_{j ≤ k} HkIntegrand α 0 (D_z^j f) z θ
    + ∑_{j ≤ k} ∑_{1 ≤ i ≤ k-j} vanC(i,j) · ∑_{1 ≤ r ≤ i} vig α f r j z θ`,

obtained by re-summing the `ℋ^k`-integrand by radial slice (`HkIntegrand_eq_slice_sum`) and
applying `vanC_spec` to each mixed slot.  This module extracts that inequality as a standalone
pointwise statement, so that the assembly of `HkMem_seven_slots_of_vanishing_family` can bound
the two sums slot by slot.

`sorry`-free; rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.ClassC.VanishFamilyDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

set_option autoImplicit false

/-- **The pointwise slot reduction.**  For `f` smooth on the open quadrant, the `ℋ^k`-integrand
is dominated by the sum of the pure radial level-`0` integrands and the `vanC`-weighted
vanishing-weight angular slots.  (This is the pointwise core of `HkMem_of_pure_and_vanishing`.) -/
theorem HkIntegrand_le_pure_vanishing {α : ℝ} (hα : 0 < α)
    (hγ : Work.Spaces.gam α ≤ 3 / 2) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (k : ℕ) (z θ : ℝ)
    (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α k f z θ
      ≤ (∑ j ∈ Finset.range (k + 1), Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter j f) z θ)
        + ∑ j ∈ Finset.range (k + 1), ∑ i ∈ Finset.Icc 1 (k - j),
            (if h : 1 ≤ i then vanC α hα hγ f hsm i j h else 0)
              * ∑ r ∈ Finset.Icc 1 i, vig α f r j z θ := by
  have hGrp : ∀ j ∈ Finset.range (k + 1),
      Work.FTS.EllipticEst.sliceGroup α k j f z θ
        = Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter j f) z θ
          + ∑ i ∈ Finset.Icc 1 (k - j),
              (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
    intro j _
    rw [Work.FTS.EllipticEst.sliceGroup, HkIntegrand_zero_eq_classC]
  rw [Work.FTS.EllipticEst.HkIntegrand_eq_slice_sum,
    Finset.sum_congr rfl hGrp, Finset.sum_add_distrib]
  refine add_le_add le_rfl (Finset.sum_le_sum fun j _ => ?_)
  refine Finset.sum_le_sum fun i hi => ?_
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  rw [dif_pos hi1]
  exact vanC_spec α hα hγ f hsm i j hi1 z hz θ hθ

end Work.FTS.ClassC
