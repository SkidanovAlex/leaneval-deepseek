/-
# `radA α f` is `C⁵` on `(0,∞)`

The order-`5` companion of `radA_contDiffOn_four_of_smoothOpen`
(`GalFields/Norm/radA_Corr_contDiffOn_four.lean`).  Recall
(`CoercivityFix.Transfer.radA_eq`)

  `radA α f z = −a(z)·L₁₂(f)(z) + (b(z)/c(α))·L₁₂(Transport f)(0)`,

a combination of the `z`-only rational factors `a(z) = 2z/(c(1+z)²)`, `b(z) = 2z²/(1+z)³` with
the nonlocal tail integral `L₁₂ f`; hence the only analytic input is `L₁₂ f ∈ C⁵((0,∞))`.

That is `UopHk.contDiffOn_L12_k α 5` — the same `C^k` statement used at order `4`, valid for
every `k ≥ 2` — applied to `SmoothOpen f` together with `HkMem α 5 f` directly (no descent in
the order is needed here, unlike the `k = 4` case which starts from `ℋ⁵`).  The rational
factors are `C⁶` on `(0,∞)` because `1/10 ≤ c(α)` (`contDiffOn_six_ampA`,
`contDiffOn_six_ampB_div`), and `1 + z > 0` there.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.GalFields.Norm.radA_Corr_contDiffOn_four

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.Norm

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The nonlocal tail integral at order `5` -/

/-- **`L₁₂ f ∈ C⁵((0,∞))`** for a datum smooth on the open quadrant and honest in `ℋ⁵`:
`contDiffOn_L12_k` at `k = 5`, transported from `Work.Elliptic.L12` to the
`Work.Coercivity.L12f = Work.Construction.L12` form used by `radA`. -/
theorem L12f_contDiffOn_five_of_smoothOpen {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    (hmem : Work.Spaces.HkMem α 5 f) :
    ContDiffOn ℝ 5 (Work.Coercivity.L12f f) (Set.Ioi (0 : ℝ)) := by
  have hEll : ContDiffOn ℝ 5 (Work.Elliptic.L12 f) (Set.Ioi (0 : ℝ)) :=
    Work.FTS.EllipticEst.UopHk.contDiffOn_L12_k α 5 f hα hα1 hsm hmem (by norm_num)
  have hCon : ContDiffOn ℝ 5 (fun z => Work.Construction.L12 f z) (Set.Ioi (0 : ℝ)) := by
    rw [Work.FTS.H2.constructionL12_eq_ellipticL12 f]
    exact hEll
  have hfun : Work.Coercivity.L12f f = Work.Construction.L12 f := rfl
  rw [hfun]
  exact hCon

/-! ## The radial profile `radA` -/

/-- **`radA α f ∈ C⁵((0,∞))`**: the two rational `z`-factors `a`, `b` are `C⁶` (hence `C⁵`)
there, and the only analytic input is `L₁₂ f ∈ C⁵((0,∞))` of the previous lemma. -/
theorem radA_contDiffOn_five_of_smoothOpen {α : ℝ} {f : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 5 f) :
    ContDiffOn ℝ 5 (Work.FTS.CoercivityFix.Transfer.radA α f) (Set.Ioi (0 : ℝ)) := by
  have h12 : ContDiffOn ℝ 5 (Work.Coercivity.L12f f) (Set.Ioi (0 : ℝ)) :=
    L12f_contDiffOn_five_of_smoothOpen hα hα1 hsm hmem
  have hfun : Work.FTS.CoercivityFix.Transfer.radA α f
      = fun z => -(Work.FTS.CoercivityFix.Transfer.ampA α z * Work.Coercivity.L12f f z)
          + ((Work.FTS.CoercivityFix.Transfer.ampB α z / Work.Spaces.c α)
              * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) := by
    funext z
    rw [Work.FTS.CoercivityFix.Transfer.radA_eq]
    simp only [Work.FTS.CoercivityFix.Transfer.ampA, Work.FTS.CoercivityFix.Transfer.ampB]
    ring
  rw [hfun]
  exact ((((Work.FTS.StrongPersist.H6Aux.contDiffOn_six_ampA hα hα1).of_le
      (by norm_num)).mul h12).neg).add
    (((Work.FTS.StrongPersist.H6Aux.contDiffOn_six_ampB_div α).of_le
      (by norm_num)).mul contDiffOn_const)

end Work.FTS.GalFields.Norm
