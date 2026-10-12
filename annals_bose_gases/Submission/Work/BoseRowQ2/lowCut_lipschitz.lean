import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.BoseGateFS.LowCut_deriv_bound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The FS cut profile `f` of a `LowCut` is globally Lipschitz

`Work.BoseBoxFix.LowCut` bundles FS's cut-off `f`: it is smooth on `ℝ`, antitone, `≡ 1` on
`(-∞,1]` and `≡ 0` on `[2,∞)`.  Being smooth and constant off the compact window `[1,2]`,
its derivative is continuous with support in `[1,2]`, hence uniformly bounded; the mean
value theorem then produces a global Lipschitz constant.

The derivative bound is `Work.BoseGateFS.LowCut_deriv_bound` (proved separately); here it is
converted into the Lipschitz statement via the mean value theorem
`norm_image_sub_le_of_norm_deriv_le`.
-/

namespace Work.BoseRowQ2

/-- A `Work.BoseBoxFix.LowCut` profile is Lipschitz with some constant `C ≥ 0`; in particular
its difference quotients are uniformly bounded. -/
theorem lowCut_lipschitz (fc : Work.BoseBoxFix.LowCut) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : ℝ, |fc.f x - fc.f y| ≤ C * |x - y| := by
  -- The derivative of `fc.f` is uniformly bounded by some `M ≥ 0`.
  obtain ⟨M, hM0, hM⟩ := Work.BoseGateFS.LowCut_deriv_bound fc
  refine ⟨M, hM0, fun x y => ?_⟩
  -- `fc.f` is differentiable, and `‖deriv fc.f‖ ≤ M` everywhere; the mean value theorem on
  -- the (convex) whole line gives the Lipschitz bound.
  have hdiff : ∀ z ∈ (Set.univ : Set ℝ), DifferentiableAt ℝ fc.f z :=
    fun z _ => (fc.smooth.differentiable (by simp)) z
  have hbound : ∀ z ∈ (Set.univ : Set ℝ), ‖deriv fc.f z‖ ≤ M :=
    fun z _ => by simpa [Real.norm_eq_abs] using hM z
  have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound convex_univ
    (Set.mem_univ x) (Set.mem_univ y)
  simpa [Real.norm_eq_abs, abs_sub_comm] using h

end Work.BoseRowQ2
