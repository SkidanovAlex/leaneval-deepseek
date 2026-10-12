import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.BSKinetic.Decomp.exists_bound_fderiv
import Submission.Work.SmallBoxTBWord.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BSKinetic

open scoped ContDiff

/-- The rescaled window `chiScale s` (`s ≠ 0`) is bounded together with its derivative:
there are constants `C, D ≥ 0` with `|chiScale s x| ≤ C` and
`|fderiv ℝ (chiScale s) x v| ≤ D * ‖v‖` for all `x, v`. -/
theorem exists_chiScale_bound {s : ℝ} (hs : s ≠ 0) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      (∀ x : EuclideanSpace ℝ (Fin 3), |Submission.BoseGases.chiScale s x| ≤ C) ∧
      (∀ x v : EuclideanSpace ℝ (Fin 3),
        |fderiv ℝ (Submission.BoseGases.chiScale s) x v| ≤ D * ‖v‖) := by
  obtain ⟨M, hM0, hMbd, hMder⟩ :=
    Work.BSKinetic.Decomp.exists_bound_fderiv
      (Submission.BoseGases.chiScale_contDiff hs)
      (Submission.BoseGases.chiScale_hasCompactSupport hs)
  exact ⟨M, M, hM0, hM0, hMbd, fun x v => by
    simpa only [Real.norm_eq_abs] using hMder x v⟩

end Work.BSKinetic
