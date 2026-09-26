import Mathlib
import Submission.Work.TorusCover.Basic
import Submission.Work.Core.torusMap_eq_iff
import Submission.Work.CoreTopology.ncard_standardCurve_meridian

namespace Work.TorusCover

open Set
open LeanEval.KnotTheory.PardonDistortion

/-- The standard `(p,q)`-torus curve meets the meridian circle `{θ = const}` in exactly `p`
points of a fundamental period `[0, 2π)`. -/
theorem ncard_standardTorusCurve_meridian (p q : ℕ) (hp : 0 < p) (θ : ℝ) :
    {t | t ∈ Set.Ico (0 : ℝ) (2 * Real.pi) ∧
      LeanEval.KnotTheory.PardonDistortion.standardTorusCurve p q t ∈
        Set.range (Work.Core.meridianCircle θ)}.ncard = p := by
  have hfun : (Work.CoreTopology.meridianCurve Work.CoreTopology.standard θ : ℝ → R3) =
      Work.Core.meridianCircle θ := by
    funext φ
    simp only [Work.CoreTopology.meridianCurve_apply, Work.CoreTopology.standard_psi,
      Work.Core.meridianCircle]
  have hrange : Set.range (Work.Core.meridianCircle θ) =
      Set.range (Work.CoreTopology.meridianCurve Work.CoreTopology.standard θ) := by
    rw [← hfun]
  have hcurve : ∀ t, LeanEval.KnotTheory.PardonDistortion.standardTorusCurve p q t =
      Work.CoreTopology.standardCurve p q t := fun t =>
    (Work.CoreTopology.standardCurve_apply p q t).symm
  have hset : {t | t ∈ Set.Ico (0 : ℝ) (2 * Real.pi) ∧
      LeanEval.KnotTheory.PardonDistortion.standardTorusCurve p q t ∈
        Set.range (Work.Core.meridianCircle θ)}
      = Set.Ico (0 : ℝ) (2 * Real.pi) ∩
        {t | Work.CoreTopology.standardCurve p q t ∈
          Set.range (Work.CoreTopology.meridianCurve Work.CoreTopology.standard θ)} := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    rw [hrange, hcurve t]
  rw [hset]
  exact Work.CoreTopology.ncard_standardCurve_meridian p q hp θ

end Work.TorusCover
