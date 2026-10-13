import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.Honest.SliceIbpDefs
import Submission.Work.FTS.EllipticEst.AngSecond.slice_a_priori_bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

theorem SliceBounds (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ 2 f (Set.Icc 0 (Real.pi / 2))) (h0 : f 0 = 0)
    (hπ : f (Real.pi / 2) = 0) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ θ ∈ Work.FTS.EllipticEst.Honest.Iθo, |f θ| ≤ C * θ) ∧
      (∀ θ ∈ Work.FTS.EllipticEst.Honest.Iθo, |f θ| ≤ C * (Real.pi / 2 - θ)) ∧
      (∀ θ ∈ Work.FTS.EllipticEst.Honest.Iθo, |deriv f θ| ≤ C) ∧
      (∀ θ ∈ Work.FTS.EllipticEst.Honest.Iθo, |deriv (deriv f) θ| ≤ C) := by
  obtain ⟨C, hC0, hd1, hd2, hv1, hv2⟩ :=
    Work.FTS.EllipticEst.AngSecond.slice_a_priori_bounds f hf h0 hπ
  refine ⟨C, hC0, ?_, ?_, ?_, ?_⟩
  · intro θ hθ
    exact hv1 θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  · intro θ hθ
    exact hv2 θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  · intro θ hθ
    exact hd1 θ hθ
  · intro θ hθ
    exact hd2 θ hθ

end Work.FTS.EllipticEst.Honest
