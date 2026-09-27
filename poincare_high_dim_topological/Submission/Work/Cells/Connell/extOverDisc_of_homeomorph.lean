import Mathlib
import Submission.Work.PL.Defs

/-!
# `PL.ExtOverDisc` is a homeomorphism invariant

`PL.ExtOverDisc X j` says that every map `𝕊ʲ → X` extends over the closed ball `𝔻ʲ⁺¹`.
This is a purely topological property, hence invariant under homeomorphism: transport the
map along `e.symm`, extend, and push the extension forward along `e`.

Used by `Work.Cells.Connell` to move connectivity hypotheses between homeomorphic models
of a neighbourhood.
-/

namespace Work.Cells.Connell

theorem extOverDisc_of_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) {j : ℕ} (h : PL.ExtOverDisc X j) : PL.ExtOverDisc Y j := by
  intro f
  obtain ⟨g, hg⟩ := h ((e.symm : C(Y, X)).comp f)
  refine ⟨(e : C(X, Y)).comp g, fun x => ?_⟩
  show e (g ⟨x.1, Metric.sphere_subset_closedBall x.2⟩) = f x
  have h1 := congrArg e (hg x)
  simpa using h1

end Work.Cells.Connell
