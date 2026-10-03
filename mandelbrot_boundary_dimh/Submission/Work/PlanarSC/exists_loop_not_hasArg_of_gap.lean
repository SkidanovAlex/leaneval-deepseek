import Mathlib
import Submission.Work.HornSC.Tools
import Submission.Work.PlanarSC.Tools
import Submission.Work.PlanarSC.exists_jordan_curve_of_gap
import Submission.Work.PlanarSC.not_hasArg_of_jordan_curve

namespace Work.PlanarSC

/-- **A loop winding about a point of a compact set separated from a closed set.**

If `S` is compact and nonempty, `S'` is closed, and `S` stays at distance `≥ δ > 0` from `S'`,
then for every `a ∈ S` there is a continuous `1`-periodic loop avoiding `S ∪ S'` whose winding
number about `a` is non-zero.

The loop is obtained from a Jordan curve `γ` lying in the complement of `S ∪ S'` and enclosing `a`
(`Work.PlanarSC.exists_jordan_curve_of_gap`); a Jordan curve winds non-trivially around the points
of its bounded complementary region (`Work.PlanarSC.not_hasArg_of_jordan_curve`). -/
theorem exists_loop_not_hasArg_of_gap {S S' : Set ℂ} (hS : IsCompact S) (hSne : S.Nonempty)
    (hS' : IsClosed S') (hgap : ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ S, ∀ s' ∈ S', δ ≤ dist s s')
    {a : ℂ} (ha : a ∈ S) :
    ∃ f : ℝ → ℂ, Continuous f ∧ Function.Periodic f 1 ∧ (∀ t : ℝ, f t ∉ S ∪ S') ∧
      ¬ Commons.Topology.Winding.HasArg (fun t : ℝ => f t - a) 0 := by
  obtain ⟨γ, hγinj, hγrange, hγna, hγbdd⟩ :=
    exists_jordan_curve_of_gap hS hSne hS' hgap ha
  refine ⟨circleParam γ, ?_, circleParam_periodic γ, ?_, ?_⟩
  · show Continuous (fun t : ℝ => γ (Circle.exp (2 * Real.pi * t)))
    fun_prop
  · intro t
    exact hγrange ⟨Circle.exp (2 * Real.pi * t), rfl⟩
  · exact not_hasArg_of_jordan_curve hγinj hγna hγbdd

end Work.PlanarSC
