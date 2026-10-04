import Mathlib
import Submission.Work.OddBound.LiftKit
import Submission.Work.OddBound.polygon.riemannianDist_eq_toReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.OddBound.polygonValue

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval
open Submission.Geodesic Submission.GlobalExp Submission.Length Submission.InjRadius

/-- **The extended Riemannian distance is the `ofReal` of the Riemannian distance.**  On a compact,
path-connected manifold, `Manifold.riemannianEDist I x y` is finite: a piecewise smooth path from
`x` to `y` exists by path connectedness, and the extended distance is at most the total length of
any chain of `C¹` pieces (`Work.OddBound.polygon.riemannianEDist_le_sum_pathELength`), which is a
finite sum of finite numbers.  The comparison `riemannianDist = (riemannianEDist).toReal`
(`Work.OddBound.polygon.riemannianDist_eq_toReal`) then converts this into the stated identity. -/
theorem edist_eq_ofReal_riemannianDist
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    (x y : M) :
    Manifold.riemannianEDist I x y
      = ENNReal.ofReal (Submission.Distance.riemannianDist (I := I) x y) := by
  -- path connectedness gives a piecewise smooth path from `x` to `y`
  have hFne : Manifold.riemannianEDist I x y ≠ ⊤ := by
    obtain ⟨s, hs⟩ := Work.OddBound.polygon.PwLengthSet_nonempty (I := I) x y
    obtain ⟨p, rfl⟩ := hs
    -- each piece of the path has finite extended length
    have hpiece : ∀ i ∈ Finset.range (p.N + 1),
        Manifold.pathELength I (p.c i) (p.a i) (p.b i) < ⊤ := fun i _ => by
      rw [Work.OddBound.polygon.pathELength_eq_ofReal_curveLength (I := I) (p.hsmooth i)
        (p.hab i)]
      exact ENNReal.ofReal_lt_top
    -- the extended distance is at most the total extended length of the chain
    have hle := Work.OddBound.polygon.riemannianEDist_le_sum_pathELength (I := I) (N := p.N)
      (c := p.c) (a := p.a) (b := p.b) (x := x) (y := y) p.hsmooth p.hab p.hjoin p.hx p.hy
    have hsumlt := ENNReal.sum_lt_top.mpr hpiece
    exact ne_of_lt (lt_of_le_of_lt hle hsumlt)
  -- convert `riemannianDist` to `(riemannianEDist).toReal` and use finiteness
  rw [Work.OddBound.polygon.riemannianDist_eq_toReal (I := I) x y]
  exact (ENNReal.ofReal_toReal hFne).symm

end Work.OddBound.polygonValue
