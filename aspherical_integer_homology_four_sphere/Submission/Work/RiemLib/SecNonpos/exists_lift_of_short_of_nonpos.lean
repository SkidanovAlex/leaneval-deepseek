import Mathlib
import Submission.Work.RiemLib.API
import Submission.Work.RiemLib.Work.OddBound.longHomotopy.exists_lift_of_short

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.RiemLib.SecNonpos

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle CovariantDerivative

/-- **The lifting lemma for non-positively curved manifolds, with no length restriction.**

Given a curve `h : ℝ → M` starting at `p` and `C¹` on `[0,S]`, and given that the sectional
curvature of `M` is `≤ 0`, there is a continuous curve `W` in `T_pM` starting at `0` with
`GExp p (W s) = h s` and `‖W s‖ ≤ curveLength h 0 s`.

The point is that `sec ≤ 0` supplies the upper bound `CurvLe cov K` for *every* `K > 0`, and
`π/√K` is unbounded, so the hypothesis `curveLength h 0 S < π/√K` of the parametric lifting theorem
`Work.OddBound.longHomotopy.exists_lift_of_short` can always be met. -/
theorem exists_lift_of_short_of_nonpos
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hsec : ∀ (x : M) (u v : TangentSpace I x), ‖u‖ = 1 → ‖v‖ = 1 → inner ℝ u v = 0 →
      inner ℝ (Submission.CurvatureVec.curvVec cov x u v v) u ≤ 0)
    {p : M} {h : ℝ → M} {S : ℝ} (hS : 0 < S)
    (hc : ContMDiffOn 𝓘(ℝ) I 1 h (Set.Icc (0 : ℝ) S)) (h0 : h 0 = p) :
    ∃ W : ℝ → TangentSpace I p, ContinuousOn W (Set.Icc (0 : ℝ) S) ∧ W 0 = 0 ∧
      (∀ s ∈ Set.Icc (0 : ℝ) S,
        Submission.GlobalExp.GExp (cov := cov) hmet p (W s) = h s) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) S, ‖W s‖ ≤ Submission.Length.curveLength (I := I) h 0 s) := by
  obtain ⟨K, hK, hlen⟩ :=
    Work.RiemLib.exists_lt_pi_div_sqrt (Submission.Length.curveLength (I := I) h 0 S)
  exact Work.OddBound.longHomotopy.exists_lift_of_short
    (cov := cov) hmet htor hK (Work.RiemLib.CurvLe_of_nonpos hsec hK) hS hc h0 hlen

end Work.RiemLib.SecNonpos
