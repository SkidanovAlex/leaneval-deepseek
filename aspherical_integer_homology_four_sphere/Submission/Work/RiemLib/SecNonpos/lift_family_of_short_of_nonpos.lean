import Mathlib
import Submission.Work.RiemLib.API
import Submission.Work.RiemLib.Work.OddBound.longHomotopy.lift_family_of_short
import Submission.Work.RiemLib.Work.OddBound.longHomotopy.continuousOn_curveLength_family

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.RiemLib.SecNonpos

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle CovariantDerivative

/-- **The family lift of a family of curves, for non-positively curved `M`.**

If `M` has `sec ≤ 0` (the hypothesis `hsec`) then every upper curvature bound `K > 0` holds
(`Work.RiemLib.CurvLe_of_nonpos`), and since `π/√K` is unbounded (`Work.RiemLib.exists_lt_pi_div_sqrt`)
any prescribed length bound `L` is `< π/√K` for a suitable `K`.  The `_of_short` lifting theorem
`Work.OddBound.longHomotopy.lift_family_of_short` therefore applies to a jointly smooth family of
curves `s ↦ c s t` starting at `p` whose slices have length `≤ L`, with no constraint on `L`.

The lift `W` is jointly continuous, vanishes at `s = 0`, and satisfies
`GExp (W s t) = c s t` together with the norm bound `‖W s t‖ ≤ curveLength (c · t) 0 s`. -/
theorem lift_family_of_short_of_nonpos
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
    {p : M} {c : ℝ → ℝ → M} {S L : ℝ} (hS : 0 < S)
    (hcsm : ContMDiff (𝓘(ℝ, ℝ × ℝ)) I ∞ (fun u : ℝ × ℝ => c u.1 u.2))
    (hbase : ∀ t : ℝ, c 0 t = p)
    (hlen : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Submission.Length.curveLength (I := I) (fun s : ℝ => c s t) 0 S ≤ L) :
    ∃ W : ℝ → ℝ → TangentSpace I p,
      Continuous (fun u : ℝ × ℝ => W u.1 u.2) ∧
      (∀ t : ℝ, W 0 t = 0) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) S,
        Submission.GlobalExp.GExp (cov := cov) hmet p (W s t) = c s t ∧
        ‖W s t‖ ≤ Submission.Length.curveLength (I := I) (fun r : ℝ => c r t) 0 s) := by
  -- Choose `K > 0` with `L < π/√K`; this is possible because `π/√K → ∞` as `K → 0⁺`.
  obtain ⟨K, hK, hLK⟩ := Work.RiemLib.exists_lt_pi_div_sqrt L
  -- `sec ≤ 0` gives the upper bound `CurvLe cov K`, and the length bound is `< π/√K`.
  exact Work.OddBound.longHomotopy.lift_family_of_short (cov := cov) hmet htor hK
    (Work.RiemLib.CurvLe_of_nonpos hsec hK) hS hcsm hbase
    (fun t ht => lt_of_le_of_lt (hlen t ht) hLK)

end Work.RiemLib.SecNonpos
