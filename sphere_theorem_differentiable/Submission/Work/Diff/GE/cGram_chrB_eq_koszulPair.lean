import Mathlib
import Submission.Work.Diff.GE.rmChartExpr_kit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Lowering the Christoffel vector `chrB` against the metric

The Christoffel symbol read in the chart at `x₀` carries the *vector*
`chrB (lcOf g) x₀ y a b = Γ(σ_a)(σ_b)`, i.e. the coordinates of `∇_{σ_b} σ_a`.
Pairing this vector with `σ_k` through the metric is the same as the *lowered* Christoffel
pairing `⟨∇_{σ_b} σ_a, σ_k⟩`, which for a torsion-free connection coincides with
`⟨∇_{σ_a} σ_b, σ_k⟩ = fPair a b k`; the Koszul formula (`fPair_eq_koszul`) identifies the latter
with `½(∂_a G_{bc} + ∂_b G_{ac} - ∂_c G_{ab}) = koszulPair a b k`.

The proof is three bookkeeping steps:

* `frameVector` is the inverse of the chart trivialisation's `continuousLinearMapAt`
  (`Bundle.Trivialization.symmL_continuousLinearMapAt`), so `frameVector` of the coordinates of a
  tangent vector is that tangent vector again;
* torsion-freeness of `lcOf` (`cov_frameSection_frameVector_comm`) swaps the two frame directions;
* `fPair_eq_koszul` (Koszul's formula in the coordinate frame).
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE

theorem cGram_chrB_eq_koszulPair
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) {y : M} (hy : y ∈ (chartAt H x₀).source) (t : ℝ)
    (a b k : Fin (Module.finrank ℝ E)) :
    Work.Diff.GE.cGram (G t) x₀ y
        (Submission.ChartCurv.chrB (Submission.Diff.lcOf (G t)) x₀ y
          (Work.Diff.GE.cBasis (E := E) a) (Work.Diff.GE.cBasis (E := E) b))
        (Work.Diff.GE.cBasis (E := E) k)
      = Work.Diff.GE.koszulPair (I := I) G x₀ a b k t y := by
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G t).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  -- torsion-freeness of the Levi-Civita connection of `G t`
  have htor : (Submission.Diff.lcOf (G t)).torsion = 0 := by
    rw [Submission.Diff.lcOf]
    exact CovariantDerivative.torsion_leviCivitaConnection_eq_zero I
  -- `y` lies in the base set of the chart trivialisation
  have hmem : y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by simpa using hy
  -- the coordinates carried by `chrB` are undone by `frameVector`
  have harg : Submission.Geodesic.frameVector (I := I) x₀ y
      (Submission.ChartCurv.chrB (Submission.Diff.lcOf (G t)) x₀ y
        (Work.Diff.GE.cBasis (E := E) a) (Work.Diff.GE.cBasis (E := E) b))
      = (Submission.Diff.lcOf (G t))
          (Submission.Geodesic.frameSection (I := I) x₀ (Work.Diff.GE.cBasis (E := E) a)) y
          (Submission.Geodesic.frameVector (I := I) x₀ y (Work.Diff.GE.cBasis (E := E) b)) := by
    rw [Submission.ChartCurv.chrB_apply, Submission.Geodesic.christoffelEval_def]
    exact Bundle.Trivialization.symmL_continuousLinearMapAt _ hmem _
  -- torsion-freeness swaps the two directions of the coordinate frame
  have hcomm := Submission.Geodesic.cov_frameSection_frameVector_comm
      (cov := Submission.Diff.lcOf (G t))
      htor x₀ y hy (Work.Diff.GE.cBasis (E := E) a) (Work.Diff.GE.cBasis (E := E) b)
  simp only [Work.Diff.GE.cGram, harg, hcomm]
  exact Work.Diff.GE.fPair_eq_koszul G x₀ t hy a b k

end Work.Diff.GE
