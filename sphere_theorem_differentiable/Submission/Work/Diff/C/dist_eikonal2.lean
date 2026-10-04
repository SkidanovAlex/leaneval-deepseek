import Mathlib
import Submission.Work.Diff.C.Defs
import Submission.Work.Diff.C.inj_radius_v2
import Submission.Work.Diff.C.eikonal_of_inj_v2
import Submission.Work.Final.DimOne

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

CONTEXT: this is one area of the Brendle–Schoen differentiable sphere theorem, driven by the lead. Read HANDOFF.md.
The contracts in Submission/Diff/Interfaces.lean and Submission/Diff/Alg.lean are frozen. Your statement's hypotheses are other
areas' contracts: USE them, do not re-prove them. Go wide: file all the independent sub-lemmas at once,
each with an exact statement, and write your assembly against their statements. If your statement looks
false or unprovable as stated, say so at once in `declare_false` with a precise reason. The lead will fix it.
Part of area C (owner H4). ROUTE: Klingenberg's injectivity radius from the seeded library, then smoothness of d = |exp_p⁻¹|.
- Injectivity: Work.EvenBound.injAllAtLeast_pi_div_sqrt_even (even n) and the odd counterpart in Work/OddBound (see Minimax.lean
  injAllAtLeast_pi_div_sqrt_odd_of_minimaxInput and the final assembly in Work/Final/Final.lean, Work/OddBound/Assembly.lean for
  how MinimaxInput is discharged). Apply them with K := 1 + η. The hypothesis sec ≥ K/4 (+ε) holds since sec > 1 ≥ (1+η)/4 + ε for η < 3.
  This gives InjAllAtLeast hmet (π/√(1+η)).
- No conjugate points before π/√(1+η): ConjRadius / RauchGlobal (normalised to sec ≤ 4; rescale the metric, see MetricScale.lean).
- So GExp p is a local diffeomorphism and injective on the open ball of radius π/√(1+η), and d(p, GExp p v) = ‖v‖ there (InjRadiusCut, CutTime).
- d is then the smooth function y ↦ ‖(GExp p)⁻¹ y‖ away from p, with gradient the unit radial field (Gauss lemma: Gauss.lean).
y ≠ p is required (hy0); at p, d is not smooth.
Replaces Diff/C/dist_eikonal (H154). As H154 found, that statement is false for η ≥ 3 (no quarter pinching). Now η < 3.
Then sec ∈ (1, 1+η] with 1+η < 4 is strictly quarter-pinched after normalisation, and Klingenberg applies.
-/

namespace Work.Diff.C

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg Work.Diff.C
open scoped Manifold ContDiff Bundle Topology
open Bundle Set VectorField CovariantDerivative Metric

theorem dist_eikonal2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [T2Space M] [CompactSpace M] [SimplyConnectedSpace M]
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {η : ℝ} (hη : 0 < η) (hη3 : η < 3) (hpinch : Pinched cov 1 (1 + η)) (p : M) {y : M}
    (hy0 : 0 < rdist (I := I) p y)
    (hy : rdist (I := I) p y < Real.pi / Real.sqrt (1 + η)) :
    CMDiffAt ∞ (fun z : M ↦ rdist (I := I) p z) y ∧
      Inner.inner ℝ (rgrad (I := I) (rdist (I := I) p) y)
        (rgrad (I := I) (rdist (I := I) p) y) = 1 := by
  by_cases hdim : 2 ≤ Module.finrank ℝ E
  · -- Main case: the dimension is at least `2`.
    -- Klingenberg's estimate turns the pinching `1 < sec ≤ 1 + η` into an injectivity radius
    -- `π/√(1+η)`, and inside the injectivity radius the distance to `p` is the norm of the
    -- (smooth) local inverse of the exponential map at `p`.
    haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (M := E) (by omega)
    have hinj : Submission.InjRadius.InjAllAtLeast (I := I) (cov := cov) hmet
        (Real.pi / Real.sqrt (1 + η)) :=
      Work.Diff.C.inj_radius_v2 (I := I) (M := M) hdim cov hmet htor hη hη3 hpinch
    have hρ : 0 < Real.pi / Real.sqrt (1 + η) := by positivity
    exact Work.Diff.C.eikonal_of_inj_v2 (I := I) (M := M) cov hmet htor hρ hinj p hy0 hy
  · -- Degenerate cases: `finrank ℝ E ≤ 1`, where the hypotheses are contradictory.
    have hcases : Module.finrank ℝ E = 0 ∨ Module.finrank ℝ E = 1 := by omega
    rcases hcases with h0 | h1
    · -- `finrank ℝ E = 0`: then `M` carries the discrete topology and, being path connected,
      -- is a subsingleton, so `p = y` and `rdist p y = 0`, contradicting `hy0`.
      exfalso
      haveI : Subsingleton E := Module.finrank_zero_iff.mp h0
      -- The model space `H` is a subsingleton too: `I.toFun : H → E` is injective
      -- (with inverse `I.invFun`, `I.left_inv`) and `E` is a subsingleton.
      haveI : Subsingleton H := ⟨fun a b => by
        have hab : I.toFun a = I.toFun b := Subsingleton.elim _ _
        calc a = I.invFun (I.toFun a) := (I.left_inv a).symm
          _ = I.invFun (I.toFun b) := by rw [hab]
          _ = b := I.left_inv b⟩
      -- Every chart source is a single point, so every point is isolated.
      have hdisc : DiscreteTopology M := by
        rw [discreteTopology_iff_isOpen_singleton]
        intro x
        have hsub : (chartAt H x).source ⊆ {x} := by
          intro u hu
          refine (chartAt H x).injOn hu (mem_chart_source H x) ?_
          exact Subsingleton.elim _ _
        have heq : (chartAt H x).source = {x} :=
          Set.Subset.antisymm hsub
            (by rw [Set.singleton_subset_iff]; exact mem_chart_source H x)
        rw [← heq]
        exact (chartAt H x).open_source
      haveI : DiscreteTopology M := hdisc
      haveI : Subsingleton M := by
        refine ⟨fun x y => ?_⟩
        by_contra hxy
        have hpre : IsPreconnected (univ : Set M) := isPreconnected_univ
        have hu : IsOpen ({x} : Set M) := isOpen_discrete _
        have hv : IsOpen ((univ : Set M) \ {x}) := isOpen_discrete _
        have hcov : (univ : Set M) ⊆ {x} ∪ (univ \ {x}) := by
          intro z _
          by_cases hzx : z = x
          · exact Or.inl hzx
          · exact Or.inr ⟨trivial, hzx⟩
        have hne1 : ((univ : Set M) ∩ {x}).Nonempty := ⟨x, trivial, rfl⟩
        have hne2 : ((univ : Set M) ∩ (univ \ {x})).Nonempty :=
          ⟨y, trivial, trivial, fun h => hxy (Set.mem_singleton_iff.mp h).symm⟩
        obtain ⟨z, -, hzx, -, hzv⟩ := hpre {x} (univ \ {x}) hu hv hcov hne1 hne2
        exact hzv (Set.mem_singleton_iff.mp hzx)
      have hpy : p = y := Subsingleton.elim p y
      have hzero : rdist (I := I) p y = 0 := by
        rw [hpy, rdist, Manifold.riemannianEDist_self, ENNReal.toReal_zero]
      rw [hzero] at hy0
      exact lt_irrefl 0 hy0
    · -- `finrank ℝ E = 1`: no such manifold exists
      -- (`Work.Final.false_of_finrank_one`, from the dimension-one half of Klingenberg).
      haveI : Nontrivial E :=
        Module.nontrivial_of_finrank_pos (R := ℝ) (M := E) (by rw [h1]; norm_num)
      exact (Work.Final.false_of_finrank_one (I := I) (M := M) (cov := cov) hmet htor h1).elim

end Work.Diff.C
