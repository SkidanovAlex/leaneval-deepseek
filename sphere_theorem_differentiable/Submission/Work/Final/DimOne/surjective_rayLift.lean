import Mathlib
import Submission.Work.Final.DimOne.Defs
import Submission.HopfRinow2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Final.DimOne

open scoped Manifold ContDiff Bundle Topology ENNReal
open LeanEval.Geometry.SphereTheorem
open CovariantDerivative
open Submission.GlobalExp

set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

/-- **One-dimensional linear algebra.**  In a one-dimensional real vector space every vector is a
real multiple of any given nonzero vector. -/
lemma exists_smul_eq_of_finrank_eq_one_surj {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (hdim : Module.finrank ℝ V = 1) {u v : V} (hu : u ≠ 0) :
    ∃ s : ℝ, v = s • u := by
  classical
  have b : Module.Basis (Fin 1) ℝ V := Module.finBasisOfFinrankEq ℝ V hdim
  have hu' : u = (b.repr u) 0 • b 0 := by simpa using (b.sum_repr u).symm
  have hv' : v = (b.repr v) 0 • b 0 := by simpa using (b.sum_repr v).symm
  have hc : (b.repr u) 0 ≠ 0 := by
    intro h0
    exact hu (by rw [hu', h0, zero_smul])
  refine ⟨(b.repr v) 0 / (b.repr u) 0, ?_⟩
  calc v = (b.repr v) 0 • b 0 := hv'
    _ = (((b.repr v) 0 / (b.repr u) 0) * (b.repr u) 0) • b 0 := by rw [div_mul_cancel₀ _ hc]
    _ = ((b.repr v) 0 / (b.repr u) 0) • ((b.repr u) 0 • b 0) := (smul_smul _ _ _).symm
    _ = ((b.repr v) 0 / (b.repr u) 0) • u := by rw [← hu']

/-- **Surjectivity of the descended ray.**  In dimension one the geodesic ray `s ↦ GExp p (s • u)`
of a nonzero tangent vector is a coarse parametrisation of all of `M`: for every `q : M` the
minimising geodesic of Hopf–Rinow joins `p` to `q` with initial vector `v ∈ T_pM`, and `v = s • u`
because `T_pM` is one-dimensional.  Hence `q` is the image of the class of `s` in `AddCircle P`. -/
theorem surjective_rayLift
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [ConnectedSpace M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hdim : Module.finrank ℝ E = 1) (p : M) (u : TangentSpace I p) (hu : u ≠ 0) {P : ℝ}
    (hP : 0 < P)
    (hper : ∀ s : ℝ, GExp (cov := cov) hmet p ((s + P) • u) = GExp (cov := cov) hmet p (s • u))
    (hcont : Continuous (Work.Final.rayLift (cov := cov) hmet p u P hper)) :
    Function.Surjective (Work.Final.rayLift (cov := cov) hmet p u P hper) := by
  classical
  -- `M` is a regular space (locally compact Hausdorff charted space), as Hopf–Rinow requires
  haveI : RegularSpace M := by
    haveI : LocallyCompactSpace H := I.locallyCompactSpace
    haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
    infer_instance
  intro q
  -- Hopf–Rinow: some `v ∈ T_pM` is joined to `q` by a geodesic starting at `p`
  obtain ⟨v, hv, -⟩ :=
    Submission.HopfRinow.exists_geodesic_riemannianEDist_eq (I := I) (cov := cov) hmet htor p q
  -- in dimension one, that initial vector is a multiple of `u`
  haveI : FiniteDimensional ℝ (TangentSpace I p) := inferInstanceAs (FiniteDimensional ℝ E)
  have hrank : Module.finrank ℝ (TangentSpace I p) = 1 := hdim
  obtain ⟨s, hs⟩ : ∃ s : ℝ, v = s • u := exists_smul_eq_of_finrank_eq_one_surj hrank hu
  refine ⟨(s : AddCircle P), ?_⟩
  rw [Work.Final.rayLift_coe, ← hs]
  exact hv

end Work.Final.DimOne
