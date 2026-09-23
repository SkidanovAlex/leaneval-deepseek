import Submission.GSHalf
import Submission.GSStep1
import Submission.GSCap
import Submission.Commons.Topology.Sphere.two_disk_cover_strong

/-!
# The restricted Grove–Shiohama sphere theorem

`Submission.GSRestricted.restricted_sphere_theorem`: a compact, connected Riemannian manifold with
`sec ∈ (1,4]` and `π/2 < diam ≤ 2π/3` is homeomorphic to a sphere.

This is the exact range in which the formalised Toponogov comparison (`HingeClosed`) and hence the
Grove–Shiohama critical point theory apply.  The assembly is the classical one: with `(p,q)` a
diameter pair and `f = d(p,·)`, the level `D - ε` splits `M` into the *half-disk*
`{f ≤ D - ε} ≅ Dⁿ` (`Submission.GSHalf.exists_homeo_halfdisk`) and the *cap*
`{f ≥ D - ε} ≅ Dⁿ` (`Submission.GSCap.exists_homeo_cap`), glued along their common boundary
`{f = D - ε}`; Alexander's trick
(`Commons.Topology.Sphere.two_disk_cover_strong`) then gives `M ≅ Sⁿ`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 2000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal InnerProductSpace
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.Distance
open Submission.EDist

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.GSRestricted

noncomputable section

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable [PathConnectedSpace M] [RegularSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **The restricted Grove–Shiohama sphere theorem.** -/
theorem restricted_sphere_theorem
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    {D : ℝ}
    (hdiam : ∀ r s : M, Manifold.riemannianEDist I r s ≤ ENNReal.ofReal D)
    (hDgt : Real.pi / 2 < D) (hDlt : D < Real.pi)
    (hpq : ∃ p q : M, Manifold.riemannianEDist I p q = ENNReal.ofReal D) :
    Nonempty (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1))) 1) := by
  haveI hcb : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  obtain ⟨p, q, hpq'⟩ := hpq
  have hDnn : 0 ≤ D := le_trans (by linarith [Real.pi_pos]) hDgt.le
  have hfin : ∀ y : M, Manifold.riemannianEDist I p y ≠ ⊤ := fun y =>
    (Submission.HopfRinow.riemannianEDist_lt_top (I := I) (cov := cov) hmet htor p y).ne
  set f : M → ℝ := fun y => (Manifold.riemannianEDist I p y).toReal with hfdef
  have hfcont : Continuous f := by
    show Continuous fun y : M => (Manifold.riemannianEDist I p y).toReal
    have h1 : Continuous fun y : M => Manifold.riemannianEDist I p y :=
      Submission.HopfRinow.continuous_riemannianEDist_left (I := I) p
    exact ENNReal.continuousOn_toReal.comp_continuous h1 hfin
  obtain ⟨ε, hεpos, hεlt, ecp, hec⟩ :=
    Submission.GSCap.exists_homeo_cap (cov := cov) hmet htor hpinch hdiam hDgt hDlt hpq'
  have hbpos : 0 < D - ε := by linarith [Real.pi_pos]
  have hbD : D - ε < D := by linarith
  obtain ⟨ehf, heh⟩ := Submission.GSHalf.exists_homeo_halfdisk (cov := cov) hmet htor hpinch
    hdiam hDgt hDlt hpq' hbpos hbD
  -- the two closed sets
  have hAclosed : IsClosed {y : M | f y ≤ D - ε} := isClosed_Iic.preimage hfcont
  have hBclosed : IsClosed {y : M | D - ε ≤ f y} := isClosed_Ici.preimage hfcont
  have hAB : {y : M | f y ≤ D - ε} ∪ {y : M | D - ε ≤ f y} = Set.univ := by
    ext y
    simp only [Set.mem_union, Set.mem_univ, Set.mem_setOf_eq, iff_true]
    rcases le_total (f y) (D - ε) with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hAint : {y : M | f y ≤ D - ε} ∩ {y : M | D - ε ≤ f y} = {y : M | f y = D - ε} := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact le_antisymm h1 h2
    · intro h
      exact ⟨le_of_eq h, le_of_eq h.symm⟩
  -- the boundary identifications
  have heh' : ehf ⁻¹' (Metric.sphere (0 : Metric.closedBall
        (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 1) 1)
      = {y : ↥{y : M | (Manifold.riemannianEDist I p y).toReal ≤ D - ε} |
          (Manifold.riemannianEDist I p (y : M)).toReal = D - ε} := heh
  have hAc : {y : M | f y ≤ D - ε} ∩ {y : M | D - ε ≤ f y}
      = Subtype.val '' (ehf ⁻¹' (Metric.sphere (0 : Metric.closedBall
          (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 1) 1)) := by
    rw [hAint, heh']
    ext y
    constructor
    · intro hy
      have hy' : f y = D - ε := hy
      refine ⟨⟨y, ?_⟩, ?_, rfl⟩
      · show f y ≤ D - ε
        exact le_of_eq hy'
      · show (Manifold.riemannianEDist I p y).toReal = D - ε
        exact hy'
    · rintro ⟨a, ha, hay⟩
      rw [← hay]
      show f (a : M) = D - ε
      exact ha
  have hec' : ecp ⁻¹' (Metric.sphere (0 : Metric.closedBall
        (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 1) 1)
      = {y : ↥{y : M | D - ε ≤ (Manifold.riemannianEDist I p y).toReal} |
          (Manifold.riemannianEDist I p (y : M)).toReal = D - ε} := hec
  have hBc : {y : M | f y ≤ D - ε} ∩ {y : M | D - ε ≤ f y}
      = Subtype.val '' (ecp ⁻¹' (Metric.sphere (0 : Metric.closedBall
          (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 1) 1)) := by
    rw [hAint, hec']
    ext y
    constructor
    · intro hy
      have hy' : f y = D - ε := hy
      refine ⟨⟨y, ?_⟩, ?_, rfl⟩
      · show D - ε ≤ f y
        exact le_of_eq hy'.symm
      · show (Manifold.riemannianEDist I p y).toReal = D - ε
        exact hy'
    · rintro ⟨a, ha, hay⟩
      rw [← hay]
      show f (a : M) = D - ε
      exact ha
  exact Commons.Topology.Sphere.two_disk_cover_strong hAclosed hBclosed hAB ehf ecp hAc hBc

end

end Submission.GSRestricted
