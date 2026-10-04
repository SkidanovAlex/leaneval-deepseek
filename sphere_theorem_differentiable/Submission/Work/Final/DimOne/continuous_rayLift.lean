import Mathlib
import Submission.Work.Final.DimOne.Defs
import Submission.LensLoop

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Final.DimOne

set_option linter.unusedVariables false

open scoped Manifold ContDiff Bundle Topology ENNReal
open LeanEval.Geometry.SphereTheorem
open CovariantDerivative
open Submission.GlobalExp

theorem continuous_rayLift
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (p : M) (u : TangentSpace I p) (hu : u ≠ 0) {P : ℝ}
    (hP : 0 < P)
    (hper : ∀ s : ℝ, GExp (cov := cov) hmet p ((s + P) • u) = GExp (cov := cov) hmet p (s • u)) :
    Continuous (Work.Final.rayLift (cov := cov) hmet p u P hper) := by
  have hray : Continuous (fun s : ℝ => GExp (cov := cov) hmet p (s • u)) := by
    rw [continuous_iff_continuousAt]
    intro s
    have hs : s ∈ Set.Ioo (-(|s| + 1)) (|s| + 1) :=
      ⟨by linarith [neg_abs_le s], by linarith [le_abs_self s]⟩
    exact ((Submission.LensLoop.contMDiffOn_GExp_smul_Ioo_symm (cov := cov) hmet p hu
      (|s| + 1)).contMDiffAt (isOpen_Ioo.mem_nhds hs)).continuousAt
  refine (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples P)).continuous_iff.mpr ?_
  refine hray.congr (fun x => ?_)
  simp only [Function.comp_apply]
  exact (Work.Final.rayLift_coe (cov := cov) hmet p u P hper x).symm

end Work.Final.DimOne
