import Submission.Work.RiemLib.GSFlow
import Submission.Work.RiemLib.Commons.Topology.Order.strictMonoOn_of_left_lt

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Strict monotonicity of `d(p,·)` along the flow of an ascent field

`Submission/GSFlow.flow_left_lt` shows that moving *backwards* along the flow of an ascent field
strictly decreases `d(p,·)`.  Here we upgrade this pointwise statement to the strict monotonicity of
`t ↦ d(p, φ x t)` on an interval, using the abstract lemma
`Commons.Topology.Order.strictMonoOn_of_left_lt`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal InnerProductSpace
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GSField
open Submission.GSFlow
open Submission.Length

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.GSMono

noncomputable section

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **Strict monotonicity of `d(p,·)` along the flow.**  If the global flow `φ` of a field `V` is an
ascent field for `d(p,·)` on a set `W`, and the trajectory `t ↦ φ x t` stays in `W` on `[a,b]`, then
`t ↦ d(p, φ x t)` is strictly increasing on `[a,b]`. -/
theorem strictMonoOn_flow
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    [PathConnectedSpace M] [RegularSpace M]
    {p : M} {V : (y : M) → TangentSpace I y} {φ : M → ℝ → M}
    (hφ0 : ∀ y : M, φ y 0 = y)
    (hadd : ∀ (y : M) (s t : ℝ), φ (φ y s) t = φ y (s + t))
    (hφsm : ∀ y : M, ContMDiffAt 𝓘(ℝ) I ∞ (φ y) 0)
    (hvel : ∀ y : M, curveVelocity (I := I) (φ y) 0 = V y)
    {W : Set M} (hasc : ∀ y ∈ W, IsAscentAt (cov := cov) hmet p y (V y))
    {a b : ℝ} (hab : a ≤ b) {x₀ : M} (hW : ∀ t ∈ Set.Icc a b, φ x₀ t ∈ W)
    (hcont : ContinuousOn (fun t : ℝ => (Manifold.riemannianEDist I p (φ x₀ t)).toReal)
      (Set.Icc a b)) :
    StrictMonoOn (fun t : ℝ => (Manifold.riemannianEDist I p (φ x₀ t)).toReal) (Set.Icc a b) := by
  haveI hcb : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  refine Commons.Topology.Order.strictMonoOn_of_left_lt hab hcont ?_
  intro t ht
  have hVt : IsAscentAt (cov := cov) hmet p (φ x₀ t) (V (φ x₀ t)) := hasc (φ x₀ t) (hW t ht)
  -- the reversed flow line through `φ x t`
  have hbase : (fun s : ℝ => φ (φ x₀ t) (-s)) 0 = φ x₀ t := by
    show φ (φ x₀ t) (-(0:ℝ)) = φ x₀ t
    rw [neg_zero]
    exact hφ0 _
  have hvelσ : curveVelocity (I := I) (fun s : ℝ => φ (φ x₀ t) (-s)) 0
      = -V (φ x₀ t) := by
    have hfun : (fun s : ℝ => φ (φ x₀ t) (-s))
        = (fun s : ℝ => φ (φ x₀ t) ((-1:ℝ) * s + 0)) := by
      funext s; rw [neg_one_mul, add_zero]
    rw [hfun]
    have hmd : MDifferentiableAt 𝓘(ℝ) I (φ (φ x₀ t)) ((-1:ℝ) * 0 + 0) := by
      rw [mul_zero, add_zero]
      exact (hφsm (φ x₀ t)).mdifferentiableAt (by simp)
    rw [curveVelocity_comp_mul_add (I := I) (γ := φ (φ x₀ t)) (c := -1) (d := 0) (t := 0) hmd,
      mul_zero, add_zero, neg_one_smul]
    exact congrArg (fun w => -w) (hvel (φ x₀ t))
  have hσsm : ContMDiffAt 𝓘(ℝ) I ∞ (fun s : ℝ => φ (φ x₀ t) (-s)) 0 := by
    have hf : ContMDiffAt 𝓘(ℝ) I ∞ (φ (φ x₀ t)) (-(0:ℝ)) := by
      rw [neg_zero]
      exact hφsm (φ x₀ t)
    exact hf.comp 0 contMDiffAt_id.neg
  obtain ⟨δ, hδpos, hδ'⟩ :=
    flow_left_lt (cov := cov) hmet htor hpinch (p := p) (x := φ x₀ t) (V := V (φ x₀ t))
      hVt (σ := fun s : ℝ => φ (φ x₀ t) (-s)) hbase hσsm hvelσ
  refine ⟨δ, hδpos, fun ε hε => ?_⟩
  have h := hδ' ε hε
  have hpt : φ x₀ (t - ε) = φ (φ x₀ t) (-ε) := by
    rw [hadd x₀ t (-ε), sub_eq_add_neg]
  rw [hpt]
  have hfina : Manifold.riemannianEDist I p (φ (φ x₀ t) (-ε)) ≠ ⊤ :=
    (Submission.HopfRinow.riemannianEDist_lt_top (I := I) (cov := cov) hmet htor p _).ne
  have hfinb : Manifold.riemannianEDist I p (φ x₀ t) ≠ ⊤ :=
    (Submission.HopfRinow.riemannianEDist_lt_top (I := I) (cov := cov) hmet htor p _).ne
  exact (ENNReal.toReal_lt_toReal hfina hfinb).mpr h

end

end Submission.GSMono
