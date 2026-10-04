import Mathlib
import Submission.Work.Diff.Dim2.Field
import Submission.GSFlow

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Dim2

-- NOTE for the prover: you will need `import Submission.GSFlow` (its `flow_left_lt` is exactly
-- the tool: apply it to `σ s := Φ 0 (-s) y`; the velocity input `curveVelocity σ 0 = -V y` comes
-- from `hΦderiv 0 0 y` by the chain rule).  Neither `Submission.GSFlow` nor `Submission.GSField`
-- can be listed in `depends_on` (they are seeded library modules).
open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 1000000

theorem flow_lowers_f
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    {p : M} {D a γ : ℝ}
    {V : (x : M) → TangentSpace I x} {Φ : ℝ → ℝ → M → M}
    (hVsm : ContMDiff I (I.prod (modelWithCornersSelf ℝ E)) ∞
      (fun y : M => (⟨y, V y⟩ : Bundle.TotalSpace E (TangentSpace I))))
    (hΦsm : ContMDiff ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod I) I ∞
      (fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2))
    (hΦself : ∀ s x, Φ s s x = x)
    (hΦderiv : ∀ s t x, HasMFDerivAt 𝓘(ℝ,ℝ) I (fun τ : ℝ => Φ s τ x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ s t x))))
    (hV : ∀ y : M, a / 4 ≤ Work.Diff.C.rdist (I := I) (M := M) p y →
      Work.Diff.C.rdist (I := I) (M := M) p y ≤ D - 2 * γ →
      Submission.GSField.IsAscentAt hmet p y (V y)) :
    ∀ y : M, a / 4 ≤ Work.Diff.C.rdist (I := I) (M := M) p y →
      Work.Diff.C.rdist (I := I) (M := M) p y ≤ D - 2 * γ →
      ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Set.Ioo (0 : ℝ) δ,
        Work.Diff.C.rdist (I := I) (M := M) p (Φ 0 (-s) y) <
          Work.Diff.C.rdist (I := I) (M := M) p y := by
  intro y hy1 hy2
  have hself : Φ 0 0 y = y := hΦself 0 y
  -- Smoothness of the curve `s ↦ Φ 0 (-s) y`.
  have hσsm : ContMDiffAt 𝓘(ℝ,ℝ) I ∞ (fun s : ℝ => Φ 0 (-s) y) (0 : ℝ) := by
    have hneg : ContMDiffAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) ∞ (fun s : ℝ => -s) (0 : ℝ) :=
      contMDiff_neg 𝓘(ℝ,ℝ) ∞ (0 : ℝ)
    have h1 : ContMDiffAt 𝓘(ℝ,ℝ) (𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)) ∞
        (fun s : ℝ => (((0 : ℝ), -s) : ℝ × ℝ)) (0 : ℝ) :=
      ContMDiffAt.prodMk (contMDiffAt_const (c := (0 : ℝ)) (x := (0 : ℝ))) hneg
    have h2 : ContMDiffAt 𝓘(ℝ,ℝ) ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod I) ∞
        (fun s : ℝ => ((((0 : ℝ), -s) : ℝ × ℝ), y)) (0 : ℝ) :=
      ContMDiffAt.prodMk h1 (contMDiffAt_const (c := y) (x := (0 : ℝ)))
    have h3 : ContMDiffAt 𝓘(ℝ,ℝ) I ∞
        ((fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2)
          ∘ fun s : ℝ => ((((0 : ℝ), -s) : ℝ × ℝ), y)) (0 : ℝ) :=
      ContMDiffAt.comp (0 : ℝ) (hΦsm ((((0 : ℝ), -(0 : ℝ)) : ℝ × ℝ), y)) h2
    exact h3
  -- The velocity at `0` is `-V y`.
  have hvel : Submission.Geodesic.curveVelocity (I := I) (fun s : ℝ => Φ 0 (-s) y) 0 = - V y := by
    have hg : HasMFDerivAt 𝓘(ℝ,ℝ) I (fun τ : ℝ => Φ 0 τ y) (-(0 : ℝ))
        ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ 0 (-(0 : ℝ)) y))) :=
      hΦderiv 0 (-(0 : ℝ)) y
    have hn : HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) (fun s : ℝ => -s) (0 : ℝ)
        (-(1 : ℝ →L[ℝ] ℝ)) :=
      (hasMFDerivAt_id (I := 𝓘(ℝ,ℝ)) (0 : ℝ)).neg
    have hcomp := hg.comp (0 : ℝ) hn
    have hNval : (-(1 : ℝ →L[ℝ] ℝ)) (1 : ℝ) = -(1 : ℝ) := by
      rw [neg_apply, ContinuousLinearMap.one_def, ContinuousLinearMap.id_apply]
    have hGval : ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ 0 (-(0 : ℝ)) y))) (-(1 : ℝ))
        = - V (Φ 0 (-(0 : ℝ)) y) := by
      rw [ContinuousLinearMap.smulRight_apply]
      rw [show (1 : ℝ →L[ℝ] ℝ) (-(1 : ℝ)) = -(1 : ℝ) by
        rw [ContinuousLinearMap.one_def, ContinuousLinearMap.id_apply]]
      rw [neg_one_smul]
    have hself' : Φ 0 (-(0 : ℝ)) y = y := by
      rw [neg_zero]; exact hself
    have hfun : (fun s : ℝ => Φ 0 (-s) y)
        = ((fun τ : ℝ => Φ 0 τ y) ∘ (fun s : ℝ => -s)) := rfl
    rw [Submission.Geodesic.curveVelocity_apply, hfun, hcomp.mfderiv]
    change ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ 0 (-(0 : ℝ)) y)))
        ((-(1 : ℝ →L[ℝ] ℝ)) (1 : ℝ)) = - V y
    rw [hNval, hGval, hself']
  obtain ⟨δ, hδ, hlt⟩ := Submission.GSFlow.flow_left_lt (cov := cov) hmet htor hpinch
    (hV y hy1 hy2) (by simpa using hΦself 0 y) hσsm hvel
  refine ⟨δ, hδ, fun s hs => ?_⟩
  have h1 := hlt s hs
  have hfin1 : Manifold.riemannianEDist I p (Φ 0 (-s) y) ≠ ⊤ :=
    (Submission.HopfRinow.riemannianEDist_lt_top (I := I) (cov := cov) hmet htor p _).ne
  have hfin2 : Manifold.riemannianEDist I p y ≠ ⊤ :=
    (Submission.HopfRinow.riemannianEDist_lt_top (I := I) (cov := cov) hmet htor p y).ne
  show (Manifold.riemannianEDist I p (Φ 0 (-s) y)).toReal
    < (Manifold.riemannianEDist I p y).toReal
  exact (ENNReal.toReal_lt_toReal hfin1 hfin2).mpr h1

end Work.Diff.Dim2
