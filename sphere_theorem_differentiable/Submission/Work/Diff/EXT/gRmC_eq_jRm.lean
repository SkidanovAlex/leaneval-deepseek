import Mathlib
import Submission.Work.Diff.GE.chartcalc
import Submission.Work.Diff.GE.koszul
import Submission.Work.Diff.GE.norms_defs
import Submission.Work.Diff.GE.cGram_chrB_eq_koszulPair
import Submission.Work.Diff.GE.cGram_eq_sum_gramInv
import Submission.Work.Diff.EXT.cGram_chrB_chrB_eq_sum_koszul
import Submission.Work.Diff.GE.rmChartExpr_kit
import Submission.Work.Diff.GE.rmP_jointSmooth
import Submission.Work.Diff.T.lc_smooth
import Submission.Work.Diff.T.mvfderiv_frameVector_real
import Submission.Work.Diff.EXT.chartRic_jet_partial
import Submission.Work.Diff.EXT.ricJetDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The curvature components in the chart frame are the scalar jet expression

This file proves `Work.Diff.EXT.gRmC_eq_jRm`: the curvature component
`gRmC g x₀ p a b c d = ⟪R(σ_a,σ_b)σ_d, σ_c⟫` of the Levi-Civita connection of a smooth metric `g`,
read in the coordinate frame of the chart at `x₀`, equals the classical coordinate formula
`jRm A L B a b c d` built from the value `A = chartMatFun g x₀ y`, the first derivative
`L = fderiv (chartMatFun g x₀) y` and the second derivative `B = fderiv (fderiv (chartMatFun)) y`
of the chart matrix.

Route.

* `gRmC = cRm` (`rmC4_eq_cRm`): unfold the curvature via `curvVec_eq_chart`.
* `cRm = rmChartExpr` (the product rule `cGram_dB_chrB_prod_rule`, below): the metric
  compatibility (Leibniz) rule for the pairing `⟪∇_{σ_B}σ_Dd, σ_K⟫` combined with the chart formula
  for `∇` of a frame field (`cov_eq_frameVector_chartCoord_at`).
* `rmChartExpr = sRm (dJet0) (dJet1) (dJet2)` (`rmChartExpr_eq_sRm`, proved in
  `EXT.chartRic_jet_partial`).
* `sRm = jRm`: the two expressions differ only in the order of the indices, which is exchanged
  using the symmetry of the chart matrix and of its first two derivatives.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT

section Aux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

/-- **The chart formula for `∇` of a frame field, at a point.**  Local form of
`Submission.ChartCurv.cov_eq_frameVector_chartCoord`: the section `W` needs only to be
differentiable at `p`. -/
private theorem cov_eq_frameVector_chartCoord_at
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))} [ContMDiffCovariantDerivative cov ∞]
    {W : Π x : M, TangentSpace I x} {c : M → E} {x₀ p : M}
    (hp : p ∈ (chartAt H' x₀).source) (hW : CMDiffAt ∞ (T% W) p)
    (hc : ContMDiffAt I 𝓘(ℝ, E) ∞ c p)
    (heq : W =ᶠ[𝓝 p] fun q => Submission.Geodesic.frameVector (I := I) x₀ q (c q)) (v : E) :
    cov W p (Submission.Geodesic.frameVector (I := I) x₀ p v)
      = Submission.Geodesic.frameVector (I := I) x₀ p
          (mvfderiv I c p (Submission.Geodesic.frameVector (I := I) x₀ p v)
            + Submission.ChartCurv.chrB cov x₀ p (c p) v) := by
  classical
  have hfr : (fun q : M => Submission.Geodesic.frameVector (I := I) x₀ q (c q))
      = (fun q : M => ∑ i, (Module.finBasis ℝ E).coord i (c q) •
          Submission.Geodesic.frameSection (I := I) x₀ (Module.finBasis ℝ E i) q) := by
    funext q
    show Submission.Geodesic.frameVector (I := I) x₀ q (c q)
      = ∑ i, (Module.finBasis ℝ E).coord i (c q) •
          Submission.Geodesic.frameSection (I := I) x₀ (Module.finBasis ℝ E i) q
    conv_lhs => rw [← Submission.ChartCurv.sum_coord_smul_eq (E := E) (c q)]
    rw [Submission.Geodesic.frameVector_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    show (Module.finBasis ℝ E).coord i (c q) •
          Submission.Geodesic.frameVector (I := I) x₀ q (Module.finBasis ℝ E i)
      = (Module.finBasis ℝ E).coord i (c q) •
          Submission.Geodesic.frameSection (I := I) x₀ (Module.finBasis ℝ E i) q
    rw [show Submission.Geodesic.frameSection (I := I) x₀ (Module.finBasis ℝ E i) q
        = Submission.Geodesic.frameVector (I := I) x₀ q (Module.finBasis ℝ E i) from rfl]
  have hkey := Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.cov_eq_sum_of_eventuallyEq_pointwise
    (cov := cov) Finset.univ
    (fun i (q : M) => (Module.finBasis ℝ E).coord i (c q))
    (fun i (q : M) => Submission.Geodesic.frameSection (I := I) x₀ (Module.finBasis ℝ E i) q)
    (Z := W) (x := p) (v := Submission.Geodesic.frameVector (I := I) x₀ p v) hW
    (fun i => Submission.Geodesic.contMDiffAt_frameSection (I := I) x₀
      (Module.finBasis ℝ E i) hp)
    (fun i => (((Module.finBasis ℝ E).coord i : E →ₗ[ℝ] ℝ).toContinuousLinearMap).contMDiffAt.comp
      p hc)
    (heq.trans (Filter.Eventually.of_forall (fun q => congrFun hfr q)))
  rw [hkey]
  have hsum1 : (∑ i, (Module.finBasis ℝ E).coord i (c p) •
        cov (Submission.Geodesic.frameSection (I := I) x₀ (Module.finBasis ℝ E i)) p
          (Submission.Geodesic.frameVector (I := I) x₀ p v))
      = Submission.Geodesic.frameVector (I := I) x₀ p
          (Submission.ChartCurv.chrB cov x₀ p (c p) v) := by
    have h1 : ∀ i, cov (Submission.Geodesic.frameSection (I := I) x₀ (Module.finBasis ℝ E i)) p
          (Submission.Geodesic.frameVector (I := I) x₀ p v)
        = Submission.Geodesic.frameVector (I := I) x₀ p
            (Submission.Geodesic.christoffelEval cov x₀ p (Module.finBasis ℝ E i)
              (Submission.Geodesic.frameVector (I := I) x₀ p v)) :=
      fun i => Submission.Geodesic.cov_frameSection_eq cov x₀ p (Module.finBasis ℝ E i)
        (Submission.Geodesic.frameVector (I := I) x₀ p v) hp
    simp only [h1]
    rw [← Submission.Geodesic.frameVector_sum,
      ← Submission.Geodesic.christoffelEval_sum_left Finset.univ cov x₀ p
          (fun i => (Module.finBasis ℝ E).coord i (c p))
          (fun i => Module.finBasis ℝ E i)
          (Submission.Geodesic.frameVector (I := I) x₀ p v) hp]
    congr 1
    rw [Submission.ChartCurv.chrB_apply, Submission.ChartCurv.sum_coord_smul_eq]
  have hsum2 : (∑ i, mvfderiv I (fun q : M => (Module.finBasis ℝ E).coord i (c q)) p
        (Submission.Geodesic.frameVector (I := I) x₀ p v) •
          Submission.Geodesic.frameSection (I := I) x₀ (Module.finBasis ℝ E i) p)
      = Submission.Geodesic.frameVector (I := I) x₀ p
          (mvfderiv I c p (Submission.Geodesic.frameVector (I := I) x₀ p v)) := by
    simp only [show ∀ i : Fin (Module.finrank ℝ E),
        Submission.Geodesic.frameSection (I := I) x₀ (Module.finBasis ℝ E i)
          = fun q => Submission.Geodesic.frameVector (I := I) x₀ q (Module.finBasis ℝ E i)
      from fun i => rfl]
    rw [← Submission.Geodesic.frameVector_sum,
      Submission.ChartCurv.mvfderiv_eq_sum_coord (I := I) (hc.mdifferentiableAt (by simp))]
  rw [hsum1, hsum2, ← Submission.Geodesic.frameVector_add, add_comm]

/-- The covariant derivative of a coordinate frame field along another coordinate frame field is
smooth at every point of the chart. -/
theorem contMDiffAt_cov_frameSection (g : Submission.Diff.SMet I M)
    (hcov : ContMDiffCovariantDerivative (Submission.Diff.lcOf g) ∞)
    (x₀ : M) {p : M} (hp : p ∈ (chartAt H' x₀).source) (i j : Fin (Module.finrank ℝ E)) :
    CMDiffAt ∞ (T% (fun q : M => (Submission.Diff.lcOf g)
        (Submission.Geodesic.frameSection (I := I) x₀ (Module.finBasis ℝ E i)) q
        (Submission.Geodesic.frameVector (I := I) x₀ q (Module.finBasis ℝ E j)))) p := by
  haveI : ContMDiffCovariantDerivative (Submission.Diff.lcOf g) ∞ := hcov
  have hσ : ∀ k : Fin (Module.finrank ℝ E),
      CMDiff[(chartAt H' x₀).source] ∞
        (T% (fun q : M => (trivializationAt E (TangentSpace I) x₀).symmL ℝ q
          (Module.finBasis ℝ E k))) :=
    fun k => Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiffOn_trivializationAt_symmL_section
      (I := I) x₀ (Module.finBasis ℝ E k)
  have hW : CMDiff[(chartAt H' x₀).source] ∞
      (T% (fun q : M => (Submission.Diff.lcOf g)
        (Submission.Geodesic.frameSection (I := I) x₀ (Module.finBasis ℝ E i)) q
        (Submission.Geodesic.frameVector (I := I) x₀ q (Module.finBasis ℝ E j)))) :=
    Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiffOn_cov_apply
      (Submission.Diff.lcOf g) (inferInstance) (chartAt H' x₀).open_source (hσ i) (hσ j)
  exact (hW p hp).contMDiffAt ((chartAt H' x₀).open_source.mem_nhds hp)

/-- Congruence of `mvfderiv` for real-valued functions under eventual equality. -/
theorem mvfderiv_congr_of_eventuallyEq_real {f₁ f₂ : M → ℝ} {x : M}
    (h : f₁ =ᶠ[𝓝 x] f₂) : mvfderiv I f₁ x = mvfderiv I f₂ x := by
  rw [mvfderiv, mvfderiv, h.eq_of_nhds, Filter.EventuallyEq.mfderiv_eq h]
  all_goals first | rfl | (ext v; rfl)

end Aux

section ProductRule

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

/-- **The product rule for the coordinate Christoffel pairing.**  The pairing
`Γ_{BDK} = ⟪∇_{σ_B}σ_D, σ_K⟫` is a first derivative of the metric, so its derivative in the
direction `σ_A` is `⟪∇_A∇_Bσ_D, σ_K⟫ + ⟪∇_Bσ_D, ∇_Aσ_K⟫`; writing `∇_A∇_Bσ_D` in the chart
splits as `∂_A` of the Christoffel vector plus the Christoffel contraction. -/
theorem cGram_dB_chrB_prod_rule
    (g : Submission.Diff.SMet I M)
    (hcov : ContMDiffCovariantDerivative (Submission.Diff.lcOf g) ∞)
    (x₀ : M) {p : M} (hp : p ∈ (chartAt H' x₀).source)
    (A B Dd K : Fin (Module.finrank ℝ E)) :
    Work.Diff.GE.cGram g x₀ p
        (Submission.ChartCurv.dB (Submission.Diff.lcOf g) x₀ p
          (Module.finBasis ℝ E A) (Module.finBasis ℝ E Dd) (Module.finBasis ℝ E B))
        (Module.finBasis ℝ E K)
      + Work.Diff.GE.cGram g x₀ p
          (Submission.ChartCurv.chrB (Submission.Diff.lcOf g) x₀ p
            (Submission.ChartCurv.chrB (Submission.Diff.lcOf g) x₀ p
              (Module.finBasis ℝ E Dd) (Module.finBasis ℝ E B))
            (Module.finBasis ℝ E A))
          (Module.finBasis ℝ E K)
      = Work.Diff.GE.dOp (I := I) x₀ A
          (Work.Diff.GE.koszulPair (I := I) (fun _ : ℝ => g) x₀ B Dd K) 0 p
        - Work.Diff.GE.cGram g x₀ p
            (Submission.ChartCurv.chrB (Submission.Diff.lcOf g) x₀ p
              (Module.finBasis ℝ E Dd) (Module.finBasis ℝ E B))
            (Submission.ChartCurv.chrB (Submission.Diff.lcOf g) x₀ p
              (Module.finBasis ℝ E K) (Module.finBasis ℝ E A)) := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  haveI : ContMDiffCovariantDerivative (Submission.Diff.lcOf g) ∞ := hcov
  let U : Π q : M, TangentSpace I q := fun q => (Submission.Diff.lcOf g)
      (Submission.Geodesic.frameSection (I := I) x₀ (Module.finBasis ℝ E Dd)) q
      (Submission.Geodesic.frameVector (I := I) x₀ q (Module.finBasis ℝ E B))
  let F : M → E := fun q => Submission.ChartCurv.chrB (Submission.Diff.lcOf g) x₀ q
      (Module.finBasis ℝ E Dd) (Module.finBasis ℝ E B)
  have hFsm : ContMDiffAt I 𝓘(ℝ, E) ∞ F p :=
    ((Submission.ChartCurv.contMDiffOn_gammaEntry (cov := Submission.Diff.lcOf g) x₀ Dd B) p hp).contMDiffAt
      ((chartAt H' x₀).open_source.mem_nhds hp)
  have hUsm : CMDiffAt ∞ (T% U) p :=
    contMDiffAt_cov_frameSection (I := I) g hcov x₀ hp Dd B
  have hUF : U =ᶠ[𝓝 p] fun q => Submission.Geodesic.frameVector (I := I) x₀ q (F q) := by
    filter_upwards [((chartAt H' x₀).open_source).mem_nhds hp] with q hq
    show (Submission.Diff.lcOf g)
        (Submission.Geodesic.frameSection (I := I) x₀ (Module.finBasis ℝ E Dd)) q
        (Submission.Geodesic.frameVector (I := I) x₀ q (Module.finBasis ℝ E B))
      = Submission.Geodesic.frameVector (I := I) x₀ q
          (Submission.ChartCurv.chrB (Submission.Diff.lcOf g) x₀ q
            (Module.finBasis ℝ E Dd) (Module.finBasis ℝ E B))
    exact Submission.Geodesic.cov_frameSection_eq (Submission.Diff.lcOf g) x₀ q
      (Module.finBasis ℝ E Dd) (Submission.Geodesic.frameVector (I := I) x₀ q (Module.finBasis ℝ E B)) hq
  -- the chart formula for `∇_A U`
  have hcovU : (Submission.Diff.lcOf g) U p
      (Submission.Geodesic.frameVector (I := I) x₀ p (Module.finBasis ℝ E A))
      = Submission.Geodesic.frameVector (I := I) x₀ p
          (Submission.ChartCurv.dB (Submission.Diff.lcOf g) x₀ p
              (Module.finBasis ℝ E A) (Module.finBasis ℝ E Dd) (Module.finBasis ℝ E B)
            + Submission.ChartCurv.chrB (Submission.Diff.lcOf g) x₀ p
              (Submission.ChartCurv.chrB (Submission.Diff.lcOf g) x₀ p
                (Module.finBasis ℝ E Dd) (Module.finBasis ℝ E B))
              (Module.finBasis ℝ E A)) := by
    have h := cov_eq_frameVector_chartCoord_at (I := I) (cov := Submission.Diff.lcOf g)
      (W := U) (c := F) hp hUsm hFsm hUF (Module.finBasis ℝ E A)
    simpa only [show mvfderiv I F p
        (Submission.Geodesic.frameVector (I := I) x₀ p (Module.finBasis ℝ E A))
        = Submission.ChartCurv.dB (Submission.Diff.lcOf g) x₀ p
            (Module.finBasis ℝ E A) (Module.finBasis ℝ E Dd) (Module.finBasis ℝ E B) from rfl,
      show F p = Submission.ChartCurv.chrB (Submission.Diff.lcOf g) x₀ p
          (Module.finBasis ℝ E Dd) (Module.finBasis ℝ E B) from rfl] using h
  -- the metric-compatibility equation
  have hmc := Work.Diff.T.lc_metric_identity (I := I)
    (X := fun q : M => Submission.Geodesic.frameVector (I := I) x₀ q (Module.finBasis ℝ E A))
    (Y := U)
    (Z := fun q : M => Submission.Geodesic.frameVector (I := I) x₀ q (Module.finBasis ℝ E K))
    (x := p)
    (Submission.Geodesic.mdiffAt_frameSection x₀ (Module.finBasis ℝ E A) hp)
    (hUsm.mdifferentiableAt (by simp))
    (Submission.Geodesic.mdiffAt_frameSection x₀ (Module.finBasis ℝ E K) hp)
  -- the pairing `⟪∇_B σ_Dd, σ_K⟫` and its derivative
  have hpair : (fun q : M => Work.Diff.GE.koszulPair (I := I) (fun _ : ℝ => g) x₀ B Dd K 0 q)
      =ᶠ[𝓝 p] (fun q : M => (g).inner q (U q)
        (Submission.Geodesic.frameVector (I := I) x₀ q (Module.finBasis ℝ E K))) := by
    filter_upwards [((chartAt H' x₀).open_source).mem_nhds hp] with q hq
    rw [← Work.Diff.GE.fPair_eq_koszul (I := I) (fun _ : ℝ => g) x₀ 0 hq B Dd K]
    show (g).inner q ((Submission.Diff.lcOf g)
        (Work.Diff.GE.cFrame (I := I) x₀ Dd) q (Work.Diff.GE.cFrame (I := I) x₀ B q))
        (Work.Diff.GE.cFrame (I := I) x₀ K q)
      = (g).inner q (U q) (Submission.Geodesic.frameVector (I := I) x₀ q (Module.finBasis ℝ E K))
    rfl
  have hdOp : Work.Diff.GE.dOp (I := I) x₀ A
      (Work.Diff.GE.koszulPair (I := I) (fun _ : ℝ => g) x₀ B Dd K) 0 p
      = mvfderiv I (fun q : M => (g).inner q (U q)
          (Submission.Geodesic.frameVector (I := I) x₀ q (Module.finBasis ℝ E K))) p
          (Submission.Geodesic.frameVector (I := I) x₀ p (Module.finBasis ℝ E A)) := by
    show mvfderiv I (fun q : M => Work.Diff.GE.koszulPair (I := I) (fun _ : ℝ => g) x₀ B Dd K 0 q)
        p (Submission.Geodesic.frameVector (I := I) x₀ p (Module.finBasis ℝ E A)) = _
    rw [mvfderiv_congr_of_eventuallyEq_real (I := I) hpair]
  -- identify the two terms of the metric-compatibility equation
  have hlc : (Submission.Diff.lcOf g) = leviCivitaConnection I M := rfl
  have hmc' := hmc
  simp only [show ∀ (y : M) (u v : TangentSpace I y), Inner.inner ℝ u v = (g).inner y u v from
    fun _ _ _ => rfl, ← hlc] at hmc'
  have hterm1 : (g).inner p ((Submission.Diff.lcOf g) U p
        (Submission.Geodesic.frameVector (I := I) x₀ p (Module.finBasis ℝ E A)))
        (Submission.Geodesic.frameVector (I := I) x₀ p (Module.finBasis ℝ E K))
      = Work.Diff.GE.cGram g x₀ p
          (Submission.ChartCurv.dB (Submission.Diff.lcOf g) x₀ p
            (Module.finBasis ℝ E A) (Module.finBasis ℝ E Dd) (Module.finBasis ℝ E B))
          (Module.finBasis ℝ E K)
        + Work.Diff.GE.cGram g x₀ p
            (Submission.ChartCurv.chrB (Submission.Diff.lcOf g) x₀ p
              (Submission.ChartCurv.chrB (Submission.Diff.lcOf g) x₀ p
                (Module.finBasis ℝ E Dd) (Module.finBasis ℝ E B))
              (Module.finBasis ℝ E A))
            (Module.finBasis ℝ E K) := by
    rw [hcovU, ← Work.Diff.GE.cGram_add_fst]
    rfl
  have hterm2 : (g).inner p (U p) ((Submission.Diff.lcOf g)
        (fun q : M => Submission.Geodesic.frameVector (I := I) x₀ q (Module.finBasis ℝ E K)) p
        (Submission.Geodesic.frameVector (I := I) x₀ p (Module.finBasis ℝ E A)))
      = Work.Diff.GE.cGram g x₀ p
          (Submission.ChartCurv.chrB (Submission.Diff.lcOf g) x₀ p
            (Module.finBasis ℝ E Dd) (Module.finBasis ℝ E B))
          (Submission.ChartCurv.chrB (Submission.Diff.lcOf g) x₀ p
            (Module.finBasis ℝ E K) (Module.finBasis ℝ E A)) := by
    have hUp : U p = Submission.Geodesic.frameVector (I := I) x₀ p
        (Submission.ChartCurv.chrB (Submission.Diff.lcOf g) x₀ p
          (Module.finBasis ℝ E Dd) (Module.finBasis ℝ E B)) :=
      (hUF.eq_of_nhds).trans rfl
    have hZ : (Submission.Diff.lcOf g)
        (fun q : M => Submission.Geodesic.frameVector (I := I) x₀ q (Module.finBasis ℝ E K)) p
        (Submission.Geodesic.frameVector (I := I) x₀ p (Module.finBasis ℝ E A))
        = Submission.Geodesic.frameVector (I := I) x₀ p
            (Submission.ChartCurv.chrB (Submission.Diff.lcOf g) x₀ p
              (Module.finBasis ℝ E K) (Module.finBasis ℝ E A)) := by
      rw [show (fun q : M => Submission.Geodesic.frameVector (I := I) x₀ q
            (Module.finBasis ℝ E K))
          = Submission.Geodesic.frameSection (I := I) x₀ (Module.finBasis ℝ E K) from rfl]
      rw [Submission.Geodesic.cov_frameSection_eq (Submission.Diff.lcOf g) x₀ p
        (Module.finBasis ℝ E K) (Submission.Geodesic.frameVector (I := I) x₀ p
          (Module.finBasis ℝ E A)) hp]
      rfl
    rw [hUp, hZ]
    rfl
  rw [hdOp, hmc', hterm1, hterm2]
  ring


end ProductRule

/-! ## The bridge `cRm = rmChartExpr` -/

section Assembly

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

/-- The manifold curvature component `⟪R(σ_a,σ_b)σ_d, σ_c⟫` is the chart expression `cRm`. -/
theorem gRmC_eq_cRm (g : Submission.Diff.SMet I M) (x₀ : M) {p : M}
    (hp : p ∈ (chartAt H' x₀).source) (a b c d : Fin (Module.finrank ℝ E)) :
    Work.Diff.EXT.gRmC (I := I) g x₀ p a b c d
      = Work.Diff.GE.cRm g x₀ p (Module.finBasis ℝ E a) (Module.finBasis ℝ E b)
          (Module.finBasis ℝ E c) (Module.finBasis ℝ E d) := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  rw [show Work.Diff.EXT.gRmC (I := I) g x₀ p a b c d
      = Work.Diff.GE.rmC4 (I := I) (fun _ : ℝ => g) x₀ 0 p a b c d from rfl]
  exact Work.Diff.GE.rmC4_eq_cRm (I := I) (Work.Diff.T.lc_smooth (I := I) (M := M))
    (fun _ : ℝ => g) x₀ 0 hp a b c d

/-- **The chart coordinate expression for the curvature.**  Expanding `cCurv` and applying the
product rule `cGram_dB_chrB_prod_rule` twice produces `rmChartExpr`. -/
theorem cRm_eq_rmChartExpr (g : Submission.Diff.SMet I M)
    (hcov : ContMDiffCovariantDerivative (Submission.Diff.lcOf g) ∞)
    (x₀ : M) {p : M} (hp : p ∈ (chartAt H' x₀).source) (a b c d : Fin (Module.finrank ℝ E)) :
    Work.Diff.GE.cRm g x₀ p (Module.finBasis ℝ E a) (Module.finBasis ℝ E b)
        (Module.finBasis ℝ E c) (Module.finBasis ℝ E d)
      = Work.Diff.GE.rmChartExpr (I := I) (fun _ : ℝ => g) x₀ a b c d 0 p := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  have hLC : Submission.Diff.LCSmooth I M := Work.Diff.T.lc_smooth
  have h1 := cGram_dB_chrB_prod_rule (I := I) g hcov x₀ hp a b d c
  have h2 := cGram_dB_chrB_prod_rule (I := I) g hcov x₀ hp b a d c
  have h3 : Work.Diff.GE.cGram g x₀ p
        (Submission.ChartCurv.chrB (Submission.Diff.lcOf g) x₀ p
          (Module.finBasis ℝ E d) (Module.finBasis ℝ E b))
        (Submission.ChartCurv.chrB (Submission.Diff.lcOf g) x₀ p
          (Module.finBasis ℝ E c) (Module.finBasis ℝ E a))
      = ∑ m, ∑ n, Work.Diff.GE.GramInv (fun _ : ℝ => g) x₀ 0 p m n
          * Work.Diff.GE.koszulPair (fun _ : ℝ => g) x₀ b d m 0 p
          * Work.Diff.GE.koszulPair (fun _ : ℝ => g) x₀ a c n 0 p :=
    cGram_chrB_chrB_eq_sum_koszul (I := I) hLC (fun _ : ℝ => g) x₀ 0 hp b d a c
  have h4 : Work.Diff.GE.cGram g x₀ p
        (Submission.ChartCurv.chrB (Submission.Diff.lcOf g) x₀ p
          (Module.finBasis ℝ E d) (Module.finBasis ℝ E a))
        (Submission.ChartCurv.chrB (Submission.Diff.lcOf g) x₀ p
          (Module.finBasis ℝ E c) (Module.finBasis ℝ E b))
      = ∑ m, ∑ n, Work.Diff.GE.GramInv (fun _ : ℝ => g) x₀ 0 p m n
          * Work.Diff.GE.koszulPair (fun _ : ℝ => g) x₀ a d m 0 p
          * Work.Diff.GE.koszulPair (fun _ : ℝ => g) x₀ b c n 0 p :=
    cGram_chrB_chrB_eq_sum_koszul (I := I) hLC (fun _ : ℝ => g) x₀ 0 hp a d b c
  rw [Work.Diff.GE.cRm, Work.Diff.GE.cCurv, Work.Diff.GE.cGram_sub_fst,
    Work.Diff.GE.cGram_add_fst, Work.Diff.GE.cGram_sub_fst, Work.Diff.GE.rmChartExpr]
  linear_combination (h1 - h2) - h3 + h4

/-! ## Symmetries of the chart matrix and its jets -/

/-- `fderiv` commutes with reading a matrix entry. -/
theorem fderiv_eval_coord {Φ : E → MatE (E := E)} {y : E} (hd : DifferentiableAt ℝ Φ y)
    (w : E) (i j : Fin (Module.finrank ℝ E)) :
    fderiv ℝ (fun x : E => Φ x i j) y w = (fderiv ℝ Φ y w) i j := by
  have hd1 : DifferentiableAt ℝ (fun x : E => Φ x i) y := by
    simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using
      (ContinuousLinearMap.proj i).differentiableAt.comp y hd
  have hd2 : DifferentiableAt ℝ (fun x : E => Φ x i j) y := by
    simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using
      (ContinuousLinearMap.proj j).differentiableAt.comp y hd1
  rw [fderiv_apply (𝕜 := ℝ) (x := y) (Φ := fun x : E => Φ x i) hd1 j,
    fderiv_apply (𝕜 := ℝ) (x := y) (Φ := Φ) hd i]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]

/-- The chart matrix of a metric is symmetric. -/
theorem chartMatFun_swap (g : Submission.Diff.SMet I M) (x₀ : M) (y : E)
    (i j : Fin (Module.finrank ℝ E)) :
    chartMatFun g x₀ y i j = chartMatFun g x₀ y j i :=
  (g).symm ((extChartAt I x₀).symm y)
    (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
      (Module.finBasis ℝ E i))
    (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
      (Module.finBasis ℝ E j))

/-- The derivative of a pointwise symmetric matrix-valued function is pointwise symmetric. -/
theorem fderiv_eval_coord_swap {Φ : E → MatE (E := E)} {y : E} (hd : DifferentiableAt ℝ Φ y)
    (hsymm : ∀ y' (i j : Fin (Module.finrank ℝ E)), Φ y' i j = Φ y' j i)
    (v : E) (i j : Fin (Module.finrank ℝ E)) :
    (fderiv ℝ Φ y v) i j = (fderiv ℝ Φ y v) j i := by
  rw [← fderiv_eval_coord (Φ := Φ) hd v i j, ← fderiv_eval_coord (Φ := Φ) hd v j i]
  rw [show (fun x : E => Φ x i j) = (fun x : E => Φ x j i) from funext fun x => hsymm x i j]

/-- The first jet of the chart matrix is symmetric in its two matrix indices. -/
theorem dJet1_swap (g : Submission.Diff.SMet I M) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) (k i j : Fin (Module.finrank ℝ E)) :
    dJet1 g x₀ y k i j = dJet1 g x₀ y k j i := by
  have hd : DifferentiableAt ℝ (chartMatFun g x₀) y :=
    (contDiffAt_chartMatFun (I := I) g x₀ hy).differentiableAt (by simp)
  show (fderiv ℝ (chartMatFun g x₀) y (Module.finBasis ℝ E k)) i j = _
  exact fderiv_eval_coord_swap hd (fun y' i j => chartMatFun_swap g x₀ y' i j)
    (Module.finBasis ℝ E k) i j

/-- **The component of a second derivative.**  The derivative of the `(i,j)`-component of
`x ↦ fderiv Φ x v` is the `(i,j)`-component of the second derivative of `Φ`, applied to `v`. -/
theorem fderiv_fderiv_apply_coord {Φ : E → MatE (E := E)} {y : E}
    (hΦ : ContDiffAt ℝ 2 Φ y) (v w : E) (i j : Fin (Module.finrank ℝ E)) :
    fderiv ℝ (fun x : E => (fderiv ℝ Φ x v) i j) y w
      = ((fderiv ℝ (fun x : E => fderiv ℝ Φ x) y w) v) i j := by
  have h1 : ContDiffAt ℝ 1 (fun x : E => fderiv ℝ Φ x) y :=
    hΦ.fderiv_right (m := 1) (by norm_num)
  have hd : DifferentiableAt ℝ (fun x : E => fderiv ℝ Φ x) y :=
    h1.differentiableAt (by norm_num)
  have hdV : DifferentiableAt ℝ (fun x : E => fderiv ℝ Φ x v) y := by
    simpa only [Function.comp_def, ContinuousLinearMap.apply_apply] using
      (ContinuousLinearMap.apply ℝ (MatE (E := E)) v).differentiableAt.comp y hd
  have hsw : fderiv ℝ (fun x : E => fderiv ℝ Φ x v) y
      = (fderiv ℝ (fun x : E => fderiv ℝ Φ x) y).flip v := by
    rw [fderiv_clm_apply (c := fun x : E => fderiv ℝ Φ x) (u := fun _ : E => v) hd
      (differentiableAt_const v)]
    have hz : fderiv ℝ (fun _ : E => v) y = 0 := (hasFDerivAt_const (𝕜 := ℝ) v y).fderiv
    rw [hz]
    simp
  rw [fderiv_eval_coord (Φ := fun x : E => fderiv ℝ Φ x v) hdV w i j, hsw]
  simp only [ContinuousLinearMap.flip_apply]

/-- The second jet of the chart matrix is symmetric in its two matrix indices. -/
theorem dJet2_swap23 (g : Submission.Diff.SMet I M) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) (m k i j : Fin (Module.finrank ℝ E)) :
    dJet2 g x₀ y m k i j = dJet2 g x₀ y m k j i := by
  have hΦ : ContDiffAt ℝ 2 (chartMatFun g x₀) y :=
    (contDiffAt_chartMatFun (I := I) g x₀ hy).of_le (by norm_num)
  show ((fderiv ℝ (fun x : E => fderiv ℝ (chartMatFun g x₀) x) y (Module.finBasis ℝ E m))
      (Module.finBasis ℝ E k)) i j
    = ((fderiv ℝ (fun x : E => fderiv ℝ (chartMatFun g x₀) x) y (Module.finBasis ℝ E m))
      (Module.finBasis ℝ E k)) j i
  rw [← fderiv_fderiv_apply_coord (Φ := chartMatFun g x₀) (hΦ := hΦ)
      (v := Module.finBasis ℝ E k) (w := Module.finBasis ℝ E m) i j,
    ← fderiv_fderiv_apply_coord (Φ := chartMatFun g x₀) (hΦ := hΦ)
      (v := Module.finBasis ℝ E k) (w := Module.finBasis ℝ E m) j i]
  have hev : (fun x : E => (fderiv ℝ (chartMatFun g x₀) x (Module.finBasis ℝ E k)) i j)
      =ᶠ[𝓝 y] (fun x : E => (fderiv ℝ (chartMatFun g x₀) x (Module.finBasis ℝ E k)) j i) := by
    filter_upwards [hΦ.eventually (by simp)] with x hx
    exact fderiv_eval_coord_swap (hx.differentiableAt (by simp))
      (fun y' i j => chartMatFun_swap g x₀ y' i j) (Module.finBasis ℝ E k) i j
  rw [Filter.EventuallyEq.fderiv_eq hev]

/-- The jet Koszul pairing is symmetric in its first two slots. -/
theorem jKz_swap12 (g : Submission.Diff.SMet I M) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) (a b c : Fin (Module.finrank ℝ E)) :
    jKz (fderiv ℝ (chartMatFun g x₀) y) a b c
      = jKz (fderiv ℝ (chartMatFun g x₀) y) b a c := by
  have h2 : (fderiv ℝ (chartMatFun g x₀) y (bB (E := E) c)) a b
      = (fderiv ℝ (chartMatFun g x₀) y (bB (E := E) c)) b a := by
    show (dJet1 g x₀ y c) a b = (dJet1 g x₀ y c) b a
    exact dJet1_swap (I := I) g x₀ hy c a b
  simp only [jKz]
  rw [h2]
  ring

/-- The jet Koszul derivative is symmetric in its second and third slots. -/
theorem jKzD_swap23 (g : Submission.Diff.SMet I M) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) (m a b c : Fin (Module.finrank ℝ E)) :
    jKzD (fderiv ℝ (fderiv ℝ (chartMatFun g x₀)) y) m a b c
      = jKzD (fderiv ℝ (fderiv ℝ (chartMatFun g x₀)) y) m b a c := by
  have h2 : (fderiv ℝ (fderiv ℝ (chartMatFun g x₀)) y (bB (E := E) m) (bB (E := E) c)) a b
      = (fderiv ℝ (fderiv ℝ (chartMatFun g x₀)) y (bB (E := E) m) (bB (E := E) c)) b a := by
    show (dJet2 g x₀ y m c) a b = (dJet2 g x₀ y m c) b a
    exact dJet2_swap23 (I := I) g x₀ hy m c a b
  simp only [jKzD]
  rw [h2]
  ring

/-- **`sRm` is `jRm`**: the two expressions differ only by the order of the indices. -/
theorem sRm_eq_jRm_jet (g : Submission.Diff.SMet I M) (x₀ : M) {p : M}
    (hp : p ∈ (chartAt H' x₀).source) (a b c d : Fin (Module.finrank ℝ E)) :
    sRm (dJet0 g x₀ ((extChartAt I x₀) p)) (dJet1 g x₀ ((extChartAt I x₀) p))
        (dJet2 g x₀ ((extChartAt I x₀) p)) a b c d
      = jRm (chartMatFun g x₀ ((extChartAt I x₀) p))
          (fderiv ℝ (chartMatFun g x₀) ((extChartAt I x₀) p))
          (fderiv ℝ (fderiv ℝ (chartMatFun g x₀)) ((extChartAt I x₀) p)) a b c d := by
  have hy : (extChartAt I x₀) p ∈ (extChartAt I x₀).target :=
    (extChartAt I x₀).map_source (by rwa [extChartAt_source])
  have h1 : sKzD (dJet2 g x₀ ((extChartAt I x₀) p)) a b d c
      = jKzD (fderiv ℝ (fderiv ℝ (chartMatFun g x₀)) ((extChartAt I x₀) p)) a d b c := by
    rw [show sKzD (dJet2 g x₀ ((extChartAt I x₀) p)) a b d c
        = jKzD (fderiv ℝ (fderiv ℝ (chartMatFun g x₀)) ((extChartAt I x₀) p)) a b d c
        from rfl,
      jKzD_swap23 (I := I) g x₀ hy a b d c]
  have h2 : sKzD (dJet2 g x₀ ((extChartAt I x₀) p)) b a d c
      = jKzD (fderiv ℝ (fderiv ℝ (chartMatFun g x₀)) ((extChartAt I x₀) p)) b d a c := by
    rw [show sKzD (dJet2 g x₀ ((extChartAt I x₀) p)) b a d c
        = jKzD (fderiv ℝ (fderiv ℝ (chartMatFun g x₀)) ((extChartAt I x₀) p)) b a d c
        from rfl,
      jKzD_swap23 (I := I) g x₀ hy b a d c]
  have h3 : (∑ m : Fin (Module.finrank ℝ E), ∑ n : Fin (Module.finrank ℝ E),
        sInv (dJet0 g x₀ ((extChartAt I x₀) p)) m n
          * sKz (dJet1 g x₀ ((extChartAt I x₀) p)) b d m
          * sKz (dJet1 g x₀ ((extChartAt I x₀) p)) a c n)
      = (∑ m : Fin (Module.finrank ℝ E), ∑ n : Fin (Module.finrank ℝ E),
        jInv (chartMatFun g x₀ ((extChartAt I x₀) p)) m n
          * jKz (fderiv ℝ (chartMatFun g x₀) ((extChartAt I x₀) p)) d b m
          * jKz (fderiv ℝ (chartMatFun g x₀) ((extChartAt I x₀) p)) a c n) := by
    refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun n _ => ?_))
    rw [show sInv (dJet0 g x₀ ((extChartAt I x₀) p)) m n
        = jInv (chartMatFun g x₀ ((extChartAt I x₀) p)) m n from rfl,
      show sKz (dJet1 g x₀ ((extChartAt I x₀) p)) b d m
        = jKz (fderiv ℝ (chartMatFun g x₀) ((extChartAt I x₀) p)) b d m from rfl,
      show sKz (dJet1 g x₀ ((extChartAt I x₀) p)) a c n
        = jKz (fderiv ℝ (chartMatFun g x₀) ((extChartAt I x₀) p)) a c n from rfl,
      jKz_swap12 (I := I) g x₀ hy b d m]
  have h4 : (∑ m : Fin (Module.finrank ℝ E), ∑ n : Fin (Module.finrank ℝ E),
        sInv (dJet0 g x₀ ((extChartAt I x₀) p)) m n
          * sKz (dJet1 g x₀ ((extChartAt I x₀) p)) a d m
          * sKz (dJet1 g x₀ ((extChartAt I x₀) p)) b c n)
      = (∑ m : Fin (Module.finrank ℝ E), ∑ n : Fin (Module.finrank ℝ E),
        jInv (chartMatFun g x₀ ((extChartAt I x₀) p)) m n
          * jKz (fderiv ℝ (chartMatFun g x₀) ((extChartAt I x₀) p)) d a m
          * jKz (fderiv ℝ (chartMatFun g x₀) ((extChartAt I x₀) p)) b c n) := by
    refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun n _ => ?_))
    rw [show sInv (dJet0 g x₀ ((extChartAt I x₀) p)) m n
        = jInv (chartMatFun g x₀ ((extChartAt I x₀) p)) m n from rfl,
      show sKz (dJet1 g x₀ ((extChartAt I x₀) p)) a d m
        = jKz (fderiv ℝ (chartMatFun g x₀) ((extChartAt I x₀) p)) a d m from rfl,
      show sKz (dJet1 g x₀ ((extChartAt I x₀) p)) b c n
        = jKz (fderiv ℝ (chartMatFun g x₀) ((extChartAt I x₀) p)) b c n from rfl,
      jKz_swap12 (I := I) g x₀ hy a d m]
  rw [show sRm (dJet0 g x₀ ((extChartAt I x₀) p)) (dJet1 g x₀ ((extChartAt I x₀) p))
        (dJet2 g x₀ ((extChartAt I x₀) p)) a b c d
      = sKzD (dJet2 g x₀ ((extChartAt I x₀) p)) a b d c
        - sKzD (dJet2 g x₀ ((extChartAt I x₀) p)) b a d c
        - (∑ m : Fin (Module.finrank ℝ E), ∑ n : Fin (Module.finrank ℝ E),
            sInv (dJet0 g x₀ ((extChartAt I x₀) p)) m n
              * sKz (dJet1 g x₀ ((extChartAt I x₀) p)) b d m
              * sKz (dJet1 g x₀ ((extChartAt I x₀) p)) a c n)
        + (∑ m : Fin (Module.finrank ℝ E), ∑ n : Fin (Module.finrank ℝ E),
            sInv (dJet0 g x₀ ((extChartAt I x₀) p)) m n
              * sKz (dJet1 g x₀ ((extChartAt I x₀) p)) a d m
              * sKz (dJet1 g x₀ ((extChartAt I x₀) p)) b c n) from rfl,
    show jRm (chartMatFun g x₀ ((extChartAt I x₀) p))
        (fderiv ℝ (chartMatFun g x₀) ((extChartAt I x₀) p))
        (fderiv ℝ (fderiv ℝ (chartMatFun g x₀)) ((extChartAt I x₀) p)) a b c d
      = jKzD (fderiv ℝ (fderiv ℝ (chartMatFun g x₀)) ((extChartAt I x₀) p)) a d b c
        - jKzD (fderiv ℝ (fderiv ℝ (chartMatFun g x₀)) ((extChartAt I x₀) p)) b d a c
        - (∑ m : Fin (Module.finrank ℝ E), ∑ n : Fin (Module.finrank ℝ E),
            jInv (chartMatFun g x₀ ((extChartAt I x₀) p)) m n
              * jKz (fderiv ℝ (chartMatFun g x₀) ((extChartAt I x₀) p)) d b m
              * jKz (fderiv ℝ (chartMatFun g x₀) ((extChartAt I x₀) p)) a c n)
        + (∑ m : Fin (Module.finrank ℝ E), ∑ n : Fin (Module.finrank ℝ E),
            jInv (chartMatFun g x₀ ((extChartAt I x₀) p)) m n
              * jKz (fderiv ℝ (chartMatFun g x₀) ((extChartAt I x₀) p)) d a m
              * jKz (fderiv ℝ (chartMatFun g x₀) ((extChartAt I x₀) p)) b c n) from rfl,
    h1, h2, h3, h4]

/-! ## The target -/

/-- **The curvature component in the chart frame is the scalar jet expression.** -/
theorem gRmC_eq_jRm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (g : Submission.Diff.SMet I M)
    (hcov : CovariantDerivative.ContMDiffCovariantDerivative (Submission.Diff.lcOf g) (⊤ : ℕ∞))
    (x₀ : M) {p : M} (hp : p ∈ (chartAt H' x₀).source) (a b c d : Fin (Module.finrank ℝ E)) :
    Work.Diff.EXT.gRmC (I := I) g x₀ p a b c d
      = Work.Diff.EXT.jRm (Work.Diff.EXT.chartMatFun g x₀ ((extChartAt I x₀) p))
          (fderiv ℝ (Work.Diff.EXT.chartMatFun g x₀) ((extChartAt I x₀) p))
          (fderiv ℝ (fderiv ℝ (Work.Diff.EXT.chartMatFun g x₀)) ((extChartAt I x₀) p))
          a b c d := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  haveI : ContMDiffCovariantDerivative (Submission.Diff.lcOf g) ∞ := hcov
  have hy : (extChartAt I x₀) p ∈ (extChartAt I x₀).target :=
    (extChartAt I x₀).map_source (by rwa [extChartAt_source])
  have hsymm : (extChartAt I x₀).symm ((extChartAt I x₀) p) = p :=
    (extChartAt I x₀).left_inv (by rwa [extChartAt_source])
  have hmid : Work.Diff.GE.rmChartExpr (I := I) (fun _ : ℝ => g) x₀ a b c d 0 p
      = sRm (dJet0 g x₀ ((extChartAt I x₀) p)) (dJet1 g x₀ ((extChartAt I x₀) p))
          (dJet2 g x₀ ((extChartAt I x₀) p)) a b c d := by
    conv_lhs => rw [← hsymm]
    exact rmChartExpr_eq_sRm (I := I) g x₀ hy a b c d
  rw [gRmC_eq_cRm (I := I) g x₀ hp a b c d,
    cRm_eq_rmChartExpr (I := I) g hcov x₀ hp a b c d,
    hmid, sRm_eq_jRm_jet (I := I) g x₀ hp a b c d]

end Assembly

end Work.Diff.EXT
