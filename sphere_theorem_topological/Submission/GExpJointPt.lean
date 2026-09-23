import Submission.GExpFlow
import Submission.GExpJoint
import Submission.GExpBoundary
import Submission.GExpRay2
import Submission.LiftUniform
import Submission.InjSup
import Submission.UniformInj
import Submission.ConjEnergy
import Submission.ChartBounds
import Submission.Length
import Submission.GExpVelocity
import Submission.LensLoop
import Submission.ChartStateTrans
import Submission.Roadmap

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.GExpFlow
open Submission.ChartBounds
open Submission.ChartConnection
open Submission.InjRadius
open Submission.GExpJoint

namespace Submission.GExpJointPt

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

open scoped Classical in
/-- Small extended distances imply topological convergence. -/
theorem tendsto_of_eventually_edist_lt [RegularSpace M] {x : M} {l : Filter ℕ} {f : ℕ → M}
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in l, Manifold.riemannianEDist I x (f n) < ENNReal.ofReal ε) :
    Tendsto f l (𝓝 x) := by
  haveI hcb : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  rw [Filter.tendsto_iff_forall_eventually_mem]
  intro s hs
  obtain ⟨c, hc, hcs⟩ := Submission.EDist.setOf_riemannianEDist_lt_subset_nhds (I := I) hs
  set c' : ℝ≥0∞ := min c 1 with hc'def
  have hc'pos : 0 < c' := lt_min hc (by norm_num)
  have hc'lt : c' < ⊤ := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hsub : {y : M | Manifold.riemannianEDist I x y < c'} ⊆ s := fun y hy =>
    hcs (lt_of_lt_of_le (show Manifold.riemannianEDist I x y < c' from hy) (min_le_left _ _))
  have hpos : 0 < c'.toReal := ENNReal.toReal_pos (ne_of_gt hc'pos) (ne_of_lt hc'lt)
  filter_upwards [h c'.toReal hpos] with n hn
  refine hsub ?_
  show Manifold.riemannianEDist I x (f n) < c'
  rw [ENNReal.ofReal_toReal (ne_of_lt hc'lt)] at hn
  exact hn

/-- **The velocity is determined by the positions at two nearby parameters.** -/
theorem tendsto_coord_velocity
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {z₀ : M} {Z : Set M} (hZsrc : Z ⊆ (chartAt H z₀).source) (hZc : IsCompact Z)
    (D : ChartFlowData (cov := cov) (I := I) z₀ Z)
    {η m : ℝ} (hηc : η ≤ 1 / (2 * flowScale D))
    (hinj : ∀ q ∈ Z, InjAtLeast hmet q m)
    (hnorm : ∀ q ∈ Z, ∀ u ∈ Metric.closedBall (0 : E) η, ‖frameVector (I := I) z₀ q u‖ < m)
    {xn : ℕ → M} {x : M} (hx : Tendsto xn atTop (𝓝 x))
    (hxnZ : ∀ᶠ n in atTop, xn n ∈ Z) (hxZ : x ∈ Z)
    {yn : ℕ → M} {y : M} (hy : Tendsto yn atTop (𝓝 y))
    {un : ℕ → E} {u : E} (huη : ∀ᶠ n in atTop, un n ∈ Metric.closedBall (0 : E) η)
    (huη' : u ∈ Metric.closedBall (0 : E) η)
    (heqn : ∀ᶠ n in atTop,
      GExp (cov := cov) hmet (xn n) (frameVector (I := I) z₀ (xn n) (un n)) = yn n)
    (heq : GExp (cov := cov) hmet x (frameVector (I := I) z₀ x u) = y) :
    Tendsto un atTop (𝓝 u) := by
  classical
  haveI hcb : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδpos, hδspec⟩ :=
    Submission.LiftUniform.exists_pos_joint_frameVector_edist_lt_imp_norm_sub_lt
      (cov := cov) hmet htor D hZsrc hZc hηc hinj hnorm hε
  have hcont : ContinuousAt (fun q : M => (extChartAt I z₀) q) x := by
    have hsrc : x ∈ (extChartAt I z₀).source := by simpa using hZsrc hxZ
    have hopen : (chartAt H z₀).source ∈ 𝓝 x :=
      (chartAt H z₀).open_source.mem_nhds (by simpa using hsrc)
    exact ((contMDiffOn_extChartAt (I := I) (x := z₀) (n := ∞)).continuousOn.continuousAt hopen)
  have hcoord : ∀ᶠ n in atTop,
      ‖(extChartAt I z₀) (xn n) - (extChartAt I z₀) x‖ < δ := by
    have h := hcont.tendsto.comp hx
    have h2 : ∀ᶠ n in atTop,
        (extChartAt I z₀) (xn n) ∈ Metric.ball ((extChartAt I z₀) x) δ :=
      h (Metric.ball_mem_nhds _ hδpos)
    filter_upwards [h2] with n hn
    simpa [Metric.mem_ball, dist_eq_norm] using hn
  have himg : ∀ᶠ n in atTop,
      Manifold.riemannianEDist I
        (GExp (cov := cov) hmet (xn n) (frameVector (I := I) z₀ (xn n) (un n)))
        (GExp (cov := cov) hmet x (frameVector (I := I) z₀ x u)) < ENNReal.ofReal δ := by
    have hmem : {p : M | Manifold.riemannianEDist I y p < ENNReal.ofReal δ} ∈ 𝓝 y :=
      eventually_riemannianEDist_lt (I := I) y (ENNReal.ofReal_pos.mpr hδpos)
    have h2 : ∀ᶠ n in atTop, Manifold.riemannianEDist I (yn n) y < ENNReal.ofReal δ := by
      filter_upwards [hy hmem] with n hn
      have hn' : Manifold.riemannianEDist I y (yn n) < ENNReal.ofReal δ := hn
      rwa [Manifold.riemannianEDist_comm] at hn'
    filter_upwards [h2, heqn] with n hn he
    rw [he, heq]
    exact hn
  have hfin : ∀ᶠ n in atTop, ‖un n - u‖ < ε := by
    filter_upwards [hxnZ, hcoord, himg, huη] with n hnZ hnc hni hun
    exact hδspec (xn n) hnZ x hxZ (un n) hun u huη' hnc hni
  simpa [dist_eq_norm] using (Filter.eventually_atTop.mp hfin)


/-! ## The chart-flow window step -/

/-- **Position convergence propagates across a chart-flow window.** -/
theorem tendsto_ray_window
    (hmet : IsMetricCompatible cov)
    {z₀ : M} {Z : Set M} (hZsrc : Z ⊆ (chartAt H z₀).source)
    (D : ChartFlowData (cov := cov) (I := I) z₀ Z)
    {σn : ℕ → ℝ → M} {σ : ℝ → M}
    {qn : ℕ → M} {q : M} (hq : Tendsto qn atTop (𝓝 q)) (hqZ : ∀ᶠ n in atTop, qn n ∈ Z)
    (hqZ' : q ∈ Z)
    {s₀ s₁ : ℝ} (hs : s₀ ≤ s₁)
    {an : ℕ → E} {a : E} (ha : Tendsto an atTop (𝓝 a)) (ha0 : a ≠ 0)
    (hrep : ∀ t ∈ Icc s₀ s₁, ∀ᶠ n in atTop, σn n t = GExp (cov := cov) hmet (qn n)
              (frameVector (I := I) z₀ (qn n) ((t - s₀) • an n)))
    (hrep0 : ∀ t ∈ Icc s₀ s₁, σ t = GExp (cov := cov) hmet q
              (frameVector (I := I) z₀ q ((t - s₀) • a)))
    (hph : (((extChartAt I z₀) q), flowScale D • ((s₁ - s₀) • a)) ∈ chartData (I := I) z₀ Z) :
    ∀ t ∈ Icc s₀ s₁, Tendsto (fun n => σn n t) atTop (𝓝 (σ t)) := by
  classical
  set c : ℝ := flowScale D with hcdef
  have hcpos : 0 < c := flowScale_pos D
  have hclt : |c⁻¹| < D.ρ := by
    rw [inv_flowScale, abs_of_pos (div_pos D.hρ two_pos)]
    linarith [D.hρ]
  have hD0 : 0 ≤ s₁ - s₀ := by linarith
  have hqsrc : q ∈ (extChartAt I z₀).source := by simpa using hZsrc hqZ'
  have hqP : (((extChartAt I z₀) q, c • ((s₁ - s₀) • a)) ∈ chartData (I := I) z₀ Z) := hph
  have hPnorm : (s₁ - s₀) * (c * ‖a‖) ≤ 1 := by
    have h3 : ‖c • ((s₁ - s₀) • a)‖ = (s₁ - s₀) * (c * ‖a‖) := by
      rw [smul_smul, norm_smul, Real.norm_of_nonneg (mul_nonneg hcpos.le hD0)]
      ring
    have h := hqP.2
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, h3] at h
    exact h
  have hanorm : ∀ δ : ℝ, 0 ≤ δ → δ ≤ s₁ - s₀ → ‖c • (δ • a)‖ ≤ 1 := by
    intro δ hδ hδle
    have h1 : ‖c • (δ • a)‖ = δ * (c * ‖a‖) := by
      rw [smul_smul, norm_smul, Real.norm_of_nonneg (mul_nonneg hcpos.le hδ)]
      ring
    rw [h1]
    calc δ * (c * ‖a‖) ≤ (s₁ - s₀) * (c * ‖a‖) :=
          mul_le_mul_of_nonneg_right hδle (mul_nonneg hcpos.le (norm_nonneg _))
      _ ≤ 1 := hPnorm
  have hevne : ∀ᶠ n in atTop, an n ≠ 0 := ha.eventually (isOpen_ne.mem_nhds ha0)
  intro t htI
  rcases eq_or_lt_of_le htI.1 with ht0 | ht0
  · -- the left endpoint
    have h1 : (fun n : ℕ => σn n t) =ᶠ[atTop] qn := by
      filter_upwards [hrep t htI] with n hn
      rw [hn, ← ht0, sub_self, zero_smul, Submission.ChartBounds.frameVector_zero', GExp_zero]
    have h2 : σ t = q := by
      rw [hrep0 t htI, ← ht0, sub_self, zero_smul, Submission.ChartBounds.frameVector_zero',
        GExp_zero]
    rw [h2]
    exact Filter.Tendsto.congr' h1.symm hq
  · -- the interior of the window
    have hδpos : 0 < t - s₀ := sub_pos.mpr ht0
    have hδle : t - s₀ ≤ s₁ - s₀ := by linarith [htI.2]
    have hPmem : (((extChartAt I z₀) q, c • ((t - s₀) • a)) ∈ chartData (I := I) z₀ Z) := by
      refine ⟨hqP.1, ?_⟩
      have h := hanorm (t - s₀) (le_of_lt hδpos) hδle
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      exact h
    have hPO : ((extChartAt I z₀) q, c • ((t - s₀) • a)) ∈ D.O := D.hKO hPmem
    have hPn : Tendsto (fun n => ((extChartAt I z₀) (qn n), c • ((t - s₀) • an n))) atTop
        (𝓝 ((extChartAt I z₀) q, c • ((t - s₀) • a))) := by
      have hcoord : Tendsto (fun n => (extChartAt I z₀) (qn n)) atTop
          (𝓝 ((extChartAt I z₀) q)) := by
        have hcont : ContinuousAt (fun p : M => (extChartAt I z₀) p) q :=
          ((contMDiffOn_extChartAt (I := I) (x := z₀) (n := ∞)).continuousOn.continuousAt
            ((chartAt H z₀).open_source.mem_nhds (by simpa using hqsrc)))
        exact hcont.tendsto.comp hq
      have h1 : Tendsto (fun n => c • ((t - s₀) • an n)) atTop (𝓝 (c • ((t - s₀) • a))) :=
        tendsto_const_nhds.smul (tendsto_const_nhds.smul ha)
      exact (Prod.tendsto_iff (fun n => ((extChartAt I z₀) (qn n), c • ((t - s₀) • an n)))
        ((extChartAt I z₀) q, c • ((t - s₀) • a))).mpr ⟨hcoord, h1⟩
    have hevO : ∀ᶠ n in atTop,
        ((extChartAt I z₀) (qn n), c • ((t - s₀) • an n)) ∈ D.O :=
      hPn (D.hO.mem_nhds hPO)
    have hflow : Tendsto (fun n => D.α ((extChartAt I z₀) (qn n), c • ((t - s₀) • an n)) c⁻¹)
        atTop (𝓝 (D.α ((extChartAt I z₀) q, c • ((t - s₀) • a)) c⁻¹)) := by
      have hcont : ContinuousAt (fun p : (E × E) × ℝ => D.α p.1 p.2)
          (((extChartAt I z₀) q, c • ((t - s₀) • a)), c⁻¹) :=
        (D.hjoint _ (by simpa [hcdef] using hPmem) c⁻¹
          (by simpa [hcdef] using hclt)).continuousAt
      have h := hcont.tendsto.comp ((Prod.tendsto_iff
        (fun n => (((extChartAt I z₀) (qn n), c • ((t - s₀) • an n)), c⁻¹))
        (((extChartAt I z₀) q, c • ((t - s₀) • a)), c⁻¹)).mpr ⟨hPn, tendsto_const_nhds⟩)
      simpa only [Function.comp_def] using h
    have hflowfst : Tendsto
        (fun n => (D.α ((extChartAt I z₀) (qn n), c • ((t - s₀) • an n)) c⁻¹).1) atTop
        (𝓝 ((D.α ((extChartAt I z₀) q, c • ((t - s₀) • a)) c⁻¹).1)) :=
      (continuous_fst.tendsto _).comp hflow
    have hsn : σ t = (extChartAt I z₀).symm
        ((D.α ((extChartAt I z₀) q, c • ((t - s₀) • a)) c⁻¹).1) := by
      rw [hrep0 t htI]
      exact Submission.GExpFlow.GExp_eq_chartFlow (cov := cov) hmet D hqsrc ((t - s₀) • a)
        (by simpa [hcdef] using hPO) (smul_ne_zero hδpos.ne' ha0)
    have hPtgt : (D.α ((extChartAt I z₀) q, c • ((t - s₀) • a)) c⁻¹).1 ∈
        (extChartAt I z₀).target :=
      D.htgt _ hPO c⁻¹ (le_of_lt (by simpa [hcdef] using hclt))
    have hsymm : ContinuousAt (fun y : E => (extChartAt I z₀).symm y)
        ((D.α ((extChartAt I z₀) q, c • ((t - s₀) • a)) c⁻¹).1) :=
      ((contMDiffOn_extChartAt_symm (I := I) (n := ∞) z₀).contMDiffAt
        ((isOpen_extChartAt_target z₀).mem_nhds hPtgt)).continuousAt
    have hevrep : (fun n : ℕ => σn n t) =ᶠ[atTop]
        (fun n => (extChartAt I z₀).symm
          ((D.α ((extChartAt I z₀) (qn n), c • ((t - s₀) • an n)) c⁻¹).1)) := by
      filter_upwards [hrep t htI, hqZ, hevO, hevne] with n hrepn hnZ hnO hne
      have hsrc : qn n ∈ (extChartAt I z₀).source := by simpa using hZsrc hnZ
      rw [hrepn]
      exact Submission.GExpFlow.GExp_eq_chartFlow (cov := cov) hmet D hsrc ((t - s₀) • an n)
        (by simpa [hcdef] using hnO) (smul_ne_zero hδpos.ne' hne)
    rw [hsn]
    exact Filter.Tendsto.congr' hevrep.symm (hsymm.tendsto.comp hflowfst)


/-! ## The rays, their semigroup law, and the chart frame -/

/-- The `n`-th ray of the sequence, at parameter `t`. -/
noncomputable abbrev raySeq (hmet : IsMetricCompatible cov) (z₀ : M) (q : ℕ → M) (y : ℕ → E)
    (t : ℝ) (n : ℕ) : M :=
  GExp (cov := cov) hmet (q n) (t • frameVector (I := I) z₀ (q n) (y n))

/-- The limit ray, at parameter `t`. -/
noncomputable abbrev rayLim (hmet : IsMetricCompatible cov) (z₀ : M) (p : M) (y₀ : E)
    (t : ℝ) : M :=
  GExp (cov := cov) hmet p (t • frameVector (I := I) z₀ p y₀)

/-- The chart coordinates of the velocity of the `n`-th ray at parameter `s`. -/
noncomputable abbrev velCoords (hmet : IsMetricCompatible cov) (z₀ : M) (q : ℕ → M) (y : ℕ → E)
    (z : M) (s : ℝ) (n : ℕ) : E :=
  (Trivialization.continuousLinearMapAt ℝ (trivializationAt E (TangentSpace I) z)
      (raySeq (cov := cov) hmet z₀ q y s n))
    (curveVelocity (I := I) (fun r : ℝ => raySeq (cov := cov) hmet z₀ q y r n) s)

/-- The chart coordinates of the velocity of the limit ray at parameter `s`. -/
noncomputable abbrev velCoordsLim (hmet : IsMetricCompatible cov) (z₀ : M) (p : M) (y₀ : E)
    (z : M) (s : ℝ) : E :=
  (Trivialization.continuousLinearMapAt ℝ (trivializationAt E (TangentSpace I) z)
      (rayLim (cov := cov) hmet z₀ p y₀ s))
    (curveVelocity (I := I) (rayLim (cov := cov) hmet z₀ p y₀) s)

variable {hmet : IsMetricCompatible cov} {z₀ : M} {q : ℕ → M} {y : ℕ → E} {p : M} {y₀ : E}

lemma raySeq_zero (n : ℕ) : raySeq (cov := cov) hmet z₀ q y 0 n = q n := by
  rw [raySeq, zero_smul, GExp_zero]

lemma rayLim_zero : rayLim (cov := cov) hmet z₀ p y₀ 0 = p := by
  rw [rayLim, zero_smul, GExp_zero]

/-- Unit-speed directions have non-vanishing vectors. -/
lemma frameVector_ne_zero_of_norm {z : M} {r : M} {a : E} (h : ‖frameVector (I := I) z r a‖ = 1) :
    frameVector (I := I) z r a ≠ 0 := by
  intro h0; rw [h0, norm_zero] at h; exact absurd h.symm one_ne_zero

lemma raySeq_semigroup (hunit : ∀ n, ‖frameVector (I := I) z₀ (q n) (y n)‖ = 1)
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (n : ℕ) :
    raySeq (cov := cov) hmet z₀ q y t n
      = GExp (cov := cov) hmet (raySeq (cov := cov) hmet z₀ q y s n)
          ((t - s) • curveVelocity (I := I) (fun r : ℝ => raySeq (cov := cov) hmet z₀ q y r n) s) := by
  have h := Submission.GExpGlob.GExp_add_smul (cov := cov) hmet (p := q n) (hunit n)
    (s := s) (t := t - s) hs (by linarith)
  have hsum : s + (t - s) = t := by ring
  rw [hsum] at h
  simpa only [raySeq] using h

/-- The step law in the form used by the chart-flow window: the displacement is the (scaled)
coordinate velocity. -/
lemma raySeq_step (hunit : ∀ n, ‖frameVector (I := I) z₀ (q n) (y n)‖ = 1) {z : M}
    {s₀ s : ℝ} (hs : 0 < s₀) (hst : s₀ ≤ s) (n : ℕ)
    (hsrc : raySeq (cov := cov) hmet z₀ q y s₀ n ∈ (extChartAt I z).source) :
    raySeq (cov := cov) hmet z₀ q y s n
      = GExp (cov := cov) hmet (raySeq (cov := cov) hmet z₀ q y s₀ n)
          (frameVector (I := I) z (raySeq (cov := cov) hmet z₀ q y s₀ n)
            ((s - s₀) • velCoords (cov := cov) hmet z₀ q y z s₀ n)) := by
  rw [raySeq_semigroup (cov := cov) hunit hs hst n, frameVector_smul,
    Submission.GExpFlow.frameVector_clm (I := I) hsrc
      (curveVelocity (I := I) (fun r : ℝ => raySeq (cov := cov) hmet z₀ q y r n) s₀)]

lemma rayLim_step (hu₀ : ‖frameVector (I := I) z₀ p y₀‖ = 1) {z : M}
    {s₀ s : ℝ} (hs : 0 < s₀) (hst : s₀ ≤ s)
    (hsrc : rayLim (cov := cov) hmet z₀ p y₀ s₀ ∈ (extChartAt I z).source) :
    rayLim (cov := cov) hmet z₀ p y₀ s
      = GExp (cov := cov) hmet (rayLim (cov := cov) hmet z₀ p y₀ s₀)
          (frameVector (I := I) z (rayLim (cov := cov) hmet z₀ p y₀ s₀)
            ((s - s₀) • velCoordsLim (cov := cov) hmet z₀ p y₀ z s₀)) := by
  have h := Submission.GExpGlob.GExp_add_smul (cov := cov) hmet (p := p) hu₀ (s := s₀)
    (t := s - s₀) hs (by linarith)
  have hsum : s₀ + (s - s₀) = s := by ring
  rw [hsum] at h
  change GExp (cov := cov) hmet p (s • frameVector (I := I) z₀ p y₀)
    = GExp (cov := cov) hmet (rayLim (cov := cov) hmet z₀ p y₀ s₀)
      (frameVector (I := I) z (rayLim (cov := cov) hmet z₀ p y₀ s₀)
        ((s - s₀) • velCoordsLim (cov := cov) hmet z₀ p y₀ z s₀))
  rw [h, frameVector_smul,
    Submission.GExpFlow.frameVector_clm (I := I) hsrc
      (curveVelocity (I := I) (rayLim (cov := cov) hmet z₀ p y₀) s₀)]

/-- The velocity of a unit ray is non-vanishing. -/
lemma curveVelocity_raySeq_ne (hunit : ∀ n, ‖frameVector (I := I) z₀ (q n) (y n)‖ = 1)
    {s : ℝ} (hs : s ≠ 0) (n : ℕ) :
    curveVelocity (I := I) (fun r : ℝ => raySeq (cov := cov) hmet z₀ q y r n) s ≠ 0 := by
  have hv : frameVector (I := I) z₀ (q n) (y n) ≠ 0 := frameVector_ne_zero_of_norm (hunit n)
  have h := Submission.LensLoop.norm_curveVelocity_GExp_smul_ne (cov := cov) hmet (q n) hv hs
  intro h0
  rw [h0, norm_zero, hunit n] at h
  exact one_ne_zero h.symm

lemma curveVelocity_rayLim_ne (hu₀ : ‖frameVector (I := I) z₀ p y₀‖ = 1) {s : ℝ} (hs : s ≠ 0) :
    curveVelocity (I := I) (rayLim (cov := cov) hmet z₀ p y₀) s ≠ 0 := by
  have hv : frameVector (I := I) z₀ p y₀ ≠ 0 := frameVector_ne_zero_of_norm hu₀
  have h := Submission.LensLoop.norm_curveVelocity_GExp_smul_ne (cov := cov) hmet p hv hs
  intro h0
  rw [h0, norm_zero, hu₀] at h
  exact one_ne_zero h.symm

/-- The velocity of a unit ray is unit. -/
lemma norm_curveVelocity_raySeq (hunit : ∀ n, ‖frameVector (I := I) z₀ (q n) (y n)‖ = 1)
    {s : ℝ} (hs : s ≠ 0) (n : ℕ) :
    ‖curveVelocity (I := I) (fun r : ℝ => raySeq (cov := cov) hmet z₀ q y r n) s‖ = 1 := by
  have hv : frameVector (I := I) z₀ (q n) (y n) ≠ 0 := frameVector_ne_zero_of_norm (hunit n)
  have h := Submission.LensLoop.norm_curveVelocity_GExp_smul_ne (cov := cov) hmet (q n) hv hs
  simpa only [hunit n] using h

lemma norm_curveVelocity_rayLim (hu₀ : ‖frameVector (I := I) z₀ p y₀‖ = 1)
    {s : ℝ} (hs : s ≠ 0) :
    ‖curveVelocity (I := I) (rayLim (cov := cov) hmet z₀ p y₀) s‖ = 1 := by
  have hv : frameVector (I := I) z₀ p y₀ ≠ 0 := frameVector_ne_zero_of_norm hu₀
  have h := Submission.LensLoop.norm_curveVelocity_GExp_smul_ne (cov := cov) hmet p hv hs
  simpa only [hu₀] using h

/-- The limit ray is continuous. -/
lemma continuous_rayLim (hu₀ : ‖frameVector (I := I) z₀ p y₀‖ = 1) :
    Continuous (rayLim (cov := cov) hmet z₀ p y₀) := by
  have hv : frameVector (I := I) z₀ p y₀ ≠ 0 := frameVector_ne_zero_of_norm hu₀
  have h : Continuous (fun s : ℝ => GExp (cov := cov) hmet p
      (s • frameVector (I := I) z₀ p y₀)) :=
    (Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet p hv).continuous
  exact h

/-- The (exponentials of) the rays of a chart around a point. -/
structure ChartFrame (cov : CovariantDerivative I E (TangentSpace I (M := M))) (z p : M) where
  x : E
  hx : x = (extChartAt I z) p
  η : ℝ
  hη : 0 < η
  hball : Metric.closedBall x η ⊆ (extChartAt I z).target
  Z : Set M
  hZeq : Z = (extChartAt I z).symm '' Metric.closedBall x η
  hZc : IsCompact Z
  hZsrc : Z ⊆ (chartAt H z).source
  D : ChartFlowData (cov := cov) (I := I) z Z
  lam : ℝ
  hlam : 0 < lam
  Lam : ℝ
  hLam : 0 < Lam
  hbnd : ∀ r ∈ Z, ∀ a : E, lam * ‖a‖ ^ 2 ≤ chartGram (I := I) z r a a ∧
    chartGram (I := I) z r a a ≤ Lam * ‖a‖ ^ 2

variable {z p : M}

theorem ChartFrame.mem_of_norm {F : ChartFrame cov z p} {r : M}
    (hsrc : r ∈ (chartAt H z).source)
    (h : ‖(extChartAt I z) r - F.x‖ < F.η) : r ∈ F.Z := by
  rw [F.hZeq]
  refine ⟨(extChartAt I z) r, ?_, ?_⟩
  · rw [Metric.mem_closedBall, dist_eq_norm]
    exact le_of_lt h
  · have hsrc' : r ∈ (extChartAt I z).source := by
      simpa only [extChartAt_source (I := I) z] using hsrc
    exact (extChartAt I z).left_inv hsrc'

theorem ChartFrame.nhds_of_strict {F : ChartFrame cov z p} {r : M}
    (hsrc : r ∈ (chartAt H z).source)
    (h : ‖(extChartAt I z) r - F.x‖ < F.η) : F.Z ∈ 𝓝 r := by
  have hcont : ContinuousAt (fun s : M => (extChartAt I z) s) r :=
    ((contMDiffOn_extChartAt (I := I) (x := z) (n := ∞)).continuousOn.continuousAt
      ((chartAt H z).open_source.mem_nhds hsrc))
  have hmem : (extChartAt I z) r ∈ Metric.ball F.x F.η := by
    rw [Metric.mem_ball, dist_eq_norm]; exact h
  have hpre : {s : M | ‖(extChartAt I z) s - F.x‖ < F.η} ∈ 𝓝 r := by
    have h1 := hcont.tendsto (Metric.isOpen_ball.mem_nhds hmem)
    filter_upwards [h1] with s hs
    simpa [Metric.mem_ball, dist_eq_norm] using hs
  refine Filter.mem_of_superset
    (Filter.inter_mem ((chartAt H z).open_source.mem_nhds hsrc) hpre) ?_
  intro s hs
  exact F.mem_of_norm hs.1 hs.2

theorem exists_chartFrame (hmet : IsMetricCompatible cov) {z p : M}
    (hp : p ∈ (chartAt H z).source) : Nonempty (ChartFrame (cov := cov) z p) := by
  have hptgt : (extChartAt I z) p ∈ (extChartAt I z).target :=
    PartialEquiv.map_source _ (by simpa only [extChartAt_source (I := I) z] using hp)
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp ((isOpen_extChartAt_target z).mem_nhds hptgt)
  set η : ℝ := ε / 2 with hηdef
  have hη : 0 < η := by rw [hηdef]; linarith
  have hball : Metric.closedBall ((extChartAt I z) p) η ⊆ (extChartAt I z).target := by
    intro a ha
    apply hsub
    rw [Metric.mem_ball]
    have h2 : dist a ((extChartAt I z) p) ≤ η := by rwa [Metric.mem_closedBall] at ha
    have h3 : dist ((extChartAt I z) p) a ≤ η := by rw [dist_comm]; exact h2
    rw [hηdef] at h3
    linarith
  set Z : Set M := (extChartAt I z).symm '' Metric.closedBall ((extChartAt I z) p) η with hZdef
  have hZc : IsCompact Z := by
    have hcont : ContinuousOn (fun a : E => (extChartAt I z).symm a)
        (Metric.closedBall ((extChartAt I z) p) η) :=
      (contMDiffOn_extChartAt_symm (I := I) (n := ∞) z).continuousOn.mono hball
    have hres := (isCompact_closedBall ((extChartAt I z) p) η).image_of_continuousOn hcont
    simpa only [hZdef] using hres
  have hZsrc : Z ⊆ (chartAt H z).source := by
    rintro r ⟨a, ha, rfl⟩
    have hatgt : a ∈ (extChartAt I z).target := hball ha
    have hmem : (extChartAt I z).symm a ∈ (extChartAt I z).source :=
      PartialEquiv.map_target _ hatgt
    simpa only [extChartAt_source (I := I) z] using hmem
  have hZne : Z.Nonempty :=
    ⟨(extChartAt I z).symm ((extChartAt I z) p),
      ⟨(extChartAt I z) p, Metric.mem_closedBall_self hη.le, rfl⟩⟩
  obtain ⟨D, -⟩ := exists_chartFlowData (cov := cov) (I := I) (z₀ := z) hZc hZsrc
  obtain ⟨lam, hlam, Lam, hLam, hbnd⟩ :=
    Submission.ChartBounds.exists_chartGram_bounds (I := I) z hZc hZne hZsrc
  refine ⟨⟨(extChartAt I z) p, rfl, η, hη, hball, Z, rfl, hZc, hZsrc, D, lam, hlam, Lam, hLam,
    hbnd⟩⟩

/-! ## The extension step -/

set_option maxHeartbeats 4000000 in
/-- **No gap in the good set.**  For every `t` of the good set below `L` there is `h > 0` such that
`t + h` is still good. -/
theorem exists_pos_add_mem_A
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {z₀ : M} {p : M} (hp : p ∈ (chartAt H z₀).source)
    {q : ℕ → M} (hq : Tendsto q atTop (𝓝 p))
    {y : ℕ → E} {y₀ : E} (hy : Tendsto y atTop (𝓝 y₀))
    (hunit : ∀ n, ‖frameVector (I := I) z₀ (q n) (y n)‖ = 1)
    (hu₀ : ‖frameVector (I := I) z₀ p y₀‖ = 1)
    {L : ℝ} (hL : 0 < L)
    {A : Set ℝ}
    (hA : A = {t : ℝ | 0 ≤ t ∧ t ≤ L ∧ ∀ s ∈ Icc 0 t,
        Tendsto (fun n => raySeq (cov := cov) hmet z₀ q y s n) atTop
          (𝓝 (rayLim (cov := cov) hmet z₀ p y₀ s))})
    {t : ℝ} (ht : t ∈ A) (htL : t < L) :
    ∃ h : ℝ, 0 < h ∧ t + h ∈ A := by
  classical
  obtain ⟨m, hmpos, hinjm⟩ := Submission.UniformInj.exists_pos_injAllAtLeast (cov := cov) hmet
  have ht' := ht
  rw [hA] at ht'
  obtain ⟨ht0, htLle, hP⟩ := ht'
  have hy₀ne : y₀ ≠ 0 := by
    intro h0
    exact frameVector_ne_zero_of_norm hu₀ (by rw [h0, Submission.ChartBounds.frameVector_zero'])
  by_cases ht00 : t = 0
  · -- the base case
    subst ht00
    obtain ⟨F⟩ := exists_chartFrame (cov := cov) hmet (z := z₀) (p := p) hp
    have hFp : p ∈ F.Z := by
      refine F.mem_of_norm hp ?_
      rw [F.hx, sub_self, norm_zero]
      exact F.hη
    have hstr : ‖(extChartAt I z₀) p - F.x‖ < F.η := by
      rw [F.hx, sub_self, norm_zero]; exact F.hη
    have hqZ : ∀ᶠ n in atTop, q n ∈ F.Z := hq (F.nhds_of_strict hp hstr)
    have hlam : 0 < Real.sqrt F.lam := Real.sqrt_pos.mpr F.hlam
    have hgram : chartGram (I := I) z₀ p y₀ y₀ = 1 := by
      rw [Submission.ChartConnection.chartGram_apply, real_inner_self_eq_norm_sq, hu₀]
      norm_num
    have hy₀norm : Real.sqrt F.lam * ‖y₀‖ ≤ 1 := by
      have hb := (F.hbnd p hFp y₀).1
      rw [hgram] at hb
      have hs : Real.sqrt F.lam ^ 2 = F.lam := Real.sq_sqrt F.hlam.le
      nlinarith [hb, hs, Real.sqrt_nonneg F.lam, norm_nonneg y₀]
    have hcpos : 0 < flowScale F.D := flowScale_pos F.D
    set hh : ℝ := min (L / 2) (Real.sqrt F.lam / (2 * flowScale F.D)) with hhdef
    have hhpos : 0 < hh := by
      rw [hhdef]; exact lt_min (by linarith) (div_pos hlam (by positivity))
    have hhL : hh ≤ L := by
      have h1 : hh ≤ L / 2 := by rw [hhdef]; exact min_le_left _ _
      linarith
    have hhsmall : hh ≤ Real.sqrt F.lam / (2 * flowScale F.D) := by
      rw [hhdef]; exact min_le_right _ _
    have hphase : (((extChartAt I z₀) p), flowScale F.D • (hh • y₀)) ∈
        chartData (I := I) z₀ F.Z := by
      refine ⟨⟨p, hFp, rfl⟩, ?_⟩
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_smul, norm_smul,
        Real.norm_of_nonneg hcpos.le, Real.norm_of_nonneg hhpos.le]
      refine le_trans ?_ (by norm_num : (1 : ℝ) / 2 ≤ 1)
      have hcm : flowScale F.D * hh ≤ Real.sqrt F.lam / 2 := by
        have h3 : flowScale F.D * hh ≤
            flowScale F.D * (Real.sqrt F.lam / (2 * flowScale F.D)) :=
          mul_le_mul_of_nonneg_left hhsmall hcpos.le
        have h4 : flowScale F.D * (Real.sqrt F.lam / (2 * flowScale F.D)) = Real.sqrt F.lam / 2 := by
          first | (field_simp; ring) | field_simp
        linarith
      have h2 : Real.sqrt F.lam / 2 * ‖y₀‖ ≤ 1 / 2 := by
        have h3 : (1 / 2 : ℝ) * (Real.sqrt F.lam * ‖y₀‖) ≤ 1 / 2 := by
          have h4 := mul_le_mul_of_nonneg_left hy₀norm (by norm_num : (0 : ℝ) ≤ 1 / 2)
          linarith [h4]
        nlinarith [h3]
      nlinarith [mul_le_mul_of_nonneg_right hcm (norm_nonneg y₀), h2]
    refine ⟨hh, hhpos, ?_⟩
    rw [hA]
    refine ⟨by rw [zero_add]; exact hhpos.le, by rw [zero_add]; exact hhL, ?_⟩
    intro s hs
    rw [zero_add] at hs
    exact tendsto_ray_window (cov := cov) hmet (z₀ := z₀) (Z := F.Z) F.hZsrc F.D
      (qn := q) (q := p) hq hqZ hFp (s₀ := 0) (s₁ := hh) hhpos.le
      (an := y) (a := y₀) hy hy₀ne
      (fun s _ => Filter.Eventually.of_forall (fun n => by
        rw [sub_zero, frameVector_smul]))
      (fun s _ => by rw [sub_zero, frameVector_smul])
      (by simpa only [sub_zero] using hphase) s hs
  · -- the non-degenerate case
    have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht00)
    set rt : M := rayLim (cov := cov) hmet z₀ p y₀ t with hrtdef
    obtain ⟨F⟩ := exists_chartFrame (cov := cov) hmet (z := rt) (p := rt) (mem_chart_source H rt)
    have hσcont : Continuous (rayLim (cov := cov) hmet z₀ p y₀) := continuous_rayLim hu₀
    have hrtZ : rt ∈ F.Z := by
      refine F.mem_of_norm (mem_chart_source H rt) ?_
      change ‖(extChartAt I rt) rt - F.x‖ < F.η
      rw [F.hx, sub_self, norm_zero]
      exact F.hη
    -- continuity in the parameter
    have hcont1 : ContinuousAt
        (fun s : ℝ => (extChartAt I rt) (rayLim (cov := cov) hmet z₀ p y₀ s)) t := by
      have h1 : ContinuousAt (fun r : M => (extChartAt I rt) r)
          (rayLim (cov := cov) hmet z₀ p y₀ t) :=
        ((contMDiffOn_extChartAt (I := I) (x := rt) (n := ∞)).continuousOn.continuousAt
          ((chartAt H rt).open_source.mem_nhds (mem_chart_source H rt)))
      exact h1.comp hσcont.continuousAt
    obtain ⟨δ₁, hδ₁pos, hδ₁⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, |s - t| < δ →
        ‖(extChartAt I rt) (rayLim (cov := cov) hmet z₀ p y₀ s) - F.x‖ < F.η := by
      have hmem : Metric.ball F.x F.η ∈
          𝓝 ((extChartAt I rt) (rayLim (cov := cov) hmet z₀ p y₀ t)) := by
        refine Metric.isOpen_ball.mem_nhds ?_
        have h0 : (extChartAt I rt) (rayLim (cov := cov) hmet z₀ p y₀ t) = F.x := by
          change (extChartAt I rt) rt = F.x
          exact F.hx.symm
        rw [h0, Metric.mem_ball, dist_self]
        exact F.hη
      obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp (hcont1 hmem)
      exact ⟨δ, hδ, fun s hs => by
        simpa only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm]
          using hδsub (by rwa [Metric.mem_ball, Real.dist_eq])⟩
    obtain ⟨δ₂, hδ₂pos, hδ₂⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, |s - t| < δ →
        rayLim (cov := cov) hmet z₀ p y₀ s ∈ (chartAt H rt).source := by
      have hmem : (chartAt H rt).source ∈ 𝓝 (rayLim (cov := cov) hmet z₀ p y₀ t) :=
        (chartAt H rt).open_source.mem_nhds (mem_chart_source H rt)
      obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp (hσcont.continuousAt hmem)
      exact ⟨δ, hδ, fun s hs => hδsub (by rwa [Metric.mem_ball, Real.dist_eq])⟩
    -- the constants
    have hcpos : 0 < flowScale F.D := flowScale_pos F.D
    have hLam : 0 < Real.sqrt F.Lam := Real.sqrt_pos.mpr F.hLam
    have hlam : 0 < Real.sqrt F.lam := Real.sqrt_pos.mpr F.hlam
    set η' : ℝ := min (1 / (2 * flowScale F.D)) (m / (2 * Real.sqrt F.Lam)) with hη'def
    have hη'pos : 0 < η' := by
      rw [hη'def]; exact lt_min (by positivity) (div_pos hmpos (by positivity))
    have hη'c : η' ≤ 1 / (2 * flowScale F.D) := by rw [hη'def]; exact min_le_left _ _
    have hη'm : Real.sqrt F.Lam * η' ≤ m / 2 := by
      have h : η' ≤ m / (2 * Real.sqrt F.Lam) := by rw [hη'def]; exact min_le_right _ _
      calc Real.sqrt F.Lam * η' ≤ Real.sqrt F.Lam * (m / (2 * Real.sqrt F.Lam)) :=
            mul_le_mul_of_nonneg_left h hLam.le
        _ = m / 2 := by first | (field_simp; ring) | field_simp
    have hnorm : ∀ r ∈ F.Z, ∀ u ∈ Metric.closedBall (0 : E) η',
        ‖frameVector (I := I) rt r u‖ < m := by
      intro r hr u hu
      have hu' : ‖u‖ ≤ η' := by simpa [Metric.mem_closedBall, dist_eq_norm] using hu
      rw [Submission.GExpFlow.norm_frameVector]
      have h1 : Real.sqrt (chartGram (I := I) rt r u u) ≤ Real.sqrt F.Lam * η' := by
        calc Real.sqrt (chartGram (I := I) rt r u u) ≤ Real.sqrt (F.Lam * ‖u‖ ^ 2) :=
              Real.sqrt_le_sqrt (F.hbnd r hr u).2
          _ = Real.sqrt F.Lam * ‖u‖ := by
              rw [Real.sqrt_mul F.hLam.le, Real.sqrt_sq (norm_nonneg u)]
          _ ≤ Real.sqrt F.Lam * η' := mul_le_mul_of_nonneg_left hu' hLam.le
      linarith
    -- the step size
    set hh : ℝ := min (t / 2) (min ((L - t) / 2) (min (δ₁ / 2) (min (δ₂ / 2)
      (min (Real.sqrt F.lam * η') (min (m / 4) (Real.sqrt F.lam / (2 * flowScale F.D)))))))
      with hhdef
    have hh1 : hh ≤ t / 2 := by rw [hhdef]; exact min_le_left _ _
    have hh2 : hh ≤ (L - t) / 2 := by
      rw [hhdef]; exact (min_le_right _ _).trans (min_le_left _ _)
    have hh3 : hh ≤ δ₁ / 2 := by
      rw [hhdef]; exact ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    have hh4 : hh ≤ δ₂ / 2 := by
      rw [hhdef]
      exact ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
        (min_le_left _ _))))
    have hh5 : hh ≤ Real.sqrt F.lam * η' := by
      rw [hhdef]
      exact ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))))
    have hh6 : hh ≤ m / 4 := by
      rw [hhdef]
      exact ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))))
    have hh7 : hh ≤ Real.sqrt F.lam / (2 * flowScale F.D) := by
      rw [hhdef]
      exact ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))))
    have hhpos : 0 < hh := by
      rw [hhdef]
      refine lt_min (by linarith) (lt_min (by linarith) (lt_min (by linarith) (lt_min (by linarith)
        (lt_min (mul_pos hlam hη'pos) (lt_min (by linarith)
          (div_pos hlam (by positivity)))))))
    have hs₀def' : True := trivial
    set s₀ : ℝ := t - hh with hs₀def
    have hs₀pos : 0 < s₀ := by rw [hs₀def]; linarith [hh1]
    have hs₀le : s₀ ≤ t := by rw [hs₀def]; linarith [hhpos.le]
    have hs₀le' : s₀ ≤ t + hh := by rw [hs₀def]; linarith [hhpos.le]
    have hts₀ : t - s₀ = hh := by rw [hs₀def]; ring
    have htne : s₀ ≠ 0 := ne_of_gt hs₀pos
    -- the states
    have hPs₀ : Tendsto (fun n => raySeq (cov := cov) hmet z₀ q y s₀ n) atTop
        (𝓝 (rayLim (cov := cov) hmet z₀ p y₀ s₀)) := hP s₀ ⟨hs₀pos.le, hs₀le⟩
    have hPt : Tendsto (fun n => raySeq (cov := cov) hmet z₀ q y t n) atTop
        (𝓝 (rayLim (cov := cov) hmet z₀ p y₀ t)) := hP t ⟨ht0, le_refl t⟩
    have habs₁ : |s₀ - t| < δ₁ := by
      rw [hs₀def]
      have : t - hh - t = -hh := by ring
      rw [this, abs_neg, abs_of_pos hhpos]
      linarith [hh3, hδ₁pos]
    have habs₂ : |s₀ - t| < δ₂ := by
      rw [hs₀def]
      have : t - hh - t = -hh := by ring
      rw [this, abs_neg, abs_of_pos hhpos]
      linarith [hh4, hδ₂pos]
    have hstrict₀ : ‖(extChartAt I rt) (rayLim (cov := cov) hmet z₀ p y₀ s₀) - F.x‖ < F.η :=
      hδ₁ s₀ habs₁
    have hsrclim : rayLim (cov := cov) hmet z₀ p y₀ s₀ ∈ (chartAt H rt).source := hδ₂ s₀ habs₂
    have hslim : rayLim (cov := cov) hmet z₀ p y₀ s₀ ∈ (extChartAt I rt).source := by
      simpa only [extChartAt_source (I := I) rt] using hsrclim
    have hzs₀ : rayLim (cov := cov) hmet z₀ p y₀ s₀ ∈ F.Z := F.mem_of_norm hsrclim hstrict₀
    have hxnZ : ∀ᶠ n in atTop, raySeq (cov := cov) hmet z₀ q y s₀ n ∈ F.Z :=
      hPs₀ (F.nhds_of_strict hsrclim hstrict₀)
    -- the limit velocity is non-zero
    have ha0 : velCoordsLim (cov := cov) hmet z₀ p y₀ rt s₀ ≠ 0 := by
      intro h0
      have h0' : (Trivialization.continuousLinearMapAt ℝ (trivializationAt E (TangentSpace I) rt)
          (rayLim (cov := cov) hmet z₀ p y₀ s₀))
          (curveVelocity (I := I) (rayLim (cov := cov) hmet z₀ p y₀) s₀) = 0 := h0
      have h1 : curveVelocity (I := I) (rayLim (cov := cov) hmet z₀ p y₀) s₀ = 0 := by
        rw [← Submission.GExpFlow.frameVector_clm (I := I) hslim
          (curveVelocity (I := I) (rayLim (cov := cov) hmet z₀ p y₀) s₀), h0',
          Submission.ChartBounds.frameVector_zero' rt (rayLim (cov := cov) hmet z₀ p y₀ s₀)]
      exact curveVelocity_rayLim_ne (cov := cov) hu₀ htne h1
    -- the velocity coordinates are small
    have hlimnorm : Real.sqrt F.lam * ‖(velCoordsLim (cov := cov) hmet z₀ p y₀ rt s₀ : E)‖ ≤ 1 := by
      have hclm : frameVector (I := I) rt (rayLim (cov := cov) hmet z₀ p y₀ s₀)
          (velCoordsLim (cov := cov) hmet z₀ p y₀ rt s₀)
          = curveVelocity (I := I) (rayLim (cov := cov) hmet z₀ p y₀) s₀ :=
        Submission.GExpFlow.frameVector_clm (I := I) hslim _
      have hnormv : ‖curveVelocity (I := I) (rayLim (cov := cov) hmet z₀ p y₀) s₀‖ = 1 :=
        norm_curveVelocity_rayLim (cov := cov) hu₀ htne
      have hgram : chartGram (I := I) rt (rayLim (cov := cov) hmet z₀ p y₀ s₀)
          (velCoordsLim (cov := cov) hmet z₀ p y₀ rt s₀)
          (velCoordsLim (cov := cov) hmet z₀ p y₀ rt s₀) = 1 := by
        rw [Submission.ChartConnection.chartGram_apply, real_inner_self_eq_norm_sq, hclm, hnormv]
        norm_num
      have hb := (F.hbnd (rayLim (cov := cov) hmet z₀ p y₀ s₀) hzs₀
        (velCoordsLim (cov := cov) hmet z₀ p y₀ rt s₀)).1
      rw [hgram] at hb
      have hs : Real.sqrt F.lam ^ 2 = F.lam := Real.sq_sqrt F.hlam.le
      nlinarith [hb, hs, Real.sqrt_nonneg F.lam, norm_nonneg (velCoordsLim
        (cov := cov) hmet z₀ p y₀ rt s₀ : E)]
    have hmemu : (hh • velCoordsLim (cov := cov) hmet z₀ p y₀ rt s₀) ∈
        Metric.closedBall (0 : E) η' := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_smul, Real.norm_of_nonneg hhpos.le]
      have h2 : (Real.sqrt F.lam * η') * ‖(velCoordsLim (cov := cov) hmet z₀ p y₀ rt s₀ : E)‖ ≤ η' := by
        have h3 := mul_le_mul_of_nonneg_left hlimnorm hη'pos.le
        rw [mul_one] at h3
        nlinarith [h3]
      exact le_trans (mul_le_mul_of_nonneg_right hh5 (norm_nonneg _)) h2
    have hmemun : ∀ᶠ n in atTop, (hh • velCoords (cov := cov) hmet z₀ q y rt s₀ n) ∈
        Metric.closedBall (0 : E) η' := by
      filter_upwards [hxnZ] with n hnZ
      have hsrc : raySeq (cov := cov) hmet z₀ q y s₀ n ∈ (extChartAt I rt).source := by
        simpa only [extChartAt_source (I := I) rt] using F.hZsrc hnZ
      have hclm : frameVector (I := I) rt (raySeq (cov := cov) hmet z₀ q y s₀ n)
          (velCoords (cov := cov) hmet z₀ q y rt s₀ n)
          = curveVelocity (I := I) (fun r : ℝ => raySeq (cov := cov) hmet z₀ q y r n) s₀ :=
        Submission.GExpFlow.frameVector_clm (I := I) hsrc _
      have hnormv : ‖curveVelocity (I := I) (fun r : ℝ => raySeq (cov := cov) hmet z₀ q y r n) s₀‖ = 1 :=
        norm_curveVelocity_raySeq (cov := cov) hunit htne n
      have hgram : chartGram (I := I) rt (raySeq (cov := cov) hmet z₀ q y s₀ n)
          (velCoords (cov := cov) hmet z₀ q y rt s₀ n)
          (velCoords (cov := cov) hmet z₀ q y rt s₀ n) = 1 := by
        rw [Submission.ChartConnection.chartGram_apply, real_inner_self_eq_norm_sq, hclm, hnormv]
        norm_num
      have hb := (F.hbnd (raySeq (cov := cov) hmet z₀ q y s₀ n) hnZ
        (velCoords (cov := cov) hmet z₀ q y rt s₀ n)).1
      rw [hgram] at hb
      have hb2 : Real.sqrt F.lam * ‖(velCoords (cov := cov) hmet z₀ q y rt s₀ n : E)‖ ≤ 1 := by
        have hs : Real.sqrt F.lam ^ 2 = F.lam := Real.sq_sqrt F.hlam.le
        nlinarith [hb, hs, Real.sqrt_nonneg F.lam, norm_nonneg (velCoords
          (cov := cov) hmet z₀ q y rt s₀ n : E)]
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_smul, Real.norm_of_nonneg hhpos.le]
      have h2 : (Real.sqrt F.lam * η') * ‖(velCoords (cov := cov) hmet z₀ q y rt s₀ n : E)‖ ≤ η' := by
        have h3 := mul_le_mul_of_nonneg_left hb2 hη'pos.le
        rw [mul_one] at h3
        nlinarith [h3]
      exact le_trans (mul_le_mul_of_nonneg_right hh5 (norm_nonneg _)) h2
    -- the two-position input
    have hstep := tendsto_coord_velocity (cov := cov) hmet htor
      (z₀ := rt) (Z := F.Z) F.hZsrc F.hZc F.D hη'c (fun r _ => hinjm r) hnorm
      (xn := fun n => raySeq (cov := cov) hmet z₀ q y s₀ n)
      (x := rayLim (cov := cov) hmet z₀ p y₀ s₀) hPs₀ hxnZ hzs₀
      (yn := fun n => raySeq (cov := cov) hmet z₀ q y t n)
      (y := rayLim (cov := cov) hmet z₀ p y₀ t) hPt
      (un := fun n => hh • velCoords (cov := cov) hmet z₀ q y rt s₀ n)
      (u := hh • velCoordsLim (cov := cov) hmet z₀ p y₀ rt s₀) hmemun hmemu
      (by
        filter_upwards [hxnZ] with n hnZ
        have hsrc : raySeq (cov := cov) hmet z₀ q y s₀ n ∈ (extChartAt I rt).source := by
          simpa only [extChartAt_source (I := I) rt] using F.hZsrc hnZ
        have h := raySeq_step (cov := cov) hunit hs₀pos hs₀le n hsrc
        rw [hts₀] at h
        exact h.symm)
      (by
        have h := rayLim_step (cov := cov) hu₀ hs₀pos hs₀le hslim
        rw [hts₀] at h
        exact h.symm)
    have htend' : Tendsto (fun n => velCoords (cov := cov) hmet z₀ q y rt s₀ n) atTop
        (𝓝 (velCoordsLim (cov := cov) hmet z₀ p y₀ rt s₀)) := by
      have h := hstep.const_smul (hh⁻¹)
      simpa only [smul_smul, inv_mul_cancel₀ (ne_of_gt hhpos), one_smul] using h
    -- the window
    have htphs : t + hh - s₀ = 2 * hh := by rw [hs₀def]; ring
    have hphase : (((extChartAt I rt) (rayLim (cov := cov) hmet z₀ p y₀ s₀)),
        flowScale F.D • ((t + hh - s₀) • velCoordsLim (cov := cov) hmet z₀ p y₀ rt s₀)) ∈
        chartData (I := I) rt F.Z := by
      refine ⟨⟨rayLim (cov := cov) hmet z₀ p y₀ s₀, hzs₀, rfl⟩, ?_⟩
      rw [htphs, Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_smul, norm_smul,
        Real.norm_of_nonneg hcpos.le, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * hh),
        ← mul_assoc]
      calc flowScale F.D * (2 * hh) * ‖(velCoordsLim (cov := cov) hmet z₀ p y₀ rt s₀ : E)‖
          ≤ Real.sqrt F.lam * ‖(velCoordsLim (cov := cov) hmet z₀ p y₀ rt s₀ : E)‖ := by
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
            have h3 : flowScale F.D * (2 * hh) ≤
                flowScale F.D * (2 * (Real.sqrt F.lam / (2 * flowScale F.D))) := by
              apply mul_le_mul_of_nonneg_left _ hcpos.le
              linarith [hh7]
            have h4 : flowScale F.D * (2 * (Real.sqrt F.lam / (2 * flowScale F.D)))
                = Real.sqrt F.lam := by
              first | (field_simp; ring) | field_simp
            linarith
        _ ≤ 1 := hlimnorm
    refine ⟨hh, hhpos, ?_⟩
    rw [hA]
    refine ⟨by linarith, by linarith, ?_⟩
    intro s hs
    by_cases hst : s ≤ t
    · exact hP s ⟨hs.1, hst⟩
    · have hlt : t < s := not_le.mp hst
      exact tendsto_ray_window (cov := cov) hmet (z₀ := rt) (Z := F.Z) F.hZsrc F.D
        (qn := fun n => raySeq (cov := cov) hmet z₀ q y s₀ n)
        (q := rayLim (cov := cov) hmet z₀ p y₀ s₀)
        hPs₀ hxnZ hzs₀ (s₀ := s₀) (s₁ := t + hh) hs₀le'
        (an := fun n => velCoords (cov := cov) hmet z₀ q y rt s₀ n)
        (a := velCoordsLim (cov := cov) hmet z₀ p y₀ rt s₀) htend' ha0
        (fun s' hs' => by
          filter_upwards [hxnZ] with n hnZ
          have hsrc : raySeq (cov := cov) hmet z₀ q y s₀ n ∈ (extChartAt I rt).source := by
            simpa only [extChartAt_source (I := I) rt] using F.hZsrc hnZ
          exact raySeq_step (cov := cov) hunit hs₀pos hs'.1 n hsrc)
        (fun s' hs' => rayLim_step (cov := cov) hu₀ hs₀pos hs'.1 hslim)
        hphase s ⟨by rw [hs₀def]; linarith, hs.2⟩


/-! ## The good set argument -/

set_option maxHeartbeats 2000000 in
/-- **Rays of `GExp` converge**: if the base points and the (unit) directions converge, then so do the
points of the rays, for parameters in a fixed interval. -/
theorem tendsto_ray_unit
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {z₀ : M} {p : M} (hp : p ∈ (chartAt H z₀).source)
    {q : ℕ → M} (hq : Tendsto q atTop (𝓝 p))
    {y : ℕ → E} {y₀ : E} (hy : Tendsto y atTop (𝓝 y₀))
    (hunit : ∀ n, ‖frameVector (I := I) z₀ (q n) (y n)‖ = 1)
    (hu₀ : ‖frameVector (I := I) z₀ p y₀‖ = 1)
    {L : ℝ} (hL : 0 < L) :
    ∀ t ∈ Icc (0 : ℝ) L, Tendsto (fun n => raySeq (cov := cov) hmet z₀ q y t n) atTop
      (𝓝 (rayLim (cov := cov) hmet z₀ p y₀ t)) := by
  classical
  set A : Set ℝ := {t : ℝ | 0 ≤ t ∧ t ≤ L ∧ ∀ s ∈ Icc 0 t,
      Tendsto (fun n => raySeq (cov := cov) hmet z₀ q y s n) atTop
        (𝓝 (rayLim (cov := cov) hmet z₀ p y₀ s))} with hAdef
  have hA0 : (0 : ℝ) ∈ A := by
    refine ⟨le_refl 0, hL.le, ?_⟩
    intro s hs
    have hs0 : s = 0 := le_antisymm hs.2 hs.1
    have hlim : rayLim (cov := cov) hmet z₀ p y₀ s = p := by
      rw [hs0]; exact rayLim_zero
    rw [hlim]
    have hev : (fun n => raySeq (cov := cov) hmet z₀ q y s n) =ᶠ[atTop] q := by
      filter_upwards with n
      rw [hs0]
      exact raySeq_zero n
    exact Filter.Tendsto.congr' hev.symm hq
  have hAne : A.Nonempty := ⟨0, hA0⟩
  have hAbdd : BddAbove A := ⟨L, fun t ht => ht.2.1⟩
  set T : ℝ := sSup A with hTdef
  have hTle : T ≤ L := csSup_le hAne (fun t ht => ht.2.1)
  have hTmem : T ∈ A := by
    refine ⟨le_csSup hAbdd hA0, hTle, ?_⟩
    intro s hs
    rcases lt_or_eq_of_le hs.2 with hlt | heq
    · obtain ⟨t', ht'A, hst'⟩ :=
        exists_lt_of_lt_csSup (s := A) (b := s) hAne (by rw [← hTdef]; exact hlt)
      exact ht'A.2.2 s ⟨hs.1, hst'.le⟩
    · subst heq
      refine tendsto_of_eventually_edist_lt (I := I) (M := M) ?_
      intro ε hε
      have hε3 : (0 : ℝ) < ε / 3 := by positivity
      have hex : ∀ k : ℕ, ∃ t ∈ A, T - 1 / ((k : ℝ) + 1) < t := by
        intro k
        refine exists_lt_of_lt_csSup (s := A) (b := T - 1 / ((k : ℝ) + 1)) hAne ?_
        rw [← hTdef]
        exact sub_lt_self _ (by positivity)
      choose tseq htA htlt using hex
      have htle : ∀ k, tseq k ≤ T := fun k => le_csSup hAbdd (htA k)
      obtain ⟨k, hk⟩ : ∃ k, T - tseq k < ε / 3 := by
        obtain ⟨k, hk⟩ := exists_nat_gt ((3 : ℝ) / ε)
        refine ⟨k, ?_⟩
        have h1 : T - tseq k < 1 / ((k : ℝ) + 1) := by linarith [htlt k]
        have h2 : 1 / ((k : ℝ) + 1) ≤ ε / 3 := by
          have hk' : (3 : ℝ) ≤ ε * ((k : ℝ) + 1) := by
            have h5 : 3 / ε * ε ≤ (k : ℝ) * ε := mul_le_mul_of_nonneg_right hk.le hε.le
            rw [div_mul_cancel₀ 3 (ne_of_gt hε)] at h5
            linarith [h5]
          rw [div_le_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) + 1),
            div_mul_eq_mul_div, le_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
          linarith [hk']
        linarith
      haveI hcb : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
        Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
      have hev : ∀ᶠ n in atTop, Manifold.riemannianEDist I
          (rayLim (cov := cov) hmet z₀ p y₀ (tseq k))
          (raySeq (cov := cov) hmet z₀ q y (tseq k) n) < ENNReal.ofReal (ε / 3) :=
        (htA k).2.2 (tseq k) ⟨(htA k).1, le_refl _⟩
          (eventually_riemannianEDist_lt (I := I) (rayLim (cov := cov) hmet z₀ p y₀ (tseq k))
            (ENNReal.ofReal_pos.mpr hε3))
      filter_upwards [hev] with n hn
      have h1 : Manifold.riemannianEDist I (rayLim (cov := cov) hmet z₀ p y₀ T)
          (rayLim (cov := cov) hmet z₀ p y₀ (tseq k)) ≤ ENNReal.ofReal (T - tseq k) := by
        have h := Submission.GExpRay2.edist_GExp_smul_le_mul_norm (cov := cov) hmet p
          (v := frameVector (I := I) z₀ p y₀) (a := tseq k) (b := T) (htA k).1 (htle k)
        rw [hu₀, mul_one] at h
        rwa [Manifold.riemannianEDist_comm] at h
      have h3 : Manifold.riemannianEDist I (raySeq (cov := cov) hmet z₀ q y (tseq k) n)
          (raySeq (cov := cov) hmet z₀ q y T n) ≤ ENNReal.ofReal (T - tseq k) := by
        have h := Submission.GExpRay2.edist_GExp_smul_le_mul_norm (cov := cov) hmet (q n)
          (v := frameVector (I := I) z₀ (q n) (y n)) (a := tseq k) (b := T)
          (htA k).1 (htle k)
        rw [hunit n, mul_one] at h
        exact h
      have h4 : ENNReal.ofReal (T - tseq k) + ENNReal.ofReal (ε / 3)
          + ENNReal.ofReal (T - tseq k) < ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (by linarith [htle k]) (le_of_lt hε3),
          ← ENNReal.ofReal_add (by linarith [htle k, hε3]) (by linarith [htle k])]
        exact (ENNReal.ofReal_lt_ofReal_iff hε).mpr (by linarith)
      have h5 : Manifold.riemannianEDist I (rayLim (cov := cov) hmet z₀ p y₀ T)
            (rayLim (cov := cov) hmet z₀ p y₀ (tseq k))
          + Manifold.riemannianEDist I (rayLim (cov := cov) hmet z₀ p y₀ (tseq k))
            (raySeq (cov := cov) hmet z₀ q y (tseq k) n)
          + Manifold.riemannianEDist I (raySeq (cov := cov) hmet z₀ q y (tseq k) n)
            (raySeq (cov := cov) hmet z₀ q y T n)
          ≤ ENNReal.ofReal (T - tseq k) + ENNReal.ofReal (ε / 3)
            + ENNReal.ofReal (T - tseq k) :=
        add_le_add (add_le_add h1 (le_of_lt hn)) h3
      refine lt_of_le_of_lt ?_ (lt_of_le_of_lt h5 h4)
      have ht1 : Manifold.riemannianEDist I (rayLim (cov := cov) hmet z₀ p y₀ T)
          (raySeq (cov := cov) hmet z₀ q y T n)
          ≤ Manifold.riemannianEDist I (rayLim (cov := cov) hmet z₀ p y₀ T)
              (rayLim (cov := cov) hmet z₀ p y₀ (tseq k))
            + Manifold.riemannianEDist I (rayLim (cov := cov) hmet z₀ p y₀ (tseq k))
              (raySeq (cov := cov) hmet z₀ q y T n) :=
        Manifold.riemannianEDist_triangle
      have ht2 : Manifold.riemannianEDist I (rayLim (cov := cov) hmet z₀ p y₀ (tseq k))
          (raySeq (cov := cov) hmet z₀ q y T n)
          ≤ Manifold.riemannianEDist I (rayLim (cov := cov) hmet z₀ p y₀ (tseq k))
              (raySeq (cov := cov) hmet z₀ q y (tseq k) n)
            + Manifold.riemannianEDist I (raySeq (cov := cov) hmet z₀ q y (tseq k) n)
              (raySeq (cov := cov) hmet z₀ q y T n) :=
        Manifold.riemannianEDist_triangle
      calc Manifold.riemannianEDist I (rayLim (cov := cov) hmet z₀ p y₀ T)
            (raySeq (cov := cov) hmet z₀ q y T n)
          ≤ Manifold.riemannianEDist I (rayLim (cov := cov) hmet z₀ p y₀ T)
              (rayLim (cov := cov) hmet z₀ p y₀ (tseq k))
            + Manifold.riemannianEDist I (rayLim (cov := cov) hmet z₀ p y₀ (tseq k))
              (raySeq (cov := cov) hmet z₀ q y T n) := ht1
        _ ≤ Manifold.riemannianEDist I (rayLim (cov := cov) hmet z₀ p y₀ T)
              (rayLim (cov := cov) hmet z₀ p y₀ (tseq k))
            + (Manifold.riemannianEDist I (rayLim (cov := cov) hmet z₀ p y₀ (tseq k))
                (raySeq (cov := cov) hmet z₀ q y (tseq k) n)
              + Manifold.riemannianEDist I (raySeq (cov := cov) hmet z₀ q y (tseq k) n)
                (raySeq (cov := cov) hmet z₀ q y T n)) :=
            add_le_add le_rfl ht2
        _ = Manifold.riemannianEDist I (rayLim (cov := cov) hmet z₀ p y₀ T)
              (rayLim (cov := cov) hmet z₀ p y₀ (tseq k))
            + Manifold.riemannianEDist I (rayLim (cov := cov) hmet z₀ p y₀ (tseq k))
              (raySeq (cov := cov) hmet z₀ q y (tseq k) n)
            + Manifold.riemannianEDist I (raySeq (cov := cov) hmet z₀ q y (tseq k) n)
              (raySeq (cov := cov) hmet z₀ q y T n) := by rw [add_assoc]

  have hTcomplement : T = L := by
    by_contra hne
    have hlt : T < L := lt_of_le_of_ne hTle hne
    obtain ⟨h, hhpos, hmem⟩ := exists_pos_add_mem_A (cov := cov) hmet htor hp hq hy hunit hu₀
      hL hAdef hTmem hlt
    exact absurd (le_csSup hAbdd hmem) (not_le.mpr (lt_add_of_pos_right T hhpos))
  have hLmem : L ∈ A := hTcomplement ▸ hTmem
  exact hLmem.2.2


/-! ## The brick: joint continuity of `GExp` in the base point -/

set_option maxHeartbeats 2000000 in
/-- Rays with **converging lengths** converge. -/
theorem tendsto_GExp_ray_length
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {z₀ : M} {p : M} (hp : p ∈ (chartAt H z₀).source)
    {q : ℕ → M} (hq : Tendsto q atTop (𝓝 p))
    {y : ℕ → E} {y₀ : E} (hy : Tendsto y atTop (𝓝 y₀))
    (hunit : ∀ n, ‖frameVector (I := I) z₀ (q n) (y n)‖ = 1)
    (hu₀ : ‖frameVector (I := I) z₀ p y₀‖ = 1)
    {Ln : ℕ → ℝ} {L : ℝ} (hLn : Tendsto Ln atTop (𝓝 L)) (hLnpos : ∀ n, 0 ≤ Ln n)
    (hL : 0 < L) :
    Tendsto (fun n => raySeq (cov := cov) hmet z₀ q y (Ln n) n) atTop
      (𝓝 (rayLim (cov := cov) hmet z₀ p y₀ L)) := by
  classical
  haveI hcb : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  have hmain := tendsto_ray_unit (cov := cov) hmet htor hp hq hy hunit hu₀ (L := L + 1)
    (by linarith)
  have hLconv : Tendsto (fun n => raySeq (cov := cov) hmet z₀ q y L n) atTop
      (𝓝 (rayLim (cov := cov) hmet z₀ p y₀ L)) :=
    hmain L ⟨hL.le, by linarith⟩
  refine tendsto_of_eventually_edist_lt (I := I) (M := M) ?_
  intro ε hε
  have hε3 : (0 : ℝ) < ε / 3 := by positivity
  have hdiff : ∀ᶠ n in atTop, Manifold.riemannianEDist I
      (raySeq (cov := cov) hmet z₀ q y (Ln n) n) (raySeq (cov := cov) hmet z₀ q y L n)
      < ENNReal.ofReal (ε / 3) := by
    have hclose : ∀ᶠ n in atTop, |Ln n - L| < ε / 3 := by
      have hmem : Metric.ball L (ε / 3) ∈ 𝓝 L := Metric.ball_mem_nhds L hε3
      filter_upwards [hLn hmem] with n hn
      simp only [Set.mem_preimage] at hn
      rw [Metric.mem_ball, Real.dist_eq] at hn
      exact hn
    filter_upwards [hclose] with n hn
    rcases le_total (Ln n) L with hle | hle
    · have h := Submission.GExpRay2.edist_GExp_smul_le_mul_norm (cov := cov) hmet (q n)
        (v := frameVector (I := I) z₀ (q n) (y n)) (a := Ln n) (b := L) (hLnpos n) hle
      rw [hunit n, mul_one] at h
      have h' : Manifold.riemannianEDist I (raySeq (cov := cov) hmet z₀ q y (Ln n) n)
          (raySeq (cov := cov) hmet z₀ q y L n) ≤ ENNReal.ofReal (L - Ln n) := h
      refine lt_of_le_of_lt h' ((ENNReal.ofReal_lt_ofReal_iff hε3).mpr ?_)
      rw [show L - Ln n = |Ln n - L| from by
        first | (rw [abs_of_nonpos (by linarith)]; ring) | rw [abs_of_nonpos (by linarith)]]
      exact hn
    · have h := Submission.GExpRay2.edist_GExp_smul_le_mul_norm (cov := cov) hmet (q n)
        (v := frameVector (I := I) z₀ (q n) (y n)) (a := L) (b := Ln n) hL.le hle
      rw [hunit n, mul_one, Manifold.riemannianEDist_comm] at h
      have h' : Manifold.riemannianEDist I (raySeq (cov := cov) hmet z₀ q y (Ln n) n)
          (raySeq (cov := cov) hmet z₀ q y L n) ≤ ENNReal.ofReal (Ln n - L) := h
      refine lt_of_le_of_lt h' ((ENNReal.ofReal_lt_ofReal_iff hε3).mpr ?_)
      rw [show Ln n - L = |Ln n - L| from by
        first | (rw [abs_of_nonneg (by linarith)]; ring) | rw [abs_of_nonneg (by linarith)]]
      exact hn
  have hconv : ∀ᶠ n in atTop, Manifold.riemannianEDist I
      (raySeq (cov := cov) hmet z₀ q y L n) (rayLim (cov := cov) hmet z₀ p y₀ L)
      < ENNReal.ofReal (ε / 3) := by
    have h := hLconv (eventually_riemannianEDist_lt (I := I)
      (rayLim (cov := cov) hmet z₀ p y₀ L) (ENNReal.ofReal_pos.mpr hε3))
    filter_upwards [h] with n hn
    have hn' : Manifold.riemannianEDist I (rayLim (cov := cov) hmet z₀ p y₀ L)
        (raySeq (cov := cov) hmet z₀ q y L n) < ENNReal.ofReal (ε / 3) := hn
    rwa [Manifold.riemannianEDist_comm] at hn'
  filter_upwards [hdiff, hconv] with n h1 h2
  rw [Manifold.riemannianEDist_comm]
  calc Manifold.riemannianEDist I (raySeq (cov := cov) hmet z₀ q y (Ln n) n)
        (rayLim (cov := cov) hmet z₀ p y₀ L)
      ≤ Manifold.riemannianEDist I (raySeq (cov := cov) hmet z₀ q y (Ln n) n)
          (raySeq (cov := cov) hmet z₀ q y L n)
        + Manifold.riemannianEDist I (raySeq (cov := cov) hmet z₀ q y L n)
          (rayLim (cov := cov) hmet z₀ p y₀ L) := Manifold.riemannianEDist_triangle
    _ < ENNReal.ofReal ε := by
        refine lt_of_le_of_lt (add_le_add (le_of_lt h1) (le_of_lt h2)) ?_
        rw [← ENNReal.ofReal_add (le_of_lt hε3) (le_of_lt hε3)]
        exact (ENNReal.ofReal_lt_ofReal_iff hε).mpr (by linarith)

set_option maxHeartbeats 2000000 in
/-- The non-degenerate case, with the vectors assumed non-zero. -/
theorem tendsto_GExp_frameVector_ne
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {z₀ : M} {p : M} (hp : p ∈ (chartAt H z₀).source)
    {q : ℕ → M} (hq : Tendsto q atTop (𝓝 p))
    {a : ℕ → E} {a₀ : E} (ha : Tendsto a atTop (𝓝 a₀))
    (hpos : ∀ n, 0 < ‖frameVector (I := I) z₀ (q n) (a n)‖)
    (ha₀ : a₀ ≠ 0) :
    Tendsto (fun n => GExp (cov := cov) hmet (q n) (frameVector (I := I) z₀ (q n) (a n)))
      atTop (𝓝 (GExp (cov := cov) hmet p (frameVector (I := I) z₀ p a₀))) := by
  classical
  have hpunit : frameVector (I := I) z₀ p a₀ ≠ 0 := fun h0 =>
    ha₀ ((Submission.ChartBounds.frameVector_eq_zero_iff (I := I) (x₀ := z₀) (p := p) hp a₀).mp h0)
  have hLpos : 0 < ‖frameVector (I := I) z₀ p a₀‖ := norm_pos_iff.mpr hpunit
  have hLn : Tendsto (fun n => ‖frameVector (I := I) z₀ (q n) (a n)‖) atTop
      (𝓝 ‖frameVector (I := I) z₀ p a₀‖) := by
    have hcont := Submission.ChartBounds.continuousAt_chartGram_prod (I := I) z₀ hp a₀
    have hpair : Tendsto (fun n => (q n, a n)) atTop (𝓝 (p, a₀)) :=
      (Prod.tendsto_iff (fun n => (q n, a n)) (p, a₀)).mpr ⟨hq, ha⟩
    have h1 : Tendsto (fun n => chartGram (I := I) z₀ (q n) (a n) (a n)) atTop
        (𝓝 (chartGram (I := I) z₀ p a₀ a₀)) := hcont.tendsto.comp hpair
    have h2 := Real.continuous_sqrt.continuousAt.tendsto.comp h1
    simpa only [Function.comp_def, Submission.GExpFlow.norm_frameVector] using h2
  have hy : Tendsto (fun n => (‖frameVector (I := I) z₀ (q n) (a n)‖)⁻¹ • a n) atTop
      (𝓝 ((‖frameVector (I := I) z₀ p a₀‖)⁻¹ • a₀)) := hLn.inv₀ hLpos.ne' |>.smul ha
  have hunit : ∀ n, ‖frameVector (I := I) z₀ (q n)
      ((‖frameVector (I := I) z₀ (q n) (a n)‖)⁻¹ • a n)‖ = 1 := by
    intro n
    rw [Submission.Geodesic.frameVector_smul, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr (le_of_lt (hpos n)))]
    exact inv_mul_cancel₀ (ne_of_gt (hpos n))
  have hu₀unit : ‖frameVector (I := I) z₀ p ((‖frameVector (I := I) z₀ p a₀‖)⁻¹ • a₀)‖ = 1 := by
    rw [Submission.Geodesic.frameVector_smul, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr (le_of_lt hLpos))]
    exact inv_mul_cancel₀ (ne_of_gt hLpos)
  have hmain := tendsto_GExp_ray_length (cov := cov) hmet htor hp hq hy hunit hu₀unit
    (Ln := fun n => ‖frameVector (I := I) z₀ (q n) (a n)‖) hLn (fun n => norm_nonneg _) hLpos
  have hlim : rayLim (cov := cov) hmet z₀ p
      ((‖frameVector (I := I) z₀ p a₀‖)⁻¹ • a₀) (‖frameVector (I := I) z₀ p a₀‖)
      = GExp (cov := cov) hmet p (frameVector (I := I) z₀ p a₀) := by
    simp only [rayLim]
    rw [frameVector_smul, smul_smul, mul_inv_cancel₀ (ne_of_gt hLpos), one_smul]
  rw [hlim] at hmain
  refine Filter.Tendsto.congr' ?_ hmain
  filter_upwards with n
  have h1 : (‖frameVector (I := I) z₀ (q n) (a n)‖)
      • frameVector (I := I) z₀ (q n) ((‖frameVector (I := I) z₀ (q n) (a n)‖)⁻¹ • a n)
      = frameVector (I := I) z₀ (q n) (a n) := by
    rw [frameVector_smul, smul_smul, mul_inv_cancel₀ (ne_of_gt (hpos n)), one_smul]
  simp only [raySeq]
  rw [h1]

set_option maxHeartbeats 2000000 in
/-- **Joint continuity of the exponential map in the base point and the velocity**, in the
coordinates of a fixed chart. -/
theorem tendsto_GExp_frameVector
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {z₀ : M} {p : M} (hp : p ∈ (chartAt H z₀).source)
    {q : ℕ → M} {a : ℕ → E} {a₀ : E}
    (hq : Tendsto q atTop (𝓝 p)) (ha : Tendsto a atTop (𝓝 a₀)) :
    Tendsto (fun n => GExp (cov := cov) hmet (q n) (frameVector (I := I) z₀ (q n) (a n)))
      atTop (𝓝 (GExp (cov := cov) hmet p (frameVector (I := I) z₀ p a₀))) := by
  classical
  by_cases ha₀ : a₀ = 0
  · subst ha₀
    haveI hcb : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
      Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
    obtain ⟨F⟩ := exists_chartFrame (cov := cov) hmet (z := z₀) (p := p) hp
    have hZnhds : F.Z ∈ 𝓝 p := F.nhds_of_strict hp (by
      change ‖(extChartAt I z₀) p - F.x‖ < F.η
      rw [F.hx, sub_self, norm_zero]
      exact F.hη)
    have hevZ : ∀ᶠ n in atTop, q n ∈ F.Z := hq hZnhds
    have hLampos : 0 < Real.sqrt F.Lam := Real.sqrt_pos.mpr F.hLam
    refine tendsto_of_eventually_edist_lt (I := I) (M := M) ?_
    intro ε hε
    have hε3 : (0 : ℝ) < ε / 3 := by positivity
    have hbound : ∀ᶠ n in atTop, ‖frameVector (I := I) z₀ (q n) (a n)‖ < ε / 3 := by
      have ha0 : Tendsto (fun n => ‖a n‖) atTop (𝓝 0) := by simpa using ha.norm
      have h2 : Tendsto (fun n => Real.sqrt F.Lam * ‖a n‖) atTop (𝓝 0) := by
        have h3 : Tendsto (fun n => Real.sqrt F.Lam * ‖a n‖) atTop
            (𝓝 (Real.sqrt F.Lam * (0 : ℝ))) := tendsto_const_nhds.mul ha0
        simpa using h3
      have h4 : ∀ᶠ n in atTop, Real.sqrt F.Lam * ‖a n‖ < ε / 3 := by
        have h5 := h2 (Metric.ball_mem_nhds (0 : ℝ) hε3)
        filter_upwards [h5] with n hn
        simp only [Set.mem_preimage] at hn
        rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg
          (mul_nonneg hLampos.le (norm_nonneg _))] at hn
        exact hn
      filter_upwards [h4, hevZ] with n hn hnZ
      have hb := (F.hbnd (q n) hnZ (a n)).2
      rw [Submission.GExpFlow.norm_frameVector (I := I) (a n)]
      calc Real.sqrt (chartGram (I := I) z₀ (q n) (a n) (a n))
          ≤ Real.sqrt (F.Lam * ‖a n‖ ^ 2) := Real.sqrt_le_sqrt hb
        _ = Real.sqrt F.Lam * ‖a n‖ := by
              rw [Real.sqrt_mul F.hLam.le, Real.sqrt_sq (norm_nonneg _)]
        _ < ε / 3 := hn
    have hpclose : ∀ᶠ n in atTop, Manifold.riemannianEDist I p (q n)
        < ENNReal.ofReal (ε / 3) :=
      hq (eventually_riemannianEDist_lt (I := I) p (ENNReal.ofReal_pos.mpr hε3))
    rw [Submission.ChartBounds.frameVector_zero', GExp_zero]
    filter_upwards [hbound, hpclose] with n hb hpc
    have h1 : Manifold.riemannianEDist I (q n)
        (GExp (cov := cov) hmet (q n) (frameVector (I := I) z₀ (q n) (a n)))
        ≤ ENNReal.ofReal (ε / 3) := by
      have h := Submission.GExpRay2.edist_GExp_smul_le_mul_norm (cov := cov) hmet (q n)
        (v := frameVector (I := I) z₀ (q n) (a n)) (a := 0) (b := 1) le_rfl zero_le_one
      rw [zero_smul, one_smul, sub_zero, GExp_zero, one_mul] at h
      exact le_trans h (ENNReal.ofReal_le_ofReal hb.le)
    calc Manifold.riemannianEDist I p
          (GExp (cov := cov) hmet (q n) (frameVector (I := I) z₀ (q n) (a n)))
        ≤ Manifold.riemannianEDist I p (q n)
          + Manifold.riemannianEDist I (q n)
            (GExp (cov := cov) hmet (q n) (frameVector (I := I) z₀ (q n) (a n))) :=
          Manifold.riemannianEDist_triangle
      _ < ENNReal.ofReal ε := by
          refine lt_of_le_of_lt (add_le_add (le_of_lt hpc) h1) ?_
          rw [← ENNReal.ofReal_add (le_of_lt hε3) (le_of_lt hε3)]
          exact (ENNReal.ofReal_lt_ofReal_iff hε).mpr (by linarith)
  · -- the non-degenerate case: shift so that no vector vanishes
    have hpunit : frameVector (I := I) z₀ p a₀ ≠ 0 := fun h0 =>
      ha₀ ((Submission.ChartBounds.frameVector_eq_zero_iff (I := I) (x₀ := z₀) (p := p) hp a₀).mp h0)
    have hLpos : 0 < ‖frameVector (I := I) z₀ p a₀‖ := norm_pos_iff.mpr hpunit
    have hLnorm : Tendsto (fun n => ‖frameVector (I := I) z₀ (q n) (a n)‖) atTop
        (𝓝 ‖frameVector (I := I) z₀ p a₀‖) := by
      have hcont := Submission.ChartBounds.continuousAt_chartGram_prod (I := I) z₀ hp a₀
      have hpair : Tendsto (fun n => (q n, a n)) atTop (𝓝 (p, a₀)) :=
        (Prod.tendsto_iff (fun n => (q n, a n)) (p, a₀)).mpr ⟨hq, ha⟩
      have h1 : Tendsto (fun n => chartGram (I := I) z₀ (q n) (a n) (a n)) atTop
          (𝓝 (chartGram (I := I) z₀ p a₀ a₀)) := hcont.tendsto.comp hpair
      have h2 := Real.continuous_sqrt.continuousAt.tendsto.comp h1
      simpa only [Function.comp_def, Submission.GExpFlow.norm_frameVector] using h2
    have hevpos : ∀ᶠ n in atTop, 0 < ‖frameVector (I := I) z₀ (q n) (a n)‖ :=
      hLnorm (isOpen_Ioi.mem_nhds hLpos)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hevpos
    have hshift : Tendsto (fun n : ℕ => n + N) atTop atTop := tendsto_add_atTop_nat N
    have hfinal : Tendsto (fun n : ℕ => GExp (cov := cov) hmet (q (n + N))
        (frameVector (I := I) z₀ (q (n + N)) (a (n + N)))) atTop
        (𝓝 (GExp (cov := cov) hmet p (frameVector (I := I) z₀ p a₀))) :=
      tendsto_GExp_frameVector_ne (cov := cov) hmet htor hp (hq.comp hshift)
        (ha.comp hshift) (fun n => hN _ (by simp)) ha₀
    rw [Filter.tendsto_def] at hfinal ⊢
    intro s hs
    obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp (hfinal s hs)
    exact Filter.eventually_atTop.mpr ⟨M + N, fun n hn => by
      have h1 : M ≤ n - N := Nat.le_sub_of_add_le hn
      have h2 : n - N + N = n := Nat.sub_add_cancel (le_trans (Nat.le_add_left N M) hn)
      have h3 : GExp (cov := cov) hmet (q ((n - N) + N))
          (frameVector (I := I) z₀ (q ((n - N) + N)) (a ((n - N) + N))) ∈ s := hM (n - N) h1
      rw [h2] at h3
      exact h3⟩

end Submission.GExpJointPt
