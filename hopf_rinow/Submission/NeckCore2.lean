import ChallengeDeps
import Submission.Metric
import Submission.ChartArc
import Submission.Rigidity
import Submission.ChartNormal
import Submission.LocalExt
import Submission.TinyStrict
import Submission.ModelNormalBall
import Submission.ArcModel
import Submission.ModelArc
import Submission.ArcNB
import Submission.ModelExpDiffeo2
import Submission.NeckModel
import Submission.NeckEq
import Submission.NeckSmoothCurve
import Submission.NeckFlow
import Submission.NeckSmooth
import Submission.LiftChild
import Submission.FlowOdeChild
import Submission.ReparamChild
import Mathlib

/-!
# Neck (tail) rigidity, route B (child task)

Prove COMPLETELY the theorem below (identical statement to `Submission.neck_rigidity`, new
name `Submission.NeckCore2.neck_rigidity`).  It is TRUE.  Route B is the MODEL-FIRST route:
prove that the tail of γ is a genuine geodesic of the q-chart model, then use flow facts.

## Route B (model-first)

Facts you may rely on (all VERIFIED; READ their statements in the imported files):
- `chart_normal_forward` (LocalExt): per-point data at q: rho0, ge, r, ExpM, S, invM, radial
  identity edist q (ExpM v) = ofReal(sqrt((ge x0) v v)); model data rho_e, tau_e, Phi (a flow
  of odeField ge on closedBall (x0,0) 2), exp (exp v = (Phi (x0, v/tau_e) tau_e).1 for v in
  ball 0 rho_e, ContDiffOn 1, exp 0 = x0), ExpM v = chart⁻¹(exp v) on ball 0 rho_e;
  `hcv` geodesic curves from x0 to exp v of constant ge-speed sqrt((ge x0) v v) staying in
  ball x0 rhoT; FWD forward-ray identity.
- `region_flow_pkg` (ModelArc): given g C3 with invertible gx and R0 = (K+3:NNReal) etc.,
  provides Tf, rho_u, L, Phi with per-base flow clauses on closedBall (b,0) 1 for all
  b in ball x0 rho_u, Lipschitz in data, etc.
- `uniform_normal_ball` (ArcModel) / `uniform_normal_ball_aux` (ArcNB): per-base staying
  minimality: for all b in ball x0 rho_B and v in ball 0 delta_u: every C¹ staying curve from
  b to expOf b Phi tau_u v has mgLength >= sqrt((g b) v v).
- `model_normal_ball` (ModelNormalBall), `radial_minimality` (MinimalityWrap): per-base normal
  ball data incl. radial derivative bound hRad: for z in V, z != x0, and all X:
  |(fderiv of radialCoord at z) X| <= mgSpeed(g,z,X); `bilin_cs_eq_colinear` (LocalExt) gives
  the equality case: |F'(z)X| = mgSpeed(g,z,X) iff X is collinear with the radial direction
  at z.
- `exp_two_point_bound`, `flow_exp_local_diffeomorphism`, `ExpLocalDiffeo`, `ModelExpC1`:
  exp_b is a local diffeo near 0 with explicit uniform radii; two-point estimates.
- `Metric.IsLocLinear.edist_le` and `edist_le_limit`: γ is c-Lipschitz on (a,b) and
  edist q (γt) ≤ c(b-t).
- Manifold path length vs model length: for a C¹ manifold path staying in the q-chart domain,
  `pathELength ≥ ofReal(mgLength of coordinate curve)` (see Rigidity.lean ~line 700, the
  hgamTlen argument; also `chart_speed_core` in MChartSpeed).  riemannianEDist = edist =
  infimum over C¹ paths (Manifold.exists_lt_locally_constant_of_riemannianEDist_lt gives C¹
  paths of length < edist + eps; riemannianEDist_le_pathELength).

### Step 1 (setup)
γ locally linear speed c on (a,b), limit q at b⁻.  Then γ is continuous on (a,b], γ(b):=q,
and γ is C¹ on (a,b) (apply interior rigidity `Submission.arc_rigidity` at each base point
γ(t0): the exact two-sided window from IsLocLinear plus arc_rigidity's rigid clause gives
γ(t) = ExpM_{γ(t0)}((t−t0)•v) near t0, and these ExpM arcs are C¹ in the ambient charts
(`hcv`/`hExpExpM` structure).  Its manifold speed is constant c.  For t near b⁻, γt ∈ S, so
x(t) := invM(γt) is defined with γt = ExpM(x t), x(t) → 0, and sqrt((ge x0)(x t)(x t)) =
edist q (γt) ≤ c(b−t) (radial identity + lin_tendsto_q_edist_le).

### Step 2 (curve is a model geodesic on a neck — KEY)
Goal: there is m > 0 such that on (b−m,b) the q-chart coordinate curve of γ is a single
model geodesic (flow curve of odeField ge) of speed c; equivalently γ(t) = ExpM((b−t)•V).
Proof plan:
2a. Two-point model geodesics: for model points p = exp(u), p' = exp(w) with u,w in a tiny
ball at 0, there is v (‖v‖ ≤ C·dist) with expOf p Phi tau v = p' (surjectivity of the
per-base exp onto a ball around p, uniform: use the local-diffeomorphism/ball-image facts
`exp_ball_subset_image`, `flow_exp_local_diffeomorphism`, plus the uniform Lipschitz/radii
from `region_flow_pkg`/`uniform_normal_ball_aux`); the model geodesic σ(t) = expOf p Phi tau
(t•v), t∈[0,1], stays inside ball p delta_u ⊆ ball x0 rho_B and has mgLength sqrt((g p) v v).
2b. Any C¹ curve c from p to p' staying inside ball x0 rho_B with ‖...‖ has
mgLength ≥ sqrt((g p) v v) (uniform_normal_ball at base p) with EQUALITY iff c equals σ
(equality case: mgLength = sqrt((g p) v v) = radial coordinate drop at base p; use
`radial_minimality`/hRad at base p and `bilin_cs_eq_colinear` + uniqueness of flow-geodesics).
2c. Manifold transfer: for P = ExpM(u), Q = ExpM(w) small, every manifold C¹ path from P to Q
of length < ρ (small) stays inside the q-metric-ball ⊂ S ⊂ chart domain ("leaving adds
length": paths to radius > R cost ≥ 2R − edist(q,P) − edist(q,Q)); inside the domain,
manifold length ≥ mgLength of the coordinate curve ≥ sqrt((g exp u) v v) (2b).  Consequently
edist(P,Q) ≥ sqrt((g exp u) v v) =: L(u,w), while the lift of σ has length ≤ L(u,w)+eps,
i.e. edist(P,Q) = L(u,w) when both are small enough (attained by the lifted σ, by the
pathELength ≥ mgLength and pathELength ≤ length of lift via chart_speed if needed — carefully
check the two inequalities; the metric ball of radius ρ must sit inside the region where the
chart-speed identity holds, use rhoT).
2d. Exactness of γ windows ⟹ γ is a model geodesic: γ is locally exact with speed c, so on
any pair (s,t) in an exact window, edist(γs,γt) = c(t−s) = L(xs,xt) (2c with P=γs,Q=γt and
L(u,w) = c(t−s)).  Now the model geodesic σ between exp(xs) and exp(xt) lifts to a manifold
path of length exactly c(t−s) = edist, so γ|[s,t] (length c(t−s), staying in the ball) is a
length-minimizer; by the equality case in 2b it equals the lifted σ.  Therefore γ is locally
a model geodesic (in the q-chart) on every small exact window.  Chaining (windows overlap;
locally-model-geodesic curves with exact straddling windows have no corners — if directions
disagreed at an interior point t0, the exact pair (t0−ε,t0+ε) would be shorter than 2cε by
the corner-cut using the model geodesic between γ(t0−ε) and γ(t0+ε), contradicting exactness)
shows γ is ONE model geodesic of speed c on a whole left neck (b−m,b).
2e. Model geodesic ending at x0 is radial: a model-geodesic (flow curve) y(t) with y(t) → x0
as t → b⁻ and constant speed c satisfies y(t) = exp((t−b)•v0) for t near b (radial): because
flow curves extend through x0 (the geodesic field is smooth and y stays bounded near
(x0, velocity c)); by continuity of the flow and the ray agreement
`exp (t•w) = (Phi (x0,w) t).1` (hRay) the extension is exp((t−b)v0); hence γ(t) =
ExpM(x t) = ExpM((b−t)•V) with V := −v0 and sqrt((ge x0) V V) = c.

### Step 3 (assembly)
Output data: from ONE chart_normal_forward destructure re-export ρ0, ge clauses, r, ExpM, S,
invM, radial identity; build ρa and the two-sided arc identity hArcM by copying the first
~610 lines of `Submission/Rigidity.lean` (the proof of `arc_rigidity` up to its `refine`).
Then Step 2 gives the tail clause.  Watch the final output data clauses exactly match the
theorem statement.

CONSTRAINTS: no placeholders/axioms in the final file; build `lake build Submission.NeckCore2`.
Do not edit any other file.
-/

open scoped Manifold ENNReal ContDiff Topology
open Set Filter Metric
open Bundle
open MeasureTheory

namespace Submission
namespace NeckCore2

open Submission.Model

set_option synthInstance.maxHeartbeats 10000000
set_option maxHeartbeats 32000000


theorem neck_rigidity {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    (q : M) (c : NNReal) (hc : 0 < c) :
    ∃ ρ₀ > 0, ∃ ge : E → E →L[ℝ] E →L[ℝ] ℝ,
      ContDiff ℝ 3 ge ∧
      (∀ y u v : E, (ge y) u v = (ge y) v u) ∧
      (∀ y : E, ∀ v : E, v ≠ 0 → 0 < (ge y) v v) ∧
      (∀ y ∈ ball (extChartAt I q q) ρ₀, ∀ u v : E,
         (ge y) u v = (Bundle.RiemannianBundle.g (E := fun x : M => TangentSpace I x)).inner
                       ((extChartAt I q).symm y)
                       ((mfderiv[range I] (extChartAt I q).symm y) u)
                       ((mfderiv[range I] (extChartAt I q).symm y) v)) ∧
      ∃ r > 0, ∃ ExpM : E → M, ∃ S : Set M, ∃ invM : M → E,
        ExpM 0 = q ∧ S ∈ 𝓝 q ∧
        (∀ v ∈ ball (0 : E) r, ExpM v ∈ S) ∧
        ContinuousOn ExpM (ball (0 : E) r) ∧
        Function.Injective (fun v : {v : E // v ∈ ball (0 : E) r} => ExpM v.1) ∧
        Set.SurjOn ExpM (ball (0 : E) r) S ∧
        (∀ y ∈ S, invM y ∈ ball (0 : E) r ∧ ExpM (invM y) = y) ∧
        (∀ v ∈ ball (0 : E) r, invM (ExpM v) = v) ∧
        (∀ v ∈ ball (0 : E) r,
           edist q (ExpM v) = ENNReal.ofReal (Real.sqrt ((ge (extChartAt I q q)) v v))) ∧
        ∃ ρa : ℝ, 0 < ρa ∧ ρa ≤ r ∧
          (∀ (W : E), Real.sqrt ((ge (extChartAt I q q)) W W) = 1 →
            ∀ ⦃s t : ℝ⦄, s ≤ t → |s| < ρa → |t| < ρa →
              edist (ExpM (s • W)) (ExpM (t • W)) = ENNReal.ofReal (t - s)) ∧
          ∀ (a b : ℝ) (hab : a < b) (γ : ℝ → M),
            Metric.IsLocLinear a b c γ →
            Tendsto γ (𝓝[Iio b] b) (𝓝 q) →
            ∃ δ₀ > 0, ∃ V : E, Real.sqrt ((ge (extChartAt I q q)) V V) = c ∧
              ∀ t ∈ Ioo (b - δ₀) b, γ t = ExpM ((b - t) • V) := by
  classical
  let x₀ : E := extChartAt I q q
  rcases chart_normal_forward (I := I) (M := M) q with
    ⟨ρ0, hρ00, ge, hgeC, hgeSymm, hgePos, hgeAgree, hrest⟩
  rcases hrest with ⟨r, hr0, ExpM, S, invM, hExpM0, hSnhds, hS_in, hExpCont, hInj,
    hSurj, hInvS, hInvExp, hRadial, hrest2⟩
  rcases hrest2 with ⟨ρe, hρe0, hρele, τe, hτe0, hρeτe4, Φ, expm, hrest3⟩
  rcases hrest3 with ⟨hExpExpM, hexp0, hExpC1, hΦODE, hexpform, hRay, hrest4⟩
  rcases hrest4 with ⟨hrest4a, hFWD⟩
  rcases hrest4a with ⟨ρT, hρT0, hrest4b⟩
  rcases hrest4b with ⟨hρTle, hrest4c⟩
  rcases hrest4c with ⟨hρTtgt, hcv⟩
  have hBnonneg : ∀ v : E, 0 ≤ (ge x₀) v v := by
    intro v
    by_cases hv : v = 0
    · subst v; simp
    · exact le_of_lt (hgePos x₀ v hv)
  -- uniform Euclidean bound for metric-unit vectors
  rcases unit_norm_bound (ge x₀) (hgePos x₀) with ⟨K, hK0, hKbound⟩
  let hinv : ∀ y : E, (ge y).IsInvertible := fun y => bilin_isInvertible_of_pos (ge y) (hgePos y)
  -- model-level two-sided arc minimality for the chart exponential
  rcases Submission.ArcModel.arc_model_two_sided (g := ge) (hg := hgeC) (hinv := hinv)
      (hsym := hgeSymm) (hpos := hgePos) (x₀ := x₀) (ρe := ρe) (τe := τe) (hρe := hρe0)
      (hτe := hτe0) (hρeτe := hρeτe4) (Φ := Φ) (hΦ := hΦODE) (exp := expm) (hexp0 := hexp0)
      (hexpform := hexpform) (hExpC1 := hExpC1) (K := K) (hK := hK0)
    with ⟨ρA, hρA0, hArc⟩
  -- finite metric-ball radius contained in S
  rcases Metric.nhds_basis_eball.mem_iff.mp hSnhds with ⟨cInf, hcInf0, hcInfsub⟩
  let cf : ℝ≥0∞ := min cInf 1
  have hcf0 : 0 < cf := lt_min hcInf0 (by norm_num)
  have hcflt1 : cf ≤ (1 : ℝ≥0∞) := min_le_right _ _
  have hcftop : cf ≠ (⊤ : ℝ≥0∞) := ne_top_of_le_ne_top (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) hcflt1
  let cp : ℝ := cf.toReal
  have hcp0 : 0 < cp := ENNReal.toReal_pos (ne_of_gt hcf0) hcftop
  have hcp_le_cf : ENNReal.ofReal cp = cf := ENNReal.ofReal_toReal hcftop
  have hcp_sub : {y : M | edist q y < ENNReal.ofReal cp} ⊆ S := by
    intro y hy
    have hdist : edist q y < ENNReal.ofReal cp := hy
    have hdist2 : edist y q < ENNReal.ofReal cp := by simpa [edist_comm] using hdist
    exact hcInfsub (by
      have hle : ENNReal.ofReal cp ≤ cInf := by
        rw [hcp_le_cf]
        exact min_le_left _ _
      exact lt_of_lt_of_le hdist2 hle)
  -- continuity radius: the model exponential sends `ball 0 r₀` into the model region
  -- `ball x₀ ρA` (where the model two-sided lemma applies) and into `ball x₀ ρT`
  have hExpCont0 : ContinuousAt expm (0 : E) := by
    have h0mem : (0 : E) ∈ ball (0 : E) ρe := by simpa using hρe0
    exact (hExpC1.contDiffAt (isOpen_ball.mem_nhds h0mem)).continuousAt
  have hpreA : expm ⁻¹' (ball x₀ ρA) ∈ 𝓝 (0 : E) := by
    exact hExpCont0.preimage_mem_nhds (by
      rw [hexp0]
      exact ball_mem_nhds x₀ hρA0)
  rcases Metric.mem_nhds_iff.mp hpreA with ⟨rA, hrA0, hrA⟩
  have hpreT : expm ⁻¹' (ball x₀ ρT) ∈ 𝓝 (0 : E) := by
    exact hExpCont0.preimage_mem_nhds (by
      rw [hexp0]
      exact ball_mem_nhds x₀ hρT0)
  rcases Metric.mem_nhds_iff.mp hpreT with ⟨rT, hrT0, hrT⟩
  let r₀ : ℝ := min ρe (min rA rT)
  have hr₀pos : 0 < r₀ := by dsimp [r₀]; positivity
  have hr₀ρe : r₀ ≤ ρe := by dsimp [r₀]; exact min_le_left _ _
  have hr₀rA : r₀ ≤ rA := by dsimp [r₀]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hr₀rT : r₀ ≤ rT := by dsimp [r₀]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hExpModelRegion : ∀ v ∈ ball (0 : E) r₀, expm v ∈ ball x₀ ρA := by
    intro v hv
    exact hrA (ball_subset_ball hr₀rA hv)
  have hExpTRegion : ∀ v ∈ ball (0 : E) r₀, expm v ∈ ball x₀ ρT := by
    intro v hv
    exact hrT (ball_subset_ball hr₀rT hv)
  -- metric ball around q inside the coordinate region `ExpM '' ball 0 r₀`
  let c'' : ℝ := min (r₀ / (2 * K)) (cp / 2)
  have hc''pos : 0 < c'' := by
    dsimp [c'']
    exact lt_min (div_pos hr₀pos (by positivity)) (half_pos hcp0)
  have hc''_cp : c'' ≤ cp / 2 := by dsimp [c'']; exact min_le_right _ _
  have hc''_r0 : c'' ≤ r₀ / (2 * K) := by dsimp [c'']; exact min_le_left _ _
  have hballR : {y : M | edist q y < ENNReal.ofReal c''} ⊆ ExpM '' ball (0 : E) r₀ := by
    intro y hy
    have hycp : edist q y < ENNReal.ofReal cp := by
      have hlt : ENNReal.ofReal c'' < ENNReal.ofReal cp := by
        exact (ENNReal.ofReal_lt_ofReal_iff hcp0).mpr (by linarith [hc''_cp, hcp0])
      exact lt_trans hy hlt
    have hyS : y ∈ S := hcp_sub (by simpa [edist_comm] using hycp)
    rcases hInvS y hyS with ⟨hinvball, hExpInv⟩
    have hrad := hRadial (invM y) hinvball
    have hE : edist q y = ENNReal.ofReal (Real.sqrt ((ge x₀) (invM y) (invM y))) := by
      have hrad' := hRadial (invM y) hinvball
      rw [hExpInv] at hrad'
      simpa [x₀] using hrad'
    have hlt2 : ENNReal.ofReal (Real.sqrt ((ge x₀) (invM y) (invM y))) < ENNReal.ofReal c'' := by
      have hy' := hy
      change edist q y < ENNReal.ofReal c'' at hy'
      rwa [hE] at hy'
    have hnorm_g : Real.sqrt ((ge x₀) (invM y) (invM y)) < c'' := by
      exact (ENNReal.ofReal_lt_ofReal_iff hc''pos).mp hlt2
    have hnorm : ‖invM y‖ ≤ K * Real.sqrt ((ge x₀) (invM y) (invM y)) := by
      exact unit_norm_bound_all (ge x₀) (hgePos x₀) K hK0.le (fun V hV => hKbound V hV) (invM y)
    have hltK : K * Real.sqrt ((ge x₀) (invM y) (invM y)) < r₀ := by
      have hKpos : 0 < K := hK0
      have hmul : Real.sqrt ((ge x₀) (invM y) (invM y)) * K < r₀ / 2 := by
        have h1 : Real.sqrt ((ge x₀) (invM y) (invM y)) * K < c'' * K := by
          exact mul_lt_mul_of_pos_right hnorm_g hKpos
        have h2 : c'' * K ≤ (r₀ / (2 * K)) * K := by
          exact mul_le_mul_of_nonneg_right hc''_r0 hKpos.le
        have h3 : (r₀ / (2 * K)) * K = r₀ / 2 := by
          field_simp [ne_of_gt hKpos]
        calc
          Real.sqrt ((ge x₀) (invM y) (invM y)) * K < c'' * K := h1
          _ ≤ (r₀ / (2 * K)) * K := h2
          _ = r₀ / 2 := h3
      calc
        K * Real.sqrt ((ge x₀) (invM y) (invM y)) ≤ r₀ / 2 := by
          have hmul' : Real.sqrt ((ge x₀) (invM y) (invM y)) * K < r₀ / 2 := hmul
          simpa [mul_comm] using (le_of_lt hmul')
        _ < r₀ := by linarith [hr₀pos]
    have hnormlt : ‖invM y‖ < r₀ := lt_of_le_of_lt hnorm hltK
    have hinvmem : invM y ∈ ball (0 : E) r₀ := by
      rw [mem_ball, dist_eq_norm, sub_zero]
      exact hnormlt
    refine ⟨invM y, hinvmem, ?_⟩
    exact hExpInv
  -- small radius ρa (with the new constraints for the two-sided argument)
  let denom : ℝ := K + 3 + 1
  have hdenom0 : 0 < denom := by dsimp [denom]; linarith
  let ρa : ℝ := min (min (cp / denom) (ρe / (K + 1)))
      (min ρA (min (r₀ / (12 * K)) (cp / 8)))
  have hρa0 : 0 < ρa := by
    dsimp [ρa]
    positivity
  have hρa_cp : ρa ≤ cp / denom := by
    dsimp [ρa]
    exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hρa_ρe : ρa ≤ ρe / (K + 1) := by
    dsimp [ρa]
    exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hρa_ρA : ρa ≤ ρA := by
    dsimp [ρa]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hρa_r0 : ρa ≤ r₀ / (12 * K) := by
    dsimp [ρa]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hρa_c8 : ρa ≤ cp / 8 := by
    dsimp [ρa]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hρale_r : ρa ≤ r := by
    have hle1 : ρe / (K + 1) ≤ ρe := by
      rw [div_le_iff₀ (by linarith : 0 < K + 1)]
      nlinarith [hρe0]
    exact le_trans hρa_ρe (le_trans hle1 hρele)
  have hρa_small : ρa * denom ≤ cp := by
    calc
      ρa * denom ≤ (cp / denom) * denom := mul_le_mul_of_nonneg_right hρa_cp (le_of_lt hdenom0)
      _ = cp := by
        field_simp [denom, ne_of_gt hdenom0]
  have h3ρa_c' : 3 * ρa < c'' := by
    have hA : 3 * ρa < r₀ / (2 * K) := by
      have hle : 3 * ρa ≤ 3 * (r₀ / (12 * K)) := by
        exact mul_le_mul_of_nonneg_left hρa_r0 (by norm_num)
      have hlt : 3 * (r₀ / (12 * K)) < r₀ / (2 * K) := by
        have hKpos : 0 < K := hK0
        field_simp [ne_of_gt hKpos, ne_of_gt hr₀pos]
        nlinarith
      linarith
    have hB : 3 * ρa < cp / 2 := by
      have hle : 3 * ρa ≤ 3 * (cp / 8) := by
        exact mul_le_mul_of_nonneg_left hρa_c8 (by norm_num)
      have hlt : 3 * (cp / 8) < cp / 2 := by linarith [hcp0]
      linarith
    have hc''eq : c'' = min (r₀ / (2 * K)) (cp / 2) := rfl
    rw [hc''eq]
    exact lt_min hA hB
  have hArcM : ∀ (W : E), Real.sqrt ((ge x₀) W W) = 1 →
      ∀ ⦃s t : ℝ⦄, s ≤ t → |s| < ρa → |t| < ρa →
        edist (ExpM (s • W)) (ExpM (t • W)) = ENNReal.ofReal (t - s) := by
    intro W hWnorm
    have hWnormleK : ‖W‖ ≤ K := hKbound W hWnorm
    have hWball (aa : ℝ) (haa : |aa| < ρa) : aa • W ∈ ball (0 : E) ρe := by
      rw [mem_ball, dist_eq_norm, sub_zero]
      have hnorm : ‖aa • W‖ ≤ |aa| * K := by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left hWnormleK (abs_nonneg aa)
      have hlt : |aa| * K < ρe := by
        have h1 : |aa| < ρe / (K + 1) := lt_of_lt_of_le haa hρa_ρe
        have h2 : |aa| * (K + 1) < ρe := (lt_div_iff₀ (by linarith : 0 < K + 1)).mp h1
        have h3 : |aa| * K ≤ |aa| * (K + 1) := by
          exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg aa)
        exact lt_of_le_of_lt h3 h2
      exact lt_of_le_of_lt hnorm hlt
    intro s t hst hs ht
    have hstW : t • W ∈ ball (0 : E) ρe := hWball t ht
    have hssW : s • W ∈ ball (0 : E) ρe := hWball s hs
    by_cases hs0 : 0 ≤ s
    · -- forward pair 0 ≤ s ≤ t
      have hd := hFWD W s t hs0 hst hstW
      have hsqrt : Real.sqrt ((ge x₀) W W) = 1 := by simpa [x₀] using hWnorm
      calc
        edist (ExpM (s • W)) (ExpM (t • W))
            = ENNReal.ofReal ((t - s) * Real.sqrt ((ge x₀) W W)) := hd
        _ = ENNReal.ofReal (t - s) := by
          congr 1
          rw [hsqrt]
          ring
    · by_cases ht0 : t ≤ 0
      · -- negative pair s ≤ t ≤ 0; use vector -W with scalars -t ≤ -s
        have hmt : (-s) • (-W) ∈ ball (0 : E) ρe := by
          simpa using hssW
        have hnonneg_neg : 0 ≤ -t := by linarith
        have hle_neg : -t ≤ -s := by linarith
        have hd := hFWD (-W) (-t) (-s) hnonneg_neg hle_neg hmt
        have hsqrt : Real.sqrt ((ge x₀) (-W) (-W)) = 1 := by
          have h' : Real.sqrt ((ge x₀) W W) = 1 := by simpa [x₀] using hWnorm
          rw [← h']
          congr 1
          simp
        calc
          edist (ExpM (s • W)) (ExpM (t • W))
              = edist (ExpM (t • W)) (ExpM (s • W)) := edist_comm _ _
          _ = edist (ExpM ((-t) • (-W))) (ExpM ((-s) • (-W))) := by
                  congr 1 <;> simp [smul_smul]
          _ = ENNReal.ofReal (((-s) - (-t)) * Real.sqrt ((ge x₀) (-W) (-W))) := by
                  simpa [x₀] using hd
          _ = ENNReal.ofReal (t - s) := by
              congr 1
              rw [hsqrt]
              ring
      · -- straddling pair s < 0 < t: upper bound easy (triangle via q), lower bound = core
        have hslt : s < 0 := lt_of_not_ge hs0
        have htp : 0 < t := lt_of_not_ge ht0
        have hsW_r : s • W ∈ ball (0 : E) r := by
          rw [mem_ball, dist_eq_norm, sub_zero]
          have hnorm : ‖s • W‖ ≤ |s| * K := by
            rw [norm_smul, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_left hWnormleK (abs_nonneg s)
          have hlt : |s| * K < ρe := by
            have h1 : |s| < ρe / (K + 1) := lt_of_lt_of_le hs hρa_ρe
            have h2 : |s| * (K + 1) < ρe := (lt_div_iff₀ (by linarith : 0 < K + 1)).mp h1
            have h3 : |s| * K ≤ |s| * (K + 1) := by
              exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg s)
            exact lt_of_le_of_lt h3 h2
          exact lt_of_le_of_lt hnorm (lt_of_lt_of_le hlt hρele)
        have htW_r : t • W ∈ ball (0 : E) r := by
          rw [mem_ball, dist_eq_norm, sub_zero]
          have hnorm : ‖t • W‖ ≤ |t| * K := by
            rw [norm_smul, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_left hWnormleK (abs_nonneg t)
          have hlt : |t| * K < ρe := by
            have h1 : |t| < ρe / (K + 1) := lt_of_lt_of_le ht hρa_ρe
            have h2 : |t| * (K + 1) < ρe := (lt_div_iff₀ (by linarith : 0 < K + 1)).mp h1
            have h3 : |t| * K ≤ |t| * (K + 1) := by
              exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg t)
            exact lt_of_le_of_lt h3 h2
          exact lt_of_le_of_lt hnorm (lt_of_lt_of_le hlt hρele)
        have hnegW : Real.sqrt ((ge x₀) (-W) (-W)) = 1 := by
          have h' : Real.sqrt ((ge x₀) W W) = 1 := by simpa [x₀] using hWnorm
          rw [← h']
          congr 1
          simp
        have hsqrt_s : Real.sqrt ((ge x₀) (s • W) (s • W)) = -s := by
          have hsgn : s • W = (-s) • (-W) := by simp [smul_smul]
          rw [hsgn]
          rw [sqrt_quad_smul_nonneg (ge x₀) (le_of_lt (neg_pos.mpr hslt)) (-W) (hBnonneg (-W))]
          rw [hnegW]
          simp
        have hsqrt_t : Real.sqrt ((ge x₀) (t • W) (t • W)) = t := by
          rw [sqrt_quad_smul_nonneg (ge x₀) (le_of_lt htp) W (hBnonneg W)]
          have hs : Real.sqrt ((ge x₀) W W) = 1 := by simpa [x₀] using hWnorm
          rw [hs]
          simp
        have hds : edist (ExpM (s • W)) q = ENNReal.ofReal (-s) := by
          have hd := hRadial (s • W) hsW_r
          calc
            edist (ExpM (s • W)) q = ENNReal.ofReal (Real.sqrt ((ge x₀) (s • W) (s • W))) := by
                simpa [x₀, edist_comm] using hd
            _ = ENNReal.ofReal (-s) := by rw [hsqrt_s]
        have hdt : edist q (ExpM (t • W)) = ENNReal.ofReal t := by
          have hd := hRadial (t • W) htW_r
          calc
            edist q (ExpM (t • W)) = ENNReal.ofReal (Real.sqrt ((ge x₀) (t • W) (t • W))) := by
                simpa [x₀] using hd
            _ = ENNReal.ofReal t := by rw [hsqrt_t]
        have htri : edist (ExpM (s • W)) (ExpM (t • W)) ≤
            edist (ExpM (s • W)) q + edist q (ExpM (t • W)) :=
          edist_triangle (x := ExpM (s • W)) (y := q) (z := ExpM (t • W))
        have hup : edist (ExpM (s • W)) (ExpM (t • W)) ≤ ENNReal.ofReal (t - s) := by
          calc
            edist (ExpM (s • W)) (ExpM (t • W))
                ≤ edist (ExpM (s • W)) q + edist q (ExpM (t • W)) := htri
            _ = ENNReal.ofReal (-s) + ENNReal.ofReal t := by rw [hds, hdt]
            _ = ENNReal.ofReal (t - s) := by
                have h1 : ENNReal.ofReal (-s) + ENNReal.ofReal t = ENNReal.ofReal (-s + t) := by
                  rw [ENNReal.ofReal_add (le_of_lt (neg_pos.mpr hslt)) (le_of_lt htp)]
                rw [h1]
                congr 1
                ring
        -- lower bound: the deep core (straddling arcs through the base point minimize)
        have hlo : ENNReal.ofReal (t - s) ≤ edist (ExpM (s • W)) (ExpM (t • W)) := by
          by_cases hge : ENNReal.ofReal (t - s) ≤ edist (ExpM (s • W)) (ExpM (t • W))
          · exact hge
          · have hlt : edist (ExpM (s • W)) (ExpM (t • W)) < ENNReal.ofReal (t - s) := lt_of_not_ge hge
            have hlt' : Manifold.riemannianEDist I (ExpM (s • W)) (ExpM (t • W)) < ENNReal.ofReal (t - s) := by
              rwa [← IsRiemannianManifold.out (I := I) (ExpM (s • W)) (ExpM (t • W))]
            rcases Manifold.exists_lt_locally_constant_of_riemannianEDist_lt (I := I) hlt' zero_lt_one with
              ⟨γ, hγ0, hγ1, hγsm, hγlen, hγloc0, hγloc1⟩
            have hγOn (ss : Set ℝ) : ContMDiffOn 𝓘(ℝ,ℝ) I 1 γ ss := hγsm.contMDiffOn
            have hsW_ρe : s • W ∈ ball (0 : E) ρe := hWball s hs
            have htW_ρe : t • W ∈ ball (0 : E) ρe := hWball t ht
            have hExpSrc (v : E) (hv : v ∈ ball (0 : E) ρe) : expm v ∈ ball x₀ ρT := by
              rcases hcv v hv with ⟨cv, velv, hcv0, hcv1, hcvd, hcvsp, hcvstay, hcvO⟩
              have hmem : cv 1 ∈ ball x₀ ρT := hcvstay 1 (by norm_num)
              rwa [hcv1] at hmem
            have hxSrc : ExpM (s • W) ∈ (extChartAt I q).source := by
              have hE : ExpM (s • W) = (extChartAt I q).symm (expm (s • W)) := by
                have := hExpExpM (s • W) hsW_ρe
                simpa using this
              rw [hE]
              exact (extChartAt I q).map_target (hρTtgt (hExpSrc (s • W) hsW_ρe))
            have hySrc : ExpM (t • W) ∈ (extChartAt I q).source := by
              have hE : ExpM (t • W) = (extChartAt I q).symm (expm (t • W)) := by
                have := hExpExpM (t • W) htW_ρe
                simpa using this
              rw [hE]
              exact (extChartAt I q).map_target (hρTtgt (hExpSrc (t • W) htW_ρe))
            -- every point of the short path lies in `ExpM '' ball 0 r₀`
            have hγR : ∀ u ∈ Icc (0 : ℝ) 1, γ u ∈ ExpM '' ball (0 : E) r₀ := by
              intro u hu
              have hlen_u : edist (ExpM (s • W)) (γ u) ≤ Manifold.pathELength I γ 0 1 := by
                have htmp : Manifold.riemannianEDist I (ExpM (s • W)) (γ u) ≤ Manifold.pathELength I γ 0 u :=
                  Manifold.riemannianEDist_le_pathELength (I := I) (hγOn (Icc (0 : ℝ) u)) hγ0 rfl hu.1
                have hmono := htmp.trans (Manifold.pathELength_mono (a := 0) (a' := 0) (b := u) (b' := 1) le_rfl hu.2)
                rwa [← IsRiemannianManifold.out (I := I) (ExpM (s • W)) (γ u)] at hmono
              have htri' : edist q (γ u) ≤ edist q (ExpM (s • W)) + edist (ExpM (s • W)) (γ u) :=
                edist_triangle (x := q) (y := ExpM (s • W)) (z := γ u)
              have hds_comm : edist q (ExpM (s • W)) = ENNReal.ofReal (-s) := by
                simpa [edist_comm] using hds
              have hsum : edist q (ExpM (s • W)) + edist (ExpM (s • W)) (γ u) < ENNReal.ofReal c'' := by
                have hsum_le : edist q (ExpM (s • W)) + edist (ExpM (s • W)) (γ u)
                    ≤ ENNReal.ofReal (-s) + Manifold.pathELength I γ 0 1 := by
                  exact add_le_add (le_of_eq hds_comm) hlen_u
                have hlt_sum : ENNReal.ofReal (-s) + Manifold.pathELength I γ 0 1 < ENNReal.ofReal c'' := by
                  have hlen_lt : Manifold.pathELength I γ 0 1 < ENNReal.ofReal (t - s) := hγlen
                  have hlt2 : ENNReal.ofReal (-s) + Manifold.pathELength I γ 0 1
                      < ENNReal.ofReal (-s) + ENNReal.ofReal (t - s) := by
                    exact ENNReal.add_lt_add_left (by simp) hlen_lt
                  have hsum_eq : ENNReal.ofReal (-s) + ENNReal.ofReal (t - s)
                      = ENNReal.ofReal (t - 2 * s) := by
                    have h1 : ENNReal.ofReal (-s) + ENNReal.ofReal (t - s) = ENNReal.ofReal (-s + (t - s)) := by
                      rw [ENNReal.ofReal_add (le_of_lt (neg_pos.mpr hslt)) (by linarith : 0 ≤ t - s)]
                    rw [h1]
                    congr 1
                    ring
                  have hbound : ENNReal.ofReal (t - 2 * s) < ENNReal.ofReal c'' := by
                    have hreal : t - 2 * s < c'' := by
                      have hA : t < ρa := (abs_lt.mp ht).2
                      have hB : -s < ρa := by linarith [(abs_lt.mp hs).1]
                      have hlt3a : t - 2 * s < 3 * ρa := by linarith
                      exact lt_trans hlt3a h3ρa_c'
                    exact (ENNReal.ofReal_lt_ofReal_iff hc''pos).mpr hreal
                  calc
                    ENNReal.ofReal (-s) + Manifold.pathELength I γ 0 1 < ENNReal.ofReal (-s) + ENNReal.ofReal (t - s) := hlt2
                    _ = ENNReal.ofReal (t - 2 * s) := hsum_eq
                    _ < ENNReal.ofReal c'' := hbound
                exact lt_of_le_of_lt hsum_le hlt_sum
              have hmem : edist q (γ u) < ENNReal.ofReal c'' := lt_of_le_of_lt htri' hsum
              exact hballR hmem
            -- coordinate curve of γ
            have hγsrc : ∀ u ∈ Icc (0 : ℝ) 1, γ u ∈ (extChartAt I q).source := by
              intro u hu
              rcases hγR u hu with ⟨v, hv, hEqv⟩
              have hEqs : γ u = (extChartAt I q).symm (expm v) := by
                have hE : ExpM v = (extChartAt I q).symm (expm v) := by
                  have := hExpExpM v (ball_subset_ball hr₀ρe hv)
                  simpa using this
                rw [← hEqv]
                exact hE
              rw [hEqs]
              exact (extChartAt I q).map_target (hρTtgt (hExpTRegion v hv))
            let ccoor : ℝ → E := fun uu => (extChartAt I q) (γ uu)
            let gamT : ℝ → M := fun uu => (extChartAt I q).symm (ccoor uu)
            have hγeqgamT : Set.EqOn γ gamT (Icc (0 : ℝ) 1) := by
              intro uu huu
              dsimp [gamT, ccoor]
              exact (PartialEquiv.left_inv (extChartAt I q) (hγsrc uu huu)).symm
            have hplEq : Manifold.pathELength I γ 0 1 = Manifold.pathELength I gamT 0 1 :=
              Manifold.pathELength_congr hγeqgamT
            -- ccoor is C¹ on an open set containing [0,1]
            have hOγ : ∃ O : Set ℝ, IsOpen O ∧ Icc (0 : ℝ) 1 ⊆ O ∧ ContDiffOn ℝ 1 ccoor O := by
              let O : Set ℝ := γ ⁻¹' (extChartAt I q).source
              have hγcont : Continuous γ := hγsm.continuous
              have hOopen : IsOpen O := hγcont.isOpen_preimage (extChartAt I q).source
                (isOpen_extChartAt_source (I := I) q)
              have hOIcc : Icc (0 : ℝ) 1 ⊆ O := by
                intro uu huu
                simpa [O] using (hγsrc uu huu)
              have hγOnO : ContMDiffOn 𝓘(ℝ,ℝ) I 1 γ O := hγsm.contMDiffOn
              have hphi : ContMDiffOn I 𝓘(ℝ, E) 1 (extChartAt I q) (chartAt H q).source := by
                have hfull : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I q) (chartAt H q).source :=
                  contMDiffOn_extChartAt (I := I) (x := q)
                exact hfull.of_le (by norm_num : (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω))
              have hsubO : O ⊆ γ ⁻¹' (chartAt H q).source := by
                intro uu huu
                simpa [O, extChartAt_source] using huu
              have hcomp : ContMDiffOn 𝓘(ℝ,ℝ) 𝓘(ℝ,E) 1 ((extChartAt I q) ∘ γ) O := by
                exact ContMDiffOn.comp hphi hγOnO hsubO
              have hcomp' : ContDiffOn ℝ 1 ((extChartAt I q) ∘ γ) O :=
                contMDiffOn_iff_contDiffOn.mp hcomp
              refine ⟨O, hOopen, hOIcc, ?_⟩
              convert hcomp' using 1
              funext uu
              rfl
            -- ccoor endpoints and staying in the model region
            have hccoor0 : ccoor 0 = expm (s • W) := by
              dsimp [ccoor]
              rw [hγ0]
              have hE : ExpM (s • W) = (extChartAt I q).symm (expm (s • W)) := by
                have := hExpExpM (s • W) hsW_ρe
                simpa using this
              rw [hE]
              exact PartialEquiv.right_inv (extChartAt I q) (hρTtgt (hExpSrc (s • W) hsW_ρe))
            have hccoor1 : ccoor 1 = expm (t • W) := by
              dsimp [ccoor]
              rw [hγ1]
              have hE : ExpM (t • W) = (extChartAt I q).symm (expm (t • W)) := by
                have := hExpExpM (t • W) htW_ρe
                simpa using this
              rw [hE]
              exact PartialEquiv.right_inv (extChartAt I q) (hρTtgt (hExpSrc (t • W) htW_ρe))
            have hccoorModel : ∀ uu ∈ Icc (0 : ℝ) 1, ccoor uu ∈ ball x₀ ρA := by
              intro uu huu
              rcases hγR uu huu with ⟨v, hv, hEqv⟩
              have hval : ccoor uu = expm v := by
                dsimp [ccoor]
                have hEqs : γ uu = (extChartAt I q).symm (expm v) := by
                  have hE : ExpM v = (extChartAt I q).symm (expm v) := by
                    have := hExpExpM v (by
                      exact (ball_subset_ball hr₀ρe (by simpa [dist_eq_norm] using hv)))
                    simpa using this
                  rw [← hEqv]
                  exact hE
                rw [hEqs]
                exact PartialEquiv.right_inv (extChartAt I q) (hρTtgt (hExpTRegion v hv))
              rw [hval]
              exact hExpModelRegion v hv
            have hccoorAgree : ∀ uu ∈ Icc (0 : ℝ) 1, ccoor uu ∈ ball x₀ ρT := by
              intro uu huu
              rcases hγR uu huu with ⟨v, hv, hEqv⟩
              have hval : ccoor uu = expm v := by
                dsimp [ccoor]
                have hEqs : γ uu = (extChartAt I q).symm (expm v) := by
                  have hE : ExpM v = (extChartAt I q).symm (expm v) := by
                    have := hExpExpM v (by
                      exact (ball_subset_ball hr₀ρe (by simpa [dist_eq_norm] using hv)))
                    simpa using this
                  rw [← hEqv]
                  exact hE
                rw [hEqs]
                exact PartialEquiv.right_inv (extChartAt I q) (hρTtgt (hExpTRegion v hv))
              rw [hval]
              exact hExpTRegion v hv
            -- model-level staying minimality
            have hmg : t - s ≤ Model.mgLength ge ccoor 0 1 := by
              have hsltA : |s| < ρA := lt_of_lt_of_le hs hρa_ρA
              have htltA : |t| < ρA := lt_of_lt_of_le ht hρa_ρA
              have hWbound : ‖W‖ ≤ K := hWnormleK
              have hs1 : Real.sqrt ((ge x₀) W W) = 1 := by simpa [x₀] using hWnorm
              have hmain := hArc W hWbound hs1 s t hst hsltA htltA ccoor hccoor0 hccoor1 hOγ hccoorModel
              simpa [hs1] using hmain
            -- pathELength of gamT ≥ ofReal (mgLength ge ccoor)
            have hgamTlen : ENNReal.ofReal (Model.mgLength ge ccoor 0 1) ≤ Manifold.pathELength I gamT 0 1 := by
              let sp : ℝ → ℝ := fun uu => Real.sqrt ((ge (ccoor uu)) (deriv ccoor uu) (deriv ccoor uu))
              have hsp0 : ∀ uu, 0 ≤ sp uu := fun uu => Real.sqrt_nonneg _
              have hIoo_ae : (Ioo (0 : ℝ) 1) =ᵐ[MeasureTheory.volume] (Icc (0 : ℝ) 1) :=
                (MeasureTheory.Ioo_ae_eq_Ioc (a := (0:ℝ)) (b := (1:ℝ))).trans
                  (MeasureTheory.Ioc_ae_eq_Icc (a := (0:ℝ)) (b := (1:ℝ)))
              have h1 : Manifold.pathELength I gamT 0 1 = ∫⁻ uu in Ioo (0 : ℝ) 1, ‖(mfderiv% gamT uu) 1‖ₑ := by
                rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
                exact (setLIntegral_congr (s := Icc (0 : ℝ) 1) (t := Ioo (0 : ℝ) 1) hIoo_ae.symm)
              have h2 : (∫⁻ uu in Ioo (0 : ℝ) 1, ‖(mfderiv% gamT uu) 1‖ₑ)
                  = ∫⁻ uu in Ioo (0 : ℝ) 1, ENNReal.ofReal (sp uu) := by
                refine setLIntegral_congr_fun measurableSet_Ioo ?_
                intro uu huu
                dsimp [sp]
                have huucc : uu ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt huu.1, le_of_lt huu.2⟩
                have hγe : ∀ uu2 : ℝ, gamT uu2 = (extChartAt I q).symm (ccoor uu2) := by
                  intro uu2
                  rfl
                rcases hOγ with ⟨O, hOopen, hOIcc, hCcoor⟩
                have hder : HasDerivAt ccoor (deriv ccoor uu) uu := by
                  have hOmem : O ∈ 𝓝 uu := hOopen.mem_nhds (hOIcc huucc)
                  have hdf : DifferentiableAt ℝ ccoor uu :=
                    (hCcoor.differentiableOn (by norm_num : (1 : ℕ∞ω) ≠ 0)).differentiableAt hOmem
                  exact hdf.hasDerivAt
                have hagree : ∀ y ∈ ball x₀ ρT, ∀ uu2 vv : E,
                    (ge y) uu2 vv = (Bundle.RiemannianBundle.g (E := fun x : M => TangentSpace I x)).inner
                      ((extChartAt I q).symm y)
                      ((mfderiv[range I] (extChartAt I q).symm y) uu2)
                      ((mfderiv[range I] (extChartAt I q).symm y) vv) := by
                  intro y hy uu2 vv
                  exact hgeAgree y (ball_subset_ball hρTle hy) uu2 vv
                have hspd := chart_speed_core (I := I) (M := M) q (ρ := ρT) (ge := ge) hagree hρTtgt
                  (γ := gamT) (c := ccoor) (t := uu) (u := deriv ccoor uu) hγe (hccoorAgree uu huucc) hder
                exact hspd
              have hspcont : ContinuousOn sp (Ioo (0 : ℝ) 1) := by
                rcases hOγ with ⟨O0, hO0open, hO0Icc, hCcoor0⟩
                have hsub : Ioo (0 : ℝ) 1 ⊆ O0 := fun uu huu => hO0Icc ⟨le_of_lt huu.1, le_of_lt huu.2⟩
                have hderCont : ContinuousOn (fun uu : ℝ => deriv ccoor uu) O0 :=
                  deriv_contDiffOn_contOn hCcoor0 hO0open
                have hcc : ContinuousOn ccoor O0 := hCcoor0.continuousOn
                have hccIoo : ContinuousOn ccoor (Ioo (0 : ℝ) 1) := hcc.mono hsub
                have hdIoo : ContinuousOn (fun uu : ℝ => deriv ccoor uu) (Ioo (0 : ℝ) 1) :=
                  hderCont.mono hsub
                have hg : ContinuousOn (fun uu : ℝ => ge (ccoor uu)) (Ioo (0 : ℝ) 1) := by
                  have hgfull : Continuous ge := hgeC.continuous
                  have hgo : ContinuousOn ge univ := hgfull.continuousOn
                  exact ContinuousOn.comp hgo hccIoo (by intro uu huu; trivial)
                have hq1 : ContinuousOn (fun uu : ℝ => (ge (ccoor uu)) (deriv ccoor uu)) (Ioo (0 : ℝ) 1) :=
                  ContinuousOn.clm_apply hg hdIoo
                have hq2 : ContinuousOn (fun uu : ℝ => ((ge (ccoor uu)) (deriv ccoor uu)) (deriv ccoor uu))
                    (Ioo (0 : ℝ) 1) := ContinuousOn.clm_apply hq1 hdIoo
                have hsp0' : sp = fun uu : ℝ => Real.sqrt (((ge (ccoor uu)) (deriv ccoor uu)) (deriv ccoor uu)) := by
                  rfl
                rw [hsp0']
                exact hq2.sqrt
              have hspmeas : AEStronglyMeasurable sp (MeasureTheory.volume.restrict (Ioo (0 : ℝ) 1)) :=
                hspcont.aestronglyMeasurable measurableSet_Ioo
              have h3 : ENNReal.ofReal (∫ uu in Ioo (0 : ℝ) 1, sp uu)
                  ≤ ∫⁻ uu in Ioo (0 : ℝ) 1, ENNReal.ofReal (sp uu) := by
                let μ : Measure ℝ := MeasureTheory.volume.restrict (Ioo (0 : ℝ) 1)
                change ENNReal.ofReal (∫ x, sp x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (sp x) ∂μ
                have hmeas : AEStronglyMeasurable sp μ := by
                  simpa [μ] using hspmeas
                by_cases hfi : Integrable sp μ
                · have hE := MeasureTheory.integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hsp0) hmeas
                  rw [hE]
                  exact ENNReal.ofReal_toReal_le (a := (∫⁻ x, ENNReal.ofReal (sp x) ∂μ))
                · have hz : (∫ x, sp x ∂μ) = 0 := integral_undef hfi
                  rw [hz]
                  simp
              have h4 : Model.mgLength ge ccoor 0 1 = ∫ uu in Ioo (0 : ℝ) 1, sp uu := by
                unfold Model.mgLength Model.mgSpeed
                rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
                have hrest : MeasureTheory.volume.restrict (Ioo (0 : ℝ) 1) =
                    MeasureTheory.volume.restrict (Ioc (0 : ℝ) 1) := by
                  exact MeasureTheory.Measure.restrict_congr_set
                    (MeasureTheory.Ioo_ae_eq_Ioc (a := (0:ℝ)) (b := (1:ℝ)))
                calc
                  (∫ uu in Ioc (0 : ℝ) 1, Real.sqrt ((ge (ccoor uu)) (deriv ccoor uu) (deriv ccoor uu)))
                      = ∫ uu, Real.sqrt ((ge (ccoor uu)) (deriv ccoor uu) (deriv ccoor uu)) ∂(MeasureTheory.volume.restrict (Ioc (0 : ℝ) 1)) := rfl
                  _ = ∫ uu, Real.sqrt ((ge (ccoor uu)) (deriv ccoor uu) (deriv ccoor uu)) ∂(MeasureTheory.volume.restrict (Ioo (0 : ℝ) 1)) := by
                      rw [hrest]
                  _ = ∫ uu in Ioo (0 : ℝ) 1, Real.sqrt ((ge (ccoor uu)) (deriv ccoor uu) (deriv ccoor uu)) := rfl
              have hmg' : ENNReal.ofReal (Model.mgLength ge ccoor 0 1) ≤
                  ∫⁻ uu in Ioo (0 : ℝ) 1, ENNReal.ofReal (sp uu) := by
                rw [h4]
                change ENNReal.ofReal (∫ uu in Ioo (0 : ℝ) 1,
                  Real.sqrt ((ge (ccoor uu)) (deriv ccoor uu) (deriv ccoor uu)))
                    ≤ ∫⁻ uu in Ioo (0 : ℝ) 1, ENNReal.ofReal
                      (Real.sqrt ((ge (ccoor uu)) (deriv ccoor uu) (deriv ccoor uu)))
                exact h3
              calc
                ENNReal.ofReal (Model.mgLength ge ccoor 0 1) ≤
                    ∫⁻ uu in Ioo (0 : ℝ) 1, ENNReal.ofReal (sp uu) := hmg'
                _ = ∫⁻ uu in Ioo (0 : ℝ) 1, ‖(mfderiv% gamT uu) 1‖ₑ := h2.symm
                _ = Manifold.pathELength I gamT 0 1 := h1.symm
            have hcontra : ENNReal.ofReal (t - s) ≤ Manifold.pathELength I γ 0 1 := by
              calc
                ENNReal.ofReal (t - s) ≤ ENNReal.ofReal (Model.mgLength ge ccoor 0 1) := by
                  exact ENNReal.ofReal_le_ofReal hmg
                _ ≤ Manifold.pathELength I gamT 0 1 := hgamTlen
                _ = Manifold.pathELength I γ 0 1 := hplEq.symm
            exact False.elim ((lt_of_le_of_lt hcontra hγlen).ne rfl)
        exact le_antisymm hup hlo

  refine ⟨ρ0, hρ00, ge, hgeC, hgeSymm, hgePos, hgeAgree, ⟨r, hr0, ExpM, S, invM,
    hExpM0, hSnhds, hS_in, hExpCont, hInj, hSurj, hInvS, hInvExp, hRadial,
    ⟨ρa, hρa0, hρale_r, hArcM, ?rigid⟩⟩⟩

  -- ============================================================
  -- TAIL part (development placeholder)
  -- ============================================================
  intro a b hab γ hγ hγq
  -- real speed
  let cR : ℝ := (c : ℝ)
  have hcR0 : 0 < cR := by exact_mod_cast hc
  have hcR_nonneg : 0 ≤ cR := le_of_lt hcR0
  have hEdist_le : ∀ t ∈ Ioo a b, edist q (γ t) ≤ (c : ℝ≥0∞) * ENNReal.ofReal (b - t) :=
    lin_tendsto_q_edist_le (a := a) (b := b) (c := c) (γ := γ) (q := q) hab hγ hγq
  have hcoe : (c : ℝ≥0∞) = ENNReal.ofReal (c : ℝ) := (ENNReal.ofReal_coe_nnreal).symm
  have hEdist_real (t : ℝ) (ht : t ∈ Ioo a b) : edist q (γ t) ≤ ENNReal.ofReal (cR * (b - t)) := by
    have hE := hEdist_le t ht
    calc
      edist q (γ t) ≤ (c : ℝ≥0∞) * ENNReal.ofReal (b - t) := hE
      _ = ENNReal.ofReal (cR * (b - t)) := by
        rw [hcoe]
        rw [ENNReal.ofReal_mul hcR_nonneg]
  have htoReal_le {r : ℝ} (hr : 0 ≤ r) {A : ℝ≥0∞} (hA : A ≤ ENNReal.ofReal r) (hfin : A ≠ ⊤) :
      ENNReal.toReal A ≤ r := by
    have hfino : (ENNReal.ofReal r) ≠ ⊤ := ne_of_lt ENNReal.ofReal_lt_top
    have hle : ENNReal.toReal A ≤ ENNReal.toReal (ENNReal.ofReal r) :=
      (ENNReal.toReal_le_toReal hfin hfino).mpr hA
    rwa [ENNReal.toReal_ofReal hr] at hle
  have hcp_sub_S : {y : M | edist q y < ENNReal.ofReal cp} ⊆ S := hcp_sub
  have hKp1 : 0 < K + 1 := by linarith
  -- smallness thresholds (positive)
  let νx : ℝ := ρe / (K + 1)
  have hνx0 : 0 < νx := by positivity
  let νtot : ℝ := min cp (min νx (cR * (b - a) / 2))
  have hνtot0 : 0 < νtot := by
    dsimp [νtot]
    exact lt_min hcp0 (lt_min hνx0 (by positivity))
  have hνtot_le_γ : νtot ≤ cp := by dsimp [νtot]; exact min_le_left _ _
  have hνtot_le_x : νtot ≤ νx := by dsimp [νtot]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hνtot_bnd : νtot ≤ cR * (b - a) / 2 := by dsimp [νtot]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  -- neck base point
  let t2 : ℝ := b - νtot / (2 * cR)
  have hν_lt_ba : νtot / (2 * cR) < b - a := by
    have hpos : 0 < 2 * cR := by positivity
    have hd : νtot / (2 * cR) ≤ (cR * (b - a) / 2) / (2 * cR) :=
      div_le_div_of_nonneg_right hνtot_bnd (le_of_lt hpos)
    have hstep : (cR * (b - a) / 2) / (2 * cR) = (b - a) / 4 := by
      field_simp [ne_of_gt hcR0]
      ring
    have hsmall : (b - a) / 4 < b - a := by
      have hba : 0 < b - a := sub_pos.mpr hab
      linarith
    exact lt_of_le_of_lt hd (by rw [hstep]; exact hsmall)
  have ht2_a : a < t2 := by
    dsimp [t2]
    linarith
  have ht2_b : t2 < b := by
    dsimp [t2]
    have hpos : 0 < νtot / (2 * cR) := by positivity
    linarith
  have hneck_c : ∀ t ∈ Ioo t2 b, cR * (b - t) < νtot := by
    intro t ht
    have hbt : b - t < νtot / (2 * cR) := by
      dsimp [t2] at ht
      linarith [ht.1]
    have hmul : cR * (b - t) < cR * (νtot / (2 * cR)) := mul_lt_mul_of_pos_left hbt hcR0
    have hstep : cR * (νtot / (2 * cR)) = νtot / 2 := by
      field_simp [ne_of_gt hcR0]
    rw [hstep] at hmul
    exact lt_trans hmul (by linarith [hνtot0])
  -- γ stays inside S on the neck
  have hγS_neck : ∀ t ∈ Ioo t2 b, γ t ∈ S := by
    intro t ht
    have htab : t ∈ Ioo a b := ⟨lt_trans ht2_a ht.1, ht.2⟩
    have h1 : edist q (γ t) ≤ ENNReal.ofReal (cR * (b - t)) := hEdist_real t htab
    have h2 : cR * (b - t) < cp := lt_of_lt_of_le (hneck_c t ht) hνtot_le_γ
    have hlt : edist q (γ t) < ENNReal.ofReal cp :=
      lt_of_le_of_lt h1 ((ENNReal.ofReal_lt_ofReal_iff hcp0).mpr h2)
    exact hcp_sub_S hlt
  -- x(t) := invM (γ t); basic facts
  let x : ℝ → E := fun t => invM (γ t)
  have hxS {t : ℝ} (ht : t ∈ Ioo t2 b) : x t ∈ ball (0 : E) r := by
    exact (hInvS (γ t) (hγS_neck t ht)).1
  have hxExp {t : ℝ} (ht : t ∈ Ioo t2 b) : ExpM (x t) = γ t := by
    exact (hInvS (γ t) (hγS_neck t ht)).2
  have hsqrt_eq {t : ℝ} (ht : t ∈ Ioo t2 b) :
      Real.sqrt ((ge x₀) (x t) (x t)) = ENNReal.toReal (edist q (γ t)) := by
    have hxr : x t ∈ ball (0 : E) r := hxS ht
    have hrad := hRadial (x t) hxr
    have hto : edist q (γ t) = ENNReal.ofReal (Real.sqrt ((ge x₀) (x t) (x t))) := by
      rw [← hxExp ht]
      simpa [x₀] using hrad
    rw [hto]
    exact (ENNReal.toReal_ofReal (Real.sqrt_nonneg _)).symm
  have hx_ρ {t : ℝ} (ht : t ∈ Ioo t2 b) : Real.sqrt ((ge x₀) (x t) (x t)) ≤ cR * (b - t) := by
    have htab : t ∈ Ioo a b := ⟨lt_trans ht2_a ht.1, ht.2⟩
    have hle : ENNReal.toReal (edist q (γ t)) ≤ cR * (b - t) := by
      have hb : 0 ≤ cR * (b - t) := mul_nonneg hcR_nonneg (le_of_lt (sub_pos.mpr ht.2))
      exact htoReal_le (r := cR * (b - t)) hb (hEdist_real t htab)
        (ne_top_of_lt (lt_of_le_of_lt (hEdist_real t htab) ENNReal.ofReal_lt_top))
    rw [hsqrt_eq ht]
    exact hle
  have hxballρe {t : ℝ} (ht : t ∈ Ioo t2 b) : x t ∈ ball (0 : E) ρe := by
    rw [mem_ball, dist_eq_norm, sub_zero]
    have hKnn : 0 ≤ K := le_of_lt hK0
    have hnb : ‖x t‖ ≤ K * Real.sqrt ((ge x₀) (x t) (x t)) := by
      exact unit_norm_bound_all (ge x₀) (hgePos x₀) K hKnn (fun V hV => hKbound V hV) (x t)
    have hsq_lt : Real.sqrt ((ge x₀) (x t) (x t)) < νx := by
      have h1 := hx_ρ ht
      have h2 : cR * (b - t) < νx := lt_of_lt_of_le (hneck_c t ht) hνtot_le_x
      exact lt_of_le_of_lt h1 h2
    have hKsq : K * Real.sqrt ((ge x₀) (x t) (x t)) < K * νx :=
      mul_lt_mul_of_pos_left hsq_lt hK0
    have hKνx : K * νx < ρe := by
      dsimp [νx]
      have hmain : K * (ρe / (K + 1)) < ρe := by
        have heq : K * (ρe / (K + 1)) = (K * ρe) / (K + 1) := by
          ring
        rw [heq]
        rw [div_lt_iff₀ hKp1]
        nlinarith [hρe0, hK0]
      exact hmain
    exact lt_of_le_of_lt hnb (lt_trans hKsq hKνx)
  -- C(t) := expm (x t) = chart (γ t) lies in ball x₀ ρT
  let C : ℝ → E := fun t => expm (x t)
  have hC_in_ballT {t : ℝ} (ht : t ∈ Ioo t2 b) : C t ∈ ball x₀ ρT := by
    dsimp [C]
    rcases hcv (x t) (hxballρe ht) with ⟨cv, velv, hcv0, hcv1, hcvd, hcvsp, hcvstay, hcvform⟩
    have hmem : cv 1 ∈ ball x₀ ρT := hcvstay 1 (by norm_num)
    rwa [hcv1] at hmem
  have hC_chart {t : ℝ} (ht : t ∈ Ioo t2 b) : (extChartAt I q) (γ t) = C t := by
    have hE : ExpM (x t) = (extChartAt I q).symm (expm (x t)) := by
      have hmem : x t ∈ ball (0 : E) ρe := hxballρe ht
      have hh := hExpExpM (x t) hmem
      simpa using hh
    have hCtarget : C t ∈ (extChartAt I q).target := hρTtgt (hC_in_ballT ht)
    have hEq : γ t = (extChartAt I q).symm (C t) := by
      calc
        γ t = ExpM (x t) := (hxExp ht).symm
        _ = (extChartAt I q).symm (expm (x t)) := hE
        _ = (extChartAt I q).symm (C t) := by rfl
    calc
      (extChartAt I q) (γ t) = (extChartAt I q) ((extChartAt I q).symm (C t)) := by rw [hEq]
      _ = C t := PartialEquiv.right_inv (extChartAt I q) hCtarget
  -- ---------------------------------------------------------------
  -- uniform per-base exponential data near x0 (region flow of ge)
  -- ---------------------------------------------------------------
  have hKnn : 0 ≤ K := le_of_lt hK0
  let R0n : NNReal := 2
  have hR0ge2 : (2 : ℝ) ≤ (R0n : ℝ) := by norm_num
  rcases Submission.Model.region_flow_pkg (g := ge) (hg := hgeC) (hinv := hinv)
      x₀ R0n hR0ge2 with ⟨τf, hτf, ρu, hρu, Lf, Φr, hΦrAll, hCon2r, hLip1r, hLipBr, hPerBr⟩
  rcases Submission.NeckEq.neck_package (g := ge) (hg := hgeC) (hinv := hinv)
      (hsym := hgeSymm) (hpos := hgePos) x₀ (ρu := ρu) (τf := τf) (hρu := hρu) (hτf := hτf)
      (Lf := Lf) (Φ := Φr) (hPerBase := hPerBr) (hLip := hLipBr)
    with ⟨ρB, δu, τu, ρE, K0, hρB0, hδu0, hτu0, hρE0, hK0nn, hρBρu, hδuρE, h4ρEτu, h8τuτf,
      hKbigP, hUbP, hpkg⟩
  have hδuτu : δu ≤ τu := by linarith [h4ρEτu, hδuρE]
  -- C(t) → x0 as t → b⁻ (within the neck)
  -- ------------------------------------------------------------------
  -- ------------------------------------------------------------------
  -- P1: interior-rigidity window at each t0 of the neck with the FULL smooth data at
  -- p := γ t0: ExpMp = chart_p⁻¹ ∘ exp_p with exp_p C¹, and γ(t0+u) = ExpMp(u·vp).
  -- ------------------------------------------------------------------
  have hP1 (t0 : ℝ) (ht0 : t0 ∈ Ioo t2 b) :
      ∃ ε > 0, ε ≤ (t0 - t2) / 2 ∧ ε ≤ (b - t0) / 2 ∧
        ∃ (x0p : E) (ExpMp : E → M) (gep : E → E →L[ℝ] E →L[ℝ] ℝ) (ρep : ℝ) (exp_p : E → E) (vp : E),
          Real.sqrt ((gep x0p) vp vp) = cR ∧
          (∀ v ∈ ball (0 : E) ρep, ExpMp v = (extChartAt I (γ t0)).symm (exp_p v)) ∧
          exp_p 0 = x0p ∧ ContDiffOn ℝ 1 exp_p (ball (0 : E) ρep) ∧
          (∀ t ∈ Ioo (t0 - ε) (t0 + ε), (t - t0) • vp ∈ ball (0 : E) ρep) ∧
          (∀ t ∈ Ioo (t0 - ε) (t0 + ε), γ t = ExpMp ((t - t0) • vp)) := by
    rcases hγ t0 (show t0 ∈ Ioo a b from ⟨lt_trans ht2_a ht0.1, ht0.2⟩) with ⟨δ₀, hδ₀, hwin⟩
    rcases Submission.NeckSmooth.rigid_smooth (I := I) (M := M) (p := γ t0) with
      ⟨ρ0p, hρ0p0, gep, hgepC, hgepSymm, hgepPos, hgepAgree, hrestp⟩
    rcases hrestp with ⟨rp, hrp0, ExpMp, Sp, invMp, hExpMp0, hSpnhds, hSp_in, hExpMpCont, hInjp,
      hSurjp, hInvSp, hInvExpp, hRadialp, hrestp2⟩
    rcases hrestp2 with ⟨ρap, hρap0, hρap_le_rp, hArcMp, hrestp3⟩
    rcases hrestp3 with ⟨hmodp, hRigidp⟩
    rcases hmodp with ⟨ρep, hρep0, hρep_le_rp, τep, hτep0, Φp, exp_p, hExpExpMp, hexp0p, hExpC1p, hExpformp⟩
    let x0p : E := extChartAt I (γ t0) (γ t0)
    rcases unit_norm_bound (gep x0p) (hgepPos x0p) with ⟨Kp, hKp0, hKpbound⟩
    let ε : ℝ := min (δ₀ / 2) (min ((t0 - t2) / 2)
      (min ((b - t0) / 2) (min (ρap / (2 * cR)) (ρep / (2 * (Kp + 1) * (cR + 1))))))
    have hε0 : 0 < ε := by
      dsimp [ε]
      refine lt_min (half_pos hδ₀) (lt_min (half_pos (by linarith [ht0.1])) (lt_min
        (half_pos (sub_pos.mpr ht0.2)) (lt_min (div_pos hρap0 (by positivity)) (by positivity))))
    have hεδ : ε ≤ δ₀ / 2 := by dsimp [ε]; exact min_le_left _ _
    have hεt2 : ε ≤ (t0 - t2) / 2 := by dsimp [ε]; exact le_trans (min_le_right _ _) (min_le_left _ _)
    have hεb : ε ≤ (b - t0) / 2 := by dsimp [ε]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    have hερa : ε ≤ ρap / (2 * cR) := by dsimp [ε]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
    have hερep : ε ≤ ρep / (2 * (Kp + 1) * (cR + 1)) := by dsimp [ε]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
    have hcRε : cR * ε ≤ ρap := by
      have hle : cR * ε ≤ cR * (ρap / (2 * cR)) := mul_le_mul_of_nonneg_left hερa hcR_nonneg
      have hstep : cR * (ρap / (2 * cR)) = ρap / 2 := by
        field_simp [ne_of_gt hcR0]
      rw [hstep] at hle
      exact le_trans hle (by linarith [hρap0])
    have hWinMem (u : ℝ) (hu : |u| < ε) : t0 + u ∈ Ioo (max a (t0 - δ₀)) (min b (t0 + δ₀)) := by
      have hu_δ : |u| < δ₀ := lt_of_lt_of_le hu (le_trans hεδ (le_of_lt (half_lt_self hδ₀)))
      have hu_t2 : |u| < (t0 - t2) / 2 := lt_of_lt_of_le hu hεt2
      have hu_b : |u| < (b - t0) / 2 := lt_of_lt_of_le hu hεb
      constructor
      · apply max_lt
        · have hstep : t0 - (t0 - t2) / 2 < t0 + u := by linarith [abs_lt.mp hu_t2 |>.1]
          have ha : a < t0 - (t0 - t2) / 2 := by linarith [ht2_a, ht0.1]
          linarith
        · have hu_lo : -δ₀ < u := by linarith [abs_lt.mp hu_δ |>.1]
          linarith
      · apply lt_min
        · have hstep : t0 + u < t0 + (b - t0) / 2 := by linarith [abs_lt.mp hu_b |>.2]
          have hbb : t0 + (b - t0) / 2 < b := by linarith
          linarith
        · have hu_hi : u < δ₀ := abs_lt.mp hu_δ |>.2
          linarith
    have hexact : ∀ u v : ℝ, |u| < ε → |v| < ε →
        edist (γ (t0 + u)) (γ (t0 + v)) = (c : ℝ≥0∞) * ENNReal.ofReal |v - u| := by
      intro u v hu hv
      have hd := hwin (t0 + u) (t0 + v) (hWinMem u hu) (hWinMem v hv)
      simpa using hd
    have hγ0r : (fun u : ℝ => γ (t0 + u)) 0 = γ t0 := by simp
    have hrigid := hRigidp c hc (fun u : ℝ => γ (t0 + u)) ε hγ0r hε0 hcRε hexact
    rcases hrigid with ⟨vp, hvp, hvpcurve⟩
    have hvp_euc : ‖vp‖ ≤ Kp * cR := by
      have h1 := unit_norm_bound_all (gep x0p) (hgepPos x0p) Kp hKp0.le (fun V hV => hKpbound V hV) vp
      have hsq : Real.sqrt ((gep x0p) vp vp) = cR := by simpa [x0p] using hvp
      rw [hsq] at h1
      exact h1
    have hmem (u : ℝ) (hu : |u| < ε) : u • vp ∈ ball (0 : E) ρep := by
      rw [mem_ball, dist_eq_norm, sub_zero]
      rw [norm_smul, Real.norm_eq_abs]
      have h1 : |u| < ρep / (2 * (Kp + 1) * (cR + 1)) := lt_of_lt_of_le hu hερep
      have hmain : |u| * ((Kp + 1) * (cR + 1)) < ρep := by
        have hposA : 0 < (Kp + 1) * (cR + 1) := by positivity
        have h5 : |u| * ((Kp + 1) * (cR + 1)) < (ρep / (2 * (Kp + 1) * (cR + 1))) * ((Kp + 1) * (cR + 1)) := by
          exact mul_lt_mul_of_pos_right h1 hposA
        have h6 : (ρep / (2 * (Kp + 1) * (cR + 1))) * ((Kp + 1) * (cR + 1)) = ρep / 2 := by
          field_simp [ne_of_gt hρep0]
        rw [h6] at h5
        exact lt_trans h5 (by linarith [hρep0])
      have hle1 : |u| * ‖vp‖ ≤ |u| * ((Kp + 1) * (cR + 1)) := by
        have h3 : ‖vp‖ ≤ (Kp + 1) * (cR + 1) := by nlinarith [hvp_euc, hKp0, hcR0]
        exact mul_le_mul_of_nonneg_left h3 (abs_nonneg u)
      have hle2 : |u| * ‖vp‖ < ρep := lt_of_le_of_lt hle1 hmain
      simpa [mul_comm, mul_left_comm, mul_assoc] using hle2
    refine ⟨ε, hε0, hεt2, hεb, x0p, ExpMp, gep, ρep, exp_p, vp, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [x0p] using hvp
    · intro v hv
      exact hExpExpMp v hv
    · exact hexp0p
    · exact hExpC1p
    · intro t ht
      have hu : |t - t0| < ε := by
        rw [abs_lt]
        constructor <;> linarith [ht.1, ht.2]
      exact hmem (t - t0) hu
    · intro t ht
      have hu : |t - t0| < ε := by
        rw [abs_lt]
        constructor <;> linarith [ht.1, ht.2]
      simpa using (hvpcurve (t - t0) hu)
  -- ============================================================
  -- TAIL: prove the model-geodesic (flow) structure of C on a left neck, then use
  -- `flow_limit_ray` to conclude C is an expm-ray and γ is the ExpM-ray.
  -- ============================================================
  -- ============================================================
  -- TAIL: prove the model-geodesic (flow) structure of C on a left neck, then use
  -- `flow_limit_ray` to conclude C is an expm-ray and γ is the ExpM-ray.
  -- ============================================================
  -- (s0) C(t) → x0 as t → b⁻ (within the neck (t2,b)).
  have hIoo_nhds : Ioo t2 b ∈ 𝓝[Iio b] b := by
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    refine ⟨Ioi t2, isOpen_Ioi.mem_nhds ht2_b, ?_⟩
    intro y hy
    exact ⟨hy.1, hy.2⟩
  have hC_tend : Tendsto C (𝓝[Iio b] b) (𝓝 x₀) := by
    -- C t = expm (x t); x t → 0 (squeeze ‖x t‖ ≤ K*cR*(b−t)) and expm continuous at 0.
    have hx_tend0 : Tendsto x (𝓝[Iio b] b) (𝓝 (0 : E)) := by
      have hnonneg : ∀ᶠ t in 𝓝[Iio b] b, (0 : ℝ) ≤ ‖x t‖ := by
        filter_upwards with t
        exact norm_nonneg _
      have hub : ∀ᶠ t in 𝓝[Iio b] b, ‖x t‖ ≤ K * cR * (b - t) := by
        filter_upwards [hIoo_nhds] with t ht
        have hKnn : 0 ≤ K := le_of_lt hK0
        have hnb : ‖x t‖ ≤ K * Real.sqrt ((ge x₀) (x t) (x t)) := by
          exact unit_norm_bound_all (ge x₀) (hgePos x₀) K hKnn (fun V hV => hKbound V hV) (x t)
        have hle1 : K * Real.sqrt ((ge x₀) (x t) (x t)) ≤ K * (cR * (b - t)) := by
          exact mul_le_mul_of_nonneg_left (hx_ρ ht) hKnn
        calc
          ‖x t‖ ≤ K * Real.sqrt ((ge x₀) (x t) (x t)) := hnb
          _ ≤ K * (cR * (b - t)) := hle1
          _ = K * cR * (b - t) := by ring
      have hz : Tendsto (fun t : ℝ => (0 : ℝ)) (𝓝[Iio b] b) (𝓝 (0 : ℝ)) := tendsto_const_nhds
      have hg : Tendsto (fun t : ℝ => K * cR * (b - t)) (𝓝[Iio b] b) (𝓝 (0 : ℝ)) := by
        have hlin : Tendsto (fun t : ℝ => b - t) (𝓝[Iio b] b) (𝓝 (0 : ℝ)) := by
          have ht : Tendsto (fun x : ℝ => x) (𝓝[Iio b] b) (𝓝 b) :=
            tendsto_id.mono_left nhdsWithin_le_nhds
          have hc : ContinuousAt (fun x : ℝ => b - x) b := by
            exact (continuous_const.sub continuous_id).continuousAt
          have hm : Tendsto (fun x : ℝ => b - x) (𝓝[Iio b] b) (𝓝 (b - b)) := hc.tendsto.comp ht
          simpa using hm
        have hcst : Tendsto (fun _ : ℝ => K * cR) (𝓝[Iio b] b) (𝓝 (K * cR)) := tendsto_const_nhds
        have hmul : Tendsto (fun t : ℝ => (K * cR) * (b - t)) (𝓝[Iio b] b) (𝓝 (0 : ℝ)) := by
          have hmm : Tendsto (fun t : ℝ => (K * cR) * (b - t)) (𝓝[Iio b] b) (𝓝 ((K * cR) * 0)) :=
            hcst.mul hlin
          simpa using hmm
        simpa [mul_assoc, mul_comm, mul_left_comm] using hmul
      have hmain : Tendsto (fun t : ℝ => ‖x t‖) (𝓝[Iio b] b) (𝓝 (0 : ℝ)) :=
        tendsto_of_tendsto_of_tendsto_of_le_of_le' hz hg hnonneg hub
      -- ‖x t‖ → 0 forces x t → 0
      rw [Metric.tendsto_nhds]
      intro ε hε
      have hev : ∀ᶠ t in 𝓝[Iio b] b, dist (‖x t‖) (0 : ℝ) < ε :=
        (Metric.tendsto_nhds.mp hmain) ε hε
      filter_upwards [hev] with t ht
      rw [dist_eq_norm, sub_zero, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (x t))] at ht
      rw [dist_eq_norm, sub_zero]
      exact ht
    have hexpcont : ContinuousAt expm (0 : E) := by
      have h0mem : (0 : E) ∈ ball (0 : E) ρe := by simpa using hρe0
      exact (hExpC1.contDiffAt (isOpen_ball.mem_nhds h0mem)).continuousAt
    have hlim0 : Tendsto (fun t : ℝ => expm (x t)) (𝓝[Iio b] b) (𝓝 x₀) := by
      have hlim : Tendsto (fun t : ℝ => expm (x t)) (𝓝[Iio b] b) (𝓝 (expm (0 : E))) :=
        hexpcont.tendsto.comp hx_tend0
      simpa [x₀, hexp0] using hlim
    simpa [C] using hlim0
  -- C is continuous on (t2,b) (values in the chart source on the neck)
  have hγsrc {t : ℝ} (ht : t ∈ Ioo t2 b) : γ t ∈ (extChartAt I q).source := by
    have hEq : γ t = (extChartAt I q).symm (C t) := by
      have hE : ExpM (x t) = (extChartAt I q).symm (expm (x t)) := by
        have hmem : x t ∈ ball (0 : E) ρe := hxballρe ht
        have hh := hExpExpM (x t) hmem
        simpa using hh
      calc
        γ t = ExpM (x t) := (hxExp ht).symm
        _ = (extChartAt I q).symm (expm (x t)) := hE
        _ = (extChartAt I q).symm (C t) := by rfl
    rw [hEq]
    exact (extChartAt I q).map_target (hρTtgt (hC_in_ballT ht))
  have hγ_chart {t : ℝ} (ht : t ∈ Ioo t2 b) : γ t = (extChartAt I q).symm (C t) := by
    have hE : ExpM (x t) = (extChartAt I q).symm (expm (x t)) := by
      have hmem : x t ∈ ball (0 : E) ρe := hxballρe ht
      have hh := hExpExpM (x t) hmem
      simpa using hh
    calc
      γ t = ExpM (x t) := (hxExp ht).symm
      _ = (extChartAt I q).symm (expm (x t)) := hE
      _ = (extChartAt I q).symm (C t) := by rfl
  -- (s1) choose a left subneck (t2B,b) ⊆ (t2,b) where C stays in ball x0 ρB
  have hηB1 : ∃ η > 0, Ioo (b - η) b ⊆ C ⁻¹' (ball x₀ ρB) := by
    have hpre : C ⁻¹' (ball x₀ ρB) ∈ 𝓝[Iio b] b := hC_tend (ball_mem_nhds x₀ hρB0)
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hpre
    rcases hpre with ⟨O, hO, hOsub⟩
    rcases Metric.mem_nhds_iff.mp hO with ⟨δ, hδ0, hballO⟩
    refine ⟨δ, hδ0, ?_⟩
    intro t ht
    have hdm : dist t b < δ := by
      have h1 : b - t < δ := by linarith [ht.1]
      have h2 : t - b < 0 := by linarith [ht.2]
      rw [Real.dist_eq]
      rw [abs_of_neg h2]
      linarith
    have htO : t ∈ O := hballO (by rw [mem_ball]; exact hdm)
    have htIio : t ∈ Iio b := ht.2
    exact hOsub ⟨htO, htIio⟩
  have hηB2 : ∃ η > 0, η < b - t2 := by
    refine ⟨(b - t2) / 2, half_pos (sub_pos.mpr ht2_b), by linarith⟩
  rcases hηB1 with ⟨ηB1, hηB10, hηB1s⟩
  rcases hηB2 with ⟨ηB2, hηB20, hηB2lt⟩
  let ηB : ℝ := min ηB1 ηB2
  have hηB0 : 0 < ηB := lt_min hηB10 hηB20
  have hηB_lt_t2 : ηB < b - t2 := lt_of_le_of_lt (min_le_right _ _) hηB2lt
  let t2B : ℝ := b - ηB
  have ht2B_a : t2 < t2B := by
    dsimp [t2B]
    linarith
  have ht2B_b : t2B < b := by
    dsimp [t2B]
    linarith
  have hCBmem : ∀ t ∈ Ioo t2B b, C t ∈ ball x₀ ρB := by
    intro t ht
    dsimp [t2B] at ht
    have hsub : Ioo (b - ηB) b ⊆ Ioo (b - ηB1) b := by
      exact Ioo_subset_Ioo (by linarith [min_le_left ηB1 ηB2]) (le_refl b)
    exact hηB1s (hsub ⟨ht.1, ht.2⟩)

  -- (s2) pointwise: C is C¹ at every point of (t2,b), and has model speed cR.
  have hC_contDiffAt (t : ℝ) (ht : t ∈ Ioo t2 b) : ContDiffAt ℝ 1 C t := by
    have htab : t ∈ Ioo a b := ⟨lt_trans ht2_a ht.1, ht.2⟩
    rcases Submission.NeckSmoothCurve.smooth_curve (I := I) (M := M) hab hc γ hγ t htab with
      ⟨ε0, hε00, hγsm, hγsp⟩
    -- a small window around t inside (t2,b) and inside (t−ε0,t+ε0) with γ values in the source
    have hγsrc_t : γ t ∈ (extChartAt I q).source := hγsrc ht
    have hsrc_open : IsOpen (extChartAt I q).source := isOpen_extChartAt_source (I := I) q
    have hγcontOn0 : ContinuousOn γ (Ioo (t - ε0) (t + ε0)) := hγsm.continuousOn
    have hγcontAt : ContinuousAt γ t := by
      have ht0mem : t ∈ Ioo (t - ε0) (t + ε0) := by constructor <;> linarith
      exact hγcontOn0.continuousAt (isOpen_Ioo.mem_nhds ht0mem)
    have hpre : γ ⁻¹' (extChartAt I q).source ∈ 𝓝 t :=
      hγcontAt.preimage_mem_nhds (hsrc_open.mem_nhds hγsrc_t)
    rcases Metric.mem_nhds_iff.mp hpre with ⟨δs, hδs0, hδs⟩
    let ε : ℝ := min ε0 (min δs (min ((t - t2) / 2) ((b - t) / 2)))
    have hε0 : 0 < ε := by
      dsimp [ε]
      exact lt_min hε00 (lt_min hδs0 (lt_min (half_pos (sub_pos.mpr ht.1)) (half_pos (sub_pos.mpr ht.2))))
    have hεle0 : ε ≤ ε0 := by dsimp [ε]; exact min_le_left _ _
    have hεleδ : ε ≤ δs := by dsimp [ε]; exact le_trans (min_le_right _ _) (min_le_left _ _)
    have hεt2 : ε ≤ (t - t2) / 2 := by dsimp [ε]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    have hεbt : ε ≤ (b - t) / 2 := by dsimp [ε]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
    let W : Set ℝ := Ioo (t - ε) (t + ε)
    have hWopen : IsOpen W := isOpen_Ioo
    have hWmem : t ∈ W := by
      dsimp [W]
      constructor <;> linarith
    have hW_t2b : W ⊆ Ioo t2 b := by
      intro u hu
      constructor
      · have h2 : t - ε ≥ t2 := by linarith [hεt2, ht.1]
        linarith [hu.1, h2]
      · have h2 : t + ε ≤ b := by linarith [hεbt, ht.2]
        linarith [hu.2, h2]
    have hW_smooth : W ⊆ Ioo (t - ε0) (t + ε0) := by
      intro u hu
      constructor <;> linarith [hu.1, hu.2, hεle0]
    have hγsmW : ContMDiffOn 𝓘(ℝ,ℝ) I 1 γ W := hγsm.mono hW_smooth
    have hW_src : W ⊆ γ ⁻¹' (extChartAt I q).source := by
      intro u hu
      exact hδs (by
        rw [mem_ball]
        rw [Real.dist_eq]
        rw [abs_lt]
        constructor <;> linarith [hu.1, hu.2, hεleδ])
    have hcomp : ContMDiffOn 𝓘(ℝ,ℝ) 𝓘(ℝ,E) 1 ((extChartAt I q) ∘ γ) W := by
      have hphi : ContMDiffOn I 𝓘(ℝ, E) 1 (extChartAt I q) (chartAt H q).source := by
        have hfull : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I q) (chartAt H q).source :=
          contMDiffOn_extChartAt (I := I) (x := q)
        exact hfull.of_le (by norm_num : (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω))
      have hsub : W ⊆ γ ⁻¹' (chartAt H q).source := by
        intro u hu
        have hsrc : γ u ∈ (extChartAt I q).source := hW_src hu
        simpa [extChartAt_source] using hsrc
      exact ContMDiffOn.comp hphi hγsmW hsub
    have hD : ContDiffOn ℝ 1 ((extChartAt I q) ∘ γ) W := contMDiffOn_iff_contDiffOn.mp hcomp
    -- C = extChartAt ∘ γ on W
    have hCW : ∀ u ∈ W, C u = (extChartAt I q) (γ u) := by
      intro u hu
      exact (hC_chart (hW_t2b hu)).symm
    have hCdiffOn : ContDiffOn ℝ 1 C W := by
      refine hD.congr ?_
      intro u hu
      exact hCW u hu
    exact hCdiffOn.contDiffAt (hWopen.mem_nhds hWmem)
  have hC_diffAt (t : ℝ) (ht : t ∈ Ioo t2 b) : DifferentiableAt ℝ C t := by
    have hc := hC_contDiffAt t ht
    exact hc.differentiableAt (by norm_num : (1 : ℕ∞ω) ≠ 0)
  -- model speed of C at each neck point
  have hC_speed (t : ℝ) (ht : t ∈ Ioo t2 b) :
      Real.sqrt ((ge (C t)) (deriv C t) (deriv C t)) = cR := by
    have htab : t ∈ Ioo a b := ⟨lt_trans ht2_a ht.1, ht.2⟩
    have hder : HasDerivAt C (deriv C t) t := (hC_diffAt t ht).hasDerivAt
    -- the model speed identity via the chart curve γ̃ := φ.symm ∘ C (equal to γ near t)
    let gT : ℝ → M := fun s => (extChartAt I q).symm (C s)
    have hγeq : gT = (extChartAt I q).symm ∘ C := rfl
    have hagree : ∀ y ∈ ball x₀ ρT, ∀ uu vv : E,
        (ge y) uu vv = (Bundle.RiemannianBundle.g (E := fun x : M => TangentSpace I x)).inner
          ((extChartAt I q).symm y)
          ((mfderiv[range I] (extChartAt I q).symm y) uu)
          ((mfderiv[range I] (extChartAt I q).symm y) vv) := by
      intro y hy uu vv
      exact hgeAgree y (ball_subset_ball hρTle hy) uu vv
    have hspd0 := chart_speed_core (I := I) (M := M) q (ρ := ρT) (ge := ge) hagree hρTtgt
      (γ := gT) (c := C) (t := t) (u := deriv C t) (fun s : ℝ => rfl) (hC_in_ballT ht) hder
    have hgTeq : gT =ᶠ[𝓝 t] γ := by
      have hW : Ioo t2 b ∈ 𝓝 t := isOpen_Ioo.mem_nhds ht
      filter_upwards [hW] with s hs
      dsimp [gT]
      rw [hγ_chart hs]
      rfl
    have hmfd : mfderiv% gT t = mfderiv% γ t := hgTeq.mfderiv_eq
    have hsp1 : ‖mfderiv% γ t 1‖ₑ = ENNReal.ofReal (Real.sqrt ((ge (C t)) (deriv C t) (deriv C t))) := by
      have hCtarget : C t ∈ (extChartAt I q).target := hρTtgt (hC_in_ballT ht)
      have hcompT := chart_mfderiv_comp (I := I) (M := M) q (γ := gT) (c := C) (t := t) (u := deriv C t)
        (show gT = (extChartAt I q).symm ∘ C from rfl) hCtarget hder
      have hmfd' : mfderiv% γ t = mfderiv% gT t := hgTeq.symm.mfderiv_eq
      have hv : (mfderiv% γ t) 1 = (mfderiv[range I] (extChartAt I q).symm (C t)) (deriv C t) := by
        rw [hmfd']
        exact hcompT
      have hnorm0 : ‖(mfderiv% γ t) 1‖ₑ =
          ENNReal.ofReal (Real.sqrt (inner ℝ ((mfderiv% γ t) 1) ((mfderiv% γ t) 1))) := by
        exact enorm_sqrt_inner ((mfderiv% γ t) 1)
      have hfib1 : inner ℝ ((mfderiv% γ t) 1) ((mfderiv% γ t) 1) =
          (Bundle.RiemannianBundle.g (E := fun x : M => TangentSpace I x)).inner (γ t)
            ((mfderiv% γ t) 1) ((mfderiv% γ t) 1) := rfl
      have hbase : γ t = (extChartAt I q).symm (C t) := hγ_chart ht
      have hval : Real.sqrt (inner ℝ ((mfderiv% γ t) 1) ((mfderiv% γ t) 1)) =
          Real.sqrt ((ge (C t)) (deriv C t) (deriv C t)) := by
        congr 1
        calc
          inner ℝ ((mfderiv% γ t) 1) ((mfderiv% γ t) 1)
              = (Bundle.RiemannianBundle.g (E := fun x : M => TangentSpace I x)).inner (γ t)
                  ((mfderiv% γ t) 1) ((mfderiv% γ t) 1) := hfib1
          _ = (Bundle.RiemannianBundle.g (E := fun x : M => TangentSpace I x)).inner
                  ((extChartAt I q).symm (C t))
                  ((mfderiv[range I] (extChartAt I q).symm (C t)) (deriv C t))
                  ((mfderiv[range I] (extChartAt I q).symm (C t)) (deriv C t)) := by
                rw [hv, hbase]
          _ = (ge (C t)) (deriv C t) (deriv C t) := by
                exact (hgeAgree (C t) (ball_subset_ball hρTle (hC_in_ballT ht)) (deriv C t) (deriv C t)).symm
      calc
        ‖(mfderiv% γ t) 1‖ₑ = ENNReal.ofReal (Real.sqrt (inner ℝ ((mfderiv% γ t) 1) ((mfderiv% γ t) 1))) := hnorm0
        _ = ENNReal.ofReal (Real.sqrt ((ge (C t)) (deriv C t) (deriv C t))) := by rw [hval]
    have hsp2 : ‖mfderiv% γ t 1‖ₑ = (c : ℝ≥0∞) := by
      rcases Submission.NeckSmoothCurve.smooth_curve (I := I) (M := M) hab hc γ hγ t htab with
        ⟨ε0, hε00, hγsm, hγsp⟩
      have htW : t ∈ Ioo (t - ε0) (t + ε0) := by constructor <;> linarith
      exact hγsp t htW
    have hsp3 : ENNReal.ofReal (Real.sqrt ((ge (C t)) (deriv C t) (deriv C t))) = (c : ℝ≥0∞) := by
      rw [← hsp1]
      exact hsp2
    have hcoe : (c : ℝ≥0∞) = ENNReal.ofReal (c : ℝ) := (ENNReal.ofReal_coe_nnreal).symm
    have hsp4 : ENNReal.ofReal (Real.sqrt ((ge (C t)) (deriv C t) (deriv C t))) = ENNReal.ofReal (cR) := by

      calc
        ENNReal.ofReal (Real.sqrt ((ge (C t)) (deriv C t) (deriv C t))) = (c : ℝ≥0∞) := hsp3
        _ = ENNReal.ofReal (cR) := by
          simpa [cR] using hcoe
    exact (ENNReal.ofReal_eq_ofReal_iff (Real.sqrt_nonneg _) hcR_nonneg).1 hsp4

  -- (s2b) subneck refinement: eventually C(t) is within any prescribed ball around x0
  have hCsub (ε : ℝ) (hε : 0 < ε) : ∃ η : ℝ, 0 < η ∧ η < b - t2B ∧
      ∀ t ∈ Ioo (b - η) b, t ∈ Ioo t2B b → ‖C t - x₀‖ < ε := by
    have hpre0 : C ⁻¹' (ball x₀ ε) ∈ 𝓝[Iio b] b := hC_tend (ball_mem_nhds x₀ hε)
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hpre0
    rcases hpre0 with ⟨O, hO, hOsub0⟩
    rcases Metric.mem_nhds_iff.mp hO with ⟨δ, hδ0, hballO⟩
    let η1 : ℝ := min δ ((b - t2B) / 2)
    have hη10 : 0 < η1 := lt_min hδ0 (half_pos (sub_pos.mpr ht2B_b))
    refine ⟨η1, hη10, by
      dsimp [η1]
      exact lt_of_le_of_lt (min_le_right _ _) (by linarith [ht2B_b]), ?_⟩
    intro t ht htB
    have h1 : b - t < δ := by
      have hlt : b - t < η1 := by linarith [ht.1]
      exact lt_of_lt_of_le hlt (min_le_left δ ((b - t2B) / 2))
    have h2 : t - b < 0 := by linarith [ht.2]
    have hdist : dist t b < δ := by
      rw [Real.dist_eq]
      rw [abs_of_neg h2]
      linarith
    have htO : t ∈ O := hballO (by rw [mem_ball]; exact hdist)
    have hmem : C t ∈ ball x₀ ε := hOsub0 ⟨htO, ht.2⟩
    rw [mem_ball, dist_eq_norm] at hmem
    exact hmem
  -- (s3) metric lower bound near x0 (positive definiteness, uniform on a small ball)
  rcases quad_ellipsoid_bound (ge x₀) (hgePos x₀) with ⟨m0, hm00, hm0b⟩
  have hg_close : ∃ r : ℝ, 0 < r ∧ r < ρB ∧ ∀ y ∈ ball x₀ r, ‖ge y - ge x₀‖ ≤ m0 / 2 := by
    have hc : ContinuousAt ge x₀ := hgeC.continuous.continuousAt
    have hd : ∀ᶠ y in 𝓝 x₀, dist (ge y) (ge x₀) < m0 / 2 :=
      (Metric.continuousAt_iff'.mp hc) (m0 / 2) (by positivity)
    rcases Metric.mem_nhds_iff.mp hd with ⟨r0, hr00, hr0⟩
    let r : ℝ := min r0 (ρB / 2)
    have hr0' : 0 < r := by dsimp [r]; exact lt_min hr00 (half_pos hρB0)
    refine ⟨r, hr0', ?_, ?_⟩
    · dsimp [r]
      exact lt_of_le_of_lt (min_le_right r0 (ρB / 2)) (by linarith [hρB0])
    · intro y hy
      have hy0 : y ∈ ball x₀ r0 := by
        have : r ≤ r0 := by dsimp [r]; exact min_le_left _ _
        exact ball_subset_ball this hy
      have h : dist (ge y) (ge x₀) < m0 / 2 := hr0 hy0
      have heq : ‖ge y - ge x₀‖ = dist (ge y) (ge x₀) := (dist_eq_norm (a := ge y) (b := ge x₀)).symm
      have hnorm0 : ‖ge y - ge x₀‖ < m0 / 2 := by
        rw [heq]
        exact h
      exact le_of_lt hnorm0
  rcases hg_close with ⟨rgeo, hrgeo0, hrgeoB, hge_close⟩
  have hgeo_lower : ∀ y ∈ ball x₀ rgeo, ∀ w : E, (m0 / 2) * ‖w‖ ^ 2 ≤ (ge y) w w := by
    intro y hy w
    have hcl := hge_close y hy
    have hQ0 : 0 ≤ (ge x₀) w w := by
      by_cases hw : w = 0
      · subst w; simp
      · exact le_of_lt (hgePos x₀ w hw)
    have hmm : m0 * ‖w‖ ^ 2 ≤ (ge x₀) w w := hm0b w
    have hbd1 : ‖(ge y - ge x₀) w‖ ≤ ‖ge y - ge x₀‖ * ‖w‖ := (ge y - ge x₀).le_opNorm w
    have habs : ‖(((ge y - ge x₀) w) w)‖ ≤ ‖ge y - ge x₀‖ * ‖w‖ ^ 2 := by
      have h21 := ((ge y - ge x₀) w).le_opNorm w
      calc
        ‖(((ge y - ge x₀) w) w)‖ ≤ ‖(ge y - ge x₀) w‖ * ‖w‖ := h21
        _ ≤ (‖ge y - ge x₀‖ * ‖w‖) * ‖w‖ := mul_le_mul_of_nonneg_right hbd1 (norm_nonneg w)
        _ = ‖ge y - ge x₀‖ * ‖w‖ ^ 2 := by ring
    have hcl2 : ‖ge y - ge x₀‖ * ‖w‖ ^ 2 ≤ (m0 / 2) * ‖w‖ ^ 2 := by
      exact mul_le_mul_of_nonneg_right hcl (sq_nonneg ‖w‖)
    have hbd3 : |((ge y - ge x₀) w) w| ≤ (m0 / 2) * ‖w‖ ^ 2 := by
      have hle : |((ge y - ge x₀) w) w| ≤ ‖((ge y - ge x₀) w) w‖ := by
        simpa [Real.norm_eq_abs]
      exact le_trans hle (le_trans habs hcl2)
    have hmd : -|((ge y - ge x₀) w) w| ≤ ((ge y - ge x₀) w) w := by
      have h := le_abs_self (a := -(((ge y - ge x₀) w) w))
      rw [abs_neg] at h
      linarith
    have hsub : (ge y) w w - (ge x₀) w w = ((ge y - ge x₀) w) w := by simp
    have h1 : (m0 / 2) * ‖w‖ ^ 2 ≤ (ge x₀) w w - |((ge y - ge x₀) w) w| := by nlinarith [hmm, hbd3]
    have h2 : (ge x₀) w w - |((ge y - ge x₀) w) w| ≤ (ge y) w w := by
      have hs3 : (ge x₀) w w + ((ge y - ge x₀) w) w = (ge y) w w := by linarith [hsub]
      nlinarith [hs3, hmd]
    exact le_trans h1 h2
  -- (s4) refine the subneck once more: C stays inside ball x0 (min rgeo ρB (ρT/2))
  let rC : ℝ := min (min rgeo ρB) (ρT / 2)
  have hrC0 : 0 < rC := by dsimp [rC]; positivity
  have hrC_geo : rC ≤ rgeo := by dsimp [rC]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hrC_B : rC ≤ ρB := by dsimp [rC]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hrC_T2 : rC ≤ ρT / 2 := by dsimp [rC]; exact min_le_right _ _
  rcases hCsub rC hrC0 with ⟨ηC, hηC0, hηC_t2B, hηCmem⟩
  let t2C : ℝ := b - ηC
  have ht2C_B : t2B < t2C := by
    dsimp [t2C]
    linarith
  have ht2C_b : t2C < b := by
    dsimp [t2C]
    linarith
  have hC_mem : ∀ t ∈ Ioo t2C b, C t ∈ ball x₀ rC := by
    intro t ht
    dsimp [t2C] at ht
    have htB : t ∈ Ioo t2B b := ⟨lt_trans ht2C_B ht.1, ht.2⟩
    have hnorm : ‖C t - x₀‖ < rC := hηCmem t ⟨ht.1, ht.2⟩ htB
    rw [mem_ball, dist_eq_norm]
    exact hnorm
  have hC_mem_geo : ∀ t ∈ Ioo t2C b, C t ∈ ball x₀ rgeo := by
    intro t ht
    exact ball_subset_ball hrC_geo (hC_mem t ht)
  have hC_mem_B : ∀ t ∈ Ioo t2C b, C t ∈ ball x₀ ρB := by
    intro t ht
    exact ball_subset_ball hrC_B (hC_mem t ht)
  have hC_mem_T2 : ∀ t ∈ Ioo t2C b, C t ∈ ball x₀ (ρT / 2) := by
    intro t ht
    exact ball_subset_ball hrC_T2 (hC_mem t ht)
  -- (s5) uniform Euclidean bound for deriv C on the subneck (t2C,b)
  let Bv : ℝ := cR / Real.sqrt (m0 / 2)
  have hBv0 : 0 < Bv := by
    dsimp [Bv]
    positivity
  have hder_bnd : ∀ t ∈ Ioo t2C b, ‖deriv C t‖ ≤ Bv := by
    intro t ht
    have ht2 : t ∈ Ioo t2 b := ⟨lt_trans ht2B_a (lt_trans ht2C_B ht.1), ht.2⟩
    have hspd := hC_speed t ht2
    have hy : C t ∈ ball x₀ rgeo := hC_mem_geo t ht
    let v : E := deriv C t
    have hq : (m0 / 2) * ‖v‖ ^ 2 ≤ (ge (C t)) v v := hgeo_lower (C t) hy v
    have hspd2 : (ge (C t)) v v = cR ^ 2 := by
      have hnn : 0 ≤ (ge (C t)) v v := by
        by_cases hv : v = 0
        · simp [hv]
        · exact le_of_lt (hgePos (C t) v hv)
      calc
        (ge (C t)) v v = (Real.sqrt ((ge (C t)) v v)) ^ 2 := by
          rw [Real.sq_sqrt hnn]
        _ = cR ^ 2 := by
          have hspd' : Real.sqrt ((ge (C t)) (deriv C t) (deriv C t)) = cR := hspd
          change (Real.sqrt ((ge (C t)) (deriv C t) (deriv C t))) ^ 2 = cR ^ 2
          rw [hspd']
    have h1 : (m0 / 2) * ‖v‖ ^ 2 ≤ cR ^ 2 := by
      calc
        (m0 / 2) * ‖v‖ ^ 2 ≤ (ge (C t)) v v := hq
        _ = cR ^ 2 := hspd2
    have hnonneg1 : 0 ≤ Real.sqrt (m0 / 2) * ‖v‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg v)
    have hnonneg2 : 0 ≤ cR := le_of_lt hcR0
    have hsq : (Real.sqrt (m0 / 2) * ‖v‖) ^ 2 ≤ cR ^ 2 := by
      calc
        (Real.sqrt (m0 / 2) * ‖v‖) ^ 2 = (m0 / 2) * ‖v‖ ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ m0 / 2)]
        _ ≤ cR ^ 2 := h1
    have hsq2 : Real.sqrt (m0 / 2) * ‖v‖ ≤ cR := (sq_le_sq₀ hnonneg1 hnonneg2).mp hsq
    have hmhalf : 0 < m0 / 2 := by positivity
    have hlen : ‖v‖ ≤ cR / Real.sqrt (m0 / 2) := by
      rw [le_div_iff₀ (Real.sqrt_pos.2 hmhalf)]
      nlinarith [hsq2]
    dsimp [Bv]
    dsimp [v] at hlen
    exact hlen

  -- (s6) C is C¹ on the whole open subneck (t2C,b) (locality via per-point ContDiffAt)
  have hC_c1_open : ContDiffOn ℝ 1 C (Ioo t2C b) := by
    rw [IsOpen.contDiffOn_iff isOpen_Ioo]
    intro u hu
    have hu2 : u ∈ Ioo t2 b := ⟨lt_trans ht2B_a (lt_trans ht2C_B hu.1), hu.2⟩
    exact hC_contDiffAt u hu2
  -- (s7) CORE PAIR CLAIM: an exact pair (s,t) of γ with the C-curve staying near C s is
  --     realised by the model flow geodesic between C s and C t (NeckData-based).
  have hPairGeo : ∀ {s t : ℝ}, s ∈ Ioo t2C b → t ∈ Ioo t2C b → s < t →
      edist (γ s) (γ t) = (c : ℝ≥0∞) * ENNReal.ofReal (t - s) →
      (∀ u ∈ Icc s t, ‖C u - C s‖ < δu) →
      (∀ u ∈ Ioo s t, C u ≠ C s) →
      (cR / Real.sqrt (m0 / 2)) * (t - s) < δu →
      (t - s) < 1 →
      (∀ u v : ℝ, u ∈ Icc s t → v ∈ Icc s t → edist (γ u) (γ v) =
         (c : ℝ≥0∞) * ENNReal.ofReal |v - u|) →
      (Lf / τu) * (cR / Real.sqrt (m0 / 2)) * (t - s) < ρT / 2 →
      ∃ v : E, v ∈ ball (0 : E) δu ∧ Real.sqrt ((ge (C s)) v v) = cR * (t - s) ∧
        C t = expOf (C s) Φr τu v ∧
        (∀ τ ∈ Icc (0 : ℝ) 1, C (s + τ * (t - s)) = expOf (C s) Φr τu (τ • v)) := by
    intro s t hs ht hst hexact hstay hInjArc hsmallv hlt1 hexactSub hsmallT
    let p : E := C s
    let q' : E := C t
    have hpB : p ∈ ball x₀ ρB := hC_mem_B s hs
    -- per-base NeckData at p
    have hnp : Nonempty (Submission.NeckEq.NeckData ge p Φr τu δu ρE) := hpkg p hpB
    rcases hnp with ⟨D⟩
    have hq'δ : q' ∈ ball p δu := by
      rw [mem_ball]
      have htIcc : t ∈ Icc s t := ⟨le_of_lt hst, le_rfl⟩
      have hbnd := hstay t htIcc
      simpa [p, q', dist_eq_norm] using hbnd
    have hvinv : D.invb q' ∈ ball (0 : E) ρE ∧ D.expb (D.invb q') = q' := D.inv_right q' hq'δ
    have hpρu : p ∈ ball x₀ ρu := ball_subset_ball hρBρu hpB
    have hPerB0 : ∀ z ∈ closedBall (p, 0) 1, Φr z 0 = z ∧
        (∀ t ∈ Icc (-τf) τf, HasDerivAt (Φr z) (odeField ge (Φr z t)) t) ∧
        (∀ t : ℝ, Φr z t ∈ closedBall (p, 0) 2) := by
      intro z hz
      exact hPerBr p hpρu z hz
    have hLipB0 : ∀ t ∈ Icc (-τf) τf,
        LipschitzOnWith Lf (fun z => Φr z t) (closedBall (p, 0) 1) := by
      intro t ht
      exact hLipBr t ht p hpρu
    have hKb0 : ∀ pp ∈ closedBall (p, 0) 2, ‖fderiv ℝ (odeField ge) pp‖ ≤ K0 := by
      intro pp hpp
      exact hKbigP pp (closedBall_b0_subset x₀ hρu hpρu hpp)
    let v : E := D.invb q'
    have hvρE : v ∈ ball (0 : E) ρE := hvinv.1
    have hexp_v : D.expb v = q' := hvinv.2
    let L : ℝ := Real.sqrt ((ge p) v v)
    -- the rescaled curve
    let ct : ℝ → E := fun τ => C (s + τ * (t - s))
    have hstep : 0 < t - s := sub_pos.mpr hst
    -- ct is C¹ on an open set containing [0,1]
    have hO : ∃ O : Set ℝ, IsOpen O ∧ Icc (0 : ℝ) 1 ⊆ O ∧ ContDiffOn ℝ 1 ct O := by
      let O : Set ℝ := {τ : ℝ | s + τ * (t - s) ∈ Ioo t2C b}
      have hOopen : IsOpen O := by
        have hlin : Continuous (fun τ : ℝ => s + τ * (t - s)) := by
          exact continuous_const.add (continuous_id.mul continuous_const)
        exact hlin.isOpen_preimage (Ioo t2C b) isOpen_Ioo
      have hOIcc : Icc (0 : ℝ) 1 ⊆ O := by
        intro τ hτ
        have hseg : s + τ * (t - s) ∈ Icc s t := by
          constructor <;> nlinarith [hτ.1, hτ.2, hstep]
        have h1 : t2C < s + τ * (t - s) := lt_of_lt_of_le hs.1 hseg.1
        have h2 : s + τ * (t - s) < b := lt_of_le_of_lt hseg.2 ht.2
        exact ⟨h1, h2⟩
      have hcomp : ContDiffOn ℝ 1 ct O := by
        have haffC : ContDiff ℝ ∞ (fun τ : ℝ => s + τ * (t - s)) := by
          exact contDiff_const.add (contDiff_id.mul (contDiff_const (c := t - s)))
        have hcomp0 : ContDiffOn ℝ 1 (C ∘ (fun τ : ℝ => s + τ * (t - s))) O := by
          exact ContDiffOn.comp (g := C) (f := fun τ : ℝ => s + τ * (t - s))
            (s := O) (t := Ioo t2C b) hC_c1_open
            (haffC.of_le (by norm_num : (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω))).contDiffOn
            (fun τ hτ => hτ)
        convert hcomp0 using 1
        funext τ
        rfl
      refine ⟨O, hOopen, hOIcc, hcomp⟩
    -- endpoints
    have hc0 : ct 0 = p := by
      dsimp [ct, p]
      congr 1
      ring
    have hc1 : ct 1 = D.expb v := by
      dsimp [ct]
      have harg : s + 1 * (t - s) = t := by ring
      rw [harg]
      exact hexp_v.symm
    have hstayc : ∀ u ∈ Icc (0 : ℝ) 1, ct u ∈ ball p δu := by
      intro u hu
      have hseg : s + u * (t - s) ∈ Icc s t := by
        constructor <;> nlinarith [hu.1, hu.2, hstep]
      have hbnd := hstay (s + u * (t - s)) hseg
      rw [mem_ball]
      dsimp [ct, p]
      simpa [dist_eq_norm] using hbnd
    -- const model speed of ct on (0,1) (chain rule + C's speed)
    have hsp (τ : ℝ) (hτ : τ ∈ Ioo (0 : ℝ) 1) :
        Model.mgSpeed ge (ct τ) (deriv ct τ) = cR * (t - s) := by
      have hseg : s + τ * (t - s) ∈ Ioo t2C b := by
        have hseg' : s + τ * (t - s) ∈ Icc s t := by
          constructor <;> nlinarith [hτ.1, hτ.2, hstep]
        exact ⟨lt_of_lt_of_le hs.1 hseg'.1, lt_of_le_of_lt hseg'.2 ht.2⟩
      have hseg2 : s + τ * (t - s) ∈ Ioo t2 b :=
        ⟨lt_trans ht2B_a (lt_trans ht2C_B hseg.1), hseg.2⟩
      have hderC := hC_diffAt (s + τ * (t - s)) hseg2
      have haffder : HasDerivAt (fun u : ℝ => s + u * (t - s)) (t - s) τ := by
        have h1 : HasDerivAt (fun u : ℝ => u * (t - s)) (t - s) τ := by
          simpa using ((hasDerivAt_id τ).mul_const (t - s))
        simpa [add_comm, add_left_comm, add_assoc] using h1.const_add s
      have hder : HasDerivAt ct ((t - s) • deriv C (s + τ * (t - s))) τ := by
        exact HasDerivAt.scomp (x := τ) (g₁ := C) (hg := hderC.hasDerivAt)
          (h := fun u : ℝ => s + u * (t - s)) (h' := t - s) (hh := haffder)
      have hder2 : deriv ct τ = (t - s) • deriv C (s + τ * (t - s)) := hder.deriv
      dsimp [Model.mgSpeed]
      rw [hder2]
      have hspdC := hC_speed (s + τ * (t - s)) hseg2
      have hnn : 0 ≤ (ge (ct τ)) (deriv C (s + τ * (t - s))) (deriv C (s + τ * (t - s))) := by
        by_cases hz : deriv C (s + τ * (t - s)) = 0
        · rw [hz]; simp
        · exact le_of_lt (hgePos (ct τ) (deriv C (s + τ * (t - s))) hz)
      rw [sqrt_quad_smul_nonneg (ge (ct τ)) (le_of_lt hstep) (deriv C (s + τ * (t - s))) hnn]
      change (t - s) * Real.sqrt
          ((ge (C (s + τ * (t - s)))) (deriv C (s + τ * (t - s))) (deriv C (s + τ * (t - s)))) =
        cR * (t - s)
      rw [hspdC]
      ring
    -- lower bound: L ≤ cR(t−s) via the radial drop bound (NeckData radial data)
    have hFp0 : radialCoord ge p D.invb p = 0 := by
      have h0mem : (0 : E) ∈ ball (0 : E) ρE := by simpa using hρE0
      have hp0 : D.invb p = 0 := by
        have hpb : p ∈ ball p δu := by rw [mem_ball, dist_self]; exact hδu0
        have hiv : D.invb p ∈ ball (0 : E) ρE ∧ D.expb (D.invb p) = p := D.inv_right p hpb
        have heq : D.expb (D.invb p) = D.expb (0 : E) := by
          rw [hiv.2]
          exact D.exp0.symm
        exact D.inj (D.invb p) (0 : E) hiv.1 h0mem heq
      dsimp [radialCoord]
      rw [hp0]
      simp
    have hFend : radialCoord ge p D.invb (ct 1) = L := by
      have hvv : ct 1 = D.expb v := hc1
      have hvl : D.invb (D.expb v) = v := D.inv_left v hvρE
      dsimp [radialCoord, L]
      rw [hvv, hvl]
    have hctne : ∀ s' ∈ Ioo (0 : ℝ) 1, ct s' ≠ p := by
      intro s' hs'
      have hseg' : s + s' * (t - s) ∈ Ioo s t := by
        constructor
        · have h1 : s < s + s' * (t - s) := by nlinarith [hs'.1, hstep]
          exact h1
        · have h2 : s + s' * (t - s) < t := by nlinarith [hs'.2, hstep]
          exact h2
      have hne : C (s + s' * (t - s)) ≠ C s := hInjArc (s + s' * (t - s)) hseg'
      dsimp [ct, p]
      exact hne
    have hdrop : L ≤ cR * (t - s) := by
      have hd := Submission.NeckEq.radial_drop_le ge p D.invb hδu0 D.F_cont D.F_diff D.F_bound
        hO hstayc (r := cR * (t - s)) (fun s' hs' => hsp s' hs')
        (p := (0 : ℝ)) (q := 1) (by norm_num) (by norm_num) (by norm_num) hctne
      rw [hFend, hc0, hFp0] at hd
      simpa using hd
    -- upper bound cR(t−s) ≤ L via the lifted flow geodesic
    have hL_ge : cR * (t - s) ≤ L := by
      -- model geodesic σ(u) := expOf p Φr τu (u • v) from p to q'
      have hvτu : ‖v‖ ≤ τu := by
        have hvρ : ‖v‖ < ρE := by simpa [dist_eq_norm] using (mem_ball.mp hvρE)
        have hle : ρE ≤ τu := by nlinarith [h4ρEτu]
        exact le_trans (le_of_lt hvρ) hle
      have hτuτf : τu < τf := by nlinarith [h8τuτf, hτf]
      -- ‖v‖ control via the lower bound (hdrop)
      have hvn : ‖v‖ ≤ (cR / Real.sqrt (m0 / 2)) * (t - s) := by
        have hy0 : p ∈ ball x₀ rgeo := hC_mem_geo s hs
        have hPD : (m0 / 2) * ‖v‖ ^ 2 ≤ (ge p) v v := by
          dsimp [p]
          exact hgeo_lower (C s) hy0 v
        have hLsq : (m0 / 2) * ‖v‖ ^ 2 ≤ L ^ 2 := by
          calc
            (m0 / 2) * ‖v‖ ^ 2 ≤ (ge p) v v := hPD
            _ = L ^ 2 := by
              have hnn : 0 ≤ (ge p) v v := by
                by_cases hv0 : v = 0
                · rw [hv0]; simp
                · exact le_of_lt (hgePos p v hv0)
              rw [Real.sq_sqrt hnn]
        have hnn1 : 0 ≤ Real.sqrt (m0 / 2) * ‖v‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg v)
        have hnn2 : 0 ≤ L := Real.sqrt_nonneg _
        have hsq : (Real.sqrt (m0 / 2) * ‖v‖) ^ 2 ≤ L ^ 2 := by
          calc
            (Real.sqrt (m0 / 2) * ‖v‖) ^ 2 = (m0 / 2) * ‖v‖ ^ 2 := by
              rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ m0 / 2)]
            _ ≤ L ^ 2 := hLsq
        have hmain : Real.sqrt (m0 / 2) * ‖v‖ ≤ L := (sq_le_sq₀ hnn1 hnn2).mp hsq
        have hpos : 0 < Real.sqrt (m0 / 2) := Real.sqrt_pos.2 (by positivity)
        have hle : ‖v‖ ≤ L / Real.sqrt (m0 / 2) := by
          rw [le_div_iff₀ hpos]
          nlinarith [hmain]
        have hdL : L / Real.sqrt (m0 / 2) ≤ (cR / Real.sqrt (m0 / 2)) * (t - s) := by
          have h1 : L ≤ cR * (t - s) := hdrop
          have hmhalf2 : 0 < Real.sqrt (m0 / 2) := Real.sqrt_pos.2 (by positivity)
          field_simp [ne_of_gt hmhalf2]
          exact h1
        exact le_trans hle hdL
      have hsmall' : (Lf : ℝ) * ‖v‖ / τu < ρT / 2 := by
        have hle1 : (Lf : ℝ) * ‖v‖ / τu ≤ (Lf : ℝ) * ((cR / Real.sqrt (m0 / 2)) * (t - s)) / τu := by
          have hLf0 : 0 ≤ (Lf : ℝ) := by exact_mod_cast (Lf : NNReal).2
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hvn hLf0) (le_of_lt hτu0)
        have hlt2 : (Lf : ℝ) * ((cR / Real.sqrt (m0 / 2)) * (t - s)) / τu < ρT / 2 := by
          have hT : (Lf : ℝ) / τu * (cR / Real.sqrt (m0 / 2)) * (t - s) < ρT / 2 := hsmallT
          field_simp [ne_of_gt hτu0] at hT ⊢
          nlinarith
        exact lt_of_le_of_lt hle1 hlt2
      have hagree : ∀ y ∈ ball x₀ ρT, ∀ uu vv : E,
          (ge y) uu vv = (Bundle.RiemannianBundle.g (E := fun x : M => TangentSpace I x)).inner
            ((extChartAt I q).symm y)
            ((mfderiv[range I] (extChartAt I q).symm y) uu)
            ((mfderiv[range I] (extChartAt I q).symm y) vv) := by
        intro y hy uu vv
        exact hgeAgree y (ball_subset_ball hρTle hy) uu vv
      have hlt := Submission.LiftChild.lift_length (I := I) (M := M) q ge hgeC hinv hgeSymm hgePos
        (ρT := ρT) (hρT0 := hρT0) (hρTtgt := hρTtgt) (hagree := hagree) (p := p)
        (hpT2 := hC_mem_T2 s hs) (τf := τf) (hτf := hτf) (Lf := Lf) (Φr := Φr)
        (hPerB := hPerB0) (hLipB := hLipB0) (τu := τu) (hτu0 := hτu0) (hτuTf := hτuτf)
        (v := v) (hv := hvτu) (hsmall := hsmall')
      -- hlt : let σ := fun u => expOf p Φr τu (u•v); let Γ := fun u => chart⁻¹ (σ u);
      --       ContMDiffOn Γ (Icc 0 1) ∧ pathELength Γ 0 1 ≤ ofReal (√((ge p) v v))
      let σ : ℝ → E := fun u => expOf p Φr τu (u • v)
      let Γ : ℝ → M := fun u => (extChartAt I q).symm (σ u)
      have hlt2 : ContMDiffOn 𝓘(ℝ,ℝ) I 1 Γ (Icc (0 : ℝ) 1) ∧
          Manifold.pathELength I Γ 0 1 ≤ ENNReal.ofReal (Real.sqrt ((ge p) v v)) := by
        simpa [σ, Γ] using hlt
      have hΓsm : ContMDiffOn 𝓘(ℝ,ℝ) I 1 Γ (Icc (0 : ℝ) 1) := hlt2.1
      have hpl : Manifold.pathELength I Γ 0 1 ≤ ENNReal.ofReal L := by
        have h2 := hlt2.2
        simpa [L] using h2
      have hΓ0 : Γ 0 = γ s := by
        dsimp [Γ, σ]
        have h0mem : (0 : E) ∈ ball (0 : E) ρE := by simpa using hρE0
        have hz0 : (p, τu⁻¹ • v) ∈ closedBall (p, 0) 1 := by
          exact Submission.Model.slice_data_mem p τu hτu0 hvτu
        -- expOf p Φr τu ((0 : ℝ) • v) = p
        have hσ0 : expOf p Φr τu ((0 : ℝ) • v) = p := by
          have hflow := Submission.Model.exp_ray_value ge hgeC hinv p (Tf := τf) (hTf := hτf)
            (Φ := Φr) (hΦ := fun z hz => ⟨(hPerB0 z hz).1, (hPerB0 z hz).2.1⟩)
            (τ := τu) (hτ := hτu0) (hτTf := hτuτf) (v := v) (hv := hvτu)
            (s := (0 : ℝ)) (hs := by norm_num) (hs1 := by norm_num)
          have hre0 := (hPerB0 (p, τu⁻¹ • v) hz0).1
          have hre0f : (Φr (p, τu⁻¹ • v) (0 * τu)).1 = p := by
            simpa using congrArg Prod.fst hre0
          calc
            expOf p Φr τu ((0 : ℝ) • v) = (Φr (p, τu⁻¹ • v) (0 * τu)).1 := hflow
            _ = p := hre0f

        rw [hσ0]
        have hpdef : p = C s := rfl
        rw [hpdef]
        have hs2 : s ∈ Ioo t2 b := ⟨lt_trans ht2B_a (lt_trans ht2C_B hs.1), hs.2⟩
        exact (hγ_chart hs2).symm
      have hΓ1 : Γ 1 = γ t := by
        dsimp [Γ, σ]
        have hσ1 : expOf p Φr τu ((1 : ℝ) • v) = q' := by
          have harg : (1 : ℝ) • v = v := by simp
          rw [harg]
          have hdform := D.expform v
          rw [← hdform]
          exact hexp_v
        rw [hσ1]
        have hqdef : q' = C t := rfl
        rw [hqdef]
        have ht2 : t ∈ Ioo t2 b := ⟨lt_trans ht2B_a (lt_trans ht2C_B ht.1), ht.2⟩
        exact (hγ_chart ht2).symm
      have hdst : edist (γ s) (γ t) ≤ Manifold.pathELength I Γ 0 1 := by
        have h1 := Manifold.riemannianEDist_le_pathELength (I := I) hΓsm hΓ0 hΓ1 (by norm_num)
        rwa [← IsRiemannianManifold.out (I := I) (γ s) (γ t)] at h1
      have heq_ed : edist (γ s) (γ t) = ENNReal.ofReal (cR * (t - s)) := by
        have hcoe : (c : ℝ≥0∞) = ENNReal.ofReal (c : ℝ) := (ENNReal.ofReal_coe_nnreal).symm
        calc
          edist (γ s) (γ t) = (c : ℝ≥0∞) * ENNReal.ofReal (t - s) := hexact
          _ = ENNReal.ofReal (cR * (t - s)) := by
            rw [hcoe]
            rw [ENNReal.ofReal_mul hcR_nonneg]
      have hof : ENNReal.ofReal (cR * (t - s)) ≤ ENNReal.ofReal L := by
        calc
          ENNReal.ofReal (cR * (t - s)) = edist (γ s) (γ t) := heq_ed.symm
          _ ≤ Manifold.pathELength I Γ 0 1 := hdst
          _ ≤ ENNReal.ofReal L := hpl
      have hLnn : 0 ≤ L := Real.sqrt_nonneg _
      exact (ENNReal.ofReal_le_ofReal_iff hLnn).mp hof
    -- equality and the v-ball bound
    have hL_eq : L = cR * (t - s) := le_antisymm hdrop hL_ge
    have hsqrtL : Real.sqrt ((ge p) v v) = cR * (t - s) := by
      simpa [L] using hL_eq
    have hvδ : v ∈ ball (0 : E) δu := by
      rw [mem_ball, dist_eq_norm, sub_zero]
      have hy0 : p ∈ ball x₀ rgeo := hC_mem_geo s hs
      have hPD : (m0 / 2) * ‖v‖ ^ 2 ≤ (ge p) v v := by
        dsimp [p]
        exact hgeo_lower (C s) hy0 v
      have hsq0 : (m0 / 2) * ‖v‖ ^ 2 ≤ (cR * (t - s)) ^ 2 := by
        calc
          (m0 / 2) * ‖v‖ ^ 2 ≤ (ge p) v v := hPD
          _ = L ^ 2 := by
            have hnn : 0 ≤ (ge p) v v := by
              by_cases hv0 : v = 0
              · rw [hv0]; simp
              · exact le_of_lt (hgePos p v hv0)
            rw [Real.sq_sqrt hnn]
          _ = (cR * (t - s)) ^ 2 := by rw [hL_eq]
      have hnn1 : 0 ≤ Real.sqrt (m0 / 2) * ‖v‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg v)
      have hnn2 : 0 ≤ cR * (t - s) := mul_nonneg hcR_nonneg (le_of_lt hstep)
      have hsq : (Real.sqrt (m0 / 2) * ‖v‖) ^ 2 ≤ (cR * (t - s)) ^ 2 := by
        calc
          (Real.sqrt (m0 / 2) * ‖v‖) ^ 2 = (m0 / 2) * ‖v‖ ^ 2 := by
            rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ m0 / 2)]
          _ ≤ (cR * (t - s)) ^ 2 := hsq0
      have hmain : Real.sqrt (m0 / 2) * ‖v‖ ≤ cR * (t - s) := (sq_le_sq₀ hnn1 hnn2).mp hsq
      have hpos : 0 < Real.sqrt (m0 / 2) := Real.sqrt_pos.2 (by positivity)
      have hle : ‖v‖ ≤ (cR / Real.sqrt (m0 / 2)) * (t - s) := by
        rw [div_mul_eq_mul_div]
        rw [le_div_iff₀ hpos]
        nlinarith [hmain]
      have hlt2 : (cR / Real.sqrt (m0 / 2)) * (t - s) < δu := by
        simpa [div_eq_mul_inv, mul_assoc] using hsmallv
      exact lt_of_le_of_lt hle hlt2
    -- equality case: const-speed staying curve from p to expb v is the radial curve
    have hconst_speed : ∀ s' ∈ Ioo (0 : ℝ) 1,
        Model.mgSpeed ge (ct s') (deriv ct s') = Real.sqrt ((ge p) v v) := by
      intro s' hs'
      rw [hsp s' hs']
      exact hsqrtL.symm
    have hres := Submission.NeckEq.neck_eq_per_base (g := ge) (hg := hgeC) (hinv := hinv) (hsym := hgeSymm) (hpos := hgePos)
      p (τf := τf) hτf (Lf := Lf) (Φ := Φr)
      (hPerB := hPerB0) (hLipB := hLipB0) (K0 := K0) (hK0 := hK0nn) (hKb := hKb0)
      (τu := τu) (δu := δu) (ρE := ρE) (hτu0 := hτu0) (hδu0 := hδu0) (hρE0 := hρE0)
      (h8τuτf := h8τuτf) (h4ρEτu := h4ρEτu) (hδuρE := hδuρE) (hUb := hUbP)
      D hvδ hc0 hc1 hO hstayc hconst_speed
    refine ⟨v, ?_, ?_, ?_, ?_⟩
    · exact hvδ
    · exact hsqrtL
    · exact by
        simpa [q', p] using ((D.expform v).symm.trans hexp_v).symm
    · intro τ hτ
      have hmain := hres τ hτ
      change ct τ = expOf (C s) Φr τu (τ • v)
      rw [hmain]
      exact D.expform (τ • v)

  -- (T0) C is Bv-Lipschitz on the subneck (from ‖C'‖ ≤ Bv)
  have hC_lip {u v : ℝ} (hu : u ∈ Ioo t2C b) (hv : v ∈ Ioo t2C b) (huv : u ≤ v) :
      ‖C v - C u‖ ≤ Bv * (v - u) := by
    have hseg (x : ℝ) (hx : x ∈ Icc u v) : HasDerivWithinAt C (deriv C x) (Icc u v) x := by
      have hxu : x ∈ Ioo t2C b := by
        constructor
        · have h1 : t2C < u := hu.1
          exact lt_of_lt_of_le h1 hx.1
        · have h1 : v < b := hv.2
          exact lt_of_le_of_lt hx.2 h1
      have hx2 : x ∈ Ioo t2 b := ⟨lt_trans ht2B_a (lt_trans ht2C_B hxu.1), hxu.2⟩
      exact (hC_diffAt x hx2).hasDerivAt.hasDerivWithinAt
    have hbnd : ∀ x ∈ Ico u v, ‖deriv C x‖ ≤ Bv := by
      intro x hx
      have hxu : x ∈ Ioo t2C b := by
        constructor
        · have h1 : t2C < u := hu.1
          exact lt_of_lt_of_le h1 hx.1
        · have h1 : x < v := hx.2
          exact lt_trans h1 hv.2
      exact hder_bnd x hxu
    have hvcc : v ∈ Icc u v := ⟨huv, le_rfl⟩
    exact norm_image_sub_le_of_norm_deriv_le_segment' (f := C) (a := u) (b := v) (f' := fun x => deriv C x)
      (C := Bv) hseg hbnd v hvcc

  -- (T1) per-point: C solves the model geodesic ODE at every point of (t2C,b).
  have hC_ode (t0 : ℝ) (ht0 : t0 ∈ Ioo t2C b) :
      HasDerivAt C (deriv C t0) t0 ∧
      HasDerivAt (deriv C)
        (Submission.Model.accel (ge (C t0)) (fderiv ℝ ge (C t0)) (deriv C t0)) t0 := by
    have ht0ab : t0 ∈ Ioo a b := ⟨lt_trans ht2_a (lt_trans ht2B_a (lt_trans ht2C_B ht0.1)), ht0.2⟩
    rcases hγ t0 ht0ab with ⟨δ0, hδ00, hwin⟩
    have hLfp : 0 < (Lf : ℝ) + 1 := by positivity
    have hsqrtpos : 0 < Real.sqrt (m0 / 2) := Real.sqrt_pos.2 (by positivity)
    -- pair radius (halved quantities give strict conclusions)
    let α : ℝ := min (δ0 / 2) (min ((t0 - t2C) / 4) (min ((b - t0) / 4)
      (min (δu / (4 * Bv)) (min ((δu * Real.sqrt (m0 / 2)) / (4 * cR))
        (min (1 / 4) (ρT * τu * Real.sqrt (m0 / 2) / (8 * cR * ((Lf : ℝ) + 1))))))))
    have ha00 : 0 < α := by
      dsimp [α]
      have hA : 0 < δ0 / 2 := by positivity
      have hB : 0 < (t0 - t2C) / 4 := by
        exact div_pos (sub_pos.mpr ht0.1) (by norm_num)
      have hC : 0 < (b - t0) / 4 := by
        exact div_pos (sub_pos.mpr ht0.2) (by norm_num)
      have hD : 0 < δu / (4 * Bv) := by positivity
      have hE : 0 < (δu * Real.sqrt (m0 / 2)) / (4 * cR) := by positivity
      have hF : 0 < (1 : ℝ) / 4 := by norm_num
      have hG : 0 < ρT * τu * Real.sqrt (m0 / 2) / (8 * cR * ((Lf : ℝ) + 1)) := by positivity
      exact lt_min hA (lt_min hB (lt_min hC (lt_min hD (lt_min hE (lt_min hF hG)))))
    have hα0 : 0 < α := ha00
    have hα_lt_δ0 : α < δ0 := by
      have h1 : α ≤ δ0 / 2 := by dsimp [α]; exact min_le_left _ _
      linarith [h1, hδ00]
    have hα_lt_st2C : α < (t0 - t2C) / 2 := by
      have h1 : α ≤ (t0 - t2C) / 4 := by dsimp [α]; exact le_trans (min_le_right _ _) (min_le_left _ _)
      linarith [h1, ht0.1]
    have hα_lt_bt0 : α < (b - t0) / 2 := by
      have h1 : α ≤ (b - t0) / 4 := by dsimp [α]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
      linarith [h1, ht0.2]
    have hα_le_δuBv : α ≤ δu / (4 * Bv) := by dsimp [α]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
    have hα_le_vsmall : α ≤ δu * Real.sqrt (m0 / 2) / (4 * cR) := by dsimp [α]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
    have hα_le_one : α ≤ 1 / 4 := by dsimp [α]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))))
    have hα_le_T : α ≤ ρT * τu * Real.sqrt (m0 / 2) / (8 * cR * ((Lf : ℝ) + 1)) := by
      dsimp [α]
      exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))))
    let s : ℝ := t0 - α
    let t : ℝ := t0 + α
    have hs_mem : s ∈ Ioo t2C b := by
      dsimp [s]
      constructor
      · have h1 : t2C < t0 - α := by linarith [hα_lt_st2C, ht0.1]
        exact h1
      · have h1 : t0 - α < t0 + α := by linarith [hα0]
        have h2 : t0 + α < b := by linarith [hα_lt_bt0, ht0.2]
        exact lt_trans h1 h2
    have ht_mem : t ∈ Ioo t2C b := by
      dsimp [t]
      constructor
      · have h1 : t2C < t0 - α := by linarith [hα_lt_st2C, ht0.1]
        have h2 : t0 - α < t0 + α := by linarith [hα0]
        exact lt_trans h1 h2
      · have h1 : t0 + α < b := by linarith [hα_lt_bt0, ht0.2]
        exact h1
    have hst : s < t := by dsimp [s, t]; linarith [hα0]
    have hwin_in (u : ℝ) (hu : u ∈ Icc s t) : u ∈ Ioo (max a (t0 - δ0)) (min b (t0 + δ0)) := by
      have hu_lo : t0 - δ0 < u := by
        have h1 : t0 - δ0 < t0 - α := by linarith [hα_lt_δ0]
        have h2 : t0 - α ≤ u := by
          dsimp [s] at hu
          exact hu.1
        linarith
      have hu_hi : u < t0 + δ0 := by
        have h1 : t0 + α < t0 + δ0 := by linarith [hα_lt_δ0]
        have h2 : u ≤ t0 + α := by
          dsimp [t] at hu
          exact hu.2
        linarith
      have hau : a < u := by
        have h1 : a < t2 := ht2_a
        have h2 : t2 < t2B := ht2B_a
        have h3 : t2B < t2C := ht2C_B
        have h4 : t2C < t0 - α := by linarith [hα_lt_st2C, ht0.1]
        have h5 : t0 - α ≤ u := by dsimp [s] at hu; exact hu.1
        linarith
      have hub : u < b := by
        have h1 : u ≤ t0 + α := by dsimp [t] at hu; exact hu.2
        have h2 : t0 + α < b := ht_mem.2
        linarith
      constructor
      · exact max_lt hau hu_lo
      · exact lt_min hub hu_hi
    have hexactSub : ∀ u v : ℝ, u ∈ Icc s t → v ∈ Icc s t →
        edist (γ u) (γ v) = (c : ℝ≥0∞) * ENNReal.ofReal |v - u| := by
      intro u v hu hv
      exact hwin u v (hwin_in u hu) (hwin_in v hv)
    have hstay_c : ∀ u ∈ Icc s t, ‖C u - C s‖ < δu := by
      intro u hu
      have huT : u ∈ Ioo t2C b := by
        constructor
        · have h1 : t2C < t0 - α := by linarith [hα_lt_st2C, ht0.1]
          have h2 : t0 - α ≤ u := by dsimp [s] at hu; exact hu.1
          exact lt_of_lt_of_le h1 h2
        · have h1 : u ≤ t0 + α := by dsimp [t] at hu; exact hu.2
          have h2 : t0 + α < b := ht_mem.2
          exact lt_of_le_of_lt h1 h2
      have hus : s ≤ u := hu.1
      have hle := hC_lip hs_mem huT hus
      have h1 : u - s ≤ 2 * α := by
        dsimp [s]
        have h2 : u ≤ t0 + α := by dsimp [t] at hu; exact hu.2
        linarith
      have h2 : Bv * (u - s) ≤ Bv * (2 * α) := by
        exact mul_le_mul_of_nonneg_left h1 (le_of_lt hBv0)
      have h3 : Bv * (2 * α) < δu := by
        have h4 : Bv * (2 * α) ≤ δu / 2 := by
          have h5 : Bv * (2 * α) ≤ Bv * (2 * (δu / (4 * Bv))) := by
            have h6 : 2 * α ≤ 2 * (δu / (4 * Bv)) :=
              mul_le_mul_of_nonneg_left hα_le_δuBv (by norm_num)
            exact mul_le_mul_of_nonneg_left h6 (le_of_lt hBv0)
          have h7 : Bv * (2 * (δu / (4 * Bv))) = δu / 2 := by
            field_simp [ne_of_gt hBv0]
            ring
          linarith
        linarith [hδu0]
      exact lt_of_le_of_lt (le_trans hle h2) h3

    -- no-return of the C arc (chart injectivity + subpair exactness)
    have hInjArc : ∀ u ∈ Ioo s t, C u ≠ C s := by
      intro u hu
      have huI : u ∈ Icc s t := ⟨le_of_lt hu.1, le_of_lt hu.2⟩
      have hsI : s ∈ Icc s t := ⟨le_rfl, le_of_lt hst⟩
      have hex : edist (γ u) (γ s) = (c : ℝ≥0∞) * ENNReal.ofReal (u - s) := by
        have hh := hexactSub u s huI hsI
        have hpos : 0 ≤ u - s := by linarith [hu.1]
        rw [abs_sub_comm] at hh
        rw [abs_of_nonneg hpos] at hh
        exact hh
      have hposE : 0 < (c : ℝ≥0∞) * ENNReal.ofReal (u - s) := by
        have hcne : (c : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr (ne_of_gt hc)
        have hrne : ENNReal.ofReal (u - s) ≠ 0 := (ENNReal.ofReal_ne_zero_iff).2 (by linarith [hu.1])
        exact ENNReal.mul_pos hcne hrne
      intro hCeq
      have hγeq : γ u = γ s := by
        have hu2 : u ∈ Ioo t2 b := ⟨lt_trans (lt_trans ht2B_a (lt_trans ht2C_B hs_mem.1)) hu.1, lt_trans hu.2 ht_mem.2⟩
        have hs2 : s ∈ Ioo t2 b := ⟨lt_trans ht2B_a (lt_trans ht2C_B hs_mem.1), hs_mem.2⟩
        calc
          γ u = (extChartAt I q).symm (C u) := hγ_chart hu2
          _ = (extChartAt I q).symm (C s) := by rw [hCeq]
          _ = γ s := (hγ_chart hs2).symm
      have hγne : γ u ≠ γ s := by
        intro hEq
        have hdist : edist (γ u) (γ s) = 0 := by simp [hEq]
        rw [hex] at hdist
        exact (ne_of_gt hposE) hdist
      exact hγne hγeq
    have hsmallv : (cR / Real.sqrt (m0 / 2)) * (t - s) < δu := by
      have h1 : (cR / Real.sqrt (m0 / 2)) * (t - s) ≤ (cR / Real.sqrt (m0 / 2)) * (2 * α) := by
        have hts : t - s ≤ 2 * α := by dsimp [t, s]; linarith
        exact mul_le_mul_of_nonneg_left hts (div_nonneg hcR_nonneg (le_of_lt hsqrtpos))
      have h2 : (cR / Real.sqrt (m0 / 2)) * (2 * α) < δu := by
        have h3 : (cR / Real.sqrt (m0 / 2)) * (2 * α) ≤ δu / 2 := by
          have h4 : (cR / Real.sqrt (m0 / 2)) * (2 * α)
              ≤ (cR / Real.sqrt (m0 / 2)) * (2 * (δu * Real.sqrt (m0 / 2) / (4 * cR))) := by
            have h5 : 2 * α ≤ 2 * (δu * Real.sqrt (m0 / 2) / (4 * cR)) :=
              mul_le_mul_of_nonneg_left hα_le_vsmall (by norm_num)
            exact mul_le_mul_of_nonneg_left h5 (div_nonneg hcR_nonneg (le_of_lt hsqrtpos))
          have h6 : (cR / Real.sqrt (m0 / 2)) * (2 * (δu * Real.sqrt (m0 / 2) / (4 * cR))) = δu / 2 := by
            field_simp [ne_of_gt hcR0, ne_of_gt hsqrtpos]
            ring
          linarith
        linarith [hδu0]
      exact lt_of_le_of_lt h1 h2
    have hsmallT : (Lf : ℝ) / τu * (cR / Real.sqrt (m0 / 2)) * (t - s) < ρT / 2 := by
      have hts : t - s ≤ 2 * α := by dsimp [t, s]; linarith
      have hnonA : 0 ≤ (Lf : ℝ) / τu * (cR / Real.sqrt (m0 / 2)) := by
        have h1 : 0 ≤ (Lf : ℝ) := by exact_mod_cast (Lf : NNReal).2
        have h2 : 0 ≤ (Lf : ℝ) / τu := div_nonneg h1 (le_of_lt hτu0)
        have h3 : 0 ≤ cR / Real.sqrt (m0 / 2) := div_nonneg hcR_nonneg (le_of_lt hsqrtpos)
        exact mul_nonneg h2 h3
      have hle1 : (Lf : ℝ) / τu * (cR / Real.sqrt (m0 / 2)) * (t - s)
          ≤ (Lf : ℝ) / τu * (cR / Real.sqrt (m0 / 2)) * (2 * α) := by
        exact mul_le_mul_of_nonneg_left hts hnonA
      have hle2 : (Lf : ℝ) / τu * (cR / Real.sqrt (m0 / 2)) * (2 * α) ≤ ρT / 4 := by
        have hb : (Lf : ℝ) / τu * (cR / Real.sqrt (m0 / 2)) * (2 * α)
            ≤ (Lf : ℝ) / τu * (cR / Real.sqrt (m0 / 2)) * (2 * (ρT * τu * Real.sqrt (m0 / 2) / (8 * cR * ((Lf : ℝ) + 1)))) := by
          have hA : 2 * α ≤ 2 * (ρT * τu * Real.sqrt (m0 / 2) / (8 * cR * ((Lf : ℝ) + 1))) :=
            mul_le_mul_of_nonneg_left hα_le_T (by norm_num)
          exact mul_le_mul_of_nonneg_left hA hnonA
        have hc : (Lf : ℝ) / τu * (cR / Real.sqrt (m0 / 2)) * (2 * (ρT * τu * Real.sqrt (m0 / 2) / (8 * cR * ((Lf : ℝ) + 1))))
            ≤ ρT / 4 := by
          have hnz : τu ≠ 0 := ne_of_gt hτu0
          have hnz2 : cR ≠ 0 := ne_of_gt hcR0
          have hnz3 : Real.sqrt (m0 / 2) ≠ 0 := ne_of_gt hsqrtpos
          have hnz4 : ((Lf : ℝ) + 1) ≠ 0 := by positivity
          field_simp [hnz, hnz2, hnz3, hnz4]
          have hLf0 : 0 ≤ (Lf : ℝ) := by exact_mod_cast (Lf : NNReal).2
          nlinarith
        exact le_trans hb hc
      exact lt_of_le_of_lt (le_trans hle1 hle2) (by linarith [hρT0])
    have hlt1 : t - s < 1 := by
      dsimp [t, s]
      have h1 : 2 * α ≤ 1 / 2 := by
        have h2 : α ≤ 1 / 4 := hα_le_one
        nlinarith
      linarith [hα0]
    have hexact : edist (γ s) (γ t) = (c : ℝ≥0∞) * ENNReal.ofReal (t - s) := by
      have hsI : s ∈ Icc s t := ⟨le_rfl, le_of_lt hst⟩
      have htI : t ∈ Icc s t := ⟨le_of_lt hst, le_rfl⟩
      have hh := hexactSub s t hsI htI
      have hpos : 0 ≤ t - s := sub_nonneg.mpr (le_of_lt hst)
      rw [abs_of_nonneg hpos] at hh
      exact hh
    rcases hPairGeo hs_mem ht_mem hst hexact hstay_c hInjArc hsmallv hlt1 hexactSub hsmallT with
      ⟨v, hvδ, hsqrt, hCend, hCurve⟩
    -- v is small for the flow data
    have hvτu : ‖v‖ ≤ τu := by
      have hvρ : ‖v‖ < δu := by simpa [dist_eq_norm] using (mem_ball.mp hvδ)
      have hle : δu ≤ τu := hδuτu
      exact le_trans (le_of_lt hvρ) hle

    -- flow-geodesic σ in the rescaled variable over the pair
    let b0 : E := C s
    have hb0B : b0 ∈ ball x₀ ρB := by
      dsimp [b0]
      exact hC_mem_B s hs_mem
    have hb0u : b0 ∈ ball x₀ ρu := ball_subset_ball hρBρu hb0B
    have hPerB0b : ∀ z ∈ closedBall (b0, 0) 1, Φr z 0 = z ∧
        (∀ t ∈ Icc (-τf) τf, HasDerivAt (Φr z) (odeField ge (Φr z t)) t) ∧
        (∀ t : ℝ, Φr z t ∈ closedBall (b0, 0) 2) := by
      intro z hz
      exact hPerBr b0 hb0u z hz
    have hτuτf' : τu < τf := by nlinarith [h8τuτf, hτf]
    let σv : ℝ → E := fun x => expOf b0 Φr τu (x • v)
    have hodeσ := Submission.FlowOdeChild.flow_exp_geodesic_ode ge hgeC hinv b0 (hTf := hτf) (Φ := Φr)
      (hΦ := fun z hz => ⟨(hPerB0b z hz).1, (hPerB0b z hz).2.1⟩) (τu := τu) (hτu0 := hτu0)
      (hτuTf := hτuτf') (v := v) (hv := hvτu) (σ := σv) (hσ := rfl)
    -- C(u') = σv((u' − s)/(t − s)) on (s,t)
    have hCurve_aff (u' : ℝ) (hu' : u' ∈ Ioo s t) : C u' = σv ((u' - s) / (t - s)) := by
      have huI : u' ∈ Icc s t := ⟨le_of_lt hu'.1, le_of_lt hu'.2⟩
      let τ : ℝ := (u' - s) / (t - s)
      have hτ : τ ∈ Icc (0 : ℝ) 1 := by
        dsimp [τ]
        constructor
        · exact div_nonneg (sub_nonneg.mpr (le_of_lt hu'.1)) (sub_nonneg.mpr (le_of_lt hst))
        · have hnum : u' - s ≤ t - s := by linarith [hu'.2]
          exact (div_le_one (sub_pos.mpr hst)).mpr hnum
      have hcv := hCurve τ hτ
      have harg : s + ((u' - s) / (t - s)) * (t - s) = u' := by
        rw [div_mul_cancel₀ (u' - s) (ne_of_gt (sub_pos.mpr hst))]
        ring
      calc
        C u' = C (s + τ * (t - s)) := by rw [harg]
        _ = expOf (C s) Φr τu (τ • v) := hcv
        _ = expOf b0 Φr τu (τ • v) := by dsimp [b0]
        _ = σv ((u' - s) / (t - s)) := by
          dsimp [σv, τ]
    have ht0st : t0 ∈ Ioo s t := by
      dsimp [s, t]
      constructor <;> linarith [hα0]
    have hre := Submission.ReparamChild.reparam_geodesic_ode ge hgeC (σ := σv)
      (hσd := fun x hx => (hodeσ x hx).1.differentiableAt.hasDerivAt)
      (hσd2 := fun x hx => (hodeσ x hx).2)
      (s := s) (t := t) (u := t0) hst ht0st
    -- hre : let c := fun w => σv ((w - s) / (t - s)); ODE facts for c at t0
    have hC_eq_ev : C =ᶠ[𝓝 t0] (fun w => σv ((w - s) / (t - s))) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht0st] with w hw
      exact hCurve_aff w hw
    have hdev_pt (w : ℝ) (hw : w ∈ Ioo s t) :
        deriv C w = deriv (fun u => σv ((u - s) / (t - s))) w := by
      have hL : (fun u => σv ((u - s) / (t - s))) =ᶠ[𝓝 w] C := by
        filter_upwards [isOpen_Ioo.mem_nhds hw] with z hz
        exact (hCurve_aff z hz).symm
      exact (Filter.EventuallyEq.deriv_eq hL).symm
    have hderev : deriv C =ᶠ[𝓝 t0] deriv (fun u => σv ((u - s) / (t - s))) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht0st] with w hw
      exact hdev_pt w hw
    have ht0t2 : t0 ∈ Ioo t2 b := ⟨lt_trans ht2B_a (lt_trans ht2C_B ht0.1), ht0.2⟩
    constructor
    · exact (hC_diffAt t0 ht0t2).hasDerivAt
    · -- transfer the second-derivative fact of the rescaled geodesic to C
      have hB0 : HasDerivAt (deriv (fun u => σv ((u - s) / (t - s))))
          (Submission.Model.accel (ge (C t0)) (fderiv ℝ ge (C t0)) (deriv C t0)) t0 := by
        have hc0eq : (fun u => σv ((u - s) / (t - s))) t0 = C t0 := by
          exact (hCurve_aff t0 ht0st).symm
        have hdc0 : deriv (fun u => σv ((u - s) / (t - s))) t0 = deriv C t0 := (hdev_pt t0 ht0st).symm
        have h2 := hre.2
        have hval : Submission.Model.accel (ge ((fun u => σv ((u - s) / (t - s))) t0))
            (fderiv ℝ ge ((fun u => σv ((u - s) / (t - s))) t0))
            (deriv (fun u => σv ((u - s) / (t - s))) t0)
            = Submission.Model.accel (ge (C t0)) (fderiv ℝ ge (C t0)) (deriv C t0) := by
          rw [hc0eq, hdc0]
        exact h2.congr_deriv hval

      exact hB0.congr_of_eventuallyEq hderev


  -- (T2) C is eventually an expm-ray; conclude that γ is an ExpM-ray.
  rcases Submission.NeckFlow.flow_limit_ray (g := ge) (hg := hgeC) (hinv := hinv)
      (hsym := hgeSymm) (hpos := hgePos) (x0 := x₀) (τe := τe) (hτe := hτe0) (Φ := Φ)
      (hΦ := hΦODE) (ρe := ρe) (hρe := hρe0) (hρeτe := hρeτe4) (expm := expm)
      (hexp0 := hexp0) (hexpform := hexpform) (cR := cR) (hcR := hcR0) (b := b)
      (t1 := t2C) (ht1 := ht2C_b) (c := C) (vel := deriv C)
      (hcder := fun t ht => (hC_ode t ht).1)
      (hvder := fun t ht => (hC_ode t ht).2)
      (hclim := hC_tend)
      (hcspeed := fun t ht => hC_speed t ⟨lt_trans ht2B_a (lt_trans ht2C_B ht.1), ht.2⟩)
    with ⟨w, hsqrtw, δ, hδ0, hray⟩
  let V : E := -w
  have hw1p : 0 < ‖w‖ + 1 := by positivity
  let δ₀ : ℝ := min δ (min (b - t2) ((ρe / 2) / (‖w‖ + 1)))
  have hδ₀pos : 0 < δ₀ := by
    dsimp [δ₀]
    exact lt_min hδ0 (lt_min (sub_pos.mpr ht2_b) (div_pos (half_pos hρe0) hw1p))
  have hδ₀_le_δ : δ₀ ≤ δ := by
    dsimp [δ₀]
    exact min_le_left _ _
  have hδ₀_le_t2 : δ₀ ≤ b - t2 := by
    dsimp [δ₀]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ₀_le_ρ : δ₀ ≤ (ρe / 2) / (‖w‖ + 1) := by
    dsimp [δ₀]
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hsqrtV : Real.sqrt ((ge (extChartAt I q q)) V V) = c := by
    have hV2 : (ge (extChartAt I q q)) V V = (ge (extChartAt I q q)) w w := by
      dsimp [V]
      simp
    rw [hV2]
    have hsq1 : Real.sqrt ((ge (extChartAt I q q)) w w) = cR := by
      simpa [x₀] using hsqrtw
    simpa [cR] using hsq1
  refine ⟨δ₀, hδ₀pos, V, hsqrtV, ?_⟩
  intro t ht
  have ht2 : t ∈ Ioo t2 b := by
    constructor
    · have hle : t2 ≤ b - δ₀ := by linarith [hδ₀_le_t2]
      exact lt_of_le_of_lt hle ht.1
    · exact ht.2
  have htδ : t ∈ Ioo (b - δ) b := by
    constructor
    · have hle : b - δ ≤ b - δ₀ := by linarith [hδ₀_le_δ]
      exact lt_of_le_of_lt hle ht.1
    · exact ht.2
  have hbt : b - t < δ₀ := by linarith [ht.1]
  have hf : ‖w‖ / (‖w‖ + 1) ≤ 1 := (div_le_one hw1p).mpr (by linarith)
  have hδw : δ₀ * ‖w‖ < ρe := by
    have h1 : δ₀ * ‖w‖ ≤ ((ρe / 2) / (‖w‖ + 1)) * ‖w‖ :=
      mul_le_mul_of_nonneg_right hδ₀_le_ρ (norm_nonneg w)
    have heq : ((ρe / 2) / (‖w‖ + 1)) * ‖w‖ = (ρe / 2) * (‖w‖ / (‖w‖ + 1)) := by
      field_simp [hw1p.ne']
    have h2 : (ρe / 2) * (‖w‖ / (‖w‖ + 1)) < ρe := by
      have hle : (ρe / 2) * (‖w‖ / (‖w‖ + 1)) ≤ ρe / 2 * 1 := by
        exact mul_le_mul_of_nonneg_left hf (le_of_lt (half_pos hρe0))
      have hstep : ρe / 2 * 1 = ρe / 2 := by ring
      have hhalf : ρe / 2 < ρe := by linarith [hρe0]
      calc
        (ρe / 2) * (‖w‖ / (‖w‖ + 1)) ≤ ρe / 2 := by simpa [hstep] using hle
        _ < ρe := hhalf
    have h3 : ((ρe / 2) / (‖w‖ + 1)) * ‖w‖ < ρe := by
      rw [heq]
      exact h2
    exact lt_of_le_of_lt h1 h3
  have hnormw : ‖(t - b) • w‖ < ρe := by
    have hnorm : ‖(t - b) • w‖ = (b - t) * ‖w‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr (le_of_lt ht.2))]
      ring
    have hle1 : (b - t) * ‖w‖ ≤ δ₀ * ‖w‖ := by
      exact mul_le_mul_of_nonneg_right (le_of_lt hbt) (norm_nonneg w)
    calc
      ‖(t - b) • w‖ = (b - t) * ‖w‖ := hnorm
      _ ≤ δ₀ * ‖w‖ := hle1
      _ < ρe := hδw
  have hmemρe : (t - b) • w ∈ ball (0 : E) ρe := by
    rw [mem_ball, dist_eq_norm, sub_zero]
    exact hnormw
  calc
    γ t = (extChartAt I q).symm (C t) := hγ_chart ht2
    _ = (extChartAt I q).symm (expm ((t - b) • w)) := by
      rw [hray t htδ]
    _ = ExpM ((t - b) • w) := (hExpExpM ((t - b) • w) hmemρe).symm
    _ = ExpM ((b - t) • V) := by
      congr 1
      have hvec : (t - b) • w = (b - t) • (-w) := by
        rw [show t - b = -(b - t) by ring]
        rw [neg_smul, smul_neg]
      simpa [V] using hvec
end NeckCore2
end Submission
