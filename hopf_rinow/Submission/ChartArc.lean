import ChallengeDeps
import Submission.ChartNormal
import Submission.ModelNormalBall
import Submission.LocalExt
import Submission.ArcModel
import Mathlib

open scoped Manifold ENNReal ContDiff Topology
open Set Metric
open Bundle
open MeasureTheory

namespace Submission

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 4000000


/-- Euclidean norm bound for all vectors with `g`-quadratic value at most 1, by homogeneity. -/
lemma unit_norm_bound_all {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (Q : E →L[ℝ] E →L[ℝ] ℝ) (hQpos : ∀ u : E, u ≠ 0 → 0 < Q u u)
    (K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ V : E, Real.sqrt (Q V V) = 1 → ‖V‖ ≤ K) :
    ∀ V : E, ‖V‖ ≤ K * Real.sqrt (Q V V) := by
  intro V
  by_cases hv0 : V = 0
  · simp [hv0]
  · have hnonneg : 0 ≤ Q V V := le_of_lt (hQpos V hv0)
    have hsv : (0 : ℝ) < Real.sqrt (Q V V) := Real.sqrt_pos.2 (hQpos V hv0)
    have hunit : Real.sqrt (Q ((Real.sqrt (Q V V))⁻¹ • V) ((Real.sqrt (Q V V))⁻¹ • V)) = 1 := by
      rw [sqrt_quad_smul_nonneg Q (inv_nonneg.mpr hsv.le) V hnonneg]
      field_simp [ne_of_gt hsv]
    have hb := hK ((Real.sqrt (Q V V))⁻¹ • V) hunit
    have hn : ‖(Real.sqrt (Q V V))⁻¹ • V‖ = (Real.sqrt (Q V V))⁻¹ * ‖V‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hsv.le)]
    calc
      ‖V‖ ≤ (Real.sqrt (Q V V)) * ‖(Real.sqrt (Q V V))⁻¹ • V‖ := by
        rw [hn]
        rw [← mul_assoc]
        rw [mul_inv_cancel₀ hsv.ne']
        simp
      _ ≤ (Real.sqrt (Q V V)) * K := mul_le_mul_of_nonneg_left hb hsv.le
      _ = K * Real.sqrt (Q V V) := by ring

open ContinuousLinearMap

noncomputable section

/-- Norm bound for unit (in the metric Q) vectors: Euclidean norm ≤ K. -/
lemma unit_norm_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (Q : E →L[ℝ] E →L[ℝ] ℝ) (hQpos : ∀ u : E, u ≠ 0 → 0 < Q u u) :
    ∃ K : ℝ, 0 < K ∧ ∀ V : E, Real.sqrt (Q V V) = 1 → ‖V‖ ≤ K := by
  rcases norm_bound_of_quad_le Q hQpos 1 (by norm_num) with ⟨K, hK0, hK⟩
  refine ⟨K, hK0, ?_⟩
  intro V hV
  exact hK V (by rw [hV])

/-!
# chart_arc_linear: two-sided local linearity of short exp-arcs (rigid)

Statement: per point `p` (challenge hypotheses), normal-coordinate data (as in
`Submission.chart_normal`: `ρ₀`, `ge`, `r`, `ExpM`, `S`, `invM`, radial identity
`edist p (ExpM v) = ‖v‖`) PLUS: for every `W` with coordinate metric norm 1 and all small
`s ≤ t`: `edist (ExpM (s•W)) (ExpM (t•W)) = t - s`.

Pairs with `0 ≤ s ≤ t` (same forward ray): PROVED already (see `Submission.LocalExt`: the
forward-ray identity `edist (ExpM(a•W)) (ExpM(b•W)) = (b-a)` for `0 ≤ a ≤ b`, via the radial
identity + reverse triangle + the arc length).  Negative-side pairs follow by applying that to
`-W`.  The remaining content is the STRADDLING lower bound for `s < 0 < t`:

  edist (ExpM (s•W)) (ExpM (t•W)) ≥ t - s

## Exact proof of the straddling lower bound (model first, then transfer)

Let `x₀ := extChartAt I p p`, `φ := extChartAt I p`, and let `exp_m`/`ge` be the model
exponential and coordinate metric from `chart_normal` (or `chart_normal_forward`) data;
`ExpM(λ•W) = φ⁻¹(exp_m(λ•W))`, and `c₀(λ) := exp_m(λ•W)` solves the `ge`-geodesic ODE with
unit `ge`-speed (ray property + `ModelSpeed.speed_const`).

Fix `s < 0 < t`.  Apply `Submission.Model.model_normal_ball (g := ge)` at the base
`b₀ := c₀(s)`.  Its data give a normal image `V_{b₀}` of `b₀`, and (crucially) by the *flow
continuation* property of the model (single ODE on `E × E`), the arc is the exponential arc
from `b₀` with velocity `v(s) := c₀'(s)`, so `exp_{b₀}((t-s)•v(s)) = c₀(t)` and
`‖exp_{b₀}⁻¹(c₀(t))‖_{ge(b₀)} = t-s`.  Hence (staying-curve minimality at `b₀`): every C¹
model curve `c` from `b₀ = c₀(s)` to `c₀(t)` staying in `V_{b₀}` has `mgLength ge c ≥ t-s`.

**Uniform normal radius over the compact arc (helper to prove inside this file).**  There are
`ρu > 0`, `δu > 0` with: for every base `b ∈ ball x₀ ρu`, the `model_normal_ball` data at `b`
have their normal image containing the Euclidean ball `ball b δu`.  To prove it, make the
per-base constructions of `Submission.ModelExpC1.exp_c1` / `Submission.ModelNormalBall` uniform
in the base over a compact neighbourhood of `x₀`: the `ge`-geodesic field is fixed and C³, all
ODE/flow estimates depend continuously on the base (use finite subcovers / compactness for
uniform windows and uniform bounds `‖exp_b v - (b+v)‖ ≤ C‖v‖²`), then a uniform
inverse-function-theorem radius.  (This helper is the main new analytic work of the task.)

**Transfer.**  Choose the normal region `S` (shrink the `chart_normal` data) so small that its
coordinate image lies in `ball x₀ ρu` and in the `ge`-agreement ball.  For a C¹ manifold path
`γ` from `x := ExpM(s•W)` to `y := ExpM(t•W)`:
* if `γ` leaves `S`: length ≥ `c_p` (distance-ball argument; choose `ρa` with `t-s < c_p`);
* if `γ` stays in `S`: its coordinate curve `c` stays in `V_{c₀(s)}` (uniform radius + small
  arc), starts at `c₀(s)`, ends at `c₀(t)`; the coordinate length identity gives
  `pathELength I γ ≥ mgLength ge c ≥ t-s` (reuse `chart_normal`'s transfer machinery:
  `chart_speed` + `ofReal_integral_eq_lintegral_ofReal`).
Therefore `edist x y ≥ t-s`; with the upper bound (the arc itself has length `t-s`), the
identity follows.  Upper bound for straddling pairs: concatenate the two radial geodesics
`p → x` (length `-s`) and `p → y` (length `t`), total `t-s`.

## Reusable verified API
- `Submission.chart_normal`, `Submission.LocalExt.chart_normal_forward` (model data: `ρe`,
  `τe`, `Φ`, `exp`, ray identity), `Submission.LocalExt` forward-ray identity, gluing
  `Metric.IsLocLinear.of_glue`.
- `Submission.Model.model_normal_ball` (any base), `ModelSpeed.speed_const`,
  `ModelUniq.unique_geodesic`, `Submission.Model.mgLength`/`mgSpeed`, `Submission.ExpCore`,
  `Submission.ModelExpC1.exp_c1`.
- Model helpers proved by earlier agents in `Submission/LocalExt.lean` and
  `Submission/ModelNormalBall.lean` (e.g. `norm_bound_of_quad_le`, `bilin_*`).

Do NOT change the statement of `chart_arc_linear`; no placeholders may remain.
-/

theorem chart_arc_linear {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] (p : M) :
    ∃ ρ₀ > 0, ∃ ge : E → E →L[ℝ] E →L[ℝ] ℝ,
      ContDiff ℝ 3 ge ∧
      (∀ y u v : E, (ge y) u v = (ge y) v u) ∧
      (∀ y : E, ∀ v : E, v ≠ 0 → 0 < (ge y) v v) ∧
      (∀ y ∈ ball (extChartAt I p p) ρ₀, ∀ u v : E,
         (ge y) u v = (Bundle.RiemannianBundle.g (E := fun x : M => TangentSpace I x)).inner
                       ((extChartAt I p).symm y)
                       ((mfderiv[range I] (extChartAt I p).symm y) u)
                       ((mfderiv[range I] (extChartAt I p).symm y) v)) ∧
      ∃ r > 0, ∃ ExpM : E → M, ∃ S : Set M, ∃ invM : M → E,
        ExpM 0 = p ∧ S ∈ 𝓝 p ∧
        (∀ v ∈ ball (0 : E) r, ExpM v ∈ S) ∧
        ContinuousOn ExpM (ball (0 : E) r) ∧
        Function.Injective (fun v : {v : E // v ∈ ball (0 : E) r} => ExpM v.1) ∧
        Set.SurjOn ExpM (ball (0 : E) r) S ∧
        (∀ y ∈ S, invM y ∈ ball (0 : E) r ∧ ExpM (invM y) = y) ∧
        (∀ v ∈ ball (0 : E) r, invM (ExpM v) = v) ∧
        (∀ v ∈ ball (0 : E) r,
           edist p (ExpM v) = ENNReal.ofReal (Real.sqrt ((ge (extChartAt I p p)) v v))) ∧
        ∃ ρa : ℝ, 0 < ρa ∧ ρa ≤ r ∧
          ∀ (W : E), Real.sqrt ((ge (extChartAt I p p)) W W) = 1 →
            ∀ ⦃s t : ℝ⦄, s ≤ t → |s| < ρa → |t| < ρa →
              edist (ExpM (s • W)) (ExpM (t • W)) =
                ENNReal.ofReal (t - s) := by
  classical
  let x₀ : E := extChartAt I p p
  rcases chart_normal_forward (I := I) (M := M) p with
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
  have hcp_sub : {y : M | edist p y < ENNReal.ofReal cp} ⊆ S := by
    intro y hy
    have hdist : edist p y < ENNReal.ofReal cp := hy
    have hdist2 : edist y p < ENNReal.ofReal cp := by simpa [edist_comm] using hdist
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
  -- metric ball around p inside the coordinate region `ExpM '' ball 0 r₀`
  let c'' : ℝ := min (r₀ / (2 * K)) (cp / 2)
  have hc''pos : 0 < c'' := by
    dsimp [c'']
    exact lt_min (div_pos hr₀pos (by positivity)) (half_pos hcp0)
  have hc''_cp : c'' ≤ cp / 2 := by dsimp [c'']; exact min_le_right _ _
  have hc''_r0 : c'' ≤ r₀ / (2 * K) := by dsimp [c'']; exact min_le_left _ _
  have hballR : {y : M | edist p y < ENNReal.ofReal c''} ⊆ ExpM '' ball (0 : E) r₀ := by
    intro y hy
    have hycp : edist p y < ENNReal.ofReal cp := by
      have hlt : ENNReal.ofReal c'' < ENNReal.ofReal cp := by
        exact (ENNReal.ofReal_lt_ofReal_iff hcp0).mpr (by linarith [hc''_cp, hcp0])
      exact lt_trans hy hlt
    have hyS : y ∈ S := hcp_sub (by simpa [edist_comm] using hycp)
    rcases hInvS y hyS with ⟨hinvball, hExpInv⟩
    have hrad := hRadial (invM y) hinvball
    have hE : edist p y = ENNReal.ofReal (Real.sqrt ((ge x₀) (invM y) (invM y))) := by
      have hrad' := hRadial (invM y) hinvball
      rw [hExpInv] at hrad'
      simpa [x₀] using hrad'
    have hlt2 : ENNReal.ofReal (Real.sqrt ((ge x₀) (invM y) (invM y))) < ENNReal.ofReal c'' := by
      have hy' := hy
      change edist p y < ENNReal.ofReal c'' at hy'
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
  refine ⟨ρ0, hρ00, ge, hgeC, hgeSymm, hgePos, hgeAgree, ⟨r, hr0, ExpM, S, invM,
    hExpM0, hSnhds, hS_in, hExpCont, hInj, hSurj, hInvS, hInvExp, hRadial,
    ⟨ρa, hρa0, hρale_r, ?main⟩⟩⟩
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
    · -- straddling pair s < 0 < t: upper bound easy (triangle via p), lower bound = core
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
      have hds : edist (ExpM (s • W)) p = ENNReal.ofReal (-s) := by
        have hd := hRadial (s • W) hsW_r
        calc
          edist (ExpM (s • W)) p = ENNReal.ofReal (Real.sqrt ((ge x₀) (s • W) (s • W))) := by
              simpa [x₀, edist_comm] using hd
          _ = ENNReal.ofReal (-s) := by rw [hsqrt_s]
      have hdt : edist p (ExpM (t • W)) = ENNReal.ofReal t := by
        have hd := hRadial (t • W) htW_r
        calc
          edist p (ExpM (t • W)) = ENNReal.ofReal (Real.sqrt ((ge x₀) (t • W) (t • W))) := by
              simpa [x₀] using hd
          _ = ENNReal.ofReal t := by rw [hsqrt_t]
      have htri : edist (ExpM (s • W)) (ExpM (t • W)) ≤
          edist (ExpM (s • W)) p + edist p (ExpM (t • W)) :=
        edist_triangle (x := ExpM (s • W)) (y := p) (z := ExpM (t • W))
      have hup : edist (ExpM (s • W)) (ExpM (t • W)) ≤ ENNReal.ofReal (t - s) := by
        calc
          edist (ExpM (s • W)) (ExpM (t • W))
              ≤ edist (ExpM (s • W)) p + edist p (ExpM (t • W)) := htri
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
          have hxSrc : ExpM (s • W) ∈ (extChartAt I p).source := by
            have hE : ExpM (s • W) = (extChartAt I p).symm (expm (s • W)) := by
              have := hExpExpM (s • W) hsW_ρe
              simpa using this
            rw [hE]
            exact (extChartAt I p).map_target (hρTtgt (hExpSrc (s • W) hsW_ρe))
          have hySrc : ExpM (t • W) ∈ (extChartAt I p).source := by
            have hE : ExpM (t • W) = (extChartAt I p).symm (expm (t • W)) := by
              have := hExpExpM (t • W) htW_ρe
              simpa using this
            rw [hE]
            exact (extChartAt I p).map_target (hρTtgt (hExpSrc (t • W) htW_ρe))
          -- every point of the short path lies in `ExpM '' ball 0 r₀`
          have hγR : ∀ u ∈ Icc (0 : ℝ) 1, γ u ∈ ExpM '' ball (0 : E) r₀ := by
            intro u hu
            have hlen_u : edist (ExpM (s • W)) (γ u) ≤ Manifold.pathELength I γ 0 1 := by
              have htmp : Manifold.riemannianEDist I (ExpM (s • W)) (γ u) ≤ Manifold.pathELength I γ 0 u :=
                Manifold.riemannianEDist_le_pathELength (I := I) (hγOn (Icc (0 : ℝ) u)) hγ0 rfl hu.1
              have hmono := htmp.trans (Manifold.pathELength_mono (a := 0) (a' := 0) (b := u) (b' := 1) le_rfl hu.2)
              rwa [← IsRiemannianManifold.out (I := I) (ExpM (s • W)) (γ u)] at hmono
            have htri' : edist p (γ u) ≤ edist p (ExpM (s • W)) + edist (ExpM (s • W)) (γ u) :=
              edist_triangle (x := p) (y := ExpM (s • W)) (z := γ u)
            have hds_comm : edist p (ExpM (s • W)) = ENNReal.ofReal (-s) := by
              simpa [edist_comm] using hds
            have hsum : edist p (ExpM (s • W)) + edist (ExpM (s • W)) (γ u) < ENNReal.ofReal c'' := by
              have hsum_le : edist p (ExpM (s • W)) + edist (ExpM (s • W)) (γ u)
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
            have hmem : edist p (γ u) < ENNReal.ofReal c'' := lt_of_le_of_lt htri' hsum
            exact hballR hmem
          -- coordinate curve of γ
          have hγsrc : ∀ u ∈ Icc (0 : ℝ) 1, γ u ∈ (extChartAt I p).source := by
            intro u hu
            rcases hγR u hu with ⟨v, hv, hEqv⟩
            have hEqs : γ u = (extChartAt I p).symm (expm v) := by
              have hE : ExpM v = (extChartAt I p).symm (expm v) := by
                have := hExpExpM v (ball_subset_ball hr₀ρe hv)
                simpa using this
              rw [← hEqv]
              exact hE
            rw [hEqs]
            exact (extChartAt I p).map_target (hρTtgt (hExpTRegion v hv))
          let ccoor : ℝ → E := fun uu => (extChartAt I p) (γ uu)
          let gamT : ℝ → M := fun uu => (extChartAt I p).symm (ccoor uu)
          have hγeqgamT : Set.EqOn γ gamT (Icc (0 : ℝ) 1) := by
            intro uu huu
            dsimp [gamT, ccoor]
            exact (PartialEquiv.left_inv (extChartAt I p) (hγsrc uu huu)).symm
          have hplEq : Manifold.pathELength I γ 0 1 = Manifold.pathELength I gamT 0 1 :=
            Manifold.pathELength_congr hγeqgamT
          -- ccoor is C¹ on an open set containing [0,1]
          have hOγ : ∃ O : Set ℝ, IsOpen O ∧ Icc (0 : ℝ) 1 ⊆ O ∧ ContDiffOn ℝ 1 ccoor O := by
            let O : Set ℝ := γ ⁻¹' (extChartAt I p).source
            have hγcont : Continuous γ := hγsm.continuous
            have hOopen : IsOpen O := hγcont.isOpen_preimage (extChartAt I p).source
              (isOpen_extChartAt_source (I := I) p)
            have hOIcc : Icc (0 : ℝ) 1 ⊆ O := by
              intro uu huu
              simpa [O] using (hγsrc uu huu)
            have hγOnO : ContMDiffOn 𝓘(ℝ,ℝ) I 1 γ O := hγsm.contMDiffOn
            have hphi : ContMDiffOn I 𝓘(ℝ, E) 1 (extChartAt I p) (chartAt H p).source := by
              have hfull : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I p) (chartAt H p).source :=
                contMDiffOn_extChartAt (I := I) (x := p)
              exact hfull.of_le (by norm_num : (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω))
            have hsubO : O ⊆ γ ⁻¹' (chartAt H p).source := by
              intro uu huu
              simpa [O, extChartAt_source] using huu
            have hcomp : ContMDiffOn 𝓘(ℝ,ℝ) 𝓘(ℝ,E) 1 ((extChartAt I p) ∘ γ) O := by
              exact ContMDiffOn.comp hphi hγOnO hsubO
            have hcomp' : ContDiffOn ℝ 1 ((extChartAt I p) ∘ γ) O :=
              contMDiffOn_iff_contDiffOn.mp hcomp
            refine ⟨O, hOopen, hOIcc, ?_⟩
            convert hcomp' using 1
            funext uu
            rfl
          -- ccoor endpoints and staying in the model region
          have hccoor0 : ccoor 0 = expm (s • W) := by
            dsimp [ccoor]
            rw [hγ0]
            have hE : ExpM (s • W) = (extChartAt I p).symm (expm (s • W)) := by
              have := hExpExpM (s • W) hsW_ρe
              simpa using this
            rw [hE]
            exact PartialEquiv.right_inv (extChartAt I p) (hρTtgt (hExpSrc (s • W) hsW_ρe))
          have hccoor1 : ccoor 1 = expm (t • W) := by
            dsimp [ccoor]
            rw [hγ1]
            have hE : ExpM (t • W) = (extChartAt I p).symm (expm (t • W)) := by
              have := hExpExpM (t • W) htW_ρe
              simpa using this
            rw [hE]
            exact PartialEquiv.right_inv (extChartAt I p) (hρTtgt (hExpSrc (t • W) htW_ρe))
          have hccoorModel : ∀ uu ∈ Icc (0 : ℝ) 1, ccoor uu ∈ ball x₀ ρA := by
            intro uu huu
            rcases hγR uu huu with ⟨v, hv, hEqv⟩
            have hval : ccoor uu = expm v := by
              dsimp [ccoor]
              have hEqs : γ uu = (extChartAt I p).symm (expm v) := by
                have hE : ExpM v = (extChartAt I p).symm (expm v) := by
                  have := hExpExpM v (by
                    exact (ball_subset_ball hr₀ρe (by simpa [dist_eq_norm] using hv)))
                  simpa using this
                rw [← hEqv]
                exact hE
              rw [hEqs]
              exact PartialEquiv.right_inv (extChartAt I p) (hρTtgt (hExpTRegion v hv))
            rw [hval]
            exact hExpModelRegion v hv
          have hccoorAgree : ∀ uu ∈ Icc (0 : ℝ) 1, ccoor uu ∈ ball x₀ ρT := by
            intro uu huu
            rcases hγR uu huu with ⟨v, hv, hEqv⟩
            have hval : ccoor uu = expm v := by
              dsimp [ccoor]
              have hEqs : γ uu = (extChartAt I p).symm (expm v) := by
                have hE : ExpM v = (extChartAt I p).symm (expm v) := by
                  have := hExpExpM v (by
                    exact (ball_subset_ball hr₀ρe (by simpa [dist_eq_norm] using hv)))
                  simpa using this
                rw [← hEqv]
                exact hE
              rw [hEqs]
              exact PartialEquiv.right_inv (extChartAt I p) (hρTtgt (hExpTRegion v hv))
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
              have hγe : ∀ uu2 : ℝ, gamT uu2 = (extChartAt I p).symm (ccoor uu2) := by
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
                    ((extChartAt I p).symm y)
                    ((mfderiv[range I] (extChartAt I p).symm y) uu2)
                    ((mfderiv[range I] (extChartAt I p).symm y) vv) := by
                intro y hy uu2 vv
                exact hgeAgree y (ball_subset_ball hρTle hy) uu2 vv
              have hspd := chart_speed_core (I := I) (M := M) p (ρ := ρT) (ge := ge) hagree hρTtgt
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

end

end Submission
