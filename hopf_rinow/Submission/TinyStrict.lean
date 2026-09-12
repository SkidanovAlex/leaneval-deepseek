import ChallengeDeps
import Submission.ChartArc
import Submission.ChartNormal
import Submission.ModelNormalBall
import Mathlib

/-!
# Tiny-scale strict triangle inequality in a normal ball (rigid statement)

Theorem: `Submission.tiny_strict`.

## Statement

At every point `p : M` (challenge hypotheses), build the normal-coordinate data (as in
`Submission.chart_arc_linear`).  Prove the *corner-cut* fact: for two metric-unit vectors `û,
ŵ` that are NOT opposite (`ŵ ≠ -û`), points on the two tiny radial arcs
`ExpM(ε•û)`, `ExpM(ε•ŵ)` are strictly closer than `2ε`:

    theorem tiny_strict {E : Type*} ... (M : Type*) ... [IsRiemannianManifold I M] (p : M) :
        ∃ ρ₀ > 0, ∃ ge : E → E →L[ℝ] E →L[ℝ] ℝ, [chart data as in chart_arc_linear]
          ∧ ∃ r > 0, ∃ ExpM : E → M, ∃ S : Set M, ∃ invM : M → E,
            [homeo + radial identity]
            ∧ ∃ ρt : ℝ, 0 < ρt ∧ ρt ≤ r ∧
              ∀ (û ŵ : E),
                Real.sqrt ((ge (extChartAt I p p)) û û) = 1 →
                Real.sqrt ((ge (extChartAt I p p)) ŵ ŵ) = 1 →
                ŵ ≠ -û →
                ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ ρt ∧
                  ∀ ε : ℝ, 0 < ε → ε < ε₀ →
                    edist (ExpM (ε • û)) (ExpM (ε • ŵ)) <
                      ENNReal.ofReal (2 * ε)

## Why

`Submission.arc_rigidity` (interior rigidity: locally linear curves are radial exp-arcs)
reduces to this "tiny-scale strictness": an exact curve of speed `c` through `p` forces
`edist (ExpM (x s)) (ExpM (x t)) = ‖x s‖ + ‖x t‖` for opposite-side pairs `s<0<t`; with
`‖x s‖ = c|s|`, `‖x t‖ = c t` this equals `c(t-s)`.  At tiny scale with the pair of unit
directions `û = x s/‖x s‖`, `ŵ = x t/‖x t‖` the bound `< 2ε` (for `ŵ ≠ -û`) contradicts the
equality and forces `ŵ = -û` (collinearity).  [An earlier child proved the whole reduction of
`arc_rigidity` to exactly this statement.]

## Proof route

Take metric-unit `û`, `ŵ`, `ŵ ≠ -û`.  We need a path from `ExpM(εû)` to `ExpM(εŵ)` of length
`< 2ε` for small `ε`.

1. **Straight coordinate segment path.**  For `τ ∈ [0,1]`, let
   `η(τ) := exp_m((1-τ)•(εû) + τ•(εŵ))` (the model exponential of `ge` at base
   `x₀ := extChartAt I p p`, so `ExpM(v) = φ⁻¹(exp_m v)`), and `γ(τ) := ExpM((1-τ)•(εû) +
   τ•(εŵ)) = φ⁻¹(η τ)`.  This is a C¹ manifold path from `ExpM(εû)` to `ExpM(εŵ)`.
   Show `pathELength I γ 0 1 ≤ (2 - δ₀) • ε` for some fixed `δ₀ > 0` and all small `ε`, by the
   coordinate length identity (`chart_speed`/`MChartGeodesicUB` machinery): the manifold speed
   at `τ` equals `√(ge (η τ) (η' τ) (η' τ))`.

2. **Displacement of the exponential.**  From the model data (`Submission.ModelExpC1.exp_c1` or
   the flow estimate `‖exp_m v - (x₀ + v)‖ ≤ C ‖v‖²`, verified in `Submission.ModelExp`):
   `η(τ) = x₀ + ε•((1-τ)û + τŵ) + O(ε²)` uniformly in `τ`, and the derivative
   `η'(τ) = ε•(ŵ - û) + O(ε²)`; in particular for small `ε` the whole segment stays in a tiny
   ball around `x₀`.

3. **Metric close to constant on the tiny ball.**  Since `ge` is continuous (indeed C³) at
   `x₀`, for every `λ > 0` there is `ρλ > 0` with:
   for all `y ∈ ball x₀ ρλ` and all vectors `d`, `√(ge y d d) ≤ (1+λ) √(ge x₀ d d)`.
   Choose `λ := δ₁` small.

4. **Conclude.**  For small `ε`, the length of `γ` is at most
   `∫₀¹ (1+λ) √((ge x₀) (η' τ) (η' τ)) dτ ≤ (1+λ) • ε • ‖ŵ - û‖_{ge x₀} • (1+o(1))`
   where `‖ŵ - û‖_{ge x₀} = √((ge x₀)(ŵ-û)(ŵ-û))`.  Since `ŵ ≠ -û` and both are unit for the
   same positive definite form, `‖ŵ - û‖_{ge x₀} < 2` (equality iff `ŵ = -û`); pick `λ, o(1)`
   small enough that the product is `< 2ε`.  Hence
   `edist (ExpM(εû)) (ExpM(εŵ)) ≤ pathELength I γ 0 1 < 2ε`.
   `edist ≤ pathELength` because `edist = riemannianEDist` is the infimum over C¹ paths
   (`Manifold.riemannianEDist_le_pathELength`).

## Reusable API
- `Submission.chart_arc_linear`, `Submission.chart_normal`, `Submission.ModelNormalBall`,
  `Submission.ModelExpC1`, `Submission.ExpCore`, `Submission.LocalExt` (helpers).
- Model facts: `exp_fderiv_zero_id`, displacement bounds, `ModelSpeed`, flow estimates.
- Chart speed identity: `Submission.MChartSpeed.chart_speed_core`; path length bounds:
  `Submission.MChartGeodesicUB.chart_geodesic_pathELength_le`; ENNReal conversions.
- `Manifold.riemannianEDist_le_pathELength` for `edist ≤ length` of C¹ paths.

Do NOT change the statement of `tiny_strict`; you may add helper lemmas and definitions freely.
No placeholders may remain in the file.
-/

open scoped Manifold ENNReal ContDiff Topology
open Set Metric Filter
open ContinuousLinearMap
open Bundle
open MeasureTheory

namespace Submission

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 4000000

/-- `sqrt (1 + x²) ≤ 1 + x` for `x ≥ 0`. -/
lemma sqrt_one_add_sq_le {x : ℝ} (hx : 0 ≤ x) : Real.sqrt (1 + x * x) ≤ 1 + x := by
  have hsq2 : 1 + x * x ≤ (1 + x) ^ 2 := by
    nlinarith [sq_nonneg x]
  have hnonneg : 0 ≤ 1 + x := by positivity
  have hroot : Real.sqrt (1 + x * x) ≤ Real.sqrt ((1 + x) ^ 2) := Real.sqrt_le_sqrt hsq2
  rwa [Real.sqrt_sq_eq_abs, abs_of_nonneg hnonneg] at hroot

/-- The coordinate metric `g` is uniformly `(1+lam)`-close to `g x₀` (in the sense of quadratic
forms) on a small ball around `x₀`. -/
lemma metric_upper_close {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (g : E → E →L[ℝ] E →L[ℝ] ℝ) (hgC : ContDiff ℝ 3 g) (x₀ : E)
    (hpos : ∀ y : E, ∀ v : E, v ≠ 0 → 0 < ((g y) v) v) :
    ∀ lam : ℝ, 0 < lam → ∃ rho : ℝ, 0 < rho ∧
      ∀ y ∈ ball x₀ rho, ∀ z : E,
        Real.sqrt (((g y) z) z) ≤ (1 + lam) * Real.sqrt (((g x₀) z) z) := by
  intro lam hlam
  rcases quad_ellipsoid_bound (g x₀) (hpos x₀) with ⟨m, hm0, hmb⟩
  have hgc : Continuous g := hgC.continuous
  have hgcAt : ContinuousAt g x₀ := hgc.continuousAt
  have hd : ∀ᶠ y in 𝓝 x₀, dist (g y) (g x₀) < lam * lam * m := by
    exact (Metric.continuousAt_iff'.mp hgcAt) (lam * lam * m) (by positivity)
  rcases Metric.mem_nhds_iff.mp hd with ⟨rho, hrho0, hrho⟩
  refine ⟨rho, hrho0, ?_⟩
  intro y hy z
  have hres := hrho hy
  have hnear : ‖g y - g x₀‖ ≤ lam * lam * m := by
    rw [← dist_eq_norm (g y) (g x₀)]
    exact le_of_lt hres
  by_cases hz0 : z = 0
  · subst z
    simp
  · have hQ0 : 0 ≤ ((g x₀) z) z := le_of_lt (hpos x₀ z hz0)
    have hQm : m * ‖z‖ ^ 2 ≤ ((g x₀) z) z := hmb z
    have hbd1 : ‖(g y - g x₀) z‖ ≤ ‖g y - g x₀‖ * ‖z‖ := (g y - g x₀).le_opNorm z
    have habs : ‖(((g y - g x₀) z) z)‖ ≤ ‖g y - g x₀‖ * ‖z‖ ^ 2 := by
      have h21 := ((g y - g x₀) z).le_opNorm z
      calc
        ‖(((g y - g x₀) z) z)‖ ≤ ‖(g y - g x₀) z‖ * ‖z‖ := h21
        _ ≤ (‖g y - g x₀‖ * ‖z‖) * ‖z‖ := mul_le_mul_of_nonneg_right hbd1 (norm_nonneg z)
        _ = ‖g y - g x₀‖ * ‖z‖ ^ 2 := by ring
    have hbd : ((g y) z) z ≤ ((g x₀) z) z + ‖g y - g x₀‖ * ‖z‖ ^ 2 := by
      have hsub : ((g y) z) z - ((g x₀) z) z = ((g y - g x₀) z) z := by simp
      have h : ((g y) z) z - ((g x₀) z) z ≤ ‖((g y - g x₀) z) z‖ := by
        rw [hsub]
        exact le_abs_self _
      linarith
    have hde : ‖g y - g x₀‖ * ‖z‖ ^ 2 ≤ (lam * lam * m) * ‖z‖ ^ 2 := by
      exact mul_le_mul_of_nonneg_right hnear (sq_nonneg ‖z‖)
    have hbd0 : ((g y) z) z ≤ ((g x₀) z) z + (lam * lam * m) * ‖z‖ ^ 2 := by linarith
    have hscal : (lam * lam * m) * ‖z‖ ^ 2 ≤ (lam * lam) * ((g x₀) z) z := by
      have hmm : (lam * lam * m) * ‖z‖ ^ 2 = (lam * lam) * (m * ‖z‖ ^ 2) := by ring
      rw [hmm]
      exact mul_le_mul_of_nonneg_left hQm (by simpa [pow_two] using sq_nonneg lam)
    have hle : ((g y) z) z ≤ (1 + lam * lam) * ((g x₀) z) z := by nlinarith
    have hsqrt : Real.sqrt (((g y) z) z) ≤ Real.sqrt ((1 + lam * lam) * ((g x₀) z) z) :=
      Real.sqrt_le_sqrt hle
    have hroot : Real.sqrt ((1 + lam * lam) * ((g x₀) z) z) =
        Real.sqrt (1 + lam * lam) * Real.sqrt (((g x₀) z) z) := by
      rw [Real.sqrt_mul (by positivity) (((g x₀) z) z)]
    calc
      Real.sqrt (((g y) z) z) ≤ Real.sqrt ((1 + lam * lam) * ((g x₀) z) z) := hsqrt
      _ = Real.sqrt (1 + lam * lam) * Real.sqrt (((g x₀) z) z) := hroot
      _ ≤ (1 + lam) * Real.sqrt (((g x₀) z) z) := by
        exact mul_le_mul_of_nonneg_right (sqrt_one_add_sq_le (le_of_lt hlam)) (Real.sqrt_nonneg _)

/-- The exponential of the flow formula (`exp v = (Φ (x₀, (1 / τe) • v) τe).1` on `ball 0 ρe`)
has derivative the identity at `0`, provided the flow and `exp` satisfy the standard exported
properties of the normal-coordinate chart. -/
lemma quad_sqrt_add_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hsym : ∀ u v : E, B u v = B v u)
    (hpos : ∀ u : E, u ≠ 0 → 0 < B u u) (u v : E) :
    Real.sqrt (B (u + v) (u + v)) ≤ Real.sqrt (B u u) + Real.sqrt (B v v) := by
  have hnn1 : 0 ≤ B u u := by
    by_cases hu : u = 0
    · simp [hu]
    · exact le_of_lt (hpos u hu)
  have hnn2 : 0 ≤ B v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact le_of_lt (hpos v hv)
  have hnn3 : 0 ≤ B (u + v) (u + v) := by
    by_cases h : u + v = 0
    · simp [h]
    · exact le_of_lt (hpos (u+v) h)
  have hx := Model.bilin_quad_add_smul (B := B) hsym u v (1 : ℝ)
  have hx' : B (u + v) (u + v) = B u u + 2 * B u v + B v v := by
    simpa using hx
  have hcs : |B u v| ≤ Real.sqrt (B u u) * Real.sqrt (B v v) :=
    Model.bilin_cauchy_schwarz (B := B) hsym hpos u v
  have hle : B (u+v) (u+v) ≤ (Real.sqrt (B u u) + Real.sqrt (B v v)) ^ 2 := by
    rw [hx']
    let X : ℝ := Real.sqrt (B u u)
    let Y : ℝ := Real.sqrt (B v v)
    have hX2 : X ^ 2 = B u u := by dsimp [X]; exact Real.sq_sqrt hnn1
    have hY2 : Y ^ 2 = B v v := by dsimp [Y]; exact Real.sq_sqrt hnn2
    have hb : B u v ≤ X * Y := by
      have habs : B u v ≤ |B u v| := le_abs_self _
      have h' : |B u v| ≤ X * Y := by simpa [X, Y] using hcs
      linarith
    have hm : 0 ≤ X * Y := mul_nonneg (by dsimp [X]; positivity) (by dsimp [Y]; positivity)
    have hlin : B u u + 2 * B u v + B v v ≤ X ^ 2 + 2 * X * Y + Y ^ 2 := by
      rw [← hX2, ← hY2]
      nlinarith
    have hsq : X ^ 2 + 2 * X * Y + Y ^ 2 = (X + Y) ^ 2 := by ring
    rwa [hsq] at hlin
  have hnn : 0 ≤ Real.sqrt (B u u) + Real.sqrt (B v v) := by positivity
  have hroot : Real.sqrt (B (u+v) (u+v)) ≤ Real.sqrt ((Real.sqrt (B u u) + Real.sqrt (B v v)) ^ 2) :=
    Real.sqrt_le_sqrt hle
  rwa [Real.sqrt_sq_eq_abs, abs_of_nonneg hnn] at hroot

lemma expm_fderiv_zero_id {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (g : E → E →L[ℝ] E →L[ℝ] ℝ) (hgC : ContDiff ℝ 3 g)
    (hinv : ∀ y, ContinuousLinearMap.IsInvertible (g y))
    (x₀ : E) {ρe τe : ℝ} (hρe : 0 < ρe) (hτe : 0 < τe) (hρeτe : ρe ≤ τe / 4)
    (Φ : E × E → ℝ → E × E) (exp : E → E)
    (hΦode : ∀ z ∈ closedBall (x₀, 0) 2, Φ z 0 = z ∧
       ∀ t ∈ Ioo (-((3 / 2) * τe)) ((3 / 2) * τe),
         HasDerivAt (Φ z) (Model.odeField g (Φ z t)) t)
    (hform : ∀ v ∈ ball (0 : E) ρe, exp v = (Φ (x₀, (1 / τe) • v) τe).1)
    (hC : ContDiffOn ℝ 1 exp (ball 0 ρe)) :
    HasFDerivAt exp (ContinuousLinearMap.id ℝ E) 0 := by
  let T0 : ℝ := (5 / 4) * τe
  have hT0pos : 0 < T0 := by dsimp [T0]; positivity
  have hτT0 : τe < T0 := by dsimp [T0]; nlinarith
  have hwin : Icc (-T0) T0 ⊆ Ioo (-((3 / 2) * τe)) ((3 / 2) * τe) := by
    intro t ht
    dsimp [T0] at ht ⊢
    constructor
    · have h1 : -((3 / 2) * τe) < -((5 / 4) * τe) := by
        have hc : -(3 / 2 : ℝ) < -(5 / 4 : ℝ) := by norm_num
        have hm := mul_lt_mul_of_pos_right hc hτe
        simpa [mul_comm] using hm
      exact lt_of_lt_of_le h1 ht.1
    · have h2 : (5 / 4) * τe < (3 / 2) * τe := by
        have hc : (5 / 4 : ℝ) < (3 / 2 : ℝ) := by norm_num
        have hm := mul_lt_mul_of_pos_right hc hτe
        simpa [mul_comm] using hm
      exact lt_of_le_of_lt ht.2 h2
  have hΦc : ∀ z ∈ closedBall (x₀, (0 : E)) 1, Φ z 0 = z ∧
      ∀ t ∈ Icc (-T0) T0, HasDerivAt (Φ z) (Model.odeField g (Φ z t)) t := by
    intro z hz
    have hz2 : z ∈ closedBall (x₀, 0) 2 := closedBall_subset_closedBall (by norm_num) hz
    exact ⟨(hΦode z hz2).1, fun t ht => (hΦode z hz2).2 t (hwin ht)⟩
  let exp' : E → E := fun v => (Φ (x₀, (1 / τe) • v) τe).1
  have hC' : ContDiffOn ℝ 1 exp' (ball 0 ρe) := by
    refine hC.congr ?_
    intro v hv
    exact (hform v hv).symm
  have hrest : Φ (x₀, 0) τe = (x₀, 0) := by
    exact Model.rest_point_fixed g hgC hinv x₀ (τ := T0) hT0pos Φ hΦc (s := τe) (by constructor <;> nlinarith)
  have hExp' : HasFDerivAt exp' (ContinuousLinearMap.id ℝ E) 0 := by
    exact Model.exp_fderiv_zero_id g hgC hinv x₀ (T0 := T0) (τ := τe) hT0pos hτe hτT0 Φ hΦc hrest
      (ρ := ρe) hρe exp' rfl hC'
  have heq : exp =ᶠ[𝓝 (0 : E)] exp' := by
    filter_upwards [ball_mem_nhds (0 : E) hρe] with v hv
    exact hform v hv
  exact hExp'.congr_of_eventuallyEq heq


theorem tiny_strict {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
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
        ∃ ρt : ℝ, 0 < ρt ∧ ρt ≤ r ∧
          ∀ (û ŵ : E),
            Real.sqrt ((ge (extChartAt I p p)) û û) = 1 →
            Real.sqrt ((ge (extChartAt I p p)) ŵ ŵ) = 1 →
            ŵ ≠ -û →
            ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ ρt ∧
              ∀ ε : ℝ, 0 < ε → ε < ε₀ →
                edist (ExpM (ε • û)) (ExpM (ε • ŵ)) < ENNReal.ofReal (2 * ε) := by
  classical
  let x₀ : E := extChartAt I p p
  rcases chart_normal_forward (I := I) (M := M) p with
    ⟨ρ0, hρ00, ge, hgeC, hgeSymm, hgePos, hgeAgree, hrest⟩
  rcases hrest with ⟨r, hr0, ExpM, S, invM, hExpM0, hSnhds, hS_in, hExpCont, hInj,
    hSurj, hInvS, hInvExp, hRadial, hrest2⟩
  rcases hrest2 with ⟨ρe, hρe0, hρele, τe, hτe0, hρeτe4, Φ, expm,
    hExpExpM, hexp0, hExpC1, hΦODE, hexpform, hRay, hrest3⟩
  rcases hrest3 with ⟨hρTrest, hFWD⟩
  rcases hρTrest with ⟨ρT, hρT0, hρTle, hρTtgt, hcv⟩
  let Q : E →L[ℝ] E →L[ℝ] ℝ := ge x₀
  have hQnonneg : ∀ v : E, 0 ≤ (Q v) v := by
    intro v
    by_cases hv : v = 0
    · subst v; simp
    · exact le_of_lt (hgePos x₀ v hv)
  let hinv : ∀ y : E, ContinuousLinearMap.IsInvertible (ge y) :=
    fun y => bilin_isInvertible_of_pos (ge y) (hgePos y)
  rcases norm_bound_of_quad_le Q (hgePos x₀) 1 (by norm_num) with ⟨K, hK0, hKle⟩
  -- expm fderiv data at 0
  have hExpId : HasFDerivAt expm (ContinuousLinearMap.id ℝ E) 0 := by
    exact expm_fderiv_zero_id ge hgeC hinv x₀ hρe0 hτe0 hρeτe4 Φ expm hΦODE hexpform hExpC1
  have hfderiv0 : fderiv ℝ expm 0 = ContinuousLinearMap.id ℝ E := hExpId.fderiv
  have hfdCont : ContinuousOn (fun v : E => fderiv ℝ expm v) (ball (0 : E) ρe) := by
    exact Model.contDiffOn_one_cont_fderiv (isOpen_ball : IsOpen (ball (0 : E) ρe)) hExpC1
  have hfdAt0 : ContinuousAt (fun v : E => fderiv ℝ expm v) (0 : E) := by
    have h0mem : (0 : E) ∈ ball (0 : E) ρe := by simpa using hρe0
    exact hfdCont.continuousAt (by simpa [ball, dist_eq_norm] using (isOpen_ball.mem_nhds h0mem))
  -- quantitative fderiv-closeness to id on a small ball
  have hfdclose : ∀ th : ℝ, 0 < th → ∃ rh : ℝ, 0 < rh ∧
      ∀ v ∈ ball (0 : E) rh, ‖fderiv ℝ expm v - ContinuousLinearMap.id ℝ E‖ ≤ th := by
    intro th hth
    have hd : ∀ᶠ v in 𝓝 (0 : E), dist (fderiv ℝ expm v) (fderiv ℝ expm 0) < th :=
      (Metric.continuousAt_iff'.mp hfdAt0) th hth
    rcases Metric.mem_nhds_iff.mp hd with ⟨rh, hrh0, hrh⟩
    refine ⟨rh, hrh0, ?_⟩
    intro v hv
    have hb : dist (fderiv ℝ expm v) (fderiv ℝ expm 0) < th := by simpa using (hrh hv)
    rw [hfderiv0] at hb
    have hb2 : ‖fderiv ℝ expm v - ContinuousLinearMap.id ℝ E‖ < th := by
      rw [← dist_eq_norm]
      simpa using hb
    exact le_of_lt hb2
  -- value-level continuity of expm at 0
  have hExpCont0 : ContinuousAt expm (0 : E) := by
    have h0mem : (0 : E) ∈ ball (0 : E) ρe := by simpa using hρe0
    exact (hExpC1.contDiffAt (isOpen_ball.mem_nhds h0mem)).continuousAt
  -- Euclidean norm bound for unit (metric) vectors and their differences
  have hKunit : ∀ V : E, Real.sqrt (Q V V) = 1 → ‖V‖ ≤ K := by
    intro V hV
    exact hKle V (by rw [hV])
  -- radius ρt : small enough that the coordinate chords of length ≤ ρt stay in ball 0 ρe
  let ρt : ℝ := min r (ρe / (8 * (K + 1)))
  have hρt0 : 0 < ρt := by
    dsimp [ρt]
    exact lt_min hr0 (div_pos hρe0 (by positivity))
  have hρtle_r : ρt ≤ r := by
    dsimp [ρt]
    exact min_le_left _ _
  refine ⟨ρ0, hρ00, ge, hgeC, hgeSymm, hgePos, hgeAgree, ⟨r, hr0, ExpM, S, invM,
    hExpM0, hSnhds, hS_in, hExpCont, hInj, hSurj, hInvS, hInvExp, hRadial,
    ⟨ρt, hρt0, hρtle_r, ?tiny⟩⟩⟩
  -- ============================================================
  -- strictness claim
  -- ============================================================
  intro û ŵ hûunit hŵunit hnotopp
  by_cases huw : ŵ = û
  · -- identical radial directions: distance 0 < 2ε
    subst ŵ
    refine ⟨ρt, hρt0, le_rfl, ?_⟩
    intro ε hε hεlt
    rw [edist_self]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  · -- main case: û, ŵ unit, pairwise distinct and not opposite
    let d : E := ŵ - û
    have hd_ne : d ≠ 0 := by
      dsimp [d]
      exact sub_ne_zero.mpr huw
    have hQdpos : 0 < Q d d := hgePos x₀ d hd_ne
    have hQdnn : 0 ≤ Q d d := le_of_lt hQdpos
    let A : ℝ := Real.sqrt (Q d d)
    have hA0 : 0 < A := by
      dsimp [A]
      exact Real.sqrt_pos.2 hQdpos
    have hA_lt_2 : A < 2 := by
      -- Q û û = 1, Q ŵ ŵ = 1, Q û ŵ > -1 ⇒ Q d d < 4
      have hQuu : Q û û = 1 := by
        have hsq := Real.sq_sqrt (hQnonneg û)
        calc
          Q û û = (Real.sqrt (Q û û)) ^ 2 := hsq.symm
          _ = 1 := by rw [hûunit]; norm_num
      have hQww : Q ŵ ŵ = 1 := by
        have hsq := Real.sq_sqrt (hQnonneg ŵ)
        calc
          Q ŵ ŵ = (Real.sqrt (Q ŵ ŵ)) ^ 2 := hsq.symm
          _ = 1 := by rw [hŵunit]; norm_num
      have hsum_ne : û + ŵ ≠ 0 := by
        intro hsum
        apply hnotopp
        have : û = -ŵ := by
          rw [← add_eq_zero_iff_eq_neg]
          exact hsum
        rw [this]
        simp
      have hpos_sum : 0 < Q (û + ŵ) (û + ŵ) := hgePos x₀ (û + ŵ) hsum_ne
      have hQuad : Q (û + ŵ) (û + ŵ) = 2 + 2 * (Q û ŵ) := by
        have hx := bilin_quad_add_smul' Q û ŵ (1 : ℝ)
        have hy : (û + (1 : ℝ) • ŵ) = û + ŵ := by simp
        rw [hy] at hx
        have hsym2 : Q ŵ û = Q û ŵ := hgeSymm x₀ ŵ û
        rw [hsym2] at hx
        have hu' : Q û û = 1 := hQuu
        have hw' : Q ŵ ŵ = 1 := hQww
        nlinarith
      have hQuw_gt : -1 < Q û ŵ := by
        nlinarith [hQuad, hpos_sum]
      have hd2 : Q d d = 2 - 2 * (Q û ŵ) := by
        have hx := bilin_quad_sub_smul' Q (fun u v => hgeSymm x₀ u v) ŵ û (1 : ℝ)
        have hy : (ŵ - (1 : ℝ) • û) = d := by
          dsimp [d]
          simp
        rw [hy] at hx
        have hsym2 : Q ŵ û = Q û ŵ := hgeSymm x₀ ŵ û
        rw [hsym2] at hx
        have hu' : Q û û = 1 := hQuu
        have hw' : Q ŵ ŵ = 1 := hQww
        dsimp [d]
        nlinarith
      have hd2lt : Q d d < 4 := by
        have h1 : 2 - 2 * (Q û ŵ) < 4 := by nlinarith [hQuw_gt]
        calc
          Q d d = 2 - 2 * (Q û ŵ) := hd2
          _ < 4 := h1
      -- A = √(Qdd) < √4 = 2
      have hsqrt : Real.sqrt (Q d d) < Real.sqrt (4 : ℝ) := by
        exact (Real.sqrt_lt_sqrt_iff hQdnn).2 hd2lt
      have h4 : Real.sqrt (4 : ℝ) = 2 := by norm_num
      dsimp [A]
      rwa [h4] at hsqrt
    let u : ℝ := 2 - A
    have hu : 0 < u := by dsimp [u]; linarith
    -- tolerances (depend on the pair through u)
    let lamG : ℝ := u / 16
    have hlamG : 0 < lamG := by dsimp [lamG]; positivity
    let B0 : ℝ := Real.sqrt ‖Q‖
    have hB0nn : 0 ≤ B0 := by dsimp [B0]; exact Real.sqrt_nonneg _
    let theta : ℝ := u / (128 * (K + 1) * (B0 + 1))
    have htheta : 0 < theta := by
      dsimp [theta]
      positivity
    -- ==========================================================
    -- metric comparison and smallness radii (depend on the pair)
    -- ==========================================================
    rcases metric_upper_close ge hgeC x₀ hgePos lamG hlamG with ⟨rhoG, hrhoG0, hrhoG⟩
    have hexpball : ∃ δG : ℝ, 0 < δG ∧ ∀ v ∈ ball (0 : E) δG, ‖expm v - x₀‖ < rhoG := by
      have hd : ∀ᶠ v in 𝓝 (0 : E), dist (expm v) x₀ < rhoG := by
        have hh := (Metric.continuousAt_iff'.mp hExpCont0) rhoG hrhoG0
        simpa [x₀, hexp0] using hh
      rcases Metric.mem_nhds_iff.mp hd with ⟨δG, hδG0, hδG⟩
      refine ⟨δG, hδG0, ?_⟩
      intro v hv
      have hb := hδG hv
      rw [← dist_eq_norm (expm v) x₀]
      exact hb
    rcases hexpball with ⟨δG, hδG0, hδG⟩
    rcases hfdclose theta htheta with ⟨rhθ, hrhθ0, hrhθ⟩
    have hKnn : 0 ≤ K := le_of_lt hK0
    let b : ℝ := min (δG / (5 * (K + 1)))
        (min (rhθ / (5 * (K + 1))) (ρe / (5 * (K + 1))))
    let e0 : ℝ := min ρt b
    have hbpos : 0 < b := by
      dsimp [b]
      exact lt_min (div_pos hδG0 (by positivity))
        (lt_min (div_pos hrhθ0 (by positivity)) (div_pos hρe0 (by positivity)))
    have he0pos : 0 < e0 := by
      dsimp [e0]
      exact lt_min hρt0 hbpos
    have he0le_ρt : e0 ≤ ρt := by
      dsimp [e0]
      exact min_le_left _ _
    have he0δG : e0 ≤ δG / (5 * (K + 1)) := by
      dsimp [e0, b]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    have he0rh : e0 ≤ rhθ / (5 * (K + 1)) := by
      dsimp [e0, b]
      exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    have he0ρe : e0 ≤ ρe / (5 * (K + 1)) := by
      dsimp [e0, b]
      exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
    -- norm bounds
    have hdl : ‖d‖ ≤ 2 * K := by
      have h1 : ‖ŵ - û‖ ≤ ‖ŵ‖ + ‖û‖ := norm_sub_le _ _
      have h2 : ‖ŵ‖ ≤ K := hKunit ŵ hŵunit
      have h3 : ‖û‖ ≤ K := hKunit û hûunit
      dsimp [d]
      nlinarith
    have hB0norm : ∀ z : E, Real.sqrt (Q z z) ≤ B0 * ‖z‖ := by
      intro z
      have h1 : ‖Q z‖ ≤ ‖Q‖ * ‖z‖ := Q.le_opNorm z
      have h2 : ‖(Q z) z‖ ≤ ‖Q z‖ * ‖z‖ := (Q z).le_opNorm z
      have h3 : ‖(Q z) z‖ ≤ ‖Q‖ * ‖z‖ ^ 2 := by
        calc
          ‖(Q z) z‖ ≤ ‖Q z‖ * ‖z‖ := h2
          _ ≤ (‖Q‖ * ‖z‖) * ‖z‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg z)
          _ = ‖Q‖ * ‖z‖ ^ 2 := by ring
      have h4 : (Q z) z ≤ ‖Q‖ * ‖z‖ ^ 2 := le_trans (le_abs_self _) h3
      have h5 : Real.sqrt (Q z z) ≤ Real.sqrt (‖Q‖ * ‖z‖ ^ 2) := Real.sqrt_le_sqrt h4
      calc
        Real.sqrt (Q z z) ≤ Real.sqrt (‖Q‖ * ‖z‖ ^ 2) := h5
        _ = Real.sqrt ‖Q‖ * Real.sqrt (‖z‖ ^ 2) := by
          rw [Real.sqrt_mul (norm_nonneg Q) (‖z‖ ^ 2)]
        _ = Real.sqrt ‖Q‖ * ‖z‖ := by
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg z)]
        _ = B0 * ‖z‖ := rfl
    -- error bound for the derivative displacement
    have hErr : 2 * K * B0 * theta ≤ u / 16 := by
      dsimp [theta]
      have hden : 0 < 128 * (K + 1) * (B0 + 1) := by positivity
      have hA0 : 2 * K * B0 ≤ 8 * (K + 1) * (B0 + 1) := by
        nlinarith [hKnn, hB0nn]
      have hmain : (2 * K * B0) * u ≤ (u / 16) * (128 * (K + 1) * (B0 + 1)) := by
        calc
          (2 * K * B0) * u ≤ (8 * (K + 1) * (B0 + 1)) * u := by
            exact mul_le_mul_of_nonneg_right hA0 hu.le
          _ = (u / 16) * (128 * (K + 1) * (B0 + 1)) := by ring
      have hdiv : (2 * K * B0 * u) / (128 * (K + 1) * (B0 + 1)) ≤ u / 16 := by
        exact (div_le_iff₀ hden).2 hmain
      have hsim : 2 * K * B0 * (u / (128 * (K + 1) * (B0 + 1))) =
          (2 * K * B0 * u) / (128 * (K + 1) * (B0 + 1)) := by ring
      rwa [hsim]
    -- target multiplier Nval < 2
    let Nval : ℝ := (1 + lamG) * (A + u / 16)
    have hNval2 : Nval < 2 := by
      dsimp [Nval, lamG, u]
      have hmain : (1 + (2 - A) / 16) * (A + (2 - A) / 16)
          = 2 - (13 * (2 - A)) / 16 - (15 * (2 - A) ^ 2) / 256 := by ring
      rw [hmain]
      have hsq : 0 ≤ (2 - A) ^ 2 := sq_nonneg (2 - A)
      have huA : 0 < 2 - A := by dsimp [u] at hu; linarith
      nlinarith
    have hNvalnn : 0 ≤ Nval := by
      dsimp [Nval]
      positivity
    refine ⟨e0, he0pos, he0le_ρt, ?_⟩
    -- ==========================================================
    -- fix ε with 0 < ε < e0 ; estimate the chord path
    -- ==========================================================
    intro ε hε hεlt
    have hεδG : ε < δG / (5 * (K + 1)) := lt_of_lt_of_le hεlt he0δG
    have hεrh : ε < rhθ / (5 * (K + 1)) := lt_of_lt_of_le hεlt he0rh
    have hερe : ε < ρe / (5 * (K + 1)) := lt_of_lt_of_le hεlt he0ρe
    have hε5 : (5 * (K + 1)) * ε < δG := by
      have hc : 0 < 5 * (K + 1) := by positivity
      have hm := mul_lt_mul_of_pos_right hεδG hc
      rw [div_mul_cancel₀] at hm
      · rw [mul_comm (5 * (K + 1)) ε]
        exact hm
      · exact ne_of_gt hc
    have hε5r : (5 * (K + 1)) * ε < rhθ := by
      have hc : 0 < 5 * (K + 1) := by positivity
      have hm := mul_lt_mul_of_pos_right hεrh hc
      rw [div_mul_cancel₀] at hm
      · rw [mul_comm (5 * (K + 1)) ε]
        exact hm
      · exact ne_of_gt hc
    have hε5e : (5 * (K + 1)) * ε < ρe := by
      have hc : 0 < 5 * (K + 1) := by positivity
      have hm := mul_lt_mul_of_pos_right hερe hc
      rw [div_mul_cancel₀] at hm
      · rw [mul_comm (5 * (K + 1)) ε]
        exact hm
      · exact ne_of_gt hc
    -- coordinate straight chord from εû to εŵ (small scale)
    let v : ℝ → E := fun t => ε • (û + t • d)
    let c : ℝ → E := fun t => expm (v t)
    let cder : ℝ → E := fun t => fderiv ℝ expm (v t) (ε • d)
    have hvnorm (t : ℝ) (ht : t ∈ Ioo (-1 : ℝ) 2) : ‖v t‖ < (5 * (K + 1)) * ε := by
      have h1 : ‖û + t • d‖ ≤ ‖û‖ + ‖t • d‖ := norm_add_le _ _
      have h2 : ‖û‖ ≤ K := hKunit û hûunit
      have ht_abs : |t| < 2 := by
        rw [abs_lt]
        constructor <;> linarith [ht.1, ht.2]
      have h3 : ‖t • d‖ ≤ |t| * ‖d‖ := by rw [norm_smul, Real.norm_eq_abs]
      have h4 : |t| * ‖d‖ ≤ 2 * ‖d‖ :=
        mul_le_mul_of_nonneg_right (le_of_lt ht_abs) (norm_nonneg d)
      have h5 : ‖û + t • d‖ ≤ K + 2 * ‖d‖ := by
        calc
          ‖û + t • d‖ ≤ ‖û‖ + ‖t • d‖ := h1
          _ ≤ ‖û‖ + |t| * ‖d‖ := add_le_add_right h3 ‖û‖
          _ ≤ K + 2 * ‖d‖ := by nlinarith
      have h7 : ‖û + t • d‖ ≤ 5 * K := by
        calc
          ‖û + t • d‖ ≤ K + 2 * ‖d‖ := h5
          _ ≤ 5 * K := by nlinarith [hdl]
      have h8 : ‖v t‖ ≤ ε * (5 * K) := by
        rw [show v t = ε • (û + t • d) by rfl, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (le_of_lt hε)]
        exact mul_le_mul_of_nonneg_left h7 (le_of_lt hε)
      calc
        ‖v t‖ ≤ ε * (5 * K) := h8
        _ < (5 * (K + 1)) * ε := by nlinarith [hε, hKnn]
    have hv_ρe (t : ℝ) (ht : t ∈ Ioo (-1 : ℝ) 2) : v t ∈ ball (0 : E) ρe := by
      rw [mem_ball, dist_eq_norm, sub_zero]
      exact lt_of_lt_of_le (hvnorm t ht) (by linarith [hε5e])
    have hv_δG (t : ℝ) (ht : t ∈ Ioo (-1 : ℝ) 2) : v t ∈ ball (0 : E) δG := by
      rw [mem_ball, dist_eq_norm, sub_zero]
      exact lt_of_lt_of_le (hvnorm t ht) (by linarith [hε5])
    have hv_rh (t : ℝ) (ht : t ∈ Ioo (-1 : ℝ) 2) : v t ∈ ball (0 : E) rhθ := by
      rw [mem_ball, dist_eq_norm, sub_zero]
      exact lt_of_lt_of_le (hvnorm t ht) (by linarith [hε5r])
    -- the manifold path σ
    let σ : ℝ → M := fun t => (extChartAt I p).symm (c t)
    have hvC : ContDiff ℝ 1 v := by
      have hvC' : ContDiff ℝ 1 (fun t : ℝ => ε • (û + t • d)) := by fun_prop
      simpa [v] using hvC'
    have hcO : ContDiffOn ℝ 1 c (Ioo (-1 : ℝ) 2) := by
      have hv1 : ContDiffOn ℝ 1 v (Ioo (-1 : ℝ) 2) := hvC.contDiffOn
      have hmaps : Set.MapsTo v (Ioo (-1 : ℝ) 2) (ball (0 : E) ρe) := by
        intro t ht
        exact hv_ρe t ht
      exact ContDiffOn.comp hExpC1 hv1 hmaps
    have hOIcc : Icc (0 : ℝ) 1 ⊆ Ioo (-1 : ℝ) 2 := by
      intro t ht
      constructor <;> linarith [ht.1, ht.2]
    have hcC1I : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 c (Icc (0 : ℝ) 1) := by
      exact ((contMDiffOn_iff_contDiffOn).mpr hcO).mono hOIcc
    have hExp_ρT (w : E) (hw : w ∈ ball (0 : E) ρe) : expm w ∈ ball x₀ ρT := by
      rcases hcv w hw with ⟨cv, velv, hcv0, hcv1, hcvd, hcvsp, hcvstay, hcvform, hcvO⟩
      have hmem : cv 1 ∈ ball x₀ ρT := hcvstay 1 (by norm_num)
      rwa [hcv1] at hmem
    have hsubI : Set.MapsTo c (Icc (0 : ℝ) 1) (extChartAt I p).target := by
      intro t ht
      exact hρTtgt (hExp_ρT (v t) (hv_ρe t (hOIcc ht)))
    have hσC : ContMDiffOn 𝓘(ℝ, ℝ) I 1 σ (Icc (0 : ℝ) 1) := by
      have hmainC := ContMDiffOn.comp (contMDiffOn_extChartAt_symm (I := I) p) hcC1I hsubI
      have hσeq : Set.EqOn σ ((extChartAt I p).symm ∘ c) (Icc (0 : ℝ) 1) := by
        intro t ht
        rfl
      exact hmainC.congr hσeq
    -- endpoints
    have hv0 : v 0 = ε • û := by
      dsimp [v]
      simp
    have hv1 : v 1 = ε • ŵ := by
      dsimp [v, d]
      simp [add_sub_cancel]
    have hmem0 : ε • û ∈ ball (0 : E) ρe := by
      rw [← hv0]
      exact hv_ρe 0 (by constructor <;> norm_num)
    have hmem1 : ε • ŵ ∈ ball (0 : E) ρe := by
      rw [← hv1]
      exact hv_ρe 1 (by constructor <;> norm_num)
    have hσ0 : σ 0 = ExpM (ε • û) := by
      simpa [σ, c, hv0] using (hExpExpM (ε • û) hmem0).symm
    have hσ1 : σ 1 = ExpM (ε • ŵ) := by
      simpa [σ, c, hv1] using (hExpExpM (ε • ŵ) hmem1).symm
    -- derivative of the coordinate curve on [0,1]
    have hExpDiff (w : E) (hw : w ∈ ball (0 : E) ρe) : DifferentiableAt ℝ expm w := by
      exact (hExpC1.contDiffAt (isOpen_ball.mem_nhds hw)).differentiableAt
        (by norm_num : (1 : ℕ∞ω) ≠ 0)
    have hcd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt c (cder t) t := by
      intro t ht
      have hmem : v t ∈ ball (0 : E) ρe := hv_ρe t (hOIcc ht)
      have hvd : HasDerivAt v (ε • d) t := by
        have h1 : HasDerivAt (fun u : ℝ => û + u • d) d t := by
          have hsm : HasDerivAt (fun u : ℝ => u • d) d t := by
            simpa using ((hasDerivAt_id (𝕜 := ℝ) t).smul_const d)
          exact hsm.const_add û
        have hc' : HasDerivAt (fun u : ℝ => ε • (û + u • d)) (ε • d) t := h1.const_smul ε
        simpa [v] using hc'
      have hfd : HasFDerivAt expm (fderiv ℝ expm (v t)) (v t) :=
        (hExpDiff (v t) hmem).hasFDerivAt
      have hc' : HasDerivAt (fun u : ℝ => expm (v u)) (fderiv ℝ expm (v t) (ε • d)) t :=
        HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (F := E) (E := E) t hfd hvd
      simpa [c, cder, Function.comp_def] using hc'
    -- pointwise speed bound
    have hγeq : ∀ s : ℝ, σ s = (extChartAt I p).symm (c s) := by intro s; rfl
    have hsp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
        ‖mfderiv% σ t 1‖ₑ ≤ ENNReal.ofReal (ε * Nval) := by
      have hmemT : c t ∈ ball x₀ ρT := hExp_ρT (v t) (hv_ρe t (hOIcc ht))
      have hspd := chart_speed_core (I := I) (M := M) p
        (ρ := ρT) (ge := ge)
        (by intro y hy u v; exact hgeAgree y (ball_subset_ball hρTle hy) u v)
        (by simpa [x₀] using hρTtgt)
        (hγeq := hγeq) (hcball := hmemT) (hu := hcd t ht)
      have hcball_g : c t ∈ ball x₀ rhoG := by
        rw [mem_ball, dist_eq_norm]
        have hdG : ‖expm (v t) - x₀‖ < rhoG := hδG (v t) (hv_δG t (hOIcc ht))
        simpa [c] using hdG
      have hfderb : ‖fderiv ℝ expm (v t) - ContinuousLinearMap.id ℝ E‖ ≤ theta :=
        hrhθ (v t) (hv_rh t (hOIcc ht))
      have hsqA : Real.sqrt (Q (ε • d) (ε • d)) = ε * A := by
        rw [sqrt_quad_smul_nonneg (B := Q) (le_of_lt hε) d (hQdnn)]
      have herr : ‖fderiv ℝ expm (v t) (ε • d) - ε • d‖ ≤ 2 * K * theta * ε := by
        have hsub : fderiv ℝ expm (v t) (ε • d) - ε • d
            = (fderiv ℝ expm (v t) - ContinuousLinearMap.id ℝ E) (ε • d) := by
          rw [sub_apply, id_apply]
        rw [hsub]
        have h1 := (fderiv ℝ expm (v t) - ContinuousLinearMap.id ℝ E).le_opNorm (ε • d)
        have h2 : ‖ε • d‖ = ε * ‖d‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
        calc
          ‖(fderiv ℝ expm (v t) - ContinuousLinearMap.id ℝ E) (ε • d)‖
              ≤ ‖fderiv ℝ expm (v t) - ContinuousLinearMap.id ℝ E‖ * ‖ε • d‖ := h1
          _ ≤ theta * (ε * ‖d‖) := by
            rw [h2]
            exact mul_le_mul_of_nonneg_right hfderb (mul_nonneg (le_of_lt hε) (norm_nonneg d))
          _ ≤ theta * (ε * (2 * K)) := by
            have h : ε * ‖d‖ ≤ ε * (2 * K) := mul_le_mul_of_nonneg_left hdl (le_of_lt hε)
            exact mul_le_mul_of_nonneg_left h (by dsimp [theta]; positivity)
          _ = 2 * K * theta * ε := by ring
      have hQerr : Real.sqrt (Q (fderiv ℝ expm (v t) (ε • d) - ε • d)
          (fderiv ℝ expm (v t) (ε • d) - ε • d)) ≤ (2 * K * B0 * theta) * ε := by
        have hq : Real.sqrt (Q (fderiv ℝ expm (v t) (ε • d) - ε • d)
            (fderiv ℝ expm (v t) (ε • d) - ε • d)) ≤ B0 * ‖fderiv ℝ expm (v t) (ε • d) - ε • d‖ := by
          simpa using hB0norm (fderiv ℝ expm (v t) (ε • d) - ε • d)
        calc
          Real.sqrt (Q (fderiv ℝ expm (v t) (ε • d) - ε • d)
              (fderiv ℝ expm (v t) (ε • d) - ε • d)) ≤ B0 * ‖fderiv ℝ expm (v t) (ε • d) - ε • d‖ := hq
          _ ≤ B0 * (2 * K * theta * ε) := mul_le_mul_of_nonneg_left herr hB0nn
          _ = (2 * K * B0 * theta) * ε := by ring
      have hmet : Real.sqrt (ge (c t) (cder t) (cder t)) ≤ (1 + lamG) * Real.sqrt (Q (cder t) (cder t)) := by
        exact hrhoG (c t) hcball_g (cder t)
      have htri : Real.sqrt (Q (cder t) (cder t)) ≤
          Real.sqrt (Q (ε • d) (ε • d)) + Real.sqrt (Q (cder t - ε • d) (cder t - ε • d)) := by
        have hx := quad_sqrt_add_le (B := Q) (hsym := hgeSymm x₀) (hpos := hgePos x₀)
          (ε • d) (cder t - ε • d)
        have harg : ε • d + (cder t - ε • d) = cder t := by abel
        simpa [harg] using hx
      have htotal : Real.sqrt (Q (cder t) (cder t)) ≤ ε * A + (2 * K * B0 * theta) * ε := by
        calc
          Real.sqrt (Q (cder t) (cder t)) ≤
              Real.sqrt (Q (ε • d) (ε • d)) + Real.sqrt (Q (cder t - ε • d) (cder t - ε • d)) := htri
          _ ≤ ε * A + (2 * K * B0 * theta) * ε := by linarith [hsqA, hQerr]
      have hlin : ε * A + (2 * K * B0 * theta) * ε ≤ ε * (A + u / 16) := by
        nlinarith [mul_le_mul_of_nonneg_left hErr (le_of_lt hε)]
      have hroot : (1 + lamG) * Real.sqrt (Q (cder t) (cder t)) ≤ (1 + lamG) * (ε * (A + u / 16)) := by
        exact mul_le_mul_of_nonneg_left (le_trans htotal hlin) (by dsimp [lamG]; positivity)
      have hspeedreal : Real.sqrt (ge (c t) (cder t) (cder t)) ≤ ε * Nval := by
        dsimp [Nval]
        calc
          Real.sqrt (ge (c t) (cder t) (cder t)) ≤ (1 + lamG) * Real.sqrt (Q (cder t) (cder t)) := hmet
          _ ≤ (1 + lamG) * (ε * (A + u / 16)) := hroot
          _ = ε * ((1 + lamG) * (A + u / 16)) := by ring
      have hspd' : ‖mfderiv% σ t 1‖ₑ = ENNReal.ofReal (Real.sqrt (ge (c t) (cder t) (cder t))) := by
        simpa [cder] using hspd
      calc
        ‖mfderiv% σ t 1‖ₑ = ENNReal.ofReal (Real.sqrt (ge (c t) (cder t) (cder t))) := hspd'
        _ ≤ ENNReal.ofReal (ε * Nval) := ENNReal.ofReal_le_ofReal hspeedreal
    -- bound the path length
    have hpath : Manifold.pathELength I σ 0 1 ≤ ENNReal.ofReal (ε * Nval) := by
      rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
      calc
        (∫⁻ t in Icc (0 : ℝ) 1, ‖mfderiv% σ t 1‖ₑ)
            ≤ ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal (ε * Nval) := by
              exact MeasureTheory.setLIntegral_mono' measurableSet_Icc (fun t ht => hsp t ht)
        _ = ENNReal.ofReal (ε * Nval) * volume (Icc (0 : ℝ) 1) := by
            rw [MeasureTheory.setLIntegral_const]
        _ = ENNReal.ofReal (ε * Nval) * ENNReal.ofReal (1 - 0) := by
            congr 1
            exact Real.volume_Icc
        _ ≤ ENNReal.ofReal ((ε * Nval) * (1 - 0)) := by
            have hn0 : 0 ≤ ε * Nval := by positivity
            rw [ENNReal.ofReal_mul hn0]
        _ = ENNReal.ofReal (ε * Nval) := by ring
    -- edist ≤ pathELength ≤ ofReal(ε Nval) < ofReal(2ε)
    have hdst : edist (ExpM (ε • û)) (ExpM (ε • ŵ)) ≤ Manifold.pathELength I σ 0 1 := by
      have hR : Manifold.riemannianEDist I (ExpM (ε • û)) (ExpM (ε • ŵ)) ≤ Manifold.pathELength I σ 0 1 := by
        exact Manifold.riemannianEDist_le_pathELength (I := I) hσC hσ0 hσ1 (by norm_num)
      calc
        edist (ExpM (ε • û)) (ExpM (ε • ŵ))
            = Manifold.riemannianEDist I (ExpM (ε • û)) (ExpM (ε • ŵ)) :=
              IsRiemannianManifold.out (I := I) (ExpM (ε • û)) (ExpM (ε • ŵ))
        _ ≤ Manifold.pathELength I σ 0 1 := hR
    have hltN : ENNReal.ofReal (ε * Nval) < ENNReal.ofReal (2 * ε) := by
      have h1 : ε * Nval < 2 * ε := by
        have hN : Nval < 2 := hNval2
        nlinarith [mul_lt_mul_of_pos_left hN hε]
      exact (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < 2 * ε)).2 h1
    exact lt_of_le_of_lt (le_trans hdst hpath) hltN

end Submission