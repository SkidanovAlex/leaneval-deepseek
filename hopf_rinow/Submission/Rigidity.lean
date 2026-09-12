import ChallengeDeps
import Submission.Metric
import Submission.ChartArc
import Submission.TinyStrict
import Submission.ChartNormal
import Submission.ModelNormalBall
import Mathlib

/-!
# Interior rigidity: locally linear curves are radial exponential arcs (rigid statement)

Theorem: `Submission.arc_rigidity`.

## Statement

At every point `p : M` (challenge hypotheses) build the normal-coordinate data (as in
`Submission.chart_arc_linear`: `ρ₀`, `ge`, `r`, `ExpM`, `S`, `invM`, radial identity
`edist p (ExpM v) = ‖v‖`, and the two-sided arc identity for metric-unit `W`: small `s ≤ t`
⇒ `edist (ExpM (s•W)) (ExpM (t•W)) = t - s`).  ADDITIONALLY prove **interior rigidity**:
any curve `γ` that passes through `p` at time `0` and is locally linear of speed `c` on a
two-sided window around `0` (i.e. pairs within `δ` of `0` are distance-exact with constant `c`)
is, on a full neighbourhood of `0`, the radial exponential arc `t ↦ ExpM (t • v)` for a fixed
vector `v` with metric norm `c`:

    theorem arc_rigidity {E : Type*} ... (M : Type*) ... [IsRiemannianManifold I M] (p : M) :
        ∃ ρ₀ > 0, ∃ ge : E → E →L[ℝ] E →L[ℝ] ℝ, [ContDiff 3, symmetric, positive definite,
           fibre agreement on ball (extChartAt I p p) ρ₀]
          ∧ ∃ r > 0, ∃ ExpM : E → M, ∃ S : Set M, ∃ invM : M → E,
            [homeo structure on ball 0 r: ExpM 0 = p, S ∈ 𝓝 p, injective/continuous/surj, invM,
             radial identity ∀ v ∈ ball 0 r, edist p (ExpM v) = ofReal ‖v‖,
             two-sided arc identity: ∃ ρa ≤ r, ∀ W with ‖W‖ = 1, ∀ s ≤ t with |s|,|t| < ρa:
               edist (ExpM (s•W)) (ExpM (t•W)) = ofReal (t - s)]
            ∧ ∀ (c : NNReal) (hc : 0 < c) (γ : ℝ → M) (δ : ℝ),
                γ 0 = p → 0 < δ → (c : ℝ) * δ ≤ ρa →
                (∀ s t : ℝ, |s| < δ → |t| < δ →
                   edist (γ s) (γ t) = (c : ℝ≥0∞) * ENNReal.ofReal |t - s|) →
                ∃ v : E, Real.sqrt ((ge (extChartAt I p p)) v v) = c ∧
                  ∀ t : ℝ, |t| < δ → γ t = ExpM (t • v)

`‖v‖ := Real.sqrt ((ge (extChartAt I p p)) v v)`.

## Why this is the key missing theorem

A locally linear curve (metric definition of geodesic) must be shown to be a genuine
exponential arc at interior points.  This is used for: uniqueness of locally linear extensions
(ULU), the rigidity of tails at limit points, and hence `local_extension`, the interfaces
`GeoRightExt`/`GeoLeftExt`, and the Hopf–Rinow compactness lemma.

## Proof route (scaling / antipodal argument)

Fix `γ` through `p = γ 0`, exact of speed `c` on `(-δ, δ)` (two-sided window).  Let
`x(t) := invM (γ t)` for `t` near `0` (values in `ball 0 r`), so `γ t = ExpM (x t)` and, by the
radial identity at `p`, `‖x t‖ = edist p (γ t) = c |t|` for `|t| < δ`.  (The second equality is
exactness at the centre `0`.)

**Step 1 (upper asymptotics of ExpM, prove as a helper).**  For all `u, w ∈ ball 0 r`:
`edist (ExpM u) (ExpM w) ≤ ‖u - w‖ * (1 + o(1))` as `‖u‖,‖w‖ → 0` — precisely: there is
`R₁ ≤ r` and a function `φ : ℝ → ℝ` with `φ(ρ) → 0` (as `ρ → 0⁺`) such that for all
`u,w ∈ ball 0 R₁`: `edist (ExpM u) (ExpM w) ≤ ‖u-w‖ * (1 + φ(max ‖u‖ ‖w‖))`.
PROOF: the coordinate straight segment `ζ(τ) := exp_m((1-τ)u + τ w)` (model exponential of
`ge` at `x₀`), pushed to `M` by the chart, is a path from `ExpM u` to `ExpM w`; its manifold
length is at most its `ge`-length (chart speed identity, reuse the `chart_normal`/MChartGeodesicUB
machinery) which is `∫₀¹ √(ge (ζ τ) (ζ' τ) (ζ' τ)) dτ = ‖u-w‖·(1 + O(ρ))` because
`exp_m` is C¹ with derivative `id` at `0` and `ge` is continuous (`‖exp_m z - (x₀+z)‖ ≤ C‖z‖²`
and `dexp` close to identity — all verified in `Submission.ModelExp`/`ModelExpC1`).  Hence
`edist (ExpM u) (ExpM w) ≤` length `≤ ‖u-w‖(1+o(1))`.

**Step 2 (antipodal rigidity of close pairs).**  Fix `s < 0 < t` with `|s|,|t| < δ'` small
(≤ R₁).  Exactness gives `edist (ExpM (x s)) (ExpM (x t)) = c (t - s)`.  By Step 1 applied to
`u := x s`, `w := x t`:
`c (t-s) ≤ ‖x s - x t‖ (1 + o(1))`.
On the other hand `‖x s - x t‖ ≤ ‖x s‖ + ‖x t‖ = c (t₀ - s) + c(t - t₀) = c(t-s)` (here
`t₀ = 0`, `‖x s‖ = c|s|`, `‖x t‖ = c t`).  Combining:
`‖x s - x t‖ ≥ c(t-s)(1 - o(1)) = (‖x s‖ + ‖x t‖)(1 - o(1))`.
Conclude that `x s` and `x t` are almost opposite: for the unit vectors `u(s) := x s/‖x s‖`,
`u(t) := x t/‖x t‖`, `‖u(s) + u(t)‖ → 0` as `|s|,|t| → 0` (equality case of the triangle
inequality for norms).  Prove this quantitatively: for any vectors `a,b` with
`‖a‖,‖b‖ ≤ C ρ` and `‖a‖ + ‖b‖ - ‖a-b‖ ≤ ε ρ`, we have `‖a/‖a‖ + b/‖b‖‖ ≤ C'√ε`.

**Step 3 (directions have one-sided limits).**  For `s → 0⁻`, the unit vectors `u(s)`
(eventually defined, `x s ≠ 0` for `s ≠ 0`) form a Cauchy family: for `s₁ < s₂ < 0` small,
apply Step 2 to the pairs and use `‖x s‖ = c|s|` to estimate `‖u(s₁) - u(s₂)‖` (express
`x s₂ = (s₂/s₁) • x s₁`? — NO, not known yet; instead: use Step 2 on the pair `(s₁, t)` and
`(s₂, t)` for a fixed `t > 0`, giving `u(s₁) ≈ -u(t) ≈ u(s₂)`, hence `u(s₁) ≈ u(s₂)` with a
quantitative bound → `u(s)` is Cauchy as `s → 0⁻`, so it has a limit `u₋`; similarly
`u(t) → u₊` as `t → 0⁺`, and Step 2 gives `u₊ = -u₋`.)

**Step 4 (the curve is the radial arc).**  For every `t` with `|t| < ρR` (say `t > 0`):
`x(t) = t • (c u₊)`.  Indeed for each small `s < 0`, Step 2's almost-antipodality gives
`u(t) ≈ -u(s) ≈ u₊`; to get EXACT collinearity rather than approximation, use the
**two-sided arc identity at `p`** together with the following equality-case argument:
for `s < 0 < t` in the window, exactness gives
`edist (ExpM (x s)) (ExpM (x t)) = c(t-s) = ‖x s‖ + ‖x t‖`.
By the triangle inequality through `p`, `edist (ExpM (x s)) (ExpM (x t)) ≤ ‖x s‖ + ‖x t‖`
always, and the total is `c(t-s)`, so this is an EQUALITY: `p` lies "between" the two points
additively.  Now use the following exact rigidity statement (prove as a helper from the
two-sided arc identity + injectivity of `ExpM`): for `a,b ∈ ball 0 r` with `a,b ≠ 0`,
`edist (ExpM a) (ExpM b) = ‖a‖ + ‖b‖` iff `a,b,0` are collinear with `0` between `a` and `b`
(i.e. `b = -λ a` for `λ > 0`).  [Proof of the helper: if `a,b,0` are collinear with 0 between,
the two-sided identity along the ray `a/‖a‖` (unit) with `s = -‖a‖`, `t = ‖b‖` gives the
value `‖a‖+‖b‖`.  Conversely suppose `edist (ExpM a) (ExpM b) = ‖a‖+‖b‖`.  Let
`a' := -‖a‖ • (b/‖b‖)` (the antipodal point of `b` on `b`'s ray at radius `‖a‖`); the two-sided
identity gives `edist (ExpM a') (ExpM b) = ‖a‖+‖b‖`, so `ExpM a` and `ExpM a'` are both at
distance `‖a‖+‖b‖` from `ExpM b`.  Show these two points coincide: take a C¹ path of length
`≤ ‖a‖+‖b‖` from `ExpM b` to `ExpM a` (exists by the definition of edist as an infimum over
C¹ paths — get an almost-minimizing path, length `< ‖a‖+‖b‖+ε`); ... — settle the details:
the cleanest route is to use the model staying-minimality at the base `p` (from
`model_normal_ball`, transferred by `chart_normal`) applied to the radial function `F` along
the path, together with the fact that equality in the radial bound holds only in the radial
direction (`bilin_cs_eq_colinear`, in `Submission.LocalExt`).  In any case the conclusion is:
`a = a'`, i.e. `a,b,0` collinear with 0 between.]
Applying this to `a := x s`, `b := x t` for all small `s < 0 < t`: `x t` is a positive multiple
of `x s`; varying `t` and `s` shows all `x(t)` (`t ≠ 0`) lie on one line through `0`, with the
direction independent of the side (Step 3), i.e. `x t = t • (c u₊)` for `t > 0` and
`x t = t • (c u₋)` for `t < 0`, with `u₋ = -u₊`; but since `γ` is continuous and
`ExpM` is injective, the two sides meet consistently at `t = 0`: define `v := c u₊`, so
`x t = t • v` for all `t` with `|t| < ρR`, i.e. `γ t = ExpM (t • v)`, and `‖v‖ = c`.  Done.

## Notes
- The exact rigidity helper in Step 4 ("equality `edist = ‖a‖+‖b‖` forces collinearity") is the
  heart of the proof; the two-sided identity gives the "if" direction, and the "only if" needs
  the equality-case analysis of the radial bound (model staying-minimality from `p` + strict
  Cauchy-Schwarz) transferred to the manifold.  You may also prove it by an explicit corner-
  cutting argument using the two-sided identity at intermediate points.  Take whatever route is
  cleanest; you may add many helper lemmas.
- Reuse `Submission.chart_arc_linear` by destructuring it (it already returns all the data and
  the two-sided identity); you then only add the rigidity conjunct — but note the statement
  above returns data with BOTH the two-sided identity AND the rigidity clause, so destructure
  `chart_arc_linear` and re-export, then prove the rigidity part.
- `ModelExpC1`, `ModelNormalBall`, `ExpCore`, `LocalExt` provide the analytic/model pieces.
- `Real.sqrt` metric norm, ENNReal conversions, `edist` arithmetic: follow the earlier modules.

Do NOT change the statement of `arc_rigidity`; no placeholders may remain in the file.
-/

open scoped Manifold ENNReal ContDiff Topology
open scoped Manifold ENNReal ContDiff Topology
open Set Metric
open Bundle
open MeasureTheory

namespace Submission

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 4000000


theorem arc_rigidity {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
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
          (∀ (W : E), Real.sqrt ((ge (extChartAt I p p)) W W) = 1 →
            ∀ ⦃s t : ℝ⦄, s ≤ t → |s| < ρa → |t| < ρa →
              edist (ExpM (s • W)) (ExpM (t • W)) = ENNReal.ofReal (t - s)) ∧
          ∀ (c : NNReal) (hc : 0 < c) (γ : ℝ → M) (δ : ℝ),
            γ 0 = p → 0 < δ → (c : ℝ) * δ ≤ ρa →
            (∀ s t : ℝ, |s| < δ → |t| < δ →
               edist (γ s) (γ t) = (c : ℝ≥0∞) * ENNReal.ofReal |t - s|) →
            ∃ v : E, Real.sqrt ((ge (extChartAt I p p)) v v) = c ∧
              ∀ t : ℝ, |t| < δ → γ t = ExpM (t • v) := by
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

  refine ⟨ρ0, hρ00, ge, hgeC, hgeSymm, hgePos, hgeAgree, ⟨r, hr0, ExpM, S, invM,
    hExpM0, hSnhds, hS_in, hExpCont, hInj, hSurj, hInvS, hInvExp, hRadial,
    ⟨ρa, hρa0, hρale_r, hArcM, ?rigid⟩⟩⟩
  -- ============================================================
  -- RIGIDITY part
  -- ============================================================
  intro c hc γ δ hγ0 hδ0 hcδ hexact
  -- real speed and basic positivity
  let cR : ℝ := (c : ℝ)
  have hcR0 : 0 < cR := by exact_mod_cast hc
  have hcR_nonneg : 0 ≤ cR := le_of_lt hcR0
  -- distance from p is exact on the window
  have hEdist0 : ∀ t : ℝ, |t| < δ → edist p (γ t) = ENNReal.ofReal (cR * |t|) := by
    intro t ht
    have hd := hexact 0 t (by simpa using hδ0) ht
    have h1 : edist (γ 0) (γ t) = (c : ℝ≥0∞) * ENNReal.ofReal |t| := by
      simpa [hγ0] using hd
    have h2 : (c : ℝ≥0∞) = ENNReal.ofReal (c : ℝ) := (ENNReal.ofReal_coe_nnreal).symm
    calc
      edist p (γ t) = (c : ℝ≥0∞) * ENNReal.ofReal |t| := by simpa [hγ0] using h1
      _ = ENNReal.ofReal (cR * |t|) := by
        rw [h2]
        rw [ENNReal.ofReal_mul hcR_nonneg]
  -- curve stays in the metric ball of radius cδ ≤ ρa ≤ cp/8, hence inside S
  have hγS : ∀ t : ℝ, |t| < δ → γ t ∈ S := by
    intro t ht
    have hlt : ENNReal.ofReal (cR * |t|) < ENNReal.ofReal cp := by
      have h2 : cR * |t| < cR * δ := mul_lt_mul_of_pos_left ht hcR0
      have h4 : cR * |t| < ρa := lt_of_lt_of_le h2 hcδ
      have h6 : cR * |t| < cp / 8 := lt_of_lt_of_le h4 hρa_c8
      have h7 : cR * |t| < cp := lt_trans h6 (by linarith [hcp0])
      exact (ENNReal.ofReal_lt_ofReal_iff hcp0).mpr h7
    have hlt' : edist p (γ t) < ENNReal.ofReal cp := by
      rw [hEdist0 t ht]
      exact hlt
    exact hcp_sub hlt'
  -- coordinate x(t) := invM (γ t)
  let x : ℝ → E := fun t => invM (γ t)
  have hxball : ∀ t : ℝ, |t| < δ → x t ∈ ball (0 : E) r := by
    intro t ht
    exact (hInvS (γ t) (hγS t ht)).1
  have hxExp : ∀ t : ℝ, |t| < δ → ExpM (x t) = γ t := by
    intro t ht
    exact (hInvS (γ t) (hγS t ht)).2
  have hxnorm : ∀ t : ℝ, |t| < δ → Real.sqrt ((ge x₀) (x t) (x t)) = cR * |t| := by
    intro t ht
    have hrad := hRadial (x t) (hxball t ht)
    have h1 : edist p (ExpM (x t)) = ENNReal.ofReal (Real.sqrt ((ge x₀) (x t) (x t))) := by
      simpa [x₀] using hrad
    have h2 : edist p (γ t) = ENNReal.ofReal (Real.sqrt ((ge x₀) (x t) (x t))) := by
      rw [← hxExp t ht]
      exact h1
    have h3 : ENNReal.ofReal (Real.sqrt ((ge x₀) (x t) (x t))) = ENNReal.ofReal (cR * |t|) := by
      rw [← h2]
      exact hEdist0 t ht
    exact (ENNReal.ofReal_eq_ofReal_iff (Real.sqrt_nonneg _) (mul_nonneg hcR_nonneg (abs_nonneg t))).1 h3
  -- x(0) = 0
  have hx0 : x 0 = 0 := by
    have h00 : (0 : E) ∈ ball (0 : E) r := by simpa using hr0
    calc
      x 0 = invM (γ 0) := rfl
      _ = invM p := by rw [hγ0]
      _ = invM (ExpM 0) := by rw [hExpM0]
      _ = 0 := hInvExp 0 h00
  -- ============================================================
  -- tiny-scale strictness: for non-opposite unit directions û, ŵ the tiny radial points
  -- ExpM(εû), ExpM(εŵ) are at distance STRICTLY below 2ε (analytic lemma, proved below)
  -- ============================================================
  have hTiny : ∀ ⦃û ŵ : E⦄, Real.sqrt ((ge x₀) û û) = 1 →
      Real.sqrt ((ge x₀) ŵ ŵ) = 1 → ŵ ≠ -û →
      ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
        edist (ExpM (ε • û)) (ExpM (ε • ŵ)) < ENNReal.ofReal (2 * ε) := by
    let Q : E →L[ℝ] E →L[ℝ] ℝ := ge x₀
    have hQnonneg : ∀ v : E, 0 ≤ (Q v) v := by
      intro v
      by_cases hv : v = 0
      · subst v; simp
      · exact le_of_lt (hgePos x₀ v hv)
    have hExpId : HasFDerivAt expm (ContinuousLinearMap.id ℝ E) 0 := by
      exact expm_fderiv_zero_id ge hgeC hinv x₀ hρe0 hτe0 hρeτe4 Φ expm hΦODE hexpform hExpC1
    have hfderiv0 : fderiv ℝ expm 0 = ContinuousLinearMap.id ℝ E := hExpId.fderiv
    have hfdCont : ContinuousOn (fun v : E => fderiv ℝ expm v) (ball (0 : E) ρe) := by
      exact Model.contDiffOn_one_cont_fderiv (isOpen_ball : IsOpen (ball (0 : E) ρe)) hExpC1
    have hfdAt0 : ContinuousAt (fun v : E => fderiv ℝ expm v) (0 : E) := by
      have h0mem : (0 : E) ∈ ball (0 : E) ρe := by simpa using hρe0
      exact hfdCont.continuousAt (by simpa [ball, dist_eq_norm] using (isOpen_ball.mem_nhds h0mem))
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
    have hKunit : ∀ V : E, Real.sqrt (Q V V) = 1 → ‖V‖ ≤ K := by
      intro V hV
      exact hKbound V (by simpa [Q] using hV)
    let ρt : ℝ := min r (ρe / (8 * (K + 1)))
    have hρt0 : 0 < ρt := by
      dsimp [ρt]
      exact lt_min hr0 (div_pos hρe0 (by positivity))

    intro û ŵ hûunit hŵunit hnotopp
    by_cases huw : ŵ = û
    · -- identical radial directions: distance 0 < 2ε
      subst ŵ
      refine ⟨ρt, hρt0, ?_⟩
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
      refine ⟨e0, he0pos, ?_⟩
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
            rw [sub_apply, ContinuousLinearMap.id_apply]
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

  -- ============================================================
  -- pairwise antipodality: for s < 0 < t, x(s) is on the negative ray of x(t)
  -- ============================================================
  have hPair : ∀ ⦃s t : ℝ⦄, |s| < δ → |t| < δ → s < 0 → 0 < t →
      ∃ la : ℝ, 0 < la ∧ x s = -la • x t := by
    intro s t hs ht hs0 ht0
    let a : E := x s
    let b : E := x t
    let A : ℝ := Real.sqrt ((ge x₀) a a)
    let B : ℝ := Real.sqrt ((ge x₀) b b)
    have ha_mem : a ∈ ball (0 : E) r := by simpa [a] using hxball s hs
    have hb_mem : b ∈ ball (0 : E) r := by simpa [b] using hxball t ht
    have hAs : A = cR * |s| := by simpa [A, a] using hxnorm s hs
    have hBt : B = cR * |t| := by simpa [B, b] using hxnorm t ht
    have hAs_pos : 0 < A := by
      rw [hAs]
      exact mul_pos hcR0 (abs_pos.mpr (ne_of_lt hs0))
    have hBt_pos : 0 < B := by
      rw [hBt]
      exact mul_pos hcR0 (abs_pos.mpr (ne_of_gt ht0))
    have hA_lt_ρa : A < ρa := by
      rw [hAs]
      have h1 : |s| < δ := hs
      have h2 : cR * |s| < cR * δ := mul_lt_mul_of_pos_left h1 hcR0
      exact lt_of_lt_of_le h2 hcδ
    have hB_lt_ρa : B < ρa := by
      rw [hBt]
      have h2 : cR * |t| < cR * δ := mul_lt_mul_of_pos_left ht hcR0
      exact lt_of_lt_of_le h2 hcδ
    let û : E := (1 / A) • a
    let ŵ : E := (1 / B) • b
    have hûunit : Real.sqrt ((ge x₀) û û) = 1 := by
      have hsc : 0 ≤ 1 / A := by positivity
      have hs := sqrt_quad_smul_nonneg (ge x₀) hsc a (hBnonneg a)
      calc
        Real.sqrt ((ge x₀) û û) = Real.sqrt ((ge x₀) ((1 / A) • a) ((1 / A) • a)) := by rfl
        _ = (1 / A) * Real.sqrt ((ge x₀) a a) := hs
        _ = 1 := by
          have hA : Real.sqrt ((ge x₀) a a) = A := rfl
          rw [hA]
          field_simp [ne_of_gt hAs_pos]
    have hŵunit : Real.sqrt ((ge x₀) ŵ ŵ) = 1 := by
      have hsc : 0 ≤ 1 / B := by positivity
      have hs := sqrt_quad_smul_nonneg (ge x₀) hsc b (hBnonneg b)
      calc
        Real.sqrt ((ge x₀) ŵ ŵ) = Real.sqrt ((ge x₀) ((1 / B) • b) ((1 / B) • b)) := by rfl
        _ = (1 / B) * Real.sqrt ((ge x₀) b b) := hs
        _ = 1 := by
          have hB : Real.sqrt ((ge x₀) b b) = B := rfl
          rw [hB]
          field_simp [ne_of_gt hBt_pos]
    -- distances among the involved points
    have hd_ab : edist (ExpM a) (ExpM b) = ENNReal.ofReal (A + B) := by
      have hd := hexact s t hs ht
      have hst : t - s = |t - s| := by
        rw [abs_of_pos (sub_pos.mpr (lt_trans hs0 ht0))]
      have hc' : (c : ℝ≥0∞) = ENNReal.ofReal (cR) := by
        dsimp [cR]
        exact (ENNReal.ofReal_coe_nnreal).symm
      have hsum : cR * (t - s) = A + B := by
        rw [hAs, hBt]
        have h1 : |s| = -s := abs_of_neg hs0
        have h2 : |t| = t := abs_of_pos ht0
        rw [h1, h2]
        ring
      have hd' : edist (ExpM a) (ExpM b) = (c : ℝ≥0∞) * ENNReal.ofReal (t - s) := by
        have hg : edist (ExpM (x s)) (ExpM (x t)) = edist (γ s) (γ t) := by
          rw [hxExp s hs, hxExp t ht]
        rw [hg]
        have habs : |t - s| = t - s := abs_of_pos (sub_pos.mpr (lt_trans hs0 ht0))
        rw [habs] at hd
        exact hd
      calc
        edist (ExpM a) (ExpM b) = (c : ℝ≥0∞) * ENNReal.ofReal (t - s) := hd'
        _ = ENNReal.ofReal (cR * (t - s)) := by
          rw [hc']
          rw [← ENNReal.ofReal_mul hcR_nonneg]
        _ = ENNReal.ofReal (A + B) := by rw [hsum]
    -- exactness through p
    have hd_a_p : edist p (ExpM a) = ENNReal.ofReal A := by
      have hd := hRadial a ha_mem
      calc
        edist p (ExpM a) = ENNReal.ofReal (Real.sqrt ((ge x₀) a a)) := by simpa [x₀] using hd
        _ = ENNReal.ofReal A := rfl
    have hd_b_p : edist p (ExpM b) = ENNReal.ofReal B := by
      have hd := hRadial b hb_mem
      calc
        edist p (ExpM b) = ENNReal.ofReal (Real.sqrt ((ge x₀) b b)) := by simpa [x₀] using hd
        _ = ENNReal.ofReal B := rfl
    -- radical: a = A•û etc.
    have hAû : A • û = a := by
      dsimp [û]
      rw [smul_smul]
      have h : (A * (1 / A)) • a = a := by
        rw [mul_one_div_cancel (ne_of_gt hAs_pos)]
        simp
      exact h
    have hBŵ : B • ŵ = b := by
      dsimp [ŵ]
      rw [smul_smul]
      have h : (B * (1 / B)) • b = b := by
        rw [mul_one_div_cancel (ne_of_gt hBt_pos)]
        simp
      exact h
    -- main contradiction when directions are not opposite
    by_contra hnot
    have hneq : ŵ ≠ -û := by
      intro hw
      have huw : û = -ŵ := by
        rw [hw]
        simp
      have heq : a = -(A / B) • b := by
        have h1 : a = A • û := hAû.symm
        calc
          a = A • û := h1
          _ = A • (-ŵ) := by rw [huw]
          _ = -(A / B) • b := by
            dsimp [ŵ]
            rw [smul_neg, smul_smul, neg_smul]
            apply congrArg Neg.neg
            apply congrArg (fun s : ℝ => s • b)
            ring
      exact hnot ⟨A / B, div_pos hAs_pos hBt_pos, heq⟩
    rcases hTiny (û := û) (ŵ := ŵ) hûunit hŵunit hneq with ⟨η, hη0, hη⟩
    let ε : ℝ := min (min A B) η / 2
    have hεpos : 0 < ε := by
      dsimp [ε]
      exact half_pos (lt_min (lt_min hAs_pos hBt_pos) hη0)
    have hεltη : ε < η := by
      dsimp [ε]
      have h1 : min (min A B) η ≤ η := min_le_right _ _
      linarith
    have hεltA : ε < A := by
      dsimp [ε]
      have h1 : min (min A B) η ≤ A := le_trans (min_le_left _ _) (min_le_left _ _)
      linarith
    have hεltB : ε < B := by
      dsimp [ε]
      have h1 : min (min A B) η ≤ B := le_trans (min_le_left _ _) (min_le_right _ _)
      linarith
    -- a(ε) := ExpM(ε û) is inside the ball and radial identity applies
    have hεû_r : ε • û ∈ ball (0 : E) r := by
      rw [mem_ball, dist_eq_norm, sub_zero]
      have hnorm : ‖ε • û‖ < r := by
        have hle : ‖ε • û‖ ≤ ‖a‖ := by
          -- ε/A in (0,1) so ‖(ε/A)•a‖ ≤ ‖a‖
          have hscale : ε • û = (ε / A) • a := by
            dsimp [û]
            rw [smul_smul]
            congr 1
            ring
          rw [hscale]
          rw [norm_smul]
          have hεA0 : 0 ≤ ε / A := by positivity
          rw [Real.norm_of_nonneg hεA0]
          have hle1 : ε / A ≤ 1 := by
            have hlt : ε < A := hεltA
            have hpos : 0 < A := hAs_pos
            rw [div_le_iff₀ hpos]
            nlinarith
          exact mul_le_of_le_one_left (norm_nonneg a) hle1
        have hmem := (mem_ball.mp ha_mem)
        rw [dist_eq_norm, sub_zero] at hmem
        exact lt_of_le_of_lt hle hmem
      exact hnorm
    have hεŵ_r : ε • ŵ ∈ ball (0 : E) r := by
      rw [mem_ball, dist_eq_norm, sub_zero]
      have hnorm : ‖ε • ŵ‖ < r := by
        have hscale : ε • ŵ = (ε / B) • b := by
          dsimp [ŵ]
          rw [smul_smul]
          congr 1
          ring
        rw [hscale]
        rw [norm_smul]
        have hεB0 : 0 ≤ ε / B := by positivity
        rw [Real.norm_of_nonneg hεB0]
        have hle1 : ε / B ≤ 1 := by
          have hlt : ε < B := hεltB
          have hpos : 0 < B := hBt_pos
          rw [div_le_iff₀ hpos]
          nlinarith
        have hle : (ε / B) * ‖b‖ ≤ ‖b‖ := mul_le_of_le_one_left (norm_nonneg b) hle1
        have hmem := (mem_ball.mp hb_mem)
        rw [dist_eq_norm, sub_zero] at hmem
        exact lt_of_le_of_lt (by simpa [mul_comm] using hle) hmem
      exact hnorm
    have hd_ae_p : edist p (ExpM (ε • û)) = ENNReal.ofReal ε := by
      have hd := hRadial (ε • û) hεû_r
      have hs := sqrt_quad_smul_nonneg (ge x₀) (le_of_lt hεpos) û (hBnonneg û)
      calc
        edist p (ExpM (ε • û)) = ENNReal.ofReal (Real.sqrt ((ge x₀) (ε • û) (ε • û))) := by
          simpa [x₀] using hd
        _ = ENNReal.ofReal (ε * Real.sqrt ((ge x₀) û û)) := by rw [hs]
        _ = ENNReal.ofReal ε := by rw [hûunit]; ring
    have hd_be_p : edist p (ExpM (ε • ŵ)) = ENNReal.ofReal ε := by
      have hd := hRadial (ε • ŵ) hεŵ_r
      have hs := sqrt_quad_smul_nonneg (ge x₀) (le_of_lt hεpos) ŵ (hBnonneg ŵ)
      calc
        edist p (ExpM (ε • ŵ)) = ENNReal.ofReal (Real.sqrt ((ge x₀) (ε • ŵ) (ε • ŵ))) := by
          simpa [x₀] using hd
        _ = ENNReal.ofReal (ε * Real.sqrt ((ge x₀) ŵ ŵ)) := by rw [hs]
        _ = ENNReal.ofReal ε := by rw [hŵunit]; ring
    -- subarc distances along û and ŵ (two-sided identity, ε ≤ A and ε ≤ B, all < ρa)
    have hsub_a : edist (ExpM (ε • û)) (ExpM (A • û)) = ENNReal.ofReal (A - ε) := by
      have hle : ε ≤ A := le_of_lt hεltA
      have hltA' : |A| < ρa := by
        rw [abs_of_pos hAs_pos]
        exact hA_lt_ρa
      have hltε : |ε| < ρa := by
        rw [abs_of_pos hεpos]
        exact lt_trans hεltA hA_lt_ρa
      exact hArcM û hûunit (s := ε) (t := A) hle hltε hltA'
    have hsub_b : edist (ExpM (ε • ŵ)) (ExpM (B • ŵ)) = ENNReal.ofReal (B - ε) := by
      have hle : ε ≤ B := le_of_lt hεltB
      have hltB' : |B| < ρa := by
        rw [abs_of_pos hBt_pos]
        exact hB_lt_ρa
      have hltε : |ε| < ρa := by
        rw [abs_of_pos hεpos]
        exact lt_trans hεltB hB_lt_ρa
      exact hArcM ŵ hŵunit (s := ε) (t := B) hle hltε hltB'
    -- propagation: distance from ExpM(ε û) to ExpM(ε ŵ) is exactly 2ε
    have h_ae_b_le : edist (ExpM (ε • û)) (ExpM b) ≤ ENNReal.ofReal (ε + B) := by
      calc
        edist (ExpM (ε • û)) (ExpM b) ≤ edist (ExpM (ε • û)) p + edist p (ExpM b) :=
          edist_triangle _ _ _
        _ = ENNReal.ofReal ε + ENNReal.ofReal B := by
          rw [edist_comm, hd_ae_p, hd_b_p]
        _ = ENNReal.ofReal (ε + B) := by
          rw [ENNReal.ofReal_add (le_of_lt hεpos) (le_of_lt hBt_pos)]
    have h_ae_b_ge : ENNReal.ofReal (ε + B) ≤ edist (ExpM (ε • û)) (ExpM b) := by
      have htri : edist (ExpM a) (ExpM b) ≤
          edist (ExpM a) (ExpM (ε • û)) + edist (ExpM (ε • û)) (ExpM b) :=
        edist_triangle _ _ _
      have hsub_a' : edist (ExpM (A • û)) (ExpM (ε • û)) = ENNReal.ofReal (A - ε) := by
        simpa [edist_comm] using hsub_a
      have hd1 : edist (ExpM a) (ExpM (ε • û)) = ENNReal.ofReal (A - ε) := by
        rw [← hAû]
        exact hsub_a'
      have hstep : ENNReal.ofReal (A + B) ≤ ENNReal.ofReal (A - ε) + edist (ExpM (ε • û)) (ExpM b) := by
        simpa [hd_ab, hd1] using htri
      have hnonneg : 0 ≤ A - ε := by linarith
      calc
        ENNReal.ofReal (ε + B) = ENNReal.ofReal ((A + B) - (A - ε)) := by
          congr 1
          ring
        _ = ENNReal.ofReal (A + B) - ENNReal.ofReal (A - ε) := by
          rw [ENNReal.ofReal_sub (A + B) hnonneg]
        _ ≤ edist (ExpM (ε • û)) (ExpM b) := by
          exact (tsub_le_iff_right).2 (by simpa [add_comm] using hstep)
    have h_ae_b : edist (ExpM (ε • û)) (ExpM b) = ENNReal.ofReal (ε + B) :=
      le_antisymm h_ae_b_le h_ae_b_ge
    have h_ae_be_le : edist (ExpM (ε • û)) (ExpM (ε • ŵ)) ≤ ENNReal.ofReal (2 * ε) := by
      calc
        edist (ExpM (ε • û)) (ExpM (ε • ŵ)) ≤ edist (ExpM (ε • û)) p + edist p (ExpM (ε • ŵ)) :=
          edist_triangle _ _ _
        _ = ENNReal.ofReal ε + ENNReal.ofReal ε := by
          rw [edist_comm, hd_ae_p, hd_be_p]
        _ = ENNReal.ofReal (2 * ε) := by
          rw [← ENNReal.ofReal_add (le_of_lt hεpos) (le_of_lt hεpos)]
          ring
    have h_ae_be_ge : ENNReal.ofReal (2 * ε) ≤ edist (ExpM (ε • û)) (ExpM (ε • ŵ)) := by
      have htri : edist (ExpM (ε • û)) (ExpM b) ≤
          edist (ExpM (ε • û)) (ExpM (ε • ŵ)) + edist (ExpM (ε • ŵ)) (ExpM b) :=
        edist_triangle _ _ _
      have hd2 : edist (ExpM (ε • ŵ)) (ExpM b) = ENNReal.ofReal (B - ε) := by
        rw [← hBŵ]
        exact hsub_b
      have hstep : ENNReal.ofReal (ε + B) ≤
          edist (ExpM (ε • û)) (ExpM (ε • ŵ)) + ENNReal.ofReal (B - ε) := by
        simpa [h_ae_b, hd2] using htri
      have hnonneg : 0 ≤ B - ε := by linarith
      calc
        ENNReal.ofReal (2 * ε) = ENNReal.ofReal ((ε + B) - (B - ε)) := by
          congr 1
          ring
        _ = ENNReal.ofReal (ε + B) - ENNReal.ofReal (B - ε) := by
          rw [ENNReal.ofReal_sub (ε + B) hnonneg]
        _ ≤ edist (ExpM (ε • û)) (ExpM (ε • ŵ)) := by
          exact (tsub_le_iff_right).2 (by simpa [add_comm] using hstep)
    have h_ae_be : edist (ExpM (ε • û)) (ExpM (ε • ŵ)) = ENNReal.ofReal (2 * ε) :=
      le_antisymm h_ae_be_le h_ae_be_ge
    -- contradiction with the tiny-scale strict inequality
    have hsmall : edist (ExpM (ε • û)) (ExpM (ε • ŵ)) < ENNReal.ofReal (2 * ε) := hη ε hεpos hεltη
    exact (ne_of_lt hsmall) h_ae_be
  -- ============================================================
  -- assemble v
  -- ============================================================
  let t₀ : ℝ := δ / 2
  have ht₀δ : |t₀| < δ := by
    dsimp [t₀]
    have hδhalf : δ / 2 < δ := by linarith [hδ0]
    rw [abs_of_pos (half_pos hδ0)]
    exact hδhalf
  have ht₀pos : 0 < t₀ := by dsimp [t₀]; positivity
  let v : E := (1 / t₀) • x t₀
  have hvnorm : Real.sqrt ((ge x₀) v v) = cR := by
    have hx := hxnorm t₀ ht₀δ
    have hsc : 0 ≤ 1 / t₀ := by positivity
    have hs := sqrt_quad_smul_nonneg (ge x₀) hsc (x t₀) (hBnonneg (x t₀))
    have hxt0 : Real.sqrt ((ge x₀) (x t₀) (x t₀)) = cR * t₀ := by
      rw [hx, abs_of_pos ht₀pos]
    calc
      Real.sqrt ((ge x₀) v v) = Real.sqrt ((ge x₀) ((1 / t₀) • x t₀) ((1 / t₀) • x t₀)) := by rfl
      _ = (1 / t₀) * Real.sqrt ((ge x₀) (x t₀) (x t₀)) := hs
      _ = (1 / t₀) * (cR * t₀) := by rw [hxt0]
      _ = cR := by field_simp [ne_of_gt ht₀pos]
  -- every x(t) equals t • v
  have hxt0 : Real.sqrt ((ge x₀) (x t₀) (x t₀)) = cR * t₀ := by
    rw [hxnorm t₀ ht₀δ, abs_of_pos ht₀pos]
  have hx_lin : ∀ t : ℝ, |t| < δ → x t = t • v := by
    intro t ht
    by_cases ht0 : t = 0
    · subst t
      rw [hx0]
      simp
    · by_cases htp : 0 < t
      · -- positive t: same ray as t₀
        have hmt₀ : |-t₀| < δ := by
          rw [abs_neg]
          exact ht₀δ
        rcases hPair (s := -t₀) (t := t) hmt₀ ht (by linarith) htp with ⟨lam1, hlam10, hneg1⟩
        rcases hPair (s := -t₀) (t := t₀) hmt₀ ht₀δ (by linarith) ht₀pos with ⟨lam2, hlam20, hneg2⟩
        -- x(-t₀) = -lam1 • x t = -lam2 • x(t₀)  =>  x t = (lam2/lam1) • x(t₀)
        have hrel : x t = (lam2 / lam1) • x t₀ := by
          have h1' : lam1 • x t = lam2 • x t₀ := by
            have heq : -lam1 • x t = -lam2 • x t₀ := by
              rw [← hneg1, ← hneg2]
            have hpos : lam1 • x t = -(-lam1 • x t) := by simp
            rw [hpos, heq]
            simp
          have hsc := congrArg (fun w : E => lam1⁻¹ • w) h1'
          have hsc2 := hsc
          rw [smul_smul] at hsc2
          have hL : (lam1⁻¹ * lam1) • x t = x t := by
            rw [inv_mul_cancel₀ (ne_of_gt hlam10)]
            simp
          have hR : (lam1⁻¹ * lam2) • x t₀ = (lam2 / lam1) • x t₀ := by
            apply congrArg (fun s : ℝ => s • x t₀)
            field_simp [ne_of_gt hlam10]
          rw [hL] at hsc2
          rw [smul_smul] at hsc2
          rw [hR] at hsc2
          exact hsc2
        -- norms: ‖x t‖_g = (lam2/lam1) * ‖x(t₀)‖_g
        have hnorm_t : Real.sqrt ((ge x₀) (x t) (x t)) = cR * |t| := hxnorm t ht
        have hrat_pos : 0 ≤ lam2 / lam1 := by positivity
        have hsqt : Real.sqrt ((ge x₀) (x t) (x t)) = (lam2 / lam1) * Real.sqrt ((ge x₀) (x t₀) (x t₀)) := by
          rw [hrel]
          exact sqrt_quad_smul_nonneg (ge x₀) hrat_pos (x t₀) (hBnonneg (x t₀))
        have hfactor : lam2 / lam1 = t / t₀ := by
          have hrhs : cR * |t| = (lam2 / lam1) * (cR * t₀) := by
            rw [← hnorm_t, hsqt, hxt0]
          have hpos : 0 < cR * t₀ := mul_pos hcR0 ht₀pos
          have hdiv : cR * |t| / (cR * t₀) = lam2 / lam1 := by
            rw [hrhs]
            field_simp [ne_of_gt hpos]
          have hd : cR * |t| / (cR * t₀) = |t| / t₀ := by
            field_simp [ne_of_gt hcR0, ne_of_gt ht₀pos]
          rw [← hdiv, hd]
          rw [abs_of_pos htp]
        calc
          x t = (lam2 / lam1) • x t₀ := hrel
          _ = (t / t₀) • x t₀ := by rw [hfactor]
          _ = t • v := by
            dsimp [v]
            rw [smul_smul]
            congr 1
            ring
      · -- negative t: x(t) is on the negative ray of x(t₀)
        have htn : t < 0 := by
          have hle : t ≤ 0 := le_of_not_gt htp
          exact lt_of_le_of_ne hle ht0
        rcases hPair (s := t) (t := t₀) ht ht₀δ htn ht₀pos with ⟨la, hla0, hneg⟩
        have hnorm_t : Real.sqrt ((ge x₀) (x t) (x t)) = cR * |t| := hxnorm t ht
        have hsqt : Real.sqrt ((ge x₀) (x t) (x t)) = la * Real.sqrt ((ge x₀) (x t₀) (x t₀)) := by
          calc
            Real.sqrt ((ge x₀) (x t) (x t))
                = Real.sqrt ((ge x₀) (-la • x t₀) (-la • x t₀)) := by rw [hneg]
            _ = Real.sqrt ((ge x₀) (la • x t₀) (la • x t₀)) := by simp
            _ = la * Real.sqrt ((ge x₀) (x t₀) (x t₀)) :=
              sqrt_quad_smul_nonneg (ge x₀) (le_of_lt hla0) (x t₀) (hBnonneg (x t₀))
        have hla : la = |t| / t₀ := by
          have hrhs : cR * |t| = la * (cR * t₀) := by
            rw [← hnorm_t, hsqt, hxt0]
          have hpos : 0 < cR * t₀ := mul_pos hcR0 ht₀pos
          have hdiv : cR * |t| / (cR * t₀) = la := by
            rw [hrhs]
            field_simp [ne_of_gt hpos]
          have hd : cR * |t| / (cR * t₀) = |t| / t₀ := by
            field_simp [ne_of_gt hcR0, ne_of_gt ht₀pos]
          rw [← hdiv, hd]
        calc
          x t = -la • x t₀ := hneg
          _ = -(|t| / t₀) • x t₀ := by rw [hla]
          _ = t • v := by
            dsimp [v]
            rw [smul_smul]
            apply congrArg (fun s : ℝ => s • x t₀)
            rw [abs_of_neg htn]
            ring
  -- final: γ t = ExpM (t • v) and the norm is c
  refine ⟨v, ?_, ?_⟩
  · -- Real.sqrt ((ge x₀) v v) = c
    have hv := hvnorm
    -- cR is defeq (c : ℝ)
    simpa [cR, x₀] using hv
  · intro t ht
    have h1 := hxExp t ht
    have h2 := hx_lin t ht
    calc
      γ t = ExpM (x t) := h1.symm
      _ = ExpM (t • v) := by rw [h2]
end Submission
