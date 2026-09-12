import Submission.Cwnorm
import Submission.ChebGrowth
import Submission.SerrePotentialIcc
import Submission.WnormToolkit
import Submission.RemezReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic
import Mathlib.Order.Interval.Set.Infinite

/-!
# Weighted Remez division by a COMPLEX root (Smith `lem:Remez`, full version)

GOAL (complex-polynomial case of Smith prelim.tex `lem:Remez`, specialised to
`Σ = [aSerre,bSerre]`, `μ = muSerre`, `w = weight muSerre`):

    ∃ C > 0,  ∀ (N m : ℕ), 1 ≤ m → ∀ P : Polynomial ℂ, P.natDegree = m →
      ∀ α : ℂ, P.eval α = 0 →
        ∃ Q : Polynomial ℂ, P = (X − C α)·Q ∧
          cwnorm N Q ≤ ((2 · max N m : ℕ) : ℝ)^C · cwnorm N P

where `cwnorm k R = Submission.Cwnorm.cwnorm k R =
sSup_{x ∈ [aSerre,bSerre]} w(x)^k · ‖R.eval (x : ℂ)‖` for `R : Polynomial ℂ`.
This is the division lemma used by `cor:adjust` (bounding
`‖Q_i‖_N ≤ (2N)^C·‖Q‖_N` for `Q_i = Q/(X − α_i)` with the possibly COMPLEX
roots `α_i` of a squarefree integer `Q`) and by `lem:second_squeeze`
(bounding `‖H_j·G‖_N`).  The real-root instance is
`Submission/RemezReal.lean` (`RemezReal` namespace) — READ IT for the overall
structure, the weight/potential bookkeeping, and the endpoint/interval dance.
The NEW ingredient for complex roots is the near-root ("two-flank") estimate,
which is exactly `Submission/ChebGrowth.cheb_growth` (a degree-`d` complex
polynomial bounded on an interval stays bounded by `C·(d+1)` at a point
within `4L/d²` beyond an end).  All lemmas you need are below.

## Data / notation
- `aSerre bSerre` : ℝ with `0 < aSerre < bSerre` (`SerreExample`);
  `muSerre = serreMeasure gSerre aSerre bSerre`;
  `U(x) = logPotential muSerre (x : ℂ)`;
  `weight muSerre x = Real.exp (U x)` (`WeightedNorm.weight`);
  `cwnorm` (`Submission.Cwnorm`), real `wnorm` (`Submission.Contracts`).
- `exists_potential_half_holder` (SerrePotentialIcc): `∃ H ≥ 0, ∀ x y ∈ Icc,
  |U x − U y| ≤ H·√|x−y|` — hence on any interval of length `ℓ`,
  `w(x)^N ≤ e^{H·N·√ℓ}·w(y)^N`; with `ℓ = (N+1)⁻²` this gives the CONSTANT
  factor `e^H` (since `N·√((N+1)⁻²) = N/(N+1) ≤ 1`).
- `Polynomial.dvd_iff_isRoot`, `Polynomial.X_sub_C_dvd_iff`, division witness:
  from `P.eval α = 0` obtain the factorization `P = (X − C α)·Q`.
- `‖·‖` on ℂ is the norm; `cwnorm_*` API in `Submission.Cwnorm`
  (`cwnorm_ge_pointwise`, `cwnorm_sSup_le`, `cwnorm_nonneg`, `cwnorm_add_le`,
  `cwnorm_smul`, `cwnorm_sum_le`, `cwnorm_map_eq_wnorm`, `cwnorm_zero`).

## Proof plan
Fix `N ≥ 0`, `m ≥ 1`, `P` deg `m`, root `α`, and (once the factorization is
obtained) write `P = (X−Cα)·Q` with `Q.natDegree = m − 1` (or ≤ m−1).

(0) Handle `m = 1` and/or small-degree degeneracies directly if needed:
    `Q` is a constant `c`; `‖Q‖_N = |c|·‖1‖_N`; `‖P‖_N ≥ |c|·cwnorm-ish`
    estimate `‖P‖_N ≥ |c|·e^{−K}·min-diameter` — rather than fuss, note the
    proof below also works for `m = 1` with `d = 0` handled by making
    `ChebGrowth`-style bounds trivial for constants; simplest: treat `m=1`
    by the crude bound `‖Q‖_N ≤ (sup w^N)·|c| ≤ e^{N·K}...` NO — do the
    general argument: `sup` of `w^N·‖Q‖` is attained at some `x₀`; if
    `|x₀−α| ≥ r` use Case A; else Case B with `d = 0 ≤ m−1 = 0`: ChebGrowth
    needs `1 ≤ d`; for `d = 0` (Q constant) the "growth" is trivial
    (`Q` constant ⇒ `‖Q(x₀)‖ = ‖Q(y)‖` for flank points `y`): handle `d=0`
    as a special case: `‖Q(x₀)‖ = ‖Q(y)‖ ≤ max_{flank}‖Q‖` EXACTLY (no
    growth).  So split `m = 1` first and prove it directly: `P = c(X−α)`,
    `Q = c`; bound `|c|·sup_x w^N` vs `|c|·sup_x w^N·|x−α|`: show
    `sup_x w^N ≤ C₁·(N+1)² · sup_x w^N·|x−α|` for an absolute `C₁` (roots of
    the real function `x ↦ w^N·|x−α|` on `[aSerre,bSerre]`: split into
    `α ∉ [aSerre,bSerre]` and `α ∈ [aSerre,bSerre]`; in the latter case use
    the explicit `w(x) = e^{serreC}·x^{−γ}` (`weight_serre_on_Icc`) and the
    calculus of `x ↦ x^{−γN}·(x−Reα)` — the maximum of `x^{−γN}(x−t)` over
    `[a,b]` is `≥ c·a^{−γN}·(something)/N` by evaluating at
    `x₀ = min(b, t + t/(γN))`; you may instead avoid calculus by a crude
    two-point argument: values at `x = a` and `x = min(b, a + 1/(N+1))` give
    `sup w^N·|x−α| ≥ w^N(a)·min(|a−α|, (1/(N+1))·(a/(a+1/(N+1)))^{γN}/1)`
    and `(a/(a+1/(N+1)))^{γN} ≥ e^{−γ/a}` — so `≥ w^N(a)·min(|a−α|, c/N)`;
    and if `|a−α|` is small you use the OTHER side / the far-end value at
    `x = b`:  `w^N(b)(b−a)`-ish; overall `sup w^N·|x−α| ≥ w^N(a)·c/N` in all
    cases EXCEPT when `w`'s max point `a` is far from `α` in which case
    `≥ w^N(a)|a−α| ≥ w^N(a)·c` — combine into `≥ w^N(a)·min(c, c/N)`:  i.e.
    always `≥ w^N(a)·c/(N+1)`, giving `‖Q‖_N ≤ c'(N+1)·‖P‖_N ≤ (2N)^C·‖P‖_N`
    with `w^N(a) ≤ ‖Q‖_N·1` since `sup w^N = w^N(a)`... wait `w` decreasing?
    `w(x) = e^{serreC}x^{−γ}` with `γ = gSerre > 0` IS decreasing on `(0,∞)`,
    so `sup_{[a,b]} w^N = w(a)^N` (`weight_serre_on_Icc` +
    monotonicity of `x^{−γ}`).  USE THIS: it makes the `m=1` and other
    endpoint estimates much easier.)

(1) `δ₀ := (N+1:ℝ)⁻²` (so `δ₀ ≤ 1 < bSerre − aSerre`; intervals of length
    `δ₀` fit; for points within `δ₀` of an endpoint use the half-interval of
    length `δ₀/2` from that endpoint — copy RemezReal's interval dance).
    For every `x₀ ∈ [aSerre,bSerre]` there is a closed interval
    `I ⊆ [aSerre,bSerre]` with `x₀ ∈ I` and `δ₀/2 ≤ length I ≤ δ₀`
    (prove it; helper lemma `exists_interval_around`).
    By (Hölder) for `x,y ∈ I`: `w(x)^N ≤ e^H · w(y)^N` (constant `e^H`).

(2) `r := (m:ℝ)⁻² · δ₀ / 16` (positive).  `Σ₀ := {x ∈ Icc aSerre bSerre |
    ‖(x:ℂ) − α‖ ≤ r}` (real points within complex distance `r` of `α`).
    MAIN ESTIMATE to prove for every `x₀ ∈ [aSerre,bSerre]`:
        `w(x₀)^N·‖Q.eval (x₀:ℂ)‖ ≤ (2·max N m : ℕ)^C·‖P‖_N`   (uniform `C`)

    Case A: `x₀ ∉ Σ₀` (i.e. `‖(x₀:ℂ)−α‖ ≥ r`):  `‖Q(x₀)‖ = ‖P(x₀)‖/|x₀−α|
    ≤ ‖P(x₀)‖/r`, so `w^N‖Q‖ ≤ w^N‖P‖/r ≤ ‖P‖_N·(1/r)` with
    `1/r = 16·m²·(N+1)² ≤ (2·max N m)^C` (check: `N+1 ≤ 2·max N m` for
    `m ≥ 1`; `16 m² (N+1)² ≤ (2max(N,m))^6` say — verify and use).

    Case B: `x₀ ∈ Σ₀`.  Take the interval `I ∋ x₀` from (1).  Let
    `d := m − 1`.  Sub-estimate (`two-flank`, from `ChebGrowth`): there is an
    interval `J ⊂ I` (one of the two components of `I ∖ Σ₀`-interior) with
    `length J ≥ δ₀/8` and `dist(x₀, J) ≤ 2r` (distance to the closer flank;
    PROVE: `Σ₀∩I` has length ≤ `2r` when it meets `I`, so `I∖Σ₀` has total
    length ≥ `δ₀/2 − 2r ≥ δ₀/4`; pick the component nearer `x₀`; its length
    is ≥ `(δ₀/2 − 2r)/2` when the gap is interior, and ≥ `δ₀/2 − 2r` when
    it is an end-gap — in BOTH cases the chosen component has length
    `L ≥ δ₀/8` (verify: `2r = δ₀/(8m²) ≤ δ₀/8` so `δ₀/2 − 2r ≥ 3δ₀/8`; for
    an interior gap each component ≥ `(3δ₀/8)/2 = 3δ₀/16 ≥ δ₀/8`), and
    `x₀` is within `ρ := 2r = δ₀/(8m²)` of it.  Check the ChebGrowth
    hypothesis:  `ρ/L ≤ (δ₀/(8m²))/(δ₀/8) = 1/m² ≤ 4/(m−1)²` for `m ≥ 2`
    (since `4(m−1)² ≥ m²` for `m ≥ 2`); for `m = 1`, `d = 0` handled
    separately (constant `Q`: no growth needed — `‖Q(x₀)‖ = ‖Q(y)‖` for the
    flank point `y`).
    Let `B := max_{y ∈ J} ‖Q.eval (y:ℂ)‖`.  Apply `ChebGrowth.cheb_growth`
    (both one-sided clauses; scale: `Q/B` bounded by 1 on `J`, using the
    clause matching whether `x₀` is right or left of `J`, with
    `c := left endpoint of J`, `L := length J`, `ρ := dist`) to get
    `‖Q(x₀)‖ ≤ Cg·(d+1)·B ≤ Cg·(m)·B` (or `≤ Cg·(d+1)+1` scaled:
    `‖Q(x₀)‖ ≤ (Cg·(d+1)+1)·B`).  `B ≤ max_{y∈I∖Σ₀}‖Q(y)‖`, and for
    `y ∈ I∖Σ₀`: `‖Q(y)‖ = ‖P(y)‖/|y−α| ≤ ‖P(y)‖·(1/r)`.
    Weighted: for the `y₀ ∈ I∖Σ₀` attaining `B` (or any point with
    `‖Q(y₀)‖ ≥ B/2`-ish; you may instead bound directly: `B ≤
    max_{y ∈ I∖Σ₀} ‖P(y)‖/r`), we have `x₀,y₀ ∈ I` so `w(x₀)^N ≤ e^H w(y₀)^N`:
        `w(x₀)^N‖Q(x₀)‖ ≤ e^H·(Cg·m+1)·(1/r)·w(y₀)^N‖P(y₀)‖ ≤ e^H(Cg m+1)(1/r)‖P‖_N`.
    Absorb `e^H·(Cg·m + 1)·16m²(N+1)² ≤ (2max(N,m))^{C}` for a big enough
    absolute `C` (e.g. `C = 40`; just prove existence by choosing a large
    explicit `C` or by `∃` with `refine ⟨..., ?_⟩` and pushing through —
    the arithmetic is elementary: all factors are `≤ (2max(N,m))^{c}` for
    absolute `c`; you may use `nlinarith`/`nlinarith`-style and
    `Real.rpow`-monotonicity lemmas, or reduce to powers of integers).

(3) Conclude with `cwnorm_sSup_le`: for every `x₀ ∈ Icc` the pointwise bound
    of (2) holds, so `cwnorm N Q ≤ (2max(N,m))^C·cwnorm N P`.
    (Note `cwnorm N P` in the bound vs the `‖P‖_N` shorthand — identical.)

## Extra facts you may need / want to prove as helpers in this file
- `weight_decreasing` : `w` is decreasing on `[aSerre,bSerre]` (from
  `weight_serre_on_Icc`: `w(x) = e^{serreConstant}·x^{−gSerre}` and
  `Real.rpow`/pow monotonicity — `gSerre > 0`, so `x^{−gSerre}` decreases),
  hence `sup_{x ∈ Icc} w(x)^N = w(aSerre)^N` (used only for `m=1` clarity;
  NOT essential elsewhere).
- `one_div_r_bound`: `16·(m:ℝ)²·(N+1:ℝ)² ≤ (2·max N m : ℝ)^C` for your `C`.
- division by a root: `P.eval α = 0` → `∃ Q, P = (X − C α) · Q` via
  `Polynomial.dvd_iff_isRoot` (a root iff `X−Cα ∣ P`; note `eval` of `ℂ`
  polynomial at complex `α`).  Also `Q.natDegree ≤ m − 1` (or = m−1).
- from `P = (X−Cα)·Q`: `‖P.eval (y:ℂ)‖ = ‖(y:ℂ)−α‖·‖Q.eval (y:ℂ)‖` and
  `|y − α| = ‖(y:ℂ) − α‖` (norm of a complex number equals its abs, and
  `(y:ℂ) − α` for real `y` — use `Complex.normSq`/`norm`-simp).

Read `Submission/RemezReal.lean` and `Submission/ChebGrowth.lean` for exact
names and for the interval dance; read `Submission/Cwnorm.lean` for the norm
API.  Everything hole-free, axioms only propext/Quot.sound/Classical.choice.
Keep the declaration below EXACTLY as written.  You may add helper lemmas in
this file (namespace `Submission.RemezComplex`).
-/

noncomputable section

set_option maxHeartbeats 1000000

open MeasureTheory
open scoped Real BigOperators
open Polynomial

namespace Submission.RemezComplex

open Submission.Cwnorm
open Submission.Contracts
open Submission.Serre
open Submission.SerreExample
open Submission.WeightedNorm
open Submission.SerrePotentialIcc
open Submission.PotentialDefs
open Submission.WnormToolkit
open Submission.ChebGrowth


/-! ## Helper lemmas -/

/-- A small closed interval around `x₀` inside `[aSerre,bSerre]` of length
between `δ/2` and `δ`. -/
lemma interval_around {x₀ δ : ℝ} (hδpos : 0 < δ) (hδle : δ ≤ bSerre - aSerre)
    (hx₀ : x₀ ∈ Set.Icc aSerre bSerre) :
    ∃ u v : ℝ, aSerre ≤ u ∧ u < v ∧ v ≤ bSerre ∧
      x₀ ∈ Set.Icc u v ∧ δ / 2 ≤ v - u ∧ v - u ≤ δ := by
  rcases hx₀ with ⟨hxlo, hxhi⟩
  by_cases h1 : x₀ ≤ aSerre + δ / 2
  · refine ⟨aSerre, aSerre + δ, le_rfl, ?_, ?_, ?_, ?_, ?_⟩
    · linarith
    · linarith
    · constructor <;> linarith
    · linarith
    · linarith
  · have h1' : aSerre + δ / 2 < x₀ := lt_of_not_ge h1
    by_cases h2 : x₀ ≤ bSerre - δ / 2
    · refine ⟨x₀ - δ / 2, x₀ + δ / 2, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · linarith
      · linarith
      · linarith
      · constructor <;> linarith
      · linarith
      · linarith
    · have h2' : bSerre - δ / 2 < x₀ := lt_of_not_ge h2
      refine ⟨bSerre - δ, bSerre, ?_, ?_, le_rfl, ?_, ?_, ?_⟩
      · linarith
      · linarith
      · constructor <;> linarith
      · linarith
      · linarith

/-- A point at least `2r` to the right of a point within complex distance `< r`
of `α` is itself at complex distance `≥ r` of `α`. -/
lemma far_good_right {x₀ y : ℝ} {α : ℂ} {r : ℝ} (hr : 0 < r)
    (hx : ‖(x₀ : ℂ) - α‖ < r) (hy : x₀ + 2 * r ≤ y) : r ≤ ‖(y : ℂ) - α‖ := by
  let z : ℂ := (y : ℂ) - α
  have hzre : z.re = y - α.re := by
    simp [z]
  have hαx : |x₀ - α.re| < r := by
    have h1 : ((x₀ : ℂ) - α).re = x₀ - α.re := by simp
    rw [← h1]
    exact lt_of_le_of_lt (RCLike.abs_re_le_norm ((x₀ : ℂ) - α)) hx
  have hgt : r < y - α.re := by
    have hb : -r < x₀ - α.re := (abs_lt.mp hαx).1
    nlinarith
  have hpos : 0 < y - α.re := by linarith
  calc
    r ≤ |z.re| := by
      rw [hzre, abs_of_pos hpos]
      exact le_of_lt hgt
    _ ≤ ‖z‖ := by
      exact RCLike.abs_re_le_norm z

/-- A point at least `2r` to the left of a point within complex distance `< r`
of `α` is itself at complex distance `≥ r` of `α`. -/
lemma far_good_left {x₀ y : ℝ} {α : ℂ} {r : ℝ} (hr : 0 < r)
    (hx : ‖(x₀ : ℂ) - α‖ < r) (hy : y + 2 * r ≤ x₀) : r ≤ ‖(y : ℂ) - α‖ := by
  let z : ℂ := (y : ℂ) - α
  have hzre : z.re = y - α.re := by
    simp [z]
  have hαx : |x₀ - α.re| < r := by
    have h1 : ((x₀ : ℂ) - α).re = x₀ - α.re := by simp
    rw [← h1]
    exact lt_of_le_of_lt (RCLike.abs_re_le_norm ((x₀ : ℂ) - α)) hx
  have hneg : y - α.re < 0 := by
    have hb : x₀ - α.re < r := (abs_lt.mp hαx).2
    have : y - α.re < -r := by nlinarith
    linarith
  have hgt : r < -(y - α.re) := by
    have hb : x₀ - α.re < r := (abs_lt.mp hαx).2
    nlinarith
  calc
    r ≤ |z.re| := by
      rw [hzre, abs_of_neg hneg]
      exact le_of_lt hgt
    _ ≤ ‖z‖ := by
      exact RCLike.abs_re_le_norm z

/-- Two-flank geometry: from a point `x₀ ∈ [u,v]` within distance `< r` of the
(possibly complex) point `α`, there is a subinterval `[c,c+L] ⊆ [u,v]` of
length `≥ δ/32`, all of whose points are at distance `≥ r` from `α`, and
`x₀` lies beyond one of its ends at distance exactly `2r`. -/
lemma flank_good (α : ℂ) {u v x₀ : ℝ} (r δ : ℝ) (hr : 0 < r) (hδ : 0 < δ)
    (huv : u < v) (hx₀ : x₀ ∈ Set.Icc u v)
    (hδ2 : δ / 2 ≤ v - u) (h4r : 4 * r ≤ δ / 4)
    (hbad : ‖(x₀ : ℂ) - α‖ < r) :
    ∃ c L : ℝ, u ≤ c ∧ c + L ≤ v ∧ 0 < L ∧ δ / 32 ≤ L ∧
      (∀ y : ℝ, y ∈ Set.Icc c (c + L) → r ≤ ‖(y : ℂ) - α‖) ∧
      (x₀ = c - 2 * r ∨ x₀ = c + L + 2 * r) := by
  rcases hx₀ with ⟨hxlo, hxhi⟩
  by_cases hR : δ / 32 ≤ v - (x₀ + 2 * r)
  · refine ⟨x₀ + 2 * r, v - (x₀ + 2 * r), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · nlinarith [hxlo, hr]
    · linarith
    · nlinarith [hR, hδ]
    · exact hR
    · intro y hy
      exact far_good_right hr hbad hy.1
    · left
      ring
  · have hRlt : v - (x₀ + 2 * r) < δ / 32 := lt_of_not_ge hR
    refine ⟨u, x₀ - 2 * r - u, le_rfl, ?_, ?_, ?_, ?_, ?_⟩
    · nlinarith [hxhi]
    · nlinarith [hδ2, h4r, hRlt, hδ]
    · nlinarith [hδ2, h4r, hRlt, hδ]
    · intro y hy
      exact far_good_left hr hbad (by nlinarith [hy.2])
    · right
      ring
/-- A nonzero complex polynomial cannot vanish on a nondegenerate real
interval. -/
lemma poly_zero_of_eval_zero_on_Icc {P : Polynomial ℂ} {c L : ℝ} (hL : 0 < L)
    (hP : ∀ y : ℝ, y ∈ Set.Icc c (c + L) → P.eval (y : ℂ) = 0) : P = 0 := by
  by_contra hPne
  have hfin : Set.Finite {x : ℂ | P.IsRoot x} := Polynomial.finite_setOfPred_isRoot hPne
  have hrootall : ∀ y : ℝ, y ∈ Set.Icc c (c + L) → P.IsRoot (y : ℂ) := by
    intro y hy
    exact hP y hy
  have hc : c < c + L := by linarith
  have hinfin : (Set.Icc c (c + L)).Infinite := Set.Icc_infinite hc
  have hinjon : Set.InjOn (fun y : ℝ => (y : ℂ)) (Set.Icc c (c + L)) := by
    exact Complex.ofReal_injective.injOn.mono (Set.subset_univ _)
  have himg : ((fun y : ℝ => (y : ℂ)) '' Set.Icc c (c + L)).Infinite := hinfin.image hinjon
  have hsubset : (fun y : ℝ => (y : ℂ)) '' Set.Icc c (c + L) ⊆ {x : ℂ | P.IsRoot x} := by
    intro z hz
    rcases hz with ⟨y, hy, rfl⟩
    exact hrootall y hy
  have hrootinf : ({x : ℂ | P.IsRoot x}).Infinite := himg.mono hsubset
  exact hrootinf hfin

/-- The quotient `Q` in `P = (X − Cα)·Q` has degree at most `m = natDegree P`. -/
lemma q_natDegree_le {P Q : Polynomial ℂ} {m : ℕ} {α : ℂ} (hm : 1 ≤ m)
    (hdegP : P.natDegree = m) (hfac : P = (Polynomial.X - Polynomial.C α) * Q) :
    Q.natDegree ≤ m := by
  by_cases hQ0 : Q = 0
  · simp [hQ0]
  · have hPne : P ≠ 0 := by
      intro hP0
      have : m = 0 := by
        rw [← hdegP, hP0]
        simp
      omega
    have hXne : (Polynomial.X - Polynomial.C α : Polynomial ℂ) ≠ 0 := by
      intro hX0
      have hdeg : (Polynomial.X - Polynomial.C α : Polynomial ℂ).natDegree = 0 := by
        rw [hX0]
        simp
      rw [Polynomial.natDegree_X_sub_C] at hdeg
      norm_num at hdeg
    have hmul := Polynomial.natDegree_mul hXne hQ0
    have hf : P.natDegree = (Polynomial.X - Polynomial.C α : Polynomial ℂ).natDegree + Q.natDegree := by
      rw [hfac, hmul]
    rw [Polynomial.natDegree_X_sub_C] at hf
    rw [hdegP] at hf
    omega

/-- The maximum of `‖P.eval (y:ℂ)‖` on a nondegenerate interval is attained. -/
lemma exists_max_norm_eval (P : Polynomial ℂ) {c L : ℝ} (hL : 0 < L) :
    ∃ z : ℝ, z ∈ Set.Icc c (c + L) ∧
      ∀ y : ℝ, y ∈ Set.Icc c (c + L) → ‖P.eval (y : ℂ)‖ ≤ ‖P.eval (z : ℂ)‖ := by
  have hcont : ContinuousOn (fun y : ℝ => ‖P.eval (y : ℂ)‖) (Set.Icc c (c + L)) := by
    have hc : Continuous (fun y : ℝ => P.eval (y : ℂ)) := by
      have h1 : Continuous (fun z : ℂ => Polynomial.aeval z P) := Polynomial.continuous_aeval P
      have h2 := h1.comp Complex.continuous_ofReal
      convert h2 using 1
      ext y
      simp [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    exact (Continuous.norm hc).continuousOn
  have hne : (Set.Icc c (c + L) : Set ℝ).Nonempty := ⟨c, le_rfl, by linarith⟩
  rcases isCompact_Icc.exists_isMaxOn hne hcont with ⟨z, hz, hzmax⟩
  refine ⟨z, hz, ?_⟩
  intro y hy
  exact (isMaxOn_iff.mp hzmax) y hy

/-- `cheb_growth` rescaled by a uniform bound `B ≥ 0` (single probe point). -/
lemma cheb_scaled_point {Cg : ℝ} {d : ℕ} (hd : 1 ≤ d) {Q : Polynomial ℂ} {c L ρ B : ℝ} {t : ℂ}
    (hL : 0 < L) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ (4 : ℝ) * L / (d : ℝ) ^ 2) (hB : 0 ≤ B)
    (hdeg : Q.natDegree ≤ d)
    (hbnd : ∀ y : ℝ, y ∈ Set.Icc c (c + L) → ‖Q.eval (y : ℂ)‖ ≤ B)
    (hclause : ∀ (R : Polynomial ℂ), R.natDegree ≤ d →
      (∀ y : ℝ, y ∈ Set.Icc c (c + L) → ‖R.eval (y : ℂ)‖ ≤ 1) →
        ‖R.eval t‖ ≤ Cg * (d : ℝ) + 1) :
    ‖Q.eval t‖ ≤ (Cg * (d : ℝ) + 1) * B := by
  by_cases hB0 : B = 0
  · have hQ0 : Q = 0 := by
      apply poly_zero_of_eval_zero_on_Icc hL
      intro y hy
      have hb := hbnd y hy
      rw [hB0] at hb
      exact norm_eq_zero.mp (le_antisymm hb (norm_nonneg _))
    subst Q
    rw [hB0]
    simp
  · have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
    have hBne : B ≠ 0 := ne_of_gt hBpos
    let c0 : ℂ := ((B⁻¹ : ℝ) : ℂ)
    let R : Polynomial ℂ := Polynomial.C c0 * Q
    have hc0norm : ‖c0‖ = B⁻¹ := by
      have hnorm : ‖((B⁻¹ : ℝ) : ℂ)‖ = |B⁻¹| := by simp
      rw [hnorm, abs_of_pos (inv_pos.mpr hBpos)]
    have hdegR : R.natDegree ≤ d := by
      calc
        R.natDegree ≤ (Polynomial.C c0).natDegree + Q.natDegree := by
          unfold R
          exact Polynomial.natDegree_mul_le
        _ ≤ d := by
          rw [Polynomial.natDegree_C]
          omega
    have hRbnd : ∀ y : ℝ, y ∈ Set.Icc c (c + L) → ‖R.eval (y : ℂ)‖ ≤ 1 := by
      intro y hy
      calc
        ‖R.eval (y : ℂ)‖ = ‖c0 * Q.eval (y : ℂ)‖ := by simp [R]
        _ = ‖c0‖ * ‖Q.eval (y : ℂ)‖ := by rw [norm_mul]
        _ = B⁻¹ * ‖Q.eval (y : ℂ)‖ := by rw [hc0norm]
        _ ≤ B⁻¹ * B := mul_le_mul_of_nonneg_left (hbnd y hy) (inv_nonneg.mpr hB)
        _ = 1 := by rw [inv_mul_cancel₀ hBne]
    have hcl := hclause R hdegR hRbnd
    have hSR : ‖R.eval t‖ = ‖c0‖ * ‖Q.eval t‖ := by
      simp [R, norm_mul]
    have hmain : B⁻¹ * ‖Q.eval t‖ ≤ Cg * (d : ℝ) + 1 := by
      rw [hSR] at hcl
      rwa [hc0norm] at hcl
    calc
      ‖Q.eval t‖ = (B * B⁻¹) * ‖Q.eval t‖ := by
        rw [mul_inv_cancel₀ hBne, one_mul]
      _ = B * (B⁻¹ * ‖Q.eval t‖) := by rw [← mul_assoc]
      _ ≤ B * (Cg * (d : ℝ) + 1) := mul_le_mul_of_nonneg_left hmain (le_of_lt hBpos)
      _ = (Cg * (d : ℝ) + 1) * B := by ring

/-- `cheb_growth` rescaled by a uniform bound `B ≥ 0`, both ends. -/
lemma cheb_scaled {Cg : ℝ}
    (hprops : ∀ (d : ℕ), 1 ≤ d → ∀ (c : ℝ) (L : ℝ) (ρ : ℝ),
      0 < L → 0 ≤ ρ → ρ ≤ (4 : ℝ) * L / (d : ℝ) ^ 2 →
      (∀ (Q : Polynomial ℂ), Q.natDegree ≤ d →
        (∀ y : ℝ, y ∈ Set.Icc c (c + L) → ‖Q.eval (y : ℂ)‖ ≤ 1) →
          ‖Q.eval ((c + L + ρ) : ℂ)‖ ≤ Cg * (d : ℝ) + 1) ∧
      (∀ (Q : Polynomial ℂ), Q.natDegree ≤ d →
        (∀ y : ℝ, y ∈ Set.Icc c (c + L) → ‖Q.eval (y : ℂ)‖ ≤ 1) →
          ‖Q.eval ((c - ρ) : ℂ)‖ ≤ Cg * (d : ℝ) + 1))
    {d : ℕ} (hd : 1 ≤ d) {Q : Polynomial ℂ} {c L ρ B : ℝ} (hL : 0 < L) (hρ0 : 0 ≤ ρ)
    (hρ : ρ ≤ (4 : ℝ) * L / (d : ℝ) ^ 2) (hB : 0 ≤ B) (hdeg : Q.natDegree ≤ d)
    (hbnd : ∀ y : ℝ, y ∈ Set.Icc c (c + L) → ‖Q.eval (y : ℂ)‖ ≤ B) :
    ‖Q.eval ((c + L + ρ) : ℂ)‖ ≤ (Cg * (d : ℝ) + 1) * B ∧
    ‖Q.eval ((c - ρ) : ℂ)‖ ≤ (Cg * (d : ℝ) + 1) * B := by
  constructor
  · exact cheb_scaled_point (t := (c + L + ρ : ℂ)) hd hL hρ0 hρ hB hdeg hbnd
      ((hprops d hd c L ρ hL hρ0 hρ).1)
  · exact cheb_scaled_point (t := (c - ρ : ℂ)) hd hL hρ0 hρ hB hdeg hbnd
      ((hprops d hd c L ρ hL hρ0 hρ).2)

/-- per-point bound in the FAR case (`x₀` at distance ≥ r from the root). -/
lemma div_bound_far (H0 : ℝ) (hH0 : 0 ≤ H0) (Cg : ℝ) (hCg0 : 0 ≤ Cg)
    {N m : ℕ} (hm : 1 ≤ m) {P Q : Polynomial ℂ} {α : ℂ} {x₀ : ℝ}
    (hfac : P = (Polynomial.X - Polynomial.C α) * Q)
    (hx₀ : x₀ ∈ Set.Icc aSerre bSerre)
    (hfar : (16 * (m : ℝ) ^ 2 * (((N : ℝ) + 1) ^ 2))⁻¹ ≤ ‖(x₀ : ℂ) - α‖) :
    (weight muSerre x₀) ^ N * ‖Q.eval (x₀ : ℂ)‖ ≤
      (16 * (Cg + 1) * Real.exp H0 * (m : ℝ) ^ 3 * ((N : ℝ) + 1) ^ 2) * cwnorm N P := by
  let A : ℝ := 16 * (m : ℝ) ^ 2 * (((N : ℝ) + 1) ^ 2)
  have hApos : 0 < A := by dsimp [A]; positivity
  have hAinvpos : 0 < A⁻¹ := inv_pos.mpr hApos
  have hxne : ‖(x₀ : ℂ) - α‖ ≠ 0 := by
    have : 0 < ‖(x₀ : ℂ) - α‖ := lt_of_lt_of_le hAinvpos hfar
    exact ne_of_gt this
  have hnormpos : 0 < ‖(x₀ : ℂ) - α‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hxne)
  have hPeq : P.eval (x₀ : ℂ) = ((x₀ : ℂ) - α) * Q.eval (x₀ : ℂ) := by
    rw [hfac]
    simp
  have hnormP : ‖P.eval (x₀ : ℂ)‖ = ‖(x₀ : ℂ) - α‖ * ‖Q.eval (x₀ : ℂ)‖ := by
    rw [hPeq, norm_mul]
  have hQdiv : ‖Q.eval (x₀ : ℂ)‖ = ‖P.eval (x₀ : ℂ)‖ * ‖(x₀ : ℂ) - α‖⁻¹ := by
    rw [hnormP]
    field_simp [hxne]
  have hAinv : ‖(x₀ : ℂ) - α‖⁻¹ ≤ (A⁻¹)⁻¹ := by
    exact (inv_le_inv₀ hnormpos hAinvpos).mpr hfar
  have hnormle : ‖(x₀ : ℂ) - α‖⁻¹ ≤ A := by
    rwa [inv_inv] at hAinv
  have hQle : ‖Q.eval (x₀ : ℂ)‖ ≤ ‖P.eval (x₀ : ℂ)‖ * A := by
    rw [hQdiv]
    exact mul_le_mul_of_nonneg_left hnormle (norm_nonneg _)
  have hw : (weight muSerre x₀) ^ N * ‖Q.eval (x₀ : ℂ)‖ ≤
      ((weight muSerre x₀) ^ N * ‖P.eval (x₀ : ℂ)‖) * A := by
    calc
      (weight muSerre x₀) ^ N * ‖Q.eval (x₀ : ℂ)‖
          ≤ (weight muSerre x₀) ^ N * (‖P.eval (x₀ : ℂ)‖ * A) := by
            exact mul_le_mul_of_nonneg_left hQle (pow_nonneg (le_of_lt (weight_pos muSerre x₀)) N)
      _ = ((weight muSerre x₀) ^ N * ‖P.eval (x₀ : ℂ)‖) * A := by ring
  have hwP : (weight muSerre x₀) ^ N * ‖P.eval (x₀ : ℂ)‖ ≤ cwnorm N P :=
    cwnorm_ge_pointwise N P hx₀
  have hfin1 : (weight muSerre x₀) ^ N * ‖Q.eval (x₀ : ℂ)‖ ≤ A * cwnorm N P := by
    calc
      (weight muSerre x₀) ^ N * ‖Q.eval (x₀ : ℂ)‖ ≤ ((weight muSerre x₀) ^ N * ‖P.eval (x₀ : ℂ)‖) * A := hw
      _ ≤ cwnorm N P * A := by
        exact mul_le_mul_of_nonneg_right hwP (le_of_lt hApos)
      _ = A * cwnorm N P := by ring
  have heH1 : 1 ≤ Real.exp H0 := by
    rw [← Real.exp_zero]
    exact (Real.exp_le_exp).2 hH0
  have hmm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hCg1 : (1 : ℝ) ≤ Cg + 1 := by linarith
  have hK : A ≤ 16 * (Cg + 1) * Real.exp H0 * (m : ℝ) ^ 3 * (((N : ℝ) + 1) ^ 2) := by
    have hbase : 0 ≤ A := le_of_lt hApos
    have hExp0 : 0 ≤ Real.exp H0 := Real.exp_nonneg H0
    have hCg0' : 0 ≤ Cg + 1 := by linarith
    have h1em : 1 ≤ Real.exp H0 * (m : ℝ) := by
      have h : (1 : ℝ) * 1 ≤ Real.exp H0 * (m : ℝ) :=
        mul_le_mul heH1 hmm1 (by norm_num) hExp0
      simpa using h
    have hfact : 1 ≤ (Cg + 1) * Real.exp H0 * (m : ℝ) := by
      have h : (1 : ℝ) * 1 ≤ (Cg + 1) * (Real.exp H0 * (m : ℝ)) :=
        mul_le_mul hCg1 h1em (by norm_num) hCg0'
      simpa [mul_assoc] using h
    calc
      A = A * 1 := by ring
      _ ≤ A * ((Cg + 1) * Real.exp H0 * (m : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hfact hbase
      _ = 16 * (Cg + 1) * Real.exp H0 * (m : ℝ) ^ 3 * (((N : ℝ) + 1) ^ 2) := by
        dsimp [A]
        ring
  calc
    (weight muSerre x₀) ^ N * ‖Q.eval (x₀ : ℂ)‖ ≤ A * cwnorm N P := hfin1
    _ ≤ (16 * (Cg + 1) * Real.exp H0 * (m : ℝ) ^ 3 * (((N : ℝ) + 1) ^ 2)) * cwnorm N P := by
      exact mul_le_mul_of_nonneg_right hK (cwnorm_nonneg N P)

/-- per-point bound in the NEAR case: `x₀` is within complex distance
`r = (16m²(N+1)²)⁻¹` of the root `α`; growth is controlled by the two-flank
Chebyshev estimate. -/
lemma div_bound_near (H0 : ℝ) (hH0 : 0 ≤ H0)
    (hU : ∀ x y : ℝ, x ∈ Set.Icc aSerre bSerre → y ∈ Set.Icc aSerre bSerre →
      |logPotential (serreMeasure gSerre aSerre bSerre) (x : ℂ) -
        logPotential (serreMeasure gSerre aSerre bSerre) (y : ℂ)| ≤ H0 * Real.sqrt |x - y|)
    (Cg : ℝ) (hCg0 : 0 ≤ Cg)
    (hCg : ∀ (d : ℕ), 1 ≤ d → ∀ (c : ℝ) (L : ℝ) (ρ : ℝ),
      0 < L → 0 ≤ ρ → ρ ≤ (4 : ℝ) * L / (d : ℝ) ^ 2 →
      (∀ (Q : Polynomial ℂ), Q.natDegree ≤ d →
        (∀ y : ℝ, y ∈ Set.Icc c (c + L) → ‖Q.eval (y : ℂ)‖ ≤ 1) →
          ‖Q.eval ((c + L + ρ) : ℂ)‖ ≤ Cg * (d : ℝ) + 1) ∧
      (∀ (Q : Polynomial ℂ), Q.natDegree ≤ d →
        (∀ y : ℝ, y ∈ Set.Icc c (c + L) → ‖Q.eval (y : ℂ)‖ ≤ 1) →
          ‖Q.eval ((c - ρ) : ℂ)‖ ≤ Cg * (d : ℝ) + 1))
    {N m : ℕ} (hm : 1 ≤ m) {P Q : Polynomial ℂ} {α : ℂ} {x₀ : ℝ}
    (hdegP : P.natDegree = m) (hfac : P = (Polynomial.X - Polynomial.C α) * Q)
    (hx₀ : x₀ ∈ Set.Icc aSerre bSerre)
    (hnear : ‖(x₀ : ℂ) - α‖ < (16 * (m : ℝ) ^ 2 * (((N : ℝ) + 1) ^ 2))⁻¹) :
    (weight muSerre x₀) ^ N * ‖Q.eval (x₀ : ℂ)‖ ≤
      (16 * (Cg + 1) * Real.exp H0 * (m : ℝ) ^ 3 * ((N : ℝ) + 1) ^ 2) * cwnorm N P := by
  let s : ℝ := (N : ℝ) + 1
  let δ : ℝ := 1 / s ^ 2
  let r : ℝ := δ / (16 * (m : ℝ) ^ 2)
  have hs1 : 1 ≤ s := by dsimp [s]; linarith
  have hs_pos : 0 < s := by linarith
  have hδpos : 0 < δ := by dsimp [δ]; positivity
  have hδeq : δ = 1 / ((N : ℝ) + 1) ^ 2 := by dsimp [δ, s]
  have hδle : δ ≤ bSerre - aSerre := by
    have hδ1 : δ ≤ 1 := by
      rw [hδeq]
      have hsq : 1 ≤ ((N : ℝ) + 1) ^ 2 := by
        have h1 : 1 ≤ (N : ℝ) + 1 := by exact_mod_cast (by omega : (1 : ℕ) ≤ N + 1)
        simpa using (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) h1 2)
      have hpos : 0 < ((N : ℝ) + 1) ^ 2 := by positivity
      rw [div_le_iff₀ hpos]
      nlinarith
    have hL1 : 1 ≤ bSerre - aSerre := by
      have h4 : (4 : ℝ) ≤ bSerre - aSerre := le_of_lt cap_gt_one
      linarith
    linarith
  have hmm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmRpos : 0 < (m : ℝ) := by linarith
  have hsqm : 0 < (m : ℝ) ^ 2 := by positivity
  have hm2 : 1 ≤ (m : ℝ) ^ 2 := by
    simpa using (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hmm1 2)
  have hδ0 : 0 ≤ δ := le_of_lt hδpos
  have hrpos : 0 < r := by
    dsimp [r]
    exact div_pos hδpos (mul_pos (by norm_num) (sq_pos_of_ne_zero (ne_of_gt hmRpos)))
  have hδr : r = (16 * (m : ℝ) ^ 2 * s ^ 2)⁻¹ := by
    dsimp [r, δ]
    field_simp [ne_of_gt hs_pos, ne_of_gt hmRpos]
  have hnear' : ‖(x₀ : ℂ) - α‖ < r := by
    rw [hδr]
    simpa [s] using hnear
  have h4r : 4 * r ≤ δ / 4 := by
    dsimp [r]
    field_simp [ne_of_gt hsqm]
    nlinarith [hδ0, hm2]
  have hr_inv : r⁻¹ = 16 * (m : ℝ) ^ 2 * s ^ 2 := by
    dsimp [r, δ]
    field_simp [ne_of_gt hs_pos, ne_of_gt hmRpos]
  have hQdeg : Q.natDegree ≤ m := q_natDegree_le hm hdegP hfac
  -- interval and flank
  rcases interval_around hδpos hδle hx₀ with ⟨u, v, hu, huv, hv, hx0I, hδ2, hδlen⟩
  rcases flank_good α r δ hrpos hδpos huv hx0I hδ2 h4r hnear' with
    ⟨c, L, hcu, hcLv, hL, hLb, hgood, hmode⟩
  rcases exists_max_norm_eval (P := P) (c := c) (L := L) hL with ⟨z, hzJ, hzmax⟩
  have hzI : z ∈ Set.Icc u v := by
    constructor <;> nlinarith [hcu, hcLv, hzJ.1, hzJ.2]
  have hzS : z ∈ Set.Icc aSerre bSerre := by
    constructor <;> nlinarith [hu, hv, hzI.1, hzI.2]
  have hx0z : |x₀ - z| ≤ δ := by
    rw [abs_le]
    constructor <;> nlinarith [hx0I.1, hx0I.2, hzI.1, hzI.2, hδlen]
  have hxy : |x₀ - z| ≤ 1 / ((N : ℝ) + 1) ^ 2 := by
    simpa [hδeq] using hx0z
  have hwratio := Submission.RemezReal.weight_ratio_le H0 hH0 hU hx₀ hzS hxy
  have hQb : ∀ y : ℝ, y ∈ Set.Icc c (c + L) → ‖Q.eval (y : ℂ)‖ ≤ ‖P.eval (z : ℂ)‖ / r := by
    intro y hy
    have hgy := hgood y hy
    have hyn : ‖(y : ℂ) - α‖ ≠ 0 := by
      have : 0 < ‖(y : ℂ) - α‖ := lt_of_lt_of_le hrpos hgy
      exact ne_of_gt this
    have hPeq : P.eval (y : ℂ) = ((y : ℂ) - α) * Q.eval (y : ℂ) := by rw [hfac]; simp
    have hnormP : ‖P.eval (y : ℂ)‖ = ‖(y : ℂ) - α‖ * ‖Q.eval (y : ℂ)‖ := by rw [hPeq, norm_mul]
    have hQd : ‖Q.eval (y : ℂ)‖ = ‖P.eval (y : ℂ)‖ / ‖(y : ℂ) - α‖ := by
      rw [hnormP]
      field_simp [hyn]
    calc
      ‖Q.eval (y : ℂ)‖ = ‖P.eval (y : ℂ)‖ / ‖(y : ℂ) - α‖ := hQd
      _ ≤ ‖P.eval (y : ℂ)‖ / r := div_le_div_of_nonneg_left (norm_nonneg _) hrpos hgy
      _ ≤ ‖P.eval (z : ℂ)‖ / r := div_le_div_of_nonneg_right (hzmax y hy) (le_of_lt hrpos)
  have hρ0 : 0 ≤ 2 * r := by positivity
  have hρ : 2 * r ≤ (4 : ℝ) * L / (m : ℝ) ^ 2 := by
    dsimp [r]
    field_simp [ne_of_gt hsqm]
    nlinarith [hLb, hδ0, hm2]
  have hM0 : 0 ≤ ‖P.eval (z : ℂ)‖ := norm_nonneg _
  have hB0 : 0 ≤ ‖P.eval (z : ℂ)‖ / r := div_nonneg hM0 (le_of_lt hrpos)
  have hch := cheb_scaled (Cg := Cg) hCg (d := m) (Q := Q) (c := c) (L := L) (ρ := 2 * r)
    (B := ‖P.eval (z : ℂ)‖ / r) hm hL hρ0 hρ hB0 hQdeg hQb
  have hcheb : ‖Q.eval (x₀ : ℂ)‖ ≤ (Cg * (m : ℝ) + 1) * (‖P.eval (z : ℂ)‖ / r) := by
    rcases hmode with hxr | hxl
    · have hh : ‖Q.eval ((x₀ : ℂ))‖ ≤ (Cg * (m : ℝ) + 1) * (‖P.eval (z : ℂ)‖ / r) := by
        rw [hxr]
        simpa using hch.2
      exact hh
    · have hh : ‖Q.eval ((x₀ : ℂ))‖ ≤ (Cg * (m : ℝ) + 1) * (‖P.eval (z : ℂ)‖ / r) := by
        rw [hxl]
        simpa using hch.1
      exact hh
  have hMle : (weight muSerre x₀) ^ N * ‖P.eval (z : ℂ)‖ ≤ Real.exp H0 * cwnorm N P := by
    calc
      (weight muSerre x₀) ^ N * ‖P.eval (z : ℂ)‖
          ≤ ((weight muSerre z) ^ N * Real.exp H0) * ‖P.eval (z : ℂ)‖ := by
            exact mul_le_mul_of_nonneg_right hwratio (norm_nonneg _)
      _ = Real.exp H0 * ((weight muSerre z) ^ N * ‖P.eval (z : ℂ)‖) := by ring
      _ ≤ Real.exp H0 * cwnorm N P := by
            exact mul_le_mul_of_nonneg_left (cwnorm_ge_pointwise N P hzS) (Real.exp_nonneg H0)
  have hfinA : (weight muSerre x₀) ^ N * ‖Q.eval (x₀ : ℂ)‖ ≤
      (Cg * (m : ℝ) + 1) * (Real.exp H0 * cwnorm N P) * r⁻¹ := by
    calc
      (weight muSerre x₀) ^ N * ‖Q.eval (x₀ : ℂ)‖
          ≤ (weight muSerre x₀) ^ N * ((Cg * (m : ℝ) + 1) * (‖P.eval (z : ℂ)‖ / r)) := by
            exact mul_le_mul_of_nonneg_left hcheb (pow_nonneg (le_of_lt (weight_pos muSerre x₀)) N)
      _ = ((Cg * (m : ℝ) + 1) * (‖P.eval (z : ℂ)‖ / r)) * (weight muSerre x₀) ^ N := by ring
      _ = (Cg * (m : ℝ) + 1) * ((weight muSerre x₀) ^ N * ‖P.eval (z : ℂ)‖) * r⁻¹ := by
            field_simp [ne_of_gt hrpos]
      _ ≤ (Cg * (m : ℝ) + 1) * (Real.exp H0 * cwnorm N P) * r⁻¹ := by
            have hCgm : 0 ≤ Cg * (m : ℝ) := mul_nonneg hCg0 (by exact_mod_cast Nat.zero_le m)
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMle (by linarith)) (inv_nonneg.mpr (le_of_lt hrpos))
  have hlin : Cg * (m : ℝ) + 1 ≤ (Cg + 1) * (m : ℝ) := by nlinarith [hmm1]
  have hK : (Cg * (m : ℝ) + 1) * Real.exp H0 * r⁻¹ ≤
      16 * (Cg + 1) * Real.exp H0 * (m : ℝ) ^ 3 * s ^ 2 := by
    rw [hr_inv]
    calc
      (Cg * (m : ℝ) + 1) * Real.exp H0 * (16 * (m : ℝ) ^ 2 * s ^ 2)
          ≤ ((Cg + 1) * (m : ℝ)) * Real.exp H0 * (16 * (m : ℝ) ^ 2 * s ^ 2) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hlin (Real.exp_nonneg H0))
              (by positivity : 0 ≤ 16 * (m : ℝ) ^ 2 * s ^ 2)
      _ = 16 * (Cg + 1) * Real.exp H0 * (m : ℝ) ^ 3 * s ^ 2 := by ring
  calc
    (weight muSerre x₀) ^ N * ‖Q.eval (x₀ : ℂ)‖
        ≤ (Cg * (m : ℝ) + 1) * (Real.exp H0 * cwnorm N P) * r⁻¹ := hfinA
    _ ≤ (16 * (Cg + 1) * Real.exp H0 * (m : ℝ) ^ 3 * s ^ 2) * cwnorm N P := by
      have h : ((Cg * (m : ℝ) + 1) * Real.exp H0 * r⁻¹) * cwnorm N P ≤
          (16 * (Cg + 1) * Real.exp H0 * (m : ℝ) ^ 3 * s ^ 2) * cwnorm N P := by
        exact mul_le_mul_of_nonneg_right hK (cwnorm_nonneg N P)
      have hEq : (Cg * (m : ℝ) + 1) * (Real.exp H0 * cwnorm N P) * r⁻¹ =
          ((Cg * (m : ℝ) + 1) * Real.exp H0 * r⁻¹) * cwnorm N P := by ring
      rwa [hEq]
    _ = (16 * (Cg + 1) * Real.exp H0 * (m : ℝ) ^ 3 * ((N : ℝ) + 1) ^ 2) * cwnorm N P := by
      simp [s]

/-- Weighted division bound (the `(2·max N m)^C` absorption is applied next). -/
lemma cwnorm_div_bound (H0 : ℝ) (hH0 : 0 ≤ H0)
    (hU : ∀ x y : ℝ, x ∈ Set.Icc aSerre bSerre → y ∈ Set.Icc aSerre bSerre →
      |logPotential (serreMeasure gSerre aSerre bSerre) (x : ℂ) -
        logPotential (serreMeasure gSerre aSerre bSerre) (y : ℂ)| ≤ H0 * Real.sqrt |x - y|)
    (Cg : ℝ) (hCg0 : 0 ≤ Cg)
    (hCg : ∀ (d : ℕ), 1 ≤ d → ∀ (c : ℝ) (L : ℝ) (ρ : ℝ),
      0 < L → 0 ≤ ρ → ρ ≤ (4 : ℝ) * L / (d : ℝ) ^ 2 →
      (∀ (Q : Polynomial ℂ), Q.natDegree ≤ d →
        (∀ y : ℝ, y ∈ Set.Icc c (c + L) → ‖Q.eval (y : ℂ)‖ ≤ 1) →
          ‖Q.eval ((c + L + ρ) : ℂ)‖ ≤ Cg * (d : ℝ) + 1) ∧
      (∀ (Q : Polynomial ℂ), Q.natDegree ≤ d →
        (∀ y : ℝ, y ∈ Set.Icc c (c + L) → ‖Q.eval (y : ℂ)‖ ≤ 1) →
          ‖Q.eval ((c - ρ) : ℂ)‖ ≤ Cg * (d : ℝ) + 1))
    {N m : ℕ} (hm : 1 ≤ m) {P Q : Polynomial ℂ} {α : ℂ}
    (hdegP : P.natDegree = m) (hfac : P = (Polynomial.X - Polynomial.C α) * Q) :
    cwnorm N Q ≤ (16 * (Cg + 1) * Real.exp H0 * (m : ℝ) ^ 3 * ((N : ℝ) + 1) ^ 2) * cwnorm N P := by
  exact cwnorm_sSup_le N Q (a := (16 * (Cg + 1) * Real.exp H0 * (m : ℝ) ^ 3 * ((N : ℝ) + 1) ^ 2) * cwnorm N P) (by
    intro x₀ hx₀
    by_cases hnear : ‖(x₀ : ℂ) - α‖ < (16 * (m : ℝ) ^ 2 * (((N : ℝ) + 1) ^ 2))⁻¹
    · exact div_bound_near H0 hH0 hU Cg hCg0 hCg hm hdegP hfac hx₀ hnear
    · exact div_bound_far H0 hH0 Cg hCg0 hm hfac hx₀ (le_of_not_gt hnear))

/-- The polynomial-in-`(N,m)` constant is absorbed by `(2·max N m)^C` with the
exponent `C = 32(Cg+1)+2H+5` (all data-fixed). -/
lemma remez_pow_bound (Cg H0 : ℝ) (hCg0 : 0 ≤ Cg) (hH0 : 0 ≤ H0) (N m : ℕ) (hm : 1 ≤ m) :
    (16 * (Cg + 1) * Real.exp H0 * (m : ℝ) ^ 3 * ((N : ℝ) + 1) ^ 2) ≤
      ((2 * max N m : ℕ) : ℝ) ^ (32 * (Cg + 1) + 2 * H0 + 5) := by
  let T : ℕ := max N m
  let t : ℝ := (T : ℝ)
  have hTm : m ≤ T := by dsimp [T]; exact Nat.le_max_right N m
  have hT1n : 1 ≤ T := le_trans hm hTm
  have hT1 : (1 : ℝ) ≤ t := by
    dsimp [t]
    exact_mod_cast hT1n
  have hb : (2 : ℝ) ≤ 2 * t := by nlinarith
  have hb_pos : 0 < 2 * t := by positivity
  have hb0 : 0 ≤ 2 * t := le_of_lt hb_pos
  have hb4 : (4 : ℝ) ≤ (2 * t) ^ 2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hb 2
    norm_num at h
    exact h
  have hN2n : N + 1 ≤ 2 * T := by
    by_cases hN0 : N = 0
    · subst N
      omega
    · have hN1 : 1 ≤ N := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hN0)
      omega
  have hN2 : (N : ℝ) + 1 ≤ 2 * t := by
    have hc : ((N + 1 : ℕ) : ℝ) ≤ ((2 * T : ℕ) : ℝ) := by exact_mod_cast hN2n
    simpa [t] using hc
  have hE1 : Real.exp 1 ≤ (4 : ℝ) := by
    exact le_of_lt (lt_trans Real.exp_one_lt_three (by norm_num))
  let A : ℝ := 16 * (Cg + 1)
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (by norm_num) (by linarith)
  have hAe : A ≤ Real.exp A := by
    calc
      A ≤ A + 1 := by linarith
      _ ≤ Real.exp A := Real.add_one_le_exp A
  have hA2 : A ≤ (2 * t) ^ (2 * A) := by
    calc
      A ≤ Real.exp A := hAe
      _ = (Real.exp 1) ^ A := by
        rw [Real.rpow_def_of_pos (Real.exp_pos 1) A, Real.log_exp, one_mul]
      _ ≤ 4 ^ A := by
        exact Real.rpow_le_rpow (Real.exp_nonneg 1) hE1 hA0
      _ ≤ ((2 * t) ^ 2) ^ A := by
        exact Real.rpow_le_rpow (by norm_num) hb4 hA0
      _ = (2 * t) ^ (2 * A) := by
        rw [← Real.rpow_natCast (2 * t) 2]
        exact (Real.rpow_mul hb0 (2 : ℝ) A).symm
  have heH : Real.exp H0 ≤ (2 * t) ^ (2 * H0) := by
    calc
      Real.exp H0 = (Real.exp 1) ^ H0 := by
        rw [Real.rpow_def_of_pos (Real.exp_pos 1) H0, Real.log_exp, one_mul]
      _ ≤ 4 ^ H0 := by
        exact Real.rpow_le_rpow (Real.exp_nonneg 1) hE1 hH0
      _ ≤ ((2 * t) ^ 2) ^ H0 := by
        exact Real.rpow_le_rpow (by norm_num) hb4 hH0
      _ = (2 * t) ^ (2 * H0) := by
        rw [← Real.rpow_natCast (2 * t) 2]
        exact (Real.rpow_mul hb0 (2 : ℝ) H0).symm
  have hrpow0 : ∀ z : ℝ, 0 ≤ (2 * t) ^ z := fun z => le_of_lt (Real.rpow_pos_of_pos hb_pos z)
  have hm3 : (m : ℝ) ^ 3 ≤ (2 * t) ^ ((3 : ℕ) : ℝ) := by
    have hmn : (m : ℕ) ≤ 2 * T := by omega
    have hmr : (m : ℝ) ≤ 2 * t := by
      have hc : ((m : ℕ) : ℝ) ≤ ((2 * T : ℕ) : ℝ) := by exact_mod_cast hmn
      simpa [t] using hc
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ (m : ℝ)) hmr 3
    rw [Real.rpow_natCast (2 * t) 3]
    exact h
  have hs2 : ((N : ℝ) + 1) ^ 2 ≤ (2 * t) ^ ((2 : ℕ) : ℝ) := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ (N : ℝ) + 1) hN2 2
    rw [Real.rpow_natCast (2 * t) 2]
    exact h
  have hmul1 : A * Real.exp H0 ≤ (2 * t) ^ (2 * A) * (2 * t) ^ (2 * H0) := by
    exact mul_le_mul hA2 heH (Real.exp_nonneg H0) (hrpow0 (2 * A))
  have h1r : 0 ≤ (2 * t) ^ (2 * A) * (2 * t) ^ (2 * H0) :=
    mul_nonneg (hrpow0 (2 * A)) (hrpow0 (2 * H0))
  have hmul2 : (A * Real.exp H0) * (m : ℝ) ^ 3 ≤
      ((2 * t) ^ (2 * A) * (2 * t) ^ (2 * H0)) * (2 * t) ^ ((3 : ℕ) : ℝ) := by
    exact mul_le_mul hmul1 hm3 (by positivity : 0 ≤ (m : ℝ) ^ 3) h1r
  have h2r : 0 ≤ ((2 * t) ^ (2 * A) * (2 * t) ^ (2 * H0)) * (2 * t) ^ ((3 : ℕ) : ℝ) :=
    mul_nonneg h1r (hrpow0 ((3 : ℕ) : ℝ))
  have hmul3 : ((A * Real.exp H0) * (m : ℝ) ^ 3) * ((N : ℝ) + 1) ^ 2 ≤
      (((2 * t) ^ (2 * A) * (2 * t) ^ (2 * H0)) * (2 * t) ^ ((3 : ℕ) : ℝ)) * (2 * t) ^ ((2 : ℕ) : ℝ) := by
    exact mul_le_mul hmul2 hs2 (by positivity : 0 ≤ ((N : ℝ) + 1) ^ 2) h2r
  have hprod : (((2 * t) ^ (2 * A) * (2 * t) ^ (2 * H0)) * (2 * t) ^ ((3 : ℕ) : ℝ)) * (2 * t) ^ ((2 : ℕ) : ℝ) =
      (2 * t) ^ (2 * A + 2 * H0 + 5) := by
    rw [← Real.rpow_add hb_pos (2 * A) (2 * H0)]
    rw [← Real.rpow_add hb_pos (2 * A + 2 * H0) ((3 : ℕ) : ℝ)]
    rw [← Real.rpow_add hb_pos (2 * A + 2 * H0 + ((3 : ℕ) : ℝ)) ((2 : ℕ) : ℝ)]
    ring_nf
  have hcast : ((2 * max N m : ℕ) : ℝ) = 2 * t := by
    simp [t, T]
  calc
    (16 * (Cg + 1) * Real.exp H0 * (m : ℝ) ^ 3 * ((N : ℝ) + 1) ^ 2)
        = (A * Real.exp H0) * (m : ℝ) ^ 3 * ((N : ℝ) + 1) ^ 2 := by
          dsimp [A]
    _ ≤ (((2 * t) ^ (2 * A) * (2 * t) ^ (2 * H0)) * (2 * t) ^ ((3 : ℕ) : ℝ)) * (2 * t) ^ ((2 : ℕ) : ℝ) := hmul3
    _ = (2 * t) ^ (2 * A + 2 * H0 + 5) := by rw [hprod]
    _ = (2 * t) ^ (32 * (Cg + 1) + 2 * H0 + 5) := by
      have hexp : 2 * A + 2 * H0 + 5 = 32 * (Cg + 1) + 2 * H0 + 5 := by
        dsimp [A]
        ring
      rw [hexp]
    _ = ((2 * max N m : ℕ) : ℝ) ^ (32 * (Cg + 1) + 2 * H0 + 5) := by rw [hcast]

/-- Weighted Remez division by a complex root (Smith `lem:Remez`, full). -/
theorem complex_remez : ∃ C : ℝ, 0 < C ∧
    ∀ (N m : ℕ), 1 ≤ m → ∀ (P : Polynomial ℂ), P.natDegree = m → ∀ α : ℂ,
      P.eval α = 0 →
        ∃ Q : Polynomial ℂ, P = (Polynomial.X - Polynomial.C α) * Q ∧
          cwnorm N Q ≤ ((2 * max N m : ℕ) : ℝ) ^ C * cwnorm N P := by
  rcases Submission.ChebGrowth.cheb_growth with ⟨Cg, hCgpos, hCgprops⟩
  rcases exists_potential_half_holder with ⟨H0, hH0, hU⟩
  let Cexp : ℝ := 32 * (Cg + 1) + 2 * H0 + 5
  refine ⟨Cexp, ?_, ?_⟩
  · dsimp [Cexp]
    nlinarith [hCgpos, hH0]
  · intro N m hm P hdegP α hPα
    have hdiv : (Polynomial.X - Polynomial.C α) ∣ P :=
      (Polynomial.dvd_iff_isRoot).mpr (by simpa [Polynomial.IsRoot] using hPα)
    rcases hdiv with ⟨Q, hfac⟩
    refine ⟨Q, hfac, ?_⟩
    have hcore := cwnorm_div_bound (N := N) (m := m) H0 hH0 hU Cg (le_of_lt hCgpos) hCgprops hm hdegP hfac
    have hpow := remez_pow_bound Cg H0 (le_of_lt hCgpos) hH0 N m hm
    have hnp : 0 ≤ cwnorm N P := cwnorm_nonneg N P
    calc
      cwnorm N Q ≤ (16 * (Cg + 1) * Real.exp H0 * (m : ℝ) ^ 3 * ((N : ℝ) + 1) ^ 2) * cwnorm N P := hcore
      _ ≤ ((2 * max N m : ℕ) : ℝ) ^ Cexp * cwnorm N P := by
        dsimp [Cexp]
        exact mul_le_mul_of_nonneg_right hpow hnp

end Submission.RemezComplex
