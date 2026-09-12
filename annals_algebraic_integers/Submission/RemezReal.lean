import Submission.Contracts
import Submission.WnormToolkit
import Submission.MarkovInterval
import Submission.SerrePotentialIcc
import Submission.WeightedNorm
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Weighted Remez division by a REAL root (Smith `lem:Remez`, real case)

GOAL (real-polynomial case of Smith, prelim.tex `lem:Remez`, specialised to
`Σ = [aSerre,bSerre]`, `μ = muSerre`):

    ∃ C > 0, ∀ (N m : ℕ), 1 ≤ m → ∀ P : Polynomial ℝ, P.natDegree = m →
      ∀ α : ℝ, α ∈ Icc aSerre bSerre → P.eval α = 0 →
        ∃ Q : Polynomial ℝ, P = (X − C α)·Q ∧
          wnorm N Q ≤ (2·max N m : ℝ)^C · wnorm N P

where `wnorm k R = Contracts.wnorm k R = sSup_{x ∈ [aSerre,bSerre]}
(weight muSerre x)^k · |R.eval x|` (REAL polynomials; see
`Submission/Contracts.lean`, `Submission/WeightedNorm.lean`).  This is the
real-root instance needed by `prop:Hilbert` (dividing `P_{n+1,μ}` by its real
quantile roots `α_k`), `lem:P_ver1`-style steps, etc.  (A complex-root
version is needed elsewhere but NOT here.)

## Ingredients already verified (use them)
* `Submission/MarkovInterval.lean` (ns MarkovInterval): real-polynomial
  Markov bound on `[aSerre,bSerre]` (and on general intervals via the
  `chebPoint`/`unitCoord` affine charts) — e.g. `markov_interval`:
  `|P'.eval x| ≤ (2·(natDegree P)²/(bSerre−aSerre))·M` if `|P| ≤ M` on the
  interval; apply the SAME statement to any subinterval of length ℓ (via an
  affine reparametrisation, or reprove the needed "Markov on a subinterval
  of length ℓ" with the same constant `2·m²/ℓ` by rescaling — you may add
  such a helper here).
* `Submission/SerrePotentialIcc.lean`:
  `potential_lipschitz_on_Icc`, `exists_potential_half_holder`
  (`∃ H > 0, ∀ x y ∈ Icc aSerre bSerre, |U(x) − U(y)| ≤ H·√|x−y|` where
  `U(x) = logPotential muSerre (x : ℂ)`); `weight_serre_on_Icc`
  (`weight muSerre x = Real.exp (logPotential muSerre (x:ℂ))`).
* `Submission/WnormToolkit.lean` (ns WnormToolkit): `wnorm_ge_pointwise`
  (pointwise values ≤ the sup), `wnorm_nonneg`, etc.
* `Submission/DivLinear.lean` (ns DivLinear): the UNWEIGHTED division bound
  `supNorm Q ≤ (16·m²/(bSerre−aSerre))·supNorm P` (its proof is the model for
  the escape step below) plus `supNorm`-API (`supNorm_le_iff`,
  `abs_eval_le_supNorm`).  Read it to imitate the structure.

## Proof plan (Smith's proof of `lem:Remez`, η = 1/2; constants absorbed)
Fix `N m ≥ 1`, `P` deg `m`, real root `α ∈ [aSerre,bSerre]`, and let
`Q := P / (X − C α)` (exists by the factor theorem since `P.eval α = 0`:
use `Polynomial.dvd_iff_isRoot`-style or Mathlib's division; alternatively
state the goal as `∃ Q, P = (X−C α)·Q ∧ …` and obtain the factorization from
`P.eval α = 0` via `Polynomial.X_sub_C_dvd`/`dvd_iff_isRoot`).
1. Hölder scale.  Put `δ₀ := (N+1)⁻² · min 1 ((bSerre−aSerre)/1)` — simpler:
   `δ₀ := (N+1)⁻²` (for all N ≥ 0, δ₀ ≤ 1 < bSerre−aSerre =: L, so any
   subinterval of Σ of length ≤ δ₀·(small) fits with margin arguments; but be
   careful near the endpoints — see step 3).  From
   `exists_potential_half_holder`: for `x,y ∈ [aSerre,bSerre]` with
   `|x−y| ≤ δ₀` we get `N·|U(x)−U(y)| ≤ N·H·√δ₀ ≤ H` (since
   `√((N+1)⁻²) = (N+1)⁻¹`), so `e^{N·(U(x)−U(y))} ≤ e^H` — a CONSTANT
   (absorb it: `C` may depend on the fixed data, so `e^H` and other fixed
   constants are fine; make them all part of the final polynomial bound).
2. Escape radius.  `r := m⁻²·δ₀/8` (a tiny radius; if m = 1 handle directly
   or note r formula still works).  `Σ₀ := Σ ∩ [α−r, α+r]` (a real
   interval).  Claim (escape): `sup_{x ∈ Σ₀} |Q.eval x| ≤ sup_{x ∈ Σ∖Σ₀} |Q.eval x|`.
   Proof: let `x₀ ∈ Σ₀`; choose an interval `I ⊆ Σ` of length `ℓ ≥ δ₀/2`
   containing `x₀` (see step 3; for points within `δ₀` of an endpoint take
   the half-interval of length `δ₀/2` from the endpoint — the estimates use
   only `ℓ ≥ δ₀/2`).  Since `Q(α) = 0` and `|x₀−α| ≤ r`:
   `|Q.eval x₀| = |Q.eval x₀ − Q.eval α| ≤ |x₀−α|·(sup on [x₀,α] of |Q'|)
   ≤ r·(2·m²/ℓ)·(max on I of |Q|)` (Markov on I, `deg Q ≤ m−1`, exponent
   `2·m²/ℓ` safe) `≤ (m⁻²δ₀/8)·(2m²·2/δ₀)·max_I|Q| = (1/2)·max_I|Q|`.
   Hence `max_{Σ₀}|Q| ≤ (1/2)·max(max_{Σ₀}, max_{Σ∖Σ₀})`, giving
   `max_{Σ₀}|Q| ≤ max_{Σ∖Σ₀}|Q|`.  (Formalise carefully with `csSup` or
   with sup over finite-ish approximations — imitate DivLinear's argument
   structure, which already does this walk-to-the-boundary dance.)
3. (Interval existence) For every `x₀ ∈ [aSerre,bSerre]` there is a closed
   interval `I ⊆ [aSerre,bSerre]` with `x₀ ∈ I`, `δ₀/2 ≤ length I ≤ δ₀`
   (mid-interval: `[x₀−δ₀/2, x₀+δ₀/2]`; near the left end take
   `[aSerre, aSerre+δ₀/2]`; near the right end similarly — handle by cases).
   All Markov/potential estimates use such an `I`.
4. Weighted escape & division bound.
   (a) For `x₀ ∈ Σ₀` with its interval `I`: by (2) `|Q.eval x₀| ≤ max_{I∖Σ₀}|Q|`,
   and for the `y ∈ I∖Σ₀` attaining it, `|x₀−y| ≤ δ₀`, so
   `w(x₀)^N |Q(x₀)| ≤ e^H · w(y)^N |Q(y)| ≤ e^H · (sup over Σ∖Σ₀ of w^N|Q|)`
   (w = weight, using (1) and `w = e^U`).  Therefore
   `‖Q‖_N ≤ e^H · sup_{x ∈ Σ∖Σ₀} (w(x)^N · |Q.eval x|)`.
   (b) On `Σ∖Σ₀`, `|x − α| ≥ r`, so `w(x)^N|Q(x)| = w(x)^N·|P(x)|/|x−α| ≤
   r⁻¹·w(x)^N|P(x)| ≤ r⁻¹·‖P‖_N`.
   (c) `r⁻¹ = 8·m²·δ₀⁻¹ = 8·m²·(N+1)² ≤ (2·max N m)^{C₀}` for an absolute
   `C₀` (e.g. `C₀ = 8` suffices: `8m²(N+1)² ≤ (2·max(N,m))^8`? check:
   `N+1 ≤ 2N` for N ≥ 1, but N may be 0 — handle N=0 separately or absorb
   `N+1 ≤ 2·max N m` for m ≥ 1).  Also `e^H` and the `(m+1)!`-style
   constants are FIXED (only depend on the data) — multiply them into the
   final `(2·max N m)^C`.
   (d) Conclude `wnorm N Q ≤ (2·max N m : ℝ)^C · wnorm N P` with a fixed
   `C > 0` (any explicit value; the theorem only needs existence).  For N=0
   the same argument works (δ₀ = 1; then the potential factor is trivial and
   `r⁻¹ = 8m²`).

Everything must be free of holes at the end with axioms only
propext/Quot.sound/Classical.choice.  Read `Submission/DivLinear.lean`
(the escape structure), `Submission/MarkovInterval.lean`,
`Submission/SerrePotentialIcc.lean`, `Submission/WnormToolkit.lean`,
`Submission/Contracts.lean` for exact names.  Keep the declaration below
EXACTLY as written.  You may add any helper lemmas in this file (namespace
`Submission.RemezReal`).
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators
open Polynomial

namespace Submission.RemezReal

open Submission.Contracts
open Submission.Serre
open Submission.SerreExample
open Submission.WeightedNorm
open Submission.PotentialDefs

/-! ## Helper lemmas (added by the RemezReal agent) -/

/-- `sqrt (1/s²) = 1/s` for `s > 0`. -/
lemma sqrt_one_div_sq (s : ℝ) (hs : 0 < s) : Real.sqrt (1 / s ^ 2) = 1 / s := by
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1) (s ^ 2)]
  rw [Real.sqrt_one]
  rw [Real.sqrt_sq (le_of_lt hs)]

/-- The affine polynomial mapping `[−1,1]` onto `[u,v]`. -/
private def midAff (u v : ℝ) : Polynomial ℝ :=
  Polynomial.C ((u + v) / 2) + Polynomial.C ((v - u) / 2) * Polynomial.X

private lemma midAff_eval (u v t : ℝ) : (midAff u v).eval t = (u + v) / 2 + (v - u) / 2 * t := by
  simp [midAff]

private lemma midAff_natDegree_le_one (u v : ℝ) : (midAff u v).natDegree ≤ 1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [midAff, coeff_add, coeff_C, coeff_C_mul_X]
  have hN0 : N ≠ 0 := by omega
  have hN1 : N ≠ 1 := by omega
  simp [hN0, hN1]

private lemma midAff_mem_Icc {u v : ℝ} (huv : u < v) {t : ℝ} (ht : t ∈ Set.Icc (-1) 1) :
    (midAff u v).eval t ∈ Set.Icc u v := by
  have hpos : 0 < (v - u) / 2 := by positivity
  have hnonneg : 0 ≤ (v - u) / 2 := le_of_lt hpos
  have hm1 : (v - u) / 2 * (-1 : ℝ) ≤ (v - u) / 2 * t :=
    mul_le_mul_of_nonneg_left ht.1 hnonneg
  have hm2 : (v - u) / 2 * t ≤ (v - u) / 2 * (1 : ℝ) :=
    mul_le_mul_of_nonneg_left ht.2 hnonneg
  rw [midAff_eval]
  constructor <;> nlinarith

private lemma midAff_derivative (u v : ℝ) : (midAff u v).derivative = Polynomial.C ((v - u) / 2) := by
  simp [midAff]

/-- The coordinate `t ∈ [−1,1]` of `x ∈ [u,v]`. -/
private def midCoord (u v x : ℝ) : ℝ := (2 * x - u - v) / (v - u)

private lemma midCoord_mem_Icc {u v : ℝ} (huv : u < v) {x : ℝ} (hx : x ∈ Set.Icc u v) :
    midCoord u v x ∈ Set.Icc (-1) 1 := by
  have hpos : 0 < v - u := by linarith
  constructor
  · show (-1 : ℝ) ≤ (2 * x - u - v) / (v - u)
    rw [le_div_iff₀ hpos]
    nlinarith [hx.1]
  · show (2 * x - u - v) / (v - u) ≤ 1
    rw [div_le_iff₀ hpos]
    nlinarith [hx.2]

private lemma midAff_midCoord {u v : ℝ} (huv : u < v) {x : ℝ} (hx : x ∈ Set.Icc u v) :
    (midAff u v).eval (midCoord u v x) = x := by
  have hne : v - u ≠ 0 := by linarith
  rw [midAff_eval]
  unfold midCoord
  field_simp [hne]
  ring

/-- Markov's inequality on an arbitrary interval `[u,v]` of length `v-u`:
`deg P ≤ m` and `|P| ≤ M` on `[u,v]` imply `|P'.eval x| ≤ (2m²/(v-u))·M` there. -/
lemma markov_subinterval {P : Polynomial ℝ} {m : ℕ} (hdeg : P.natDegree ≤ m)
    {u v : ℝ} (huv : u < v) {M : ℝ} (hM : 0 ≤ M)
    (hbd : ∀ x : ℝ, x ∈ Set.Icc u v → |P.eval x| ≤ M)
    (x : ℝ) (hx : x ∈ Set.Icc u v) :
    |P.derivative.eval x| ≤ (2 * (m : ℝ) ^ 2 / (v - u)) * M := by
  let R : Polynomial ℝ := P.comp (midAff u v)
  let t : ℝ := midCoord u v x
  have hbpos : 0 < v - u := by linarith
  have hApos : 0 < (v - u) / 2 := by positivity
  have hbne : v - u ≠ 0 := ne_of_gt hbpos
  -- degree of R ≤ m
  have hdegR : R.natDegree ≤ m := by
    dsimp [R]
    calc
      (P.comp (midAff u v)).natDegree ≤ P.natDegree * (midAff u v).natDegree := natDegree_comp_le
      _ ≤ m * 1 := by exact Nat.mul_le_mul hdeg (midAff_natDegree_le_one u v)
      _ = m := by rw [mul_one]
  -- |R| ≤ M on [−1,1]
  have hbdR : ∀ t' : ℝ, t' ∈ Set.Icc (-1) 1 → |R.eval t'| ≤ M := by
    intro t' ht'
    dsimp [R]
    rw [eval_comp]
    exact hbd ((midAff u v).eval t') (midAff_mem_Icc huv ht')
  have ht : t ∈ Set.Icc (-1) 1 := by
    dsimp [t]
    exact midCoord_mem_Icc huv hx
  have hxeq : (midAff u v).eval t = x := by
    dsimp [t]
    exact midAff_midCoord huv hx
  have hmain := Submission.Markov.markov_unit hdegR hM hbdR t ht
  -- chain rule
  have hder : R.derivative.eval t = ((v - u) / 2) * P.derivative.eval x := by
    dsimp [R]
    rw [derivative_comp, eval_mul]
    rw [midAff_derivative]
    simp [eval_comp, hxeq]
  have hder_abs : ((v - u) / 2) * |P.derivative.eval x| ≤ (m : ℝ) ^ 2 * M := by
    have h := hmain
    rw [hder] at h
    rwa [abs_mul, abs_of_pos hApos] at h
  have hq0 : |P.derivative.eval x| ≤ (m : ℝ) ^ 2 * M / ((v - u) / 2) := by
    have h' : |P.derivative.eval x| * ((v - u) / 2) ≤ (m : ℝ) ^ 2 * M := by
      simpa [mul_comm] using hder_abs
    exact (le_div_iff₀ hApos).mpr h'
  calc
    |P.derivative.eval x| ≤ (m : ℝ) ^ 2 * M / ((v - u) / 2) := hq0
    _ = (2 * (m : ℝ) ^ 2 / (v - u)) * M := by
      field_simp [hbne]


/-- Consequence of Markov on `[u,v]`: `P` is `(2m²/(v-u))·M`-Lipschitz on `[u,v]`. -/
lemma eval_lipschitz_on {P : Polynomial ℝ} {m : ℕ} (hdeg : P.natDegree ≤ m)
    {u v : ℝ} (huv : u < v) {M : ℝ} (hM : 0 ≤ M)
    (hbd : ∀ x : ℝ, x ∈ Set.Icc u v → |P.eval x| ≤ M)
    {x y : ℝ} (hx : x ∈ Set.Icc u v) (hy : y ∈ Set.Icc u v) :
    |P.eval x - P.eval y| ≤ (2 * (m : ℝ) ^ 2 / (v - u)) * M * |x - y| := by
  let f : ℝ → ℝ := fun t => P.eval t
  let C : ℝ := (2 * (m : ℝ) ^ 2 / (v - u)) * M
  have hdiff : ∀ t : ℝ, t ∈ Set.Icc u v → DifferentiableAt ℝ f t := by
    intro t ht
    dsimp [f]
    exact (Polynomial.hasDerivAt P t).differentiableAt
  have hbound : ∀ t : ℝ, t ∈ Set.Icc u v → ‖deriv f t‖ ≤ C := by
    intro t ht
    dsimp [f, C]
    have hM' := markov_subinterval (P := P) (m := m) hdeg huv hM hbd t ht
    rw [Polynomial.deriv]
    simpa [Real.norm_eq_abs] using hM'
  have hmain := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (G := ℝ) (f := f)
    (s := Set.Icc u v) (x := x) (y := y) (C := C) hdiff hbound (convex_Icc u v) hx hy
  dsimp [f, C] at hmain
  simpa [Real.norm_eq_abs, abs_sub_comm] using hmain

/-- A small interval of length `δ` inside `[aSerre,bSerre]` containing both
`x` and `α`, whenever `|x-α| ≤ δ/8` and `δ ≤ bSerre-aSerre`. -/
lemma near_interval {x α : ℝ} (δ : ℝ) (hδpos : 0 < δ) (hδle : δ ≤ bSerre - aSerre)
    (hα : α ∈ Set.Icc aSerre bSerre) (hx : x ∈ Set.Icc aSerre bSerre)
    (hxa : |x - α| ≤ δ / 8) :
    ∃ u v : ℝ, aSerre ≤ u ∧ v ≤ bSerre ∧ u < v ∧ v - u = δ ∧
      u ≤ α ∧ α ≤ v ∧ u ≤ x ∧ x ≤ v := by
  have hxa' := abs_le.mp hxa
  have hxaL : α - δ / 8 ≤ x := by linarith
  have hxaR : x ≤ α + δ / 8 := by linarith
  have hd2le : δ / 2 ≤ δ := by linarith
  have hd58 : δ / 2 + δ / 8 ≤ δ := by linarith
  have hd28 : δ / 8 ≤ δ / 2 := by linarith
  by_cases h1 : α ≤ aSerre + δ / 2
  · refine ⟨aSerre, aSerre + δ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact le_rfl
    · linarith
    · linarith
    · ring
    · exact hα.1
    · linarith
    · exact hx.1
    · linarith
  · have h1' : aSerre + δ / 2 < α := lt_of_not_ge h1
    by_cases h2 : bSerre - δ / 2 ≤ α
    · refine ⟨bSerre - δ, bSerre, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · linarith
      · exact le_rfl
      · linarith
      · ring
      · linarith
      · exact hα.2
      · linarith
      · exact hx.2
    · have h2' : α < bSerre - δ / 2 := lt_of_not_ge h2
      refine ⟨α - δ / 2, α + δ / 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · linarith
      · linarith
      · linarith
      · ring
      · linarith
      · linarith
      · linarith
      · linarith

/-- The absolute value of a polynomial attains its maximum on a compact interval. -/
lemma max_abs_point (P : Polynomial ℝ) {u v : ℝ} (huv : u < v) :
    ∃ z : ℝ, z ∈ Set.Icc u v ∧ ∀ t : ℝ, t ∈ Set.Icc u v → |P.eval t| ≤ |P.eval z| := by
  have hcont : ContinuousOn (fun x : ℝ => |P.eval x|) (Set.Icc u v) := by
    have hc : Continuous (fun x : ℝ => Polynomial.aeval x P) := Polynomial.continuous_aeval (p := P)
    have hh : (fun x : ℝ => Polynomial.aeval x P) = (fun x : ℝ => P.eval x) := by
      funext x
      rw [Polynomial.aeval_def]
      simp
    simpa [hh] using hc.abs.continuousOn
  have hne : (Set.Icc u v : Set ℝ).Nonempty := ⟨u, le_rfl, le_of_lt huv⟩
  rcases isCompact_Icc.exists_isMaxOn hne hcont with ⟨z, hz, hzmax⟩
  refine ⟨z, hz, ?_⟩
  intro t ht
  exact (isMaxOn_iff.mp hzmax) t ht

/-- If `P = (X - C α)·Q` then `Q.eval α = P.derivative.eval α`. -/
lemma q_alpha_eq {P Q : Polynomial ℝ} {α : ℝ}
    (hfac : P = (Polynomial.X - Polynomial.C α) * Q) :
    Q.eval α = P.derivative.eval α := by
  have hder : P.derivative =
      (Polynomial.X - Polynomial.C α).derivative * Q +
        (Polynomial.X - Polynomial.C α) * Q.derivative := by
    rw [hfac, Polynomial.derivative_mul]
  have hval : P.derivative.eval α = Q.eval α := by
    rw [hder, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul,
      Polynomial.derivative_X_sub_C]
    simp
  exact hval.symm

/-- Weighted comparison over small distances: if `|x-y| ≤ (N+1)^{-2}` then
`w(x)^N ≤ e^{H0}·w(y)^N`, where `H0` is the 1/2-Hölder constant of the potential. -/
lemma weight_ratio_le (H0 : ℝ) (hH0 : 0 ≤ H0)
    (hU : ∀ x y : ℝ, x ∈ Set.Icc aSerre bSerre → y ∈ Set.Icc aSerre bSerre →
      |logPotential (serreMeasure gSerre aSerre bSerre) (x : ℂ) -
        logPotential (serreMeasure gSerre aSerre bSerre) (y : ℂ)| ≤ H0 * Real.sqrt |x - y|)
    {N : ℕ} {x y : ℝ} (hx : x ∈ Set.Icc aSerre bSerre) (hy : y ∈ Set.Icc aSerre bSerre)
    (hxy : |x - y| ≤ 1 / ((N : ℝ) + 1) ^ 2) :
    (weight muSerre x) ^ N ≤ (weight muSerre y) ^ N * Real.exp H0 := by
  let U : ℝ → ℝ := fun z => logPotential (serreMeasure gSerre aSerre bSerre) (z : ℂ)
  let s : ℝ := (N : ℝ) + 1
  have hs : 0 < s := by dsimp [s]; positivity
  have hxy' : |x - y| ≤ 1 / s ^ 2 := by simpa [s] using hxy
  have hsqrt : Real.sqrt (1 / s ^ 2) = 1 / s := sqrt_one_div_sq s hs
  have hWx : (weight muSerre x) ^ N = Real.exp ((N : ℝ) * U x) := by
    calc
      (weight muSerre x) ^ N =
          (Real.exp (logPotential (serreMeasure gSerre aSerre bSerre) (x : ℂ))) ^ N := by
            simp [weight, muSerre]
      _ = Real.exp ((N : ℝ) * logPotential (serreMeasure gSerre aSerre bSerre) (x : ℂ)) :=
            (Real.exp_nat_mul (logPotential (serreMeasure gSerre aSerre bSerre) (x : ℂ)) N).symm
      _ = Real.exp ((N : ℝ) * U x) := by rfl
  have hWy : (weight muSerre y) ^ N = Real.exp ((N : ℝ) * U y) := by
    calc
      (weight muSerre y) ^ N =
          (Real.exp (logPotential (serreMeasure gSerre aSerre bSerre) (y : ℂ))) ^ N := by
            simp [weight, muSerre]
      _ = Real.exp ((N : ℝ) * logPotential (serreMeasure gSerre aSerre bSerre) (y : ℂ)) :=
            (Real.exp_nat_mul (logPotential (serreMeasure gSerre aSerre bSerre) (y : ℂ)) N).symm
      _ = Real.exp ((N : ℝ) * U y) := by rfl
  have hN0 : 0 ≤ (N : ℝ) := by positivity
  -- (N)·(U x − U y) ≤ H0
  have hUdiff : (N : ℝ) * (U x - U y) ≤ H0 := by
    have h1 : U x - U y ≤ |U x - U y| := le_abs_self (U x - U y)
    have h2 : (N : ℝ) * (U x - U y) ≤ (N : ℝ) * |U x - U y| :=
      mul_le_mul_of_nonneg_left h1 hN0
    have h3 : (N : ℝ) * |U x - U y| ≤ (N : ℝ) * (H0 * Real.sqrt |x - y|) := by
      exact mul_le_mul_of_nonneg_left (hU x y hx hy) hN0
    have hsq : Real.sqrt |x - y| ≤ 1 / s := by
      have h := Real.sqrt_le_sqrt hxy'
      rw [sqrt_one_div_sq s hs] at h
      exact h
    have h4 : (N : ℝ) * (H0 * Real.sqrt |x - y|) ≤ (N : ℝ) * (H0 * (1 / s)) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq hH0) hN0
    have h5 : (N : ℝ) * (H0 * (1 / s)) ≤ H0 := by
      have hNle : (N : ℝ) / s ≤ 1 := by
        dsimp [s]
        rw [div_le_iff₀ hs]
        linarith
      calc
        (N : ℝ) * (H0 * (1 / s)) = H0 * ((N : ℝ) * (1 / s)) := by ring
        _ = H0 * ((N : ℝ) / s) := by ring
        _ ≤ H0 * 1 := by
          exact mul_le_mul_of_nonneg_left hNle hH0
        _ = H0 := by ring
    exact le_trans (le_trans (le_trans h2 h3) h4) h5
  calc
    (weight muSerre x) ^ N = Real.exp ((N : ℝ) * U x) := hWx
    _ ≤ Real.exp ((N : ℝ) * U y + H0) := by
      apply Real.exp_le_exp.mpr
      have hlin : (N : ℝ) * U x ≤ (N : ℝ) * U y + H0 := by
        have hh : (N : ℝ) * (U x - U y) = (N : ℝ) * U x - (N : ℝ) * U y := by ring
        nlinarith
      exact hlin
    _ = Real.exp ((N : ℝ) * U y) * Real.exp H0 := by rw [Real.exp_add]
    _ = (weight muSerre y) ^ N * Real.exp H0 := by rw [hWy]

/-- The division bound with explicit (still polynomial-in-`(N,m)`) constant. -/
lemma wnorm_div_bound (H0 : ℝ) (hH0 : 0 ≤ H0)
    (hU : ∀ x y : ℝ, x ∈ Set.Icc aSerre bSerre → y ∈ Set.Icc aSerre bSerre →
      |logPotential (serreMeasure gSerre aSerre bSerre) (x : ℂ) -
        logPotential (serreMeasure gSerre aSerre bSerre) (y : ℂ)| ≤ H0 * Real.sqrt |x - y|)
    {N m : ℕ} (hm : 1 ≤ m) {P Q : Polynomial ℝ} {α : ℝ}
    (hdegP : P.natDegree = m) (hα : α ∈ Set.Icc aSerre bSerre) (hPα : P.eval α = 0)
    (hfac : P = (Polynomial.X - Polynomial.C α) * Q) :
    wnorm N Q ≤ (8 * Real.exp H0 * (m : ℝ) ^ 2 * ((N : ℝ) + 1) ^ 2) * wnorm N P := by
  have hdegPle : P.natDegree ≤ m := le_of_eq hdegP
  let s : ℝ := (N : ℝ) + 1
  have hs : 0 < s := by dsimp [s]; linarith
  have hs_ne : s ≠ 0 := ne_of_gt hs
  have hsq_pos : 0 < s ^ 2 := sq_pos_of_pos hs
  let δ : ℝ := 1 / s ^ 2
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact one_div_pos.mpr hsq_pos
  have hδle : δ ≤ bSerre - aSerre := by
    have hδ1 : δ ≤ 1 := by
      dsimp [δ]
      have hs1 : 1 ≤ s := by dsimp [s]; linarith
      have hsq : 1 ≤ s ^ 2 := by
        have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hs1 2
        simpa using h
      rw [div_le_iff₀ hsq_pos]
      simpa using hsq
    have hL1 : 1 ≤ bSerre - aSerre := by
      have h4 : (4 : ℝ) ≤ bSerre - aSerre := le_of_lt cap_gt_one
      linarith
    linarith
  have hδinv : δ⁻¹ = s ^ 2 := by
    dsimp [δ]
    rw [inv_div]
    ring
  let r : ℝ := δ / (8 * (m : ℝ) ^ 2)
  have hmR : (0 : ℝ) < (m : ℝ) := by
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hrpos : 0 < r := by
    dsimp [r]
    exact div_pos hδpos (mul_pos (by norm_num) (sq_pos_of_pos hmR))
  have hrle : r ≤ δ / 8 := by
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hm2 : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by
      have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hm1 2
      simpa using h
    have h8 : (8 : ℝ) ≤ 8 * (m : ℝ) ^ 2 := by nlinarith
    have hinv : (8 * (m : ℝ) ^ 2)⁻¹ ≤ (8 : ℝ)⁻¹ := by
      exact (inv_le_inv₀ (by positivity : 0 < 8 * (m : ℝ) ^ 2) (by norm_num)).mpr h8
    dsimp [r]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hinv (le_of_lt hδpos)
  let eH : ℝ := Real.exp H0
  have heH0 : 0 ≤ eH := by
    dsimp [eH]
    exact Real.exp_nonneg H0
  have heH1 : 1 ≤ eH := by
    dsimp [eH]
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr hH0
  let B : ℝ := 8 * eH * (m : ℝ) ^ 2 * s ^ 2
  have hB0 : 0 ≤ B := by
    dsimp [B]
    positivity
  have hcoefN : (2 * (m : ℝ) ^ 2 / δ) * eH ≤ B := by
    have h1 : (2 * (m : ℝ) ^ 2 / δ) * eH = 2 * (m : ℝ) ^ 2 * s ^ 2 * eH := by
      rw [div_eq_mul_inv, hδinv]
    rw [h1]
    dsimp [B]
    have hx : 0 ≤ (m : ℝ) ^ 2 * (s ^ 2 * eH) := by
      exact mul_nonneg (sq_nonneg (m : ℝ)) (mul_nonneg (sq_nonneg s) heH0)
    calc
      2 * (m : ℝ) ^ 2 * s ^ 2 * eH = 2 * ((m : ℝ) ^ 2 * (s ^ 2 * eH)) := by ring
      _ ≤ 8 * ((m : ℝ) ^ 2 * (s ^ 2 * eH)) := by
            exact mul_le_mul_of_nonneg_right (by norm_num : (2 : ℝ) ≤ 8) hx
      _ = 8 * eH * (m : ℝ) ^ 2 * s ^ 2 := by ring
  have h1r : 1 / r = 8 * (m : ℝ) ^ 2 * s ^ 2 := by
    dsimp [r]
    have h8ne : (8 * (m : ℝ) ^ 2) ≠ 0 := by
      exact ne_of_gt (mul_pos (by norm_num) (sq_pos_of_pos hmR))
    calc
      1 / (δ / (8 * (m : ℝ) ^ 2)) = (8 * (m : ℝ) ^ 2) / δ := by
        field_simp [hδpos.ne', h8ne]
      _ = (8 * (m : ℝ) ^ 2) * δ⁻¹ := by rw [div_eq_mul_inv]
      _ = 8 * (m : ℝ) ^ 2 * s ^ 2 := by rw [hδinv]
  have hcoefF : 1 / r ≤ B := by
    rw [h1r]
    dsimp [B]
    calc
      8 * (m : ℝ) ^ 2 * s ^ 2 = (8 * (m : ℝ) ^ 2 * s ^ 2) * 1 := by ring
      _ ≤ (8 * (m : ℝ) ^ 2 * s ^ 2) * eH := by
            exact mul_le_mul_of_nonneg_left heH1 (by positivity : 0 ≤ 8 * (m : ℝ) ^ 2 * s ^ 2)
      _ = 8 * eH * (m : ℝ) ^ 2 * s ^ 2 := by ring
  have hPx_mul : ∀ x : ℝ, P.eval x = (x - α) * Q.eval x := by
    intro x
    rw [hfac, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  have hQ_abs : ∀ {x : ℝ}, x ≠ α → |Q.eval x| ≤ |P.eval x| / |x - α| := by
    intro x hxα0
    have hxane_pos : 0 < |x - α| := abs_pos.mpr (sub_ne_zero.mpr hxα0)
    rw [le_div_iff₀ hxane_pos]
    rw [hPx_mul x, abs_mul]
    rw [mul_comm]
  have htail : ∀ x z : ℝ, x ∈ Set.Icc aSerre bSerre → z ∈ Set.Icc aSerre bSerre →
      |x - z| ≤ δ →
      |Q.eval x| ≤ (2 * (m : ℝ) ^ 2 / δ) * |P.eval z| →
      (weight muSerre x) ^ N * |Q.eval x| ≤ B * wnorm N P := by
    intro x z hx hz hxz hQb
    have hxz' : |x - z| ≤ 1 / ((N : ℝ) + 1) ^ 2 := by
      simpa [δ, s] using hxz
    have hw : (weight muSerre x) ^ N ≤ (weight muSerre z) ^ N * Real.exp H0 :=
      weight_ratio_le H0 hH0 hU hx hz hxz'
    have hznorm : (weight muSerre z) ^ N * |P.eval z| ≤ wnorm N P :=
      Submission.WnormToolkit.wnorm_ge_pointwise N P hz
    have hcoef0' : 0 ≤ 2 * (m : ℝ) ^ 2 / δ := by
      exact div_nonneg (mul_nonneg (by norm_num : 0 ≤ (2 : ℝ)) (sq_nonneg (m : ℝ)))
        (le_of_lt hδpos)
    have hcoef0 : 0 ≤ (2 * (m : ℝ) ^ 2 / δ) * eH := by
      exact mul_nonneg hcoef0' heH0
    calc
      (weight muSerre x) ^ N * |Q.eval x|
          ≤ (weight muSerre x) ^ N * ((2 * (m : ℝ) ^ 2 / δ) * |P.eval z|) := by
            exact mul_le_mul_of_nonneg_left hQb
              (pow_nonneg (le_of_lt (weight_pos muSerre x)) N)
      _ = (2 * (m : ℝ) ^ 2 / δ) * ((weight muSerre x) ^ N * |P.eval z|) := by ring
      _ ≤ (2 * (m : ℝ) ^ 2 / δ) * ((weight muSerre z) ^ N * Real.exp H0 * |P.eval z|) := by
            have h1 : (weight muSerre x) ^ N * |P.eval z| ≤
                (weight muSerre z) ^ N * Real.exp H0 * |P.eval z| := by
              exact mul_le_mul_of_nonneg_right hw (abs_nonneg (P.eval z))
            exact mul_le_mul_of_nonneg_left h1 hcoef0'
      _ = ((2 * (m : ℝ) ^ 2 / δ) * eH) * ((weight muSerre z) ^ N * |P.eval z|) := by
            dsimp [eH]
            ring
      _ ≤ ((2 * (m : ℝ) ^ 2 / δ) * eH) * wnorm N P := by
            exact mul_le_mul_of_nonneg_left hznorm hcoef0
      _ = ((2 * (m : ℝ) ^ 2 / δ) * Real.exp H0) * wnorm N P := by
            dsimp [eH]
      _ ≤ B * wnorm N P := by
            dsimp [B, eH]
            exact mul_le_mul_of_nonneg_right hcoefN (Submission.WnormToolkit.wnorm_nonneg N P)
  have hpoint : ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre →
      (weight muSerre x) ^ N * |Q.eval x| ≤ B * wnorm N P := by
    intro x hx
    by_cases hxα : x = α
    · subst x
      have hzz : |α - α| ≤ δ / 8 := by
        rw [sub_self, abs_zero]
        positivity
      rcases near_interval δ hδpos hδle hα hα hzz with ⟨u, v, hu_lo, hv_hi, huv, hlen, hαu, hαv, _h1, _h2⟩
      rcases max_abs_point P huv with ⟨z, hzIJ, hzmax⟩
      have hzIcc : z ∈ Set.Icc aSerre bSerre := by
        constructor
        · linarith [hu_lo, hzIJ.1]
        · linarith [hv_hi, hzIJ.2]
      have hM0 : 0 ≤ |P.eval z| := abs_nonneg _
      have hbdM : ∀ t : ℝ, t ∈ Set.Icc u v → |P.eval t| ≤ |P.eval z| := by
        intro t ht
        exact hzmax t ht
      have hQαb : |Q.eval α| ≤ (2 * (m : ℝ) ^ 2 / δ) * |P.eval z| := by
        have hC1 : |P.derivative.eval α| ≤ (2 * (m : ℝ) ^ 2 / (v - u)) * |P.eval z| :=
          markov_subinterval (P := P) (m := m) hdegPle huv hM0 hbdM α
            (by constructor <;> assumption)
        have hC2 : |Q.eval α| ≤ (2 * (m : ℝ) ^ 2 / (v - u)) * |P.eval z| := by
          calc
            |Q.eval α| = |P.derivative.eval α| := by rw [q_alpha_eq hfac]
            _ ≤ (2 * (m : ℝ) ^ 2 / (v - u)) * |P.eval z| := hC1
        simpa [hlen] using hC2
      have hxz : |α - z| ≤ v - u := by
        rw [abs_le]
        constructor <;> linarith [hzIJ.1, hzIJ.2, hαu, hαv]
      have hxzδ : |α - z| ≤ δ := by
        simpa [hlen] using hxz
      exact htail α z hα hzIcc hxzδ hQαb
    · by_cases hfar : r ≤ |x - α|
      · have hQx : |Q.eval x| ≤ |P.eval x| / r := by
          have hxane_pos : 0 < |x - α| := lt_of_lt_of_le hrpos hfar
          have h1 : |Q.eval x| ≤ |P.eval x| / |x - α| := hQ_abs hxα
          have h2 : |P.eval x| / |x - α| ≤ |P.eval x| / r :=
            div_le_div_of_nonneg_left (abs_nonneg (P.eval x)) hrpos hfar
          exact le_trans h1 h2
        have hwP : (weight muSerre x) ^ N * |P.eval x| ≤ wnorm N P :=
          Submission.WnormToolkit.wnorm_ge_pointwise N P hx
        have h1 : (weight muSerre x) ^ N * |Q.eval x| ≤
            (weight muSerre x) ^ N * |P.eval x| / r := by
          calc
            (weight muSerre x) ^ N * |Q.eval x|
                ≤ (weight muSerre x) ^ N * (|P.eval x| / r) := by
                  exact mul_le_mul_of_nonneg_left hQx
                    (pow_nonneg (le_of_lt (weight_pos muSerre x)) N)
            _ = (weight muSerre x) ^ N * |P.eval x| / r := by ring
        have h2 : (weight muSerre x) ^ N * |P.eval x| / r ≤ wnorm N P / r :=
          div_le_div_of_nonneg_right hwP (le_of_lt hrpos)
        have h3 : wnorm N P / r ≤ B * wnorm N P := by
          calc
            wnorm N P / r = wnorm N P * (1 / r) := by ring
            _ ≤ wnorm N P * B := by
              exact mul_le_mul_of_nonneg_left hcoefF (Submission.WnormToolkit.wnorm_nonneg N P)
            _ = B * wnorm N P := by ring
        exact le_trans (le_trans h1 h2) h3
      · have hnear : |x - α| < r := lt_of_not_ge hfar
        have hxa_le : |x - α| ≤ δ / 8 := by
          exact le_trans (le_of_lt hnear) hrle
        rcases near_interval δ hδpos hδle hα hx hxa_le with
          ⟨u, v, hu_lo, hv_hi, huv, hlen, hαu, hαv, hxu, hxv⟩
        rcases max_abs_point P huv with ⟨z, hzIJ, hzmax⟩
        have hzIcc : z ∈ Set.Icc aSerre bSerre := by
          constructor
          · linarith [hu_lo, hzIJ.1]
          · linarith [hv_hi, hzIJ.2]
        have hM0 : 0 ≤ |P.eval z| := abs_nonneg _
        have hbdM : ∀ t : ℝ, t ∈ Set.Icc u v → |P.eval t| ≤ |P.eval z| := by
          intro t ht
          exact hzmax t ht
        have hC : |P.eval x - P.eval α| ≤ (2 * (m : ℝ) ^ 2 / (v - u)) * |P.eval z| * |x - α| :=
          eval_lipschitz_on (P := P) (m := m) hdegPle huv hM0 hbdM
            (x := x) (y := α)
            (by constructor <;> assumption) (by constructor <;> assumption)
        have hQb : |Q.eval x| ≤ (2 * (m : ℝ) ^ 2 / δ) * |P.eval z| := by
          have hPabs : |P.eval x| = |P.eval x - P.eval α| := by
            calc
              |P.eval x| = |P.eval x - 0| := by simp
              _ = |P.eval x - P.eval α| := by rw [hPα]
          have hPxle : |P.eval x| ≤ (2 * (m : ℝ) ^ 2 / (v - u)) * |P.eval z| * |x - α| := by
            rw [hPabs]
            exact hC
          have hxane_pos : 0 < |x - α| := abs_pos.mpr (sub_ne_zero.mpr hxα)
          have hmain : |Q.eval x| ≤ (2 * (m : ℝ) ^ 2 / (v - u)) * |P.eval z| := by
            calc
              |Q.eval x| ≤ |P.eval x| / |x - α| := hQ_abs hxα
              _ ≤ ((2 * (m : ℝ) ^ 2 / (v - u)) * |P.eval z| * |x - α|) / |x - α| :=
                    div_le_div_of_nonneg_right hPxle (le_of_lt hxane_pos)
              _ = (2 * (m : ℝ) ^ 2 / (v - u)) * |P.eval z| := by
                    field_simp [ne_of_gt hxane_pos]
          simpa [hlen] using hmain
        have hxz : |x - z| ≤ v - u := by
          rw [abs_le]
          constructor <;> linarith [hzIJ.1, hzIJ.2, hxu, hxv]
        have hxzδ : |x - z| ≤ δ := by
          simpa [hlen] using hxz
        exact htail x z hx hzIcc hxzδ hQb
  have hfin : wnorm N Q ≤ B * wnorm N P := by
    exact Submission.WnormToolkit.wnorm_sSup_le N Q (a := B * wnorm N P) hpoint
  simpa [B, eH, s] using hfin

/-- The fixed power absorbs the polynomial-in-`(N,m)` constant:
`8·e^{H0}·m²·(N+1)² ≤ (2·max N m)^{9+2·H0}` for `m ≥ 1`. -/
lemma remez_pow_bound (H0 : ℝ) (hH0 : 0 ≤ H0) (N m : ℕ) (hm : 1 ≤ m) :
    (8 * Real.exp H0 * (m : ℝ) ^ 2 * ((N : ℝ) + 1) ^ 2) ≤
      ((2 * max N m : ℕ) : ℝ) ^ (9 + 2 * H0) := by
  let T : ℕ := max N m
  have hTm : m ≤ T := by dsimp [T]; exact Nat.le_max_right N m
  have hTN : N ≤ T := by dsimp [T]; exact Nat.le_max_left N m
  have hT1n : 1 ≤ T := le_trans hm hTm
  have hT1 : 1 ≤ (T : ℝ) := by exact_mod_cast hT1n
  have hN2 : N + 1 ≤ 2 * T := by
    by_cases hN0 : N = 0
    · subst N; omega
    · have hNpos : 1 ≤ N := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hN0)
      omega
  have hN2r : (N : ℝ) + 1 ≤ 2 * (T : ℝ) := by
    have hN2c : ((N + 1 : ℕ) : ℝ) ≤ ((2 * T : ℕ) : ℝ) := by exact_mod_cast hN2
    simpa [Nat.cast_add, Nat.cast_mul] using hN2c
  have hN1nonneg : 0 ≤ (N : ℝ) + 1 := by positivity
  have hmR : (m : ℝ) ≤ (T : ℝ) := by exact_mod_cast hTm
  have hm2 : (m : ℝ) ^ 2 ≤ (T : ℝ) ^ 2 := by
    exact pow_le_pow_left₀ (by positivity : 0 ≤ (m : ℝ)) hmR 2
  have hN2sq : ((N : ℝ) + 1) ^ 2 ≤ (2 * (T : ℝ)) ^ 2 := by
    exact pow_le_pow_left₀ hN1nonneg hN2r 2
  have h8e : 0 ≤ 8 * Real.exp H0 := by positivity
  have hA1 : 8 * Real.exp H0 * (m : ℝ) ^ 2 ≤ 8 * Real.exp H0 * (T : ℝ) ^ 2 := by
    exact mul_le_mul_of_nonneg_left hm2 h8e
  have hA2 : (8 * Real.exp H0 * (m : ℝ) ^ 2) * ((N : ℝ) + 1) ^ 2 ≤
      (8 * Real.exp H0 * (m : ℝ) ^ 2) * (2 * (T : ℝ)) ^ 2 := by
    exact mul_le_mul_of_nonneg_left hN2sq (mul_nonneg h8e (sq_nonneg (m : ℝ)))
  have hA3 : (8 * Real.exp H0 * (m : ℝ) ^ 2) * (2 * (T : ℝ)) ^ 2 ≤
      (8 * Real.exp H0 * (T : ℝ) ^ 2) * (2 * (T : ℝ)) ^ 2 := by
    exact mul_le_mul_of_nonneg_right hA1 (sq_nonneg (2 * (T : ℝ)))
  have hA : 8 * Real.exp H0 * (m : ℝ) ^ 2 * ((N : ℝ) + 1) ^ 2 ≤
      32 * Real.exp H0 * (T : ℝ) ^ 4 := by
    calc
      8 * Real.exp H0 * (m : ℝ) ^ 2 * ((N : ℝ) + 1) ^ 2
          = (8 * Real.exp H0 * (m : ℝ) ^ 2) * ((N : ℝ) + 1) ^ 2 := by ring
      _ ≤ (8 * Real.exp H0 * (m : ℝ) ^ 2) * (2 * (T : ℝ)) ^ 2 := hA2
      _ ≤ (8 * Real.exp H0 * (T : ℝ) ^ 2) * (2 * (T : ℝ)) ^ 2 := hA3
      _ = 32 * Real.exp H0 * (T : ℝ) ^ 4 := by ring
  have hbT : 0 < (2 * (T : ℝ)) := by positivity
  have hT4 : (T : ℝ) ^ 4 ≤ (2 * (T : ℝ)) ^ 4 := by
    have h1 : (T : ℝ) ≤ 2 * (T : ℝ) := by nlinarith [hT1]
    exact pow_le_pow_left₀ (by positivity : 0 ≤ (T : ℝ)) h1 4
  have hB0 : 32 * Real.exp H0 * (T : ℝ) ^ 4 ≤ 32 * Real.exp H0 * (2 * (T : ℝ)) ^ 4 := by
    exact mul_le_mul_of_nonneg_left hT4 (by positivity : 0 ≤ 32 * Real.exp H0)
  have h32 : (32 : ℝ) ≤ (2 * (T : ℝ)) ^ 5 := by
    have h2 : (2 : ℝ) ≤ 2 * (T : ℝ) := by nlinarith [hT1]
    calc
      (32 : ℝ) = (2 : ℝ) ^ 5 := by norm_num
      _ ≤ (2 * (T : ℝ)) ^ 5 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h2 5
  have hE4 : Real.exp 1 ≤ (4 : ℝ) := by
    exact le_of_lt (lt_trans Real.exp_one_lt_three (by norm_num))
  have hT2 : 1 ≤ (T : ℝ) ^ 2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hT1 2
    simpa using h
  have hb4 : (4 : ℝ) ≤ (2 * (T : ℝ)) ^ 2 := by
    nlinarith
  have hb4r : (4 : ℝ) ≤ (2 * (T : ℝ)) ^ (2 : ℝ) := by
    calc
      (4 : ℝ) ≤ (2 * (T : ℝ)) ^ 2 := hb4
      _ = (2 * (T : ℝ)) ^ (2 : ℝ) := (Real.rpow_natCast (2 * (T : ℝ)) 2).symm
  have heq : Real.exp H0 = (Real.exp 1) ^ H0 := by
    rw [Real.rpow_def_of_pos (Real.exp_pos 1) H0, Real.log_exp, one_mul]
  have he4 : (Real.exp 1) ^ H0 ≤ (4 : ℝ) ^ H0 := by
    exact Real.rpow_le_rpow (Real.exp_nonneg 1) hE4 hH0
  have h4bT : (4 : ℝ) ^ H0 ≤ ((2 * (T : ℝ)) ^ (2 : ℝ)) ^ H0 := by
    exact Real.rpow_le_rpow (by norm_num) hb4r hH0
  have hb2 : ((2 * (T : ℝ)) ^ (2 : ℝ)) ^ H0 = (2 * (T : ℝ)) ^ (2 * H0) := by
    exact (Real.rpow_mul (le_of_lt hbT) (2 : ℝ) H0).symm
  have heT : Real.exp H0 ≤ (2 * (T : ℝ)) ^ (2 * H0) := by
    rw [heq]
    exact le_trans (le_trans he4 h4bT) (by rw [hb2])
  have hmul : 32 * Real.exp H0 ≤ (2 * (T : ℝ)) ^ 5 * (2 * (T : ℝ)) ^ (2 * H0) := by
    exact mul_le_mul h32 heT (Real.exp_nonneg H0) (by positivity : 0 ≤ (2 * (T : ℝ)) ^ 5)
  have hEq9 : (2 * (T : ℝ)) ^ 9 = (2 * (T : ℝ)) ^ (9 : ℝ) :=
    (Real.rpow_natCast (2 * (T : ℝ)) 9).symm
  have hB : 32 * Real.exp H0 * (2 * (T : ℝ)) ^ 4 ≤ (2 * (T : ℝ)) ^ (9 + 2 * H0) := by
    calc
      32 * Real.exp H0 * (2 * (T : ℝ)) ^ 4
          ≤ ((2 * (T : ℝ)) ^ 5 * (2 * (T : ℝ)) ^ (2 * H0)) * (2 * (T : ℝ)) ^ 4 := by
            exact mul_le_mul_of_nonneg_right hmul (by positivity : 0 ≤ (2 * (T : ℝ)) ^ 4)
      _ = (2 * (T : ℝ)) ^ 4 * (2 * (T : ℝ)) ^ 5 * (2 * (T : ℝ)) ^ (2 * H0) := by ring
      _ = (2 * (T : ℝ)) ^ (4 + 5) * (2 * (T : ℝ)) ^ (2 * H0) := by rw [pow_add]
      _ = (2 * (T : ℝ)) ^ 9 * (2 * (T : ℝ)) ^ (2 * H0) := by norm_num
      _ = (2 * (T : ℝ)) ^ (9 : ℝ) * (2 * (T : ℝ)) ^ (2 * H0) := by
            rw [hEq9]
      _ = (2 * (T : ℝ)) ^ ((9 : ℝ) + 2 * H0) := by
            rw [← Real.rpow_add hbT]
  have hcast : ((2 * max N m : ℕ) : ℝ) = 2 * (T : ℝ) := by
    simp [T]
  calc
    (8 * Real.exp H0 * (m : ℝ) ^ 2 * ((N : ℝ) + 1) ^ 2)
        ≤ 32 * Real.exp H0 * (T : ℝ) ^ 4 := hA
    _ ≤ 32 * Real.exp H0 * (2 * (T : ℝ)) ^ 4 := hB0
    _ ≤ (2 * (T : ℝ)) ^ (9 + 2 * H0) := hB
    _ = ((2 * max N m : ℕ) : ℝ) ^ (9 + 2 * H0) := by rw [hcast]


/-- Weighted Remez division by a real root in `[aSerre,bSerre]` (real
polynomials): `‖P/(X−α)‖_N ≤ (2·max N m)^C · ‖P‖_N` for a root `α` of `P`
of degree `m ≥ 1`, with a fixed `C` depending only on the data. -/
theorem weighted_remez_real :
    ∃ C : ℝ, 0 < C ∧ ∀ (N m : ℕ), 1 ≤ m →
      ∀ P : Polynomial ℝ, P.natDegree = m →
      ∀ α : ℝ, α ∈ Set.Icc aSerre bSerre → P.eval α = 0 →
        ∃ Q : Polynomial ℝ,
          P = (Polynomial.X - Polynomial.C α) * Q ∧
          wnorm N Q ≤ ((2 * max N m : ℕ) : ℝ) ^ C * wnorm N P := by
  rcases Submission.SerrePotentialIcc.exists_potential_half_holder with ⟨H0, hH0, hU⟩
  let C0 : ℝ := 9 + 2 * H0
  refine ⟨C0, ?_, ?_⟩
  · dsimp [C0]
    linarith
  · intro N m hm P hdegP α hα hPα
    have hdiv : (Polynomial.X - Polynomial.C α) ∣ P := by
      exact (Polynomial.dvd_iff_isRoot).mpr (by simpa [Polynomial.IsRoot] using hPα)
    rcases hdiv with ⟨Q, hfac⟩
    refine ⟨Q, hfac, ?_⟩
    have hcore := wnorm_div_bound (N := N) (m := m) H0 hH0 hU hm hdegP hα hPα hfac
    have hpow := remez_pow_bound H0 hH0 N m hm
    have hnp : 0 ≤ wnorm N P := Submission.WnormToolkit.wnorm_nonneg N P
    calc
      wnorm N Q ≤ (8 * Real.exp H0 * (m : ℝ) ^ 2 * ((N : ℝ) + 1) ^ 2) * wnorm N P := hcore
      _ ≤ ((2 * max N m : ℕ) : ℝ) ^ C0 * wnorm N P := by
            dsimp [C0]
            exact mul_le_mul_of_nonneg_right hpow hnp

end Submission.RemezReal
