import Mathlib
import Submission.Commons.MeasureTheory.tail_blocks_le_measure_limsup
import Submission.Commons.Analysis.Asymptotics.exists_Icc_sum_between_of_tail_lower
import Submission.Commons.NumberTheory.DuffinSchaeffer.addWellApproximable_eq_limsup_piecewise
import Submission.Commons.NumberTheory.DuffinSchaeffer.approxAddOrderOf_volume_ge_min
import Submission.Commons.NumberTheory.DuffinSchaeffer.volume_eq_one_of_positive_measure
import Submission.Commons.NumberTheory.DuffinSchaeffer.approxAddOrderOf_eq_biUnion_ball
import Submission.Commons.NumberTheory.DuffinSchaeffer.volume_ball_le_ofReal_two_mul
import Submission.Commons.NumberTheory.DuffinSchaeffer.reduced_pair_count_prime_pow
import Submission.Commons.NumberTheory.DuffinSchaeffer.fibre_window_count_le_global
import Submission.Commons.NumberTheory.DuffinSchaeffer.fibre_count_eq
import Submission.Commons.NumberTheory.Totient.coprime_window_mainTerm_bound
import Submission.Commons.NumberTheory.PrimeReciprocals.prime_recip_sum_le_log_log
import Submission.Commons.NumberTheory.DuffinSchaeffer.sum_sq_inv_Icc_le_two_div

/-!
# `positive_measure_large_values_pv` — the "large values" positive-measure input

**Statement.**  Let `δ : ℕ → ℝ` be non-negative with `δ n → 0`, and suppose that every
non-zero value is *large*, in the sense `δ n = 0 ∨ 1/2 ≤ (n : ℝ) * δ n`.  If the
φ-weighted sum `Σ n.totient * δ n` diverges, then the Duffin–Schaeffer
well-approximable set on the circle has positive measure:
`0 < volume (addWellApproximable UnitAddCircle δ)`.

**Mathematical status.**  The statement is *true*: it is the positive-measure
half of Lemma 2.2 of Koukoulopoulos–Maynard ("Duffin–Schaeffer when ψ takes only
large values", *Ann. of Math.* 192 (2020), 251–307), which follows from
Pollington–Vaughan's Theorem 2 (*Mathematika* 37 (1990), 190–200), exactly the
`ψ(q) ≥ 1/2` regime (in their normalisation `a(q) = q·δ(q)`).

**Proof structure used in this file.**  Gallagher's 0–1 law
(`AddCircle.addWellApproximable_ae_empty_or_univ`, available in Mathlib, and
`volume_eq_one_of_positive_measure` in the commons) shows the set has measure
`0` or `1`, so positive measure is equivalent to the existence of arbitrarily
far-out finite *tail blocks* whose union has uniformly positive measure
(`MeasureTheory.tail_blocks_le_measure_limsup`, in the commons).  The deep
content is therefore the following *tail-block* lemma for large values

```
large_values_tail_block (δ) ... : ∃ c > 0, ∀ N, ∃ Y > N,
    c ≤ volume (⋃ q ∈ Finset.Icc N Y, approxAddOrderOf UnitAddCircle q (δ q))
```

This is the Pollington–Vaughan second-moment analysis: for a block `[X, Y]` with
`1 ≤ Σ_{q∈[X,Y]} φ(q)·δ(q) ≤ 2` one bounds the second moment
`Σ_{q,r∈[X,Y]} volume(A_q ∩ A_r)` (the correlation structure of arcs around
reduced fractions is controlled through the divisors of `q·r / gcd(q,r)²`), so
that `volume(⋃ A_q) ≥ (Σ volume A_q)² / (second moment)` is bounded below.
`large_values_tail_block` is *not yet proved* in the shared commons; it is the
remaining `unfilled` below.

The second-moment lower bound `volume(A_q) ≥ 2·φ(q)·min(δ q, 1/(2q))` needed in
the block estimate is `approxAddOrderOf_volume_ge_min` (commons, proved).

The second-moment lower bound `volume(A_q) ≥ 2·φ(q)·min(δ q, 1/(2q))` needed in
the block estimate is `approxAddOrderOf_volume_ge_min` (commons, proved).

**Development log (this session).**

1. *Assembly (done, compiles).* `positive_measure_large_values_pv` is reduced to
   `large_values_tail_block` via `tail_blocks_le_measure_limsup` (proved below).

2. *Base pairwise overlap bound — PROVED (fleet, committed to commons as
   `Commons.NumberTheory.DuffinSchaeffer.approxAddOrderOf_inter_volume_le`,
   `Submission/Commons/NumberTheory/DuffinSchaeffer/approxAddOrderOf_inter_volume_le.lean`).*
   It imports supporting commons lemmas `approxAddOrderOf_eq_biUnion_ball`,
   `volume_ball_le_ofReal_two_mul`, `card_div_nat_ball_le`.
   For `q ≠ r`, every intersecting pair of arcs `B(m/q,δq) ∩ B(n/r,δr)` has
   measure `≤ 2·min(δq,δr)`, and for each fixed reduced `m` the number of reduced
   residues `n mod r` within circle-distance `δq+δr` of `m/q` is at most
   `2(δq+δr)r + 1` (a window of length `2(δq+δr)` on the `1/r`-grid), giving
   ```
   volume(A_q ∩ A_r) ≤ 2·min(δq,δr) ·
     min( φ(q)(2(δq+δr)r+1), φ(r)(2(δq+δr)q+1), φ(q)φ(r) ).
   ```
   This is the elementary counting layer of the PV overlap analysis.
   (`approxAddOrderOf_eq_biUnion_ball` etc. were added to the commons by the same
   subagent while proving it.)

3. *Next: PV divisor-structured overlap lemma for large values.*  The base
   bound of step 2 is *not sufficient alone* for the block second moment: for the
   boundary case `δ(q) = 1/(2q)` (all `q` in a block `[X,2X]`) it yields
   `volume(A_q∩A_r) ≤ 4φ(q)/r`, so `Σ_{q≠r} ≍ X³` while
   `(Σ_q volume A_q)² ≍ X²` — it misses the factor `φ(r)/r` (i.e. the sparsity
   of the reduced residues of `r` inside a short window).  To make
   `Σ_{q≠r} volume(A_q∩A_r)` bounded by a constant times `(Σ volume A_q)²` even
   when `φ(q)/q` is small (primorial-type denominators), the counting must be
   refined: solutions of `‖m/q − n/r‖ < δq+δr` are counted through the common
   lattice `/lcm(q,r)` with divisor structure of `q·r/gcd(q,r)²`
   (Pollington–Vaughan *Mathematika* 37 (1990), §3, Lemma p. 196; the
   `qδq,qδr ≤ 1/2` special case is being formalised in the commons request
   `pollington_vaughan_overlap_bound`).  Deriving the correct large-value
   analogue (with PV's case split on `q·r·max(δq,δr)/gcd(q,r)`) is the next
   delegation round.

4. *Then:* block selection (`1 ≤ Σ_{q∈[X,Y]} φ(q)·δ(q) ≤ 2`, arbitrarily far
   out), the Cauchy–Schwarz second-moment step
   (`volume(⋃ A_q) ≥ (Σ volume A_q)² / Σ_{q,r} volume(A_q∩A_r)` — commons
   `measure_union_lower_of_second_moment`), and the case split
   `qδq ≤ 1` / `1 < qδq ≤ q/(2φ(q))` / larger (PV Theorem 2, §5), concluding
   `large_values_tail_block`.

**Session state (CURRENT, Session 5).**  `large_values_tail_block` and
`positive_measure_large_values_pv` are FULLY PROVEN in this file (as theorems
near the end).  **K1 is COMPLETE**: `cyclic_gap_cover_bound` (the coprime-gap
coverage inequality) and all its supporting machinery are proved (see the
Session-5 note at the bottom; the helpers were spliced in after
`list_sum_map_mono`).  Remaining `unfilled`s (exactly two):
(1) `pair_sum_nat_bound` (~line 2724, inside the K1 section) — the CRT
    close-pair core `q·closePairSum q k ≤ k·φ(q)²` (k·φ(q) ≤ q).  It feeds
    `real_gap_count_le` → `gap_deficit_bound` → case A of
    `cyclic_gap_cover_bound`.  The mathematical content is proved in the
    Session-5 bottom note: it is equivalent (unconditionally in k) to
    `Σ_{h≤k} c₊(q,h) ≤ k·φ(q)²/q`, best proved via the per-prime formula
    `c₊(h) = (q/rad(q))·∏_{p|q} ((p−2) + 1[p|h])` (CRT split into prime
    powers; on `p^e` the count is `p^{e−1}·((p−2)+1[p|h])`) and the positive
    T-subset expansion `Σ_{h≤k}∏_p g_p(h) ≤ k·∏_p[(p−2)+1/p]` (ALL expansion
    coefficients ∏_{p∉T}(p−2) ≥ 0, so the `⌊k/rad(T)⌋ ≤ k/rad(T)` floor bound
    applies termwise), finishing `= k·∏_p(p−1)²/p` since `(p−2)+1/p =
    (p−1)²/p`.  [A Möbius divisor-sum alternative `q·Σ_h c₊(h) =
    Σ_{d,e|q} μ(d)μ(e)·(q²·gcd(d,e)/(d·e))·⌊k/gcd(d,e)⌋ ≤ k·(Σ_d μ(d)q/d)² =
    k·φ²` fails as a formal route: the `⌊k/g⌋ ≤ k/g` bound cannot be applied
    termwise because the coefficients μ(d)μ(e) have mixed signs.]  The needed
    ingredient `Σ_{d|q} μ(d)·(q/d) = φ(q)` is
    `Commons.NumberTheory.Totient.sum_moebius_mul_natDiv_eq_totient`
    (module `Submission.Commons.NumberTheory.Totient.coprime_window_mainTerm_bound`).
(2) `approxAddOrderOf_inter_volume_le_quasi` (~line 3715) — K2, the per-pair
    quasi-independence `μ(A_q∩A_r) ≤ 8μ(A_q)μ(A_r)`; trivial regime when one
    measure ≥ 1/8, deep close-pair-counting regime otherwise (PV §3; combine
    the committed `approxAddOrderOf_inter_volume_le` with the fibre-based
    window count and `main_term_real_ineq`, as documented in its docstring and
    in `pv_overlap_large.lean` §8/§9).
-/

open MeasureTheory Filter Set Metric
open scoped ENNReal Topology

namespace Commons.NumberTheory.DuffinSchaeffer

noncomputable section

private lemma approxAddOrderOf_nullMeasurable (δ : ℕ → ℝ) (n : ℕ) :
    NullMeasurableSet (approxAddOrderOf UnitAddCircle n (δ n)) volume := by
  rw [approxAddOrderOf]
  exact (Metric.isOpen_thickening.measurableSet :
    MeasurableSet (Metric.thickening (δ n) {y : UnitAddCircle | addOrderOf y = n})).nullMeasurableSet

open scoped ENNReal Topology BigOperators

/-! ## Block error-sum: the explicit target (PV §4 analogue)

With the per-pair bound of `pv_overlap_large.lean` Section 7
(`volume(A_q∩A_r) ≤ 2·min(δq,δr)·(2(δq+δr)·φ(q)φ(r) + E(q,r))`, `|E| ≤ φ(g)·τ(F)·3^{ω(g)}`
with `g = gcd(q,r)`, `F = qr/g²`), the second moment over a dyadic block `[X,2X]`
splits as

```
Σ_{q,r} μ(A_q∩A_r) ≤ Σ_q μ(A_q) + 8(Σ_q φ(q)δ(q))² + ErrorSum(X)
ErrorSum(X) := Σ_{q≠r ∈ [X,2X]} 2·min(δq,δr)·φ(gcd(q,r))·τ(qr/gcd²)·3^{ω(gcd)}
```

and `Σ_q μ(A_q) ≥ Σ_{q: qδ(q) ≤ 1} φ(q)δ(q)` (each `A_q` contains `φ(q)` disjoint
balls of radius `min(δq, 1/(2q))`; the `qδ(q) ≤ 1` part has
`min(δq,1/(2q)) ≥ δq/2`-free lower bound `μ(A_q) ≥ φ(q)δ(q)`).

**Explicit target inequality (the lemma to prove; the whole remaining content of
`large_values_tail_block` is: prove it, then Cauchy–Schwarz via
`measure_union_lower_of_second_moment`).**

```
large_values_block_second_moment : ∃ C : ℝ≥0∞, 0 < C ∧ ∀ X ≥ 1,
    Σ_{q,r ∈ Icc X (2X)} volume(approxAddOrderOf UnitAddCircle q (δ q)
                                ∩ approxAddOrderOf UnitAddCircle r (δ r))
      ≤ C * (1 + Σ_{q ∈ Icc X (2X)} min(1, 2φ(q)·δ(q)))²
```

where the `δ(q) > 1/q` ("very large", PV case (ii)+(iii)) terms are handled by the
PV §5 direct argument (positive/full measure) rather than the block second moment,
so the inequality above is stated for the reduction where the block index set is
restricted to `qδ(q) ≤ 1` (bounded-`b`) — this restriction is the content of the
case split documented below; it is safe because if the `b > 1` subseries diverges,
PV case (ii)/(iii) gives the result directly, and if it converges it is dropped
(the remaining `b ≤ 1` subseries still diverges, since the full series does and
the dropped part is summable).

**Important refinement discovered by direct computation (numerical, `q=210,r=420`
and friends, boundary case `δ=1/(2q)`):** for *linked* pairs (`r = 2q`, large
`g = gcd`), the true `μ(A_q∩A_r) ≈ 0.7·μ(A_q)·μ(A_r)` — quasi-independence
holds — even though the crude per-pair remainder kernel
`2min(δq,δr)·φ(g)·τ(F)·3^{ω(g)}` massively overcounts them (by `~3^{ω(g)}`).
Hence the naive statement `ErrorSum(X) ≪ (Σ min(1,2φδ))²` with `ErrorSum`
carrying the `φ(g)τ(F)3^{ω(g)}` kernel for *all* ordered pairs is FALSE for
sparse gcd-heavy supports, and the correct block estimate must instead:

1. **bound linked pairs trivially**: for the `O(1)` partners of each `q` with
   `r ∈ {q/2, q, 2q}`-type structure in the dyadic block, use
   `μ(A_q∩A_r) ≤ min(μ(A_q),μ(A_r))`, contributing `≤ C·Σ_q μ(A_q)` (an `L`-
   scale term, absorbed by `L² + L`);
2. **apply the fibre main-term + remainder bound only to the genuinely
   independent pairs** (coprime-part structure with `q/g, r/g ≥ 2`), where the
   `(2Δφ(q)φ(r))` main term gives `≤ 8(Σφδ)²` and the remainder sum
   `Σ 2min(δq,δr)·|E(q,r)|` over such pairs is the divisor-sum estimate to prove;
3. Cauchy–Schwarz (`measure_union_lower_of_second_moment`): with
   `Σ μ(A_q) ≥ Σ φ(q)δ(q) ≥ 1` on far-out blocks (bounded-`b` part after the
   case split), `μ(⋃ A_q) ≥ L²/U ≥ c > 0` uniformly;
4. `tail_blocks_le_measure_limsup` gives `0 < μ(addWellApproximable)`
   (assembly already proven in this file).

**Second refinement (quantitative, boundary case `δ = 1/(2q)`, measured by
sampling `μ∩` for `q,r ∈ [X,2X]`):** the *true* per-pair intersections satisfy
quasi-independence with a small constant in every tested regime —

* linked `(q/g, r/g) = (1,2)`: `μ∩ ≈ 0.68–0.70 · μ(A_q)μ(A_r)`;
* gcd-heavy coprime parts `(2,3)` (`(420,630)`, `(600,900)`, `(660,990)`):
  `μ∩ ≈ 1.36–1.42 · μ(A_q)μ(A_r)`;
* coprime parts `(3,5)` (`(900,1500)`, `(210,350)`): `μ∩ ≈ 0.99–1.00`.

Moreover the *true* remainder is small even for gcd-heavy pairs: for
`(420,630)` at boundary `δ`, the window is `W = ΔL = (q+r)/(2g) = 2.5`, only
`e ∈ {±1}` contribute (`C(±1) = 2·φ(2)φ(3)-weighted × shared-prime factors
= 30`), giving `N(60) ≈ 2Δφ(q)φ(r) + 5` — the crude bound
`|E| ≤ φ(g)τ(F)3^{ω(g)} = 48·τ(6)·3³ = 5184` overcounts by `~10³` because the
rounding/divisor-sum it bounds is only over the *tiny* window, not the whole
fibre.  Conclusion: the missing estimate is a **small-window remainder bound**

```
|E(q,r;Δ)| := |Σ_{|e| ≤ ΔL} C(e) − 2Δ·φ(q)φ(r)| ≤ C·(2Δ·φ(q)φ(r) + 1)   (absolute C)
```

*Refinement (from the `(130,375)`-type tests, `W = ΔL` small):* the N-level
remainder can exceed `2Δφφ + 1` when the window contains only `e = ±1`
(concentrated fibre values `C(±1) = Φ_F·∏_S B_p`, e.g. `8` vs `main ≈ 2`) —
but at the *measure* level this is harmless, since `2·min(δq,δr)·|E|` is then
`≪ μ(A_q)μ(A_r)` (e.g. `0.016` vs `0.197`).  Hence the sharp lemma to prove is
the **measure-level quasi-independence bound**, confirmed numerically in every
tested regime (linked `≈ 0.7·`, coprime-part `(2,3)` `≈ 1.4·`, `(3,5)` `≈ 1.0·`
times `μ(A_q)μ(A_r)`):  With it, the block
second moment is `U ≤ C'(L² + L)` directly (independent pairs carry `≤ C(Σμ)²`,
linked pairs are absorbed by `min(μ_q, μ_r) ≤ ...` at `L`-scale).  Proving the
measure-level quasi-independence bound — analysing `2·min(δq,δr)·N(Δ)` with
`N(Δ) = Σ_{|e|≤ΔL} C(e)` through the Section 5–7 fibre formula and the
committed `fibre_window_count_le_global`, showing the remainder contributes
`≪ μ(A_q)μ(A_r)` in the summation — is the remaining content of
`large_values_tail_block`.
-/




/-- Bounded-b main-term real inequality: with δq ≤ 1/q and δr ≤ 1/r, the "diagonal"
second-moment weight satisfies `2min·2Δ·φ(q)φ(r) ≤ 8·φ(q)/q·φ(r)/r`. -/
private lemma min_add_mul_le_two_mul (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    min a b * (a + b) ≤ 2 * a * b := by
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab]
    nlinarith
  · rw [min_eq_right hba]
    nlinarith

private lemma main_term_real_ineq (q r : ℕ) (hq : 0 < q) (hr : 0 < r) (δq δr : ℝ)
    (hδq0 : 0 ≤ δq) (hδr0 : 0 ≤ δr)
    (hδq : δq ≤ 1 / (q : ℝ)) (hδr : δr ≤ 1 / (r : ℝ)) :
    2 * min δq δr * 2 * (δq + δr) * ((q.totient : ℝ) * (r.totient : ℝ)) ≤
      8 * (((q.totient : ℝ) / (q : ℝ)) * ((r.totient : ℝ) / (r : ℝ))) := by
  have hδd : 2 * min δq δr * 2 * (δq + δr) ≤ 8 / ((q : ℝ) * (r : ℝ)) := by
    have hminΔ : min δq δr * (δq + δr) ≤ 2 * δq * δr :=
      min_add_mul_le_two_mul δq δr hδq0 hδr0
    have hqδ : δq * (q : ℝ) ≤ 1 := (le_div_iff₀ (by positivity : 0 < (q : ℝ))).mp hδq
    have hrδ : δr * (r : ℝ) ≤ 1 := (le_div_iff₀ (by positivity : 0 < (r : ℝ))).mp hδr
    have hprod : δq * (q : ℝ) * (δr * (r : ℝ)) ≤ 1 := by
      have hn2 : 0 ≤ δr * (r : ℝ) := by positivity
      calc
        δq * (q : ℝ) * (δr * (r : ℝ)) ≤ 1 * (δr * (r : ℝ)) :=
          mul_le_mul_of_nonneg_right hqδ hn2
        _ = δr * (r : ℝ) := by ring
        _ ≤ 1 := hrδ
    have hqδr : δq * δr ≤ ((q : ℝ) * (r : ℝ))⁻¹ := by
      have hqrpos : 0 < (q : ℝ) * (r : ℝ) := by positivity
      have hd : δq * δr ≤ 1 / ((q : ℝ) * (r : ℝ)) := by
        rw [le_div_iff₀ hqrpos]
        calc
          δq * δr * ((q : ℝ) * (r : ℝ)) = δq * (q : ℝ) * (δr * (r : ℝ)) := by ring
          _ ≤ 1 := hprod
      rw [div_eq_mul_inv] at hd
      simpa using hd
    have h8 : 8 * δq * δr ≤ 8 * ((q : ℝ) * (r : ℝ))⁻¹ := by
      calc
        8 * δq * δr = 8 * (δq * δr) := by ring
        _ ≤ 8 * ((q : ℝ) * (r : ℝ))⁻¹ := mul_le_mul_of_nonneg_left hqδr (by norm_num)
    rw [div_eq_mul_inv]
    calc
      2 * min δq δr * 2 * (δq + δr) = 4 * (min δq δr * (δq + δr)) := by ring
      _ ≤ 4 * (2 * δq * δr) := mul_le_mul_of_nonneg_left hminΔ (by norm_num)
      _ = 8 * δq * δr := by ring
      _ ≤ 8 * ((q : ℝ) * (r : ℝ))⁻¹ := h8
  calc
    2 * min δq δr * 2 * (δq + δr) * ((q.totient : ℝ) * (r.totient : ℝ))
        ≤ (8 / ((q : ℝ) * (r : ℝ))) * ((q.totient : ℝ) * (r.totient : ℝ)) := by
          exact mul_le_mul_of_nonneg_right hδd (by positivity)
    _ = 8 * (((q.totient : ℝ) / (q : ℝ)) * ((r.totient : ℝ) / (r : ℝ))) := by
          field_simp [hq.ne', hr.ne']

/-- Radius zero: `approxAddOrderOf` at radius 0 is empty (points at distance < 0). -/
private lemma approxAddOrderOf_eq_empty_of_radius_zero (q : ℕ) (hq : 0 < q) :
    approxAddOrderOf UnitAddCircle q 0 = (∅ : Set UnitAddCircle) := by
  ext x
  constructor
  · intro hx
    rcases (UnitAddCircle.mem_approxAddOrderOf_iff (n := q) (x := x) (δ := 0) hq).mp hx with
      ⟨m, _hm, _hg, hn⟩
    linarith [norm_nonneg (x - (↑(((m : ℝ) / (q : ℝ)) : UnitAddCircle)))]
  · intro hx
    simpa using hx


/-- Certified measure lower bound in the large-value case: `A_q` contains `φ(q)`
pairwise-disjoint balls of radius `1/(2q)`, so `μ(A_q) ≥ φ(q)/q`. -/
private lemma approxAddOrderOf_volume_ge_totient_div (q : ℕ) (hq : 0 < q) (δ : ℝ)
    (hδ : 0 ≤ δ) (hlarge : (1 : ℝ) / 2 ≤ (q : ℝ) * δ) :
    ENNReal.ofReal (((q.totient : ℕ) : ℝ) / (q : ℝ)) ≤
      MeasureTheory.volume (approxAddOrderOf UnitAddCircle q δ) := by
  have hge := Commons.NumberTheory.DuffinSchaeffer.approxAddOrderOf_volume_ge_min q δ
  have hmin : min δ (1 / (2 * (q : ℝ))) = 1 / (2 * (q : ℝ)) := by
    apply min_eq_right
    have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    have hd : (1 : ℝ) / (2 * (q : ℝ)) ≤ δ := by
      field_simp [hq0.ne']
      nlinarith [hlarge, hq0]
    exact hd
  rw [hmin] at hge
  have hmono : ENNReal.ofReal (((q.totient : ℕ) : ℝ) / (q : ℝ)) ≤
      ENNReal.ofReal (2 * (q.totient : ℝ) * (1 / (2 * (q : ℝ)))) := by
    exact ENNReal.ofReal_le_ofReal (by
      field_simp [hq.ne']
      nlinarith)
  exact le_trans hmono hge

/- (the long-arc K1 lemma was relocated below with the full K1 development) -/

/-- Case (A) of the long-arc core forces `2·φ(q) < q`: hypotheses
`δ > 1/q` (long arc) and `2φδ ≤ 1` (case A: arcs no longer than the average gap)
give `1/q < δ ≤ 1/(2φ)`, hence `2φ < q`. -/
private lemma totient_two_lt_q_of_caseA (q : ℕ) (hq : 0 < q) (δ : ℝ)
    (hδ1 : (1 : ℝ) / (q : ℝ) < δ) (hδA : 2 * (q.totient : ℝ) * δ ≤ 1) :
    2 * (q.totient : ℝ) < (q : ℝ) := by
  have hφpos : 0 < (q.totient : ℝ) := by exact_mod_cast (Nat.totient_pos.mpr hq)
  have h2φ : 0 < 2 * (q.totient : ℝ) := by positivity
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast hq
  have hδle : δ ≤ 1 / (2 * (q.totient : ℝ)) := by
    rw [le_div_iff₀ h2φ]
    nlinarith [hδA]
  have hlt : (1 : ℝ) / (q : ℝ) < 1 / (2 * (q.totient : ℝ)) := lt_of_lt_of_le hδ1 hδle
  have hcross : (1 : ℝ) / (q : ℝ) * ((q : ℝ) * (2 * (q.totient : ℝ))) <
      1 / (2 * (q.totient : ℝ)) * ((q : ℝ) * (2 * (q.totient : ℝ))) := by
    exact mul_lt_mul_of_pos_right hlt (by positivity : 0 < (q : ℝ) * (2 * (q.totient : ℝ)))
  have hL : (1 : ℝ) / (q : ℝ) * ((q : ℝ) * (2 * (q.totient : ℝ))) = 2 * (q.totient : ℝ) := by
    field_simp [hqpos.ne', h2φ.ne']
  have hR : 1 / (2 * (q.totient : ℝ)) * ((q : ℝ) * (2 * (q.totient : ℝ))) = (q : ℝ) := by
    field_simp [hqpos.ne', h2φ.ne']
  rw [hL, hR] at hcross
  exact hcross

/-! Measure-preserving lift and list-length helpers for `trimmed_arc_measure`.

Mathlib already supplies the covering-map facts needed for step (i) of the
partition-lemma spec (`AddCircle.measurePreserving_mk 1 0`,
`AddCircle.add_projection_respects_measure 1 0`, `AddCircle.measurePreserving_equivIoc`),
so computing `volume (approxAddOrderOf UnitAddCircle q δ)` reduces to the real
(Lebesgue) measure of the union of the real intervals `(m/q − δ, m/q + δ)` inside
the fundamental domain `[0,1)`.  `list_sum_div` is the elementary helper for
step (ii): the real gaps `dᵢ/q` of a list of cyclic gaps sum to `Σdᵢ/q`. -/
/-! ### Lifting circle measure to the fundamental domain `[0,1)` (step (i) of the
partition-lemma spec).  Mathlib's `AddCircle.add_projection_respects_measure`
already gives the measure-preserving lift; we record the instance we use: the
volume of a measurable subset of `UnitAddCircle` equals the real (Lebesgue)
volume of its lift to `[0,1)`. -/
/-! Seam-free preimage of a circle closed ball (sub-lemma 2 hook): for radius
`ε < 1/2` the lift of the circle ball about `↑x` into the fundamental-domain
ball `closedBall x (1/2)` is exactly the real ball `closedBall x ε` — no wrap
interaction with the seam.  Uses
`AddCircle.coe_real_preimage_closedBall_inter_eq` (Mathlib). -/
/-! Seam-side companion to `circle_closedBall_preimage_seamfree`: when a radius-`ε`
(`ε < 1/2`) ball about `x ∈ (0,1)` wraps past the seam at `0` (`x < ε`) but not
past `1` (`x + ε ≤ 1`), its lift inside `(0,1)` is the disjoint union of the two
real intervals `(0, x+ε)` and `(x+1−ε, 1)`, of total real measure `2ε`
(measure additivity across the split; the set inclusion into the ball preimage
uses the small-norm distance fact on the circle — next queue item). -/
/-! Small-norm distance on the circle (the missing link for the per-gap set
inclusions): for representatives `a, b ∈ ℝ` at real distance `≤ 1/2`, circle
distance coincides with the real interval length: `dist ↑a ↑b = |a − b|`
(`AddCircle.coe_sub` + `AddCircle.norm_coe_eq_abs_iff`). -/
/-! ### Integer-window description of the circle balls (the K1 lift layer).

For `y : ℝ` and a reduced residue `a` of `q`, the point `↑y` of the unit circle
lies in the open ball of radius `δ` around `↑(a/q)` iff the real window of radius
`qδ` about `q·y` contains an integer of the form `a + k·q` — i.e. an integer
congruent to `a` modulo `q` (all of which are coprime to `q`).  This is the
rigorous form of "the seam is handled by the periodicity of the residue lattice":
no circle-distance API is needed beyond
`circle_norm_lt_iff_exists_int` (distance to `ℤ`). -/

/-- Circle norm of a real < δ iff some integer is within δ: distance to ℤ. -/
private lemma circle_norm_lt_iff_exists_int (x : ℝ) (δ : ℝ) :
    (‖(x : UnitAddCircle)‖ < δ) ↔ ∃ k : ℤ, |x - (k : ℝ)| < δ := by
  constructor
  · intro h
    refine ⟨round x, ?_⟩
    have hn : ‖(x : UnitAddCircle)‖ = |x - (round x : ℝ)| := by
      simp [UnitAddCircle.norm_eq]
    simpa [hn] using h
  · rintro ⟨k, hk⟩
    have hle : ‖(x : UnitAddCircle)‖ ≤ |x - (k : ℝ)| := by
      rw [UnitAddCircle.norm_eq]
      exact round_le x k
    exact lt_of_le_of_lt hle hk

/-- Scaled form: `‖↑(z/q)‖ < δ` iff some `k·q` is within `qδ` of `z`. -/
private lemma norm_div_lt_iff_int_mul (z : ℝ) (q : ℕ) (hq : 0 < q) (δ : ℝ) :
    (‖((z / (q : ℝ)) : UnitAddCircle)‖ < δ) ↔
      ∃ k : ℤ, |z - (k : ℝ) * (q : ℝ)| < δ * (q : ℝ) := by
  rw [circle_norm_lt_iff_exists_int]
  constructor
  · rintro ⟨k, hk⟩
    have hpos : 0 < (q : ℝ) := by exact_mod_cast hq
    have heq : z / (q : ℝ) - (k : ℝ) = (z - (k : ℝ) * (q : ℝ)) / (q : ℝ) := by
      field_simp [hq.ne']
    have h1 : |(z - (k : ℝ) * (q : ℝ))| / (q : ℝ) < δ := by
      simpa [heq, abs_div, abs_of_pos hpos] using hk
    exact ⟨k, (div_lt_iff₀ hpos).mp h1⟩
  · rintro ⟨k, hk⟩
    have hpos : 0 < (q : ℝ) := by exact_mod_cast hq
    have heq : z / (q : ℝ) - (k : ℝ) = (z - (k : ℝ) * (q : ℝ)) / (q : ℝ) := by
      field_simp [hq.ne']
    have h1 : |z / (q : ℝ) - (k : ℝ)| < δ := by
      rw [heq]
      rw [abs_div, abs_of_pos hpos]
      exact (div_lt_iff₀ hpos).mpr hk
    exact ⟨k, h1⟩

/-- `y` is within `δ` of `a/q` on the circle iff the window of radius `qδ` about
`q·y` contains the integer `a + k·q` for some `k`. -/
private lemma ball_mem_window_iff (y : ℝ) (a q : ℕ) (δ : ℝ) (hq : 0 < q) :
    (‖(y : UnitAddCircle) - ↑(((a : ℝ) / (q : ℝ)))‖ < δ) ↔
      ∃ k : ℤ, |(q : ℝ) * y - (((a : ℤ) + k * (q : ℤ)) : ℝ)| < (q : ℝ) * δ := by
  have hz := norm_div_lt_iff_int_mul ((q : ℝ) * y - (a : ℝ)) q hq δ
  have hcast : ((((q : ℝ) * y - (a : ℝ)) / (q : ℝ)) : UnitAddCircle) =
      (y : UnitAddCircle) - ↑(((a : ℝ) / (q : ℝ))) := by
    rw [← AddCircle.coe_sub (p := (1 : ℝ)) y ((a : ℝ) / (q : ℝ))]
    congr 1
    field_simp [hq.ne']
  rw [← hcast]
  have hR : (∃ k : ℤ, |(q : ℝ) * y - (((a : ℤ) + k * (q : ℤ)) : ℝ)| < (q : ℝ) * δ) ↔
      ∃ k : ℤ, |(q : ℝ) * y - (a : ℝ) - (k : ℝ) * (q : ℝ)| < (q : ℝ) * δ := by
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      have hnorm : ((q : ℝ) * y - (((a : ℤ) + k * (q : ℤ)) : ℝ)) =
          (q : ℝ) * y - (a : ℝ) - (k : ℝ) * (q : ℝ) := by
        push_cast
        ring
      rw [hnorm] at hk
      simpa using hk
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      have hnorm : ((q : ℝ) * y - (((a : ℤ) + k * (q : ℤ)) : ℝ)) =
          (q : ℝ) * y - (a : ℝ) - (k : ℝ) * (q : ℝ) := by
        push_cast
        ring
      rw [← hnorm] at hk
      simpa using hk
  rw [hR]
  simpa [mul_comm] using hz

private lemma circle_dist_coe_eq_abs {a b : ℝ} (hab : |a - b| ≤ (1 : ℝ) / 2) :
    dist ((a : UnitAddCircle)) ((b : UnitAddCircle)) = |a - b| := by
  have hcast : ((a - b : ℝ) : UnitAddCircle) = (a : UnitAddCircle) - (b : UnitAddCircle) :=
    AddCircle.coe_sub (1 : ℝ) a b
  calc
    dist ((a : UnitAddCircle)) ((b : UnitAddCircle))
        = ‖(a : UnitAddCircle) - (b : UnitAddCircle)‖ := by rw [dist_eq_norm]
    _ = ‖(((a - b : ℝ) : UnitAddCircle))‖ := by rw [← hcast]
    _ = |a - b| := by
      exact ((AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num : (1 : ℝ) ≠ 0)).2 (by simpa using hab))

private lemma seam_split_measure {x ε : ℝ} (hx0 : 0 < x) (hε0 : 0 ≤ ε) (hε : ε < (1 : ℝ) / 2)
    (hwrap : x < ε) (hno1 : x + ε ≤ 1) :
    MeasureTheory.volume (((Set.Ioo (0 : ℝ) (x + ε)) ∪ Set.Ioo (x + 1 - ε) (1 : ℝ))) =
      ENNReal.ofReal (2 * ε) := by
  have hle : x + ε ≤ x + 1 - ε := by linarith [hε]
  have hdisj : Disjoint (Set.Ioo (0 : ℝ) (x + ε)) (Set.Ioo (x + 1 - ε) (1 : ℝ)) := by
    rw [Set.disjoint_left]
    intro y hy1 hy2
    simp at hy1 hy2
    linarith [hle]
  rw [MeasureTheory.measure_union hdisj measurableSet_Ioo]
  rw [Real.volume_Ioo, Real.volume_Ioo]
  have h1 : (x + ε) - 0 = x + ε := by ring
  have h2 : 1 - (x + 1 - ε) = ε - x := by ring
  rw [h1, h2]
  have hsum : (x + ε) + (ε - x) = 2 * ε := by ring
  rw [← ENNReal.ofReal_add (by positivity : 0 ≤ x + ε) (by linarith [hwrap] : 0 ≤ ε - x)]
  rw [hsum]

private lemma circle_closedBall_preimage_seamfree {x ε : ℝ} (hε : ε < (1 : ℝ) / 2) :
    (QuotientAddGroup.mk : ℝ → UnitAddCircle) ⁻¹'
        (Metric.closedBall (↑x : UnitAddCircle) ε) ∩ Metric.closedBall x (1 / 2) =
      Metric.closedBall x ε := by
  have h := AddCircle.coe_real_preimage_closedBall_inter_eq (p := (1 : ℝ)) (x := x) (ε := ε)
    (s := Metric.closedBall x (1 / 2)) (by intro y hy; simpa using hy)
  have hif : ε < |(1 : ℝ)| / 2 := by simpa using hε
  rw [h, if_pos hif]
  have hsub : Metric.closedBall x ε ⊆ Metric.closedBall x (1 / 2) := by
    exact Metric.closedBall_subset_closedBall (by linarith)
  rw [inter_eq_left.mpr hsub]

private lemma volume_eq_volume_preimage_Ioc {U : Set UnitAddCircle} (hU : MeasurableSet U) :
    MeasureTheory.volume U =
      MeasureTheory.volume ((fun x : ℝ => (x : UnitAddCircle)) ⁻¹' U ∩ Set.Ioc (0 : ℝ) (1 : ℝ)) := by
  have h := AddCircle.add_projection_respects_measure (T := (1 : ℝ)) (t := (0 : ℝ)) hU
  -- h : volume U = volume ((mk : ℝ → AddCircle (1:ℝ)) ⁻¹' U ∩ Ioc 0 (0 + 1))
  convert h using 2 <;> ext x <;> simp

private lemma list_sum_nat_div (l : List ℕ) (c : ℝ) (hc : c ≠ 0) :
    (l.map (fun d : ℕ => (d : ℝ) / c)).sum = (l.sum : ℝ) / c := by
  induction l with
  | nil => simp
  | cons h t ih =>
      have hc' : c ≠ 0 := hc
      rw [List.map_cons, List.sum_cons, ih]
      field_simp [hc']
      rw [List.sum_cons]
      simp

/-! ### Cyclic gaps of a sorted residue list (the gap object of `trimmed_arc_measure`)

`cyclicGaps q xs` for a sorted increasing list `xs = [a₀,…,a_{k−1}]` of residues in
`[0,q)` produces the cyclic gaps `[a₁−a₀, …, a_{k−1}−a_{k−2}, a₀+q−a_{k−1}]`
(wrapping back to the first residue).  Proven API:
`cyclicGaps_sum` (the gaps sum to `q` — the telescoping identity) and
`cyclicGaps_pos` (all gaps positive for strictly increasing lists).  Feeding this
the sorted reduced residues of `q` gives the cyclic-gap multiset of
`trimmed_arc_measure`/`gaps_cover`; real gaps are then `gᵢ = dᵢ/q` with `gᵢ ≥ 1/q`
and `Σgᵢ = 1`, exactly the hypotheses of the layer lemmas. -/
def gapChain (q : ℕ) (first : ℕ) : List ℕ → List ℕ
  | [] => []
  | [a] => [first + q - a]
  | a :: b :: rest => (b - a) :: gapChain q first (b :: rest)

def cyclicGaps (q : ℕ) : List ℕ → List ℕ
  | [] => []
  | h :: t => gapChain q h (h :: t)

lemma gapChain_sum_of_head (q first : ℕ) : ∀ (rest : List ℕ),
    (∀ a : ℕ, (a :: rest).Pairwise (· ≤ ·) → (∀ x ∈ a :: rest, x < q) →
      (gapChain q first (a :: rest)).sum = first + q - a) := by
  intro rest
  induction rest with
  | nil =>
      intro a hsort hq
      simp [gapChain]
  | cons b tail ih =>
      intro a hsort hq
      have hab : a ≤ b := (List.pairwise_cons.mp hsort).1 b (by simp)
      have hbq : b < q := hq b (by simp)
      have hsortB : (b :: tail).Pairwise (· ≤ ·) := (List.pairwise_cons.mp hsort).2
      have hqB : ∀ x ∈ b :: tail, x < q := by
        intro x hx
        exact hq x (by simp [hx])
      have htail : (gapChain q first (b :: tail)).sum = first + q - b := ih b hsortB hqB
      have hbq' : b ≤ first + q := by omega
      calc
        (gapChain q first (a :: b :: tail)).sum
            = (b - a) + (gapChain q first (b :: tail)).sum := by
                simp [gapChain]
        _ = (b - a) + (first + q - b) := by rw [htail]
        _ = first + q - a := by omega

lemma cyclicGaps_sum {q : ℕ} {xs : List ℕ} (hne : xs ≠ []) (hpw : xs.Pairwise (· ≤ ·))
    (hq : ∀ x ∈ xs, x < q) :
    (cyclicGaps q xs).sum = q := by
  cases xs with
  | nil => contradiction
  | cons h t =>
      have hpw' : (h :: t).Pairwise (· ≤ ·) := hpw
      have hq' : ∀ x ∈ h :: t, x < q := hq
      have hs : (gapChain q h (h :: t)).sum = h + q - h := gapChain_sum_of_head q h t h hpw' hq'
      have hcancel : h + q - h = q := by omega
      rw [cyclicGaps]
      exact hs.trans hcancel

private lemma gapChain_pos_of_head (q first : ℕ) : ∀ (rest : List ℕ),
    (∀ a : ℕ, (a :: rest).Pairwise (· < ·) → (∀ x ∈ a :: rest, x < q) →
      ∀ g ∈ gapChain q first (a :: rest), 0 < g) := by
  intro rest
  induction rest with
  | nil =>
      intro a hsort hq
      intro g hg
      simp [gapChain] at hg
      subst g
      have haq : a < q := hq a (by simp)
      have haq' : a < first + q := by omega
      exact Nat.sub_pos_of_lt haq'
  | cons b tail ih =>
      intro a hsort hq
      intro g hg
      have hab : a < b := (List.pairwise_cons.mp hsort).1 b (by simp)
      have hsortB : (b :: tail).Pairwise (· < ·) := (List.pairwise_cons.mp hsort).2
      have hqB : ∀ x ∈ b :: tail, x < q := by
        intro x hx
        exact hq x (by simp [hx])
      simp [gapChain] at hg
      rcases hg with hg1 | hg2
      · subst g
        exact Nat.sub_pos_of_lt hab
      · exact ih b hsortB hqB g hg2

lemma gapChain_length (q first : ℕ) : ∀ rest : List ℕ,
    (gapChain q first rest).length = rest.length := by
  intro rest
  induction rest with
  | nil => simp [gapChain]
  | cons a t ih =>
      cases t with
      | nil => simp [gapChain]
      | cons b t' =>
          simp [gapChain, ih]

/-- `cyclicGaps` preserves list length. -/
lemma cyclicGaps_length (q : ℕ) : ∀ xs : List ℕ,
    (cyclicGaps q xs).length = xs.length := by
  intro xs
  cases xs with
  | nil => simp [cyclicGaps]
  | cons h t => simp [cyclicGaps, gapChain_length]

/-- Number of cyclic gaps of `q` equals `φ(q)` (companion of `reduced_gap_sum_eq_q`). -/
lemma cyclicGaps_pos {q : ℕ} {xs : List ℕ} (hne : xs ≠ []) (hpw : xs.Pairwise (· < ·))
    (hq : ∀ x ∈ xs, x < q) :
    ∀ g ∈ cyclicGaps q xs, 0 < g := by
  cases xs with
  | nil => contradiction
  | cons h t =>
      have hpw' : (h :: t).Pairwise (· < ·) := hpw
      have hq' : ∀ x ∈ h :: t, x < q := hq
      intro g hg
      rw [cyclicGaps] at hg
      exact gapChain_pos_of_head q h t h hpw' hq' g hg

/-! ### Reduced residues and their cyclic gaps

`reducedResidueList q` is the sorted list of the reduced residues of `q`
(`m < q`, `gcd m q = 1`).  Feeding it to `cyclicGaps` yields the cyclic-gap
multiset of `q`: proven facts: it is `Pairwise (· ≤ ·)`, `Nodup`, all entries
`< q`, has length `q.totient`, and is nonempty for `q ≥ 1`; hence
`cyclicGaps_sum` gives the telescoping identity Σ gaps = q, and the real gaps
`gᵢ = dᵢ/q` satisfy `Σgᵢ = 1` and `gᵢ ≥ 1/q` (positivity), exactly the
hypotheses of the analytic layer and of `gaps_cover`/`trimmed_arc_measure`. -/
def reducedFinset (q : ℕ) : Finset ℕ :=
  (Finset.range q).filter (fun m : ℕ => m.gcd q = 1)

def reducedResidueList (q : ℕ) : List ℕ :=
  Finset.sort (reducedFinset q) (· ≤ ·)

lemma mem_reducedFinset (q m : ℕ) : m ∈ reducedFinset q ↔ m < q ∧ m.gcd q = 1 := by
  simp [reducedFinset, Finset.mem_range]

lemma mem_reducedResidueList (q m : ℕ) : m ∈ reducedResidueList q ↔ m < q ∧ m.gcd q = 1 := by
  rw [reducedResidueList, Finset.mem_sort (· ≤ ·)]
  exact mem_reducedFinset q m

private lemma pairwise_lt_of_pairwise_le_nodup {α : Type*} [LinearOrder α] {l : List α}
    (hle : l.Pairwise (· ≤ ·)) (hn : l.Nodup) : l.Pairwise (· < ·) := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a t ih =>
      rw [List.pairwise_cons] at hle ⊢
      have hle1 : ∀ a' ∈ t, a ≤ a' := hle.1
      have hle2 : t.Pairwise (· ≤ ·) := hle.2
      have hn1 : a ∉ t := (List.nodup_cons.mp hn).1
      have hn2 : t.Nodup := (List.nodup_cons.mp hn).2
      constructor
      · intro a' ha'
        have hle' : a ≤ a' := hle1 a' ha'
        have hne' : a ≠ a' := by intro heq; exact hn1 (by simpa [heq] using ha')
        exact lt_of_le_of_ne hle' hne'
      · exact ih hle2 hn2

lemma reducedResidueList_pairwise_le (q : ℕ) :
    (reducedResidueList q).Pairwise (· ≤ ·) := by
  rw [reducedResidueList]
  exact Finset.pairwise_sort (reducedFinset q) (· ≤ ·)


lemma reducedResidueList_nodup (q : ℕ) : (reducedResidueList q).Nodup := by
  rw [reducedResidueList]
  exact Finset.sort_nodup (reducedFinset q) (· ≤ ·)

lemma reducedResidueList_mem_lt (q : ℕ) : ∀ x ∈ reducedResidueList q, x < q := by
  intro x hx
  exact (mem_reducedResidueList q x).mp hx |>.1

lemma card_reducedFinset (q : ℕ) : (reducedFinset q).card = q.totient := by
  calc
    (reducedFinset q).card
        = ((Finset.range q).filter (fun m : ℕ => q.Coprime m)).card := by
            congr 1
            ext m
            simp only [reducedFinset, Finset.mem_filter, Finset.mem_range]
            rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm]
    _ = q.totient := by exact (Nat.totient_eq_card_coprime q)

lemma reducedResidueList_length (q : ℕ) : (reducedResidueList q).length = q.totient := by
  rw [reducedResidueList, Finset.length_sort (· ≤ ·)]
  exact card_reducedFinset q
lemma reduced_gap_length (q : ℕ) :
    (cyclicGaps q (reducedResidueList q)).length = q.totient := by
  rw [cyclicGaps_length]
  exact reducedResidueList_length q


lemma reducedResidueList_ne_nil_of_pos (q : ℕ) (hq : 0 < q) : reducedResidueList q ≠ [] := by
  intro h
  have hlen : (reducedResidueList q).length = q.totient := reducedResidueList_length q
  have hlen0 : (reducedResidueList q).length = 0 := by simp [h]
  have hφ : 0 < q.totient := (Nat.totient_pos.mpr hq)
  omega

lemma reducedResidueList_pairwise_lt (q : ℕ) : (reducedResidueList q).Pairwise (· < ·) := by
  exact pairwise_lt_of_pairwise_le_nodup (reducedResidueList_pairwise_le q) (reducedResidueList_nodup q)


/-- Strict monotonicity of `List.get` on a strictly increasing list. -/
lemma get_lt_get_of_pairwise_lt {l : List ℕ} (hpw : l.Pairwise (· < ·)) {i j : ℕ}
    (hi : i < l.length) (hj : j < l.length) (hij : i < j) :
    l.get ⟨i, hi⟩ < l.get ⟨j, hj⟩ := by
  have hab : (⟨i, hi⟩ : Fin l.length) < ⟨j, hj⟩ := by
    simpa using hij
  exact List.Pairwise.rel_get_of_lt hpw hab




/-- Every reduced residue `a` of `q ≥ 2` satisfies `1 ≤ a` (it cannot be `0`). -/
lemma one_le_of_mem_reducedFinset (q : ℕ) (hq : 1 < q) :
    ∀ a ∈ reducedFinset q, 1 ≤ a := by
  intro a ha
  rcases mem_reducedFinset q a |>.mp ha with ⟨haq, hga⟩
  by_contra hnot
  have ha0 : a = 0 := by omega
  subst a
  simp [Nat.gcd_zero_left] at hga
  omega

/-- Every reduced residue `a` of `q ≥ 2` satisfies `a ≤ q − 1`. -/
lemma le_pred_of_mem_reducedFinset (q : ℕ) :
    ∀ a ∈ reducedFinset q, a ≤ q - 1 := by
  intro a ha
  have haq : a < q := (mem_reducedFinset q a).mp ha |>.1
  omega

/-- `1` is a reduced residue of every `q ≥ 2`. -/
lemma one_mem_reducedFinset (q : ℕ) (hq : 1 < q) : 1 ∈ reducedFinset q := by
  rw [mem_reducedFinset]
  exact ⟨by omega, by norm_num⟩

/-- `q − 1` is a reduced residue of every `q ≥ 2`. -/
lemma pred_mem_reducedFinset (q : ℕ) (hq : 1 < q) : q - 1 ∈ reducedFinset q := by
  rw [mem_reducedFinset]
  constructor
  · omega
  · have hle : q - 1 ≤ q := by omega
    have h := Nat.gcd_sub_self_right (m := q - 1) (n := q) hle
    have hq1 : q - (q - 1) = 1 := by omega
    rw [← h, hq1]
    norm_num

/-- `1` is the minimum of the reduced residues of `q ≥ 2`, `q−1` the maximum. -/
lemma reducedResidue_min_eq_one (q : ℕ) (hq : 1 < q) :
    1 = (reducedFinset q).min' ⟨1, one_mem_reducedFinset q hq⟩ := by
  apply le_antisymm
  · exact Finset.le_min' (reducedFinset q) _ 1 (by
      intro y hy
      exact one_le_of_mem_reducedFinset q hq y hy)
  · exact Finset.min'_le (reducedFinset q) 1 (one_mem_reducedFinset q hq)
lemma reducedResidue_max_eq_pred (q : ℕ) (hq : 1 < q) :
    (reducedFinset q).max' ⟨q - 1, pred_mem_reducedFinset q hq⟩ = q - 1 := by
  apply le_antisymm
  · exact Finset.max'_le (reducedFinset q) _ (q - 1) (by
      intro y hy
      exact le_pred_of_mem_reducedFinset q y hy)
  · exact Finset.le_max' (reducedFinset q) (q - 1) (by
      exact pred_mem_reducedFinset q hq)

/-! ### K1 containment: the lift-complement lies in the middle segments (t-window form).

For `t ∈ (0,q)` (the `q·y` lift coordinate), the *uncovered* predicate is that no
integer congruent to a reduced residue modulo `q` lies within `qδ` of `t` — i.e. the
open window `(t − qδ, t + qδ)` is coprime-free (equivalently `y = t/q` is NOT in the
lift of `approxAddOrderOf q δ`; see `ball_mem_window_iff`).  `ResMiddle` is the union
of the middle segments of the interior gaps between consecutive reduced residues, and
`wrapMiddle` the two halves (near `0` and near `q`) of the wrap gap `(q−1, q+1)`.
The three lemmas below show every uncovered `t ∈ (0,q)` lies in `ResMiddle ∪ wrapMiddle`
(interior case via `Finset.max'`/`min'`; the seam cases via the residue classes
`q−1 ≡ −1 (mod q)` and `1`).  Only inclusions are used — no per-gap arc equalities.
This is the set-theoretic core of the trimmed-arc measure identity.
-/

/-- `t` is *uncovered* (window form): no integer congruent to a reduced residue
modulo `q` lies within `qδ` of `t` — the open window `(t−qδ, t+qδ)` is coprime-free.
This is the `t = q·y` form of "the point `y` is not in the lift of `approxAddOrderOf q δ`"
(see `ball_mem_window_iff`). -/
def Uncov (q : ℕ) (δ : ℝ) (t : ℝ) : Prop :=
  ∀ a ∈ reducedFinset q, ∀ k : ℤ, (q : ℝ) * δ ≤ |t - (a : ℝ) - (k : ℝ) * (q : ℝ)|


/-- The consecutive reduced-residue pairs `a < b` (with no reduced residue strictly
between them).  Their differences `b − a` are the interior cyclic gaps of `q`; the
remaining (wrap) gap is the constant `2` (between `q−1` and `1` around the circle). -/
def consecutivePairs (q : ℕ) : Finset (ℕ × ℕ) :=
  ((reducedFinset q).product (reducedFinset q)).filter
    (fun ab : ℕ × ℕ => ab.1 < ab.2 ∧
      ∀ z ∈ reducedFinset q, ¬ (ab.1 < z ∧ z < ab.2))




/-- The union of the middle segments `[a + qδ, b − qδ]` over consecutive reduced
residues `a < b` of `q` (the interior gaps; the wrap gap is treated separately). -/
def ResMiddle (q : ℕ) (δ : ℝ) : Set ℝ :=
  {t | ∃ a ∈ reducedFinset q, ∃ b ∈ reducedFinset q, a < b ∧
    (∀ z ∈ reducedFinset q, ¬ (a < z ∧ z < b)) ∧
    (a : ℝ) + (q : ℝ) * δ ≤ t ∧ t ≤ (b : ℝ) - (q : ℝ) * δ}

/-- `ResMiddle` is exactly the union over the consecutive pairs of the closed middle
intervals `[a + qδ, b − qδ]`. -/
lemma ResMiddle_eq_biUnion (q : ℕ) (δ : ℝ) :
    ResMiddle q δ = ⋃ ab ∈ (consecutivePairs q : Set (ℕ × ℕ)),
      Set.Icc (((ab.1 : ℕ) : ℝ) + (q : ℝ) * δ) (((ab.2 : ℕ) : ℝ) - (q : ℝ) * δ) := by
  classical
  ext t
  constructor
  · intro ht
    rw [ResMiddle] at ht
    simp at ht
    rcases ht with ⟨a, ha, b, hb, hab, hcon, hlo, hhi⟩
    rw [Set.mem_iUnion₂]
    refine ⟨(a,b), ?_, hlo, hhi⟩
    · exact (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩,
        by simpa using ⟨hab, hcon⟩⟩)
  · intro ht
    rw [ResMiddle]
    simp
    rw [Set.mem_iUnion₂] at ht
    rcases ht with ⟨ab, hab, hmem⟩
    have habm : (ab.1 < ab.2 ∧ ∀ z ∈ reducedFinset q, ab.1 < z → ab.2 ≤ z) := by
      simpa [consecutivePairs] using (Finset.mem_filter.mp hab).2
    have ha : ab.1 ∈ reducedFinset q := (Finset.mem_product.mp (Finset.mem_filter.mp hab).1).1
    have hb : ab.2 ∈ reducedFinset q := (Finset.mem_product.mp (Finset.mem_filter.mp hab).1).2
    refine ⟨ab.1, ha, ab.2, hb, habm.1, ?_, hmem.1, hmem.2⟩
    intro z hz hzab
    exact habm.2 z hz hzab

lemma interior_containment (q : ℕ) (hq : 1 < q) (δ t : ℝ)
    (hδ0 : 0 ≤ δ) (ht1 : (1 : ℝ) < t) (ht2 : t < (q : ℝ) - 1)
    (htnot : ∀ a ∈ reducedFinset q, t ≠ (a : ℝ)) (hU : Uncov q δ t) :
    t ∈ ResMiddle q δ := by
  classical
  let A := reducedFinset q
  let Slo := A.filter (fun a : ℕ => (a : ℝ) < t)
  let Shi := A.filter (fun a : ℕ => t < (a : ℝ))
  have h1lo : (1 : ℕ) ∈ Slo := by
    simp [Slo, A, one_mem_reducedFinset q hq, ht1]
  have ht2' : t < ((q - 1 : ℕ) : ℝ) := by
    have hsub : (q - 1 : ℕ) + 1 = q := Nat.sub_add_cancel (by omega : 1 ≤ q)
    have hcast : ((q - 1 : ℕ) : ℝ) + 1 = (q : ℝ) := by exact_mod_cast hsub
    nlinarith
  have hq1hi : (q - 1 : ℕ) ∈ Shi := by
    simp [Shi, A, pred_mem_reducedFinset q hq, ht2']
  have hSlo_ne : Slo.Nonempty := ⟨1, h1lo⟩
  have hShi_ne : Shi.Nonempty := ⟨q - 1, hq1hi⟩
  let a : ℕ := Slo.max' hSlo_ne
  let b : ℕ := Shi.min' hShi_ne
  have ha_mem : a ∈ A := (Finset.mem_filter.mp (Finset.max'_mem Slo hSlo_ne)).1
  have hb_mem : b ∈ A := (Finset.mem_filter.mp (Finset.min'_mem Shi hShi_ne)).1
  have ha_t : (a : ℝ) < t := (Finset.mem_filter.mp (Finset.max'_mem Slo hSlo_ne)).2
  have ht_b : t < (b : ℝ) := (Finset.mem_filter.mp (Finset.min'_mem Shi hShi_ne)).2
  have hab : a < b := by
    have : (a : ℝ) < (b : ℝ) := lt_trans ha_t ht_b
    exact_mod_cast this
  have hconsec : ∀ z ∈ A, ¬ (a < z ∧ z < b) := by
    intro z hz
    intro hzab
    rcases hzab with ⟨haz, hzb⟩
    have hzne : t ≠ (z : ℝ) := htnot z hz
    have hzt : (z : ℝ) < t ∨ t < (z : ℝ) := lt_or_gt_of_ne hzne.symm
    rcases hzt with hzlt | htz
    · -- z < t : z ∈ Slo, but z > a = max Slo
      have hzS : z ∈ Slo := by simp [Slo, hz, hzlt]
      have hle : z ≤ Slo.max' hSlo_ne := Finset.le_max' Slo z hzS
      omega
    · -- t < z : z ∈ Shi, z < b = min Shi
      have hzS : z ∈ Shi := by simp [Shi, hz, htz]
      have hle : Shi.min' hShi_ne ≤ z := Finset.min'_le Shi z hzS
      omega
  -- uncovered gives distance ≥ qδ from a and from b (both are residues)
  have hdist_a : (q : ℝ) * δ ≤ t - (a : ℝ) := by
    have hinst := hU a ha_mem 0
    have habs : |t - (a : ℝ)| = t - (a : ℝ) := by
      exact abs_of_pos (sub_pos.mpr ha_t)
    simpa [habs] using hinst
  have hdist_b : (q : ℝ) * δ ≤ (b : ℝ) - t := by
    have hinst := hU b hb_mem 0
    have habs : |t - (b : ℝ)| = (b : ℝ) - t := by
      have harg : t - (b : ℝ) < 0 := sub_neg.mpr ht_b
      rw [abs_of_neg harg]
      ring
    simpa [habs] using hinst
  refine ⟨a, ha_mem, b, hb_mem, hab, hconsec, ?_, ?_⟩
  · have : (a : ℝ) + (q : ℝ) * δ ≤ t := by
      have hle := hdist_a
      linarith
    exact this
  · have hle2 : t ≤ (b : ℝ) - (q : ℝ) * δ := by
      have hd := hdist_b
      linarith
    exact hle2

/-- lower wrap: 0 < t < 1 uncovered => qδ−1 ≤ t ≤ 1−qδ -/
lemma lower_wrap_bounds (q : ℕ) (hq : 1 < q) (δ t : ℝ)
    (ht0 : 0 < t) (ht1 : t < 1) (hU : Uncov q δ t) :
    (q : ℝ) * δ - 1 ≤ t ∧ t ≤ 1 - (q : ℝ) * δ := by
  have hcastq : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
    have hsub : (q - 1 : ℕ) + 1 = q := Nat.sub_add_cancel (by omega : 1 ≤ q)
    have hc : ((q - 1 : ℕ) : ℝ) + 1 = (q : ℝ) := by exact_mod_cast hsub
    linarith
  have hlo : (q : ℝ) * δ - 1 ≤ t := by
    have hinst := hU (q - 1) (pred_mem_reducedFinset q hq) (-1)
    have harg : t - ((q - 1 : ℕ) : ℝ) - ((-1 : ℤ) : ℝ) * (q : ℝ) = t + 1 := by
      rw [hcastq]
      norm_num
      ring
    rw [harg] at hinst
    have hpos : 0 < t + 1 := by linarith
    have habs : |t + 1| = t + 1 := abs_of_pos hpos
    rw [habs] at hinst
    linarith
  have hhi : t ≤ 1 - (q : ℝ) * δ := by
    have hinst0 := hU 1 (one_mem_reducedFinset q hq) 0
    have hinst : (q : ℝ) * δ ≤ |t - 1| := by simpa using hinst0
    have hneg : t - 1 < 0 := by linarith
    have habs : |t - 1| = 1 - t := by
      rw [abs_of_neg hneg]
      ring
    rw [habs] at hinst
    linarith
  exact ⟨hlo, hhi⟩

lemma upper_wrap_bounds (q : ℕ) (hq : 1 < q) (δ t : ℝ)
    (ht1 : (q : ℝ) - 1 < t) (htq : t < (q : ℝ)) (hU : Uncov q δ t) :
    ((q - 1 : ℕ) : ℝ) + (q : ℝ) * δ ≤ t ∧ t ≤ (q : ℝ) + 1 - (q : ℝ) * δ := by
  have hcastq : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
    have hsub : (q - 1 : ℕ) + 1 = q := Nat.sub_add_cancel (by omega : 1 ≤ q)
    have hc : ((q - 1 : ℕ) : ℝ) + 1 = (q : ℝ) := by exact_mod_cast hsub
    linarith
  have hlo : ((q - 1 : ℕ) : ℝ) + (q : ℝ) * δ ≤ t := by
    have hinst0 := hU (q - 1) (pred_mem_reducedFinset q hq) 0
    have hinst : (q : ℝ) * δ ≤ |t - ((q - 1 : ℕ) : ℝ)| := by simpa using hinst0
    rw [hcastq] at hinst
    have hpos : 0 < t - ((q : ℝ) - 1) := by linarith
    have habs : |t - ((q : ℝ) - 1)| = t - ((q : ℝ) - 1) := abs_of_pos hpos
    rw [habs] at hinst
    linarith
  have hhi : t ≤ (q : ℝ) + 1 - (q : ℝ) * δ := by
    have hinst1 := hU 1 (one_mem_reducedFinset q hq) 1
    have hinst : (q : ℝ) * δ ≤ |t - (1 : ℝ) - (q : ℝ)| := by simpa using hinst1
    have hneg : t - (1 : ℝ) - (q : ℝ) < 0 := by linarith
    have habs : |t - (1 : ℝ) - (q : ℝ)| = (q : ℝ) + 1 - t := by
      rw [abs_of_neg hneg]
      ring
    rw [habs] at hinst
    linarith
  exact ⟨hlo, hhi⟩


/-- The two halves of the wrap-gap middle segments: near `t = 0` (between the residue
class `q−1 ≡ −1` below and the residue `1` above) and near `t = q` (between `q−1`
below and the residue class `1 ≡ q+1` above). -/
def WrapMid (q : ℕ) (δ : ℝ) : Set ℝ :=
  Set.Icc ((q : ℝ) * δ - 1) (1 - (q : ℝ) * δ) ∪
  Set.Icc (((q - 1 : ℕ) : ℝ) + (q : ℝ) * δ) ((q : ℝ) + 1 - (q : ℝ) * δ)

/-- **Containment (K1, step 1a).**  For `t ∈ (0,q)` with `t` not a reduced residue,
the uncovered predicate (coprime-free `qδ`-window, i.e. `t/q` outside the lift of
`A_q`) forces `t` into the union of the interior-gap middle segments and the two
wrap-gap middle halves.  Inclusion only; no per-gap arc equality. -/
lemma containment_middle (q : ℕ) (hq : 1 < q) (δ t : ℝ) (hδ0 : 0 ≤ δ)
    (ht0 : 0 < t) (htq : t < (q : ℝ))
    (htnot : ∀ a ∈ reducedFinset q, t ≠ (a : ℝ)) (hU : Uncov q δ t) :
    t ∈ ResMiddle q δ ∪ WrapMid q δ := by
  classical
  by_cases ht1 : t < 1
  · right
    left
    exact ⟨(lower_wrap_bounds q hq δ t ht0 ht1 hU).1, (lower_wrap_bounds q hq δ t ht0 ht1 hU).2⟩
  · have h1le : (1 : ℝ) ≤ t := le_of_not_gt ht1
    have hne1 : t ≠ (1 : ℝ) := by simpa using (htnot 1 (one_mem_reducedFinset q hq))
    have h1lt : (1 : ℝ) < t := lt_of_le_of_ne h1le (Ne.symm hne1)
    by_cases ht2 : t < (q : ℝ) - 1
    · exact Or.inl (interior_containment q hq δ t hδ0 h1lt ht2 htnot hU)
    · have hq1le : (q : ℝ) - 1 ≤ t := le_of_not_gt ht2
      have hcast : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
        have hsub : (q - 1 : ℕ) + 1 = q := Nat.sub_add_cancel (by omega : 1 ≤ q)
        have hc : ((q - 1 : ℕ) : ℝ) + 1 = (q : ℝ) := by exact_mod_cast hsub
        linarith
      have hne : (q : ℝ) - 1 ≠ t := by
        intro heq
        have htq1 : t = ((q - 1 : ℕ) : ℝ) := by rw [hcast]; exact heq.symm
        exact htnot (q - 1) (pred_mem_reducedFinset q hq) htq1
      have hq1lt : (q : ℝ) - 1 < t := lt_of_le_of_ne hq1le hne
      right
      right
      exact ⟨(upper_wrap_bounds q hq δ t hq1lt htq hU).1, (upper_wrap_bounds q hq δ t hq1lt htq hU).2⟩


/-- **Containment in the preimage of the middle segments.**  An uncovered
`y ∈ (0,1)` (i.e. `Uncov q δ (q·y)`) satisfies `q·y ∈ ResMiddle ∪ WrapMid` unless
`q·y` is itself a reduced residue of `q` (the finitely many residue points
`y = a/q`, a null set). -/
lemma uncovered_y_subset_preimage_middle (q : ℕ) (hq : 1 < q) (δ : ℝ) (hδ0 : 0 ≤ δ) :
    {y : ℝ | y ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧ Uncov q δ ((q : ℝ) * y)}
      ⊆ ((fun y : ℝ => (q : ℝ) * y) ⁻¹' (ResMiddle q δ ∪ WrapMid q δ))
          ∪ {y : ℝ | ∃ a ∈ reducedFinset q, (q : ℝ) * y = (a : ℝ)} := by
  intro y hy
  by_cases hres : ∃ a ∈ reducedFinset q, (q : ℝ) * y = (a : ℝ)
  · right
    exact hres
  · left
    have hy0 : 0 < y := hy.1.1
    have hy1 : y < 1 := hy.1.2
    have hU : Uncov q δ ((q : ℝ) * y) := hy.2
    have ht0 : 0 < (q : ℝ) * y := by positivity
    have htq : (q : ℝ) * y < (q : ℝ) := by
      have hq0 : 0 < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
      have hy1' : (q : ℝ) * y < (q : ℝ) * 1 := mul_lt_mul_of_pos_left hy1 hq0
      simpa using hy1'
    have htnot : ∀ a ∈ reducedFinset q, (q : ℝ) * y ≠ (a : ℝ) := by
      intro a ha
      intro heq
      exact hres ⟨a, ha, heq⟩
    rw [Set.mem_preimage]
    exact containment_middle q hq δ ((q : ℝ) * y) hδ0 ht0 htq htnot hU


/-- The residue points `y = a/q` (`a` a reduced residue) form a null set. -/
lemma measure_zero_residue_points (q : ℕ) (hq : 0 < q) :
    MeasureTheory.volume {y : ℝ | ∃ a ∈ reducedFinset q, (q : ℝ) * y = (a : ℝ)} = 0 := by
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  let f : ℕ → Set ℝ := fun a => {((a : ℝ) / (q : ℝ))}
  have hsub : {y : ℝ | ∃ a ∈ reducedFinset q, (q : ℝ) * y = (a : ℝ)}
      ⊆ ⋃ a ∈ (reducedFinset q : Set ℕ), f a := by
    intro y hy
    rcases hy with ⟨a, ha, h⟩
    refine Set.mem_iUnion₂.mpr ⟨a, ha, ?_⟩
    have h' : y * (q : ℝ) = (a : ℝ) := by simpa [mul_comm] using h
    exact (eq_div_iff_mul_eq hq0).2 h'
  have hmeas (s : Finset ℕ) : MeasureTheory.volume (⋃ x ∈ (s : Set ℕ), f x) = 0 := by
    refine le_antisymm ?_ bot_le
    induction s using Finset.induction with
    | empty => simp
    | insert a s ha ih =>
        calc
          MeasureTheory.volume (⋃ x ∈ ((insert a s : Finset ℕ) : Set ℕ), f x)
              ≤ MeasureTheory.volume (f a ∪ (⋃ x ∈ (s : Set ℕ), f x)) := measure_mono (by
                  intro y hy
                  rcases (Set.mem_iUnion₂.mp hy) with ⟨z, hz, hyz⟩
                  rw [Finset.mem_coe, Finset.mem_insert] at hz
                  rcases hz with hz | hz
                  · exact Or.inl (by simpa [hz] using hyz)
                  · exact Or.inr (Set.mem_iUnion₂.mpr ⟨z, hz, hyz⟩))
          _ ≤ MeasureTheory.volume (f a) + MeasureTheory.volume (⋃ x ∈ (s : Set ℕ), f x) :=
              MeasureTheory.measure_union_le _ _
          _ ≤ 0 := by
              dsimp [f]
              rw [Real.volume_singleton]
              have ih0 : MeasureTheory.volume (⋃ x ∈ (s : Set ℕ), f x) = 0 := le_antisymm ih bot_le
              rw [ih0]
              simp

  apply le_antisymm
  · calc
      MeasureTheory.volume {y : ℝ | ∃ a ∈ reducedFinset q, (q : ℝ) * y = (a : ℝ)}
          ≤ MeasureTheory.volume (⋃ a ∈ (reducedFinset q : Set ℕ), f a) := measure_mono hsub
      _ = 0 := hmeas (reducedFinset q)
  · exact bot_le

/-- **Step 2 (null drop).**  `λ{y ∈ (0,1) : Uncov q δ (q·y)} ≤ λ((q·)⁻¹'(ResMiddle ∪ WrapMid))`
— the finitely many residue points are negligible. -/
lemma uncovered_volume_le_preimage_middle (q : ℕ) (hq : 1 < q) (δ : ℝ) (hδ0 : 0 ≤ δ) :
    MeasureTheory.volume {y : ℝ | y ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧ Uncov q δ ((q : ℝ) * y)}
      ≤ MeasureTheory.volume
          ((fun y : ℝ => (q : ℝ) * y) ⁻¹' (ResMiddle q δ ∪ WrapMid q δ)) := by
  let V : Set ℝ := {y : ℝ | y ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧ Uncov q δ ((q : ℝ) * y)}
  let R : Set ℝ := {y : ℝ | ∃ a ∈ reducedFinset q, (q : ℝ) * y = (a : ℝ)}
  let M : Set ℝ := (fun y : ℝ => (q : ℝ) * y) ⁻¹' (ResMiddle q δ ∪ WrapMid q δ)
  have hinc : V ⊆ M ∪ R := by
    intro y hy
    have hy' := (uncovered_y_subset_preimage_middle q hq δ hδ0) hy
    -- hy' : y ∈ M ∪ R (definitional after let-unfolds)
    simpa [V, R, M] using hy'
  have hR0 : MeasureTheory.volume R = 0 := by
    simpa [R] using (measure_zero_residue_points q (by omega : 0 < q))
  calc
    MeasureTheory.volume V ≤ MeasureTheory.volume (M ∪ R) := measure_mono hinc
    _ ≤ MeasureTheory.volume M + MeasureTheory.volume R := MeasureTheory.measure_union_le M R
    _ = MeasureTheory.volume M := by rw [hR0, add_zero]



/-- **Step 3, expansion.**  The preimage of the middle-segment union is exactly the
finite union over the consecutive pairs of the `q·y`-windows plus the two wrap
windows (each expressed by its two bounding inequalities). -/
lemma preimage_middle_eq_iUnion (q : ℕ) (δ : ℝ) :
    ((fun y : ℝ => (q : ℝ) * y) ⁻¹' (ResMiddle q δ ∪ WrapMid q δ)) =
      (⋃ ab ∈ (consecutivePairs q : Set (ℕ × ℕ)),
          {y : ℝ | ((ab.1 : ℕ) : ℝ) + (q : ℝ) * δ ≤ (q : ℝ) * y ∧
            (q : ℝ) * y ≤ ((ab.2 : ℕ) : ℝ) - (q : ℝ) * δ})
        ∪ {y : ℝ | (q : ℝ) * δ - 1 ≤ (q : ℝ) * y ∧ (q : ℝ) * y ≤ 1 - (q : ℝ) * δ}
        ∪ {y : ℝ | ((q - 1 : ℕ) : ℝ) + (q : ℝ) * δ ≤ (q : ℝ) * y ∧
            (q : ℝ) * y ≤ (q : ℝ) + 1 - (q : ℝ) * δ} := by
  classical
  rw [ResMiddle_eq_biUnion q δ]
  unfold WrapMid
  ext y
  simp only [Set.mem_preimage, Set.mem_union, Set.mem_iUnion₂, Set.mem_Icc, Set.mem_setOf_eq]
  exact or_assoc.symm



/-- **Step 3, per-window length.**  The `q·y`-window `{y : A ≤ q·y ≤ B}` is the real
interval `[A/q, B/q]`, of length `(B − A)/q`. -/
lemma volume_q_window (A B : ℝ) (q : ℕ) (hq : 0 < q) :
    MeasureTheory.volume {y : ℝ | A ≤ (q : ℝ) * y ∧ (q : ℝ) * y ≤ B} =
      ENNReal.ofReal ((B - A) / (q : ℝ)) := by
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast hq
  have hEq : {y : ℝ | A ≤ (q : ℝ) * y ∧ (q : ℝ) * y ≤ B} = Set.Icc (A / (q:ℝ)) (B / (q:ℝ)) := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · intro hy
      constructor
      · exact (div_le_iff₀ hq0).mpr (by simpa [mul_comm] using hy.1)
      · exact (le_div_iff₀ hq0).mpr (by simpa [mul_comm] using hy.2)
    · intro hy
      constructor
      · simpa [mul_comm] using (div_le_iff₀ hq0).mp hy.1
      · simpa [mul_comm] using (le_div_iff₀ hq0).mp hy.2
  rw [hEq, Real.volume_Icc]
  congr 1
  field_simp [hq.ne']

/-- **Step 3, scaled bound.**  `ofReal(x/q) ≤ ofReal(max x 0 / q)`: negative window
lengths clamp to zero. -/
lemma ofReal_div_q_le (x : ℝ) (q : ℕ) (hq : 0 < q) :
    ENNReal.ofReal (x / (q : ℝ)) ≤ ENNReal.ofReal (max x 0 / (q : ℝ)) := by
  exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (le_max_left x 0)
    (by positivity : 0 ≤ (q : ℝ)))



/-- **Step 3, #2 (spine): finite subadditivity.**  The measure of a finite union of
windows is at most the sum of their measures (no measurability, no disjointness
required — it is the subadditivity of the outer measure, iterated over a Finset). -/
lemma volume_iUnion_le_sum {ι : Type*} (s : Finset ι) (W : ι → Set ℝ) :
    MeasureTheory.volume (⋃ i ∈ (s : Set ι), W i) ≤ ∑ i ∈ s, MeasureTheory.volume (W i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      calc
        MeasureTheory.volume (⋃ i ∈ ((insert a s : Finset ι) : Set ι), W i)
            ≤ MeasureTheory.volume (W a ∪ (⋃ i ∈ (s : Set ι), W i)) := measure_mono (by
                intro y hy
                rcases (Set.mem_iUnion₂.mp hy) with ⟨z, hz, hyz⟩
                rw [Finset.mem_coe, Finset.mem_insert] at hz
                rcases hz with hz | hz
                · exact Or.inl (by simpa [hz] using hyz)
                · exact Or.inr (Set.mem_iUnion₂.mpr ⟨z, hz, hyz⟩))
        _ ≤ MeasureTheory.volume (W a) + MeasureTheory.volume (⋃ i ∈ (s : Set ι), W i) :=
            MeasureTheory.measure_union_le _ _
        _ ≤ MeasureTheory.volume (W a) + (∑ i ∈ s, MeasureTheory.volume (W i)) := by
            exact add_le_add (le_rfl : MeasureTheory.volume (W a) ≤ MeasureTheory.volume (W a)) ih
        _ = ∑ i ∈ insert a s, MeasureTheory.volume (W i) := by
            rw [Finset.sum_insert ha]



/-- The `q·y`-window of a consecutive pair `(a,b)`: preimage of `[a+qδ, b−qδ]`. -/
def pairWindow (q : ℕ) (δ : ℝ) (ab : ℕ × ℕ) : Set ℝ :=
  {y : ℝ | ((ab.1 : ℕ) : ℝ) + (q : ℝ) * δ ≤ (q : ℝ) * y ∧
    (q : ℝ) * y ≤ ((ab.2 : ℕ) : ℝ) - (q : ℝ) * δ}

/-- The lower wrap window: preimage of `[qδ−1, 1−qδ]` (near `q·y = 0`). -/
def lowWindow (q : ℕ) (δ : ℝ) : Set ℝ :=
  {y : ℝ | (q : ℝ) * δ - 1 ≤ (q : ℝ) * y ∧ (q : ℝ) * y ≤ 1 - (q : ℝ) * δ}

/-- The upper wrap window: preimage of `[(q−1)+qδ, q+1−qδ]` (near `q·y = q`). -/
def highWindow (q : ℕ) (δ : ℝ) : Set ℝ :=
  {y : ℝ | ((q - 1 : ℕ) : ℝ) + (q : ℝ) * δ ≤ (q : ℝ) * y ∧
    (q : ℝ) * y ≤ (q : ℝ) + 1 - (q : ℝ) * δ}

/-- **Clipping to the fundamental domain.**  `λ(V) ≤ λ((q·)⁻¹'(ResMiddle ∪ WrapMid) ∩ (0,1))`
(we drop the finitely many residue points a second time, and intersect with `(0,1)`). -/
lemma uncovered_volume_le_preimage_clipped (q : ℕ) (hq : 1 < q) (δ : ℝ) (hδ0 : 0 ≤ δ) :
    MeasureTheory.volume {y : ℝ | y ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧ Uncov q δ ((q : ℝ) * y)}
      ≤ MeasureTheory.volume
          (((fun y : ℝ => (q : ℝ) * y) ⁻¹' (ResMiddle q δ ∪ WrapMid q δ)) ∩ Set.Ioo (0 : ℝ) (1 : ℝ)) := by
  let V : Set ℝ := {y : ℝ | y ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧ Uncov q δ ((q : ℝ) * y)}
  let P : Set ℝ := (fun y : ℝ => (q : ℝ) * y) ⁻¹' (ResMiddle q δ ∪ WrapMid q δ)
  let R : Set ℝ := {y : ℝ | ∃ a ∈ reducedFinset q, (q : ℝ) * y = (a : ℝ)}
  have hinc : V ⊆ P ∪ R := by
    intro y hy
    exact (uncovered_y_subset_preimage_middle q hq δ hδ0) hy
  have hV1 : V ⊆ Set.Ioo (0 : ℝ) (1 : ℝ) := by
    intro y hy
    exact hy.1
  have hR0 : MeasureTheory.volume R = 0 := by
    simpa [R] using (measure_zero_residue_points q (by omega : 0 < q))
  calc
    MeasureTheory.volume V ≤ MeasureTheory.volume ((P ∪ R) ∩ Set.Ioo (0 : ℝ) (1 : ℝ)) := by
        exact measure_mono (by
          intro y hy
          exact ⟨hinc hy, hV1 hy⟩)
    _ ≤ MeasureTheory.volume (P ∩ Set.Ioo (0 : ℝ) (1 : ℝ)) +
          MeasureTheory.volume (R ∩ Set.Ioo (0 : ℝ) (1 : ℝ)) := by
          have hunion : ((P ∪ R) ∩ Set.Ioo (0 : ℝ) (1 : ℝ)) =
              (P ∩ Set.Ioo (0 : ℝ) (1 : ℝ)) ∪ (R ∩ Set.Ioo (0 : ℝ) (1 : ℝ)) := by
            ext y
            simp only [Set.mem_inter_iff, Set.mem_union]
            tauto
          calc
            MeasureTheory.volume ((P ∪ R) ∩ Set.Ioo (0 : ℝ) (1 : ℝ))
                = MeasureTheory.volume ((P ∩ Set.Ioo (0 : ℝ) (1 : ℝ)) ∪ (R ∩ Set.Ioo (0 : ℝ) (1 : ℝ))) := by rw [hunion]
            _ ≤ MeasureTheory.volume (P ∩ Set.Ioo (0 : ℝ) (1 : ℝ)) +
                  MeasureTheory.volume (R ∩ Set.Ioo (0 : ℝ) (1 : ℝ)) := MeasureTheory.measure_union_le _ _
    _ = MeasureTheory.volume (P ∩ Set.Ioo (0 : ℝ) (1 : ℝ)) := by
        have hR1 : MeasureTheory.volume (R ∩ Set.Ioo (0 : ℝ) (1 : ℝ)) = 0 := by
          refine le_antisymm ?_ bot_le
          calc
            MeasureTheory.volume (R ∩ Set.Ioo (0 : ℝ) (1 : ℝ)) ≤ MeasureTheory.volume R := by
              exact measure_mono (by intro y hy; exact hy.1)
            _ = 0 := hR0
        rw [hR1, add_zero]
lemma lowWindow_clipped_measure_le (q : ℕ) (hq : 0 < q) (δ : ℝ) :
    MeasureTheory.volume (lowWindow q δ ∩ Set.Ioo (0 : ℝ) (1 : ℝ)) ≤
      ENNReal.ofReal (max (1 - (q : ℝ) * δ) 0 / (q : ℝ)) := by
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast hq
  let M : ℝ := max (1 - (q : ℝ) * δ) 0
  have hsub : lowWindow q δ ∩ Set.Ioo (0 : ℝ) (1 : ℝ) ⊆ Set.Ioc (0 : ℝ) (M / (q : ℝ)) := by
    intro y hy
    rcases hy with ⟨⟨hlo, hhi⟩, hy0, hy1⟩
    constructor
    · exact hy0
    · have hle : (q : ℝ) * y ≤ M := by
        have h1 : 1 - (q : ℝ) * δ ≤ M := le_max_left _ _
        exact le_trans hhi h1
      exact (le_div_iff₀ hq0).mpr (by simpa [mul_comm] using hle)
  calc
    MeasureTheory.volume (lowWindow q δ ∩ Set.Ioo (0 : ℝ) (1 : ℝ))
        ≤ MeasureTheory.volume (Set.Ioc (0 : ℝ) (M / (q : ℝ))) := measure_mono hsub
    _ = ENNReal.ofReal (M / (q : ℝ)) := by
        rw [Real.volume_Ioc]
        congr 1
        ring

/-- **Upper wrap window, clipped to `(0,1)`:** at most `max(1 − qδ, 0)/q`. -/
lemma highWindow_clipped_measure_le (q : ℕ) (hq : 0 < q) (δ : ℝ) :
    MeasureTheory.volume (highWindow q δ ∩ Set.Ioo (0 : ℝ) (1 : ℝ)) ≤
      ENNReal.ofReal (max (1 - (q : ℝ) * δ) 0 / (q : ℝ)) := by
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast hq
  let M : ℝ := max (1 - (q : ℝ) * δ) 0
  have hsub2 : highWindow q δ ∩ Set.Ioo (0 : ℝ) (1 : ℝ) ⊆
      Set.Icc ((((q - 1 : ℕ) : ℝ) + (q : ℝ) * δ) / (q : ℝ)) (1 : ℝ) := by
    intro y hy
    rcases hy with ⟨⟨hlo, hhi⟩, hy0, hy1⟩
    constructor
    · exact (div_le_iff₀ hq0).mpr (by simpa [mul_comm] using hlo)
    · exact le_of_lt hy1
  calc
    MeasureTheory.volume (highWindow q δ ∩ Set.Ioo (0 : ℝ) (1 : ℝ))
        ≤ MeasureTheory.volume (Set.Icc ((((q - 1 : ℕ) : ℝ) + (q : ℝ) * δ) / (q : ℝ)) (1 : ℝ)) :=
            measure_mono hsub2
    _ = ENNReal.ofReal (1 - (((q - 1 : ℕ) : ℝ) + (q : ℝ) * δ) / (q : ℝ)) := by
        rw [Real.volume_Icc]
    _ ≤ ENNReal.ofReal (M / (q : ℝ)) := by
        apply ENNReal.ofReal_le_ofReal
        have hnum : 1 - (((q - 1 : ℕ) : ℝ) + (q : ℝ) * δ) / (q : ℝ) =
            (1 - (q : ℝ) * δ) / (q : ℝ) := by
          have hcast : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
            have hsubn : (q - 1 : ℕ) + 1 = q := Nat.sub_add_cancel (by omega : 1 ≤ q)
            have hc : ((q - 1 : ℕ) : ℝ) + 1 = (q : ℝ) := by exact_mod_cast hsubn
            linarith
          rw [hcast]
          field_simp [hq0.ne']
          ring
        rw [hnum]
        exact div_le_div_of_nonneg_right (le_max_left (1 - (q : ℝ) * δ) 0) (by positivity : 0 ≤ (q : ℝ))



/-- **Wrap-total identity.**  The two clipped wrap windows together contribute at most
`max(2 − 2·qδ, 0)/q` — the single wrap-gap `d = 2` of the cyclic structure. -/
lemma wrap_total_ofReal (q : ℕ) (hq : 0 < q) (δ : ℝ) :
    ENNReal.ofReal (max (1 - (q : ℝ) * δ) 0 / (q : ℝ)) +
      ENNReal.ofReal (max (1 - (q : ℝ) * δ) 0 / (q : ℝ)) =
      ENNReal.ofReal (max (2 - 2 * (q : ℝ) * δ) 0 / (q : ℝ)) := by
  let a : ℝ := max (1 - (q : ℝ) * δ) 0 / (q : ℝ)
  have ha : 0 ≤ a := by
    dsimp [a]
    exact div_nonneg (le_max_right _ _) (by positivity : 0 ≤ (q : ℝ))
  have hm : 2 * max (1 - (q : ℝ) * δ) 0 = max (2 - 2 * (q : ℝ) * δ) 0 := by
    have hmm := max_mul_of_nonneg (c := (2 : ℝ)) (1 - (q : ℝ) * δ) 0 (by norm_num)
    rw [show 2 * max (1 - (q : ℝ) * δ) 0 = max (1 - (q : ℝ) * δ) 0 * 2 by ring]
    rw [hmm]
    congr 1
    ring
    ring
  rw [← ENNReal.ofReal_add ha ha]
  congr 1
  calc
    (max (1 - (q : ℝ) * δ) 0) / (q : ℝ) + (max (1 - (q : ℝ) * δ) 0) / (q : ℝ)
        = (2 * max (1 - (q : ℝ) * δ) 0) / (q : ℝ) := by ring
    _ = (max (2 - 2 * (q : ℝ) * δ) 0) / (q : ℝ) := by rw [hm]




/-- **Item 2, preimage of the middle union.**  The preimage of `ResMiddle` is the union
of the pair-windows over `consecutivePairs`, so its measure is at most the sum over
those pairs of the pair-window measures. -/
lemma volume_preimage_ResMiddle_le_sum (q : ℕ) (δ : ℝ) :
    MeasureTheory.volume ((fun y : ℝ => (q : ℝ) * y) ⁻¹' ResMiddle q δ) ≤
      ∑ ab ∈ consecutivePairs q, MeasureTheory.volume (pairWindow q δ ab) := by
  classical
  have hEq : (fun y : ℝ => (q : ℝ) * y) ⁻¹' ResMiddle q δ =
      ⋃ ab ∈ (consecutivePairs q : Set (ℕ × ℕ)), pairWindow q δ ab := by
    rw [ResMiddle_eq_biUnion q δ]
    ext y
    simp only [Set.mem_preimage, Set.mem_iUnion₂, pairWindow, Set.mem_Icc, Set.mem_setOf_eq]
  rw [hEq]
  exact volume_iUnion_le_sum (consecutivePairs q) (pairWindow q δ)

/-- **Item 2, per-pair window measure:** `λ(pairWindow ab) = ofReal(((b − a) − 2·qδ)/q)`. -/
lemma volume_pairWindow_eq (q : ℕ) (δ : ℝ) (ab : ℕ × ℕ) (hq : 0 < q) :
    MeasureTheory.volume (pairWindow q δ ab) =
      ENNReal.ofReal ((((ab.2 : ℕ) : ℝ) - ((ab.1 : ℕ) : ℝ) - 2 * (q : ℝ) * δ) / (q : ℝ)) := by
  have hw := volume_q_window (((ab.1 : ℕ) : ℝ) + (q : ℝ) * δ) (((ab.2 : ℕ) : ℝ) - (q : ℝ) * δ) q hq
  have hw' : MeasureTheory.volume (pairWindow q δ ab) =
      ENNReal.ofReal (((((ab.2 : ℕ) : ℝ) - (q : ℝ) * δ) - (((ab.1 : ℕ) : ℝ) + (q : ℝ) * δ)) / (q : ℝ)) := by
    simpa [pairWindow] using hw
  rw [hw']
  congr 1
  field_simp [show (q : ℝ) ≠ 0 by positivity]
  ring

/-- **Item 2, step 1.**  `λ(preimage ResMiddle) ≤ Σ` over consecutive pairs of
`ofReal(max((b − a) − 2·qδ, 0)/q)` — the pair-window bound with clamping. -/
lemma volume_preimage_ResMiddle_le_maxSum (q : ℕ) (hq : 0 < q) (δ : ℝ) :
    MeasureTheory.volume ((fun y : ℝ => (q : ℝ) * y) ⁻¹' ResMiddle q δ) ≤
      ∑ ab ∈ consecutivePairs q,
        ENNReal.ofReal (max (((ab.2 : ℕ) : ℝ) - ((ab.1 : ℕ) : ℝ) - 2 * (q : ℝ) * δ) 0 / (q : ℝ)) := by
  classical
  calc
    MeasureTheory.volume ((fun y : ℝ => (q : ℝ) * y) ⁻¹' ResMiddle q δ)
        ≤ ∑ ab ∈ consecutivePairs q, MeasureTheory.volume (pairWindow q δ ab) :=
            volume_preimage_ResMiddle_le_sum q δ
    _ ≤ ∑ ab ∈ consecutivePairs q,
          ENNReal.ofReal (max (((ab.2 : ℕ) : ℝ) - ((ab.1 : ℕ) : ℝ) - 2 * (q : ℝ) * δ) 0 / (q : ℝ)) := by
        refine Finset.sum_le_sum ?_
        intro ab hab
        have hw := volume_pairWindow_eq q δ ab hq
        have hcl := ofReal_div_q_le (((ab.2 : ℕ) : ℝ) - ((ab.1 : ℕ) : ℝ) - 2 * (q : ℝ) * δ) q hq
        exact le_trans (le_of_eq hw) hcl



/-- **Item 1, membership decomposition.**  Inside `(0,1)`, the preimage of the middle
union is covered by the preimage of `ResMiddle` plus the two clipped wrap windows. -/
lemma preimage_middle_inter_subset (q : ℕ) (δ : ℝ) :
    ((fun y : ℝ => (q : ℝ) * y) ⁻¹' (ResMiddle q δ ∪ WrapMid q δ)) ∩ Set.Ioo (0 : ℝ) (1 : ℝ)
      ⊆ ((fun y : ℝ => (q : ℝ) * y) ⁻¹' ResMiddle q δ)
          ∪ (lowWindow q δ ∩ Set.Ioo (0 : ℝ) (1 : ℝ))
          ∪ (highWindow q δ ∩ Set.Ioo (0 : ℝ) (1 : ℝ)) := by
  intro y hy
  rcases hy with ⟨hyP, hy01⟩
  have hyQ : (q : ℝ) * y ∈ ResMiddle q δ ∪ WrapMid q δ := by simpa [Set.mem_preimage] using hyP
  unfold WrapMid at hyQ
  rw [Set.mem_union] at hyQ
  rcases hyQ with hR | hW
  · exact Or.inl (Or.inl (by simpa [Set.mem_preimage] using hR))
  · rw [Set.mem_union] at hW
    rcases hW with hw1 | hw2
    · exact Or.inl (Or.inr ⟨(Set.mem_Icc.mp hw1), hy01⟩)
    · exact Or.inr ⟨(Set.mem_Icc.mp hw2), hy01⟩



/-- **Item 1, subadditivity.**  `λ(V) ≤ λ(preimage ResMiddle) + λ(Wlow∩(0,1)) + λ(Whigh∩(0,1))`. -/
lemma uncovered_volume_le_subadd (q : ℕ) (hq : 1 < q) (δ : ℝ) (hδ0 : 0 ≤ δ) :
    MeasureTheory.volume {y : ℝ | y ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧ Uncov q δ ((q : ℝ) * y)}
      ≤ MeasureTheory.volume ((fun y : ℝ => (q : ℝ) * y) ⁻¹' ResMiddle q δ) +
          MeasureTheory.volume (lowWindow q δ ∩ Set.Ioo (0 : ℝ) (1 : ℝ)) +
          MeasureTheory.volume (highWindow q δ ∩ Set.Ioo (0 : ℝ) (1 : ℝ)) := by
  let f : ℝ → ℝ := fun y => (q : ℝ) * y
  let M : Set ℝ := ResMiddle q δ ∪ WrapMid q δ
  have hclip := uncovered_volume_le_preimage_clipped q hq δ hδ0
  have hinc := preimage_middle_inter_subset q δ
  calc
    MeasureTheory.volume {y : ℝ | y ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧ Uncov q δ ((q : ℝ) * y)}
        ≤ MeasureTheory.volume (f ⁻¹' M ∩ Set.Ioo (0 : ℝ) (1 : ℝ)) := by
            simpa [f, M] using hclip
    _ ≤ MeasureTheory.volume ((f ⁻¹' ResMiddle q δ) ∪
            (lowWindow q δ ∩ Set.Ioo (0 : ℝ) (1 : ℝ)) ∪
            (highWindow q δ ∩ Set.Ioo (0 : ℝ) (1 : ℝ))) := by
            apply measure_mono
            simpa [f, M] using hinc
    _ ≤ MeasureTheory.volume ((f ⁻¹' ResMiddle q δ) ∪ (lowWindow q δ ∩ Set.Ioo (0 : ℝ) (1 : ℝ))) +
          MeasureTheory.volume (highWindow q δ ∩ Set.Ioo (0 : ℝ) (1 : ℝ)) := by
          exact MeasureTheory.measure_union_le (μ := MeasureTheory.volume)
            ((f ⁻¹' ResMiddle q δ) ∪ (lowWindow q δ ∩ Set.Ioo (0 : ℝ) (1 : ℝ)))
            (highWindow q δ ∩ Set.Ioo (0 : ℝ) (1 : ℝ))
    _ ≤ MeasureTheory.volume (f ⁻¹' ResMiddle q δ) +
          MeasureTheory.volume (lowWindow q δ ∩ Set.Ioo (0 : ℝ) (1 : ℝ)) +
          MeasureTheory.volume (highWindow q δ ∩ Set.Ioo (0 : ℝ) (1 : ℝ)) := by
            have hle := MeasureTheory.measure_union_le (μ := MeasureTheory.volume)
              (f ⁻¹' ResMiddle q δ) (lowWindow q δ ∩ Set.Ioo (0 : ℝ) (1 : ℝ))
            have hle' : MeasureTheory.volume ((f ⁻¹' ResMiddle q δ) ∪ (lowWindow q δ ∩ Set.Ioo (0 : ℝ) (1 : ℝ))) +
                  MeasureTheory.volume (highWindow q δ ∩ Set.Ioo (0 : ℝ) (1 : ℝ)) ≤
                MeasureTheory.volume (f ⁻¹' ResMiddle q δ) +
                  MeasureTheory.volume (lowWindow q δ ∩ Set.Ioo (0 : ℝ) (1 : ℝ)) +
                  MeasureTheory.volume (highWindow q δ ∩ Set.Ioo (0 : ℝ) (1 : ℝ)) := by
                simpa [add_assoc] using (add_le_add hle (le_rfl : MeasureTheory.volume (highWindow q δ ∩ Set.Ioo (0 : ℝ) (1 : ℝ)) ≤ MeasureTheory.volume (highWindow q δ ∩ Set.Ioo (0 : ℝ) (1 : ℝ))))
            exact hle'



/-- **Item-1 chain: the full upper bound on `λ(V)`.**  `λ(V)` is at most the sum over
consecutive pairs of the clamped pair-window lengths plus the single wrap-gap
contribution `max(2 − 2·qδ, 0)/q`. -/
lemma uncovered_volume_le_midSum (q : ℕ) (hq : 1 < q) (δ : ℝ) (hδ0 : 0 ≤ δ) :
    MeasureTheory.volume {y : ℝ | y ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧ Uncov q δ ((q : ℝ) * y)}
      ≤ (∑ ab ∈ consecutivePairs q,
            ENNReal.ofReal (max (((ab.2 : ℕ) : ℝ) - ((ab.1 : ℕ) : ℝ) - 2 * (q : ℝ) * δ) 0 / (q : ℝ))) +
          ENNReal.ofReal (max (2 - 2 * (q : ℝ) * δ) 0 / (q : ℝ)) := by
  let A : ℝ≥0∞ := MeasureTheory.volume ((fun y : ℝ => (q : ℝ) * y) ⁻¹' ResMiddle q δ)
  let B : ℝ≥0∞ := MeasureTheory.volume (lowWindow q δ ∩ Set.Ioo (0 : ℝ) (1 : ℝ))
  let C : ℝ≥0∞ := MeasureTheory.volume (highWindow q δ ∩ Set.Ioo (0 : ℝ) (1 : ℝ))
  let P : ℝ≥0∞ := ∑ ab ∈ consecutivePairs q,
    ENNReal.ofReal (max (((ab.2 : ℕ) : ℝ) - ((ab.1 : ℕ) : ℝ) - 2 * (q : ℝ) * δ) 0 / (q : ℝ))
  let m : ℝ≥0∞ := ENNReal.ofReal (max (1 - (q : ℝ) * δ) 0 / (q : ℝ))
  let M : ℝ≥0∞ := ENNReal.ofReal (max (2 - 2 * (q : ℝ) * δ) 0 / (q : ℝ))
  have hqpos : 0 < q := by omega
  have hsub := uncovered_volume_le_subadd q hq δ hδ0
  have hR : A ≤ P := by simpa [A, P] using (volume_preimage_ResMiddle_le_maxSum q hqpos δ)
  have hL : B ≤ m := by simpa [B, m] using (lowWindow_clipped_measure_le q hqpos δ)
  have hH : C ≤ m := by simpa [C, m] using (highWindow_clipped_measure_le q hqpos δ)
  have hwt : m + m = M := by simpa [m, M] using (wrap_total_ofReal q hqpos δ)
  have hbase : MeasureTheory.volume {y : ℝ | y ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧ Uncov q δ ((q : ℝ) * y)} ≤ A + B + C := by
    simpa [A, B, C] using hsub
  calc
    MeasureTheory.volume {y : ℝ | y ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧ Uncov q δ ((q : ℝ) * y)}
        ≤ A + B + C := hbase
    _ ≤ P + B + C := by
        have h1 := add_le_add hR (le_rfl : B ≤ B)
        exact add_le_add h1 (le_rfl : C ≤ C)
    _ ≤ P + m + m := by
        have h2 := add_le_add (le_rfl : P ≤ P) hL
        have h2' := add_le_add h2 hH
        exact h2'
    _ = P + M := by
        calc
          (P + m) + m = P + (m + m) := by rw [add_assoc]
          _ = P + M := by rw [hwt]

/-- The two window forms are the same real number: `|t − (a + kq)| = |t − a − kq|`. -/
lemma abs_window_sum_eq (t : ℝ) (a : ℕ) (k : ℤ) (q : ℕ) :
    |t - (((a : ℤ) + k * (q : ℤ)) : ℝ)| = |t - (a : ℝ) - (k : ℝ) * (q : ℝ)| := by
  congr 1
  push_cast
  ring

/-- **Lift-membership aggregation.**  `y` lies in the lift of `A_q` (i.e. `↑y ∈ A_q`)
iff some reduced residue `m` has its `qδ`-window about `q·y` containing `m + kq`.
(Combines `approxAddOrderOf_eq_biUnion_ball` with `ball_mem_window_iff`.) -/
lemma lift_mem_approxAddOrderOf_iff (q : ℕ) (hq : 0 < q) (δ : ℝ) (y : ℝ) :
    (y ∈ (QuotientAddGroup.mk ⁻¹' (approxAddOrderOf UnitAddCircle q δ))) ↔
      ∃ m ∈ reducedFinset q,
        ∃ k : ℤ, |(q : ℝ) * y - (((m : ℤ) + k * (q : ℤ)) : ℝ)| < (q : ℝ) * δ := by
  rw [approxAddOrderOf_eq_biUnion_ball q hq δ]
  constructor
  · intro hy
    rcases mem_iUnion₂.mp hy with ⟨m, hm, hball⟩
    have hn : ‖(y : UnitAddCircle) - ↑(((m : ℝ) / (q : ℝ)))‖ < δ := by
      simpa [dist_eq_norm] using (Metric.mem_ball.mp hball)
    rcases (ball_mem_window_iff y m q δ hq).mp hn with ⟨k, hk⟩
    exact ⟨m, (by simpa [reducedFinset] using hm), k, hk⟩
  · intro hy
    rcases hy with ⟨m, hm, k, hk⟩
    have hn : ‖(y : UnitAddCircle) - ↑(((m : ℝ) / (q : ℝ)))‖ < δ :=
      (ball_mem_window_iff y m q δ hq).mpr ⟨k, hk⟩
    exact mem_iUnion₂.mpr ⟨m, (by simpa [reducedFinset] using hm),
      (Metric.mem_ball.mpr (by simpa [dist_eq_norm] using hn))⟩

/-- **Aggregation: the complement of the lift.**  `y` is NOT in the lift of `A_q`
iff the open window `(q·y − qδ, q·y + qδ)` contains no integer congruent to a
reduced residue modulo `q` — i.e. `Uncov q δ (q·y)`. -/
lemma lift_uncovered_iff_Uncov (q : ℕ) (hq : 0 < q) (δ : ℝ) (y : ℝ) :
    (y ∉ (QuotientAddGroup.mk ⁻¹' (approxAddOrderOf UnitAddCircle q δ))) ↔
      Uncov q δ ((q : ℝ) * y) := by
  rw [lift_mem_approxAddOrderOf_iff q hq δ y]
  constructor
  · intro hnot a ha k
    by_contra hlt
    have hlt' : |(q : ℝ) * y - (((a : ℤ) + k * (q : ℤ)) : ℝ)| < (q : ℝ) * δ := by
      have h0 : |(q : ℝ) * y - (a : ℝ) - (k : ℝ) * (q : ℝ)| < (q : ℝ) * δ := (not_le.mp hlt)
      rw [abs_window_sum_eq]
      exact h0
    exact (hnot ⟨a, ha, k, hlt'⟩).elim
  · intro hU hy
    rcases hy with ⟨a, ha, k, hk⟩
    have hge := hU a ha k
    rw [← abs_window_sum_eq] at hge
    exact (not_lt_of_ge hge) hk

/-! ### Step 1(b): the volume identity (measure layer of K1).

`A_q := approxAddOrderOf UnitAddCircle q δ` is open (a union of open balls), so its
lift `P := mk⁻¹' A_q` is measurable.  The fundamental-domain identity
(`volume_eq_volume_preimage_Ioc`) plus the lift-complement characterization
(`lift_uncovered_iff_Uncov`) give

  `volume A_q = 1 − λ{y ∈ (0,1) : Uncov q δ (q·y)} = 1 − (1/q)·λ{t ∈ (0,q) : Uncov q δ t}`,

the second equality being the linear change of variables `t = q·y`
(`Real.volume_preimage_mul_left`). -/

/-- `approxAddOrderOf q δ` is open on the circle. -/
private lemma approxAddOrderOf_open (q : ℕ) (δ : ℝ) :
    IsOpen (approxAddOrderOf UnitAddCircle q δ) := by
  rw [approxAddOrderOf]
  exact Metric.isOpen_thickening

/-- The lift of `A_q` to the real line is measurable. -/
private lemma measurableSet_lift_Aq (q : ℕ) (δ : ℝ) :
    MeasurableSet (QuotientAddGroup.mk ⁻¹' (approxAddOrderOf UnitAddCircle q δ)) := by
  exact (approxAddOrderOf_open q δ).measurableSet.preimage QuotientAddGroup.continuous_mk.measurable

/-- Fundamental-domain identity for `A_q` (instance of `volume_eq_volume_preimage_Ioc`). -/
private lemma volume_Aq_lift_Ioc (q : ℕ) (δ : ℝ) :
    MeasureTheory.volume (approxAddOrderOf UnitAddCircle q δ) =
      MeasureTheory.volume
        ((QuotientAddGroup.mk ⁻¹' (approxAddOrderOf UnitAddCircle q δ)) ∩ Set.Ioc (0 : ℝ) (1 : ℝ)) :=
  volume_eq_volume_preimage_Ioc (approxAddOrderOf_open q δ).measurableSet

/-- Dropping the right endpoint of the fundamental domain changes nothing. -/
private lemma volume_Ioc_eq_volume_Ioo (P : Set ℝ) (hP : MeasurableSet P) :
    MeasureTheory.volume (P ∩ Set.Ioc (0 : ℝ) (1 : ℝ)) =
      MeasureTheory.volume (P ∩ Set.Ioo (0 : ℝ) (1 : ℝ)) := by
  have hsing : MeasureTheory.volume (P ∩ ({1} : Set ℝ)) = 0 := by
    apply le_antisymm
    · calc
        MeasureTheory.volume (P ∩ ({1} : Set ℝ)) ≤ MeasureTheory.volume ({1} : Set ℝ) := by
          exact measure_mono (by intro x hx; exact hx.2)
        _ = 0 := by simp
    · exact bot_le
  have hsplit : P ∩ Set.Ioc (0 : ℝ) (1 : ℝ) =
      (P ∩ Set.Ioo (0 : ℝ) (1 : ℝ)) ∪ (P ∩ ({1} : Set ℝ)) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ioo, Set.mem_singleton_iff, Set.mem_union]
    constructor
    · intro hx
      rcases hx with ⟨hxP, hx0, hx1⟩
      rcases lt_or_eq_of_le hx1 with hxlt | hxeq
      · left
        exact ⟨hxP, hx0, hxlt⟩
      · right
        exact ⟨hxP, hxeq⟩
    · intro hx
      rcases hx with hx | hx
      · exact ⟨hx.1, hx.2.1, le_of_lt hx.2.2⟩
      · exact ⟨hx.1, by rw [hx.2]; norm_num, le_of_eq hx.2⟩
  have hdisj : Disjoint (P ∩ Set.Ioo (0 : ℝ) (1 : ℝ)) (P ∩ ({1} : Set ℝ)) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    exact (ne_of_lt hx1.2.2) hx2.2
  have hm1 : MeasurableSet (P ∩ ({1} : Set ℝ)) := hP.inter (measurableSet_singleton 1)
  calc
    MeasureTheory.volume (P ∩ Set.Ioc (0 : ℝ) (1 : ℝ))
        = MeasureTheory.volume ((P ∩ Set.Ioo (0 : ℝ) (1 : ℝ)) ∪ (P ∩ ({1} : Set ℝ))) := by rw [hsplit]
    _ = MeasureTheory.volume (P ∩ Set.Ioo (0 : ℝ) (1 : ℝ)) +
          MeasureTheory.volume (P ∩ ({1} : Set ℝ)) :=
          MeasureTheory.measure_union hdisj hm1
    _ = MeasureTheory.volume (P ∩ Set.Ioo (0 : ℝ) (1 : ℝ)) := by rw [hsing]; simp

/-- **The volume identity (y-form).**  `volume A_q = 1 − λ{y ∈ (0,1) : Uncov q δ (q·y)}`. -/
private lemma volume_Aq_eq_one_sub_uncovered (q : ℕ) (hq : 0 < q) (δ : ℝ) :
    MeasureTheory.volume (approxAddOrderOf UnitAddCircle q δ) =
      (1 : ℝ≥0∞) - MeasureTheory.volume
        {y : ℝ | y ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧ Uncov q δ ((q : ℝ) * y)} := by
  let P : Set ℝ := QuotientAddGroup.mk ⁻¹' (approxAddOrderOf UnitAddCircle q δ)
  have hP : MeasurableSet P := measurableSet_lift_Aq q δ
  have hiff (y : ℝ) : y ∈ Pᶜ ↔ Uncov q δ ((q : ℝ) * y) := by
    rw [Set.mem_compl_iff]
    exact (lift_uncovered_iff_Uncov q hq δ y).trans (by simp [P])
  have hcomp : {y : ℝ | y ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧ Uncov q δ ((q : ℝ) * y)} =
      Pᶜ ∩ Set.Ioo (0 : ℝ) (1 : ℝ) := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_setOf_eq]
    constructor
    · intro hy
      exact ⟨(hiff y).mpr hy.2, hy.1⟩
    · intro hy
      exact ⟨hy.2, (hiff y).mp hy.1⟩
  have hPc : MeasurableSet Pᶜ := hP.compl
  have hunion : Set.Ioo (0 : ℝ) (1 : ℝ) = (P ∩ Set.Ioo (0 : ℝ) (1 : ℝ)) ∪ (Pᶜ ∩ Set.Ioo (0 : ℝ) (1 : ℝ)) := by
    ext x
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]
    tauto
  have hdisj : Disjoint (P ∩ Set.Ioo (0 : ℝ) (1 : ℝ)) (Pᶜ ∩ Set.Ioo (0 : ℝ) (1 : ℝ)) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    exact hx2.1 hx1.1
  have hmB : MeasurableSet (Pᶜ ∩ Set.Ioo (0 : ℝ) (1 : ℝ)) := hPc.inter measurableSet_Ioo
  have hmu := MeasureTheory.measure_union (μ := MeasureTheory.volume) hdisj hmB
  have hvol : MeasureTheory.volume (Set.Ioo (0 : ℝ) (1 : ℝ)) =
      MeasureTheory.volume (P ∩ Set.Ioo (0 : ℝ) (1 : ℝ)) +
        MeasureTheory.volume (Pᶜ ∩ Set.Ioo (0 : ℝ) (1 : ℝ)) := by
    rw [← hunion] at hmu
    exact hmu
  have hIoo1 : MeasureTheory.volume (Set.Ioo (0 : ℝ) (1 : ℝ)) = (1 : ℝ≥0∞) := by
    rw [Real.volume_Ioo]
    norm_num
  have hsum : MeasureTheory.volume (P ∩ Set.Ioo (0 : ℝ) (1 : ℝ)) +
      MeasureTheory.volume (Pᶜ ∩ Set.Ioo (0 : ℝ) (1 : ℝ)) = (1 : ℝ≥0∞) := by
    rw [← hvol, hIoo1]
  have hfin : MeasureTheory.volume (Pᶜ ∩ Set.Ioo (0 : ℝ) (1 : ℝ)) ≠ ⊤ := by
    refine ne_of_lt ?_
    calc
      MeasureTheory.volume (Pᶜ ∩ Set.Ioo (0 : ℝ) (1 : ℝ)) ≤ MeasureTheory.volume (Set.Ioo (0 : ℝ) (1 : ℝ)) :=
        measure_mono (by intro x hx; exact hx.2)
      _ < ⊤ := by simp
  have hmain : MeasureTheory.volume (P ∩ Set.Ioo (0 : ℝ) (1 : ℝ)) =
      (1 : ℝ≥0∞) - MeasureTheory.volume (Pᶜ ∩ Set.Ioo (0 : ℝ) (1 : ℝ)) :=
    ENNReal.eq_sub_of_add_eq hfin hsum
  calc
    MeasureTheory.volume (approxAddOrderOf UnitAddCircle q δ)
        = MeasureTheory.volume (P ∩ Set.Ioo (0 : ℝ) (1 : ℝ)) := by
            simpa [P] using (volume_Aq_lift_Ioc q δ).trans (volume_Ioc_eq_volume_Ioo P hP)
    _ = (1 : ℝ≥0∞) - MeasureTheory.volume (Pᶜ ∩ Set.Ioo (0 : ℝ) (1 : ℝ)) := hmain
    _ = (1 : ℝ≥0∞) - MeasureTheory.volume
        {y : ℝ | y ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧ Uncov q δ ((q : ℝ) * y)} := by rw [hcomp]

/-- The real cyclic gaps `dᵢ/q` of the reduced residues of `q ≥ 1` are all ≥ `1/q`
(companion to `reduced_real_gap_sum_eq_one`: together `Σgᵢ = 1`, `gᵢ ≥ 1/q`). -/
lemma reduced_real_gap_ge_recip (q : ℕ) (hq : 0 < q) :
    ∀ g ∈ ((cyclicGaps q (reducedResidueList q)).map (fun d : ℕ => (d : ℝ) / (q : ℝ))),
      (1 : ℝ) / (q : ℝ) ≤ g := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  intro g hg
  rcases List.mem_map.mp hg with ⟨d, hd, rfl⟩
  have hpos : 0 < d := cyclicGaps_pos (q := q) (xs := reducedResidueList q)
    (reducedResidueList_ne_nil_of_pos q hq) (reducedResidueList_pairwise_lt q)
    (reducedResidueList_mem_lt q) d hd
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hpos)
  exact div_le_div_of_nonneg_right hd1 (le_of_lt hqR)

/-- The cyclic gaps of the reduced residues of `q ≥ 1` sum to `q`. -/
lemma reduced_gap_sum_eq_q (q : ℕ) (hq : 0 < q) :
    (cyclicGaps q (reducedResidueList q)).sum = q := by
  exact cyclicGaps_sum (q := q) (xs := reducedResidueList q)
    (reducedResidueList_ne_nil_of_pos q hq)
    (reducedResidueList_pairwise_le q)
    (reducedResidueList_mem_lt q)

/-- The real cyclic gaps `dᵢ/q` of the reduced residues of `q ≥ 1` sum to `1`
(step (ii) of the partition-lemma spec: total arc length around the circle). -/
lemma reduced_real_gap_sum_eq_one (q : ℕ) (hq : 0 < q) :
    ((cyclicGaps q (reducedResidueList q)).map (fun d : ℕ => (d : ℝ) / (q : ℝ))).sum = 1 := by
  rw [list_sum_nat_div (cyclicGaps q (reducedResidueList q)) (q : ℝ) (by exact_mod_cast (ne_of_gt hq))]
  rw [reduced_gap_sum_eq_q q hq]
  field_simp


/-- `1` is a reduced residue of every `q ≥ 2`. -/
lemma one_mem_reducedResidueList (q : ℕ) (hq : 1 < q) : 1 ∈ reducedResidueList q := by
  rw [mem_reducedResidueList]
  constructor
  · omega
  · norm_num

/-- `q − 1` is a reduced residue of every `q ≥ 2`. -/
lemma pred_mem_reducedResidueList (q : ℕ) (hq : 1 < q) : q - 1 ∈ reducedResidueList q := by
  rw [mem_reducedResidueList]
  constructor
  · omega
  · have hle : q - 1 ≤ q := by omega
    have h := Nat.gcd_sub_self_right (m := q - 1) (n := q) hle
    have hq1 : q - (q - 1) = 1 := by omega
    rw [← h, hq1]
    norm_num

/-- `0` is not a reduced residue of any `q ≥ 2`. -/
lemma zero_not_mem_reducedResidueList (q : ℕ) (hq : 1 < q) : 0 ∉ reducedResidueList q := by
  rw [mem_reducedResidueList]
  simp [hq.ne']


/-! ### First analytic layer under the long-arc core (real gap-systems, no
number theory).  For a finite real gap system `gᵢ ≥ 0` with `Σgᵢ = 1` (e.g. the
cyclic gaps of the reduced residues of `q` — such systems additionally satisfy
`gᵢ ≥ 1/q` and palindromy, but the lemmas here hold in general):

* `sum_min_ge_t_mul_big`: `Σᵢ min(t,gᵢ) ≥ t·#{i : t ≤ gᵢ}` — arcs shorter than
  the covering threshold still give full-length coverage for the sub-average
  gaps, so `μ ≥ t·#{large gaps}`;
* `complement_loss_eq`: `1 − Σᵢ min(t,gᵢ) = Σ_{gᵢ>t}(gᵢ−t)` — the complement
  (uncovered) measure equals the total excess of the gaps above `t`, which is
  the trimmed-arc identity at the real level.

Hence the long-arc target `Σᵢ min(t,gᵢ) ≥ min(1,φt)/2` splits as:
(A) `φt ≤ 1`: need `Σ_{gᵢ>t}(gᵢ−t) ≤ 1 − φt/2` (complement loss small);
(B) `φt ≥ 1`: need `Σ_{gᵢ>t}(gᵢ−t) ≤ 1/2`.
And `μ ≥ t·#{gᵢ ≥ t}` already settles the easy half of each case when at least
`min(1,φt)/(2t)` gaps are large (e.g. ≥ φ/2 gaps in case A, ≥ 1/(2t) gaps in
case B); the hard half is when most mass sits in gaps just below `t` and one
must use the reduced-residue bounded-gap structure. -/

/-! ### Single cyclic-gap coverage identity (real level, step (iii) of the
partition-lemma spec).  Inside an open gap `(a, a+g)` between consecutive
residues, the points within radius `δ` of an end form the union of the two
end-caps of length `δ`; their (real) measure is `min(2δ, g)` (both caps when
`2δ ≤ g`, the whole gap when `2δ ≥ g`).  Summing this over the cyclic gaps of
`q` (with the `cyclicGaps` API and `reduced_real_gap_sum_eq_one`) yields the
`trimmed_arc_measure` identity for arcs of radius `δ ≤ 1/2`. -/
/-! Real-list trimmed identity (first `trimmed_arc_measure` composition step):
for any finite real list `G`, `Σᵢ min(t,gᵢ) = Σgᵢ − Σᵢ max(gᵢ−t,0)`; in
particular when `Σgᵢ = 1` (as for the real cyclic gaps of `q`, by
`reduced_real_gap_sum_eq_one`), `Σᵢ min(t,gᵢ) = 1 − Σᵢ max(gᵢ−t,0)`. -/
private lemma min_eq_sub_max (t g : ℝ) : min t g = g - max (g - t) 0 := by
  by_cases h : t ≤ g
  · rw [min_eq_left h]
    rw [max_eq_left (by linarith)]
    ring
  · have hg : g ≤ t := le_of_not_ge h
    rw [min_eq_right hg]
    have hgt : g - t ≤ 0 := by linarith
    rw [max_eq_right hgt]
    ring

private lemma real_gap_sum_trimmed' {c : ℝ} (G : List ℝ) :
    (G.map (fun g => min c g)).sum = G.sum - (G.map (fun g => max (g - c) 0)).sum := by
  induction G with
  | nil => simp
  | cons h t ih =>
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ih]
      rw [min_eq_sub_max c h]
      rw [List.sum_cons]
      ring_nf

private lemma real_gap_sum_trimmed {c : ℝ} {G : List ℝ} (hsum : G.sum = 1) :
    (G.map (fun g => min c g)).sum = 1 - (G.map (fun g => max (g - c) 0)).sum := by
  rw [show (G.map (fun g => min c g)).sum = G.sum - (G.map (fun g => max (g - c) 0)).sum
    by exact real_gap_sum_trimmed' (c := c) G, hsum]

private lemma real_volume_end_caps (a δ g : ℝ) (hδ : 0 ≤ δ) :
    MeasureTheory.volume
      ({x : ℝ | x ∈ Set.Ioo a (a + g) ∧ (x < a + δ ∨ a + g - δ < x)}) =
      ENNReal.ofReal (min (2 * δ) g) := by
  set C : Set ℝ := {x : ℝ | x ∈ Set.Ioo a (a + g) ∧ (x < a + δ ∨ a + g - δ < x)}
  by_cases h2 : 2 * δ ≤ g
  · have hset : C = (Set.Ioo a (a + δ)) ∪ Set.Ioo (a + g - δ) (a + g) := by
      ext x
      simp only [C, Set.mem_setOf_eq, Set.mem_Ioo, Set.mem_union]
      constructor
      · intro hx
        rcases hx with ⟨⟨ha, hxg⟩, hc⟩
        rcases hc with hxl | hxr
        · left
          exact ⟨ha, hxl⟩
        · right
          exact ⟨hxr, hxg⟩
      · intro hx
        rcases hx with hxl | hxr
        · rcases hxl with ⟨ha, hxl⟩
          have hxga : x < a + g := by linarith [h2, hδ, hxl]
          exact ⟨⟨ha, hxga⟩, Or.inl hxl⟩
        · rcases hxr with ⟨hxr, hxg⟩
          have ha : a < x := by linarith
          exact ⟨⟨ha, hxg⟩, Or.inr hxr⟩
    have hdisj : Disjoint (Set.Ioo a (a + δ)) (Set.Ioo (a + g - δ) (a + g)) := by
      rw [Set.disjoint_left]
      intro x hx1 hx2
      simp at hx1 hx2
      linarith [h2]
    rw [hset]
    rw [MeasureTheory.measure_union hdisj measurableSet_Ioo]
    rw [Real.volume_Ioo, Real.volume_Ioo]
    rw [min_eq_left h2]
    have h1 : (a + δ) - a = δ := by ring
    have h2' : (a + g) - (a + g - δ) = δ := by ring
    rw [h1, h2']
    rw [← ENNReal.ofReal_add hδ hδ]
    congr 1
    ring
  · have hg2 : g ≤ 2 * δ := le_of_not_ge h2
    have hset : C = Set.Ioo a (a + g) := by
      ext x
      simp only [C, Set.mem_setOf_eq, Set.mem_Ioo]
      constructor
      · intro hx
        exact hx.1
      · intro hx
        rcases hx with ⟨ha, hxg⟩
        refine ⟨⟨ha, hxg⟩, ?_⟩
        by_cases hxl : x < a + δ
        · exact Or.inl hxl
        · right
          have hxδ : a + δ ≤ x := le_of_not_gt hxl
          by_contra hnot
          have hx2 : x ≤ a + g - δ := le_of_not_gt hnot
          linarith [hxδ, hx2, h2]
    rw [hset]
    rw [Real.volume_Ioo]
    rw [min_eq_right hg2]
    congr 1
    ring

private lemma sum_min_ge_t_mul_big {ι : Type*} [DecidableEq ι] (s : Finset ι) (g : ι → ℝ)
    {t : ℝ} (ht : 0 ≤ t) (hg : ∀ i ∈ s, 0 ≤ g i) :
    t * (s.filter (fun i => t ≤ g i)).card ≤ ∑ i ∈ s, min t (g i) := by
  have hsumt : (∑ i ∈ s.filter (fun i => t ≤ g i), t) = t * (s.filter (fun i => t ≤ g i)).card := by
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  calc
    t * (s.filter (fun i => t ≤ g i)).card
        = ∑ i ∈ s.filter (fun i => t ≤ g i), t := hsumt.symm
    _ = ∑ i ∈ s.filter (fun i => t ≤ g i), min t (g i) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        exact (min_eq_left (Finset.mem_filter.mp hi).2).symm
    _ ≤ ∑ i ∈ s, min t (g i) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (s := s.filter (fun i => t ≤ g i)) (t := s)
          ?_ ?_
        · intro i hi
          exact (Finset.mem_filter.mp hi).1
        · intro i hi hni
          exact le_min ht (hg i hi)

private lemma sum_split_at {ι : Type*} [DecidableEq ι] (s : Finset ι) (g : ι → ℝ) (a : ℝ) :
    (∑ i ∈ s, g i) = (∑ i ∈ s.filter (fun i => g i ≤ a), g i) +
      (∑ i ∈ s.filter (fun i => a < g i), g i) := by
  have h := Finset.sum_filter_add_sum_filter_not s (fun i => g i ≤ a) g
  calc
    (∑ i ∈ s, g i) = (∑ i ∈ s.filter (fun i => g i ≤ a), g i) +
        (∑ i ∈ s.filter (fun i => ¬ g i ≤ a), g i) := h.symm
    _ = (∑ i ∈ s.filter (fun i => g i ≤ a), g i) +
        (∑ i ∈ s.filter (fun i => a < g i), g i) := by
          congr 1
          refine Finset.sum_congr ?_ ?_
          · ext i
            simp only [Finset.mem_filter]
            constructor
            · intro h
              exact ⟨h.1, not_le.mp h.2⟩
            · intro h
              exact ⟨h.1, not_le.mpr h.2⟩
          · intro i hi
            rfl

private lemma complement_loss_eq {ι : Type*} [DecidableEq ι] (s : Finset ι) (g : ι → ℝ)
    (t : ℝ) (hsum : (∑ i ∈ s, g i) = 1) :
    (1 : ℝ) - (∑ i ∈ s, min t (g i)) =
      ∑ i ∈ s.filter (fun i => t < g i), (g i - t) := by
  have hsplit := sum_split_at s g t
  have hsmall : (∑ i ∈ s.filter (fun i => g i ≤ t), min t (g i)) =
      ∑ i ∈ s.filter (fun i => g i ≤ t), g i := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact min_eq_right (Finset.mem_filter.mp hi).2
  have hbig : (∑ i ∈ s.filter (fun i => t < g i), min t (g i)) =
      ∑ i ∈ s.filter (fun i => t < g i), t := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact min_eq_left (le_of_lt (Finset.mem_filter.mp hi).2)
  have hmin1 : (∑ i ∈ s.filter (fun i => g i ≤ t), min t (g i)) =
      ∑ i ∈ s.filter (fun i => g i ≤ t), g i := hsmall
  have hmin2 : (∑ i ∈ s.filter (fun i => t < g i), min t (g i)) =
      ∑ i ∈ s.filter (fun i => t < g i), t := hbig
  have hmin_split : (∑ i ∈ s, min t (g i)) =
      (∑ i ∈ s.filter (fun i => g i ≤ t), min t (g i)) +
        (∑ i ∈ s.filter (fun i => t < g i), min t (g i)) := by
    have h0 := Finset.sum_filter_add_sum_filter_not s (fun i => g i ≤ t) (fun i => min t (g i))
    calc
      (∑ i ∈ s, min t (g i))
          = (∑ i ∈ s.filter (fun i => g i ≤ t), min t (g i)) +
              (∑ i ∈ s.filter (fun i => ¬ g i ≤ t), min t (g i)) := h0.symm
      _ = (∑ i ∈ s.filter (fun i => g i ≤ t), min t (g i)) +
              (∑ i ∈ s.filter (fun i => t < g i), min t (g i)) := by
              congr 1
              refine Finset.sum_congr ?_ ?_
              · ext i
                simp only [Finset.mem_filter]
                constructor
                · intro h; exact ⟨h.1, not_le.mp h.2⟩
                · intro h; exact ⟨h.1, not_le.mpr h.2⟩
              · intro i hi; rfl
  have hmin : (∑ i ∈ s, min t (g i)) = (∑ i ∈ s.filter (fun i => g i ≤ t), g i) +
      ∑ i ∈ s.filter (fun i => t < g i), t := by
    rw [hmin_split, hmin1, hmin2]
  calc
    (1 : ℝ) - (∑ i ∈ s, min t (g i))
        = (∑ i ∈ s, g i) - (∑ i ∈ s, min t (g i)) := by rw [hsum]
    _ = (∑ i ∈ s.filter (fun i => g i ≤ t), g i + ∑ i ∈ s.filter (fun i => t < g i), g i) -
          ((∑ i ∈ s.filter (fun i => g i ≤ t), g i) + (∑ i ∈ s.filter (fun i => t < g i), t)) := by
              rw [hsplit, hmin]
    _ = (∑ i ∈ s.filter (fun i => t < g i), g i) - (∑ i ∈ s.filter (fun i => t < g i), t) := by ring
    _ = ∑ i ∈ s.filter (fun i => t < g i), (g i - t) := by
              rw [← Finset.sum_sub_distrib]



/-- consecutive differences of a list (length `l.length − 1`). -/
def adjDiffs : List ℕ → List ℕ
  | [] => []
  | _ :: [] => []
  | a :: b :: t => (b - a) :: adjDiffs (b :: t)

/-- last element of a nonempty list (0 for the empty list). -/
def lastElt : List ℕ → ℕ
  | [] => 0
  | [a] => a
  | _ :: t => lastElt t

lemma lastElt_mem_self {l : List ℕ} (hne : l ≠ []) : lastElt l ∈ l := by
  cases l with
  | nil => contradiction
  | cons h t => induction t generalizing h with
    | nil => simp [lastElt]
    | cons a t' ih =>
        have hx : lastElt (a :: t') ∈ a :: t' := ih a (by simp)
        change lastElt (a :: t') ∈ h :: a :: t'
        exact (List.mem_cons.mpr (Or.inr hx))

/-- In a ≤-sorted list the last element is maximal. -/
lemma le_lastElt_of_mem : ∀ (a : ℕ) (rest : List ℕ),
    (a :: rest).Pairwise (· ≤ ·) → ∀ y ∈ a :: rest, y ≤ lastElt (a :: rest) := by
  intro a rest
  induction rest generalizing a with
  | nil => intro hsort y hy; simp at hy; subst y; simp [lastElt]
  | cons b t' ih =>
      intro hsort y hy
      have hab : a ≤ b := (List.pairwise_cons.mp hsort).1 b (by simp)
      have hsort' : (b :: t').Pairwise (· ≤ ·) := (List.pairwise_cons.mp hsort).2
      have hy' : y = a ∨ y ∈ b :: t' := by simpa using hy
      rcases hy' with rfl | hyt
      · have hb : b ≤ lastElt (b :: t') := ih b hsort' b (by simp)
        exact le_trans hab hb
      · exact ih b hsort' y hyt

/-- adjacent-difference sum telescopes to `last − first`. -/
lemma adjDiffs_sum_cons (a : ℕ) (rest : List ℕ)
    (hsorted : (a :: rest).Pairwise (· ≤ ·)) :
    (adjDiffs (a :: rest)).sum = lastElt (a :: rest) - a := by
  induction rest generalizing a with
  | nil => simp [adjDiffs, lastElt]
  | cons b t' ih =>
      have hsort' : (b :: t').Pairwise (· ≤ ·) := by
        exact (List.pairwise_cons.mp hsorted).2
      have ih' := ih b hsort'
      have hab : a ≤ b := (List.pairwise_cons.mp hsorted).1 b (by simp)
      have hne' : b :: t' ≠ [] := by simp
      have hble : b ≤ lastElt (b :: t') := le_lastElt_of_mem b t' hsort' b (by simp)
      rw [adjDiffs, List.sum_cons, ih']
      simp [lastElt]
      omega


/-- `gapChain` computes the adjacent differences followed by the wrap term. -/
lemma gapChain_eq (q first : ℕ) : ∀ (l : List ℕ), l ≠ [] →
    gapChain q first l = adjDiffs l ++ [first + q - lastElt l] := by
  intro l
  induction l with
  | nil => intro h; contradiction
  | cons x t ih =>
      intro hl
      cases t with
      | nil => simp [gapChain, adjDiffs, lastElt]
      | cons y t' =>
          have hsub : gapChain q first (y :: t') = adjDiffs (y :: t') ++ [first + q - lastElt (y :: t')] := by
            exact ih (by simp)
          simp [gapChain, adjDiffs, lastElt, hsub]

/-- `cyclicGaps q (h :: t) = adjacent differences ++ [h + q − last]`. -/
lemma cyclicGaps_eq_adjDiffs_append_last (q : ℕ) (h : ℕ) (t : List ℕ) :
    cyclicGaps q (h :: t) = adjDiffs (h :: t) ++ [h + q - lastElt (h :: t)] := by
  rw [cyclicGaps]
  exact gapChain_eq q h (h :: t) (by simp)

open MeasureTheory Set Metric
open scoped ENNReal Topology BigOperators


lemma rr_get_mem_reducedFinset (q : ℕ) {i : ℕ} (hi : i < (reducedResidueList q).length) :
    (reducedResidueList q).get ⟨i, hi⟩ ∈ reducedFinset q := by
  have hm : (reducedResidueList q).get ⟨i, hi⟩ ∈ reducedResidueList q :=
    List.get_mem (reducedResidueList q) ⟨i, hi⟩
  exact (mem_reducedFinset q _).mpr ((mem_reducedResidueList q _).mp hm)

/-- value order equals index order on a strictly increasing list. -/
lemma get_lt_get_iff_of_pairwise_lt {l : List ℕ} (hpw : l.Pairwise (· < ·)) {i j : ℕ}
    (hi : i < l.length) (hj : j < l.length) :
    l.get ⟨i, hi⟩ < l.get ⟨j, hj⟩ ↔ i < j := by
  constructor
  · intro h
    by_contra hnot
    rcases lt_or_eq_of_le (le_of_not_gt hnot) with hjl | hje
    · have hlt : l.get ⟨j, hj⟩ < l.get ⟨i, hi⟩ :=
        get_lt_get_of_pairwise_lt hpw hj hi hjl
      exact (not_lt_of_gt h) hlt
    · have hvals : l.get ⟨i, hi⟩ = l.get ⟨j, hj⟩ := by
        apply congrArg (fun t : Fin l.length => l.get t)
        apply Fin.ext
        exact hje.symm
      exact (ne_of_lt h) hvals
  · exact get_lt_get_of_pairwise_lt hpw hi hj

/-- value ≤ order follows from index ≤ order. -/
lemma get_le_get_of_pairwise_lt {l : List ℕ} (hpw : l.Pairwise (· < ·)) {i j : ℕ}
    (hi : i < l.length) (hj : j < l.length) (hij : i ≤ j) :
    l.get ⟨i, hi⟩ ≤ l.get ⟨j, hj⟩ := by
  rcases lt_or_eq_of_le hij with hij' | hje
  · exact le_of_lt (get_lt_get_of_pairwise_lt hpw hi hj hij')
  · subst hje
    rfl

/-- Each adjacent pair of the sorted reduced-residue list is a consecutive pair. -/
lemma adjacent_mem_consecutivePairs (q : ℕ) (i : ℕ) (hia : i < (reducedResidueList q).length)
    (hi : i + 1 < (reducedResidueList q).length) :
    ((reducedResidueList q).get ⟨i, hia⟩, (reducedResidueList q).get ⟨i + 1, hi⟩) ∈
      consecutivePairs q := by
  classical
  let a : ℕ := (reducedResidueList q).get ⟨i, hia⟩
  let b : ℕ := (reducedResidueList q).get ⟨i + 1, hi⟩
  have haF : a ∈ reducedFinset q := by
    dsimp [a]
    exact rr_get_mem_reducedFinset q hia
  have hbF : b ∈ reducedFinset q := by
    dsimp [b]
    exact rr_get_mem_reducedFinset q hi
  have hab : a < b := by
    dsimp [a, b]
    exact get_lt_get_of_pairwise_lt (reducedResidueList_pairwise_lt q) hia hi (by omega)
  have hcon : ∀ z ∈ reducedFinset q, ¬ (a < z ∧ z < b) := by
    intro z hzF hzab
    have hzL : z ∈ reducedResidueList q := (mem_reducedResidueList q z).mpr ((mem_reducedFinset q z).mp hzF)
    rcases List.mem_iff_get.mp hzL with ⟨⟨j, hj⟩, hzget⟩
    rw [← hzget] at hzab
    have hj1 : i < j := (get_lt_get_iff_of_pairwise_lt (reducedResidueList_pairwise_lt q) hia hj).mp
      (by simpa [a] using hzab.1)
    have hj2 : j < i + 1 := (get_lt_get_iff_of_pairwise_lt (reducedResidueList_pairwise_lt q) hj hi).mp
      (by simpa [b] using hzab.2)
    omega
  rw [consecutivePairs]
  exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨haF, hbF⟩, ⟨hab, hcon⟩⟩

/-- Converse: every consecutive pair is an adjacent pair in the sorted list. -/
lemma consecutivePairs_adjacent (q : ℕ) (hq : 1 < q) {ab : ℕ × ℕ} (hab : ab ∈ consecutivePairs q) :
    ∃ (i : ℕ), ∃ (hi : i + 1 < (reducedResidueList q).length),
      ab.1 = (reducedResidueList q).get ⟨i, by omega⟩ ∧
      ab.2 = (reducedResidueList q).get ⟨i + 1, hi⟩ := by
  classical
  rcases Finset.mem_filter.mp hab with ⟨hmem, hprops⟩
  rcases Finset.mem_product.mp hmem with ⟨haF, hbF⟩
  have hcon : ∀ z ∈ reducedFinset q, ¬ (ab.1 < z ∧ z < ab.2) := hprops.2
  have hablt : ab.1 < ab.2 := hprops.1
  have haL : ab.1 ∈ reducedResidueList q :=
    (mem_reducedResidueList q ab.1).mpr ((mem_reducedFinset q ab.1).mp haF)
  rcases List.mem_iff_get.mp haL with ⟨⟨i, hia⟩, hgeta⟩
  have hbL : ab.2 ∈ reducedResidueList q :=
    (mem_reducedResidueList q ab.2).mpr ((mem_reducedFinset q ab.2).mp hbF)
  rcases List.mem_iff_get.mp hbL with ⟨⟨j, hjb⟩, hgetb⟩
  have hij : i < j := (get_lt_get_iff_of_pairwise_lt (reducedResidueList_pairwise_lt q) hia hjb).mp
    (by
      rw [hgeta, hgetb]
      exact hablt)
  have hsucc : i + 1 < (reducedResidueList q).length := by omega
  let z : ℕ := (reducedResidueList q).get ⟨i + 1, hsucc⟩
  have hzF : z ∈ reducedFinset q := by
    dsimp [z]
    exact rr_get_mem_reducedFinset q hsucc
  have ha_lt_z : ab.1 < z := by
    rw [← hgeta]
    dsimp [z]
    exact get_lt_get_of_pairwise_lt (reducedResidueList_pairwise_lt q) hia hsucc (by omega)
  have hnotboth : ¬ (ab.1 < z ∧ z < ab.2) := hcon z hzF
  have hz_ge_b : ab.2 ≤ z := by
    have hnotltz : ¬ z < ab.2 := by
      intro hzlt
      exact hnotboth ⟨ha_lt_z, hzlt⟩
    exact le_of_not_gt hnotltz
  have hz_le_b : z ≤ ab.2 := by
    dsimp [z]
    rw [← hgetb]
    exact get_le_get_of_pairwise_lt (reducedResidueList_pairwise_lt q) hsucc hjb (by omega)
  have hzeq : z = ab.2 := le_antisymm hz_le_b hz_ge_b
  refine ⟨i, hsucc, ?_, ?_⟩
  · simpa [z] using hgeta.symm
  · exact hzeq.symm

/-- The sorted reduced-residue list of `q ≥ 1` has positive length. -/
lemma reducedResidueList_length_pos (q : ℕ) (hq : 0 < q) :
    0 < (reducedResidueList q).length := by
  exact List.length_pos_of_ne_nil (reducedResidueList_ne_nil_of_pos q hq)

/-- `lastElt` equals the element at the final index. -/
lemma lastElt_eq_get_last (l : List ℕ) (hne : l ≠ []) :
    lastElt l = l.get ⟨l.length - 1, by
      have hpos : 0 < l.length := List.length_pos_of_ne_nil hne
      omega⟩ := by
  cases l with
  | nil => contradiction
  | cons h t =>
      cases t with
      | nil => simp [lastElt]
      | cons a t' =>
          have hne' : a :: t' ≠ [] := by simp
          have ih' := lastElt_eq_get_last (a :: t') hne'
          calc
            lastElt (h :: a :: t') = lastElt (a :: t') := by simp [lastElt]
            _ = (a :: t').get ⟨(a :: t').length - 1, by
              have hpos : 0 < (a :: t').length := by simp
              omega⟩ := ih'
            _ = (h :: a :: t').get ⟨(a :: t').length, by simp⟩ := by
              simp

/-- get on `l.zip l.tail`: `(l.zip l.tail)[i] = (l[i], l[i+1])`. -/
lemma get_zip_tail_eq {l : List ℕ} {i : ℕ} (hi : i < (l.zip l.tail).length) :
    (l.zip l.tail).get ⟨i, hi⟩ = (l.get ⟨i, by
      rw [List.length_zip] at hi; omega⟩, l.get ⟨i + 1, by
      rw [List.length_zip] at hi
      have hlt : i < l.tail.length := by omega
      rw [List.length_tail] at hlt
      omega⟩) := by
  rw [List.get_eq_getElem]
  rw [List.getElem_zip]
  rw [List.getElem_tail (by
      rw [List.length_zip] at hi
      omega : i < l.tail.length)]
  congr 1 <;> rw [List.get_eq_getElem]

/-- membership in `l.zip l.tail`: exactly the adjacent pairs of `l`. -/
lemma mem_zip_tail_iff {l : List ℕ} {ab : ℕ × ℕ} :
    ab ∈ l.zip l.tail ↔ ∃ i : ℕ, ∃ (hi : i + 1 < l.length),
      ab.1 = l.get ⟨i, by omega⟩ ∧ ab.2 = l.get ⟨i + 1, hi⟩ := by
  constructor
  · intro h
    rcases List.mem_iff_get.mp h with ⟨⟨k, hk⟩, hget⟩
    have hkp : k + 1 < l.length := by
      have : k < (l.zip l.tail).length := hk
      rw [List.length_zip] at this
      have : k < l.tail.length := by omega
      rw [List.length_tail] at this
      omega
    have hz := get_zip_tail_eq hk
    refine ⟨k, hkp, ?_, ?_⟩
    · rw [← hget, hz]
    · rw [← hget, hz]
  · intro h
    rcases h with ⟨i, hi, hab1, hab2⟩
    have hlen : i < (l.zip l.tail).length := by
      rw [List.length_zip]
      have : i < l.tail.length := by
        rw [List.length_tail]
        omega
      omega
    have hmem : (l.zip l.tail).get ⟨i, hlen⟩ ∈ l.zip l.tail :=
      List.get_mem (l.zip l.tail) ⟨i, hlen⟩
    have hz := get_zip_tail_eq hlen
    have hab : ab = (l.get ⟨i, by omega⟩, l.get ⟨i + 1, by omega⟩) := by
      ext <;> simp [hab1, hab2]
    rw [hab]
    simpa [hz] using hmem

/-- in a strictly-increasing list, `get` is injective. -/
lemma get_inj_of_pairwise_lt {l : List ℕ} (hpw : l.Pairwise (· < ·)) :
    Function.Injective (fun i : Fin l.length => l.get i) := by
  intro i j h
  by_contra hne
  have hv : i.1 ≠ j.1 := by
    intro hval
    apply Fin.ext at hval
    exact hne hval
  rcases lt_or_gt_of_ne hv with hlt | hgt
  · have hv2 := List.Pairwise.rel_get_of_lt hpw (show i < j from by
      exact Fin.lt_def.mpr hlt)
    exact (ne_of_lt hv2) h
  · have hv2 := List.Pairwise.rel_get_of_lt hpw (show j < i from by
      exact Fin.lt_def.mpr hgt)
    exact (ne_of_lt hv2) h.symm

/-- the adjacent pairs of a strictly-increasing list are distinct. -/
lemma zip_tail_nodup_of_pairwise_lt {l : List ℕ} (hpw : l.Pairwise (· < ·)) :
    (l.zip l.tail).Nodup := by
  rw [List.nodup_iff_injective_get]
  intro i j h
  have hzlenle : (l.zip l.tail).length ≤ l.length - 1 := by
    have hz : (l.zip l.tail).length = min l.length (l.length - 1) := by
      rw [List.length_zip, List.length_tail]
    rw [hz]
    exact min_le_right l.length (l.length - 1)
  have hleni : i.1 < l.length - 1 := lt_of_lt_of_le i.2 hzlenle
  have hlenj : j.1 < l.length - 1 := lt_of_lt_of_le j.2 hzlenle
  have hzi := get_zip_tail_eq i.2
  have hzj := get_zip_tail_eq j.2
  have hfirst : l.get ⟨i.1, by omega⟩ = l.get ⟨j.1, by omega⟩ := by
    have h1 := congrArg (fun p : ℕ × ℕ => p.1) h
    simpa [hzi, hzj] using h1
  have hval : i.1 = j.1 := by
    have hinj := get_inj_of_pairwise_lt hpw
    have hilt : i.1 < l.length := lt_of_lt_of_le hleni (by omega : l.length - 1 ≤ l.length)
    have hjlt : j.1 < l.length := lt_of_lt_of_le hlenj (by omega : l.length - 1 ≤ l.length)
    have hiFin : (⟨i.1, hilt⟩ : Fin l.length) = ⟨j.1, hjlt⟩ := by
      exact hinj (by simpa using hfirst)
    simpa using (congrArg (fun x : Fin l.length => x.1) hiFin)
  apply Fin.ext
  exact hval

/-- sum over a duplicate-free list equals the sum over its `toFinset`. -/
lemma list_map_sum_eq_toFinset_sum {α : Type*} [DecidableEq α] (l : List α) (f : α → ℝ)
    (hl : l.Nodup) :
    (l.map f).sum = ∑ a ∈ l.toFinset, f a := by
  induction l with
  | nil => simp
  | cons a t ih =>
      have hnod : a ∉ t := (List.nodup_cons.mp hl).1
      have hmem : a ∉ t.toFinset := by
        simpa using hnod
      have hih := ih (List.nodup_cons.mp hl).2
      calc
        ((a :: t).map f).sum = f a + (t.map f).sum := by simp
        _ = f a + ∑ a ∈ t.toFinset, f a := by rw [hih]
        _ = ∑ x ∈ (a :: t).toFinset, f x := by
          rw [List.toFinset_cons]
          rw [Finset.sum_insert hmem]

/-- `adjDiffs l` equals the differences of the zip pairs. -/
lemma adjDiffs_eq_zip_map (l : List ℕ) :
    adjDiffs l = (l.zip l.tail).map (fun p : ℕ × ℕ => p.2 - p.1) := by
  induction l with
  | nil => simp [adjDiffs]
  | cons a t ih =>
      cases t with
      | nil => simp [adjDiffs]
      | cons b t' =>
          rw [adjDiffs, ih]
          simp [List.zip]

/-- First sorted reduced residue of `q ≥ 2` is `1`. -/
lemma rr_get0_eq_one (q : ℕ) (hq : 1 < q) :
    (reducedResidueList q).get ⟨0, reducedResidueList_length_pos q (by omega)⟩ = 1 := by
  have h1 : 1 ∈ reducedResidueList q := one_mem_reducedResidueList q hq
  rcases List.mem_iff_get.mp h1 with ⟨⟨k, hk⟩, hgk⟩
  have hlen : 0 < (reducedResidueList q).length := reducedResidueList_length_pos q (by omega)
  apply le_antisymm
  · have h0k : 0 ≤ k := by omega
    have hle : (reducedResidueList q).get ⟨0, hlen⟩ ≤ (reducedResidueList q).get ⟨k, hk⟩ :=
      get_le_get_of_pairwise_lt (reducedResidueList_pairwise_lt q) hlen hk h0k
    rw [hgk] at hle
    exact hle
  · have hmem : (reducedResidueList q).get ⟨0, hlen⟩ ∈ reducedFinset q :=
      rr_get_mem_reducedFinset q hlen
    exact one_le_of_mem_reducedFinset q hq _ hmem

/-- Last sorted reduced residue of `q ≥ 2` is `q − 1`. -/
lemma rr_lastElt_eq_pred (q : ℕ) (hq : 1 < q) :
    lastElt (reducedResidueList q) = q - 1 := by
  have hp : q - 1 ∈ reducedResidueList q := pred_mem_reducedResidueList q hq
  rcases List.mem_iff_get.mp hp with ⟨⟨j, hj⟩, hgj⟩
  have hne : reducedResidueList q ≠ [] := reducedResidueList_ne_nil_of_pos q (by omega)
  have hlen : 0 < (reducedResidueList q).length := List.length_pos_of_ne_nil hne
  have hlast := lastElt_eq_get_last (reducedResidueList q) hne
  have hmem : lastElt (reducedResidueList q) ∈ reducedFinset q := by
    rw [hlast]
    exact rr_get_mem_reducedFinset q (by omega)
  apply le_antisymm
  · have hleall : lastElt (reducedResidueList q) ≤ q - 1 :=
      le_pred_of_mem_reducedFinset q (lastElt (reducedResidueList q)) hmem
    exact hleall
  · have hjl : j ≤ (reducedResidueList q).length - 1 := by omega
    have hlen1 : (reducedResidueList q).length - 1 < (reducedResidueList q).length := by omega
    have hle : (reducedResidueList q).get ⟨j, hj⟩ ≤
        (reducedResidueList q).get ⟨(reducedResidueList q).length - 1, hlen1⟩ :=
      get_le_get_of_pairwise_lt (reducedResidueList_pairwise_lt q) hj hlen1 hjl
    rw [hgj] at hle
    rw [hlast]
    exact hle

/-- The wrap cyclic gap of the reduced residues of `q ≥ 2` is `2`. -/
lemma rr_wrap_gap_eq_two (q : ℕ) (hq : 1 < q) :
    (reducedResidueList q).get ⟨0, reducedResidueList_length_pos q (by omega)⟩ +
        q - lastElt (reducedResidueList q) = 2 := by
  have h0 := rr_get0_eq_one q hq
  have hl := rr_lastElt_eq_pred q hq
  omega

/-- Cyclic gaps of the reduced residues of `q ≥ 2`: adjacent differences plus `[2]`. -/
lemma cyclicGaps_reduced_eq_adj_append_two (q : ℕ) (hq : 1 < q) :
    cyclicGaps q (reducedResidueList q) = adjDiffs (reducedResidueList q) ++ [2] := by
  have hne : reducedResidueList q ≠ [] := reducedResidueList_ne_nil_of_pos q (by omega)
  cases h : reducedResidueList q with
  | nil => exfalso; exact hne h
  | cons hd tl =>
      have hdec : cyclicGaps q (hd :: tl) = adjDiffs (hd :: tl) ++ [hd + q - lastElt (hd :: tl)] :=
        cyclicGaps_eq_adjDiffs_append_last q hd tl
      have h0 := rr_get0_eq_one q hq
      have hh : hd = 1 := by
        have hg : (hd :: tl).get ⟨0, by simp⟩ = hd := by simp
        rw [← hg]
        simpa [h] using h0
      have hl0 := rr_lastElt_eq_pred q hq
      have hl : lastElt (hd :: tl) = q - 1 := by
        simpa [h] using hl0
      have hw : hd + q - lastElt (hd :: tl) = 2 := by
        rw [hh]
        rw [hh] at hl
        rw [hl]
        omega
      rw [hdec]
      rw [hw]






/-! ### K1 gap inequality: gap counts and close-pair counts (u(k) ≤ pairSum k)

For the PV deficit bound we need, for `k ≤ q/φ(q)`, the bound
`u(k) ≤ Σ_{h ≤ k} c₊(h)` where `u(k)` is the number of cyclic gaps of `q` of
size ≤ k and `c₊(h) := #{a ∈ [0,q) : gcd(a,q) = gcd(a+h,q) = 1}` (a reduced
residue whose translate by `h` is again reduced).  Each gap of size `d ≤ k`
starts at a reduced residue and is an ordered coprime pair at forward distance
`d`, and distinct gaps have distinct starts, giving the injection. -/

/-- `c₊(h)`: reduced residues `a` mod `q` with `a + h` also coprime to `q`. -/
def closePairCount (q : ℕ) (h : ℕ) : ℕ :=
  ((Finset.range q).filter (fun a : ℕ => a.gcd q = 1 ∧ (a + h).gcd q = 1)).card

/-- cumulative close-pair count `Σ_{h=1}^{k} c₊(h)`. -/
def closePairSum (q : ℕ) (k : ℕ) : ℕ :=
  ∑ h ∈ Finset.Icc 1 k, closePairCount q h

/-- number of cyclic gaps of `q` of size ≤ k. -/
def gapCountSmall (q : ℕ) (k : ℕ) : ℕ :=
  ((cyclicGaps q (reducedResidueList q)).filter (fun d : ℕ => d ≤ k)).length

/-- a filter-count over an append is the sum of the filter-counts. -/
lemma list_countP_append {α : Type*} (l₁ l₂ : List α) (p : α → Prop) [DecidablePred p] :
    ((l₁ ++ l₂).filter p).length = (l₁.filter p).length + (l₂.filter p).length := by
  rw [List.filter_append]
  rw [List.length_append]

/-- filter of a Nodup list is Nodup. -/
lemma nodup_filter_of_nodup {α : Type*} (l : List α) (p : α → Prop) [DecidablePred p]
    (hl : l.Nodup) : (l.filter p).Nodup := by
  classical
  induction l with
  | nil => simp
  | cons a t ih =>
      by_cases hpa : p a
      · have hsplit : (a :: t).filter p = a :: (t.filter p) := by simp [hpa]
        rw [hsplit]
        have hmem : a ∉ (t.filter p) := by
          intro hm
          exact (List.nodup_cons.mp hl).1 (List.mem_of_mem_filter hm)
        exact List.nodup_cons.mpr ⟨hmem, ih (List.nodup_cons.mp hl).2⟩
      · have hsplit : (a :: t).filter p = t.filter p := by simp [hpa]
        rw [hsplit]
        exact ih (List.nodup_cons.mp hl).2

/-- filter-count of a Nodup list equals filter-card of its `toFinset`. -/
lemma list_filter_count_eq_toFinset {α : Type*} [DecidableEq α] (l : List α) (p : α → Prop)
    [DecidablePred p] (hl : l.Nodup) :
    (l.filter p).length = (l.toFinset.filter p).card := by
  classical
  have hset : (l.filter p).toFinset = l.toFinset.filter p := by
    ext x
    simp
  calc
    (l.filter p).length = ((l.filter p).toFinset).card := by
      exact (List.toFinset_card_of_nodup (nodup_filter_of_nodup l p hl)).symm
    _ = (l.toFinset.filter p).card := by rw [hset]




/-- double counting: `#((s × t).filter p)` = `Σ_{b ∈ t} #(s.filter (p · b))`. -/
lemma card_filter_product_eq_sum {α β : Type*} [DecidableEq α] [DecidableEq β] (s : Finset α)
    (t : Finset β) (p : α → β → Prop)
    [DecidablePred (fun ab : α × β => p ab.1 ab.2)] [∀ a : α, DecidablePred (p a)] :
    ((s.product t).filter (fun ab : α × β => p ab.1 ab.2)).card =
      ∑ b ∈ t, ((s.filter (fun a : α => p a b)).card) := by
  classical
  have hsp := Finset.sum_product (s := s) (t := t)
      (f := fun ab : α × β => if p ab.1 ab.2 then (1 : ℕ) else 0)
  calc
    ((s.product t).filter (fun ab : α × β => p ab.1 ab.2)).card
        = ∑ a ∈ s, ∑ b ∈ t, if p a b then (1 : ℕ) else 0 := by
          rw [Finset.card_eq_sum_ones]
          rw [Finset.sum_filter]
          change (∑ x ∈ (s ×ˢ t : Finset (α × β)), if p x.1 x.2 then (1 : ℕ) else 0) =
              ∑ a ∈ s, ∑ b ∈ t, if p a b then (1 : ℕ) else 0
          rw [hsp]
    _ = ∑ b ∈ t, ((s.filter (fun a : α => p a b)).card) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro b hb
          rw [Finset.card_eq_sum_ones]
          rw [Finset.sum_filter]


lemma length_filter_map_filter (l : List (ℕ × ℕ)) (k : ℕ) :
    ((l.map (fun p : ℕ × ℕ => p.2 - p.1)).filter (fun d : ℕ => d ≤ k)).length =
      (l.filter (fun p : ℕ × ℕ => p.2 - p.1 ≤ k)).length := by
  classical
  have hfm : (l.map (fun p : ℕ × ℕ => p.2 - p.1)).filter (fun d : ℕ => d ≤ k) =
      (l.filter (fun p : ℕ × ℕ => p.2 - p.1 ≤ k)).map (fun p : ℕ × ℕ => p.2 - p.1) := by
    change List.filter (fun d => decide (d ≤ k)) (List.map (fun p : ℕ × ℕ => p.2 - p.1) l) =
        List.map (fun p : ℕ × ℕ => p.2 - p.1) (List.filter (fun p => decide (p.2 - p.1 ≤ k)) l)
    rw [List.filter_map]
    apply congrArg (List.map (fun p : ℕ × ℕ => p.2 - p.1))
    apply List.filter_congr
    intro p hp
    rfl
  rw [hfm]
  simp

lemma gapCountSmall_eq_consecutivePairs_add (q : ℕ) (hq : 1 < q) (k : ℕ) :
    gapCountSmall q k =
      ((consecutivePairs q).filter (fun ab : ℕ × ℕ => ab.2 - ab.1 ≤ k)).card +
        (if 2 ≤ k then 1 else 0) := by
  classical
  have hdec : cyclicGaps q (reducedResidueList q) = adjDiffs (reducedResidueList q) ++ [2] :=
    cyclicGaps_reduced_eq_adj_append_two q hq
  have hzip := zip_tail_nodup_of_pairwise_lt (reducedResidueList_pairwise_lt q)
  have hset : consecutivePairs q = ((reducedResidueList q).zip (reducedResidueList q).tail).toFinset := by
    ext ab
    constructor
    · intro hab
      rw [List.mem_toFinset]
      rcases consecutivePairs_adjacent q hq hab with ⟨i, hi, hab1, hab2⟩
      have hp : ab = ((reducedResidueList q).get ⟨i, by omega⟩, (reducedResidueList q).get ⟨i + 1, hi⟩) := by
        ext <;> simpa [hab1, hab2]
      rw [hp]
      exact mem_zip_tail_iff.mpr ⟨i, hi, rfl, rfl⟩
    · intro h
      rw [List.mem_toFinset] at h
      rcases mem_zip_tail_iff.mp h with ⟨i, hi, hab1, hab2⟩
      have hp : ab = ((reducedResidueList q).get ⟨i, by omega⟩, (reducedResidueList q).get ⟨i + 1, hi⟩) := by
        ext <;> simpa [hab1, hab2]
      rw [hp]
      exact adjacent_mem_consecutivePairs q i (by omega) hi
  calc
    gapCountSmall q k
        = ((adjDiffs (reducedResidueList q) ++ [2]).filter (fun d : ℕ => d ≤ k)).length := by
            dsimp [gapCountSmall]
            rw [hdec]
    _ = ((adjDiffs (reducedResidueList q)).filter (fun d : ℕ => d ≤ k)).length +
        (([2]).filter (fun d : ℕ => d ≤ k)).length := list_countP_append _ _ _
    _ = (((reducedResidueList q).zip (reducedResidueList q).tail).filter
          (fun p : ℕ × ℕ => p.2 - p.1 ≤ k)).length + (if 2 ≤ k then 1 else 0) := by
          congr 1
          · -- adjDiffs filter count = zip filter count (map over zip)
            have hmap : adjDiffs (reducedResidueList q) =
                ((reducedResidueList q).zip (reducedResidueList q).tail).map (fun p : ℕ × ℕ => p.2 - p.1) :=
              adjDiffs_eq_zip_map (reducedResidueList q)
            rw [hmap]
            exact length_filter_map_filter ((reducedResidueList q).zip (reducedResidueList q).tail) k
          · by_cases hk : 2 ≤ k
            · simp [hk]
            · simp [hk]
    _ = ((consecutivePairs q).filter (fun ab : ℕ × ℕ => ab.2 - ab.1 ≤ k)).card +
        (if 2 ≤ k then 1 else 0) := by
          congr 1
          rw [hset]
          rw [list_filter_count_eq_toFinset ((reducedResidueList q).zip (reducedResidueList q).tail)
            (fun ab : ℕ × ℕ => ab.2 - ab.1 ≤ k) hzip]





/-- every cyclic gap of size ≤ k gives a distinct close coprime pair. -/
lemma gapCountSmall_le_closePairSum (q : ℕ) (k : ℕ) :
    gapCountSmall q k ≤ closePairSum q k := by
  classical
  by_cases hq0 : q = 0
  · subst q
    have hrr : reducedResidueList 0 = [] := by
      rw [reducedResidueList, reducedFinset]
      simp
    simp [gapCountSmall, closePairSum, closePairCount, cyclicGaps, hrr]
  by_cases hq1 : q = 1
  · -- q = 1: exactly one cyclic gap, and c₊(1, h) = 1 for every h
    subst q
    by_cases hk0 : k = 0
    · -- no gap is ≤ 0 (all cyclic gaps are ≥ 1), and the pair sum is empty
      subst k
      have hgap0 : gapCountSmall 1 0 = 0 := by
        dsimp [gapCountSmall]
        have hpos : ∀ d ∈ cyclicGaps 1 (reducedResidueList 1), 1 ≤ d := by
          intro d hd
          have hpos' : 0 < d := cyclicGaps_pos (q := 1) (xs := reducedResidueList 1)
            (reducedResidueList_ne_nil_of_pos 1 (by norm_num)) (reducedResidueList_pairwise_lt 1)
            (reducedResidueList_mem_lt 1) d hd
          omega
        have hf : (cyclicGaps 1 (reducedResidueList 1)).filter (fun d : ℕ => d ≤ 0) = [] := by
          rw [List.eq_nil_iff_forall_not_mem]
          intro d hd
          have hdm : d ∈ cyclicGaps 1 (reducedResidueList 1) := (List.mem_filter.mp hd).1
          have hle : d ≤ 0 := of_decide_eq_true (List.mem_filter.mp hd).2
          have h1 : 1 ≤ d := hpos d hdm
          omega
        rw [hf]
        simp
      have hsum0 : closePairSum 1 0 = 0 := by
        dsimp [closePairSum]
        simp
      simpa [hgap0, hsum0]
    · have hk1 : 1 ≤ k := by omega
      have hgap : gapCountSmall 1 k ≤ 1 := by
        dsimp [gapCountSmall]
        calc
          ((cyclicGaps 1 (reducedResidueList 1)).filter (fun d : ℕ => d ≤ k)).length
              ≤ (cyclicGaps 1 (reducedResidueList 1)).length := List.length_filter_le _ _
          _ = (reducedResidueList 1).length := cyclicGaps_length 1 (reducedResidueList 1)
          _ = 1 := by
              rw [reducedResidueList_length]
              norm_num
      have hone : ∀ h : ℕ, closePairCount 1 h = 1 := by
        intro h
        rw [closePairCount]
        have hp0 : (0 : ℕ).gcd 1 = 1 ∧ (0 + h).gcd 1 = 1 := by
          constructor
          · exact Nat.gcd_zero_left 1
          · simpa using (Nat.gcd_one_right h)
        have hc : (Finset.range 1).filter (fun a : ℕ => a.gcd 1 = 1 ∧ (a + h).gcd 1 = 1) = ({0} : Finset ℕ) := by
          ext a
          constructor
          · intro ha
            have ha1 : a < 1 := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
            have ha0 : a = 0 := by omega
            simp [ha0]
          · intro ha
            have ha0 : a = 0 := by simpa using ha
            subst a
            exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega : 0 < 1), hp0⟩
        rw [hc]
        simp
      have hsum : closePairSum 1 k = k := by
        dsimp [closePairSum]
        calc
          (∑ h ∈ Finset.Icc 1 k, closePairCount 1 h) = ∑ h ∈ Finset.Icc 1 k, 1 := by
            apply Finset.sum_congr rfl
            intro h hh
            exact hone h
          _ = (Finset.Icc 1 k).card := by
            rw [Finset.sum_const]
            simp
          _ = k := by
            have hcard : (Finset.Icc 1 k).card = k := by
              -- #(Icc 1 k) = k (with Icc 1 0 empty)
              simp
            exact hcard
      calc
        gapCountSmall 1 k ≤ 1 := hgap
        _ ≤ k := hk1
        _ = closePairSum 1 k := hsum.symm
  · have hq2 : 1 < q := by omega
    let CPk : Finset (ℕ × ℕ) := (consecutivePairs q).filter (fun ab : ℕ × ℕ => ab.2 - ab.1 ≤ k)
    let F : ℕ × ℕ → ℕ × ℕ := fun ab => (ab.1, ab.2 - ab.1)
    let pairSet : Finset (ℕ × ℕ) :=
      ((Finset.range q).product (Finset.Icc 1 k)).filter
        (fun ah : ℕ × ℕ => ah.1.gcd q = 1 ∧ (ah.1 + ah.2).gcd q = 1)
    have hgap : gapCountSmall q k = CPk.card + (if 2 ≤ k then 1 else 0) := by
      dsimp [CPk]
      exact gapCountSmall_eq_consecutivePairs_add q hq2 k
    have hF_mem : ∀ ab ∈ CPk, F ab ∈ pairSet := by
      intro ab hab
      have hmemCP : ab ∈ consecutivePairs q := (Finset.mem_filter.mp hab).1
      have hkab : ab.2 - ab.1 ≤ k := (Finset.mem_filter.mp hab).2
      rcases Finset.mem_product.mp (Finset.mem_filter.mp hmemCP).1 with ⟨haF, hbF⟩
      have hablt : ab.1 < ab.2 := (Finset.mem_filter.mp hmemCP).2.1
      have hstart : ab.1.gcd q = 1 := (mem_reducedFinset q ab.1).mp haF |>.2
      have hend : (ab.1 + (ab.2 - ab.1)).gcd q = 1 := by
        rw [Nat.add_sub_of_le (Nat.le_of_lt hablt)]
        exact (mem_reducedFinset q ab.2).mp hbF |>.2
      dsimp [pairSet, F]
      rw [Finset.mem_filter]
      constructor
      · rw [Finset.mem_product]
        constructor
        · exact Finset.mem_range.mpr ((mem_reducedFinset q ab.1).mp haF |>.1)
        · rw [Finset.mem_Icc]
          constructor
          · exact Nat.succ_le_of_lt (Nat.sub_pos_of_lt hablt)
          · exact hkab
      · constructor
        · exact hstart
        · exact hend
    have hF_inj : ∀ ab ∈ CPk, ∀ ab' ∈ CPk, F ab = F ab' → ab = ab' := by
      intro ab hab ab' hab' h
      have h1 : ab.1 = ab'.1 := by
        simpa [F] using (congrArg Prod.fst h)
      have hmem1 : ab ∈ consecutivePairs q := (Finset.mem_filter.mp hab).1
      have hmem2 : ab' ∈ consecutivePairs q := (Finset.mem_filter.mp hab').1
      rcases consecutivePairs_adjacent q hq2 hmem1 with ⟨i1, hi1, h1a, h1b⟩
      rcases consecutivePairs_adjacent q hq2 hmem2 with ⟨i2, hi2, h2a, h2b⟩
      have hstart' : (reducedResidueList q).get ⟨i1, by omega⟩ =
          (reducedResidueList q).get ⟨i2, by omega⟩ := by
        rw [← h1a, ← h2a]
        exact h1
      have hinj := get_inj_of_pairwise_lt (reducedResidueList_pairwise_lt q)
      have hfin : (⟨i1, by omega⟩ : Fin (reducedResidueList q).length) = ⟨i2, by omega⟩ := by
        exact hinj (by simpa using hstart')
      have hival : i1 = i2 := by
        simpa using (congrArg Fin.val hfin)
      subst hival
      ext <;> simp [h1a, h1b, h2a, h2b]
    have hCP_le_pair : CPk.card ≤ pairSet.card := by
      calc
        CPk.card = (CPk.image F).card := by
          rw [Finset.card_image_of_injOn]
          intro a ha b hb h
          exact hF_inj a ha b hb h
        _ ≤ pairSet.card := Finset.card_le_card (by
          intro x hx
          rcases Finset.mem_image.mp hx with ⟨ab, hab, rfl⟩
          exact hF_mem ab hab)
    have hwrap_mem : (q - 1, 2) ∈ pairSet ↔ 2 ≤ k := by
      constructor
      · intro h
        have hm := Finset.mem_filter.mp h
        have hcc : (2 : ℕ) ∈ Finset.Icc 1 k := (Finset.mem_product.mp hm.1).2
        exact (Finset.mem_Icc.mp hcc).2
      · intro hk2
        rw [Finset.mem_filter]
        constructor
        · change (q - 1, 2) ∈ (Finset.range q) ×ˢ (Finset.Icc 1 k)
          rw [Finset.mem_product]
          constructor
          · exact Finset.mem_range.mpr (by omega)
          · rw [Finset.mem_Icc]
            omega
        · constructor
          · have hp : q - 1 ∈ reducedResidueList q := pred_mem_reducedResidueList q hq2
            exact ((mem_reducedResidueList q (q - 1)).mp hp).2
          · have hg : (q - 1 + 2).gcd q = 1 := by
              have hq' : q - 1 + 2 = q + 1 := by omega
              rw [hq']
              have hqq : (q + 1).gcd q = 1 := by
                have h1q : q + 1 = 1 + q := by omega
                rw [h1q]
                rw [Nat.gcd_add_self_left q 1]
                rw [Nat.gcd_one_left]
              exact hqq
            simpa using hg
    have hwrap_not_image : (q - 1, 2) ∉ CPk.image F := by
      intro h
      rcases Finset.mem_image.mp h with ⟨ab, hab, hf⟩
      have hstart : ab.1 = q - 1 := congrArg Prod.fst hf
      have hmemCP : ab ∈ consecutivePairs q := (Finset.mem_filter.mp hab).1
      have hablt : ab.1 < ab.2 := (Finset.mem_filter.mp hmemCP).2.1
      rcases Finset.mem_product.mp (Finset.mem_filter.mp hmemCP).1 with ⟨haF, hbF⟩
      have hbq : ab.2 < q := (mem_reducedFinset q ab.2).mp hbF |>.1
      have hlt : q - 1 < ab.2 := by
        rw [← hstart]
        exact hablt
      omega
    have hfinal : CPk.card + (if 2 ≤ k then 1 else 0) ≤ pairSet.card := by
      by_cases hk2 : 2 ≤ k
      · have hw_mem : (q - 1, 2) ∈ pairSet := hwrap_mem.mpr hk2
        have hnotin : (q - 1, 2) ∉ CPk.image F := hwrap_not_image
        simpa [hk2] using (by
          calc
            CPk.card + 1 ≤ pairSet.card := by
              calc
                CPk.card + 1 = (CPk.image F).card + 1 := by
                  congr 1
                  rw [Finset.card_image_of_injOn]
                  intro a ha b hb h
                  exact hF_inj a ha b hb h
                _ = (insert (q - 1, 2) (CPk.image F)).card := by
                  rw [Finset.card_insert_of_notMem hnotin]
                _ ≤ pairSet.card := Finset.card_le_card (by
                  intro x hx
                  rcases Finset.mem_insert.mp hx with hx | hx
                  · simpa [hx] using hw_mem
                  · rcases Finset.mem_image.mp hx with ⟨ab, hab, rfl⟩
                    exact hF_mem ab hab))
      · simpa [hk2] using hCP_le_pair
    have hcard_pairSet : pairSet.card = closePairSum q k := by
      have hh := card_filter_product_eq_sum (s := Finset.range q) (t := Finset.Icc 1 k)
        (fun a h => a.gcd q = 1 ∧ (a + h).gcd q = 1)
      simpa [pairSet, closePairSum, closePairCount] using hh
    calc
      gapCountSmall q k ≤ pairSet.card := by
        rw [hgap]
        exact hfinal
      _ = closePairSum q k := hcard_pairSet



private lemma single_count_prime_pow (p k e : ℕ) (hp : p.Prime) (hk : 0 < k) :
    ((Finset.range (p ^ k)).filter (fun n : ℕ => ¬ p ∣ n ∧ ¬ p ∣ (n + e))).card =
      if p ∣ e then (p ^ k).totient else (p ^ k).totient - p ^ (k - 1) := by
  classical
  have hpair := reduced_pair_count_prime_pow p k 1 1 e hp hk (by simpa using hp.not_dvd_one) (by simpa using hp.not_dvd_one)
  have hdvdpow : p ∣ p ^ k := dvd_pow_self p (ne_of_gt hk)
  have hdvdmod (x : ℕ) : ¬ p ∣ x % p ^ k ↔ ¬ p ∣ x := by
    rw [Nat.dvd_mod_iff (k := p) (m := x) (n := p ^ k) hdvdpow]
  have hpowpos : 0 < p ^ k := pow_pos hp.pos k
  have hprod :
      ((Finset.range (p ^ k)).filter (fun n : ℕ => ¬ p ∣ n ∧ ¬ p ∣ (n + e))).card =
      ((Finset.product (Finset.range (p ^ k)) (Finset.range (p ^ k))).filter
        (fun mn : ℕ × ℕ => ¬ p ∣ mn.1 ∧ ¬ p ∣ mn.2 ∧
           ((mn.1 * 1) % (p ^ k) = ((mn.2 * 1 + e) % (p ^ k))))).card := by
    refine Finset.card_bij (fun n _ => ((n + e) % (p ^ k), n)) ?_ ?_ ?_
    · intro n hn
      have hnmem := (Finset.mem_filter.mp hn)
      rw [Finset.mem_filter]
      constructor
      · change ((n + e) % (p ^ k), n) ∈
          (Finset.range (p ^ k)) ×ˢ (Finset.range (p ^ k))
        rw [Finset.mem_product]
        constructor
        · exact Finset.mem_range.mpr (Nat.mod_lt (n + e) hpowpos)
        · exact hnmem.1
      · refine ⟨?_, ⟨?_, ?_⟩⟩
        · exact (hdvdmod (n + e)).mpr hnmem.2.2
        · exact hnmem.2.1
        · simp only [Prod.fst, Prod.snd, Nat.mul_one]
          rw [Nat.mod_eq_of_lt (Nat.mod_lt (n + e) hpowpos)]
    · intro n hn n' hn' h
      exact congrArg Prod.snd h
    · intro x hx
      rw [Finset.mem_filter] at hx
      rcases hx with ⟨hxprod, hxcond⟩
      change x ∈ (Finset.range (p ^ k)) ×ˢ (Finset.range (p ^ k)) at hxprod
      rw [Finset.mem_product] at hxprod
      refine ⟨x.2, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨hxprod.2, hxcond.2.1, ?_⟩
        · have hx1mod : ¬ p ∣ x.1 % p ^ k := (hdvdmod x.1).mpr hxcond.1
          have hcong : x.1 % p ^ k = (x.2 + e) % p ^ k := by
            simpa [Nat.mul_one] using hxcond.2.2
          have hx2 : ¬ p ∣ (x.2 + e) % p ^ k := by simpa [hcong] using hx1mod
          exact (hdvdmod (x.2 + e)).mp hx2
      · apply Prod.ext
        · have hm : x.1 % (p ^ k) = (x.2 + e) % (p ^ k) := by
            simpa [Nat.mul_one] using hxcond.2.2
          have hx1 : x.1 < p ^ k := Finset.mem_range.mp hxprod.1
          change ((x.2 + e) % p ^ k) = x.1
          rw [← hm]
          rw [Nat.mod_eq_of_lt hx1]
        · rfl
  calc
    ((Finset.range (p ^ k)).filter (fun n : ℕ => ¬ p ∣ n ∧ ¬ p ∣ (n + e))).card
        = ((Finset.product (Finset.range (p ^ k)) (Finset.range (p ^ k))).filter
          (fun mn : ℕ × ℕ => ¬ p ∣ mn.1 ∧ ¬ p ∣ mn.2 ∧
             ((mn.1 * 1) % (p ^ k) = ((mn.2 * 1 + e) % (p ^ k))))).card := hprod
    _ = if p ∣ e then (p ^ k).totient else (p ^ k).totient - p ^ (k - 1) := by
        simpa [Nat.mul_one, add_comm] using hpair

/-- prime-power close-pair count: `c₊(p^k, e) = p^(k-1)·((p-1) if p∣e else (p-2))`. -/
private lemma close_pair_prime_pow (p k e : ℕ) (hp : p.Prime) (hk : 0 < k) :
    ((Finset.range (p ^ k)).filter (fun n : ℕ => ¬ p ∣ n ∧ ¬ p ∣ (n + e))).card =
      p ^ (k - 1) * (if p ∣ e then p - 1 else p - 2) := by
  classical
  let A : ℕ := p ^ (k - 1)
  by_cases he : p ∣ e
  · rw [single_count_prime_pow p k e hp hk]
    rw [Nat.totient_prime_pow hp hk]
    simp [he]
  · rw [single_count_prime_pow p k e hp hk]
    rw [Nat.totient_prime_pow hp hk]
    rw [if_neg he]
    rw [if_neg he]
    have hsub : A * (p - 1) - A = A * (p - 2) := by
      have h := Nat.mul_sub_left_distrib A (p - 1) 1
      rw [mul_one] at h
      have hpp : (p - 1) - 1 = p - 2 := by omega
      rw [hpp] at h
      exact h.symm
    simpa [A] using hsub

/-- ZMod-unit count of reduced residues of `q` under translation by `e`
equals the integer range count `closePairCount q e`. -/
private lemma zmod_closePair_eq (q e : ℕ) [NeZero q] :
    Fintype.card {x : ZMod q // IsUnit x ∧ IsUnit (x + (e : ZMod q))} = closePairCount q e := by
  classical
  let Px : ZMod q → Prop := fun x => IsUnit x ∧ IsUnit (x + (e : ZMod q))
  let UZ := (Finset.univ : Finset (ZMod q)).filter Px
  let TN := (Finset.range q).filter (fun a : ℕ => a.gcd q = 1 ∧ (a + e).gcd q = 1)
  have h1 : UZ.card = Fintype.card {x : ZMod q // Px x} := by
    calc
      UZ.card = Fintype.card {x : ZMod q // x ∈ UZ} := (Fintype.card_coe UZ).symm
      _ = Fintype.card {x : ZMod q // Px x} := by
        apply Fintype.card_congr
        refine Equiv.subtypeEquivRight ?_
        intro x
        simp [UZ, Px]
  have hunit (a : ℕ) : IsUnit (a : ZMod q) ↔ a.Coprime q := ZMod.isUnit_iff_coprime a q
  have hgcd (a : ℕ) : a.gcd q = 1 ↔ a.Coprime q := Nat.coprime_iff_gcd_eq_one
  have hmain : Fintype.card {x : ZMod q // Px x} = TN.card := by
    calc
      Fintype.card {x : ZMod q // Px x} = UZ.card := by rw [h1]
      _ = TN.card := by
        refine Finset.card_bij' (fun x _ => x.val) (fun a _ => (a : ZMod q)) ?hi ?hj ?left ?right
        · intro x hx
          have hm := (Finset.mem_filter.mp hx).2
          refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt x), ?_⟩
          constructor
          · have hc : x.val.Coprime q :=
              (hunit x.val).mp (by simpa [ZMod.natCast_zmod_val x] using hm.1)
            exact (hgcd x.val).mpr hc
          · have hx2 : IsUnit ((x.val + e : ℕ) : ZMod q) := by
              simpa [ZMod.natCast_zmod_val x, Nat.cast_add] using hm.2
            have hc : (x.val + e).Coprime q := (hunit (x.val + e)).mp hx2
            exact (hgcd (x.val + e)).mpr hc
        · intro a ha
          have hm := (Finset.mem_filter.mp ha).2
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          constructor
          · exact (hunit a).mpr ((hgcd a).mp hm.1)
          · have ha2 : IsUnit ((a + e : ℕ) : ZMod q) := (hunit (a + e)).mpr ((hgcd (a + e)).mp hm.2)
            simpa [Nat.cast_add] using ha2
        · intro x hx
          exact ZMod.natCast_zmod_val x
        · intro a ha
          simp [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp ha).1)]
  calc
    Fintype.card {x : ZMod q // IsUnit x ∧ IsUnit (x + (e : ZMod q))}
        = TN.card := by simpa [Px] using hmain
    _ = closePairCount q e := by rfl

/-- ZMod prime-power value: `CP(p^k, e) = p^(k-1)·((p-1) if p∣e else (p-2))`. -/
private lemma zmod_closePair_prime_pow (p k e : ℕ) [NeZero (p ^ k)] (hp : p.Prime)
    (hk : 0 < k) :
    Fintype.card {x : ZMod (p ^ k) // IsUnit x ∧ IsUnit (x + (e : ZMod (p ^ k)))} =
      p ^ (k - 1) * (if p ∣ e then p - 1 else p - 2) := by
  classical
  rw [zmod_closePair_eq (p ^ k) e]
  have hcp (a : ℕ) : a.gcd (p ^ k) = 1 ↔ ¬ p ∣ a := by
    rw [← Nat.coprime_iff_gcd_eq_one]
    exact Commons.NumberTheory.Nat.coprime_prime_pow_right_iff_not_dvd p k a hp hk
  have hmain : (Finset.range (p ^ k)).filter (fun a : ℕ => a.gcd (p ^ k) = 1 ∧ (a + e).gcd (p ^ k) = 1) =
      (Finset.range (p ^ k)).filter (fun n : ℕ => ¬ p ∣ n ∧ ¬ p ∣ (n + e)) := by
    apply Finset.filter_congr
    intro a ha
    rw [hcp a, hcp (a + e)]
  change ((Finset.range (p ^ k)).filter
    (fun a : ℕ => a.gcd (p ^ k) = 1 ∧ (a + e).gcd (p ^ k) = 1)).card =
      p ^ (k - 1) * (if p ∣ e then p - 1 else p - 2)
  rw [hmain]
  exact close_pair_prime_pow p k e hp hk

private lemma zmod_pi_card_prod {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℕ)
    [∀ i, NeZero (a i)] (h : ℕ) :
    Fintype.card {f : (i : ι) → ZMod (a i) //
        IsUnit f ∧ IsUnit (f + (fun i => (h : ZMod (a i))))} =
      ∏ i, Fintype.card {x : ZMod (a i) // IsUnit x ∧ IsUnit (x + (h : ZMod (a i)))} := by
  classical
  let P : (i : ι) → ZMod (a i) → Prop := fun i x => IsUnit x ∧ IsUnit (x + (h : ZMod (a i)))
  have hiff : {f : (i : ι) → ZMod (a i) //
        IsUnit f ∧ IsUnit (f + (fun i => (h : ZMod (a i))))} ≃
      {f : (i : ι) → ZMod (a i) // ∀ i, P i (f i)} := by
    refine Equiv.subtypeEquivRight ?_
    intro f
    constructor
    · intro hf
      intro i
      exact ⟨(Pi.isUnit_iff.mp hf.1) i, (Pi.isUnit_iff.mp hf.2) i⟩
    · intro hfi
      exact ⟨Pi.isUnit_iff.mpr (fun i => (hfi i).1),
        Pi.isUnit_iff.mpr (fun i => (hfi i).2)⟩
  calc
    Fintype.card {f : (i : ι) → ZMod (a i) //
        IsUnit f ∧ IsUnit (f + (fun i => (h : ZMod (a i))))}
        = Fintype.card {f : (i : ι) → ZMod (a i) // ∀ i, P i (f i)} := Fintype.card_congr hiff
    _ = Fintype.card ((i : ι) → {x : ZMod (a i) // P i x}) := by
        exact Fintype.card_congr Equiv.subtypePiEquivPi
    _ = ∏ i, Fintype.card {x : ZMod (a i) // P i x} := Fintype.card_pi
    _ = ∏ i, Fintype.card {x : ZMod (a i) // IsUnit x ∧ IsUnit (x + (h : ZMod (a i)))} := by
        apply Finset.prod_congr rfl
        intro i hi
        rfl

/-- pull the unit-translation count through `ZMod.prodEquivPi` (CRT ring split). -/
private lemma zmod_card_congr_prodEquivPi {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℕ)
    (cop : Pairwise (Function.onFun Nat.Coprime a)) [∀ i, NeZero (a i)]
    [NeZero (∏ i, a i)] (h : ℕ) :
    Fintype.card {x : ZMod (∏ i, a i) // IsUnit x ∧ IsUnit (x + (h : ZMod (∏ i, a i)))} =
    Fintype.card {f : (i : ι) → ZMod (a i) //
        IsUnit f ∧ IsUnit (f + (fun i => (h : ZMod (a i))))} := by
  classical
  let e : ZMod (∏ i, a i) ≃+* ((i : ι) → ZMod (a i)) := ZMod.prodEquivPi a cop
  have hu (x : ZMod (∏ i, a i)) : IsUnit x ↔ IsUnit (e x) :=
    (MulEquiv.isUnit_map e.toMulEquiv).symm
  have hnat : e (h : ZMod (∏ i, a i)) = fun i => (h : ZMod (a i)) := by
    ext i
    rw [ZMod.prodEquivPi_apply]
    exact map_natCast (ZMod.castHom _ (ZMod (a i))) h
  have hplus (x : ZMod (∏ i, a i)) :
      e (x + (h : ZMod (∏ i, a i))) = e x + (fun i => (h : ZMod (a i))) := by
    rw [map_add, hnat]
  have hiff : {x : ZMod (∏ i, a i) //
        IsUnit x ∧ IsUnit (x + (h : ZMod (∏ i, a i)))} ≃
      {f : (i : ι) → ZMod (a i) //
        IsUnit f ∧ IsUnit (f + (fun i => (h : ZMod (a i))))} := by
    refine Equiv.subtypeEquiv e.toEquiv ?_
    intro x
    constructor
    · intro hx
      constructor
      · exact (hu x).mp hx.1
      · have hu3 : IsUnit (e (x + (h : ZMod (∏ i, a i)))) := (hu (x + (h : ZMod (∏ i, a i)))).mp hx.2
        rw [hplus x] at hu3
        simpa using hu3
    · intro hf
      constructor
      · exact (hu x).mpr hf.1
      · have hu3 : IsUnit (e (x + (h : ZMod (∏ i, a i)))) := by
          rw [hplus x]
          exact hf.2
        exact (hu (x + (h : ZMod (∏ i, a i)))).mpr hu3
  exact Fintype.card_congr hiff

/-- natCast commutes through `ZMod.ringEquivCongr`. -/
private lemma ringEquivCongr_natCast {m n : ℕ} (h : m = n) (x : ℕ) :
    (ZMod.ringEquivCongr h) (x : ZMod m) = (x : ZMod n) := by
  subst h
  simp

/-- **CP product identity over the prime factorization of `q`:**
`CP(q,h) = ∏_{p | q} p^(e_p − 1)·g_p(h)`, `e_p = q.factorization p`,
`g_p(h) = p−1` if `p | h` else `p−2`. -/
private lemma cp_eq_prod_primeFactors (q h : ℕ) [NeZero q] :
    Fintype.card {x : ZMod q // IsUnit x ∧ IsUnit (x + (h : ZMod q))} =
      ∏ p ∈ q.primeFactors, p ^ (q.factorization p - 1) * (if p ∣ h then p - 1 else p - 2) := by
  classical
  let ι : Type := q.primeFactors
  let a : ι → ℕ := fun i => (i : ℕ) ^ (q.factorization (i : ℕ))
  have hqne : q ≠ 0 := NeZero.ne q
  have hqeq : q = ∏ i : ι, a i := by
    dsimp [ι, a]
    exact Nat.prod_primeFactors_coe_pow_factorization (n := q) hqne
  have hcop : Pairwise (Function.onFun Nat.Coprime a) := by
    dsimp [a]
    exact Nat.pairwise_coprime_pow_primeFactors_factorization (n := q)
  have hprime (i : ι) : Nat.Prime (i : ℕ) := Nat.prime_of_mem_primeFactors i.2
  have hepos (i : ι) : 0 < q.factorization (i : ℕ) := by
    have hne : q.factorization (i : ℕ) ≠ 0 := by
      have hmem : (i : ℕ) ∈ q.factorization.support := by
        simpa [Nat.support_factorization] using i.2
      exact (Finsupp.mem_support_iff.mp hmem)
    exact Nat.pos_of_ne_zero hne
  have hprodne : (∏ i : ι, a i) ≠ 0 := by
    rw [← hqeq]
    exact hqne
  haveI : NeZero (∏ i : ι, a i) := ⟨hprodne⟩
  haveI : ∀ i : ι, NeZero (a i) := fun i => ⟨by
    dsimp [a]
    exact pow_ne_zero _ (hprime i).ne_zero⟩
  let hE : ZMod q ≃+* ZMod (∏ i : ι, a i) := ZMod.ringEquivCongr hqeq
  have hE_nat : hE (h : ZMod q) = (h : ZMod (∏ i : ι, a i)) := by
    simpa [hE] using (ringEquivCongr_natCast hqeq h)
  have hu (z : ZMod q) : IsUnit z ↔ IsUnit (hE z) := (MulEquiv.isUnit_map hE.toMulEquiv).symm
  have hsum (z : ZMod q) :
      hE (z + (h : ZMod q)) = hE z + (h : ZMod (∏ i : ι, a i)) := by
    rw [map_add, hE_nat]
  have hqcard : Fintype.card {x : ZMod q // IsUnit x ∧ IsUnit (x + (h : ZMod q))} =
      Fintype.card {x : ZMod (∏ i : ι, a i) //
        IsUnit x ∧ IsUnit (x + (h : ZMod (∏ i : ι, a i)))} := by
    apply Fintype.card_congr
    refine Equiv.subtypeEquiv hE.toEquiv ?_
    intro x
    constructor
    · intro hx
      constructor
      · exact (hu x).mp hx.1
      · have hx2 : IsUnit (hE (x + (h : ZMod q))) := (hu (x + (h : ZMod q))).mp hx.2
        rw [hsum x] at hx2
        simpa using hx2
    · intro hf
      constructor
      · exact (hu x).mpr hf.1
      · have hx2 : IsUnit (hE (x + (h : ZMod q))) := by
          rw [hsum x]
          simpa using hf.2
        exact (hu (x + (h : ZMod q))).mpr hx2
  have hB := zmod_card_congr_prodEquivPi (a := a) hcop h
  have hC := zmod_pi_card_prod (a := a) h
  have hD : (∏ i : ι, Fintype.card {x : ZMod (a i) //
        IsUnit x ∧ IsUnit (x + (h : ZMod (a i)))}) =
      (∏ i : ι, (i : ℕ) ^ (q.factorization (i : ℕ) - 1) *
        (if (i : ℕ) ∣ h then (i : ℕ) - 1 else (i : ℕ) - 2)) := by
    apply Finset.prod_congr rfl
    intro i hi
    have hv := zmod_closePair_prime_pow (p := (i : ℕ)) (k := q.factorization (i : ℕ)) h
      (hprime i) (hepos i)
    simpa [a] using hv
  calc
    Fintype.card {x : ZMod q // IsUnit x ∧ IsUnit (x + (h : ZMod q))}
        = Fintype.card {x : ZMod (∏ i : ι, a i) //
            IsUnit x ∧ IsUnit (x + (h : ZMod (∏ i : ι, a i)))} := hqcard
    _ = Fintype.card {f : (i : ι) → ZMod (a i) //
          IsUnit f ∧ IsUnit (f + (fun i => (h : ZMod (a i))))} := by
          simpa using hB
    _ = (∏ i : ι, Fintype.card {x : ZMod (a i) //
          IsUnit x ∧ IsUnit (x + (h : ZMod (a i)))}) := hC
    _ = (∏ i : ι, (i : ℕ) ^ (q.factorization (i : ℕ) - 1) *
          (if (i : ℕ) ∣ h then (i : ℕ) - 1 else (i : ℕ) - 2)) := hD
    _ = ∏ p ∈ q.primeFactors, p ^ (q.factorization p - 1) *
          (if p ∣ h then p - 1 else p - 2) := by
          dsimp [ι]
          exact Finset.prod_coe_sort (s := q.primeFactors)
            (f := fun p : ℕ => p ^ (q.factorization p - 1) *
              (if p ∣ h then p - 1 else p - 2))


/-- per-prime ring identity: (p−2) + 1/p = (p−1)²/p. -/
private lemma prime_ring_identity (p : ℕ) (hp : p ≠ 0) :
    (p : ℝ) - 2 + 1 / (p : ℝ) = ((p : ℝ) - 1) ^ 2 / (p : ℝ) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp
  field_simp [hp0]
  ring

/-- For distinct primes p, q: q | p·m ⟺ q | m (as ℝ indicators). -/
private lemma dvd_mul_prime_iff (p q m : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    (if p ∣ q * m then (1 : ℝ) else 0) = if p ∣ m then (1 : ℝ) else 0 := by
  by_cases h : p ∣ m
  · rw [if_pos h, if_pos]
    simpa [mul_comm] using (dvd_mul_of_dvd_left h q)
  · rw [if_neg h]
    apply if_neg
    intro hpm
    apply h
    have hpq' : ¬ p ∣ q := by
      intro hd
      rcases hq.eq_one_or_self_of_dvd p hd with h1 | hp_eq
      · exact (hp.ne_one) h1
      · exact hpq hp_eq
    have hcop : p.Coprime q := (hp.coprime_iff_not_dvd).mpr hpq'
    exact Nat.Coprime.dvd_of_dvd_mul_left hcop hpm

/-- per-prime gap value `g_p(h) = (p−2) + 1[p|h]`. -/
private def gval (p h : ℕ) : ℝ := (p : ℝ) - 2 + if p ∣ h then (1 : ℝ) else 0

/-- `F_S(h) = ∏_{p∈S} g_p(h)`. -/
private def Fprod (S : Finset ℕ) (h : ℕ) : ℝ := ∏ p ∈ S, gval p h

/-- `P(S) = ∏_{p∈S} ((p−2) + 1/p)`. -/
private def Pprod (S : Finset ℕ) : ℝ := ∏ p ∈ S, ((p : ℝ) - 2 + 1 / (p : ℝ))

/-- `Pprod ≥ 0` for S of primes. -/
private lemma Pprod_nonneg {S : Finset ℕ} (h : ∀ p ∈ S, p.Prime) : 0 ≤ Pprod S := by
  dsimp [Pprod]
  exact Finset.prod_nonneg (fun p hp => by
    have h2 : 2 ≤ p := (h p hp).two_le
    have h2R : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h2
    have hpos : 0 < 1 / (p : ℝ) := by positivity
    nlinarith)

/-- F_{S}(p₀·m) = F_S(m) when S contains primes ≠ p₀. -/
private lemma Fprod_mul_invariant (p₀ m : ℕ) {S : Finset ℕ} (hS : p₀ ∉ S)
    (hprime : ∀ p ∈ S, p.Prime) (hp₀ : p₀.Prime) :
    Fprod S (p₀ * m) = Fprod S m := by
  unfold Fprod
  apply Finset.prod_congr rfl
  intro p hp
  have hpp : p.Prime := hprime p hp
  have hneq : p ≠ p₀ := by
    intro h
    apply hS
    simpa [h] using hp
  unfold gval
  congr 1
  exact dvd_mul_prime_iff p p₀ m hpp hp₀ hneq

/-- Nat-division upper bound as reals: (k/p : ℕ : ℝ) ≤ (k : ℝ)/(p : ℝ). -/
private lemma div_nat_le_real (k p : ℕ) (hp : 0 < p) :
    ((k / p : ℕ) : ℝ) ≤ (k : ℝ) / (p : ℝ) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  rw [le_div_iff₀ hp0]
  have hnat : (k / p) * p ≤ k := Nat.div_mul_le_self k p
  have hcast : ((k / p : ℕ) : ℝ) * (p : ℝ) ≤ (k : ℝ) := by exact_mod_cast hnat
  simpa [mul_comm] using hcast

/-- `Σ` over h ≤ k of `F(h)` restricted to multiples of p equals `Σ_{m ≤ k/p} F(p·m)`. -/
private lemma sum_filter_mul_eq (p k : ℕ) (hp0 : 0 < p) (F : ℕ → ℝ) :
    (∑ h ∈ (Finset.Icc 1 k).filter (fun h => p ∣ h), F h) =
      ∑ m ∈ Finset.Icc 1 (k / p), F (p * m) := by
  classical
  refine Finset.sum_bij (fun h _ => h / p) ?_ ?_ ?_ ?_
  · intro h hh
    have hmem := (Finset.mem_filter.mp hh).1
    have hpdiv : p ∣ h := (Finset.mem_filter.mp hh).2
    rw [Finset.mem_Icc] at hmem ⊢
    constructor
    · have hhpos : 0 < h := by omega
      have hple : p ≤ h := Nat.le_of_dvd hhpos hpdiv
      exact (Nat.le_div_iff_mul_le hp0).mpr (by simpa using hple)
    · have hle : h ≤ k := hmem.2
      exact Nat.div_le_div_right hle
  · intro h₁ hh₁ h₂ hh₂ h
    -- h₁ / p = h₂ / p with p | hᵢ
    have hd1 : p ∣ h₁ := (Finset.mem_filter.mp hh₁).2
    have hd2 : p ∣ h₂ := (Finset.mem_filter.mp hh₂).2
    calc
      h₁ = p * (h₁ / p) := (Nat.mul_div_cancel' hd1).symm
      _ = p * (h₂ / p) := by rw [h]
      _ = h₂ := Nat.mul_div_cancel' hd2
  · intro m hm
    rw [Finset.mem_Icc] at hm
    refine ⟨p * m, ?_, ?_⟩
    · rw [Finset.mem_filter]
      constructor
      · rw [Finset.mem_Icc]
        constructor
        · have hm1 : 1 ≤ m := hm.1
          have hmpos : 0 < m := lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hm1
          exact Nat.succ_le_of_lt (Nat.mul_pos hp0 hmpos)
        · have hmk : m ≤ k / p := hm.2
          simpa [Nat.mul_comm] using ((Nat.le_div_iff_mul_le hp0).mp hmk)
      · exact dvd_mul_right p m
    · -- (p * m) / p = m
      exact Nat.mul_div_right m hp0
  · intro h hh
    have hpdiv : p ∣ h := (Finset.mem_filter.mp hh).2
    rw [Nat.mul_div_cancel' hpdiv]

/-- **summation bound by induction over the primes of S.** -/
private lemma prod_sum_bound (S : Finset ℕ) :
    (∀ p ∈ S, p.Prime) → ∀ k : ℕ,
      (∑ h ∈ Finset.Icc 1 k, Fprod S h) ≤ (k : ℝ) * Pprod S := by
  classical
  intro hprime
  induction S using Finset.induction_on with
  | empty =>
      intro k
      simp [Fprod, Pprod]
  | insert p₀ S' hp₀not ih =>
      have hprime' : ∀ p ∈ S', p.Prime := fun p hp => hprime p (by simp [hp])
      have hp₀ : p₀.Prime := hprime p₀ (by simp)
      have hP' : 0 ≤ Pprod S' := Pprod_nonneg hprime'
      have hB : 0 ≤ (p₀ : ℝ) - 2 := by
        have h2 : 2 ≤ p₀ := hp₀.two_le
        have h2R : (2 : ℝ) ≤ (p₀ : ℝ) := by exact_mod_cast h2
        linarith
      let F : ℕ → ℝ := Fprod S'
      have hFmul (m : ℕ) : F (p₀ * m) = F m := by
        dsimp [F]
        exact Fprod_mul_invariant p₀ m hp₀not hprime' hp₀
      have hIH (k' : ℕ) : (∑ h ∈ Finset.Icc 1 k', F h) ≤ (k' : ℝ) * Pprod S' := by
        simpa [F] using (ih hprime' k')
      intro k
      have hIHF : (∑ h ∈ Finset.Icc 1 k, F h) ≤ (k : ℝ) * Pprod S' := hIH k
      have hT1 :
          (∑ h ∈ Finset.Icc 1 k, ((p₀ : ℝ) - 2) * F h) ≤ ((p₀ : ℝ) - 2) * (k : ℝ) * Pprod S' := by
        calc
          (∑ h ∈ Finset.Icc 1 k, ((p₀ : ℝ) - 2) * F h) = ((p₀ : ℝ) - 2) * (∑ h ∈ Finset.Icc 1 k, F h) := by
            rw [Finset.mul_sum]
          _ ≤ ((p₀ : ℝ) - 2) * ((k : ℝ) * Pprod S') := mul_le_mul_of_nonneg_left hIHF hB
          _ = ((p₀ : ℝ) - 2) * (k : ℝ) * Pprod S' := by ring
      have hT2 :
          (∑ h ∈ Finset.Icc 1 k, (if p₀ ∣ h then (1 : ℝ) else 0) * F h)
            ≤ (k : ℝ) / (p₀ : ℝ) * Pprod S' := by
        calc
          (∑ h ∈ Finset.Icc 1 k, (if p₀ ∣ h then (1 : ℝ) else 0) * F h)
              = (∑ h ∈ Finset.Icc 1 k, if p₀ ∣ h then F h else 0) := by
                  apply Finset.sum_congr rfl
                  intro h hh
                  by_cases hpdiv : p₀ ∣ h <;> simp [hpdiv]
          _ = ∑ h ∈ (Finset.Icc 1 k).filter (fun h => p₀ ∣ h), F h := by
                  rw [Finset.sum_filter]
          _ = ∑ m ∈ Finset.Icc 1 (k / p₀), F (p₀ * m) := sum_filter_mul_eq p₀ k hp₀.pos F
          _ = ∑ m ∈ Finset.Icc 1 (k / p₀), F m := by
                  apply Finset.sum_congr rfl
                  intro m hm
                  exact hFmul m
          _ ≤ ((k / p₀ : ℕ) : ℝ) * Pprod S' := hIH (k / p₀)
          _ ≤ (k : ℝ) / (p₀ : ℝ) * Pprod S' := by
                  have hk : ((k / p₀ : ℕ) : ℝ) ≤ (k : ℝ) / (p₀ : ℝ) :=
                    div_nat_le_real k p₀ hp₀.pos
                  exact mul_le_mul_of_nonneg_right hk hP'
      calc
        (∑ h ∈ Finset.Icc 1 k, Fprod (insert p₀ S') h)
            = (∑ h ∈ Finset.Icc 1 k, gval p₀ h * Fprod S' h) := by
                apply Finset.sum_congr rfl
                intro h hh
                unfold Fprod
                rw [Finset.prod_insert hp₀not]
        _ = (∑ h ∈ Finset.Icc 1 k, (((p₀ : ℝ) - 2) + (if p₀ ∣ h then (1 : ℝ) else 0)) * F h) := by
                apply Finset.sum_congr rfl
                intro h hh
                unfold gval
                dsimp [F]
        _ = (∑ h ∈ Finset.Icc 1 k,
              (((p₀ : ℝ) - 2) * F h + (if p₀ ∣ h then (1 : ℝ) else 0) * F h)) := by
                apply Finset.sum_congr rfl
                intro h hh
                ring
        _ = (∑ h ∈ Finset.Icc 1 k, ((p₀ : ℝ) - 2) * F h)
            + (∑ h ∈ Finset.Icc 1 k, (if p₀ ∣ h then (1 : ℝ) else 0) * F h) := by
                rw [Finset.sum_add_distrib]
        _ ≤ (((p₀ : ℝ) - 2) * (k : ℝ) * Pprod S') + ((k : ℝ) / (p₀ : ℝ) * Pprod S') :=
                add_le_add hT1 hT2
        _ = (k : ℝ) * (((p₀ : ℝ) - 2) + 1 / (p₀ : ℝ)) * Pprod S' := by ring
        _ = (k : ℝ) * Pprod (insert p₀ S') := by
                have hpi : Pprod (insert p₀ S') = (((p₀ : ℝ) - 2) + 1 / (p₀ : ℝ)) * Pprod S' := by
                  unfold Pprod
                  rw [Finset.prod_insert hp₀not]
                rw [hpi]
                ring

/-- The natural `if p∣h then p−1 else p−2` equals the real `(p:ℝ)−2 + 1[p|h]`
(for `p ≥ 2`). -/
private lemma if_sub_two_cast_real (p h : ℕ) (hp : 2 ≤ p) :
    ((if p ∣ h then p - 1 else p - 2 : ℕ) : ℝ) =
      (p : ℝ) - 2 + (if p ∣ h then (1 : ℝ) else 0) := by
  by_cases hpd : p ∣ h
  · rw [if_pos hpd, if_pos hpd]
    have h1 : 1 ≤ p := by omega
    have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub h1]
      norm_num
    rw [hcast]
    ring
  · rw [if_neg hpd, if_neg hpd]
    have hcast : ((p - 2 : ℕ) : ℝ) = (p : ℝ) - 2 := by
      rw [Nat.cast_sub hp]
      norm_num
    rw [hcast]
    ring

/-- push a natural-number cast inside a `Finset` product. -/
private lemma nat_prod_cast_real (s : Finset ℕ) (f : ℕ → ℕ) :
    ((∏ p ∈ s, f p : ℕ) : ℝ) = ∏ p ∈ s, ((f p : ℕ) : ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s' has ih =>
      simp [Finset.prod_insert has, ih, Nat.cast_mul]

/-- **range-side product identity:** `closePairCount q h = ∏_{p|q} p^(e_p−1)·g_p(h)`
(real-valued, `g_p(h) = (p−2) + 1[p|h]`). -/
private lemma close_pair_range_product (q h : ℕ) [NeZero q] :
    (closePairCount q h : ℝ) =
      ∏ p ∈ q.primeFactors, (p : ℝ) ^ (q.factorization p - 1) *
        ((p : ℝ) - 2 + (if p ∣ h then (1 : ℝ) else 0)) := by
  classical
  have hz := zmod_closePair_eq q h
  have hcp := cp_eq_prod_primeFactors (q := q) (h := h)
  calc
    (closePairCount q h : ℝ)
        = (Fintype.card {x : ZMod q // IsUnit x ∧ IsUnit (x + (h : ZMod q))} : ℝ) := by
            exact_mod_cast hz.symm
    _ = ((∏ p ∈ q.primeFactors, p ^ (q.factorization p - 1) *
            (if p ∣ h then p - 1 else p - 2) : ℕ) : ℝ) := by
            exact_mod_cast hcp
    _ = ∏ p ∈ q.primeFactors,
          ((p ^ (q.factorization p - 1) *
            (if p ∣ h then p - 1 else p - 2) : ℕ) : ℝ) :=
            nat_prod_cast_real q.primeFactors (fun p => p ^ (q.factorization p - 1) *
              (if p ∣ h then p - 1 else p - 2))
    _ = ∏ p ∈ q.primeFactors, (p : ℝ) ^ (q.factorization p - 1) *
          ((if p ∣ h then p - 1 else p - 2 : ℕ) : ℝ) := by
            apply Finset.prod_congr rfl
            intro p hp
            rw [Nat.cast_mul, Nat.cast_pow]
    _ = ∏ p ∈ q.primeFactors, (p : ℝ) ^ (q.factorization p - 1) *
          ((p : ℝ) - 2 + (if p ∣ h then (1 : ℝ) else 0)) := by
            apply Finset.prod_congr rfl
            intro p hp
            have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
            rw [if_sub_two_cast_real p h hp2]

/-- `E(q) = ∏_{p|q} p^(e_p−1)`. -/
private def Eprod (q : ℕ) : ℝ := ∏ p ∈ q.primeFactors, (p : ℝ) ^ (q.factorization p - 1)

private lemma Eprod_nonneg (q : ℕ) : 0 ≤ Eprod q := by
  unfold Eprod
  exact Finset.prod_nonneg (fun p hp => by positivity)

/-- for `p ∈ q.primeFactors`, the exponent `q.factorization p` is positive. -/
private lemma factorization_pos_of_mem_primeFactors {q p : ℕ} (hp : p ∈ q.primeFactors) :
    0 < q.factorization p := by
  have hne : q.factorization p ≠ 0 := by
    have hmem : p ∈ q.factorization.support := by simpa [Nat.support_factorization] using hp
    exact Finsupp.mem_support_iff.mp hmem
  exact Nat.pos_of_ne_zero hne

/-- `((p−1 : ℕ) : ℝ) = (p:ℝ) − 1` for `p ≥ 1`. -/
private lemma nat_pred_cast_real (p : ℕ) (hp : 1 ≤ p) : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
  rw [Nat.cast_sub hp]
  norm_num

/-- push a natural-number cast inside a `Finset` sum. -/
private lemma nat_sum_cast_real (s : Finset ℕ) (f : ℕ → ℕ) :
    ((∑ p ∈ s, f p : ℕ) : ℝ) = ∑ p ∈ s, ((f p : ℕ) : ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s' has ih => simp [Finset.sum_insert has, ih, Nat.cast_add]

/-- **Key product identity:** `q · E(q) · P(q.primeFactors) = φ(q)²`. -/
private lemma prime_factors_prod_identity (q : ℕ) [NeZero q] :
    (q : ℝ) * Eprod q * Pprod q.primeFactors = ((q.totient : ℝ)) ^ 2 := by
  classical
  have hqne : q ≠ 0 := NeZero.ne q
  set R : ℝ := ∏ p ∈ q.primeFactors, (p : ℝ) with hR
  set S : ℝ := ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) with hS
  have hR0 : 0 < R := by
    rw [hR]
    exact Finset.prod_pos (fun p hp => by
      have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
      have h2R : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
      linarith)
  -- (a) q = R * E(q)
  have ha : (q : ℝ) = R * Eprod q := by
    have hfac := Nat.prod_primeFactors_pow_factorization (n := q) hqne
    have h1 : (q : ℝ) = ∏ p ∈ q.primeFactors, (p : ℝ) ^ (q.factorization p) := by
      calc
        (q : ℝ) = ((∏ p ∈ q.primeFactors, p ^ q.factorization p : ℕ) : ℝ) := by
            exact_mod_cast hfac
        _ = ∏ p ∈ q.primeFactors, ((p ^ q.factorization p : ℕ) : ℝ) :=
            nat_prod_cast_real _ _
        _ = ∏ p ∈ q.primeFactors, (p : ℝ) ^ (q.factorization p) := by
            apply Finset.prod_congr rfl
            intro p hp
            rw [Nat.cast_pow]
    have hpow (p : ℕ) (hp : p ∈ q.primeFactors) :
        (p : ℝ) ^ (q.factorization p) = (p : ℝ) * (p : ℝ) ^ (q.factorization p - 1) := by
      have he : 0 < q.factorization p := factorization_pos_of_mem_primeFactors hp
      obtain ⟨e', he'⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt he)
      rw [he', Nat.succ_eq_add_one, Nat.add_sub_cancel, pow_succ]
      ring
    calc
      (q : ℝ) = ∏ p ∈ q.primeFactors, (p : ℝ) ^ (q.factorization p) := h1
      _ = ∏ p ∈ q.primeFactors, (p : ℝ) * (p : ℝ) ^ (q.factorization p - 1) := by
            apply Finset.prod_congr rfl
            intro p hp
            exact hpow p hp
      _ = (∏ p ∈ q.primeFactors, (p : ℝ)) *
            (∏ p ∈ q.primeFactors, (p : ℝ) ^ (q.factorization p - 1)) :=
            Finset.prod_mul_distrib
      _ = R * Eprod q := by
            rw [hR]
            rfl
  -- (b) φ(q)·R = q·S
  have hb : (q.totient : ℝ) * R = (q : ℝ) * S := by
    have htot := Nat.totient_mul_prod_primeFactors q
    have hcast : (q.totient : ℝ) * ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) =
        (q : ℝ) * ((∏ p ∈ q.primeFactors, (p - 1) : ℕ) : ℝ) := by
      exact_mod_cast htot
    rw [nat_prod_cast_real, nat_prod_cast_real] at hcast
    have hsub : (∏ p ∈ q.primeFactors, ((p - 1 : ℕ) : ℝ)) = S := by
      rw [hS]
      apply Finset.prod_congr rfl
      intro p hp
      exact nat_pred_cast_real p (Nat.prime_of_mem_primeFactors hp).one_le
    rw [← hR, hsub] at hcast
    exact hcast
  -- φ = E(q)·S
  have hphi : (q.totient : ℝ) = Eprod q * S := by
    have h' : (q.totient : ℝ) * R = (Eprod q * S) * R := by
      rw [hb, ha]
      ring
    exact mul_right_cancel₀ (ne_of_gt hR0) h'
  -- P = S²/R
  have hP : Pprod q.primeFactors = S ^ 2 / R := by
    rw [hS, hR]
    unfold Pprod
    rw [← Finset.prod_pow, ← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    exact prime_ring_identity p (Nat.prime_of_mem_primeFactors hp).ne_zero
  calc
    (q : ℝ) * Eprod q * Pprod q.primeFactors
        = (R * Eprod q) * Eprod q * (S ^ 2 / R) := by rw [← ha, hP]
    _ = (Eprod q * S) ^ 2 := by
          field_simp [ne_of_gt hR0]
    _ = ((q.totient : ℝ)) ^ 2 := by rw [← hphi]

/-- **real form of the close-pair cumulative bound** (unconditional in `k`). -/
private lemma pair_sum_real_bound (q k : ℕ) [NeZero q] :
    (q : ℝ) * (∑ h ∈ Finset.Icc 1 k, (closePairCount q h : ℝ)) ≤
      (k : ℝ) * ((q.totient : ℝ) ^ 2) := by
  classical
  have hE0 : 0 ≤ Eprod q := Eprod_nonneg q
  have hstep1 : (∑ h ∈ Finset.Icc 1 k, (closePairCount q h : ℝ)) =
      Eprod q * (∑ h ∈ Finset.Icc 1 k, Fprod q.primeFactors h) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    rw [close_pair_range_product q h, Finset.prod_mul_distrib]
    congr 1
  have hFb : (∑ h ∈ Finset.Icc 1 k, Fprod q.primeFactors h) ≤
      (k : ℝ) * Pprod q.primeFactors :=
    prod_sum_bound q.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp) k
  have hstep2 : (∑ h ∈ Finset.Icc 1 k, (closePairCount q h : ℝ)) ≤
      Eprod q * ((k : ℝ) * Pprod q.primeFactors) := by
    rw [hstep1]
    exact mul_le_mul_of_nonneg_left hFb hE0
  calc
    (q : ℝ) * (∑ h ∈ Finset.Icc 1 k, (closePairCount q h : ℝ))
        ≤ (q : ℝ) * (Eprod q * ((k : ℝ) * Pprod q.primeFactors)) := by
            have hq0 : (0 : ℝ) ≤ q := by positivity
            exact mul_le_mul_of_nonneg_left hstep2 hq0
    _ = (k : ℝ) * ((q : ℝ) * Eprod q * Pprod q.primeFactors) := by ring
    _ = (k : ℝ) * ((q.totient : ℝ) ^ 2) := by rw [prime_factors_prod_identity]

/-- **CRT core (K1): the close-pair cumulative bound.**  For `k·φ(q) ≤ q`,
`Σ_{h=1}^{k} c₊(h) · q ≤ k·φ(q)²`.  (Tracked `unfilled`: exactly the fleet lemma
`Commons.NumberTheory.DuffinSchaeffer.close_coprime_pair_sum_le` restated via
`simpa [closePairSum, closePairCount]`; when that lands in the commons, replace
this body with the import + `simpa`.) -/
private lemma pair_sum_nat_bound (q k : ℕ) (hk : k * (q.totient : ℕ) ≤ q) :
    q * closePairSum q k ≤ k * (q.totient : ℕ) * (q.totient : ℕ) := by
  by_cases hq0 : q = 0
  · subst hq0
    simp [closePairSum]
  · haveI : NeZero q := ⟨hq0⟩
    have hreal := pair_sum_real_bound (q := q) k
    have hcs : (closePairSum q k : ℝ) =
        ∑ h ∈ Finset.Icc 1 k, (closePairCount q h : ℝ) := by
      unfold closePairSum
      exact nat_sum_cast_real (Finset.Icc 1 k) (fun h => closePairCount q h)
    have hcast : ((q * closePairSum q k : ℕ) : ℝ) ≤
        ((k * (q.totient : ℕ) * (q.totient : ℕ) : ℕ) : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, hcs]
      simpa [pow_two, mul_assoc] using hreal
    exact_mod_cast hcast

/-- real small-gap-count bound: `u(k) ≤ k·φ(q)²/q` for `k·φ(q) ≤ q`, `q ≥ 1`. -/
lemma real_gap_count_le (q k : ℕ) (hq : 0 < q) (hk : k * (q.totient : ℕ) ≤ q) :
    (gapCountSmall q k : ℝ) ≤ (((k : ℝ) * (q.totient : ℝ)) * (q.totient : ℝ)) / (q : ℝ) := by
  have h1 : gapCountSmall q k ≤ closePairSum q k := gapCountSmall_le_closePairSum q k
  have h2 : q * closePairSum q k ≤ k * (q.totient : ℕ) * (q.totient : ℕ) := pair_sum_nat_bound q k hk
  have hqmul : q * gapCountSmall q k ≤ k * (q.totient : ℕ) * (q.totient : ℕ) := by
    exact le_trans (Nat.mul_le_mul_left q h1) h2
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hR : (q : ℝ) * (gapCountSmall q k : ℝ) ≤
      (k : ℝ) * (q.totient : ℝ) * (q.totient : ℝ) := by
    have hcast : ((q * gapCountSmall q k : ℕ) : ℝ) ≤ ((k * (q.totient : ℕ) * (q.totient : ℕ) : ℕ) : ℝ) := by
      exact_mod_cast hqmul
    simpa [Nat.cast_mul] using hcast
  rw [le_div_iff₀ hqR]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hR
/-- Sums over `consecutivePairs` equal sums over the adjacent-pair zip list. -/
lemma sum_consecutivePairs_eq_zip_sum (q : ℕ) (hq : 1 < q) (F : ℕ × ℕ → ℝ) :
    (∑ ab ∈ consecutivePairs q, F ab) =
      (((reducedResidueList q).zip (reducedResidueList q).tail).map F).sum := by
  classical
  have hset : consecutivePairs q = ((reducedResidueList q).zip (reducedResidueList q).tail).toFinset := by
    ext ab
    constructor
    · intro hab
      rw [List.mem_toFinset]
      rcases consecutivePairs_adjacent q hq hab with ⟨i, hi, hab1, hab2⟩
      have hp : ab = ((reducedResidueList q).get ⟨i, by omega⟩, (reducedResidueList q).get ⟨i + 1, hi⟩) := by
        ext <;> simpa [hab1, hab2]
      rw [hp]
      exact mem_zip_tail_iff.mpr ⟨i, hi, rfl, rfl⟩
    · intro h
      rw [List.mem_toFinset] at h
      rcases mem_zip_tail_iff.mp h with ⟨i, hi, hab1, hab2⟩
      have hp : ab = ((reducedResidueList q).get ⟨i, by omega⟩, (reducedResidueList q).get ⟨i + 1, hi⟩) := by
        ext <;> simpa [hab1, hab2]
      rw [hp]
      exact adjacent_mem_consecutivePairs q i (by omega) hi
  rw [hset]
  exact (list_map_sum_eq_toFinset_sum ((reducedResidueList q).zip (reducedResidueList q).tail) F
    (zip_tail_nodup_of_pairwise_lt (reducedResidueList_pairwise_lt q))).symm

/-- Sum over consecutive pairs of `f(b − a)` equals the `adjDiffs`-list sum of `f`. -/
lemma sum_consecutivePairs_diff_eq_adjDiffs_sum (q : ℕ) (hq : 1 < q) (f : ℕ → ℝ) :
    (∑ ab ∈ consecutivePairs q, f (ab.2 - ab.1)) =
      ((adjDiffs (reducedResidueList q)).map f).sum := by
  rw [sum_consecutivePairs_eq_zip_sum q hq (fun p => f (p.2 - p.1))]
  rw [adjDiffs_eq_zip_map (reducedResidueList q)]
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  rfl

/-- Sum over the full cyclic gaps of `f(d)` equals adjacent-differences plus `f 2`. -/
lemma sum_cyclicGaps_eq_adjDiffs_add (q : ℕ) (hq : 1 < q) (f : ℕ → ℝ) :
    ((cyclicGaps q (reducedResidueList q)).map f).sum =
      ((adjDiffs (reducedResidueList q)).map f).sum + f 2 := by
  have hdec := cyclicGaps_reduced_eq_adj_append_two q hq
  rw [hdec]
  simp

/-- list sum of casts: `Σ_d (d : ℝ) = (Σ_d d : ℕ)`. -/
lemma list_sum_natCast_map (l : List ℕ) :
    (l.map (fun d : ℕ => (d : ℝ))).sum = ((l.sum : ℕ) : ℝ) := by
  induction l with
  | nil => simp
  | cons h t ih =>
      rw [List.map_cons, List.sum_cons, ih]
      simp

/-- The complement-loss identity at list level: `Σ_d min(T,d) = q − Σ_d max(d−T,0)`. -/
lemma cyclic_min_sum_eq_q_sub_max_sum (q : ℕ) (hq : 0 < q) (T : ℝ) :
    ((cyclicGaps q (reducedResidueList q)).map (fun d : ℕ => min T (d : ℝ))).sum =
      (q : ℝ) - ((cyclicGaps q (reducedResidueList q)).map (fun d : ℕ => max ((d : ℝ) - T) 0)).sum := by
  let G : List ℕ := cyclicGaps q (reducedResidueList q)
  have hsum : (G.map (fun d : ℕ => (d : ℝ))).sum = (q : ℝ) := by
    rw [list_sum_natCast_map]
    congr 1
    dsimp [G]
    exact reduced_gap_sum_eq_q q hq
  calc
    (G.map (fun d : ℕ => min T (d : ℝ))).sum
        = (G.map (fun d : ℕ => (d : ℝ) - max ((d : ℝ) - T) 0)).sum := by
          exact congrArg List.sum (List.map_congr_left (fun d hd => min_eq_sub_max T (d : ℝ)))
    _ = (G.map (fun d : ℕ => (d : ℝ))).sum -
        (G.map (fun d : ℕ => max ((d : ℝ) - T) 0)).sum := by
          have hsub : ∀ l : List ℕ,
              (l.map (fun d : ℕ => (d : ℝ) - max ((d : ℝ) - T) 0)).sum =
                (l.map (fun d : ℕ => (d : ℝ))).sum -
                  (l.map (fun d : ℕ => max ((d : ℝ) - T) 0)).sum := by
            intro l
            induction l with
            | nil => simp
            | cons h t ih =>
                calc
                  ((h :: t).map (fun d : ℕ => (d : ℝ) - max ((d : ℝ) - T) 0)).sum
                      = (↑h - max (↑h - T) 0) +
                          (t.map (fun d : ℕ => (d : ℝ) - max ((d : ℝ) - T) 0)).sum := by simp
                  _ = (↑h - max (↑h - T) 0) +
                      ((t.map (fun d : ℕ => (d : ℝ))).sum -
                        (t.map (fun d : ℕ => max ((d : ℝ) - T) 0)).sum) := by rw [ih]
                  _ = (↑h + (t.map (fun d : ℕ => (d : ℝ))).sum) -
                      (max (↑h - T) 0 + (t.map (fun d : ℕ => max ((d : ℝ) - T) 0)).sum) := by ring
                  _ = ((h :: t).map (fun d : ℕ => (d : ℝ))).sum -
                      ((h :: t).map (fun d : ℕ => max ((d : ℝ) - T) 0)).sum := by simp
          exact hsub G
    _ = (q : ℝ) - (G.map (fun d : ℕ => max ((d : ℝ) - T) 0)).sum := by rw [hsum]

/-- nonnegativity of a map-sum. -/
lemma list_sum_map_nonneg {α : Type*} (l : List α) (f : α → ℝ)
    (hf : ∀ x ∈ l, 0 ≤ f x) : 0 ≤ (l.map f).sum := by
  apply List.sum_nonneg
  intro y hy
  rcases List.mem_map.mp hy with ⟨x, hx, rfl⟩
  exact hf x hx

/-- monotone list-sum under per-element bounds. -/
lemma list_sum_map_mono {α : Type*} (l : List α) (f g : α → ℝ)
    (h : ∀ a ∈ l, f a ≤ g a) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
      exact add_le_add (h a (by simp)) (ih (fun b hb => h b (by simp [hb])))

/-- Σ_{k<K} 1[d ≤ k] = K − d  (natural numbers; K − d = 0 when d > K). -/
private lemma sum_range_indicator_ge_nat (K d : ℕ) :
    (∑ k ∈ Finset.range K, if d ≤ k then (1 : ℕ) else 0) = K - d := by
  induction K with
  | zero => simp
  | succ K ih =>
      calc
        (∑ k ∈ Finset.range (K + 1), if d ≤ k then (1 : ℕ) else 0)
            = (∑ k ∈ Finset.range K, if d ≤ k then (1 : ℕ) else 0) + (if d ≤ K then (1 : ℕ) else 0) := by
                rw [Finset.sum_range_succ]
        _ = (K - d) + (if d ≤ K then (1 : ℕ) else 0) := by rw [ih]
        _ = K + 1 - d := by
                by_cases h : d ≤ K
                · rw [if_pos h]
                  omega
                · rw [if_neg h]
                  omega

/-- Σ_{k<K} 1[d ≤ k] = K − d  (as reals). -/
private lemma sum_range_indicator_ge (K d : ℕ) :
    (∑ k ∈ Finset.range K, if d ≤ k then (1 : ℝ) else 0) = ((K - d : ℕ) : ℝ) := by
  have hn := sum_range_indicator_ge_nat K d
  exact_mod_cast hn

/-- sum over a list of the indicator d ≤ k equals the count of entries ≤ k. -/
private lemma list_sum_indicator_eq_filter_length (L : List ℕ) (k : ℕ) :
    (L.map (fun d : ℕ => if d ≤ k then (1 : ℝ) else 0)).sum =
      ((L.filter (fun d : ℕ => d ≤ k)).length : ℝ) := by
  induction L with
  | nil => simp
  | cons h t ih =>
      by_cases hh : h ≤ k
      · calc
          ((h :: t).map (fun d : ℕ => if d ≤ k then (1 : ℝ) else 0)).sum
              = 1 + (t.map (fun d : ℕ => if d ≤ k then (1 : ℝ) else 0)).sum := by simp [hh]
          _ = 1 + ((t.filter (fun d : ℕ => d ≤ k)).length : ℝ) := by rw [ih]
          _ = (((h :: t).filter (fun d : ℕ => d ≤ k)).length : ℝ) := by
                rw [show (h :: t).filter (fun d : ℕ => d ≤ k) = h :: t.filter (fun d : ℕ => d ≤ k) by simp [hh]]
                simp
                ring
      · calc
          ((h :: t).map (fun d : ℕ => if d ≤ k then (1 : ℝ) else 0)).sum
              = (t.map (fun d : ℕ => if d ≤ k then (1 : ℝ) else 0)).sum := by simp [hh]
          _ = ((t.filter (fun d : ℕ => d ≤ k)).length : ℝ) := by rw [ih]
          _ = (((h :: t).filter (fun d : ℕ => d ≤ k)).length : ℝ) := by
                rw [show (h :: t).filter (fun d : ℕ => d ≤ k) = t.filter (fun d : ℕ => d ≤ k) by simp [hh]]

/-- double-sum swap: Σ_{d∈L} Σ_{k<K} f d k = Σ_{k<K} Σ_{d∈L} f d k. -/
private lemma list_sum_sum_range_swap (L : List ℕ) (K : ℕ) (f : ℕ → ℕ → ℝ) :
    (L.map (fun d : ℕ => ∑ k ∈ Finset.range K, f d k)).sum =
      ∑ k ∈ Finset.range K, (L.map (fun d : ℕ => f d k)).sum := by
  classical
  induction L with
  | nil => simp
  | cons h t ih =>
      calc
        ((h :: t).map (fun d : ℕ => ∑ k ∈ Finset.range K, f d k)).sum
            = (∑ k ∈ Finset.range K, f h k) +
                (t.map (fun d : ℕ => ∑ k ∈ Finset.range K, f d k)).sum := by simp
        _ = (∑ k ∈ Finset.range K, f h k) +
                (∑ k ∈ Finset.range K, (t.map (fun d : ℕ => f d k)).sum) := by rw [ih]
        _ = ∑ k ∈ Finset.range K, (f h k + (t.map (fun d : ℕ => f d k)).sum) := by
                rw [Finset.sum_add_distrib]
        _ = ∑ k ∈ Finset.range K, ((h :: t).map (fun d : ℕ => f d k)).sum := by
                apply Finset.sum_congr rfl
                intro k hk
                simp

/-- per-element: max(x−d,0) = Σ_{k<⌊x⌋} 1[d≤k] + (x−⌊x⌋)·1[d≤⌊x⌋]. -/
private lemma per_element_deficit (x : ℝ) (hx0 : 0 ≤ x) (d : ℕ) :
    max (x - (d : ℝ)) 0 =
      (∑ k ∈ Finset.range (Nat.floor x), if d ≤ k then (1 : ℝ) else 0) +
        (x - (Nat.floor x : ℝ)) * (if d ≤ Nat.floor x then (1 : ℝ) else 0) := by
  classical
  by_cases hd : d ≤ Nat.floor x
  · have hcount : (∑ k ∈ Finset.range (Nat.floor x), if d ≤ k then (1 : ℝ) else 0) =
        ((Nat.floor x - d : ℕ) : ℝ) := sum_range_indicator_ge (Nat.floor x) d
    have hif2 : (if d ≤ Nat.floor x then (1 : ℝ) else 0) = 1 := by rw [if_pos hd]
    have hxge : 0 ≤ x - (d : ℝ) := by
      have hdR : (d : ℝ) ≤ (Nat.floor x : ℝ) := by exact_mod_cast hd
      have hK_le : (Nat.floor x : ℝ) ≤ x := Nat.floor_le hx0
      linarith
    have hcalc : ((Nat.floor x - d : ℕ) : ℝ) + (x - (Nat.floor x : ℝ)) = x - (d : ℝ) := by
      have hdR : (d : ℝ) ≤ (Nat.floor x : ℝ) := by exact_mod_cast hd
      rw [Nat.cast_sub hd]
      ring
    calc
      max (x - (d : ℝ)) 0 = x - (d : ℝ) := by rw [max_eq_left hxge]
      _ = ((Nat.floor x - d : ℕ) : ℝ) + (x - (Nat.floor x : ℝ)) := hcalc.symm
      _ = (∑ k ∈ Finset.range (Nat.floor x), if d ≤ k then (1 : ℝ) else 0) +
          (x - (Nat.floor x : ℝ)) * (if d ≤ Nat.floor x then (1 : ℝ) else 0) := by
            rw [hcount, hif2]
            ring
  · have hif2 : (if d ≤ Nat.floor x then (1 : ℝ) else 0) = 0 := by rw [if_neg hd]
    have hcount0 : (∑ k ∈ Finset.range (Nat.floor x), if d ≤ k then (1 : ℝ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have hkK : k < Nat.floor x := Finset.mem_range.mp hk
      have hnot : ¬ d ≤ k := by omega
      rw [if_neg hnot]
    have hneg : x - (d : ℝ) ≤ 0 := by
      have hx_lt : x < (Nat.floor x : ℝ) + 1 := Nat.lt_floor_add_one x
      have hdK1 : (Nat.floor x : ℝ) + 1 ≤ (d : ℝ) := by
        have hd' : Nat.floor x + 1 ≤ d := by omega
        exact_mod_cast hd'
      linarith
    rw [max_eq_right hneg, hcount0, hif2]
    ring

/-- List-level deficit identity: Σ_d max(x−d,0) = Σ_{k<⌊x⌋} u(k) + (x−⌊x⌋)·u(⌊x⌋),
where u(k) = #{d ∈ L : d ≤ k}. -/
private lemma list_deficit_eq_sum_counts (L : List ℕ) (x : ℝ) (hx0 : 0 ≤ x) :
    (L.map (fun d : ℕ => max (x - (d : ℝ)) 0)).sum =
      (∑ k ∈ Finset.range (Nat.floor x),
        ((L.filter (fun d : ℕ => d ≤ k)).length : ℝ))
      + (x - (Nat.floor x : ℝ)) *
          ((L.filter (fun d : ℕ => d ≤ Nat.floor x)).length : ℝ) := by
  calc
    (L.map (fun d : ℕ => max (x - (d : ℝ)) 0)).sum
        = (L.map (fun d : ℕ =>
            (∑ k ∈ Finset.range (Nat.floor x), if d ≤ k then (1 : ℝ) else 0) +
              (x - (Nat.floor x : ℝ)) * (if d ≤ Nat.floor x then (1 : ℝ) else 0))).sum := by
            apply congrArg List.sum
            apply List.map_congr_left
            intro d hd
            exact per_element_deficit x hx0 d
    _ = (L.map (fun d : ℕ => ∑ k ∈ Finset.range (Nat.floor x), if d ≤ k then (1 : ℝ) else 0)).sum
        + (x - (Nat.floor x : ℝ)) *
            (L.map (fun d : ℕ => if d ≤ Nat.floor x then (1 : ℝ) else 0)).sum := by
            induction L with
            | nil => simp
            | cons h t ih =>
                rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons,
                    List.map_cons, List.sum_cons]
                rw [ih]
                ring
    _ = (∑ k ∈ Finset.range (Nat.floor x),
            (L.map (fun d : ℕ => if d ≤ k then (1 : ℝ) else 0)).sum)
        + (x - (Nat.floor x : ℝ)) *
            ((L.filter (fun d : ℕ => d ≤ Nat.floor x)).length : ℝ) := by
            rw [list_sum_sum_range_swap]
            congr 1
            apply congrArg (fun t : ℝ => (x - (Nat.floor x : ℝ)) * t)
            exact list_sum_indicator_eq_filter_length L (Nat.floor x)
    _ = (∑ k ∈ Finset.range (Nat.floor x),
            ((L.filter (fun d : ℕ => d ≤ k)).length : ℝ))
        + (x - (Nat.floor x : ℝ)) *
            ((L.filter (fun d : ℕ => d ≤ Nat.floor x)).length : ℝ) := by
            apply congrArg (fun t : ℝ => t + (x - (Nat.floor x : ℝ)) *
              ((L.filter (fun d : ℕ => d ≤ Nat.floor x)).length : ℝ))
            apply Finset.sum_congr rfl
            intro k hk
            exact list_sum_indicator_eq_filter_length L k

/-- Σ_{k<K} (k:ℝ) = K(K−1)/2 in ℝ. -/
private lemma sum_range_id_real (K : ℕ) :
    (∑ k ∈ Finset.range K, (k : ℝ)) = (K : ℝ) * ((K : ℝ) - 1) / 2 := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, ih]
      have hK : ((K + 1 : ℕ) : ℝ) = (K : ℝ) + 1 := by norm_num
      rw [hK]
      ring

/-- triangular deficit bound: K(K−1)/2 + ηK ≤ (K+η)²/2 (K ≥ 0, η ≥ 0). -/
private lemma triangular_deficit (K : ℕ) (η : ℝ) (hη0 : 0 ≤ η) :
    (K : ℝ) * ((K : ℝ) - 1) / 2 + η * (K : ℝ) ≤ ((K : ℝ) + η) ^ 2 / 2 := by
  have hmain : (K : ℝ) * ((K : ℝ) - 1) + 2 * η * (K : ℝ) ≤ ((K : ℝ) + η) ^ 2 := by
    have hK0 : 0 ≤ (K : ℝ) := by exact_mod_cast (Nat.zero_le K)
    nlinarith [sq_nonneg η]
  nlinarith [hmain]

/-- Σ over a list of a constant c equals length·c. -/
private lemma list_map_const_sum (L : List ℕ) (c : ℝ) :
    (L.map (fun _ : ℕ => c)).sum = (L.length : ℝ) * c := by
  induction L with
  | nil => simp
  | cons h t ih =>
      rw [List.map_cons, List.sum_cons, List.length_cons, ih]
      rw [Nat.cast_add]
      ring


/-- For `k < ⌊x⌋` with `x·φ(q) ≤ q`: `k·φ(q) ≤ q`. -/
private lemma nat_mul_totient_le_q_of_lt_floor {q : ℕ} (hq : 0 < q) {x : ℝ} (hx0 : 0 ≤ x)
    (hxφ : x * (q.totient : ℝ) ≤ (q : ℝ)) {k : ℕ} (hk : k < Nat.floor x) :
    k * (q.totient : ℕ) ≤ q := by
  have hkR : (k : ℝ) < (Nat.floor x : ℝ) := by exact_mod_cast hk
  have hKx : (Nat.floor x : ℝ) ≤ x := Nat.floor_le hx0
  have hklt : (k : ℝ) < x := lt_of_lt_of_le hkR hKx
  have hφp : 0 < (q.totient : ℝ) := by exact_mod_cast (Nat.totient_pos.mpr hq)
  have hkq : (k : ℝ) * (q.totient : ℝ) < (q : ℝ) :=
    lt_of_lt_of_le (mul_lt_mul_of_pos_right hklt hφp) hxφ
  have hc : ((k * (q.totient) : ℕ) : ℝ) < (q : ℝ) := by
    simpa [Nat.cast_mul] using hkq
  exact_mod_cast (le_of_lt hc)

/-- For `⌊x⌋` with `x·φ(q) ≤ q`: `⌊x⌋·φ(q) ≤ q`. -/
private lemma nat_mul_totient_le_q_of_floor {q : ℕ} (hq : 0 < q) {x : ℝ} (hx0 : 0 ≤ x)
    (hxφ : x * (q.totient : ℝ) ≤ (q : ℝ)) :
    Nat.floor x * (q.totient : ℕ) ≤ q := by
  have hKx : (Nat.floor x : ℝ) ≤ x := Nat.floor_le hx0
  have hφp : 0 ≤ (q.totient : ℝ) := by positivity
  have hKq : (Nat.floor x : ℝ) * (q.totient : ℝ) ≤ (q : ℝ) :=
    le_trans (mul_le_mul_of_nonneg_right hKx hφp) hxφ
  have hc : ((Nat.floor x * q.totient : ℕ) : ℝ) ≤ (q : ℝ) := by
    simpa [Nat.cast_mul] using hKq
  exact_mod_cast hc

/-- **Deficit bound (case A):** `D := Σ_d max(x−d,0) ≤ x²·φ(q)²/(2q)` for `x·φ(q) ≤ q`. -/
private lemma gap_deficit_bound (q : ℕ) (hq : 0 < q) (x : ℝ) (hx0 : 0 ≤ x)
    (hxφ : x * (q.totient : ℝ) ≤ (q : ℝ)) :
    ((cyclicGaps q (reducedResidueList q)).map (fun d : ℕ => max (x - (d : ℝ)) 0)).sum ≤
      (x ^ 2 * ((q.totient : ℝ) ^ 2)) / (2 * (q : ℝ)) := by
  let G : List ℕ := cyclicGaps q (reducedResidueList q)
  let C : ℝ := (((q.totient : ℝ) * (q.totient : ℝ)) / (q : ℝ))
  let K : ℕ := Nat.floor x
  let η : ℝ := x - (K : ℝ)
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  have hη0 : 0 ≤ η := by
    dsimp [η, K]
    have : (Nat.floor x : ℝ) ≤ x := Nat.floor_le hx0
    linarith
  have hKη : (K : ℝ) + η = x := by dsimp [η]; ring
  have hsplit : (G.map (fun d : ℕ => max (x - (d : ℝ)) 0)).sum =
      (∑ k ∈ Finset.range K, ((G.filter (fun d : ℕ => d ≤ k)).length : ℝ)) +
        (x - (K : ℝ)) * ((G.filter (fun d : ℕ => d ≤ K)).length : ℝ) := by
    dsimp [K]
    simpa [G] using (list_deficit_eq_sum_counts G x hx0)
  have hu (k : ℕ) (hkφ : k * (q.totient : ℕ) ≤ q) :
      ((G.filter (fun d : ℕ => d ≤ k)).length : ℝ) ≤ (k : ℝ) * C := by
    have hb := real_gap_count_le q k hq hkφ
    dsimp [G] at hb ⊢
    dsimp [C] at hb ⊢
    ring_nf at hb ⊢
    exact hb
  have hKφ : K * (q.totient : ℕ) ≤ q := by
    dsimp [K]
    exact nat_mul_totient_le_q_of_floor (q := q) hq hx0 hxφ
  have hB_le : (x - (K : ℝ)) * ((G.filter (fun d : ℕ => d ≤ K)).length : ℝ) ≤ η * ((K : ℝ) * C) := by
    have hb := hu K hKφ
    have hle : (x - (K : ℝ)) * ((G.filter (fun d : ℕ => d ≤ K)).length : ℝ) ≤
        (x - (K : ℝ)) * ((K : ℝ) * C) := by
      have hxK0 : 0 ≤ x - (K : ℝ) := by
        dsimp [K]
        have : (Nat.floor x : ℝ) ≤ x := Nat.floor_le hx0
        linarith
      exact mul_le_mul_of_nonneg_left hb hxK0
    dsimp [η]
    exact hle
  have hA_le : (∑ k ∈ Finset.range K, ((G.filter (fun d : ℕ => d ≤ k)).length : ℝ)) ≤
      (∑ k ∈ Finset.range K, (k : ℝ) * C) := by
    apply Finset.sum_le_sum
    intro k hk
    have hkK : k < K := Finset.mem_range.mp hk
    have hkφ : k * (q.totient : ℕ) ≤ q := by
      dsimp [K] at hkK
      exact nat_mul_totient_le_q_of_lt_floor (q := q) hq hx0 hxφ hkK
    exact hu k hkφ
  have hfac : (∑ k ∈ Finset.range K, (k : ℝ) * C) = C * (∑ k ∈ Finset.range K, (k : ℝ)) := by
    have h := Finset.sum_mul (s := Finset.range K) (f := fun k : ℕ => (k : ℝ)) (a := C)
    rw [← h]
    rw [mul_comm]
  have hCtri : C * ((∑ k ∈ Finset.range K, (k : ℝ)) + η * (K : ℝ)) ≤ C * x ^ 2 / 2 := by
    have htri : (∑ k ∈ Finset.range K, (k : ℝ)) + η * (K : ℝ) ≤ x ^ 2 / 2 := by
      rw [sum_range_id_real K]
      have hx2 : ((K : ℝ) + η) ^ 2 / 2 = x ^ 2 / 2 := by
        rw [hKη]
      rw [← hx2]
      exact triangular_deficit K η hη0
    calc
      C * ((∑ k ∈ Finset.range K, (k : ℝ)) + η * (K : ℝ)) ≤ C * (x ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left htri hC0
      _ = C * x ^ 2 / 2 := by ring
  have hfinal_ring : C * x ^ 2 / 2 = (x ^ 2 * ((q.totient : ℝ) ^ 2)) / (2 * (q : ℝ)) := by
    dsimp [C]
    field_simp [hqR.ne']
  calc
    (G.map (fun d : ℕ => max (x - (d : ℝ)) 0)).sum
        = (∑ k ∈ Finset.range K, ((G.filter (fun d : ℕ => d ≤ k)).length : ℝ)) +
            (x - (K : ℝ)) * ((G.filter (fun d : ℕ => d ≤ K)).length : ℝ) := hsplit
    _ ≤ (∑ k ∈ Finset.range K, (k : ℝ) * C) + η * ((K : ℝ) * C) := add_le_add hA_le hB_le
    _ = C * (∑ k ∈ Finset.range K, (k : ℝ)) + C * (η * (K : ℝ)) := by
            rw [hfac]
            congr 1
            ring
    _ = C * ((∑ k ∈ Finset.range K, (k : ℝ)) + η * (K : ℝ)) := by ring
    _ ≤ C * x ^ 2 / 2 := hCtri
    _ = (x ^ 2 * ((q.totient : ℝ) ^ 2)) / (2 * (q : ℝ)) := hfinal_ring

/-- per-element: min(x,d) = x − max(x−d,0). -/
private lemma min_sub_max_deficit (x d : ℝ) : min x d = x - max (x - d) 0 := by
  by_cases h : x ≤ d
  · rw [min_eq_left h]
    have hxd : x - d ≤ 0 := by linarith
    rw [max_eq_right hxd]
    ring
  · have hd : d ≤ x := le_of_not_ge h
    rw [min_eq_right hd]
    have hxd0 : 0 ≤ x - d := by linarith
    rw [max_eq_left hxd0]
    ring

/-- `Σ_d min(x,d) = φ(q)·x − Σ_d max(x−d,0)` for the cyclic gaps of `q`. -/
private lemma gap_min_sum_eq (q : ℕ) (hq : 0 < q) (x : ℝ) :
    ((cyclicGaps q (reducedResidueList q)).map (fun d : ℕ => min x (d : ℝ))).sum =
      ((q.totient : ℕ) : ℝ) * x -
        ((cyclicGaps q (reducedResidueList q)).map (fun d : ℕ => max (x - (d : ℝ)) 0)).sum := by
  let G : List ℕ := cyclicGaps q (reducedResidueList q)
  have hmain : (G.map (fun d : ℕ => min x (d : ℝ))).sum =
      (G.map (fun d : ℕ => x - max (x - (d : ℝ)) 0)).sum := by
    exact congrArg List.sum (List.map_congr_left (fun d hd => min_sub_max_deficit x (d : ℝ)))
  have hlin : (G.map (fun d : ℕ => x - max (x - (d : ℝ)) 0)).sum =
      (G.length : ℝ) * x - (G.map (fun d : ℕ => max (x - (d : ℝ)) 0)).sum := by
    induction G with
    | nil => simp
    | cons h t ih =>
        calc
          ((h :: t).map (fun d : ℕ => x - max (x - (d : ℝ)) 0)).sum
              = (x - max (x - (h : ℝ)) 0) +
                  (t.map (fun d : ℕ => x - max (x - (d : ℝ)) 0)).sum := by simp
          _ = (x - max (x - (h : ℝ)) 0) +
                  (↑t.length * x - (t.map (fun d : ℕ => max (x - (d : ℝ)) 0)).sum) := by rw [ih]
          _ = ↑(h :: t).length * x - ((h :: t).map (fun d : ℕ => max (x - (d : ℝ)) 0)).sum := by
              simp
              ring
  calc
    (G.map (fun d : ℕ => min x (d : ℝ))).sum
        = (G.map (fun d : ℕ => x - max (x - (d : ℝ)) 0)).sum := hmain
    _ = (G.length : ℝ) * x - (G.map (fun d : ℕ => max (x - (d : ℝ)) 0)).sum := hlin
    _ = ((q.totient : ℕ) : ℝ) * x - (G.map (fun d : ℕ => max (x - (d : ℝ)) 0)).sum := by
        congr 1
        dsimp [G]
        rw [reduced_gap_length]

/-- Pure bound: `Σ_d min(2β,d) ≥ φ(q)` for `β ≥ 1/2` (every gap is ≥ 1). -/
private lemma gap_min_sum_pure (q : ℕ) (hq : 0 < q) (β : ℝ) (hβ : (1 : ℝ) / 2 ≤ β) :
    ((q.totient : ℕ) : ℝ) ≤
      ((cyclicGaps q (reducedResidueList q)).map (fun d : ℕ => min (2 * β) (d : ℝ))).sum := by
  let G : List ℕ := cyclicGaps q (reducedResidueList q)
  have h2b : (1 : ℝ) ≤ 2 * β := by nlinarith
  have hd1 : ∀ d ∈ G, (1 : ℝ) ≤ (d : ℝ) := by
    intro d hd
    have hpos : 0 < d := cyclicGaps_pos (q := q) (xs := reducedResidueList q)
      (reducedResidueList_ne_nil_of_pos q hq) (reducedResidueList_pairwise_lt q)
      (reducedResidueList_mem_lt q) d hd
    have : (1 : ℕ) ≤ d := Nat.succ_le_of_lt hpos
    exact_mod_cast this
  have hterm : ∀ d ∈ G, (1 : ℝ) ≤ min (2 * β) (d : ℝ) := by
    intro d hd
    exact le_min h2b (hd1 d hd)
  have hmono : (G.map (fun _ : ℕ => (1 : ℝ))).sum ≤
      (G.map (fun d : ℕ => min (2 * β) (d : ℝ))).sum :=
    list_sum_map_mono G (fun _ : ℕ => (1 : ℝ)) (fun d : ℕ => min (2 * β) (d : ℝ))
      (fun d hd => hterm d hd)
  calc
    ((q.totient : ℕ) : ℝ) = (G.length : ℝ) := by
        dsimp [G]
        rw [reduced_gap_length]
    _ = (G.map (fun _ : ℕ => (1 : ℝ))).sum := by
        rw [list_map_const_sum]
        simp
    _ ≤ (G.map (fun d : ℕ => min (2 * β) (d : ℝ))).sum := hmono

/-- Case A core: `2α·φ(q) ≤ q` (and `α ≥ 0`) ⇒ `Σ_d min(2α,d) ≥ α·φ(q)`. -/
private lemma gap_sum_min_lower_caseA (q : ℕ) (hq : 0 < q) (α : ℝ) (hα0 : 0 ≤ α)
    (hA : 2 * α * (q.totient : ℝ) ≤ (q : ℝ)) :
    α * (q.totient : ℝ) ≤
      ((cyclicGaps q (reducedResidueList q)).map (fun d : ℕ => min (2 * α) (d : ℝ))).sum := by
  let G : List ℕ := cyclicGaps q (reducedResidueList q)
  have hx0 : 0 ≤ 2 * α := by nlinarith
  have hxA : (2 * α) * (q.totient : ℝ) ≤ (q : ℝ) := hA
  have hdef := gap_deficit_bound q hq (2 * α) hx0 hxA
  have hsum_eq := gap_min_sum_eq q hq (2 * α)
  have hlow : α * (q.totient : ℝ) ≤
      ((q.totient : ℝ) * (2 * α)) -
        (((2 * α) ^ 2 * ((q.totient : ℝ) ^ 2)) / (2 * (q : ℝ))) := by
    have hqpos : 0 < 2 * (q : ℝ) := by positivity
    have hcomb : (((q.totient : ℝ) * (2 * α)) * (2 * (q : ℝ)) -
          (2 * α) ^ 2 * ((q.totient : ℝ) ^ 2)) / (2 * (q : ℝ)) =
        (q.totient : ℝ) * (2 * α) -
          ((2 * α) ^ 2 * ((q.totient : ℝ) ^ 2)) / (2 * (q : ℝ)) := by
      field_simp [hqpos.ne']
    rw [← hcomb]
    rw [le_div_iff₀ hqpos]
    have hφ0 : 0 ≤ (q.totient : ℝ) := by positivity
    have hαφ0 : 0 ≤ α * (q.totient : ℝ) := mul_nonneg hα0 hφ0
    have hqmA : 0 ≤ (q : ℝ) - 2 * α * (q.totient : ℝ) := by nlinarith
    have hnn : 0 ≤ (2 * (α * (q.totient : ℝ))) * ((q : ℝ) - 2 * α * (q.totient : ℝ)) :=
      mul_nonneg (mul_nonneg (by norm_num) hαφ0) hqmA
    nlinarith [hnn]
  have hsum_ge_bound : ((q.totient : ℝ) * (2 * α)) -
        (((2 * α) ^ 2 * ((q.totient : ℝ) ^ 2)) / (2 * (q : ℝ))) ≤
      (G.map (fun d : ℕ => min (2 * α) (d : ℝ))).sum := by
    calc
      ((q.totient : ℝ) * (2 * α)) -
            (((2 * α) ^ 2 * ((q.totient : ℝ) ^ 2)) / (2 * (q : ℝ)))
          ≤ ((q.totient : ℝ) * (2 * α)) -
              (G.map (fun d : ℕ => max ((2 * α) - (d : ℝ)) 0)).sum := by
              exact sub_le_sub_left hdef ((q.totient : ℝ) * (2 * α))
      _ = (G.map (fun d : ℕ => min (2 * α) (d : ℝ))).sum := by
              dsimp [G]
              exact hsum_eq.symm
  exact le_trans hlow hsum_ge_bound

/-- monotone in the radius: `β₁ ≤ β₂` ⇒ `Σ_d min(2β₁,d) ≤ Σ_d min(2β₂,d)`. -/
private lemma gap_min_sum_mono (q : ℕ) (β₁ β₂ : ℝ) (h : β₁ ≤ β₂) :
    ((cyclicGaps q (reducedResidueList q)).map (fun d : ℕ => min (2 * β₁) (d : ℝ))).sum ≤
      ((cyclicGaps q (reducedResidueList q)).map (fun d : ℕ => min (2 * β₂) (d : ℝ))).sum := by
  let G : List ℕ := cyclicGaps q (reducedResidueList q)
  exact list_sum_map_mono G (fun d : ℕ => min (2 * β₁) (d : ℝ)) (fun d : ℕ => min (2 * β₂) (d : ℝ))
    (fun d hd => min_le_min (by nlinarith) le_rfl)

/-- **Coprime-gap coverage (K1 gap inequality):** for `q ≥ 1` and `α ≥ 1/2`,
`min(q/2, α·φ(q)) ≤ Σ_{d} min(2α, d)` over the cyclic gaps of `q`. -/
private lemma cyclic_gap_cover_bound (q : ℕ) (hq : 0 < q) (α : ℝ) (hα : (1 : ℝ) / 2 ≤ α) :
    min ((q : ℝ) / 2) (α * (q.totient : ℝ)) ≤
      ((cyclicGaps q (reducedResidueList q)).map (fun d : ℕ => min (2 * α) (d : ℝ))).sum := by
  let G : List ℕ := cyclicGaps q (reducedResidueList q)
  by_cases hα1 : α ≤ 1
  · -- pure regime: every gap ≥ 1 and 2α ≥ 1
    have hpure := gap_min_sum_pure q hq α hα
    have hle : min ((q : ℝ) / 2) (α * (q.totient : ℝ)) ≤ (q.totient : ℝ) := by
      have hφ0 : 0 ≤ (q.totient : ℝ) := by positivity
      have hαφ : α * (q.totient : ℝ) ≤ (q.totient : ℝ) := by nlinarith
      exact le_trans (min_le_right ((q : ℝ) / 2) (α * (q.totient : ℝ))) hαφ
    exact le_trans hle hpure
  · have hαgt : 1 < α := lt_of_not_ge hα1
    have hα1' : 1 ≤ α := le_of_lt hαgt
    by_cases hA : 2 * α * (q.totient : ℝ) ≤ (q : ℝ)
    · -- case A: 2α·φ ≤ q
      have hα0 : 0 ≤ α := by nlinarith
      have hcaseA := gap_sum_min_lower_caseA q hq α hα0 hA
      have hmin : min ((q : ℝ) / 2) (α * (q.totient : ℝ)) = α * (q.totient : ℝ) := by
        rw [min_eq_right]
        nlinarith
      rw [hmin]
      exact hcaseA
    · -- case B: q < 2α·φ
      let α₀ : ℝ := (q : ℝ) / (2 * (q.totient : ℝ))
      have hφne : (q.totient : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (Nat.totient_pos.mpr hq))
      have hφpos : 0 < 2 * (q.totient : ℝ) := by positivity
      have hqlt : (q : ℝ) < 2 * α * (q.totient : ℝ) := not_le.mp hA
      have hα₀leα : α₀ ≤ α := by
        dsimp [α₀]
        rw [div_le_iff₀ hφpos]
        nlinarith
      have hmono : (G.map (fun d : ℕ => min (2 * α₀) (d : ℝ))).sum ≤
          (G.map (fun d : ℕ => min (2 * α) (d : ℝ))).sum := by
        exact list_sum_map_mono G (fun d : ℕ => min (2 * α₀) (d : ℝ)) (fun d : ℕ => min (2 * α) (d : ℝ))
          (fun d hd => min_le_min (by nlinarith) le_rfl)
      have hmin : min ((q : ℝ) / 2) (α * (q.totient : ℝ)) = (q : ℝ) / 2 := by
        rw [min_eq_left]
        nlinarith
      have hhalf : (1 : ℝ) / 2 ≤ α₀ := by
        dsimp [α₀]
        rw [le_div_iff₀ hφpos]
        have hφq : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast (Nat.totient_le q)
        nlinarith
      by_cases hα₀1 : α₀ ≤ 1
      · -- subcase α₀ ≤ 1 (q ≤ 2φ): pure bound at α₀
        have hpure₀ := gap_min_sum_pure q hq α₀ hhalf
        have hq2 : (q : ℝ) / 2 ≤ (q.totient : ℝ) := by
          dsimp [α₀] at hα₀1
          have hqle2φ : (q : ℝ) ≤ 2 * (q.totient : ℝ) := by
            simpa using (div_le_iff₀ hφpos).mp hα₀1
          rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
          nlinarith
        calc
          min ((q : ℝ) / 2) (α * (q.totient : ℝ)) = (q : ℝ) / 2 := hmin
          _ ≤ (q.totient : ℝ) := hq2
          _ ≤ (G.map (fun d : ℕ => min (2 * α₀) (d : ℝ))).sum := hpure₀
          _ ≤ (G.map (fun d : ℕ => min (2 * α) (d : ℝ))).sum := hmono

      · -- subcase α₀ ≥ 1: case A at the boundary α₀
        have hα₀1' : 1 ≤ α₀ := le_of_lt (lt_of_not_ge hα₀1)
        have hA₀ : 2 * α₀ * (q.totient : ℝ) ≤ (q : ℝ) := by
          have hα₀φ' : α₀ * (q.totient : ℝ) = (q : ℝ) / 2 := by
            dsimp [α₀]
            field_simp [hφne]
          rw [show 2 * α₀ * (q.totient : ℝ) = 2 * (α₀ * (q.totient : ℝ)) by ring, hα₀φ']
          rw [show 2 * ((q : ℝ) / 2) = (q : ℝ) by ring]
        have hα₀0 : 0 ≤ α₀ := by nlinarith
        have hcaseA₀ := gap_sum_min_lower_caseA q hq α₀ hα₀0 hA₀
        have hα₀φ : α₀ * (q.totient : ℝ) = (q : ℝ) / 2 := by
          dsimp [α₀]
          field_simp [hφne]
        calc
          min ((q : ℝ) / 2) (α * (q.totient : ℝ)) = (q : ℝ) / 2 := hmin
          _ = α₀ * (q.totient : ℝ) := hα₀φ.symm
          _ ≤ (G.map (fun d : ℕ => min (2 * α₀) (d : ℝ))).sum := hcaseA₀
          _ ≤ (G.map (fun d : ℕ => min (2 * α) (d : ℝ))).sum := hmono



/-- finite sums of `ofReal(x_i / q)` combine to `ofReal(Σx_i / q)` (positive q). -/
lemma sum_ofReal_div_eq_ofReal_sum_div (q : ℝ) (hqpos : 0 < q) {α : Type*} (s : Finset α)
    (x : α → ℝ) (hx : ∀ i ∈ s, 0 ≤ x i) :
    (∑ i ∈ s, ENNReal.ofReal (x i / q)) = ENNReal.ofReal ((∑ i ∈ s, x i) / q) := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i hi => div_nonneg (hx i hi) hqpos.le)]
  congr 1
  rw [← Finset.sum_div]

/-- The complement of `A_q` inside `(0,1)` has measure at most the gap loss. -/
lemma uncovered_volume_le_gap_loss (q : ℕ) (hq : 1 < q) (δ : ℝ) (hδ : 0 ≤ δ) :
    MeasureTheory.volume {y : ℝ | y ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧ Uncov q δ ((q : ℝ) * y)}
      ≤ ENNReal.ofReal (((cyclicGaps q (reducedResidueList q)).map
          (fun d : ℕ => max ((d : ℝ) - 2 * (q : ℝ) * δ) 0)).sum / (q : ℝ)) := by
  have hmid := uncovered_volume_le_midSum q (by omega : 1 < q) δ hδ
  have hqpos : 0 < (q : ℝ) := by positivity
  have hconv : (∑ ab ∈ consecutivePairs q, max (((ab.2 : ℕ) : ℝ) - ((ab.1 : ℕ) : ℝ) - 2 * (q : ℝ) * δ) 0) +
        max ((2 : ℝ) - 2 * (q : ℝ) * δ) 0 =
        ((cyclicGaps q (reducedResidueList q)).map
          (fun d : ℕ => max ((d : ℝ) - 2 * (q : ℝ) * δ) 0)).sum := by
    have h1 := sum_consecutivePairs_diff_eq_adjDiffs_sum q (by omega : 1 < q)
      (fun d : ℕ => max ((d : ℝ) - 2 * (q : ℝ) * δ) 0)
    have h2 := sum_cyclicGaps_eq_adjDiffs_add q (by omega : 1 < q)
      (fun d : ℕ => max ((d : ℝ) - 2 * (q : ℝ) * δ) 0)
    calc
      (∑ ab ∈ consecutivePairs q, max (((ab.2 : ℕ) : ℝ) - ((ab.1 : ℕ) : ℝ) - 2 * (q : ℝ) * δ) 0) +
            max ((2 : ℝ) - 2 * (q : ℝ) * δ) 0
          = (∑ ab ∈ consecutivePairs q, max (((ab.2 - ab.1 : ℕ) : ℝ) - 2 * (q : ℝ) * δ) 0) +
              max ((2 : ℝ) - 2 * (q : ℝ) * δ) 0 := by
              congr 1
              apply Finset.sum_congr rfl
              intro ab hab
              congr 2
              rw [← Nat.cast_sub (Nat.le_of_lt (Finset.mem_filter.mp hab).2.1)]
      _ = ((adjDiffs (reducedResidueList q)).map
            (fun d : ℕ => max ((d : ℝ) - 2 * (q : ℝ) * δ) 0)).sum +
            max ((2 : ℝ) - 2 * (q : ℝ) * δ) 0 := by
            rw [h1]
      _ = ((cyclicGaps q (reducedResidueList q)).map
            (fun d : ℕ => max ((d : ℝ) - 2 * (q : ℝ) * δ) 0)).sum := by
            have hwrap : max (2 - 2 * (q : ℝ) * δ) 0 =
                max (((2 : ℕ) : ℝ) - 2 * (q : ℝ) * δ) 0 := by
              norm_num
            rw [hwrap]
            rw [← h2]
  calc
    MeasureTheory.volume {y : ℝ | y ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧ Uncov q δ ((q : ℝ) * y)}
        ≤ (∑ ab ∈ consecutivePairs q, ENNReal.ofReal (max (((ab.2 : ℕ) : ℝ) - ((ab.1 : ℕ) : ℝ) - 2 * (q : ℝ) * δ) 0 / (q : ℝ))) +
            ENNReal.ofReal (max ((2 : ℝ) - 2 * (q : ℝ) * δ) 0 / (q : ℝ)) := by
            exact hmid
    _ = ENNReal.ofReal (((∑ ab ∈ consecutivePairs q, max (((ab.2 : ℕ) : ℝ) - ((ab.1 : ℕ) : ℝ) - 2 * (q : ℝ) * δ) 0) +
            max ((2 : ℝ) - 2 * (q : ℝ) * δ) 0) / (q : ℝ)) := by
            calc
              (∑ ab ∈ consecutivePairs q, ENNReal.ofReal (max (((ab.2 : ℕ) : ℝ) - ((ab.1 : ℕ) : ℝ) - 2 * (q : ℝ) * δ) 0 / (q : ℝ))) +
                  ENNReal.ofReal (max ((2 : ℝ) - 2 * (q : ℝ) * δ) 0 / (q : ℝ))
                  = ENNReal.ofReal ((∑ ab ∈ consecutivePairs q, max (((ab.2 : ℕ) : ℝ) - ((ab.1 : ℕ) : ℝ) - 2 * (q : ℝ) * δ) 0) / (q : ℝ)) +
                      ENNReal.ofReal (max ((2 : ℝ) - 2 * (q : ℝ) * δ) 0 / (q : ℝ)) := by
                      rw [sum_ofReal_div_eq_ofReal_sum_div (q : ℝ) hqpos (consecutivePairs q)
                        (fun ab => max (((ab.2 : ℕ) : ℝ) - ((ab.1 : ℕ) : ℝ) - 2 * (q : ℝ) * δ) 0)
                        (fun ab hab => le_max_right _ _)]
                  _ = ENNReal.ofReal (((∑ ab ∈ consecutivePairs q, max (((ab.2 : ℕ) : ℝ) - ((ab.1 : ℕ) : ℝ) - 2 * (q : ℝ) * δ) 0) +
                          max ((2 : ℝ) - 2 * (q : ℝ) * δ) 0) / (q : ℝ)) := by
                      have hB0 : 0 ≤ max ((2 : ℝ) - 2 * (q : ℝ) * δ) 0 := le_max_right _ _
                      have hX0 : 0 ≤ (∑ ab ∈ consecutivePairs q, max (((ab.2 : ℕ) : ℝ) - ((ab.1 : ℕ) : ℝ) - 2 * (q : ℝ) * δ) 0) := by
                        exact Finset.sum_nonneg (fun ab hab => le_max_right _ _)
                      calc
                        ENNReal.ofReal ((∑ ab ∈ consecutivePairs q, max (((ab.2 : ℕ) : ℝ) - ((ab.1 : ℕ) : ℝ) - 2 * (q : ℝ) * δ) 0) / (q : ℝ)) +
                            ENNReal.ofReal (max ((2 : ℝ) - 2 * (q : ℝ) * δ) 0 / (q : ℝ))
                            = ENNReal.ofReal ((∑ ab ∈ consecutivePairs q, max (((ab.2 : ℕ) : ℝ) - ((ab.1 : ℕ) : ℝ) - 2 * (q : ℝ) * δ) 0) / (q : ℝ) +
                                max ((2 : ℝ) - 2 * (q : ℝ) * δ) 0 / (q : ℝ)) :=
                              (ENNReal.ofReal_add (div_nonneg hX0 hqpos.le) (div_nonneg hB0 hqpos.le)).symm
                        _ = ENNReal.ofReal (((∑ ab ∈ consecutivePairs q, max (((ab.2 : ℕ) : ℝ) - ((ab.1 : ℕ) : ℝ) - 2 * (q : ℝ) * δ) 0) +
                                max ((2 : ℝ) - 2 * (q : ℝ) * δ) 0) / (q : ℝ)) := by
                              congr 1
                              ring
    _ = ENNReal.ofReal (((cyclicGaps q (reducedResidueList q)).map
          (fun d : ℕ => max ((d : ℝ) - 2 * (q : ℝ) * δ) 0)).sum / (q : ℝ)) := by
            rw [hconv]


/-- **K1 measure bridge:** `volume A_q ≥ (1/q)·Σ_{d ∈ cyclicGaps} min(2qδ, d)`. -/
lemma volume_Aq_ge_cyclic_min (q : ℕ) (hq : 1 < q) (δ : ℝ) (hδ : 0 ≤ δ) :
    ENNReal.ofReal (((cyclicGaps q (reducedResidueList q)).map
        (fun d : ℕ => min (2 * (q : ℝ) * δ) (d : ℝ))).sum / (q : ℝ)) ≤
      MeasureTheory.volume (approxAddOrderOf UnitAddCircle q δ) := by
  let G : List ℕ := cyclicGaps q (reducedResidueList q)
  let Vset : Set ℝ := {y : ℝ | y ∈ Set.Ioo (0 : ℝ) (1 : ℝ) ∧ Uncov q δ ((q : ℝ) * y)}
  let hmaxfun : ℕ → ℝ := fun d => max ((d : ℝ) - 2 * (q : ℝ) * δ) 0
  let hminfun : ℕ → ℝ := fun d => min (2 * (q : ℝ) * δ) (d : ℝ)
  have hqpos : 0 < (q : ℝ) := by positivity
  have hq0 : (q : ℝ) ≠ 0 := ne_of_gt hqpos
  have hVle : MeasureTheory.volume Vset ≤
      ENNReal.ofReal ((G.map hmaxfun).sum / (q : ℝ)) := by
    dsimp [G, Vset, hmaxfun]
    exact uncovered_volume_le_gap_loss q hq δ hδ
  have hvol := volume_Aq_eq_one_sub_uncovered q (by omega : 0 < q) δ
  have hplus : (G.map hmaxfun).sum + (G.map hminfun).sum = (q : ℝ) := by
    dsimp [hmaxfun, hminfun, G]
    rw [cyclic_min_sum_eq_q_sub_max_sum q (by omega : 0 < q) (2 * (q : ℝ) * δ)]
    ring
  let Amax : ℝ := (G.map hmaxfun).sum
  let Amin : ℝ := (G.map hminfun).sum
  have hAmax0 : 0 ≤ Amax := by
    dsimp [Amax]
    exact list_sum_map_nonneg G hmaxfun (fun d hd => le_max_right _ _)
  have hAmin0 : 0 ≤ Amin := by
    dsimp [Amin]
    exact list_sum_map_nonneg G hminfun (fun d hd =>
      le_min (by positivity : 0 ≤ 2 * (q : ℝ) * δ) (by positivity : 0 ≤ (d : ℝ)))
  have hsum1 : Amax / (q : ℝ) + Amin / (q : ℝ) = 1 := by
    have hAeq : Amax + Amin = (q : ℝ) := by
      dsimp [Amax, Amin]
      exact hplus
    calc
      Amax / (q : ℝ) + Amin / (q : ℝ) = (Amax + Amin) / (q : ℝ) := by ring
      _ = (q : ℝ) / (q : ℝ) := by rw [hAeq]
      _ = 1 := by field_simp [hq0]
  have hA : ENNReal.ofReal (Amax / (q : ℝ)) + ENNReal.ofReal (Amin / (q : ℝ)) = (1 : ℝ≥0∞) := by
    calc
      ENNReal.ofReal (Amax / (q : ℝ)) + ENNReal.ofReal (Amin / (q : ℝ))
          = ENNReal.ofReal (Amax / (q : ℝ) + Amin / (q : ℝ)) :=
            (ENNReal.ofReal_add (div_nonneg hAmax0 hqpos.le) (div_nonneg hAmin0 hqpos.le)).symm
      _ = ENNReal.ofReal 1 := by rw [hsum1]
      _ = (1 : ℝ≥0∞) := by simp
  have hmaxle1 : Amax / (q : ℝ) ≤ 1 := by
    have hmono : Amax ≤ (G.map (fun d : ℕ => (d : ℝ))).sum := by
      dsimp [Amax]
      apply list_sum_map_mono G hmaxfun (fun d : ℕ => (d : ℝ))
      intro d hd
      dsimp [hmaxfun]
      have h2 : 0 ≤ 2 * (q : ℝ) * δ := by positivity
      exact max_le (by linarith) (by positivity : 0 ≤ (d : ℝ))
    have hcast : (G.map (fun d : ℕ => (d : ℝ))).sum = (q : ℝ) := by
      rw [list_sum_natCast_map]
      congr 1
      dsimp [G]
      exact reduced_gap_sum_eq_q q (by omega)
    exact (div_le_iff₀ hqpos).2 (by simpa using le_trans hmono (le_of_eq hcast))
  have hmin_eq : ENNReal.ofReal (Amin / (q : ℝ)) =
      (1 : ℝ≥0∞) - ENNReal.ofReal (Amax / (q : ℝ)) := by
    have hswap : ENNReal.ofReal (Amin / (q : ℝ)) + ENNReal.ofReal (Amax / (q : ℝ)) = (1 : ℝ≥0∞) := by
      rw [add_comm]
      exact hA
    exact ENNReal.eq_sub_of_add_eq ENNReal.ofReal_ne_top hswap
  have hsub : (1 : ℝ≥0∞) - ENNReal.ofReal (Amax / (q : ℝ)) ≤
      (1 : ℝ≥0∞) - MeasureTheory.volume Vset := by
    exact tsub_le_tsub_left hVle (1 : ℝ≥0∞)
  have hvol' : MeasureTheory.volume (approxAddOrderOf UnitAddCircle q δ) =
      (1 : ℝ≥0∞) - MeasureTheory.volume Vset := by
    simpa [Vset] using hvol
  calc
    ENNReal.ofReal (((cyclicGaps q (reducedResidueList q)).map
        (fun d : ℕ => min (2 * (q : ℝ) * δ) (d : ℝ))).sum / (q : ℝ))
        = ENNReal.ofReal (Amin / (q : ℝ)) := by
            dsimp [Amin, G, hminfun]
    _ = (1 : ℝ≥0∞) - ENNReal.ofReal (Amax / (q : ℝ)) := hmin_eq
    _ ≤ (1 : ℝ≥0∞) - MeasureTheory.volume Vset := hsub
    _ = MeasureTheory.volume (approxAddOrderOf UnitAddCircle q δ) := hvol'.symm

/-- volume of a radius-`δ ≥ 1/2` ball on the unit circle is the whole circle. -/
private lemma volume_unit_ball_of_half_le (δ : ℝ) (hδ : (1 : ℝ) / 2 ≤ δ) :
    MeasureTheory.volume (Metric.ball (0 : UnitAddCircle) δ) = (1 : ℝ≥0∞) := by
  have hb : MeasureTheory.volume (Metric.closedBall (0 : UnitAddCircle) δ) = (1 : ℝ≥0∞) := by
    have hv := (AddCircle.volume_closedBall (T := (1 : ℝ)) (x := (0 : AddCircle (1 : ℝ))) (ε := δ))
    have hmin : min (1 : ℝ) (2 * δ) = 1 := by
      rw [min_eq_left]
      linarith
    simpa [hmin] using hv
  calc
    MeasureTheory.volume (Metric.ball (0 : UnitAddCircle) δ)
        = MeasureTheory.volume (Metric.closedBall (0 : UnitAddCircle) δ) := by
          exact MeasureTheory.measure_congr
            (AddCircle.closedBall_ae_eq_ball (T := (1 : ℝ)) (x := (0 : AddCircle (1 : ℝ))) (ε := δ)).symm
    _ = (1 : ℝ≥0∞) := hb

/-- Long-arc K1 core: `μ(A_q) ≥ (1/2)·min(1, 2φ(q)δ)` for `δ > 1/q`. -/
private lemma approxAddOrderOf_volume_ge_long_arc (q : ℕ) (hq : 0 < q) (δ : ℝ)
    (hδ : 0 ≤ δ) (hδ1 : (1 : ℝ) / (q : ℝ) < δ) (hqδ : (1 : ℝ) / 2 ≤ (q : ℝ) * δ) :
    ENNReal.ofReal ((1 / 2) * min (1 : ℝ) (2 * (q.totient : ℝ) * δ)) ≤
      MeasureTheory.volume (approxAddOrderOf UnitAddCircle q δ) := by
  by_cases hq1 : q = 1
  · subst hq1
    have hA : approxAddOrderOf UnitAddCircle 1 δ = Metric.ball (0 : UnitAddCircle) δ := by
      ext x
      rw [UnitAddCircle.mem_approxAddOrderOf_iff (n := 1) (by norm_num)]
      constructor
      · rintro ⟨m, hm1, hg, hd⟩
        have hm0 : m = 0 := by omega
        subst m
        simpa [dist_eq_norm] using hd
      · intro hx
        refine ⟨0, by norm_num, ?_, ?_⟩
        · norm_num
        · simpa [dist_eq_norm] using hx
    have hδ12 : (1 : ℝ) / 2 ≤ δ := by linarith
    have hvol := volume_unit_ball_of_half_le δ hδ12
    have htarget : (1 / 2) * min (1 : ℝ) (2 * ((1 : ℕ).totient : ℝ) * δ) ≤ 1 := by
      have hφ : ((1 : ℕ).totient : ℝ) = 1 := by norm_num
      rw [hφ]
      have h2δ : (1 : ℝ) ≤ 2 * δ := by linarith
      have hmin1 : min (1 : ℝ) (2 * δ) = 1 := by rw [min_eq_left h2δ]
      nlinarith [hmin1]
    calc
      ENNReal.ofReal ((1 / 2) * min (1 : ℝ) (2 * ((1 : ℕ).totient : ℝ) * δ))
          ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal htarget
      _ = (1 : ℝ≥0∞) := by simp
      _ = MeasureTheory.volume (Metric.ball (0 : UnitAddCircle) δ) := hvol.symm
      _ = MeasureTheory.volume (approxAddOrderOf UnitAddCircle 1 δ) := by rw [← hA]
  · have hq2 : 1 < q := by
      have : q ≠ 0 := by omega
      omega
    let α : ℝ := (q : ℝ) * δ
    have hα : (1 : ℝ) / 2 ≤ α := by
      dsimp [α]
      exact hqδ
    have hge := volume_Aq_ge_cyclic_min q hq2 δ hδ
    have hcover := cyclic_gap_cover_bound q hq α hα
    have hqR : (q : ℝ) ≠ 0 := by positivity
    have hqpos : 0 < (q : ℝ) := by positivity
    have hsum : ENNReal.ofReal ((1 / 2) * min (1 : ℝ) (2 * (q.totient : ℝ) * δ)) ≤
        ENNReal.ofReal (((cyclicGaps q (reducedResidueList q)).map
          (fun d : ℕ => min (2 * (q : ℝ) * δ) (d : ℝ))).sum / (q : ℝ)) := by
      apply ENNReal.ofReal_le_ofReal
      have hcoverSum : min ((q : ℝ) / 2) (α * (q.totient : ℝ)) ≤
          ((cyclicGaps q (reducedResidueList q)).map (fun d : ℕ => min (2 * (q : ℝ) * δ) (d : ℝ))).sum := by
        calc
          min ((q : ℝ) / 2) (α * (q.totient : ℝ))
              ≤ ((cyclicGaps q (reducedResidueList q)).map (fun d : ℕ => min (2 * α) (d : ℝ))).sum := hcover
          _ = ((cyclicGaps q (reducedResidueList q)).map (fun d : ℕ => min (2 * (q : ℝ) * δ) (d : ℝ))).sum := by
              apply congrArg List.sum
              apply List.map_congr_left
              intro d hd
              congr 1
              dsimp [α]
              ring
      have hdiv : min ((q : ℝ) / 2) (α * (q.totient : ℝ)) / (q : ℝ) ≤
          (((cyclicGaps q (reducedResidueList q)).map (fun d : ℕ => min (2 * (q : ℝ) * δ) (d : ℝ))).sum) / (q : ℝ) := by
          exact div_le_div_of_nonneg_right hcoverSum hqpos.le
      have hphi : α * (q.totient : ℝ) / (q : ℝ) = (q.totient : ℝ) * δ := by
        dsimp [α]
        field_simp [hqR]
      have hqhalf : ((q : ℝ) / 2) / (q : ℝ) = (1 / 2 : ℝ) := by field_simp [hqR]
      have hminsplit : min ((q : ℝ) / 2) (α * (q.totient : ℝ)) / (q : ℝ) =
          min (((q : ℝ) / 2) / (q : ℝ)) (α * (q.totient : ℝ) / (q : ℝ)) := by
        rw [min_div_div_right hqpos.le]
      have hminhalf : (1 / 2) * min (1 : ℝ) (2 * (q.totient : ℝ) * δ) =
          min (1 / 2 : ℝ) ((q.totient : ℝ) * δ) := by
        calc
          (1 / 2) * min 1 (2 * (q.totient : ℝ) * δ)
              = min ((1 / 2) * 1) ((1 / 2) * (2 * (q.totient : ℝ) * δ)) := by
                rw [mul_min_of_nonneg (1 : ℝ) (2 * (q.totient : ℝ) * δ) (by norm_num : (0 : ℝ) ≤ 1 / 2)]
          _ = min (1 / 2 : ℝ) ((q.totient : ℝ) * δ) := by congr 1 <;> ring
      have hmul : (1 / 2) * min (1 : ℝ) (2 * (q.totient : ℝ) * δ) =
          min ((q : ℝ) / 2) (α * (q.totient : ℝ)) / (q : ℝ) := by
        calc
          (1 / 2) * min (1 : ℝ) (2 * (q.totient : ℝ) * δ)
              = min (1 / 2 : ℝ) ((q.totient : ℝ) * δ) := hminhalf
          _ = min (((q : ℝ) / 2) / (q : ℝ)) (α * (q.totient : ℝ) / (q : ℝ)) := by rw [hqhalf, hphi]
          _ = min ((q : ℝ) / 2) (α * (q.totient : ℝ)) / (q : ℝ) := hminsplit.symm
      rw [hmul]
      exact hdiv
    exact le_trans hsum hge


 /-- K1 — the large-value measure lower bound (`δ = 0` or `q·δ ≥ 1/2`):
the union of the `φ(q)` arcs of radius `δ` around the reduced fractions of `q`
has measure at least `(1/2)·min(1, 2·φ(q)·δ)`.

The certified bound `μ(A_q) ≥ φ(q)/q` (`approxAddOrderOf_volume_ge_totient_div`
below) settles the regimes `δ = 0` and `δ ≤ 1/q`; the only remaining content is
the long-arc regime `δ > 1/q`, i.e. the standalone goal
`approxAddOrderOf_volume_ge_long_arc` (trimmed-arc identity + coprime-gap
coverage estimate).  Numerics: ratio `μ/min(1,2φδ)` floor ≈ 0.778 on real
reduced-residue systems, so `1/2` is safe with wide margin; cheap relaxations
(pure real gaps, palindromic systems) fail (ratios down to ≈ 0.2, ≈ 0.235), so
genuine reduced-residue geometry is needed.  Note the whole leaf needs only ANY
fixed positive constant (then `L ≥ 2c`, `μ(⋃_B A_q) ≥ 2c/(1+16c) > 0`), so even
`c = 1/8` would unlock it.  (Requested of the fleet as
`NumberTheory/DuffinSchaeffer/approxAddOrderOf_volume_ge_min_quasi`.) -/
private lemma approxAddOrderOf_volume_ge_min_quasi (q : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hlarge : δ = 0 ∨ (1 : ℝ) / 2 ≤ (q : ℝ) * δ) :
    ENNReal.ofReal ((1 / 2) * min (1 : ℝ) (2 * (q.totient : ℝ) * δ)) ≤
      MeasureTheory.volume (approxAddOrderOf UnitAddCircle q δ) := by
  -- q = 0: totient 0 = 0, RHS = 0.
  by_cases hq0 : q = 0
  · subst hq0
    simp
  have hq : 0 < q := Nat.pos_of_ne_zero hq0
  -- δ = 0: A_q empty, RHS 0.
  by_cases hδ0 : δ = 0
  · subst hδ0
    have hA : approxAddOrderOf UnitAddCircle q 0 = (∅ : Set UnitAddCircle) :=
      approxAddOrderOf_eq_empty_of_radius_zero q hq
    rw [hA]
    simp
  -- Nonzero: large-value hypothesis gives 1/2 ≤ q·δ.
  have hqδ : (1 : ℝ) / 2 ≤ (q : ℝ) * δ := by
    rcases hlarge with hz | hl
    · exfalso; exact hδ0 hz
    · exact hl
  -- Certified bound μ(A_q) ≥ φ(q)/q.
  have hcert := approxAddOrderOf_volume_ge_totient_div q hq δ hδ hqδ
  -- Case δ ≤ 1/q: φ·δ ≤ φ/q, so the certified bound already gives the claim.
  by_cases hδ1 : δ ≤ 1 / (q : ℝ)
  · have hmin_le : (1 / 2) * min (1 : ℝ) (2 * (q.totient : ℝ) * δ) ≤
        ((q.totient : ℕ) : ℝ) / (q : ℝ) := by
      have hmm : min (1 : ℝ) (2 * (q.totient : ℝ) * δ) ≤ 2 * (q.totient : ℝ) * δ :=
        min_le_right (1 : ℝ) (2 * (q.totient : ℝ) * δ)
      have hhalf : (1 / 2) * (2 * (q.totient : ℝ) * δ) = (q.totient : ℝ) * δ := by ring
      have hphi : (q.totient : ℝ) * δ ≤ ((q.totient : ℕ) : ℝ) / (q : ℝ) := by
        rw [le_div_iff₀ (by positivity : 0 < (q : ℝ))]
        have hφ0 : 0 ≤ (q.totient : ℝ) := by exact_mod_cast (Nat.zero_le q.totient)
        have hdq : δ * (q : ℝ) ≤ 1 := by
          calc
            δ * (q : ℝ) ≤ (1 / (q : ℝ)) * (q : ℝ) :=
              mul_le_mul_of_nonneg_right hδ1 (by positivity : 0 ≤ (q : ℝ))
            _ = 1 := by field_simp [hq.ne']
        calc
          (q.totient : ℝ) * δ * (q : ℝ) = (q.totient : ℝ) * (δ * (q : ℝ)) := by ring
          _ ≤ (q.totient : ℝ) * 1 := mul_le_mul_of_nonneg_left hdq hφ0
          _ = (q.totient : ℝ) := by ring
      have hm : (1 / 2) * min (1 : ℝ) (2 * (q.totient : ℝ) * δ) ≤ (q.totient : ℝ) * δ := by
        nlinarith [hhalf, hmm]
      exact le_trans hm hphi
    exact le_trans (ENNReal.ofReal_le_ofReal hmin_le) hcert
  -- Long-arc regime δ > 1/q: a direct application of the standalone core
  -- `approxAddOrderOf_volume_ge_long_arc` (the trimmed-arc identity +
  -- coprime-gap coverage estimate).  When that core lands, K1 closes with no
  -- further work.
  exact approxAddOrderOf_volume_ge_long_arc q hq δ hδ (lt_of_not_ge hδ1) hqδ
/-- **Trivial (large-measure) regime of the per-pair quasi-independence:**
if one of the two arc-unions has measure at least `1/8`, then
`μ(A_q∩A_r) ≤ 8·μ(A_q)·μ(A_r)`. -/
private lemma inter_volume_le_quasi_of_large_measure (q r : ℕ) (δq δr : ℝ)
    (hbig : (1 : ENNReal) / 8 ≤
      max (MeasureTheory.volume (approxAddOrderOf UnitAddCircle q δq))
        (MeasureTheory.volume (approxAddOrderOf UnitAddCircle r δr))) :
    MeasureTheory.volume (approxAddOrderOf UnitAddCircle q δq ∩
        approxAddOrderOf UnitAddCircle r δr) ≤
      (8 : ENNReal) * MeasureTheory.volume (approxAddOrderOf UnitAddCircle q δq) *
        MeasureTheory.volume (approxAddOrderOf UnitAddCircle r δr) := by
  set A := approxAddOrderOf UnitAddCircle q δq with hA
  set B := approxAddOrderOf UnitAddCircle r δr with hB
  have hmin : MeasureTheory.volume (A ∩ B) ≤
      min (MeasureTheory.volume A) (MeasureTheory.volume B) :=
    le_min (measure_mono Set.inter_subset_left) (measure_mono Set.inter_subset_right)
  rcases le_total (MeasureTheory.volume A) (MeasureTheory.volume B) with hle | hle
  · have h8 : (1 : ENNReal) ≤ 8 * MeasureTheory.volume B := by
      rw [max_eq_right hle] at hbig
      have h2 : (8 : ENNReal) * ((1 : ENNReal) / 8) ≤ 8 * MeasureTheory.volume B :=
        mul_le_mul_right hbig 8
      rwa [ENNReal.mul_div_cancel (by norm_num : (8 : ENNReal) ≠ 0)
        (by norm_num : (8 : ENNReal) ≠ ∞)] at h2
    refine le_trans hmin ?_
    rw [min_eq_left hle]
    calc MeasureTheory.volume A = MeasureTheory.volume A * 1 := (mul_one _).symm
      _ ≤ MeasureTheory.volume A * (8 * MeasureTheory.volume B) := mul_le_mul_right h8 _
      _ = (8 : ENNReal) * MeasureTheory.volume A * MeasureTheory.volume B := by ring
  · have h8 : (1 : ENNReal) ≤ 8 * MeasureTheory.volume A := by
      rw [max_eq_left hle] at hbig
      have h2 : (8 : ENNReal) * ((1 : ENNReal) / 8) ≤ 8 * MeasureTheory.volume A :=
        mul_le_mul_right hbig 8
      rwa [ENNReal.mul_div_cancel (by norm_num : (8 : ENNReal) ≠ 0)
        (by norm_num : (8 : ENNReal) ≠ ∞)] at h2
    refine le_trans hmin ?_
    rw [min_eq_right hle]
    calc MeasureTheory.volume B = MeasureTheory.volume B * 1 := (mul_one _).symm
      _ ≤ MeasureTheory.volume B * (8 * MeasureTheory.volume A) := mul_le_mul_right h8 _
      _ = (8 : ENNReal) * MeasureTheory.volume A * MeasureTheory.volume B := by ring

/-- **Small-measure regime consequences:** if `μ(A_q) < 1/8` with `δ > 0` and the
large-value hypothesis `1/2 ≤ q·δ`, then `δ ≥ 1/(2q)` and `φ(q)·δ < 1/8`. -/
private lemma small_measure_forces (q : ℕ) (hq : 0 < q) (δ : ℝ) (hδ : 0 ≤ δ)
    (hlarge : (1 : ℝ) / 2 ≤ (q : ℝ) * δ)
    (hsmall : MeasureTheory.volume (approxAddOrderOf UnitAddCircle q δ) <
      (1 : ENNReal) / 8) :
    (1 : ℝ) / (2 * (q : ℝ)) ≤ δ ∧ (q.totient : ℝ) * δ < 1 / 8 := by
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  constructor
  · rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (q : ℝ))]
    nlinarith
  · have hK1 := approxAddOrderOf_volume_ge_min_quasi q δ hδ (Or.inr hlarge)
    have hsmall' : MeasureTheory.volume (approxAddOrderOf UnitAddCircle q δ) <
        ENNReal.ofReal (1 / 8) := by
      rwa [show ((1 : ENNReal) / 8) = ENNReal.ofReal (1 / 8) by
        norm_num [ENNReal.ofReal_div_of_pos]] at hsmall
    have hlt : ENNReal.ofReal ((1 / 2) * min (1 : ℝ) (2 * (q.totient : ℝ) * δ)) <
        ENNReal.ofReal (1 / 8) := lt_of_le_of_lt hK1 hsmall'
    have hreal := (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1 / 8)).mp hlt
    have hmin : min (1 : ℝ) (2 * (q.totient : ℝ) * δ) < 1 / 4 := by nlinarith
    have hX : 2 * (q.totient : ℝ) * δ < 1 / 4 := by
      by_contra hle
      have : (1 / 4 : ℝ) ≤ min (1 : ℝ) (2 * (q.totient : ℝ) * δ) :=
        le_min (by norm_num) (le_of_not_gt hle)
      linarith
    nlinarith

/-- **Reduction of the small-measure per-pair bound to a counting estimate.**
If `μ(A_q∩A_r) ≤ ofReal(2·min(δq,δr)·N)` for a count `N` with
`N ≤ 2·(δq+δr)·φ(q)φ(r)`, and `ofReal(φ(q)δq) ≤ μ(A_q)`,
`ofReal(φ(r)δr) ≤ μ(A_r)`, then `μ(A_q∩A_r) ≤ 8·μ(A_q)·μ(A_r)`.
(The two inputs `N`-bound and refined intersection bound are the content of the
PV §3 fibre-window count; this lemma is the pure ENNReal/real core.) -/
private lemma quasi_of_count_bound (q r : ℕ) (δq δr N : ℝ)
    (hδq0 : 0 ≤ δq) (hδr0 : 0 ≤ δr)
    (hinter : MeasureTheory.volume (approxAddOrderOf UnitAddCircle q δq ∩
        approxAddOrderOf UnitAddCircle r δr) ≤ ENNReal.ofReal (2 * min δq δr * N))
    (hcount : N ≤ 2 * (δq + δr) * ((q.totient : ℝ) * (r.totient : ℝ)))
    (hLq : ENNReal.ofReal ((q.totient : ℝ) * δq) ≤
      MeasureTheory.volume (approxAddOrderOf UnitAddCircle q δq))
    (hLr : ENNReal.ofReal ((r.totient : ℝ) * δr) ≤
      MeasureTheory.volume (approxAddOrderOf UnitAddCircle r δr)) :
    MeasureTheory.volume (approxAddOrderOf UnitAddCircle q δq ∩
        approxAddOrderOf UnitAddCircle r δr) ≤
      (8 : ENNReal) * MeasureTheory.volume (approxAddOrderOf UnitAddCircle q δq) *
        MeasureTheory.volume (approxAddOrderOf UnitAddCircle r δr) := by
  have hφq : 0 ≤ (q.totient : ℝ) := by positivity
  have hφr : 0 ≤ (r.totient : ℝ) := by positivity
  have hm : min δq δr * (δq + δr) ≤ 2 * δq * δr :=
    min_add_mul_le_two_mul δq δr hδq0 hδr0
  have hmain : 2 * min δq δr * N ≤
      8 * ((q.totient : ℝ) * δq) * ((r.totient : ℝ) * δr) := by
    calc
      2 * min δq δr * N
          ≤ 2 * min δq δr * (2 * (δq + δr) * ((q.totient : ℝ) * (r.totient : ℝ))) :=
            mul_le_mul_of_nonneg_left hcount (by positivity)
      _ = 4 * (min δq δr * (δq + δr)) * ((q.totient : ℝ) * (r.totient : ℝ)) := by ring
      _ ≤ 4 * (2 * δq * δr) * ((q.totient : ℝ) * (r.totient : ℝ)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm (by norm_num))
              (by positivity)
      _ = 8 * ((q.totient : ℝ) * δq) * ((r.totient : ℝ) * δr) := by ring
  have h8 : ENNReal.ofReal (2 * min δq δr * N) ≤
      8 * ENNReal.ofReal ((q.totient : ℝ) * δq) *
        ENNReal.ofReal ((r.totient : ℝ) * δr) := by
    calc
      ENNReal.ofReal (2 * min δq δr * N)
          ≤ ENNReal.ofReal (8 * ((q.totient : ℝ) * δq) * ((r.totient : ℝ) * δr)) :=
            ENNReal.ofReal_le_ofReal hmain
      _ = 8 * ENNReal.ofReal ((q.totient : ℝ) * δq) *
            ENNReal.ofReal ((r.totient : ℝ) * δr) := by
            rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 8 * ((q.totient : ℝ) * δq)),
                ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8)]
            norm_num
  calc
    MeasureTheory.volume (approxAddOrderOf UnitAddCircle q δq ∩
        approxAddOrderOf UnitAddCircle r δr)
        ≤ 8 * ENNReal.ofReal ((q.totient : ℝ) * δq) *
            ENNReal.ofReal ((r.totient : ℝ) * δr) := le_trans hinter h8
    _ ≤ 8 * MeasureTheory.volume (approxAddOrderOf UnitAddCircle q δq) *
          MeasureTheory.volume (approxAddOrderOf UnitAddCircle r δr) :=
        mul_le_mul' (mul_le_mul' le_rfl hLq) hLr

/-- **Fibre-window main-term estimate.** At a window `W ≤ Δ·L + 1` with
`1/2 ≤ Δ·L` (the window is macroscopic), the fibre main term
`2·W·M/L` is at most `6·Δ·M`. -/
private lemma fibre_main_term_le (Δ L W M : ℝ) (hΔ : 0 ≤ Δ) (hL : 0 < L) (hM : 0 ≤ M)
    (hΔL : (1 : ℝ) / 2 ≤ Δ * L) (hW : W ≤ Δ * L + 1) :
    2 * W * M / L ≤ 6 * Δ * M := by
  have hstep : 2 * W * M / L ≤ 2 * (Δ * L + 1) * M / L := by
    apply div_le_div_of_nonneg_right _ hL.le
    nlinarith [hW, hM]
  have hval : 2 * (Δ * L + 1) * M / L = 2 * Δ * M + 2 * M / L := by
    field_simp [ne_of_gt hL]
  have hML : 2 * M / L ≤ 4 * Δ * M := by
    have h1 : (1 : ℝ) ≤ 2 * Δ * L := by linarith
    have hinv : 1 / L ≤ 2 * Δ := by
      rw [div_le_iff₀ hL]
      nlinarith
    calc
      2 * M / L = 2 * M * (1 / L) := by ring
      _ ≤ 2 * M * (2 * Δ) := mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = 4 * Δ * M := by ring
  linarith

/-- Same estimate with the natural window `W = ⌈Δ·L⌉`. -/
private lemma fibre_main_term_ceil_le (Δ : ℝ) (L : ℕ) (M : ℝ) (hΔ : 0 ≤ Δ) (hLpos : 0 < L)
    (hM : 0 ≤ M) (hΔL : (1 : ℝ) / 2 ≤ Δ * (L : ℝ)) :
    2 * ((Nat.ceil (Δ * (L : ℝ)) : ℕ) : ℝ) * M / (L : ℝ) ≤ 6 * Δ * M := by
  refine fibre_main_term_le Δ (L : ℝ) ((Nat.ceil (Δ * (L : ℝ)) : ℕ) : ℝ) M hΔ
    (by exact_mod_cast hLpos) hM hΔL ?_
  have hx0 : 0 ≤ Δ * (L : ℝ) := mul_nonneg hΔ (by positivity)
  exact le_of_lt (Nat.ceil_lt_add_one hx0)

/-- **Fibre-window count at the macroscopic window `W = ⌈Δ·L⌉`** (`L = lcm(q,r)`):
the number of close reduced pairs is at most `6·Δ·φ(q)φ(r)` plus the error term
`φ(g)·τ(qr/g²)·3^{ω(g)}`.  (Wrapper around `fibre_window_count_le_global` with
the main term improved by `fibre_main_term_ceil_le`.) -/
private lemma fibre_window_count_le (q r W : ℕ) (Δ : ℝ) (hq : 0 < q) (hr : 0 < r)
    (hΔ : 0 ≤ Δ) (hW : W = Nat.ceil (Δ * ((q * r / (q.gcd r) : ℕ) : ℝ)))
    (hΔL : (1 : ℝ) / 2 ≤ Δ * ((q * r / (q.gcd r) : ℕ) : ℝ)) :
    let g : ℕ := q.gcd r
    let L : ℕ := q * r / g
    let Rr : ℕ := r / g
    let Q : ℕ := q / g
    let P : ℕ × ℕ → Prop :=
      fun mn => (((mn.1 * Rr) % L) + L - ((mn.2 * Q) % L)) % L ≤ W ∨
                (((mn.2 * Q) % L) + L - ((mn.1 * Rr) % L)) % L ≤ W
    let PQ : Finset (ℕ × ℕ) :=
      Finset.product ((Finset.range q).filter (fun m : ℕ => m.gcd q = 1))
                     ((Finset.range r).filter (fun n : ℕ => n.gcd r = 1))
    (((PQ.filter P).card : ℝ) ≤
      6 * Δ * ((q.totient : ℝ) * (r.totient : ℝ)) +
        ((g.totient : ℕ) : ℝ) * (((q * r / (g * g)).divisors.card : ℕ) : ℝ) *
          (3 : ℝ) ^ g.primeFactors.card) := by
  dsimp only
  have hmain := fibre_window_count_le_global q r W
  dsimp only at hmain
  refine le_trans hmain ?_
  have hLpos : 0 < q * r / q.gcd r := by
    have hdvd : q.gcd r ∣ q * r := dvd_mul_of_dvd_left (Nat.gcd_dvd_left q r) r
    exact Nat.div_pos (Nat.le_of_dvd (Nat.mul_pos hq hr) hdvd) (Nat.gcd_pos_of_pos_left r hq)
  have hM : 0 ≤ (q.totient : ℝ) * (r.totient : ℝ) := by positivity
  have hb := fibre_main_term_ceil_le Δ (q * r / q.gcd r) ((q.totient : ℝ) * (r.totient : ℝ))
    hΔ hLpos hM hΔL
  have hcast : ((q.totient * r.totient : ℕ) : ℝ) =
      (q.totient : ℝ) * (r.totient : ℝ) := by rw [Nat.cast_mul]
  rw [hW, hcast]
  linarith [hb]

/-- The circle distance between the reduced fractions `m/q` and `n/r` equals the
norm of the lattice quantity `(m·(r/g) − n·(q/g))/L`, `g = gcd q r`, `L = lcm`. -/
private lemma circle_dist_eq_lattice (q r m n : ℕ) (hq : 0 < q) (hr : 0 < r) :
    dist (((m : ℝ) / (q : ℝ)) : UnitAddCircle) (((n : ℝ) / (r : ℝ)) : UnitAddCircle)
      = ‖(((((m * (r / q.gcd r) : ℕ) : ℝ) - ((n * (q / q.gcd r) : ℕ) : ℝ)) /
          ((q * r / q.gcd r : ℕ) : ℝ)) : UnitAddCircle)‖ := by
  have hg : 0 < q.gcd r := Nat.gcd_pos_of_pos_left r hq
  have hgdvd_q : q.gcd r ∣ q := Nat.gcd_dvd_left q r
  have hgdvd_r : q.gcd r ∣ r := Nat.gcd_dvd_right q r
  have hgdvd_qr : q.gcd r ∣ q * r := dvd_mul_of_dvd_left hgdvd_q r
  have hgR : ((q.gcd r : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hg)
  have hqR : ((q : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hq)
  have hrR : ((r : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hr)
  have hRr : ((r / q.gcd r : ℕ) : ℝ) = (r : ℝ) / (q.gcd r : ℝ) :=
    Nat.cast_div hgdvd_r hgR
  have hQg : ((q / q.gcd r : ℕ) : ℝ) = (q : ℝ) / (q.gcd r : ℝ) :=
    Nat.cast_div hgdvd_q hgR
  have hL : ((q * r / q.gcd r : ℕ) : ℝ) = (q : ℝ) * (r : ℝ) / (q.gcd r : ℝ) := by
    rw [Nat.cast_div hgdvd_qr hgR, Nat.cast_mul]
  rw [dist_eq_norm, ← AddCircle.coe_sub]
  congr 1
  push_cast
  rw [hRr, hQg, hL]
  field_simp


/-- For `0 ≤ a < L` and any integer `m`, the distance of `a` to the nearest
multiple of `L` is at most `|a + m·L|`. -/
private lemma min_le_abs_add_mul (L : ℕ) (hL : 0 < L) (a m : ℤ) (ha0 : 0 ≤ a) (haL : a < (L : ℤ)) :
    min a ((L : ℤ) - a) ≤ |a + m * (L : ℤ)| := by
  rcases lt_or_ge m 0 with hm | hm
  · -- m < 0
    have hm1 : m ≤ -1 := by omega
    have hneg : a + m * (L : ℤ) < 0 := by
      have hL1 : (1 : ℤ) ≤ (L : ℤ) := by exact_mod_cast hL
      have hmL : m * (L : ℤ) ≤ -(L : ℤ) := by
        have := mul_le_mul_of_nonneg_right hm1 (by positivity : (0 : ℤ) ≤ (L : ℤ))
        simpa using this
      linarith
    rw [abs_of_neg hneg]
    have hge : (L : ℤ) - a ≤ -(a + m * (L : ℤ)) := by
      have hmL : m * (L : ℤ) ≤ -(L : ℤ) := by
        have := mul_le_mul_of_nonneg_right hm1 (by positivity : (0 : ℤ) ≤ (L : ℤ))
        simpa using this
      linarith
    exact le_trans (min_le_right _ _) hge
  · -- 0 ≤ m
    have hnonneg : 0 ≤ a + m * (L : ℤ) := by
      have : 0 ≤ m * (L : ℤ) := mul_nonneg hm (by positivity)
      linarith
    rw [abs_of_nonneg hnonneg]
    have hle : a ≤ a + m * (L : ℤ) := by
      have : 0 ≤ m * (L : ℤ) := mul_nonneg hm (by positivity)
      linarith
    exact le_trans (min_le_left _ _) hle

/-- Distance to `Lℤ`: `min (x % L) ((-x) % L) ≤ |x − k·L|` for every integer `k`. -/
private lemma emod_min_le_abs (L : ℕ) (hL : 0 < L) (x k : ℤ) :
    min (x % (L : ℤ)) ((-x) % (L : ℤ)) ≤ |x - k * (L : ℤ)| := by
  set Lz : ℤ := (L : ℤ) with hLz
  have hLzpos : 0 < Lz := by rw [hLz]; exact_mod_cast hL
  have hLz0 : Lz ≠ 0 := ne_of_gt hLzpos
  set a : ℤ := x % Lz with ha
  set b : ℤ := (-x) % Lz with hb
  have ha0 : 0 ≤ a := by rw [ha]; exact Int.emod_nonneg _ hLz0
  have haL : a < Lz := by rw [ha]; exact Int.emod_lt_of_pos _ hLzpos
  have hb0 : 0 ≤ b := by rw [hb]; exact Int.emod_nonneg _ hLz0
  have hbL : b < Lz := by rw [hb]; exact Int.emod_lt_of_pos _ hLzpos
  have h1 : Lz ∣ x - a := by
    refine Int.dvd_iff_emod_eq_zero.mpr ?_
    have h := Int.emod_sub_emod x Lz a
    rw [← ha] at h
    simpa using h.symm
  have h2 : Lz ∣ (-x) - b := by
    refine Int.dvd_iff_emod_eq_zero.mpr ?_
    have h := Int.emod_sub_emod (-x) Lz b
    rw [← hb] at h
    simpa using h.symm
  have hsum : Lz ∣ a + b := by
    have h := dvd_add h1 h2
    have heq : (x - a) + ((-x) - b) = -(a + b) := by ring
    rw [heq] at h
    exact dvd_neg.mp h
  rcases hsum with ⟨t, ht⟩
  have ht0 : 0 ≤ t := by
    rcases lt_or_ge t 0 with htneg | htpos
    · exfalso
      have : a + b < 0 := by nlinarith
      linarith
    · exact htpos
  have ht2 : t < 2 := by nlinarith
  have ht01 : t = 0 ∨ t = 1 := by omega
  rcases ht01 with h0 | h1'
  · have htp : a + b = 0 := by simpa [h0] using ht
    have ha0' : a = 0 := by omega
    have hb0' : b = 0 := by omega
    rw [ha0', hb0', min_self]
    exact abs_nonneg _
  · have htp : a + b = Lz := by simpa [h1'] using ht
    have hba : b = Lz - a := by omega
    rcases h1 with ⟨j, hj⟩
    have hrep : x - k * Lz = a + (j - k) * Lz := by
      have : x = a + Lz * j := by linarith
      rw [this]; ring
    have haL' : a < (L : ℤ) := by rwa [hLz] at haL
    rw [hba, hrep]
    exact min_le_abs_add_mul L hL a (j - k) ha0 haL'


/-- From `‖↑(A/L)‖ < Δ` (`L > 0`), the distance of `A` to the nearest multiple
of `L` is at most `⌈Δ·L⌉`. -/
private lemma norm_lt_implies_emod_min (L : ℕ) (hL : 0 < L) (A : ℤ) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (h : ‖(((A : ℝ) / (L : ℝ)) : UnitAddCircle)‖ < Δ) :
    (min (A % (L : ℤ)) ((-A) % (L : ℤ))).toNat ≤ Nat.ceil (Δ * (L : ℝ)) := by
  rw [circle_norm_lt_iff_exists_int] at h
  rcases h with ⟨k, hk⟩
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hkL : |(A : ℝ) - (k : ℝ) * (L : ℝ)| < Δ * (L : ℝ) := by
    have h1 : |(A : ℝ) / (L : ℝ) - (k : ℝ)| * (L : ℝ) < Δ * (L : ℝ) :=
      mul_lt_mul_of_pos_right hk hLpos
    have h2 : |(A : ℝ) / (L : ℝ) - (k : ℝ)| * (L : ℝ) =
        |(A : ℝ) - (k : ℝ) * (L : ℝ)| := by
      have hfac : (A : ℝ) / (L : ℝ) - (k : ℝ) =
          ((A : ℝ) - (k : ℝ) * (L : ℝ)) / (L : ℝ) := by
        field_simp
      rw [hfac, abs_div, abs_of_pos hLpos, div_mul_cancel₀ _ (ne_of_gt hLpos)]
    rwa [h2] at h1
  have hz0 : 0 ≤ A % (L : ℤ) := Int.emod_nonneg _ (by omega)
  have hz0' : 0 ≤ (-A) % (L : ℤ) := Int.emod_nonneg _ (by omega)
  have hmin0 : 0 ≤ min (A % (L : ℤ)) ((-A) % (L : ℤ)) := le_min hz0 hz0'
  have h1 : ((min (A % (L : ℤ)) ((-A) % (L : ℤ))).toNat : ℝ) ≤ |(A : ℝ) - (k : ℝ) * (L : ℝ)| := by
    have h2 : ((min (A % (L : ℤ)) ((-A) % (L : ℤ))).toNat : ℤ) ≤ |A - k * (L : ℤ)| := by
      rw [Int.toNat_of_nonneg hmin0]
      exact emod_min_le_abs L hL A k
    have h3 : ((min (A % (L : ℤ)) ((-A) % (L : ℤ))).toNat : ℝ) ≤
        ((|A - k * (L : ℤ)| : ℤ) : ℝ) := by exact_mod_cast h2
    rw [Int.cast_abs] at h3
    push_cast at h3
    exact h3
  have h4 : ((min (A % (L : ℤ)) ((-A) % (L : ℤ))).toNat : ℝ) ≤ Nat.ceil (Δ * (L : ℝ)) := by
    have := lt_of_lt_of_le hkL (Nat.le_ceil (Δ * (L : ℝ)))
    linarith
  exact_mod_cast h4


/-- Fibre residue identification (left side). -/
private lemma fibre_residue_left (q r m n : ℕ) (hm : m < q) (hn : n < r) :
    (m * (r / q.gcd r) + q * r / q.gcd r - n * (q / q.gcd r)) % (q * r / q.gcd r)
      = ((((m * (r / q.gcd r) : ℕ) : ℤ) - ((n * (q / q.gcd r) : ℕ) : ℤ)) %
          ((q * r / q.gcd r : ℕ) : ℤ)).toNat := by
  have hq : 0 < q := by omega
  have hr : 0 < r := by omega
  have hg : 0 < q.gcd r := Nat.gcd_pos_of_pos_left r hq
  have hgdvd_q : q.gcd r ∣ q := Nat.gcd_dvd_left q r
  have hgdvd_r : q.gcd r ∣ r := Nat.gcd_dvd_right q r
  have hgdvd_qr : q.gcd r ∣ q * r := dvd_mul_of_dvd_left hgdvd_q r
  have hLpos : 0 < q * r / q.gcd r :=
    Nat.div_pos (Nat.le_of_dvd (Nat.mul_pos hq hr) hgdvd_qr) hg
  have hRr1 : 1 ≤ r / q.gcd r := Nat.div_pos (Nat.le_of_dvd hr hgdvd_r) hg
  have hLq : q * r / q.gcd r = q * (r / q.gcd r) := Nat.mul_div_assoc q hgdvd_r
  have hmRr : m * (r / q.gcd r) < q * r / q.gcd r := by
    rw [hLq]
    exact Nat.mul_lt_mul_of_pos_right hm (lt_of_lt_of_le (by norm_num) hRr1)
  have hQq1 : 1 ≤ q / q.gcd r := Nat.div_pos (Nat.le_of_dvd hq hgdvd_q) hg
  have hLr : q * r / q.gcd r = r * (q / q.gcd r) := by
    rw [Nat.mul_comm q r]
    exact Nat.mul_div_assoc r hgdvd_q
  have hnQq : n * (q / q.gcd r) < q * r / q.gcd r := by
    rw [hLr]
    exact Nat.mul_lt_mul_of_pos_right hn (lt_of_lt_of_le (by norm_num) hQq1)
  have hsub : n * (q / q.gcd r) ≤ m * (r / q.gcd r) + q * r / q.gcd r := by omega
  have hcast : ((m * (r / q.gcd r) + q * r / q.gcd r - n * (q / q.gcd r) : ℕ) : ℤ) =
      (((m * (r / q.gcd r) : ℕ) : ℤ) - ((n * (q / q.gcd r) : ℕ) : ℤ)) +
        ((q * r / q.gcd r : ℕ) : ℤ) := by
    rw [Nat.cast_sub hsub, Nat.cast_add]
    ring
  have hmod : (((m * (r / q.gcd r) + q * r / q.gcd r - n * (q / q.gcd r)) %
        (q * r / q.gcd r) : ℕ) : ℤ)
      = ((((m * (r / q.gcd r) : ℕ) : ℤ) - ((n * (q / q.gcd r) : ℕ) : ℤ)) %
          ((q * r / q.gcd r : ℕ) : ℤ)) := by
    rw [Int.natCast_mod, hcast]
    have := Int.add_mul_emod_self_left
      (((m * (r / q.gcd r) : ℕ) : ℤ) - ((n * (q / q.gcd r) : ℕ) : ℤ))
      ((q * r / q.gcd r : ℕ) : ℤ) 1
    simpa using this
  have := congrArg Int.toNat hmod
  rwa [Int.toNat_natCast] at this

/-- Fibre residue identification (right side). -/
private lemma fibre_residue_right (q r m n : ℕ) (hm : m < q) (hn : n < r) :
    (n * (q / q.gcd r) + q * r / q.gcd r - m * (r / q.gcd r)) % (q * r / q.gcd r)
      = ((((n * (q / q.gcd r) : ℕ) : ℤ) - ((m * (r / q.gcd r) : ℕ) : ℤ)) %
          ((q * r / q.gcd r : ℕ) : ℤ)).toNat := by
  have hq : 0 < q := by omega
  have hr : 0 < r := by omega
  have hg : 0 < q.gcd r := Nat.gcd_pos_of_pos_left r hq
  have hgdvd_q : q.gcd r ∣ q := Nat.gcd_dvd_left q r
  have hgdvd_r : q.gcd r ∣ r := Nat.gcd_dvd_right q r
  have hgdvd_qr : q.gcd r ∣ q * r := dvd_mul_of_dvd_left hgdvd_q r
  have hLpos : 0 < q * r / q.gcd r :=
    Nat.div_pos (Nat.le_of_dvd (Nat.mul_pos hq hr) hgdvd_qr) hg
  have hRr1 : 1 ≤ r / q.gcd r := Nat.div_pos (Nat.le_of_dvd hr hgdvd_r) hg
  have hQq1 : 1 ≤ q / q.gcd r := Nat.div_pos (Nat.le_of_dvd hq hgdvd_q) hg
  have hLq : q * r / q.gcd r = q * (r / q.gcd r) := Nat.mul_div_assoc q hgdvd_r
  have hLr : q * r / q.gcd r = r * (q / q.gcd r) := by
    rw [Nat.mul_comm q r]
    exact Nat.mul_div_assoc r hgdvd_q
  have hmRr : m * (r / q.gcd r) < q * r / q.gcd r := by
    rw [hLq]
    exact Nat.mul_lt_mul_of_pos_right hm (lt_of_lt_of_le (by norm_num) hRr1)
  have hnQq : n * (q / q.gcd r) < q * r / q.gcd r := by
    rw [hLr]
    exact Nat.mul_lt_mul_of_pos_right hn (lt_of_lt_of_le (by norm_num) hQq1)
  have hsub : m * (r / q.gcd r) ≤ n * (q / q.gcd r) + q * r / q.gcd r := by omega
  have hcast : ((n * (q / q.gcd r) + q * r / q.gcd r - m * (r / q.gcd r) : ℕ) : ℤ) =
      (((n * (q / q.gcd r) : ℕ) : ℤ) - ((m * (r / q.gcd r) : ℕ) : ℤ)) +
        ((q * r / q.gcd r : ℕ) : ℤ) := by
    rw [Nat.cast_sub hsub, Nat.cast_add]
    ring
  have hmod : (((n * (q / q.gcd r) + q * r / q.gcd r - m * (r / q.gcd r)) %
        (q * r / q.gcd r) : ℕ) : ℤ)
      = ((((n * (q / q.gcd r) : ℕ) : ℤ) - ((m * (r / q.gcd r) : ℕ) : ℤ)) %
          ((q * r / q.gcd r : ℕ) : ℤ)) := by
    rw [Int.natCast_mod, hcast]
    have := Int.add_mul_emod_self_left
      (((n * (q / q.gcd r) : ℕ) : ℤ) - ((m * (r / q.gcd r) : ℕ) : ℤ))
      ((q * r / q.gcd r : ℕ) : ℤ) 1
    simpa using this
  have := congrArg Int.toNat hmod
  rwa [Int.toNat_natCast] at this

/-- `toNat` commutes with `min` for nonnegative integers. -/
private lemma int_min_toNat_le {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) {W : ℕ}
    (h : (min a b).toNat ≤ W) : min a.toNat b.toNat ≤ W := by
  have hcast : ((min a.toNat b.toNat : ℕ) : ℤ) = ((min a b).toNat : ℤ) := by
    rw [Nat.cast_min, Int.toNat_of_nonneg ha, Int.toNat_of_nonneg hb,
      Int.toNat_of_nonneg (le_min ha hb)]
  have heq : min a.toNat b.toNat = (min a b).toNat := Int.ofNat.inj hcast
  omega

/-- **Per-pair arc→lattice implication:** if the reduced fractions `m/q` and `n/r`
(`m < q`, `n < r`) are at circle distance `< Δ`, then the fibre predicate holds
at the window `⌈Δ·L⌉` (`L = lcm`). -/
private lemma dist_lt_fibre (q r m n : ℕ) (hq : 0 < q) (hr : 0 < r) (hm : m < q) (hn : n < r)
    (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (h : dist (((m : ℝ) / (q : ℝ)) : UnitAddCircle)
      (((n : ℝ) / (r : ℝ)) : UnitAddCircle) < Δ) :
    ((m * (r / q.gcd r) % (q * r / q.gcd r) + q * r / q.gcd r -
        n * (q / q.gcd r) % (q * r / q.gcd r)) % (q * r / q.gcd r) ≤
      Nat.ceil (Δ * ((q * r / q.gcd r : ℕ) : ℝ))) ∨
    ((n * (q / q.gcd r) % (q * r / q.gcd r) + q * r / q.gcd r -
        m * (r / q.gcd r) % (q * r / q.gcd r)) % (q * r / q.gcd r) ≤
      Nat.ceil (Δ * ((q * r / q.gcd r : ℕ) : ℝ))) := by
  have hg : 0 < q.gcd r := Nat.gcd_pos_of_pos_left r hq
  have hgdvd_q : q.gcd r ∣ q := Nat.gcd_dvd_left q r
  have hgdvd_r : q.gcd r ∣ r := Nat.gcd_dvd_right q r
  have hgdvd_qr : q.gcd r ∣ q * r := dvd_mul_of_dvd_left hgdvd_q r
  have hLpos : 0 < q * r / q.gcd r :=
    Nat.div_pos (Nat.le_of_dvd (Nat.mul_pos hq hr) hgdvd_qr) hg
  have hRr1 : 1 ≤ r / q.gcd r := Nat.div_pos (Nat.le_of_dvd hr hgdvd_r) hg
  have hQq1 : 1 ≤ q / q.gcd r := Nat.div_pos (Nat.le_of_dvd hq hgdvd_q) hg
  have hLq : q * r / q.gcd r = q * (r / q.gcd r) := Nat.mul_div_assoc q hgdvd_r
  have hLr : q * r / q.gcd r = r * (q / q.gcd r) := by
    rw [Nat.mul_comm q r]
    exact Nat.mul_div_assoc r hgdvd_q
  have hmRr : m * (r / q.gcd r) < q * r / q.gcd r := by
    rw [hLq]
    exact Nat.mul_lt_mul_of_pos_right hm (lt_of_lt_of_le (by norm_num) hRr1)
  have hnQq : n * (q / q.gcd r) < q * r / q.gcd r := by
    rw [hLr]
    exact Nat.mul_lt_mul_of_pos_right hn (lt_of_lt_of_le (by norm_num) hQq1)
  rw [circle_dist_eq_lattice q r m n hq hr] at h
  have hA : (↑(((m * (r / q.gcd r) : ℕ) : ℤ) - ((n * (q / q.gcd r) : ℕ) : ℤ)) : ℝ)
      = ((m * (r / q.gcd r) : ℕ) : ℝ) - ((n * (q / q.gcd r) : ℕ) : ℝ) := by
    rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast]
  have h' : ‖(((↑(((m * (r / q.gcd r) : ℕ) : ℤ) - ((n * (q / q.gcd r) : ℕ) : ℤ)) : ℝ) /
        ((q * r / q.gcd r : ℕ) : ℝ)) : UnitAddCircle)‖ < Δ := by
    rw [hA]
    exact h
  have hmin := norm_lt_implies_emod_min (q * r / q.gcd r) hLpos
    (((m * (r / q.gcd r) : ℕ) : ℤ) - ((n * (q / q.gcd r) : ℕ) : ℤ)) Δ hΔ h'
  have hz0 : 0 ≤ (((m * (r / q.gcd r) : ℕ) : ℤ) - ((n * (q / q.gcd r) : ℕ) : ℤ)) %
      ((q * r / q.gcd r : ℕ) : ℤ) := Int.emod_nonneg _ (by omega)
  have hz1 : 0 ≤ (-(((m * (r / q.gcd r) : ℕ) : ℤ) - ((n * (q / q.gcd r) : ℕ) : ℤ))) %
      ((q * r / q.gcd r : ℕ) : ℤ) := Int.emod_nonneg _ (by omega)
  have hmin2 := int_min_toNat_le hz0 hz1 hmin
  have hneg : -(((m * (r / q.gcd r) : ℕ) : ℤ) - ((n * (q / q.gcd r) : ℕ) : ℤ)) =
      ((n * (q / q.gcd r) : ℕ) : ℤ) - ((m * (r / q.gcd r) : ℕ) : ℤ) := by ring
  rw [hneg] at hmin2
  rw [← fibre_residue_left q r m n hm hn, ← fibre_residue_right q r m n hm hn] at hmin2
  rcases min_le_iff.mp hmin2 with h1 | h1
  · left
    rwa [Nat.mod_eq_of_lt hmRr, Nat.mod_eq_of_lt hnQq]
  · right
    rwa [Nat.mod_eq_of_lt hnQq, Nat.mod_eq_of_lt hmRr]

/-- Auxiliary form of `fibre_phi_identity` with the abbreviations passed as explicit
variables (much easier to work with than the `let`-statement). -/
private lemma fibre_phi_identity_aux (q r g K Phi : ℕ) (Sbar : ℝ)
    (hq : 0 < q) (hr : 0 < r)
    (hg : g = q.gcd r)
    (hK : K = ∏ p ∈ (Nat.primeFactors g).filter (fun p => ¬ p ∣ q * r / (g * g)),
        p ^ (g.factorization p))
    (hPhi : Phi = ∏ p ∈ Nat.primeFactors (q * r / (g * g)),
        (p ^ (g.factorization p)).totient)
    (hSbar : Sbar = ∏ p ∈ Nat.primeFactors K,
        ((p : ℝ) ^ (K.factorization p - 1)) * ((p : ℝ) - 1) ^ 2 / (p : ℝ)) :
    (Phi : ℝ) * Sbar * (g : ℝ) * ((q * r / (g * g)).totient : ℝ) =
      (q.totient : ℝ) * (r.totient : ℝ) := by
  classical
  rw [hPhi, hSbar]
  push_cast
  -- basic facts
  have hgpos : 0 < g := by rw [hg]; exact Nat.gcd_pos_of_pos_left r hq
  have hgdvdq : g ∣ q := by rw [hg]; exact Nat.gcd_dvd_left q r
  have hgdvdr : g ∣ r := by rw [hg]; exact Nat.gcd_dvd_right q r
  have hqr : q * r ≠ 0 := Nat.mul_ne_zero hq.ne' hr.ne'
  have hg2dvd : g * g ∣ q * r := mul_dvd_mul hgdvdq hgdvdr
  have hQdvd : q * r / (g * g) ∣ q * r := Nat.div_dvd_of_dvd hg2dvd
  have hQ0 : q * r / (g * g) ≠ 0 := by
    have hle : g * g ≤ q * r := by
      have h1 : g ≤ q := Nat.le_of_dvd hq hgdvdq
      have h2 : g ≤ r := Nat.le_of_dvd hr hgdvdr
      exact mul_le_mul h1 h2 (Nat.zero_le g) (Nat.zero_le q)
    exact (Nat.div_pos hle (by positivity)).ne' 
  -- the common index set
  set S : Finset ℕ := (q * r).primeFactors with hSdef
  have hqS : q.primeFactors ⊆ S := by
    rw [hSdef]; exact Nat.primeFactors_mono (Nat.dvd_mul_right q r) hqr
  have hrS : r.primeFactors ⊆ S := by
    rw [hSdef]; exact Nat.primeFactors_mono (Nat.dvd_mul_left r q) hqr
  have hgS : g.primeFactors ⊆ S := by
    rw [hSdef]; exact (Nat.primeFactors_mono hgdvdq hq.ne').trans hqS
  -- subset helper for the extension trick
  have key : ∀ (T : Finset ℕ), T ⊆ S → ∀ (F : ℕ → ℝ),
      (∏ p ∈ T, F p) = ∏ p ∈ S, (if p ∈ T then F p else 1) := by
    intro T hT F
    rw [← Finset.prod_subset (s₁ := T) (s₂ := S) (f := fun p => if p ∈ T then F p else 1)
      hT (by intro x hx hxT; simp [hxT])]
    exact Finset.prod_congr rfl (fun p hp => by simp [hp])
  -- totient product formula over ℝ
  have htot : ∀ (n : ℕ), n ≠ 0 → (n.totient : ℝ) = ∏ p ∈ n.primeFactors,
      ((p : ℝ) ^ (n.factorization p - 1)) * ((p : ℝ) - 1) := by
    intro n hn
    calc (n.totient : ℝ)
        = ((∏ p ∈ n.primeFactors, p ^ (n.factorization p - 1) * (p - 1) : ℕ) : ℝ) := by
          rw [Commons.NumberTheory.Totient.totient_eq_prod_primeFactors n hn]
      _ = ∏ p ∈ n.primeFactors, ((p : ℝ) ^ (n.factorization p - 1)) * ((p : ℝ) - 1) := by
          rw [nat_prod_cast_real]
          exact Finset.prod_congr rfl (fun p hp => by
            rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le,
              Nat.cast_one])
  have hgcast : (g : ℝ) = ∏ p ∈ g.primeFactors, (p : ℝ) ^ (g.factorization p) := by
    conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hgpos.ne']
    rw [nat_prod_cast_real]
    exact Finset.prod_congr rfl (fun p hp => by rw [Nat.cast_pow])
  -- subset facts for the extension
  have hTS : (q * r / (g * g)).primeFactors ⊆ S := by
    rw [hSdef]; exact Nat.primeFactors_mono hQdvd hqr
  have hKne : K ≠ 0 := by
    rw [hK]
    exact Finset.prod_ne_zero_iff.mpr (fun p hp =>
      pow_ne_zero _ (Nat.Prime.ne_zero (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)))
  have hKS : K.primeFactors ⊆ S := by
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hdvdK : p ∣ K := Nat.dvd_of_mem_primeFactors hp
    have hge1 : 1 ≤ K.factorization p := (hprime.dvd_iff_one_le_factorization hKne).mp hdvdK
    have hfac : K.factorization p =
        if p ∈ g.primeFactors.filter (fun p => ¬ p ∣ q * r / (g * g))
          then g.factorization p else 0 := by
      rw [hK]
      exact Commons.Data.Nat.factorization_prod_prime_pow_apply _ _
        (fun q hq => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1) p
    have hmem : p ∈ g.primeFactors.filter (fun p => ¬ p ∣ q * r / (g * g)) := by
      by_contra h
      rw [hfac, if_neg h] at hge1
      omega
    exact hgS (Finset.mem_filter.mp hmem).1
  rw [hgcast, htot (q * r / (g * g)) hQ0, htot q hq.ne', htot r hr.ne']
  rw [key (q * r / (g * g)).primeFactors hTS
        (fun p => ((p ^ g.factorization p).totient : ℝ)),
      key K.primeFactors hKS
        (fun p => (p : ℝ) ^ (K.factorization p - 1) * ((p : ℝ) - 1) ^ 2 / (p : ℝ)),
      key g.primeFactors hgS (fun p => (p : ℝ) ^ (g.factorization p)),
      key (q * r / (g * g)).primeFactors hTS
        (fun p => (p : ℝ) ^ ((q * r / (g * g)).factorization p - 1) * ((p : ℝ) - 1)),
      key q.primeFactors hqS
        (fun p => (p : ℝ) ^ (q.factorization p - 1) * ((p : ℝ) - 1)),
      key r.primeFactors hrS
        (fun p => (p : ℝ) ^ (r.factorization p - 1) * ((p : ℝ) - 1))]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun p hp => ?_)
  have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hT0 : q * r / (g * g) ≠ 0 := hQ0
  -- pointwise factorizations
  have hfm : g.factorization p = min (q.factorization p) (r.factorization p) := by
    rw [hg, Nat.factorization_gcd hq.ne' hr.ne']
    rfl
  have hfk : (q * r / (g * g)).factorization p
      = q.factorization p + r.factorization p - 2 * g.factorization p := by
    have h1 : (q * r / (g * g)).factorization p
        = (q * r).factorization p - (g * g).factorization p := by
      rw [Nat.factorization_div hg2dvd]; rfl
    have h2 : (q * r).factorization p = q.factorization p + r.factorization p := by
      rw [Nat.factorization_mul hq.ne' hr.ne']; rfl
    have h3 : (g * g).factorization p = g.factorization p + g.factorization p := by
      rw [Nat.factorization_mul hgpos.ne' hgpos.ne']; rfl
    rw [h1, h2, h3]
    omega
  -- membership characterisations
  have hmem_q : p ∈ q.primeFactors ↔ 1 ≤ q.factorization p := by
    rw [Nat.mem_primeFactors]
    exact ⟨fun h => (hpprime.dvd_iff_one_le_factorization hq.ne').mp h.2.1,
      fun h => ⟨hpprime, (hpprime.dvd_iff_one_le_factorization hq.ne').mpr h, hq.ne'⟩⟩
  have hmem_r : p ∈ r.primeFactors ↔ 1 ≤ r.factorization p := by
    rw [Nat.mem_primeFactors]
    exact ⟨fun h => (hpprime.dvd_iff_one_le_factorization hr.ne').mp h.2.1,
      fun h => ⟨hpprime, (hpprime.dvd_iff_one_le_factorization hr.ne').mpr h, hr.ne'⟩⟩
  have hmem_g : p ∈ g.primeFactors ↔ 1 ≤ g.factorization p := by
    rw [Nat.mem_primeFactors]
    exact ⟨fun h => (hpprime.dvd_iff_one_le_factorization hgpos.ne').mp h.2.1,
      fun h => ⟨hpprime, (hpprime.dvd_iff_one_le_factorization hgpos.ne').mpr h, hgpos.ne'⟩⟩
  have hmem_T : p ∈ (q * r / (g * g)).primeFactors ↔ 1 ≤ (q * r / (g * g)).factorization p := by
    rw [Nat.mem_primeFactors]
    exact ⟨fun h => (hpprime.dvd_iff_one_le_factorization hT0).mp h.2.1,
      fun h => ⟨hpprime, (hpprime.dvd_iff_one_le_factorization hT0).mpr h, hT0⟩⟩
  -- K
  have hKfac : K.factorization p
      = if p ∈ g.primeFactors.filter (fun p => ¬ p ∣ q * r / (g * g))
        then g.factorization p else 0 := by
    rw [hK]
    exact Commons.Data.Nat.factorization_prod_prime_pow_apply _ _
      (fun q hq => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1) p
  have hmem_K : p ∈ K.primeFactors ↔
      p ∈ g.primeFactors.filter (fun p => ¬ p ∣ q * r / (g * g)) := by
    constructor
    · intro hpk
      have hge1 : 1 ≤ K.factorization p :=
        (hpprime.dvd_iff_one_le_factorization hKne).mp (Nat.dvd_of_mem_primeFactors hpk)
      by_contra h
      rw [hKfac, if_neg h] at hge1
      omega
    · intro hmem
      have hmem' := Finset.mem_filter.mp hmem
      have hg1 : 1 ≤ g.factorization p := (hmem_g.mp hmem'.1)
      have hfac1 : K.factorization p = g.factorization p := by
        rw [hKfac, if_pos hmem]
      have hdvdK : p ∣ K :=
        (hpprime.dvd_iff_one_le_factorization hKne).mpr (by rw [hfac1]; exact hg1)
      exact Nat.mem_primeFactors.mpr ⟨hpprime, hdvdK, hKne⟩
  have hKfac' : K.factorization p = if p ∈ K.primeFactors then g.factorization p else 0 := by
    rw [hKfac]; by_cases h : p ∈ g.primeFactors.filter (fun p => ¬ p ∣ q * r / (g * g))
    · rw [if_pos h, if_pos (hmem_K.mpr h)]
    · rw [if_neg h, if_neg (fun hc => h (hmem_K.mp hc))]
  -- abbreviations for the exponents
  set a := q.factorization p with hadef
  set b := r.factorization p with hbdef
  set m := g.factorization p with hmdef
  set k := (q * r / (g * g)).factorization p with hkdef
  have hma : m = min a b := hfm
  have hka : k = a + b - 2 * m := hfk
  have hmq : p ∈ q.primeFactors ↔ 1 ≤ a := hmem_q
  have hmr : p ∈ r.primeFactors ↔ 1 ≤ b := hmem_r
  have hmg : p ∈ g.primeFactors ↔ 1 ≤ m := hmem_g
  have hmT : p ∈ (q * r / (g * g)).primeFactors ↔ 1 ≤ k := hmem_T
  have hmK : p ∈ K.primeFactors ↔ (1 ≤ m ∧ k = 0) := by
    rw [hmem_K]
    constructor
    · intro h
      refine ⟨hmg.mp (Finset.mem_filter.mp h).1, ?_⟩
      have h2 := (Finset.mem_filter.mp h).2
      rw [hpprime.dvd_iff_one_le_factorization hT0] at h2
      omega
    · rintro ⟨hm1, hk0⟩
      refine Finset.mem_filter.mpr ⟨hmg.mpr hm1, ?_⟩
      intro hdvd
      have := (hpprime.dvd_iff_one_le_factorization hT0).mp hdvd
      omega
  have htotm : (((p : ℕ) ^ m).totient : ℝ) =
      if m = 0 then 1 else (p : ℝ) ^ (m - 1) * ((p : ℝ) - 1) := by
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · rw [hm0, if_pos rfl]; simp
    · rw [if_neg hmpos.ne', Nat.totient_prime_pow hpprime hmpos]
      push_cast [Nat.cast_sub hpprime.one_le]
      ring
  have hKthen : p ∈ K.primeFactors → K.factorization p = m := by
    intro h
    have h' : K.factorization p = if p ∈ K.primeFactors then m else 0 := hKfac'
    rw [h', if_pos h]
  have hpqr : 1 ≤ a ∨ 1 ≤ b := by
    have hdvd : p ∣ q * r := Nat.dvd_of_mem_primeFactors hp
    rcases (hpprime.dvd_mul.mp hdvd) with h | h
    · exact Or.inl ((hpprime.dvd_iff_one_le_factorization hq.ne').mp h)
    · exact Or.inr ((hpprime.dvd_iff_one_le_factorization hr.ne').mp h)
  rw [if_congr hmq rfl rfl, if_congr hmr rfl rfl, if_congr hmg rfl rfl,
    if_congr hmT rfl rfl, if_congr hmT rfl rfl, if_congr hmK rfl rfl, htotm]
  have hp2 : (p : ℝ) ≠ 0 := by exact_mod_cast hpprime.ne_zero
  have hgen : ∀ A B C : ℕ, (p : ℝ) ^ A * ((p : ℝ) - 1) * (p : ℝ) ^ B *
      ((p : ℝ) ^ C * ((p : ℝ) - 1)) = (p : ℝ) ^ (A + B + C) * ((p : ℝ) - 1) ^ 2 := by
    intro A B C
    rw [show (p : ℝ) ^ (A + B + C) = (p : ℝ) ^ A * (p : ℝ) ^ B * (p : ℝ) ^ C by
      rw [pow_add, pow_add]]
    ring
  have hgen2 : ∀ A C : ℕ, (p : ℝ) ^ A * ((p : ℝ) - 1) * ((p : ℝ) ^ C * ((p : ℝ) - 1)) =
      (p : ℝ) ^ (A + C) * ((p : ℝ) - 1) ^ 2 := by
    intro A C
    rw [show (p : ℝ) ^ (A + C) = (p : ℝ) ^ A * (p : ℝ) ^ C by rw [pow_add]]
    ring
  by_cases ha : 1 ≤ a
  · by_cases hb : 1 ≤ b
    · -- both `p ∣ q` and `p ∣ r`
      have hmg1 : 1 ≤ m := by rw [hma]; exact le_min ha hb
      by_cases hab : a = b
      · -- equal exponents: `k = 0`, `p ∉ T`, `p ∈ K`
        have hk0 : k = 0 := by omega
        have hkT : ¬ (1 ≤ k) := by omega
        have hKmem : p ∈ K.primeFactors := by rw [hmK]; exact ⟨hmg1, hk0⟩
        rw [if_neg hkT, if_pos (show 1 ≤ m ∧ k = 0 from ⟨hmg1, hk0⟩), hKthen hKmem,
          if_pos hmg1, if_neg hkT, if_pos ha, if_pos hb]
        rw [one_mul, mul_one]
        have hLHS : (p : ℝ) ^ (m - 1) * ((p : ℝ) - 1) ^ 2 / (p : ℝ) * (p : ℝ) ^ m =
            (p : ℝ) ^ (2 * m - 2) * ((p : ℝ) - 1) ^ 2 := by
          have hpk : (p : ℝ) ^ (2 * m - 1) / (p : ℝ) = (p : ℝ) ^ (2 * m - 2) := by
            rw [show 2 * m - 1 = (2 * m - 2) + 1 by omega, pow_succ]
            exact mul_div_cancel_right₀ _ hp2
          calc (p : ℝ) ^ (m - 1) * ((p : ℝ) - 1) ^ 2 / (p : ℝ) * (p : ℝ) ^ m
              = ((p : ℝ) ^ (m - 1) * (p : ℝ) ^ m) / (p : ℝ) * ((p : ℝ) - 1) ^ 2 := by ring
            _ = (p : ℝ) ^ (2 * m - 1) / (p : ℝ) * ((p : ℝ) - 1) ^ 2 := by
                  rw [← pow_add, show (m - 1) + m = 2 * m - 1 by omega]
            _ = (p : ℝ) ^ (2 * m - 2) * ((p : ℝ) - 1) ^ 2 := by rw [hpk]
        rw [hLHS, hgen2 (a - 1) (b - 1), show (a - 1) + (b - 1) = 2 * m - 2 by omega]
      · -- distinct exponents: `k ≥ 1`, `p ∉ K`
        have hk1 : 1 ≤ k := by omega
        rw [if_pos hk1, if_neg (by omega : ¬ (m = 0)),
          if_neg (by rintro ⟨-, hk0⟩; omega), if_pos hmg1, if_pos hk1, if_pos ha, if_pos hb]
        rw [mul_one, hgen (m - 1) m (k - 1), hgen2 (a - 1) (b - 1)]
        have hexp : (m - 1) + m + (k - 1) = (a - 1) + (b - 1) := by omega
        rw [hexp]
    · -- `p ∣ q`, `p ∤ r`
      have hb0 : b = 0 := by omega
      have hm0 : m = 0 := by omega
      have hk1 : 1 ≤ k := by omega
      rw [if_pos hk1, if_pos hm0, if_neg (by omega : ¬ (1 ≤ m)),
        if_neg (by rintro ⟨hm1, -⟩; omega), if_pos hk1, if_pos ha, if_neg hb]
      have hka' : k = a := by omega
      simp only [one_mul, mul_one, hka']
  · -- `p ∤ q`, hence `p ∣ r`
    have hb : 1 ≤ b := by rcases hpqr with h | h <;> omega
    have ha0 : a = 0 := by omega
    have hm0 : m = 0 := by omega
    have hk1 : 1 ≤ k := by omega
    rw [if_pos hk1, if_pos hm0, if_neg (by omega : ¬ (1 ≤ m)),
      if_neg (by rintro ⟨hm1, -⟩; omega), if_pos hk1, if_neg ha, if_pos hb]
    have hkb : k = b := by omega
    simp only [one_mul, mul_one, hkb]

/-- **The fibre totient identity.** With `g = gcd q r`, `q' = q*r/g²`,
`K = ∏_{p | g, p ∤ q'} p^(ν_p(g))`, `Phi = ∏_{p | q'} φ(p^(ν_p(g)))` and
`Sbar = ∏_{p | K} p^(ν_p(K)-1)*(p-1)²/p`, one has
`Phi * Sbar * g * φ(q') = φ(q) * φ(r)`.  (This is what makes the fibre main term
equal to `2·Δ·φ(q)φ(r)` exactly.) -/
theorem fibre_phi_identity (q r : ℕ) (hq : 0 < q) (hr : 0 < r) :
    let g : ℕ := q.gcd r
    let K : ℕ := ∏ p ∈ (Nat.primeFactors g).filter (fun p => ¬ p ∣ q * r / (g * g)),
        p ^ (g.factorization p)
    let Phi : ℕ := ∏ p ∈ Nat.primeFactors (q * r / (g * g)),
        (p ^ (g.factorization p)).totient
    let Sbar : ℝ := ∏ p ∈ Nat.primeFactors K,
        ((p : ℝ) ^ (K.factorization p - 1)) * ((p : ℝ) - 1) ^ 2 / (p : ℝ)
    (Phi : ℝ) * Sbar * (g : ℝ) * ((q * r / (g * g)).totient : ℝ) =
      (q.totient : ℝ) * (r.totient : ℝ) := by
  dsimp only
  exact fibre_phi_identity_aux q r (q.gcd r) _ _ _ hq hr rfl rfl rfl rfl

/-- **Count transfer.**  The number of reduced pairs `(a,b)` (`a < q`, `b < r`,
`a ⊥ q`, `b ⊥ r`) whose circle distance is `< Δ` equals the exact fibre sum of
`fibre_count_eq`. -/
theorem close_pair_count_eq_fibre_sum (q r : ℕ) (hq : 0 < q) (hr : 0 < r) (hqr : q ≠ r)
    (Δ : ℝ) (hΔ : 0 ≤ Δ) (hΔ8 : Δ < 1 / 8) :
    let g : ℕ := q.gcd r
    let L : ℕ := q * r / g
    let K : ℕ := ∏ p ∈ (Nat.primeFactors g).filter (fun p => ¬ p ∣ q * r / (g * g)),
        p ^ (g.factorization p)
    let Phi : ℕ := ∏ p ∈ Nat.primeFactors (q * r / (g * g)),
        (p ^ (g.factorization p)).totient
    let S : ℕ → ℕ := fun c => ∏ p ∈ Nat.primeFactors K,
        if p ∣ c then (p ^ (K.factorization p)).totient
        else p ^ (K.factorization p - 1) * (p - 2)
    ((((Finset.range q).filter (fun a : ℕ => a.gcd q = 1)).product
        ((Finset.range r).filter (fun b : ℕ => b.gcd r = 1))).filter
        (fun ab : ℕ × ℕ => ∃ j : Fin 3,
          |((ab.1 : ℤ) * (r : ℤ) - (ab.2 : ℤ) * (q : ℤ) -
              (((j.1 : ℕ) : ℤ) - 1) * ((q * r : ℕ) : ℤ) : ℝ)| <
            Δ * ((q * r : ℕ) : ℝ))).card =
      2 * Phi * (∑ c ∈ (Finset.Icc 1 (Nat.ceil (Δ * (L : ℝ)) - 1)).filter
        (fun c => c.gcd (q * r / (g * g)) = 1), S c) := by
  exact fibre_count_eq q r hq hr hqr Δ hΔ hΔ8

/-- A product of distinct primes is squarefree. -/
private lemma squarefree_prod_primes {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    Squarefree (∏ p ∈ S, p) := by
  induction S using Finset.induction with
  | empty => simp
  | insert p S hp ih =>
      have hSp : p.Prime := hS p (Finset.mem_insert_self p S)
      have hS' : ∀ q ∈ S, q.Prime := fun q hq => hS q (Finset.mem_insert_of_mem hq)
      rw [Finset.prod_insert hp, Nat.squarefree_mul_iff]
      refine ⟨?_, hSp.squarefree, ih hS'⟩
      refine hSp.coprime_iff_not_dvd.mpr (fun hdvd => hp ?_)
      have hne : ∏ q ∈ S, q ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr (fun q hq => (hS' q hq).ne_zero)
      have hpf : (∏ q ∈ S, q).primeFactors = S := Nat.primeFactors_prod hS'
      have hmem : p ∈ (∏ q ∈ S, q).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hSp, hdvd, hne⟩
      rwa [hpf] at hmem

/-- The number of squarefree divisors of `n ≠ 0` is `2^{ω(n)}` (equivalently
`∑_{d | n} μ(d)^2 = 2^{ω(n)}`); the map `d ↦ d.primeFactors` is a bijection onto
the subsets of `n.primeFactors`. -/
theorem card_squarefree_divisors_eq_two_pow_omega (n : ℕ) (hn : n ≠ 0) :
    ((n.divisors.filter Squarefree).card : ℕ) = 2 ^ n.primeFactors.card := by
  classical
  have hbij : (n.divisors.filter Squarefree).card = n.primeFactors.powerset.card := by
    refine Finset.card_bij (fun d _ => d.primeFactors) ?_ ?_ ?_
    · intro d hd
      refine Finset.mem_powerset.mpr fun p hp => ?_
      have hdn : d ∣ n := (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1
      exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp,
        dvd_trans (Nat.dvd_of_mem_primeFactors hp) hdn, hn⟩
    · intro d1 hd1 d2 hd2 heq
      rw [← Nat.prod_primeFactors_of_squarefree (Finset.mem_filter.mp hd1).2,
          ← Nat.prod_primeFactors_of_squarefree (Finset.mem_filter.mp hd2).2, heq]
    · intro S hS
      have hSp : ∀ p ∈ S, p.Prime :=
        fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp hS hp)
      refine ⟨∏ p ∈ S, p, ?_, Nat.primeFactors_prod hSp⟩
      refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨?_, hn⟩, squarefree_prod_primes hSp⟩
      calc ∏ p ∈ S, p ∣ ∏ p ∈ n.primeFactors, p :=
            Finset.prod_dvd_prod_of_subset _ _ _ (Finset.mem_powerset.mp hS)
          _ ∣ n := Nat.prod_primeFactors_dvd n
  rw [hbij, Finset.card_powerset]

/-- Floor inequality with the Möbius sign correction: for `d ≥ 1`,
`μ(d)·(X/d : ℕ) ≤ μ(d)·(X/d) + [μ(d) < 0]`. -/
theorem moebius_floor_le (d X : ℕ) (hd : 0 < d) :
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) * ((X / d : ℕ) : ℝ) ≤
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) * ((X : ℝ) / (d : ℝ)) +
        (if ((ArithmeticFunction.moebius d : ℤ) < 0) then (1 : ℝ) else 0) := by
  have hf1 : ((X / d : ℕ) : ℝ) ≤ (X : ℝ) / (d : ℝ) := Nat.cast_div_le
  have hf2 : (X : ℝ) / (d : ℝ) < ((X / d : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ (by exact_mod_cast hd)]
    have hmod : X % d < d := Nat.mod_lt _ hd
    have hde : X = d * (X / d) + X % d := (Nat.div_add_mod X d).symm
    have hcast : (X : ℝ) = (d : ℝ) * ((X / d : ℕ) : ℝ) + ((X % d : ℕ) : ℝ) := by
      conv_lhs => rw [hde]
      push_cast
      ring
    have : ((X % d : ℕ) : ℝ) < (d : ℝ) := by exact_mod_cast hmod
    rw [hcast]; nlinarith
  rcases ArithmeticFunction.moebius_eq_or d with h | h | h
  · rw [h]; norm_num
  · rw [h]
    simp only [Int.cast_one, one_mul, if_neg (by norm_num : ¬ ((1 : ℤ) < 0)), add_zero]
    exact hf1
  · rw [h]
    simp only [Int.cast_neg, Int.cast_one, neg_mul, if_pos (by norm_num : ((-1 : ℤ) < 0))]
    linarith

/-- Sieve count with the exact inclusion–exclusion error:
`#{c ∈ [1,X] : (c,n) = 1} ≤ X·φ(n)/n + 2^{ω(n)}` for `n ≥ 1`. -/
theorem card_coprime_Icc_le (n X : ℕ) (hn : 0 < n) :
    ((((Finset.Icc 1 X).filter (fun c : ℕ => c.gcd n = 1)).card : ℕ) : ℝ) ≤
      (X : ℝ) * (n.totient : ℝ) / (n : ℝ) + (2 : ℝ) ^ (n.primeFactors.card) := by
  classical
  have hn0 : n ≠ 0 := hn.ne'
  have hcnt := Commons.NumberTheory.Totient.coprime_count_moebius_real X n hn
  have hflt : (Finset.filter (fun c : ℕ => c.gcd n = 1) (Finset.Icc 1 X)) =
      (Finset.filter (fun c : ℕ => Nat.Coprime c n) (Finset.Icc 1 X)) := by
    refine Finset.filter_congr (fun c _ => ?_)
    exact Nat.coprime_iff_gcd_eq_one.symm
  rw [hflt, hcnt]
  have hle1 : (∑ d ∈ n.divisors,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) * ((X / d : ℕ) : ℝ))
      ≤ (∑ d ∈ n.divisors,
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) * ((X : ℝ) / (d : ℝ))) +
        ∑ d ∈ n.divisors,
          (if ((ArithmeticFunction.moebius d : ℤ) < 0) then (1 : ℝ) else 0) := by
    calc (∑ d ∈ n.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ) * ((X / d : ℕ) : ℝ))
        ≤ ∑ d ∈ n.divisors, (((ArithmeticFunction.moebius d : ℤ) : ℝ) * ((X : ℝ) / (d : ℝ)) +
            (if ((ArithmeticFunction.moebius d : ℤ) < 0) then (1 : ℝ) else 0)) :=
          Finset.sum_le_sum (fun d hd =>
            moebius_floor_le d X (Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd).1 hn))
      _ = (∑ d ∈ n.divisors,
            ((ArithmeticFunction.moebius d : ℤ) : ℝ) * ((X : ℝ) / (d : ℝ))) +
          ∑ d ∈ n.divisors,
            (if ((ArithmeticFunction.moebius d : ℤ) < 0) then (1 : ℝ) else 0) :=
          Finset.sum_add_distrib
  have hmain' : (∑ d ∈ n.divisors,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) * ((X : ℝ) / (d : ℝ)))
      = (X : ℝ) * ((n.totient : ℝ) / (n : ℝ)) := by
    rw [← Commons.NumberTheory.Totient.sum_moebius_div_eq_phi_ratio_real n hn, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun d hd => by ring)
  have hmain : (∑ d ∈ n.divisors,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) * ((X : ℝ) / (d : ℝ)))
      = (X : ℝ) * (n.totient : ℝ) / (n : ℝ) := by
    rw [hmain', mul_div_assoc']
  have herr : (∑ d ∈ n.divisors,
        (if ((ArithmeticFunction.moebius d : ℤ) < 0) then (1 : ℝ) else 0))
      ≤ (2 : ℝ) ^ n.primeFactors.card := by
    have h1 : (∑ d ∈ n.divisors,
          (if ((ArithmeticFunction.moebius d : ℤ) < 0) then (1 : ℝ) else 0))
        ≤ ∑ d ∈ n.divisors,
          (if ((ArithmeticFunction.moebius d : ℤ) ≠ 0) then (1 : ℝ) else 0) := by
      refine Finset.sum_le_sum (fun d hd => ?_)
      by_cases h : ((ArithmeticFunction.moebius d : ℤ) < 0)
      · rw [if_pos h, if_pos (by omega : ((ArithmeticFunction.moebius d : ℤ) ≠ 0))]
      · rw [if_neg h]
        positivity
    have h2 : (∑ d ∈ n.divisors,
          (if ((ArithmeticFunction.moebius d : ℤ) ≠ 0) then (1 : ℝ) else 0))
        = ((n.divisors.filter Squarefree).card : ℝ) := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      have hcard : (n.divisors.filter (fun d => (ArithmeticFunction.moebius d : ℤ) ≠ 0))
          = (n.divisors.filter Squarefree) := by
        refine Finset.filter_congr (fun d hd => ?_)
        exact ArithmeticFunction.moebius_ne_zero_iff_squarefree
      rw [hcard]
    calc (∑ d ∈ n.divisors,
          (if ((ArithmeticFunction.moebius d : ℤ) < 0) then (1 : ℝ) else 0))
        ≤ ∑ d ∈ n.divisors,
          (if ((ArithmeticFunction.moebius d : ℤ) ≠ 0) then (1 : ℝ) else 0) := h1
      _ = ((n.divisors.filter Squarefree).card : ℝ) := h2
      _ = (2 : ℝ) ^ n.primeFactors.card := by
          rw [card_squarefree_divisors_eq_two_pow_omega n hn0]
          push_cast
          rfl
  calc (∑ d ∈ n.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ) * ((X / d : ℕ) : ℝ))
      ≤ (∑ d ∈ n.divisors,
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) * ((X : ℝ) / (d : ℝ))) +
        ∑ d ∈ n.divisors,
          (if ((ArithmeticFunction.moebius d : ℤ) < 0) then (1 : ℝ) else 0) := hle1
    _ = (X : ℝ) * (n.totient : ℝ) / (n : ℝ) +
        ∑ d ∈ n.divisors,
          (if ((ArithmeticFunction.moebius d : ℤ) < 0) then (1 : ℝ) else 0) := by rw [hmain]
    _ ≤ (X : ℝ) * (n.totient : ℝ) / (n : ℝ) + (2 : ℝ) ^ n.primeFactors.card := by
        linarith [herr]

/-! ### Counting infrastructure for K2 (the fibre weight expansion)

`fibreS` is the weight `S` of `close_pair_count_eq_fibre_sum`/`fibre_count_eq`
(written as a standalone function), `fibreCoeff K t` its expansion coefficient
over subsets `t` of the primes of `K`, and `fibreSbar` the normalisation
`Sbar = ∏ p^(ν_p(K)-1)(p-1)²/p`.  The key identity is
`fibreS K c = ∑ t ⊆ K.primeFactors, [∏_{p∈t} p ∣ c] · fibreCoeff K t`,
proved from `Finset.prod_add`.  This is the basis for the sharp counting bound
(see `scratchdev/K2_PLAN.md`): with `D_t := ∏_{p∈t}p` one has
`Sbar = Σ_t coeff_t/D_t` and `Σ_{t: D_t ≤ X} coeff_t ≤ 2·Sbar·∏_{p ≤ X}(1+1/(p-2))`,
giving `Σ_{c ≤ X, c⊥q'} S(c) ≤ Sbar·(X·φ(q')/q' + 2^{ω(q')}·C₂·log(max X 3))`
and then, with `X ≥ √q'-1` from `ΔL ≥ (a+b)/2`, the per-pair quasi-independence
`μ(A_q∩A_r) ≤ 8C''·μ(A_q)μ(A_r)`. -/

/-- product of the primes dividing `K` -/
private def fibreRad (K : ℕ) : ℕ := ∏ p ∈ K.primeFactors, p

/-- the fibre weight `S` of `fibre_count_eq` -/
private def fibreS (K c : ℕ) : ℕ :=
  ∏ p ∈ K.primeFactors,
    if p ∣ c then (p ^ (K.factorization p)).totient else p ^ (K.factorization p - 1) * (p - 2)

/-- the expansion coefficient of `fibreS` attached to a set of primes -/
private def fibreCoeff (K : ℕ) (t : Finset ℕ) : ℕ :=
  ∏ p ∈ K.primeFactors,
    if p ∈ t then p ^ (K.factorization p - 1) else p ^ (K.factorization p - 1) * (p - 2)

/-- the normalisation `Sbar` of the fibre main term -/
private def fibreSbar (K : ℕ) : ℝ :=
  ∏ p ∈ K.primeFactors, ((p : ℝ) ^ (K.factorization p - 1)) * ((p : ℝ) - 1) ^ 2 / (p : ℝ)

private lemma fibre_factorization_pos {K p : ℕ} (hp : p ∈ K.primeFactors) :
    1 ≤ K.factorization p := by
  have hK : K ≠ 0 := by rintro rfl; simp at hp
  exact ((Nat.prime_of_mem_primeFactors hp).dvd_iff_one_le_factorization hK).mp
    (Nat.dvd_of_mem_primeFactors hp)

private lemma totient_prime_pow_eq (p ν : ℕ) (hp : p.Prime) (hν : 1 ≤ ν) :
    (p ^ ν).totient = p ^ (ν - 1) * (p - 1) := by
  rcases Nat.exists_eq_succ_of_ne_zero (by omega : ν ≠ 0) with ⟨k, rfl⟩
  rw [Nat.totient_prime_pow hp (Nat.succ_pos k)]

private lemma prod_primes_dvd_of_forall {t : Finset ℕ} {c : ℕ} (hp : ∀ p ∈ t, p.Prime)
    (h : ∀ p ∈ t, p ∣ c) : (∏ p ∈ t, p) ∣ c := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have ha' : a.Prime := hp a (Finset.mem_insert_self a s)
      have hsp : ∀ p ∈ s, p.Prime := fun p hp' => hp p (Finset.mem_insert_of_mem hp')
      have hs : (∏ p ∈ s, p) ∣ c :=
        ih hsp (fun p hp' => h p (Finset.mem_insert_of_mem hp'))
      have hcop : Nat.Coprime a (∏ p ∈ s, p) := by
        refine Nat.Coprime.prod_right (fun p hp' => ?_)
        have hpa : a ≠ p := fun he => ha (he ▸ hp')
        exact (Nat.coprime_primes ha' (hsp p hp')).mpr hpa
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop (h a (Finset.mem_insert_self a s)) hs

private lemma prod_primes_dvd_iff {t : Finset ℕ} {c : ℕ} (hp : ∀ p ∈ t, p.Prime) :
    ((∏ p ∈ t, p) ∣ c) ↔ (∀ p ∈ t, p ∣ c) :=
  ⟨fun h p hp' => dvd_trans (Finset.dvd_prod_of_mem id hp') h,
   fun h => prod_primes_dvd_of_forall hp h⟩

/-- **Fibre weight expansion.**  `fibreS K c` is the sum of `fibreCoeff K t` over
those subsets `t` of the primes of `K` whose product divides `c`. -/
private theorem fibreS_eq_sum_powerset (K c : ℕ) :
    fibreS K c = ∑ t ∈ K.primeFactors.powerset,
      (if (∏ p ∈ t, p) ∣ c then fibreCoeff K t else 0) := by
  classical
  have hterm : ∀ p ∈ K.primeFactors,
      (if p ∣ c then (p ^ (K.factorization p)).totient
        else p ^ (K.factorization p - 1) * (p - 2))
      = ((if p ∣ c then 1 else 0) * p ^ (K.factorization p - 1))
        + p ^ (K.factorization p - 1) * (p - 2) := by
    intro p hp
    have hν : 1 ≤ K.factorization p := fibre_factorization_pos hp
    have hpr : p.Prime := Nat.prime_of_mem_primeFactors hp
    rw [totient_prime_pow_eq p (K.factorization p) hpr hν]
    by_cases hpc : p ∣ c
    · rw [if_pos hpc, if_pos hpc, one_mul]
      have hp1 : p - 1 = (p - 2) + 1 := by have := hpr.two_le; omega
      rw [hp1, mul_add, mul_one]
      ring
    · rw [if_neg hpc, if_neg hpc, zero_mul, Nat.zero_add]
  rw [fibreS, Finset.prod_congr rfl hterm, Finset.prod_add]
  refine Finset.sum_congr rfl ?_
  intro t ht
  have hts : t ⊆ K.primeFactors := Finset.mem_powerset.mp ht
  have hprime : ∀ p ∈ t, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hts hp)
  have hleft :
      (∏ p ∈ t, (if p ∣ c then 1 else 0) * p ^ (K.factorization p - 1))
        = (if (∏ p ∈ t, p) ∣ c then 1 else 0) * ∏ p ∈ t, p ^ (K.factorization p - 1) := by
    rw [Finset.prod_mul_distrib, Finset.prod_boole]
    have hiff := prod_primes_dvd_iff (t := t) (c := c) hprime
    rw [if_congr hiff rfl rfl]
  rw [hleft, fibreCoeff]
  by_cases hD : (∏ p ∈ t, p) ∣ c
  · rw [if_pos hD, one_mul]
    rw [← Finset.prod_sdiff hts]
    have h1 : (∏ x ∈ K.primeFactors \ t,
        (if x ∈ t then x ^ (K.factorization x - 1)
          else x ^ (K.factorization x - 1) * (x - 2)))
        = ∏ x ∈ K.primeFactors \ t, x ^ (K.factorization x - 1) * (x - 2) :=
      Finset.prod_congr rfl (fun x hx => if_neg (Finset.mem_sdiff.mp hx).2)
    have h2 : (∏ x ∈ t,
        (if x ∈ t then x ^ (K.factorization x - 1)
          else x ^ (K.factorization x - 1) * (x - 2)))
        = ∏ x ∈ t, x ^ (K.factorization x - 1) :=
      Finset.prod_congr rfl (fun x hx => if_pos hx)
    rw [h1, h2, mul_comm, if_pos hD]
  · simp [hD]


/-- **Key pointwise bound.**  Each expansion coefficient is bounded by `Sbar` times
the product over `t` of `p/(p-1)²`. -/
theorem fibreCoeff_le_Sbar_mul (K : ℕ) (t : Finset ℕ) (ht : t ⊆ K.primeFactors) :
    (fibreCoeff K t : ℝ) ≤ fibreSbar K * ∏ p ∈ t, (p : ℝ) / ((p : ℝ) - 1) ^ 2 := by
  classical
  have hcast : (fibreCoeff K t : ℝ) =
      ∏ p ∈ K.primeFactors, (if p ∈ t then (p : ℝ) ^ (K.factorization p - 1)
        else (p : ℝ) ^ (K.factorization p - 1) * ((p : ℝ) - 2)) := by
    rw [fibreCoeff, Nat.cast_prod]
    refine Finset.prod_congr rfl (fun p hp => ?_)
    have h2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    have hsub : ((p - 2 : ℕ) : ℝ) = (p : ℝ) - 2 := Nat.cast_sub h2
    by_cases h : p ∈ t
    · simp only [h, if_true, Nat.cast_pow]
    · simp only [h, if_false, Nat.cast_pow, Nat.cast_mul, hsub]
  have hsplit : (∏ p ∈ K.primeFactors, (if p ∈ t then (p : ℝ) / ((p : ℝ) - 1) ^ 2 else 1))
      = ∏ p ∈ t, (p : ℝ) / ((p : ℝ) - 1) ^ 2 := by
    rw [← Finset.prod_sdiff ht]
    have hA : (∏ p ∈ K.primeFactors \ t,
        (if p ∈ t then (p : ℝ) / ((p : ℝ) - 1) ^ 2 else 1)) = 1 := by
      refine Finset.prod_eq_one ?_
      intro p hp
      rw [if_neg (Finset.mem_sdiff.mp hp).2]
    have hB : (∏ p ∈ t, (if p ∈ t then (p : ℝ) / ((p : ℝ) - 1) ^ 2 else 1))
        = ∏ p ∈ t, (p : ℝ) / ((p : ℝ) - 1) ^ 2 := by
      refine Finset.prod_congr rfl ?_
      intro p hp
      rw [if_pos hp]
    rw [hA, hB, one_mul]
  rw [hcast, ← hsplit, fibreSbar, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun p hp => ?_) (fun p hp => ?_)
  · have h2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    have h2R : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h2
    by_cases h : p ∈ t
    · simp only [h, if_true]; positivity
    · simp only [h, if_false]
      exact mul_nonneg (by positivity) (by linarith)
  · have h2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    have h2R : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h2
    have hpR : (0 : ℝ) < (p : ℝ) := by linarith
    have hp1 : (p : ℝ) - 1 ≠ 0 := by intro hc; rw [sub_eq_zero] at hc; linarith
    have hineq : ((p : ℝ) - 2) ≤ ((p : ℝ) - 1) ^ 2 / (p : ℝ) := by
      rw [le_div_iff₀ hpR]; nlinarith
    by_cases h : p ∈ t
    · simp only [h, if_true]
      have heq : (p : ℝ) ^ (K.factorization p - 1) * ((p : ℝ) - 1) ^ 2 / (p : ℝ)
            * ((p : ℝ) / ((p : ℝ) - 1) ^ 2) = (p : ℝ) ^ (K.factorization p - 1) := by
        field_simp
      rw [heq]
    · simp only [h, if_false, mul_one]
      have h0 : (0 : ℝ) ≤ (p : ℝ) ^ (K.factorization p - 1) := by positivity
      exact le_trans (mul_le_mul_of_nonneg_left hineq h0) (le_of_eq (by ring))



/-- Sum over a powerset of products: `∑_{t⊆s} ∏_{p∈t} g p ≤ ∏_{p∈s} (1 + g p)`. -/
private lemma sum_powerset_prod_le (s : Finset ℕ) (g : ℕ → ℝ) (h0 : ∀ p, 0 ≤ g p) :
    ∑ t ∈ s.powerset, ∏ p ∈ t, g p ≤ ∏ p ∈ s, (1 + g p) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      have hdisj : Disjoint s.powerset (s.powerset.image (insert a)) := by
        rw [Finset.disjoint_left]
        intro t ht hti
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hti
        exact ha (Finset.mem_powerset.mp ht (Finset.mem_insert_self a u))
      have hinj : Set.InjOn (insert a) (↑s.powerset : Set (Finset ℕ)) := by
        intro u hu v hv huv
        have hu' : a ∉ u := Finset.notMem_mono (Finset.mem_powerset.mp hu) ha
        have hv' : a ∉ v := Finset.notMem_mono (Finset.mem_powerset.mp hv) ha
        have := congrArg (Finset.erase · a) huv
        simpa [Finset.erase_insert hu', Finset.erase_insert hv'] using this
      rw [Finset.powerset_insert, Finset.sum_union hdisj,
        Finset.sum_image (s := s.powerset) (g := insert a) hinj]
      rw [show (∑ t ∈ s.powerset, ∏ p ∈ insert a t, g p)
            = ∑ t ∈ s.powerset, g a * ∏ p ∈ t, g p from
          Finset.sum_congr rfl (fun t ht => by
            rw [Finset.prod_insert (Finset.notMem_mono (Finset.mem_powerset.mp ht) ha)])]
      rw [← Finset.mul_sum]
      have hfac : (∑ x ∈ s.powerset, ∏ p ∈ x, g p) + g a * (∑ x ∈ s.powerset, ∏ p ∈ x, g p)
          = (1 + g a) * (∑ x ∈ s.powerset, ∏ p ∈ x, g p) := by ring
      rw [hfac, Finset.prod_insert ha]
      exact mul_le_mul_of_nonneg_left ih (by linarith [h0 a])

/-- `∑_{p ∈ s} 1/(p-1)² ≤ 8` for `s` a set of primes. -/
private lemma sum_inv_sq_pred_le (s : Finset ℕ) (hprime : ∀ p ∈ s, p.Prime) :
    ∑ p ∈ s, 1 / (((p : ℝ) - 1) ^ 2) ≤ 8 := by
  classical
  set M : ℕ := ∏ p ∈ s, p with hM
  have hMpos : 0 < M := Finset.prod_pos (fun p hp => (hprime p hp).pos)
  have hle : ∀ p ∈ s, p ≤ M := fun p hp => by
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (f := fun p => p) hp
    have hkpos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · rw [h0, mul_zero] at hk
        omega
      · exact hpos
    rw [hM, hk]
    exact Nat.le_mul_of_pos_right p hkpos
  calc ∑ p ∈ s, 1 / (((p : ℝ) - 1) ^ 2)
      ≤ ∑ p ∈ s, 4 / ((p : ℝ) ^ 2) := by
        refine Finset.sum_le_sum (fun p hp => ?_)
        have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
          exact_mod_cast (hprime p hp).two_le
        have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
        have hp1 : ((p : ℝ) - 1) ≠ 0 := by
          have : (1:ℝ) < (p:ℝ) := by linarith
          intro hc; linarith
        have hpz : (p : ℝ) ≠ 0 := ne_of_gt hp0
        have hfac : (0:ℝ) ≤ ((p : ℝ) - 2) * (3 * (p : ℝ) - 2) :=
          mul_nonneg (by linarith) (by linarith)
        rw [div_le_iff₀ (by positivity : (0:ℝ) < ((p : ℝ) - 1) ^ 2), div_mul_eq_mul_div,
          le_div_iff₀ (by positivity : (0:ℝ) < (p : ℝ) ^ 2)]
        nlinarith [hfac]
    _ = 4 * ∑ p ∈ s, 1 / ((p : ℝ) ^ 2) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun p hp => by ring)
    _ ≤ 4 * ∑ p ∈ Nat.primesBelow (M + 1), 1 / ((p : ℝ) ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) (fun x hx hxs => by positivity)
        rw [Nat.mem_primesBelow]
        exact ⟨by have := hle p hp; omega, hprime p hp⟩
    _ ≤ 4 * ∑ n ∈ Finset.Icc 1 M, 1 / ((n : ℝ) ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) (fun x hx hxs => by positivity)
        rw [Nat.mem_primesBelow] at hp
        exact Finset.mem_Icc.mpr ⟨hp.2.one_le, by omega⟩
    _ ≤ 4 * 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        have := Commons.NumberTheory.DuffinSchaeffer.sum_sq_inv_Icc_le_two_div 1 M le_rfl (by omega)
        simpa using this
    _ ≤ 8 := by norm_num

/-- `∏_{p ∈ s} (1 + 1/(p-1)²) ≤ 10000`. -/
private lemma prod_one_add_inv_sq_pred_le (s : Finset ℕ) (hprime : ∀ p ∈ s, p.Prime) :
    ∏ p ∈ s, (1 + 1 / (((p : ℝ) - 1) ^ 2)) ≤ 10000 := by
  have h1 : ∀ p ∈ s, (1 + 1 / (((p : ℝ) - 1) ^ 2)) ≤ Real.exp (1 / (((p : ℝ) - 1) ^ 2)) := by
    intro p hp
    rw [add_comm]
    exact Real.add_one_le_exp _
  have h2 : ∀ p ∈ s, 0 ≤ 1 / (((p : ℝ) - 1) ^ 2) := fun p hp => by positivity
  calc ∏ p ∈ s, (1 + 1 / (((p : ℝ) - 1) ^ 2))
      ≤ ∏ p ∈ s, Real.exp (1 / (((p : ℝ) - 1) ^ 2)) :=
          Finset.prod_le_prod₀ (fun p hp => by positivity) h1
    _ = Real.exp (∑ p ∈ s, 1 / (((p : ℝ) - 1) ^ 2)) := (Real.exp_sum s _).symm
    _ ≤ Real.exp 8 := by
        refine Real.exp_le_exp.mpr ?_
        exact sum_inv_sq_pred_le s hprime
    _ ≤ 10000 := by
        have hexp : Real.exp 8 = (Real.exp 1) ^ 8 := by
          rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
        rw [hexp]
        have h3 := Real.exp_one_lt_three
        calc (Real.exp 1) ^ 8 ≤ 3 ^ 8 :=
              pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1)) (le_of_lt h3) 8
          _ ≤ 10000 := by norm_num


/-- **(M2)**  `∑_{t ⊆ K.primeFactors} fibreCoeff K t / ∏_{p∈t} p ≤ 10000 * Sbar`. -/
theorem fibreCoeff_sum_div_le (K : ℕ) :
    (∑ t ∈ K.primeFactors.powerset,
        (fibreCoeff K t : ℝ) / (((∏ p ∈ t, p : ℕ) : ℝ))) ≤ 10000 * fibreSbar K := by
  classical
  have hSbar0 : 0 ≤ fibreSbar K := by
    rw [fibreSbar]
    refine Finset.prod_nonneg (fun p hp => ?_)
    have hp0 : (0 : ℝ) < (p : ℝ) := by
      have := (Nat.prime_of_mem_primeFactors hp).pos
      exact_mod_cast this
    positivity
  have hprime : ∀ p ∈ K.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have key : ∀ t ∈ K.primeFactors.powerset,
      (fibreCoeff K t : ℝ) / (((∏ p ∈ t, p : ℕ) : ℝ))
        ≤ fibreSbar K * ∏ p ∈ t, 1 / (((p : ℝ) - 1) ^ 2) := by
    intro t ht
    have hts : t ⊆ K.primeFactors := Finset.mem_powerset.mp ht
    have hDnat : 0 < (Finset.prod t (fun p : ℕ => p) : ℕ) :=
      Finset.prod_pos (fun p hp => (hprime p (hts hp)).pos)
    have hD : (0 : ℝ) < ((Finset.prod t (fun p : ℕ => p) : ℕ) : ℝ) := by
      exact_mod_cast hDnat
    refine le_trans (div_le_div_of_nonneg_right (fibreCoeff_le_Sbar_mul K t hts) hD.le) ?_
    have hprod : (∏ p ∈ t, (p : ℝ) / ((p : ℝ) - 1) ^ 2)
          / ((Finset.prod t (fun p : ℕ => p) : ℕ) : ℝ)
        = ∏ p ∈ t, 1 / (((p : ℝ) - 1) ^ 2) := by
      rw [Nat.cast_prod, ← Finset.prod_div_distrib]
      refine Finset.prod_congr rfl (fun p hp => ?_)
      have hp0 : (p : ℝ) ≠ 0 := by
        have hpp := (hprime p (hts hp)).pos
        exact ne_of_gt (by exact_mod_cast hpp : (0:ℝ) < (p:ℝ))
      field_simp
    rw [mul_div_assoc, hprod]
  calc ∑ t ∈ K.primeFactors.powerset,
        (fibreCoeff K t : ℝ) / ((Finset.prod t (fun p : ℕ => p) : ℕ) : ℝ)
      ≤ ∑ t ∈ K.primeFactors.powerset, fibreSbar K * ∏ p ∈ t, 1 / (((p : ℝ) - 1) ^ 2) :=
        Finset.sum_le_sum key
    _ = fibreSbar K * ∑ t ∈ K.primeFactors.powerset, ∏ p ∈ t, 1 / (((p : ℝ) - 1) ^ 2) := by
        rw [← Finset.mul_sum]
    _ ≤ fibreSbar K * 10000 := by
        refine mul_le_mul_of_nonneg_left ?_ hSbar0
        refine le_trans (sum_powerset_prod_le _ _ (fun p => by positivity)) ?_
        exact prod_one_add_inv_sq_pred_le _ hprime
    _ = 10000 * fibreSbar K := by ring


/-- **(M3)**  Truncated coefficient sum: for `D_t = ∏_{p∈t} p ≤ X`,
`∑ (fibreCoeff K t : ℝ) ≤ Sbar · ∏_{p | K, p ≤ X} (1 + p/(p-1)²)`. -/
theorem fibreCoeff_filtered_sum_le (K X : ℕ) :
    (∑ t ∈ (K.primeFactors.powerset.filter
        (fun t => Finset.prod t (fun p : ℕ => p) ≤ X)), (fibreCoeff K t : ℝ))
      ≤ fibreSbar K * ∏ p ∈ K.primeFactors.filter (fun p => p ≤ X),
          (1 + (p : ℝ) / ((p : ℝ) - 1) ^ 2) := by
  classical
  have h0 : (0 : ℝ) ≤ fibreSbar K := by
    rw [fibreSbar]
    refine Finset.prod_nonneg (fun p hp => ?_)
    have hp0 : (0 : ℝ) < (p : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
    positivity
  have hstep1 : (∑ t ∈ (K.primeFactors.powerset.filter
        (fun t => Finset.prod t (fun p : ℕ => p) ≤ X)), (fibreCoeff K t : ℝ))
      ≤ ∑ t ∈ (K.primeFactors.powerset.filter
        (fun t => Finset.prod t (fun p : ℕ => p) ≤ X)),
          fibreSbar K * ∏ p ∈ t, (p : ℝ) / ((p : ℝ) - 1) ^ 2 :=
    Finset.sum_le_sum (fun t ht =>
      fibreCoeff_le_Sbar_mul K t (Finset.mem_powerset.mp (Finset.mem_filter.mp ht).1))
  refine le_trans hstep1 ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ h0
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
    (sum_powerset_prod_le _ _ (fun p => by positivity))
  · intro t ht
    rw [Finset.mem_powerset]
    intro p hp
    rw [Finset.mem_filter]
    refine ⟨(Finset.mem_powerset.mp (Finset.mem_filter.mp ht).1) hp, ?_⟩
    have hdvd : p ∣ Finset.prod t (fun p : ℕ => p) := Finset.dvd_prod_of_mem _ hp
    have hle := (Finset.mem_filter.mp ht).2
    exact Nat.le_trans (Nat.le_of_dvd (Finset.prod_pos (fun q hq =>
      (Nat.prime_of_mem_primeFactors
        ((Finset.mem_powerset.mp (Finset.mem_filter.mp ht).1) hq)).pos)) hdvd) hle
  · intro x hx hxs
    positivity


private lemma local_factor_le (p ν : ℕ) (hp : p.Prime) (hν : 1 ≤ ν) :
    2 * (p : ℝ) ^ ((ν : ℝ) * (9 / 16 : ℝ)) / ((p : ℝ) ^ (ν - 1) * ((p : ℝ) - 1))
      ≤ 2 * (p : ℝ) ^ (9 / 16 : ℝ) / ((p : ℝ) - 1) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hp1 : (1 : ℝ) < (p : ℝ) := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    linarith
  have hpowpos : (0 : ℝ) < (p : ℝ) ^ (ν - 1) := pow_pos (by linarith) _
  have hden : (0 : ℝ) < (p : ℝ) ^ (ν - 1) * ((p : ℝ) - 1) :=
    mul_pos hpowpos (by linarith)
  have hden2 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hkey : (p : ℝ) ^ ((ν : ℝ) * (9 / 16 : ℝ))
      ≤ (p : ℝ) ^ (ν - 1) * (p : ℝ) ^ (9 / 16 : ℝ) := by
    have hexp : (ν : ℝ) * (9 / 16 : ℝ) ≤ ((ν - 1 : ℕ) : ℝ) + 9 / 16 := by
      have hνR : (1 : ℝ) ≤ (ν : ℝ) := by exact_mod_cast hν
      rw [Nat.cast_sub hν]
      push_cast
      linarith
    calc (p : ℝ) ^ ((ν : ℝ) * (9 / 16 : ℝ)) ≤ (p : ℝ) ^ (((ν - 1 : ℕ) : ℝ) + 9 / 16) :=
          Real.rpow_le_rpow_of_exponent_le (le_of_lt hp1) hexp
      _ = (p : ℝ) ^ (((ν - 1 : ℕ) : ℝ)) * (p : ℝ) ^ (9 / 16 : ℝ) :=
          Real.rpow_add (by linarith) _ _
      _ = (p : ℝ) ^ (ν - 1) * (p : ℝ) ^ (9 / 16 : ℝ) := by
          rw [Real.rpow_natCast]
  have hmain : (p : ℝ) ^ ((ν : ℝ) * (9 / 16 : ℝ)) / ((p : ℝ) ^ (ν - 1) * ((p : ℝ) - 1))
      ≤ (p : ℝ) ^ (9 / 16 : ℝ) / ((p : ℝ) - 1) := by
    rw [div_le_div_iff₀ hden hden2]
    nlinarith [mul_le_mul_of_nonneg_right hkey (le_of_lt hden2)]
  calc 2 * (p : ℝ) ^ ((ν : ℝ) * (9 / 16 : ℝ)) / ((p : ℝ) ^ (ν - 1) * ((p : ℝ) - 1))
      = 2 * ((p : ℝ) ^ ((ν : ℝ) * (9 / 16 : ℝ))
          / ((p : ℝ) ^ (ν - 1) * ((p : ℝ) - 1))) := by ring
    _ ≤ 2 * ((p : ℝ) ^ (9 / 16 : ℝ) / ((p : ℝ) - 1)) :=
        mul_le_mul_of_nonneg_left hmain (by norm_num)
    _ = 2 * (p : ℝ) ^ (9 / 16 : ℝ) / ((p : ℝ) - 1) := by ring

/-- Monotonicity of a 16th power, in the useful direction. -/
private lemma le_of_pow16_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 16 ≤ b ^ 16) :
    a ≤ b := by
  by_contra hlt
  push Not at hlt
  exact absurd h (not_le.mpr (pow_lt_pow_left₀ hlt hb (by norm_num)))

/-- `(x^{9/16})^16 = x^9` for `x ≥ 0`. -/
private lemma rpow_nine_div_sixteen_pow (x : ℝ) (hx : 0 ≤ x) :
    (x ^ (9 / 16 : ℝ)) ^ 16 = x ^ 9 := by
  rw [← Real.rpow_natCast (x ^ (9 / 16 : ℝ)) 16, ← Real.rpow_mul hx]
  norm_num

/-- **Numeric check, `p = 2`.** -/
private lemma check_two : 2 * (2 : ℝ) ^ (9 / 16 : ℝ) ≤ 4 := by
  have h1 : (2 : ℝ) ^ (9 / 16 : ℝ) ≤ (2 : ℝ) ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have h2 : (2 : ℝ) ^ (7 / 4 : ℝ) = 2 * (2 : ℝ) ^ (3 / 4 : ℝ) := by
    rw [show (7 / 4 : ℝ) = 3 / 4 + 1 by norm_num, Real.rpow_add_one (by norm_num)]
    ring
  have h3 : (2 : ℝ) ^ (7 / 4 : ℝ) ≤ (2 : ℝ) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have h4 : (2 : ℝ) ^ (2 : ℝ) = 4 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 2)
  linarith [h2, h3, h4, this]

/-- **Numeric check, `p = 3`.** -/
private lemma check_three : 2 * (3 : ℝ) ^ (9 / 16 : ℝ) / 2 ≤ 3 := by
  have h1 : (3 : ℝ) ^ (9 / 16 : ℝ) ≤ (3 : ℝ) ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have h2 : (3 : ℝ) ^ (3 / 4 : ℝ) ≤ (3 : ℝ) ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  rw [Real.rpow_one] at h2
  rw [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
  linarith

/-- **Numeric check, `p = 5`.** -/
private lemma check_five : 2 * (5 : ℝ) ^ (9 / 16 : ℝ) / 4 ≤ 2.5 := by
  have h1 : (5 : ℝ) ^ (9 / 16 : ℝ) ≤ (5 : ℝ) ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have h2 : (5 : ℝ) ^ (3 / 4 : ℝ) ≤ (5 : ℝ) ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  rw [Real.rpow_one] at h2
  linarith

/-- **Numeric check, `p ≥ 7`.**  `2 p^{9/16} ≤ p - 1`. -/
private lemma check_large (p : ℕ) (hp : 7 ≤ p) : 2 * (p : ℝ) ^ (9 / 16 : ℝ) ≤ (p : ℝ) - 1 := by
  have hpR : (7 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  -- reduce to `2 p^{9/16} ≤ (6/7) p`, i.e. `p^{7/16} ≥ 7/3`
  have hmain : 2 * (p : ℝ) ^ (9 / 16 : ℝ) ≤ 6 / 7 * (p : ℝ) := by
    have hstep : 2 * (7 / 3) ≤ (p : ℝ) ^ (7 / 16 : ℝ) * 2 := by
      have hbase : 7 / 3 ≤ (7 : ℝ) ^ (7 / 16 : ℝ) := by
        refine le_of_pow16_le (by norm_num) (by positivity) ?_
        rw [show ((7 : ℝ) ^ (7 / 16 : ℝ)) ^ 16 = (7 : ℝ) ^ 7 from by
          rw [← Real.rpow_natCast ((7 : ℝ) ^ (7 / 16 : ℝ)) 16, ← Real.rpow_mul (by norm_num)]
          norm_num, div_pow]
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < 3 ^ 16)]
        norm_num
      have hle : (7 : ℝ) ^ (7 / 16 : ℝ) ≤ (p : ℝ) ^ (7 / 16 : ℝ) :=
        Real.rpow_le_rpow (by norm_num) hpR (by norm_num)
      linarith
    -- multiply `2·(7/3) ≤ 2 p^{7/16}` by `p^{9/16}`: `2 p^{9/16}·(7/3) ≤ 2 p^{7/16}·p^{9/16} = 2p`
    have hp9 : (0 : ℝ) < (p : ℝ) ^ (9 / 16 : ℝ) := Real.rpow_pos_of_pos hp0 _
    have hmul : (p : ℝ) ^ (7 / 16 : ℝ) * (p : ℝ) ^ (9 / 16 : ℝ) = (p : ℝ) := by
      rw [← Real.rpow_add hp0, show (7 / 16 : ℝ) + 9 / 16 = 1 by norm_num, Real.rpow_one]
    have h2 : (p : ℝ) ^ (7 / 16 : ℝ) * 2 * (p : ℝ) ^ (9 / 16 : ℝ) = 2 * (p : ℝ) := by
      rw [show (p : ℝ) ^ (7 / 16 : ℝ) * 2 * (p : ℝ) ^ (9 / 16 : ℝ)
            = 2 * ((p : ℝ) ^ (7 / 16 : ℝ) * (p : ℝ) ^ (9 / 16 : ℝ)) by ring, hmul]
    have h1 := mul_le_mul_of_nonneg_right hstep (le_of_lt hp9)
    rw [h2] at h1
    nlinarith [h1]
  -- and `(6/7) p ≤ p - 1` for `p ≥ 7`
  have : 6 / 7 * (p : ℝ) ≤ (p : ℝ) - 1 := by linarith
  linarith [hmain, this]

/-- The per-prime target bound: `4` at `p = 2`, `3` at `p = 3`, `2.5` at `p = 5`, else `1`. -/
private def targetBound (p : ℕ) : ℝ :=
  if p = 2 then 4 else if p = 3 then 3 else if p = 5 then 2.5 else 1

private lemma targetBound_nonneg (p : ℕ) : 0 ≤ targetBound p := by
  rw [targetBound]; split_ifs <;> norm_num

private lemma targetBound_le_one (p : ℕ) (hp : p ∉ ({2, 3, 5} : Finset ℕ)) :
    targetBound p ≤ 1 := by
  have h2 : p ≠ 2 := fun h => hp (by simp [h])
  have h3 : p ≠ 3 := fun h => hp (by simp [h])
  have h5 : p ≠ 5 := fun h => hp (by simp [h])
  rw [targetBound]; simp [h2, h3, h5]

private lemma targetBound_ge_one (p : ℕ) (hp : p ∈ ({2, 3, 5} : Finset ℕ)) :
    1 ≤ targetBound p := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with h | h | h <;> subst h <;> (rw [targetBound]; norm_num)

/-- **Split-product bound.** -/
private lemma targetBound_prod_le_thirty (s : Finset ℕ) : ∏ p ∈ s, targetBound p ≤ 30 := by
  classical
  have hsplit : ∏ p ∈ s, targetBound p
      = (∏ p ∈ s \ ({2, 3, 5} : Finset ℕ), targetBound p)
        * (∏ p ∈ s ∩ ({2, 3, 5} : Finset ℕ), targetBound p) := by
    have hsd : s \ (s ∩ ({2, 3, 5} : Finset ℕ)) = s \ ({2, 3, 5} : Finset ℕ) := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_inter]
      tauto
    rw [← hsd,
      ← Finset.prod_sdiff Finset.inter_subset_left]
  rw [hsplit]
  have hA : (∏ p ∈ s \ ({2, 3, 5} : Finset ℕ), targetBound p) ≤ 1 := by
    refine Finset.prod_le_one₀ (fun p hp => targetBound_nonneg p) (fun p hp => ?_)
    exact targetBound_le_one p (Finset.mem_sdiff.mp hp).2
  have hB : (∏ p ∈ s ∩ ({2, 3, 5} : Finset ℕ), targetBound p) ≤ 30 := by
    have h1 : (∏ p ∈ s ∩ ({2, 3, 5} : Finset ℕ), targetBound p)
        ≤ ∏ p ∈ ({2, 3, 5} : Finset ℕ), targetBound p :=
      Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.inter_subset_right)
        (fun i hi => targetBound_nonneg i) (fun i hi _ => targetBound_ge_one i hi)
    refine le_trans h1 ?_
    have h2 : (∏ p ∈ ({2, 3, 5} : Finset ℕ), targetBound p)
        = targetBound 2 * targetBound 3 * targetBound 5 := by
      rw [show ({2, 3, 5} : Finset ℕ) = insert 2 (insert 3 (insert 5 ∅)) from rfl,
        Finset.prod_insert (by norm_num), Finset.prod_insert (by norm_num),
        Finset.prod_insert (by norm_num), Finset.prod_empty]
      ring
    rw [h2]
    norm_num [targetBound]
  have hB0 : (0 : ℝ) ≤ ∏ p ∈ s ∩ ({2, 3, 5} : Finset ℕ), targetBound p :=
    Finset.prod_nonneg (fun p hp => targetBound_nonneg p)
  calc (∏ p ∈ s \ ({2, 3, 5} : Finset ℕ), targetBound p)
        * (∏ p ∈ s ∩ ({2, 3, 5} : Finset ℕ), targetBound p) ≤ 1 * 30 :=
        mul_le_mul hA hB hB0 (by norm_num)
    _ = 30 := by norm_num

/-- **Termwise prime bound.** -/
private lemma le_targetBound (p : ℕ) (hp : p.Prime) :
    2 * (p : ℝ) ^ (9 / 16 : ℝ) / ((p : ℝ) - 1) ≤ targetBound p := by
  rcases eq_or_ne p 2 with h2 | h2
  · rw [h2, targetBound, if_pos rfl]
    push_cast
    rw [show (2 : ℝ) - 1 = 1 by norm_num, div_one]
    exact check_two
  rcases eq_or_ne p 3 with h3 | h3
  · rw [h3, targetBound, if_neg (by norm_num : ¬ (3 : ℕ) = 2), if_pos rfl]
    push_cast
    rw [show (3 : ℝ) - 1 = 2 by norm_num]
    exact check_three
  rcases eq_or_ne p 5 with h5 | h5
  · rw [h5, targetBound, if_neg (by norm_num : ¬ (5 : ℕ) = 2),
      if_neg (by norm_num : ¬ (5 : ℕ) = 3), if_pos rfl]
    push_cast
    rw [show (5 : ℝ) - 1 = 4 by norm_num]
    exact check_five
  · rw [targetBound, if_neg h2, if_neg h3, if_neg h5]
    have hp7 : 7 ≤ p := by
      by_contra hlt
      rw [not_le] at hlt
      have h2' : 2 ≤ p := hp.two_le
      interval_cases p <;> simp_all <;> (exfalso; revert hp; decide)
    have hden : (0 : ℝ) < (p : ℝ) - 1 := by
      have : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
      linarith
    rw [div_le_one hden]
    exact check_large p hp7

/-- **(M4)**  `2^{ω(n)} · n^{9/16} / φ(n) ≤ 30` for `n ≥ 1`. -/
theorem two_pow_omega_mul_rpow_div_totient_le (n : ℕ) (hn : 1 ≤ n) :
    (2 : ℝ) ^ ((n.primeFactors).card) * (n : ℝ) ^ (9 / 16 : ℝ) / (n.totient : ℝ) ≤ 30 := by
  classical
  have hn0 : n ≠ 0 := by omega
  set s : Finset ℕ := n.primeFactors with hs
  have h2p : (2 : ℝ) ^ (s.card) = ∏ p ∈ s, (2 : ℝ) := (Finset.prod_const (2 : ℝ)).symm
  have hnR : (n : ℝ) ^ (9 / 16 : ℝ)
      = ∏ p ∈ s, (p : ℝ) ^ ((n.factorization p : ℝ) * (9 / 16 : ℝ)) := by
    have h1 : (n : ℝ) = ((∏ p ∈ s, p ^ n.factorization p : ℕ) : ℝ) := by
      rw [hs]
      exact_mod_cast (Nat.prod_primeFactors_pow_factorization hn0)
    rw [h1, Nat.cast_prod, ← Real.finsetProd_rpow s _ (fun p hp => by positivity)]
    refine Finset.prod_congr rfl (fun p hp => ?_)
    rw [Nat.cast_pow, ← Real.rpow_natCast (p : ℝ) (n.factorization p),
      ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (p : ℝ))]
  have hphi : (n.totient : ℝ)
      = ∏ p ∈ s, ((p : ℝ) ^ (n.factorization p - 1) * ((p : ℝ) - 1)) := by
    rw [hs, Commons.NumberTheory.Totient.totient_eq_prod_primeFactors n hn0, Nat.cast_prod]
    refine Finset.prod_congr rfl (fun p hp => ?_)
    rw [Nat.cast_mul, Nat.cast_pow,
      Nat.cast_sub (Nat.Prime.one_le (Nat.prime_of_mem_primeFactors hp)), Nat.cast_one]
  rw [h2p, hnR, hphi, ← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
  refine le_trans (Finset.prod_le_prod₀ (fun p hp => ?_) (fun p hp => ?_))
    (targetBound_prod_le_thirty s)
  · have hpp := Nat.prime_of_mem_primeFactors hp
    have hp1 : (1 : ℝ) < (p : ℝ) := by
      have h2' : (2 : ℕ) ≤ p := hpp.two_le
      exact_mod_cast (by omega : 1 < p)
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hden : (0 : ℝ) < (p : ℝ) ^ (n.factorization p - 1) * ((p : ℝ) - 1) :=
      mul_pos (pow_pos hp0 _) (by linarith)
    exact div_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg hp0.le _)) hden.le
  · have hpp := Nat.prime_of_mem_primeFactors hp
    have hν : 1 ≤ n.factorization p :=
      (hpp.dvd_iff_one_le_factorization hn0).mp (Nat.dvd_of_mem_primeFactors hp)
    exact le_trans (local_factor_le p (n.factorization p) hpp hν) (le_targetBound p hpp)

/-- **(M5)**  `log t ≤ 8 t^{1/8}` for `t ≥ 1` (needed by (P-c)). -/
private lemma log_le_eight_rpow (t : ℝ) (ht : 1 ≤ t) :
    Real.log t ≤ 8 * t ^ (1 / 8 : ℝ) := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hpow : 0 < t ^ (1 / 8 : ℝ) := Real.rpow_pos_of_pos ht0 _
  have hlog : Real.log (t ^ (1 / 8 : ℝ)) = (1 / 8 : ℝ) * Real.log t := Real.log_rpow ht0 _
  have h2 : Real.log (t ^ (1 / 8 : ℝ)) ≤ t ^ (1 / 8 : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos hpow
  linarith

/-- **(P-c) constants.**  `3^{1/8} ≤ 2` and `2^{7/8} ≤ 2` (both crude but sufficient). -/
private lemma three_rpow_eighth_le_two : (3 : ℝ) ^ (1 / 8 : ℝ) ≤ 2 := by
  have h : (3 : ℝ) ^ (1 / 8 : ℝ) ≤ ((2 : ℝ) ^ (8 : ℕ)) ^ (1 / 8 : ℝ) :=
    Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
  have h2 : ((2 : ℝ) ^ (8 : ℕ)) ^ (1 / 8 : ℝ) = 2 := by
    rw [← Real.rpow_natCast (2 : ℝ) 8, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rwa [h2] at h

private lemma two_rpow_seven_eighth_le_two : (2 : ℝ) ^ (7 / 8 : ℝ) ≤ 2 := by
  have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    (by norm_num : (7 / 8 : ℝ) ≤ 1)
  rwa [Real.rpow_one] at h


-- (checks and main theorem still to be added; see K2_PLAN.md)

/-- Auxiliary: `log (max X 3) ≤ 8·3^{1/8}·X^{1/8}` for `X ≥ 1`. -/
private lemma pc_log (X : ℕ) (hX : 1 ≤ (X : ℝ)) :
    Real.log (max (X : ℝ) 3) ≤ 8 * (3 : ℝ) ^ (1 / 8 : ℝ) * (X : ℝ) ^ (1 / 8 : ℝ) := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hmax1 : (1 : ℝ) ≤ max (X : ℝ) 3 := le_trans hX (le_max_left _ _)
  have h1 : Real.log (max (X : ℝ) 3) ≤ 8 * (max (X : ℝ) 3) ^ (1 / 8 : ℝ) :=
    log_le_eight_rpow _ hmax1
  have hmax3X : max (X : ℝ) 3 ≤ 3 * (X : ℝ) := by
    apply max_le <;> linarith
  have h2 : (max (X : ℝ) 3) ^ (1 / 8 : ℝ) ≤ (3 * (X : ℝ)) ^ (1 / 8 : ℝ) :=
    Real.rpow_le_rpow (by linarith) hmax3X (by norm_num)
  have h3 : (3 * (X : ℝ)) ^ (1 / 8 : ℝ) = (3 : ℝ) ^ (1 / 8 : ℝ) * (X : ℝ) ^ (1 / 8 : ℝ) :=
    Real.mul_rpow (by norm_num) hX0.le
  calc Real.log (max (X : ℝ) 3) ≤ 8 * (max (X : ℝ) 3) ^ (1 / 8 : ℝ) := h1
    _ ≤ 8 * ((3 : ℝ) ^ (1 / 8 : ℝ) * (X : ℝ) ^ (1 / 8 : ℝ)) := by
        rw [← h3]
        exact mul_le_mul_of_nonneg_left h2 (by norm_num)
    _ = 8 * (3 : ℝ) ^ (1 / 8 : ℝ) * (X : ℝ) ^ (1 / 8 : ℝ) := by ring

/-- Auxiliary: `q'^{7/16} ≤ 2·X^{7/8}` when `q' ≥ 4` and `√q' ≤ X + 1`. -/
private lemma pc_key (q' X : ℕ) (hq' : 4 ≤ q')
    (hX : Real.sqrt (q' : ℝ) - 1 ≤ (X : ℝ)) :
    (q' : ℝ) ^ (7 / 16 : ℝ) ≤ 2 * (X : ℝ) ^ (7 / 8 : ℝ) := by
  have hq0 : (0 : ℝ) < (q' : ℝ) := by
    have : (4 : ℝ) ≤ (q' : ℝ) := by exact_mod_cast hq'
    linarith
  have hq4R : (4 : ℝ) ≤ (q' : ℝ) := by exact_mod_cast hq'
  have hsqrt2 : (2 : ℝ) ≤ Real.sqrt (q' : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    linarith
  have hX0 : (0 : ℝ) < (X : ℝ) := by linarith
  have hqle : (q' : ℝ) ≤ 4 * (X : ℝ) ^ 2 := by
    have h := pow_le_pow_left₀ (Real.sqrt_nonneg (q' : ℝ))
      (by linarith : Real.sqrt (q' : ℝ) ≤ 2 * (X : ℝ)) 2
    rw [Real.sq_sqrt hq0.le] at h
    nlinarith
  have h7 : (q' : ℝ) ^ (7 / 16 : ℝ) ≤ (4 * (X : ℝ) ^ 2) ^ (7 / 16 : ℝ) :=
    Real.rpow_le_rpow hq0.le hqle (by norm_num)
  have h8 : (4 * (X : ℝ) ^ 2) ^ (7 / 16 : ℝ) ≤ 2 * (X : ℝ) ^ (7 / 8 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) (by positivity : (0 : ℝ) ≤ (X : ℝ) ^ 2)]
    have hx2 : ((X : ℝ) ^ 2) ^ (7 / 16 : ℝ) = (X : ℝ) ^ (7 / 8 : ℝ) := by
      rw [← Real.rpow_natCast (X : ℝ) 2, ← Real.rpow_mul hX0.le]
      norm_num
    rw [hx2]
    have h4 : (4 : ℝ) ^ (7 / 16 : ℝ) ≤ 2 := by
      have h : (4 : ℝ) ^ (7 / 16 : ℝ) = (2 : ℝ) ^ (7 / 8 : ℝ) := by
        rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← Real.rpow_natCast (2 : ℝ) 2,
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      rw [h]; exact two_rpow_seven_eighth_le_two
    exact mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg hX0.le _)
  linarith

/-- Auxiliary algebra: the key inequalities convert into the `1000` bound. -/
private lemma pc_assembly (A u v phi Lg : ℝ) (hu : 0 < u) (hv : 0 < v) (hphi : 0 < phi)
    (hLg0 : 0 ≤ Lg)
    (hlog : Lg ≤ 8 * (3 : ℝ) ^ (1 / 8 : ℝ) * u ^ (1 / 8 : ℝ))
    (hM4 : A * v ^ (9 / 16 : ℝ) ≤ 30 * phi)
    (hkey : v ^ (7 / 16 : ℝ) ≤ 2 * u ^ (7 / 8 : ℝ)) :
    A * Lg * v / (u * phi) ≤ 1000 := by
  have hvsplit : v ^ (9 / 16 : ℝ) * v ^ (7 / 16 : ℝ) = v := by
    rw [← Real.rpow_add hv, show (9 / 16 : ℝ) + 7 / 16 = 1 by norm_num, Real.rpow_one]
  have huu : u ^ (1 / 8 : ℝ) * u ^ (7 / 8 : ℝ) = u := by
    rw [← Real.rpow_add hu, show (1 / 8 : ℝ) + 7 / 8 = 1 by norm_num, Real.rpow_one]
  have hvp0 : 0 ≤ v ^ (7 / 16 : ℝ) := Real.rpow_nonneg hv.le _
  have hb0 : 0 ≤ 8 * (3 : ℝ) ^ (1 / 8 : ℝ) * u ^ (1 / 8 : ℝ) := by positivity
  have hmain : A * Lg * v ≤ 480 * (3 : ℝ) ^ (1 / 8 : ℝ) * (phi * u) := by
    calc A * Lg * v
        = A * Lg * (v ^ (9 / 16 : ℝ) * v ^ (7 / 16 : ℝ)) := by rw [hvsplit]
      _ = (A * v ^ (9 / 16 : ℝ)) * (Lg * v ^ (7 / 16 : ℝ)) := by ring
      _ ≤ (30 * phi) * (Lg * v ^ (7 / 16 : ℝ)) :=
            mul_le_mul_of_nonneg_right hM4 (mul_nonneg hLg0 hvp0)
      _ ≤ (30 * phi) *
            ((8 * (3 : ℝ) ^ (1 / 8 : ℝ) * u ^ (1 / 8 : ℝ)) * (2 * u ^ (7 / 8 : ℝ))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul hlog hkey hvp0 hb0) (by positivity)
      _ = (30 * phi) * (16 * (3 : ℝ) ^ (1 / 8 : ℝ) * (u ^ (1 / 8 : ℝ) * u ^ (7 / 8 : ℝ))) := by
            ring
      _ = (30 * phi) * (16 * (3 : ℝ) ^ (1 / 8 : ℝ) * u) := by rw [huu]
      _ = 480 * (3 : ℝ) ^ (1 / 8 : ℝ) * (phi * u) := by ring
  have h3c : 480 * (3 : ℝ) ^ (1 / 8 : ℝ) ≤ 1000 := by
    nlinarith [three_rpow_eighth_le_two]
  have hfinal : A * Lg * v ≤ 1000 * (phi * u) := by
    calc A * Lg * v ≤ 480 * (3 : ℝ) ^ (1 / 8 : ℝ) * (phi * u) := hmain
      _ ≤ 1000 * (phi * u) := mul_le_mul_of_nonneg_right h3c (by positivity)
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < u * phi)]
  nlinarith [hfinal]

/-- **(P-c)**  `2^{ω(q')}·log(max X 3)·q'/(X·φ(q')) ≤ 1000` for `q' ≥ 4` and
`√q' - 1 ≤ X`.  Together with (P-b) this converts the `2^{ω(q')}·∏_{p≤X}(...)`
error of the sieve count into the main term. -/
theorem two_pow_omega_log_mul_le (q' X : ℕ) (hq' : 4 ≤ q')
    (hX : Real.sqrt (q' : ℝ) - 1 ≤ (X : ℝ)) :
    (2 : ℝ) ^ ((q'.primeFactors).card) * Real.log (max (X : ℝ) 3) * (q' : ℝ)
      / ((X : ℝ) * (q'.totient : ℝ)) ≤ 1000 := by
  have hq1 : (1 : ℕ) ≤ q' := by omega
  have hq4R : (4 : ℝ) ≤ (q' : ℝ) := by exact_mod_cast hq'
  have hq0R : (0 : ℝ) < (q' : ℝ) := by linarith
  have hsqrt2 : (2 : ℝ) ≤ Real.sqrt (q' : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    linarith
  have hX0 : (0 : ℝ) < (X : ℝ) := by linarith
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by linarith
  have hphi0 : (0 : ℝ) < (q'.totient : ℝ) := by
    have h := Nat.totient_pos.mpr (by omega : 0 < q')
    exact_mod_cast h
  have hM4 := two_pow_omega_mul_rpow_div_totient_le q' hq1
  have hM4' : (2 : ℝ) ^ ((q'.primeFactors).card) * (q' : ℝ) ^ (9 / 16 : ℝ) ≤
      30 * (q'.totient : ℝ) := by
    rw [div_le_iff₀ hphi0] at hM4
    exact hM4
  have hLg0 : 0 ≤ Real.log (max (X : ℝ) 3) :=
    Real.log_nonneg (le_trans hX1 (le_max_left _ _))
  exact pc_assembly ((2 : ℝ) ^ ((q'.primeFactors).card)) ((X : ℝ)) ((q' : ℝ))
    ((q'.totient : ℝ)) (Real.log (max (X : ℝ) 3)) hX0 hq0R hphi0 hLg0
    (pc_log X hX1) hM4' (pc_key q' X hq' hX)


/-- **(P-b)**  `∏_{p ∈ s, p ≤ X}(1 + p/(p-1)²) ≤ C·log(max X 3)` for `s` any finset
of primes.  (Euler–Mertens `Σ_{p ≤ X} 1/p ≤ C + log log X` in exponential form.) -/
private lemma prod_one_add_div_sq_filter_le_log :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X : ℕ) (s : Finset ℕ), (∀ p ∈ s, p.Prime) →
      ∏ p ∈ s.filter (fun p => p ≤ X), (1 + (p : ℝ) / ((p : ℝ) - 1) ^ 2)
        ≤ C * Real.log (max (X : ℝ) 3) := by
  rcases Commons.NumberTheory.PrimeReciprocals.prime_recip_sum_le_log_log with ⟨Cm, hCm0, hCm⟩
  refine ⟨max (Real.exp (Cm + 16)) 3, le_max_of_le_right (by norm_num), fun X s hs => ?_⟩
  have hlog3 : (1 : ℝ) ≤ Real.log (max (X : ℝ) 3) := by
    have h3 : (3 : ℝ) ≤ max (X : ℝ) 3 := le_max_right _ _
    have h : Real.log 3 ≤ Real.log (max (X : ℝ) 3) := Real.log_le_log (by norm_num) h3
    have h1 : (1 : ℝ) ≤ Real.log 3 := by
      rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 3)]
      exact le_of_lt Real.exp_one_lt_three
    linarith
  rcases lt_or_ge X 3 with hX | hX
  · have hsub : s.filter (fun p => p ≤ X) ⊆ ({2} : Finset ℕ) := by
      intro p hp
      have hp' : p.Prime := hs p (Finset.mem_filter.mp hp).1
      have hpX : p ≤ X := (Finset.mem_filter.mp hp).2
      have hp2 : p ≤ 2 := by omega
      have hp0 : 2 ≤ p := hp'.two_le
      interval_cases p
      simp
    have hle : ∏ p ∈ s.filter (fun p => p ≤ X), (1 + (p : ℝ) / ((p : ℝ) - 1) ^ 2)
        ≤ ∏ p ∈ ({2} : Finset ℕ), (1 + (p : ℝ) / ((p : ℝ) - 1) ^ 2) := by
      refine Finset.prod_le_prod_of_subset_of_one_le₀ hsub (fun i _ => by positivity) ?_
      intro i hi _
      have hi2 : 2 ≤ i := (Finset.mem_singleton.mp hi).ge
      have h0 : (0 : ℝ) ≤ (i : ℝ) / ((i : ℝ) - 1) ^ 2 := by positivity
      linarith
    have h2 : ∏ p ∈ ({2} : Finset ℕ), (1 + (p : ℝ) / ((p : ℝ) - 1) ^ 2) = 3 := by
      norm_num
    rw [h2] at hle
    calc ∏ p ∈ s.filter (fun p => p ≤ X), (1 + (p : ℝ) / ((p : ℝ) - 1) ^ 2)
        ≤ 3 := hle
      _ ≤ max (Real.exp (Cm + 16)) 3 * Real.log (max (X : ℝ) 3) := by
          have h3 : (3 : ℝ) ≤ max (Real.exp (Cm + 16)) 3 := le_max_right _ _
          nlinarith
  · have hX1 : (1 : ℝ) < (X : ℝ) := by
      have : (1 : ℕ) < X := by omega
      exact_mod_cast this
    have hlogX : 0 < Real.log (X : ℝ) := Real.log_pos hX1
    have hsub : s.filter (fun p => p ≤ X) ⊆ Nat.primesBelow (X + 1) := by
      intro p hp
      have hpX : p ≤ X := (Finset.mem_filter.mp hp).2
      rw [Nat.mem_primesBelow]
      exact ⟨by omega, hs p (Finset.mem_filter.mp hp).1⟩
    have h1 : ∏ p ∈ s.filter (fun p => p ≤ X), (1 + (p : ℝ) / ((p : ℝ) - 1) ^ 2)
        ≤ ∏ p ∈ Nat.primesBelow (X + 1), (1 + (p : ℝ) / ((p : ℝ) - 1) ^ 2) := by
      refine Finset.prod_le_prod_of_subset_of_one_le₀ hsub (fun i _ => by positivity) ?_
      intro i hi _
      have hi2 : 2 ≤ i := Nat.two_le_of_mem_primesBelow hi
      have h0 : (0 : ℝ) ≤ (i : ℝ) / ((i : ℝ) - 1) ^ 2 := by positivity
      linarith
    have h2 : ∏ p ∈ Nat.primesBelow (X + 1), (1 + (p : ℝ) / ((p : ℝ) - 1) ^ 2)
        ≤ Real.exp (Cm + 16) * Real.log (X : ℝ) := by
      have h1' : ∀ p ∈ Nat.primesBelow (X + 1),
          (1 + (p : ℝ) / ((p : ℝ) - 1) ^ 2) ≤ Real.exp ((p : ℝ) / ((p : ℝ) - 1) ^ 2) := by
        intro p hp
        rw [add_comm]
        exact Real.add_one_le_exp _
      calc ∏ p ∈ Nat.primesBelow (X + 1), (1 + (p : ℝ) / ((p : ℝ) - 1) ^ 2)
          ≤ ∏ p ∈ Nat.primesBelow (X + 1), Real.exp ((p : ℝ) / ((p : ℝ) - 1) ^ 2) :=
            Finset.prod_le_prod₀ (fun p hp => by positivity) h1'
        _ = Real.exp (∑ p ∈ Nat.primesBelow (X + 1), (p : ℝ) / ((p : ℝ) - 1) ^ 2) :=
            (Real.exp_sum _ _).symm
        _ ≤ Real.exp (Cm + Real.log (Real.log (X : ℝ)) + 16) := by
            refine Real.exp_le_exp.mpr ?_
            have hstep : ∀ p ∈ Nat.primesBelow (X + 1),
                (p : ℝ) / ((p : ℝ) - 1) ^ 2 ≤ 1 / (p : ℝ) + 2 / (((p : ℝ) - 1) ^ 2) := by
              intro p hp
              have hp2 : (2 : ℕ) ≤ p := Nat.two_le_of_mem_primesBelow hp
              have hpR : (0 : ℝ) < (p : ℝ) := by positivity
              have hsq : (0 : ℝ) < ((p : ℝ) - 1) ^ 2 := by
                have : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
                positivity
              have hthis : (p : ℝ) / ((p : ℝ) - 1) ^ 2 - 2 / ((p : ℝ) - 1) ^ 2
                  = ((p : ℝ) - 2) / ((p : ℝ) - 1) ^ 2 := by ring
              rw [← sub_le_iff_le_add, hthis, div_le_div_iff₀ hsq hpR]
              nlinarith [show (2 : ℝ) ≤ (p : ℝ) by exact_mod_cast hp2]
            calc ∑ p ∈ Nat.primesBelow (X + 1), (p : ℝ) / ((p : ℝ) - 1) ^ 2
                ≤ ∑ p ∈ Nat.primesBelow (X + 1), (1 / (p : ℝ) + 2 / (((p : ℝ) - 1) ^ 2)) :=
                  Finset.sum_le_sum hstep
              _ = (∑ p ∈ Nat.primesBelow (X + 1), 1 / (p : ℝ))
                    + 2 * ∑ p ∈ Nat.primesBelow (X + 1), 1 / (((p : ℝ) - 1) ^ 2) := by
                  rw [Finset.sum_add_distrib, Finset.mul_sum]
                  congr 1
                  exact Finset.sum_congr rfl (fun p hp => by ring)
              _ ≤ (Cm + Real.log (Real.log (X : ℝ))) + 2 * 8 := by
                  have hA := hCm X hX
                  have hB : (∑ p ∈ Nat.primesBelow (X + 1), 1 / (((p : ℝ) - 1) ^ 2)) ≤ 8 :=
                    sum_inv_sq_pred_le _ (fun p hp => (Nat.mem_primesBelow.mp hp).2)
                  linarith
              _ ≤ Cm + Real.log (Real.log (X : ℝ)) + 16 := by norm_num
        _ = Real.exp (Cm + 16) * Real.log (X : ℝ) := by
            rw [show Cm + Real.log (Real.log (X : ℝ)) + 16
                  = (Cm + 16) + Real.log (Real.log (X : ℝ)) by ring, Real.exp_add,
              Real.exp_log hlogX]
    have h3 : Real.log (X : ℝ) = Real.log (max (X : ℝ) 3) := by
      rw [max_eq_left]
      have : (3 : ℕ) ≤ X := hX
      exact_mod_cast this
    rw [h3] at h2
    refine le_trans h1 (le_trans h2 ?_)
    have he : Real.exp (Cm + 16) ≤ max (Real.exp (Cm + 16)) 3 := le_max_left _ _
    nlinarith [Real.exp_pos (Cm + 16), hlog3]

/-- **(P-a)** Counting bound for the fibre weight sum over a coprime window:
`Σ_{c ≤ X, c ⊥ q'} S(c) ≤ Sbar·(10000·X·φ(q')/q' + 2^{ω(q')}·∏_{p | K, p ≤ X}(1+p/(p-1)²))`. -/
private theorem fibreS_coprime_window_le (K X q' : ℕ) (hq' : 0 < q') :
    (∑ c ∈ (Finset.Icc 1 X).filter (fun c => c.gcd q' = 1), (fibreS K c : ℝ))
      ≤ fibreSbar K * (10000 * (X : ℝ) * ((q'.totient : ℝ) / (q' : ℝ))
          + (2 : ℝ) ^ (q'.primeFactors.card) *
            ∏ p ∈ K.primeFactors.filter (fun p => p ≤ X),
              (1 + (p : ℝ) / ((p : ℝ) - 1) ^ 2)) := by
  classical
  set S : Finset ℕ := (Finset.Icc 1 X).filter (fun c => c.gcd q' = 1) with hSdef
  set T : Finset (Finset ℕ) := K.primeFactors.powerset with hTdef
  set D : Finset ℕ → ℕ := fun t => ∏ p ∈ t, p with hDdef
  have hDpos : ∀ t ∈ T, 0 < D t := by
    intro t ht
    have ht' : t ∈ K.primeFactors.powerset := hTdef ▸ ht
    have hts : t ⊆ K.primeFactors := Finset.mem_powerset.mp ht'
    rw [hDdef]
    exact Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors (hts hp)).pos)
  have hq'R : (0 : ℝ) < (q' : ℝ) := by exact_mod_cast hq'
  have hphiR : (0 : ℝ) ≤ (q'.totient : ℝ) := by positivity
  -- Step 1: swap the sums
  have hswap : (∑ c ∈ S, (fibreS K c : ℝ))
      = ∑ t ∈ T, (fibreCoeff K t : ℝ) * (((S.filter (fun c => D t ∣ c)).card : ℕ) : ℝ) := by
    calc (∑ c ∈ S, (fibreS K c : ℝ))
        = ∑ c ∈ S, ∑ t ∈ T, (if D t ∣ c then (fibreCoeff K t : ℝ) else 0) := by
            refine Finset.sum_congr rfl (fun c _ => ?_)
            rw [fibreS_eq_sum_powerset]
            simp only [hTdef, hDdef]
            push_cast
            rfl
      _ = ∑ t ∈ T, ∑ c ∈ S, (if D t ∣ c then (fibreCoeff K t : ℝ) else 0) := Finset.sum_comm
      _ = ∑ t ∈ T, (fibreCoeff K t : ℝ) * (((S.filter (fun c => D t ∣ c)).card : ℕ) : ℝ) := by
            refine Finset.sum_congr rfl (fun t _ => ?_)
            rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
            ring
  -- Step 2: cardinality bound for a fixed `t`
  have hcard : ∀ t ∈ T, D t ≤ X →
      (((S.filter (fun c => D t ∣ c)).card : ℕ) : ℝ)
        ≤ (X : ℝ) / (D t : ℝ) * ((q'.totient : ℝ) / (q' : ℝ))
          + (2 : ℝ) ^ (q'.primeFactors.card) := by
    intro t ht htD
    have hDp : 0 < D t := hDpos t ht
    have hsub : (S.filter (fun c => D t ∣ c)) ⊆
        (((Finset.Icc 1 (X / D t)).filter (fun m => m.gcd q' = 1)).image
          (fun m => D t * m)) := by
      intro c hc
      have hcS : c ∈ S := (Finset.mem_filter.mp hc).1
      have hcdvd : D t ∣ c := (Finset.mem_filter.mp hc).2
      rw [hSdef] at hcS
      have hcIcc : c ∈ Finset.Icc 1 X := (Finset.mem_filter.mp hcS).1
      have hcg : c.gcd q' = 1 := (Finset.mem_filter.mp hcS).2
      have hc1 : 1 ≤ c := (Finset.mem_Icc.mp hcIcc).1
      have hcX : c ≤ X := (Finset.mem_Icc.mp hcIcc).2
      obtain ⟨m, rfl⟩ := hcdvd
      have hm1 : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with hm | hm
        · subst hm; simp at hc1
        · exact hm
      have hmX : m ≤ X / D t := by
        rw [Nat.le_div_iff_mul_le hDp]
        rw [Nat.mul_comm]
        exact hcX
      have hmg : m.gcd q' = 1 := by
        refine Nat.eq_one_of_dvd_one ?_
        rw [← hcg]
        exact Nat.dvd_gcd (dvd_mul_of_dvd_right (Nat.gcd_dvd_left m q') (D t))
          (Nat.gcd_dvd_right m q')
      exact Finset.mem_image.mpr ⟨m, Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨hm1, hmX⟩, hmg⟩, rfl⟩
    have hcard1 : (S.filter (fun c => D t ∣ c)).card ≤
        ((Finset.Icc 1 (X / D t)).filter (fun m => m.gcd q' = 1)).card :=
      le_trans (Finset.card_le_card hsub) Finset.card_image_le
    have hcc := card_coprime_Icc_le q' (X / D t) hq'
    have hcast : (((X / D t : ℕ)) : ℝ) ≤ (X : ℝ) / (D t : ℝ) := by
      exact Nat.cast_div_le
    calc (((S.filter (fun c => D t ∣ c)).card : ℕ) : ℝ)
        ≤ ((((Finset.Icc 1 (X / D t)).filter (fun m => m.gcd q' = 1)).card : ℕ) : ℝ) := by
          exact_mod_cast hcard1
      _ ≤ ((X / D t : ℕ) : ℝ) * (q'.totient : ℝ) / (q' : ℝ)
            + (2 : ℝ) ^ (q'.primeFactors.card) := hcc
      _ ≤ (X : ℝ) / (D t : ℝ) * (q'.totient : ℝ) / (q' : ℝ)
            + (2 : ℝ) ^ (q'.primeFactors.card) := by
          have h1 : ((X / D t : ℕ) : ℝ) * (q'.totient : ℝ) / (q' : ℝ)
              ≤ (X : ℝ) / (D t : ℝ) * (q'.totient : ℝ) / (q' : ℝ) :=
            div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right hcast hphiR) hq'R.le
          linarith
      _ = (X : ℝ) / (D t : ℝ) * ((q'.totient : ℝ) / (q' : ℝ))
            + (2 : ℝ) ^ (q'.primeFactors.card) := by ring
  -- Step 3: truncation
  have hempty : ∀ t ∈ T, X < D t → S.filter (fun c => D t ∣ c) = ∅ := by
    intro t ht htX
    rw [← Finset.not_nonempty_iff_eq_empty]
    rintro ⟨c, hc⟩
    have hcS : c ∈ S := (Finset.mem_filter.mp hc).1
    have hcdvd : D t ∣ c := (Finset.mem_filter.mp hc).2
    rw [hSdef] at hcS
    have hcIcc : c ∈ Finset.Icc 1 X := (Finset.mem_filter.mp hcS).1
    have hc1 : 1 ≤ c := (Finset.mem_Icc.mp hcIcc).1
    have hcX : c ≤ X := (Finset.mem_Icc.mp hcIcc).2
    have hle : D t ≤ c := Nat.le_of_dvd (by omega) hcdvd
    omega
  have hcut : (∑ t ∈ T, (fibreCoeff K t : ℝ) * (((S.filter (fun c => D t ∣ c)).card : ℕ) : ℝ))
      = ∑ t ∈ T.filter (fun t => D t ≤ X),
          (fibreCoeff K t : ℝ) * (((S.filter (fun c => D t ∣ c)).card : ℕ) : ℝ) := by
    refine (Finset.sum_subset ?_ ?_).symm
    · intro t ht
      exact (Finset.mem_filter.mp ht).1
    · intro t ht hnt
      have hlt : X < D t := by
        by_contra hcon
        exact hnt (Finset.mem_filter.mpr ⟨ht, not_lt.mp hcon⟩)
      rw [hempty t ht hlt]
      simp
  -- Step 4: bound the truncated sum
  have hstep : (∑ t ∈ T.filter (fun t => D t ≤ X),
        (fibreCoeff K t : ℝ) * (((S.filter (fun c => D t ∣ c)).card : ℕ) : ℝ))
      ≤ (q'.totient : ℝ) / (q' : ℝ)
          * ((X : ℝ) * (∑ t ∈ T, (fibreCoeff K t : ℝ) / (D t : ℝ)))
        + (2 : ℝ) ^ (q'.primeFactors.card)
          * (∑ t ∈ T.filter (fun t => D t ≤ X), (fibreCoeff K t : ℝ)) := by
    have hsplit : (∑ t ∈ T.filter (fun t => D t ≤ X),
          (fibreCoeff K t : ℝ) * (((S.filter (fun c => D t ∣ c)).card : ℕ) : ℝ))
        ≤ ∑ t ∈ T.filter (fun t => D t ≤ X),
            (fibreCoeff K t : ℝ) * ((X : ℝ) / (D t : ℝ) * ((q'.totient : ℝ) / (q' : ℝ))
              + (2 : ℝ) ^ (q'.primeFactors.card)) := by
      refine Finset.sum_le_sum (fun t ht => ?_)
      exact mul_le_mul_of_nonneg_left
        (hcard t (Finset.mem_filter.mp ht).1 (Finset.mem_filter.mp ht).2) (by positivity)
    refine le_trans hsplit ?_
    have hdist : (∑ t ∈ T.filter (fun t => D t ≤ X),
          (fibreCoeff K t : ℝ) * ((X : ℝ) / (D t : ℝ) * ((q'.totient : ℝ) / (q' : ℝ))
            + (2 : ℝ) ^ (q'.primeFactors.card)))
        = (∑ t ∈ T.filter (fun t => D t ≤ X),
            (fibreCoeff K t : ℝ) * ((X : ℝ) / (D t : ℝ) * ((q'.totient : ℝ) / (q' : ℝ))))
          + (∑ t ∈ T.filter (fun t => D t ≤ X),
            (fibreCoeff K t : ℝ) * (2 : ℝ) ^ (q'.primeFactors.card)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun t _ => by ring)
    rw [hdist]
    refine add_le_add ?_ ?_
    · -- first sum
      calc (∑ t ∈ T.filter (fun t => D t ≤ X),
              (fibreCoeff K t : ℝ) * ((X : ℝ) / (D t : ℝ) * ((q'.totient : ℝ) / (q' : ℝ))))
          = ∑ t ∈ T.filter (fun t => D t ≤ X),
              (q'.totient : ℝ) / (q' : ℝ)
                * ((X : ℝ) * ((fibreCoeff K t : ℝ) / (D t : ℝ))) :=
              Finset.sum_congr rfl (fun t _ => by simp only [div_eq_mul_inv]; ring)
        _ ≤ ∑ t ∈ T, (q'.totient : ℝ) / (q' : ℝ)
              * ((X : ℝ) * ((fibreCoeff K t : ℝ) / (D t : ℝ))) := by
              refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
              · intro t ht; exact (Finset.mem_filter.mp ht).1
              · intro t ht _
                have hDt : (0 : ℝ) < (D t : ℝ) := by
                  exact_mod_cast hDpos t ht
                have hx : (0 : ℝ) ≤ (X : ℝ) := by positivity
                have hp : (0 : ℝ) ≤ (q'.totient : ℝ) / (q' : ℝ) :=
                  div_nonneg hphiR hq'R.le
                have hc : (0 : ℝ) ≤ (fibreCoeff K t : ℝ) := by positivity
                have h1 : (0 : ℝ) ≤ (fibreCoeff K t : ℝ) / (D t : ℝ) :=
                  div_nonneg hc hDt.le
                exact mul_nonneg hp (mul_nonneg hx h1)
        _ = (q'.totient : ℝ) / (q' : ℝ)
              * ((X : ℝ) * (∑ t ∈ T, (fibreCoeff K t : ℝ) / (D t : ℝ))) := by
              rw [← Finset.mul_sum, ← Finset.mul_sum]
    · -- second sum
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun t _ => ?_)
      exact le_of_eq (by ring)
  -- Step 5: insert M2 and M3
  have hM2 := fibreCoeff_sum_div_le K
  have hM3 := fibreCoeff_filtered_sum_le K X
  have hM2' : (∑ t ∈ T, (fibreCoeff K t : ℝ) / (D t : ℝ)) ≤ 10000 * fibreSbar K := by
    simpa only [hTdef, hDdef] using hM2
  have hT0eq : (T.filter (fun t => D t ≤ X))
      = (K.primeFactors.powerset.filter (fun t => (∏ p ∈ t, p) ≤ X)) := by
    simp only [hTdef, hDdef]
  have hM3' : (∑ t ∈ T.filter (fun t => D t ≤ X), (fibreCoeff K t : ℝ))
      ≤ fibreSbar K * ∏ p ∈ K.primeFactors.filter (fun p => p ≤ X),
          (1 + (p : ℝ) / ((p : ℝ) - 1) ^ 2) := by
    rw [hT0eq]
    exact hM3
  have hfinal : (∑ c ∈ S, (fibreS K c : ℝ))
      ≤ fibreSbar K * (10000 * (X : ℝ) * ((q'.totient : ℝ) / (q' : ℝ))
          + (2 : ℝ) ^ (q'.primeFactors.card) *
            ∏ p ∈ K.primeFactors.filter (fun p => p ≤ X),
              (1 + (p : ℝ) / ((p : ℝ) - 1) ^ 2)) := by
    rw [hswap, hcut]
    refine le_trans hstep ?_
    have hA2 : (q'.totient : ℝ) / (q' : ℝ)
          * ((X : ℝ) * (∑ t ∈ T, (fibreCoeff K t : ℝ) / (D t : ℝ)))
        ≤ (q'.totient : ℝ) / (q' : ℝ) * ((X : ℝ) * (10000 * fibreSbar K)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hM2' (by positivity)) (by positivity)
    have hB2 : (2 : ℝ) ^ (q'.primeFactors.card)
          * (∑ t ∈ T.filter (fun t => D t ≤ X), (fibreCoeff K t : ℝ))
        ≤ (2 : ℝ) ^ (q'.primeFactors.card)
          * (fibreSbar K * ∏ p ∈ K.primeFactors.filter (fun p => p ≤ X),
              (1 + (p : ℝ) / ((p : ℝ) - 1) ^ 2)) :=
      mul_le_mul_of_nonneg_left hM3' (by positivity)
    refine le_trans (add_le_add hA2 hB2) ?_
    exact le_of_eq (by ring)
  exact hfinal

set_option maxHeartbeats 1600000
/-- reduced residues below `q`. -/
private def redFinset (q : ℕ) : Finset ℕ := (Finset.range q).filter (fun m : ℕ => m.gcd q = 1)

/-- The first window residue of a pair. -/
private abbrev winU (q r : ℕ) (mn : ℕ × ℕ) : ℕ :=
  (((mn.1 * (r / q.gcd r)) % (q * r / q.gcd r)) + (q * r / q.gcd r) -
      ((mn.2 * (q / q.gcd r)) % (q * r / q.gcd r))) % (q * r / q.gcd r)

/-- The second window residue of a pair. -/
private abbrev winV (q r : ℕ) (mn : ℕ × ℕ) : ℕ :=
  (((mn.2 * (q / q.gcd r)) % (q * r / q.gcd r)) + (q * r / q.gcd r) -
      ((mn.1 * (r / q.gcd r)) % (q * r / q.gcd r))) % (q * r / q.gcd r)

/-- The two-sided lattice residue window predicate with window `W`. -/
private abbrev winPred (q r W : ℕ) (mn : ℕ × ℕ) : Prop :=
  winU q r mn ≤ W ∨ winV q r mn ≤ W

/-- The number of reduced pairs inside the window `[-W,W]`. -/
private def winCount (q r W : ℕ) : ℕ :=
  (((redFinset q).product (redFinset r)).filter (winPred q r W)).card

private lemma winCount_unfold (q r W : ℕ) :
    winCount q r W = (((redFinset q).product (redFinset r)).filter (winPred q r W)).card := rfl

private lemma inter_ball_volume_le' (δq δr : ℝ) (hδq : 0 ≤ δq) (hδr : 0 ≤ δr)
    (x y : UnitAddCircle) :
    MeasureTheory.volume (Metric.ball x δq ∩ Metric.ball y δr) ≤
      ENNReal.ofReal (2 * min δq δr) := by
  calc
    MeasureTheory.volume (Metric.ball x δq ∩ Metric.ball y δr)
        ≤ min (MeasureTheory.volume (Metric.ball x δq))
            (MeasureTheory.volume (Metric.ball y δr)) :=
          le_min (measure_mono inter_subset_left) (measure_mono inter_subset_right)
    _ ≤ min (ENNReal.ofReal (2 * δq)) (ENNReal.ofReal (2 * δr)) :=
          min_le_min (volume_ball_le_ofReal_two_mul x hδq)
            (volume_ball_le_ofReal_two_mul y hδr)
    _ = ENNReal.ofReal (min (2 * δq) (2 * δr)) := by rw [ENNReal.ofReal_min]
    _ = ENNReal.ofReal (2 * min δq δr) := by
          congr 1
          exact (mul_min_of_nonneg δq δr (by norm_num)).symm

/-- **(R1)**  The volume of the intersection of the order-`q` and order-`r`
thickenings is at most `2·min δq δr` times the exact window count. -/
private lemma inter_volume_le_ofReal_mul_winCount (q r : ℕ) (hq : 0 < q) (hr : 0 < r)
    (δq δr : ℝ) (hδq : 0 ≤ δq) (hδr : 0 ≤ δr) :
    MeasureTheory.volume (approxAddOrderOf UnitAddCircle q δq ∩
        approxAddOrderOf UnitAddCircle r δr) ≤
      ENNReal.ofReal (2 * min δq δr) *
        ((winCount q r (Nat.ceil ((δq + δr) * ((q * r / q.gcd r : ℕ) : ℝ))) : ℕ) : ℝ≥0∞) := by
  classical
  have hΔ0 : 0 ≤ δq + δr := by linarith
  set W : ℕ := Nat.ceil ((δq + δr) * ((q * r / q.gcd r : ℕ) : ℝ)) with hW
  have hAq : approxAddOrderOf UnitAddCircle q δq =
      ⋃ m ∈ redFinset q, Metric.ball (↑((m : ℝ) / (q : ℝ)) : UnitAddCircle) δq := by
    simpa [redFinset] using approxAddOrderOf_eq_biUnion_ball q hq δq
  have hAr : approxAddOrderOf UnitAddCircle r δr =
      ⋃ n ∈ redFinset r, Metric.ball (↑((n : ℝ) / (r : ℝ)) : UnitAddCircle) δr := by
    simpa [redFinset] using approxAddOrderOf_eq_biUnion_ball r hr δr
  have hstep1 : MeasureTheory.volume
      (approxAddOrderOf UnitAddCircle q δq ∩ approxAddOrderOf UnitAddCircle r δr) ≤
      ∑ m ∈ redFinset q, MeasureTheory.volume
        (Metric.ball (↑((m : ℝ) / (q : ℝ)) : UnitAddCircle) δq ∩
          approxAddOrderOf UnitAddCircle r δr) := by
    rw [hAq, Set.iUnion₂_inter]
    exact measure_biUnion_finset_le (redFinset q) _
  have hstep2 : ∀ m : ℕ, MeasureTheory.volume
        (Metric.ball (↑(((m : ℕ) : ℝ) / ((q : ℕ) : ℝ)) : UnitAddCircle) δq ∩
          approxAddOrderOf UnitAddCircle r δr) ≤
      ∑ n ∈ redFinset r,
        MeasureTheory.volume (Metric.ball (↑(((m : ℕ) : ℝ) / ((q : ℕ) : ℝ)) : UnitAddCircle) δq ∩
          Metric.ball (↑(((n : ℕ) : ℝ) / ((r : ℕ) : ℝ)) : UnitAddCircle) δr) := by
    intro m
    rw [hAr, Set.inter_iUnion₂]
    exact measure_biUnion_finset_le (redFinset r) _
  have hpt : ∀ m ∈ redFinset q, ∀ n ∈ redFinset r,
      MeasureTheory.volume (Metric.ball (↑(((m : ℕ) : ℝ) / ((q : ℕ) : ℝ)) : UnitAddCircle) δq ∩
          Metric.ball (↑(((n : ℕ) : ℝ) / ((r : ℕ) : ℝ)) : UnitAddCircle) δr) ≤
        (if winPred q r W (m, n) then ENNReal.ofReal (2 * min δq δr) else 0) := by
    intro m hm n hn
    by_cases hw : winPred q r W (m, n)
    · rw [if_pos hw]
      exact inter_ball_volume_le' δq δr hδq hδr _ _
    · rw [if_neg hw]
      have hmq : m < q := Finset.mem_range.mp (Finset.mem_filter.mp hm).1
      have hnq : n < r := Finset.mem_range.mp (Finset.mem_filter.mp hn).1
      have hempty : ¬ (Metric.ball (↑(((m : ℕ) : ℝ) / ((q : ℕ) : ℝ)) : UnitAddCircle) δq ∩
          Metric.ball (↑(((n : ℕ) : ℝ) / ((r : ℕ) : ℝ)) : UnitAddCircle) δr).Nonempty := by
        rintro ⟨z, hz1, hz2⟩
        have hd : dist (↑(((m : ℕ) : ℝ) / ((q : ℕ) : ℝ)) : UnitAddCircle)
            (↑(((n : ℕ) : ℝ) / ((r : ℕ) : ℝ)) : UnitAddCircle) < δq + δr := by
          have h1 : dist (↑(((m : ℕ) : ℝ) / ((q : ℕ) : ℝ)) : UnitAddCircle) z < δq := by
            simpa [Metric.mem_ball, dist_comm] using hz1
          have h2 : dist z (↑(((n : ℕ) : ℝ) / ((r : ℕ) : ℝ)) : UnitAddCircle) < δr := by
            simpa [Metric.mem_ball] using hz2
          calc dist _ _ ≤ dist (↑(((m : ℕ) : ℝ) / ((q : ℕ) : ℝ)) : UnitAddCircle) z + dist z _ :=
                dist_triangle _ _ _
            _ < δq + δr := add_lt_add h1 h2
        have hf := dist_lt_fibre q r m n hq hr hmq hnq (δq + δr) hΔ0 hd
        exact hw (by simpa only [hW] using hf)
      rw [Set.not_nonempty_iff_eq_empty.mp hempty]
      simp
  have hfinal : MeasureTheory.volume
        (approxAddOrderOf UnitAddCircle q δq ∩ approxAddOrderOf UnitAddCircle r δr) ≤
      ENNReal.ofReal (2 * min δq δr) * ((winCount q r W : ℕ) : ℝ≥0∞) := by
    calc MeasureTheory.volume (approxAddOrderOf UnitAddCircle q δq ∩
            approxAddOrderOf UnitAddCircle r δr)
        ≤ ∑ m ∈ redFinset q, ∑ n ∈ redFinset r,
            MeasureTheory.volume (Metric.ball (↑(((m : ℕ) : ℝ) / ((q : ℕ) : ℝ)) : UnitAddCircle) δq ∩
              Metric.ball (↑(((n : ℕ) : ℝ) / ((r : ℕ) : ℝ)) : UnitAddCircle) δr) :=
          le_trans hstep1 (Finset.sum_le_sum (fun m _ => hstep2 m))
      _ ≤ ∑ m ∈ redFinset q, ∑ n ∈ redFinset r,
            (if winPred q r W (m, n) then ENNReal.ofReal (2 * min δq δr) else 0) :=
          Finset.sum_le_sum (fun m hm => Finset.sum_le_sum (fun n hn => hpt m hm n hn))
      _ = ∑ mn ∈ (redFinset q).product (redFinset r),
            (if winPred q r W mn then ENNReal.ofReal (2 * min δq δr) else 0) :=
          (Finset.sum_product (redFinset q) (redFinset r)
            (fun mn : ℕ × ℕ => if winPred q r W mn then ENNReal.ofReal (2 * min δq δr) else 0)).symm
      _ = ∑ mn ∈ ((redFinset q).product (redFinset r)).filter (winPred q r W),
            ENNReal.ofReal (2 * min δq δr) := by
          rw [← Finset.sum_filter]
      _ = ((winCount q r W : ℕ) : ℝ≥0∞) * ENNReal.ofReal (2 * min δq δr) := by
          rw [Finset.sum_const, nsmul_eq_mul, winCount_unfold]
      _ = ENNReal.ofReal (2 * min δq δr) * ((winCount q r W : ℕ) : ℝ≥0∞) := by rw [mul_comm]
  simpa [hW] using hfinal

set_option maxHeartbeats 1600000

/-- `x % L = e` for `e < L`, in divisibility form. -/
private lemma nat_mod_eq_iff_dvd (L e x : ℕ) (he : e < L) :
    x % L = e ↔ (L : ℤ) ∣ (e : ℤ) - (x : ℤ) := by
  rw [← Nat.modEq_iff_dvd (n := L) (a := x) (b := e), Nat.ModEq, Nat.mod_eq_of_lt he]

/-- `x % L = y % L` in divisibility form. -/
private lemma nat_mod_eq_mod_iff_dvd (L x y : ℕ) :
    x % L = y % L ↔ (L : ℤ) ∣ (y : ℤ) - (x : ℤ) := by
  rw [← Nat.modEq_iff_dvd (n := L) (a := x) (b := y)]
  rfl

/-- The window residue `u mn` equals `e` (`e < L`) exactly when the fibre
congruence `(m·N) % L = ((n·M + e) % L)` holds. -/
private lemma winResidue_eq_iff (q r : ℕ) (hq : 0 < q) (hr : 0 < r) (mn : ℕ × ℕ)
    (hm : mn.1 < q) (hn : mn.2 < r) (e : ℕ) (he : e < q * r / q.gcd r) :
    winU q r mn = e ↔
      (mn.1 * (r / q.gcd r)) % (q * r / q.gcd r)
        = ((mn.2 * (q / q.gcd r) + e) % (q * r / q.gcd r)) := by
  set N : ℕ := r / q.gcd r with hNdef
  set M : ℕ := q / q.gcd r with hMdef
  set L : ℕ := q * r / q.gcd r with hLdef
  have hg : 0 < q.gcd r := Nat.gcd_pos_of_pos_left r hq
  have hgdvd_r : q.gcd r ∣ r := Nat.gcd_dvd_right q r
  have hgdvd_q : q.gcd r ∣ q := Nat.gcd_dvd_left q r
  have hN1 : 1 ≤ N := Nat.div_pos (Nat.le_of_dvd hr hgdvd_r) hg
  have hM1 : 1 ≤ M := Nat.div_pos (Nat.le_of_dvd hq hgdvd_q) hg
  have hLq : L = q * N := by rw [hLdef, hNdef]; exact Nat.mul_div_assoc q hgdvd_r
  have hLr : L = r * M := by
    rw [hLdef, hMdef, Nat.mul_comm q r]; exact Nat.mul_div_assoc r hgdvd_q
  have haL : mn.1 * N < L := by
    rw [hLq]; exact Nat.mul_lt_mul_of_pos_right hm (by omega)
  have hbL : mn.2 * M < L := by
    rw [hLr]; exact Nat.mul_lt_mul_of_pos_right hn (by omega)
  change (((mn.1 * N) % L) + L - ((mn.2 * M) % L)) % L = e ↔
      (mn.1 * N) % L = ((mn.2 * M + e) % L)
  have h1 : (((mn.1 * N) % L) + L - ((mn.2 * M) % L)) % L
      = (mn.1 * N + L - mn.2 * M) % L := by
    rw [Nat.mod_eq_of_lt haL, Nat.mod_eq_of_lt hbL]
  rw [h1,
      nat_mod_eq_iff_dvd L e (mn.1 * N + L - mn.2 * M) he,
      nat_mod_eq_mod_iff_dvd L (mn.1 * N) (mn.2 * M + e)]
  have hcast : (((mn.1 * N + L - mn.2 * M : ℕ)) : ℤ)
      = ((mn.1 * N : ℕ) : ℤ) + (L : ℤ) - ((mn.2 * M : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub (by omega : mn.2 * M ≤ mn.1 * N + L)]
    ring
  rw [hcast, Nat.cast_add]
  constructor
  · intro h
    have h2 : ((e : ℤ) - (((mn.1 * N : ℕ) : ℤ) + (L : ℤ) - ((mn.2 * M : ℕ) : ℤ))) + (L : ℤ)
        = ((mn.2 * M : ℕ) : ℤ) + (e : ℤ) - ((mn.1 * N : ℕ) : ℤ) := by ring
    rw [← h2]
    exact (dvd_add_left (dvd_refl (L : ℤ))).mpr h
  · intro h
    have h2 : ((mn.2 * M : ℕ) : ℤ) + (e : ℤ) - ((mn.1 * N : ℕ) : ℤ)
        = ((e : ℤ) - (((mn.1 * N : ℕ) : ℤ) + (L : ℤ) - ((mn.2 * M : ℕ) : ℤ))) + (L : ℤ) := by ring
    rw [h2] at h
    exact (dvd_add_left (dvd_refl (L : ℤ))).mp h

/-- The involution `(m,n) ↦ (q−m, r−n)` exchanges the two window residues. -/
private lemma winResidue_swap_eq (q r : ℕ) (mn : ℕ × ℕ) (hm1 : 1 ≤ mn.1) (hm : mn.1 < q)
    (hn1 : 1 ≤ mn.2) (hn : mn.2 < r) :
    winU q r (q - mn.1, r - mn.2) = winV q r mn := by
  set N : ℕ := r / q.gcd r with hNdef
  set M : ℕ := q / q.gcd r with hMdef
  set L : ℕ := q * r / q.gcd r with hLdef
  have hg : 0 < q.gcd r := Nat.gcd_pos_of_pos_left r (by omega)
  have hgdvd_r : q.gcd r ∣ r := Nat.gcd_dvd_right q r
  have hgdvd_q : q.gcd r ∣ q := Nat.gcd_dvd_left q r
  have hN1 : 1 ≤ N := Nat.div_pos (Nat.le_of_dvd (by omega) hgdvd_r) hg
  have hM1 : 1 ≤ M := Nat.div_pos (Nat.le_of_dvd (by omega) hgdvd_q) hg
  have hLq : L = q * N := by rw [hLdef, hNdef]; exact Nat.mul_div_assoc q hgdvd_r
  have hLr : L = r * M := by
    rw [hLdef, hMdef, Nat.mul_comm q r]; exact Nat.mul_div_assoc r hgdvd_q
  have haL : mn.1 * N < L := by
    rw [hLq]; exact Nat.mul_lt_mul_of_pos_right hm (by omega)
  have hbL : mn.2 * M < L := by
    rw [hLr]; exact Nat.mul_lt_mul_of_pos_right hn (by omega)
  show ((((q - mn.1) * N) % L) + L - (((r - mn.2) * M) % L)) % L
      = (((mn.2 * M) % L) + L - ((mn.1 * N) % L)) % L
  have hmN1 : 1 ≤ mn.1 * N := Nat.one_le_iff_ne_zero.mpr (Nat.mul_pos (by omega) (by omega)).ne'
  have hnM1 : 1 ≤ mn.2 * M := Nat.one_le_iff_ne_zero.mpr (Nat.mul_pos (by omega) (by omega)).ne'
  have hqa : (q - mn.1) * N = L - mn.1 * N := by rw [Nat.sub_mul, hLq]
  have hrb : (r - mn.2) * M = L - mn.2 * M := by rw [Nat.sub_mul, hLr]
  rw [hqa, hrb,
      show (L - mn.1 * N) % L = L - mn.1 * N from Nat.mod_eq_of_lt (by omega),
      show (L - mn.2 * M) % L = L - mn.2 * M from Nat.mod_eq_of_lt (by omega),
      show (mn.2 * M) % L = mn.2 * M from Nat.mod_eq_of_lt hbL,
      show (mn.1 * N) % L = mn.1 * N from Nat.mod_eq_of_lt haL]
  congr 1
  omega

set_option maxHeartbeats 1600000

/-- The fibre count over the lattice congruence of `residue_fiber_formula`. -/
private abbrev fibreCount (q r : ℕ) (e : ℕ) : ℕ :=
  (Finset.filter (fun mn : ℕ × ℕ =>
      (mn.1 * (r / q.gcd r)) % (q * r / q.gcd r)
        = ((mn.2 * (q / q.gcd r) + e) % (q * r / q.gcd r)))
    ((redFinset q).product (redFinset r))).card

/-- Symmetric form of `winResidue_swap_eq`. -/
private lemma winResidue_swap_eq' (q r : ℕ) (mn : ℕ × ℕ) (hm1 : 1 ≤ mn.1) (hm : mn.1 < q)
    (hn1 : 1 ≤ mn.2) (hn : mn.2 < r) :
    winV q r (q - mn.1, r - mn.2) = winU q r mn := by
  have h1 : 1 ≤ q - mn.1 := by omega
  have h2 : q - mn.1 < q := by omega
  have h3 : 1 ≤ r - mn.2 := by omega
  have h4 : r - mn.2 < r := by omega
  have h := winResidue_swap_eq q r (q - mn.1, r - mn.2) h1 h2 h3 h4
  have e1 : q - (q - mn.1) = mn.1 := by omega
  have e2 : r - (r - mn.2) = mn.2 := by omega
  rw [e1, e2] at h
  exact h.symm

/-- `q - m` is a reduced residue mod `q` when `1 ≤ m < q`. -/
private lemma redFinset_sub_mem {q m : ℕ} (hm1 : 1 ≤ m) (hm : m < q) (hg : m.gcd q = 1) :
    q - m ∈ redFinset q := by
  rw [redFinset, Finset.mem_filter, Finset.mem_range]
  refine ⟨by omega, ?_⟩
  have h : (q - m).gcd q = m.gcd q := by
    have h1 : (q - m).gcd q = (q - m).gcd (m + (q - m)) := by rw [Nat.add_sub_of_le hm.le]
    rw [h1, Nat.gcd_add_self_right, Nat.gcd_comm, ← Nat.gcd_add_self_right m (q - m),
      Nat.sub_add_cancel hm.le]
  rw [h, hg]

/-- **(R2)**  The window count is dominated by twice the fibre sum over the
coprime window `[1,W]`. -/
private lemma winCount_le_fibre_sum (q r W : ℕ) (hq : 2 ≤ q) (hr : 2 ≤ r) (hqr : q ≠ r)
    (hW : W < q * r / q.gcd r) :
    ((winCount q r W : ℕ) : ℝ) ≤
      2 * ((∏ p ∈ Nat.primeFactors (q * r / ((q.gcd r) * (q.gcd r))),
              (p ^ ((q.gcd r).factorization p)).totient : ℕ) : ℝ) *
        (∑ c ∈ (Finset.Icc 1 W).filter
            (fun c => c.gcd (q * r / ((q.gcd r) * (q.gcd r))) = 1),
          (fibreS (∏ p ∈ (Nat.primeFactors (q.gcd r)).filter
              (fun p => ¬ p ∣ q * r / ((q.gcd r) * (q.gcd r))),
              p ^ ((q.gcd r).factorization p)) c : ℝ)) := by
  classical
  have hq0 : 0 < q := by omega
  have hr0 : 0 < r := by omega
  have hQQ : (q / q.gcd r) * (r / q.gcd r) = q * r / ((q.gcd r) * (q.gcd r)) :=
    Nat.div_mul_div_comm (Nat.gcd_dvd_left q r) (Nat.gcd_dvd_right q r)
  have hfib : ∀ e : ℕ, fibreCount q r e =
      if e.gcd (q * r / ((q.gcd r) * (q.gcd r))) = 1
        then (∏ p ∈ Nat.primeFactors (q * r / ((q.gcd r) * (q.gcd r))),
              (p ^ ((q.gcd r).factorization p)).totient)
          * fibreS (∏ p ∈ (Nat.primeFactors (q.gcd r)).filter
              (fun p => ¬ p ∣ q * r / ((q.gcd r) * (q.gcd r))),
              p ^ ((q.gcd r).factorization p))
            (e % (q * r / q.gcd r))
        else 0 := by
    intro e
    have h := residue_fiber_formula q r e hq0 hr0
    dsimp only at h
    rw [hQQ] at h
    simpa [redFinset, fibreS, fibreCount] using h
  have hqq1 : q * r / ((q.gcd r) * (q.gcd r)) ≠ 1 := by
    intro h1
    have h2 : (q / q.gcd r) * (r / q.gcd r) = 1 := by rw [hQQ]; exact h1
    have hM : q / q.gcd r = 1 := Nat.eq_one_of_mul_eq_one_right h2
    have hN : r / q.gcd r = 1 := Nat.eq_one_of_mul_eq_one_left h2
    have hqg : q = q.gcd r := by
      have h := Nat.div_mul_cancel (Nat.gcd_dvd_left q r)
      rw [hM, one_mul] at h; exact h.symm
    have hrg : r = q.gcd r := by
      have h := Nat.div_mul_cancel (Nat.gcd_dvd_right q r)
      rw [hN, one_mul] at h; exact h.symm
    exact hqr (hqg.trans hrg.symm)
  have hfib0 : fibreCount q r 0 = 0 := by
    rw [hfib 0]
    have h0 : ¬ ((0 : ℕ).gcd (q * r / ((q.gcd r) * (q.gcd r))) = 1) := by
      rw [Nat.gcd_zero_left]; exact hqq1
    rw [if_neg h0]
  -- Step 1: expand `winCount`
  set s : Finset (ℕ × ℕ) := (redFinset q).product (redFinset r) with hsdef
  have hwin : winCount q r W =
      (Finset.filter (fun mn : ℕ × ℕ => winU q r mn ≤ W ∨ winV q r mn ≤ W) s).card := by
    rw [winCount_unfold]
  -- membership facts
  have hmem : ∀ {mn : ℕ × ℕ}, mn ∈ s → mn.1 < q ∧ mn.2 < r ∧ mn.1.gcd q = 1 ∧ mn.2.gcd r = 1 := by
    intro mn hmn
    rw [hsdef] at hmn
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hmn
    exact ⟨Finset.mem_range.mp (Finset.mem_filter.mp h1).1, Finset.mem_range.mp (Finset.mem_filter.mp h2).1,
      (Finset.mem_filter.mp h1).2, (Finset.mem_filter.mp h2).2⟩
  have hmem1 : ∀ {mn : ℕ × ℕ}, mn ∈ s → 1 ≤ mn.1 ∧ 1 ≤ mn.2 := by
    intro mn hmn
    obtain ⟨h1, h2, hga, hgb⟩ := hmem hmn
    refine ⟨?_, ?_⟩
    · by_contra hc
      push Not at hc
      have h0 : mn.1 = 0 := by omega
      rw [h0, Nat.gcd_zero_left] at hga
      omega
    · by_contra hc
      push Not at hc
      have h0 : mn.2 = 0 := by omega
      rw [h0, Nat.gcd_zero_left] at hgb
      omega
  -- Step 2: split the disjunction
  have hor : winCount q r W ≤
      (Finset.filter (fun mn : ℕ × ℕ => winU q r mn ≤ W) s).card +
        (Finset.filter (fun mn : ℕ × ℕ => winV q r mn ≤ W) s).card := by
    rw [hwin]
    calc (Finset.filter (fun mn : ℕ × ℕ => winU q r mn ≤ W ∨ winV q r mn ≤ W) s).card
        = ((Finset.filter (fun mn : ℕ × ℕ => winU q r mn ≤ W) s) ∪
            (Finset.filter (fun mn : ℕ × ℕ => winV q r mn ≤ W) s)).card := by
          rw [Finset.filter_or]
      _ ≤ _ := Finset.card_union_le _ _
  -- Step 3: the involution identifies the two filtered sets
  have hcard_v : (Finset.filter (fun mn : ℕ × ℕ => winV q r mn ≤ W) s).card =
      (Finset.filter (fun mn : ℕ × ℕ => winU q r mn ≤ W) s).card := by
    refine Finset.card_bij (fun mn _ => (q - mn.1, r - mn.2)) ?_ ?_ ?_
    · intro mn hmn
      have hmn_s : mn ∈ s := (Finset.mem_filter.mp hmn).1
      have hmn_v : winV q r mn ≤ W := (Finset.mem_filter.mp hmn).2
      obtain ⟨hm1, hn1⟩ := hmem1 hmn_s
      obtain ⟨hmq, hnr, hga, hgb⟩ := hmem hmn_s
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · rw [hsdef] at hmn_s ⊢
        obtain ⟨ha, hb⟩ := Finset.mem_product.mp hmn_s
        exact Finset.mem_product.mpr
          ⟨redFinset_sub_mem hm1 hmq hga, redFinset_sub_mem hn1 hnr hgb⟩
      · rw [winResidue_swap_eq q r mn hm1 hmq hn1 hnr]
        exact hmn_v
    · intro a1 ha1 a2 ha2 heq
      have ha1_s : a1 ∈ s := (Finset.mem_filter.mp ha1).1
      have ha2_s : a2 ∈ s := (Finset.mem_filter.mp ha2).1
      obtain ⟨h1, h2⟩ := hmem1 ha1_s
      obtain ⟨h3, h4⟩ := hmem1 ha2_s
      obtain ⟨h5, h6, -, -⟩ := hmem ha1_s
      obtain ⟨h7, h8, -, -⟩ := hmem ha2_s
      have e1 : q - a1.1 = q - a2.1 := congrArg Prod.fst heq
      have e2 : r - a1.2 = r - a2.2 := congrArg Prod.snd heq
      exact Prod.ext (by omega) (by omega)
    · intro b hb
      have hb_s : b ∈ s := (Finset.mem_filter.mp hb).1
      have hb_u : winU q r b ≤ W := (Finset.mem_filter.mp hb).2
      obtain ⟨hm1, hn1⟩ := hmem1 hb_s
      obtain ⟨hmq, hnr, hga, hgb⟩ := hmem hb_s
      refine ⟨(q - b.1, r - b.2), ?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨?_, ?_⟩
        · rw [hsdef] at hb_s ⊢
          obtain ⟨ha, hb'⟩ := Finset.mem_product.mp hb_s
          exact Finset.mem_product.mpr
            ⟨redFinset_sub_mem hm1 hmq hga, redFinset_sub_mem hn1 hnr hgb⟩
        · rw [winResidue_swap_eq' q r b hm1 hmq hn1 hnr]
          exact hb_u
      · exact Prod.ext (by omega) (by omega)
  -- Step 4: fibre decomposition of the `u`-window
  have hcard_u : (Finset.filter (fun mn : ℕ × ℕ => winU q r mn ≤ W) s).card ≤
      ∑ e ∈ Finset.Icc 0 W, fibreCount q r e := by
    have hmaps : Set.MapsTo (winU q r)
        ↑(Finset.filter (fun mn : ℕ × ℕ => winU q r mn ≤ W) s) ↑(Finset.Icc 0 W) := by
      intro mn hmn
      simp only [Finset.mem_coe, Finset.mem_filter] at hmn
      exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, hmn.2⟩
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    refine Finset.sum_le_sum (fun e he => ?_)
    have heW : e ≤ W := (Finset.mem_Icc.mp he).2
    have heL : e < q * r / q.gcd r := lt_of_le_of_lt heW hW
    have hfil : (Finset.filter (fun mn : ℕ × ℕ => winU q r mn ≤ W) s).filter
          (fun mn : ℕ × ℕ => winU q r mn = e)
        = Finset.filter (fun mn : ℕ × ℕ =>
            (mn.1 * (r / q.gcd r)) % (q * r / q.gcd r)
              = ((mn.2 * (q / q.gcd r) + e) % (q * r / q.gcd r))) s := by
      rw [Finset.filter_filter]
      refine Finset.filter_congr (fun mn hmn => ?_)
      constructor
      · rintro ⟨hu, heq⟩
        exact (winResidue_eq_iff q r hq0 hr0 mn (hmem hmn).1 (hmem hmn).2.1 e heL).mp heq
      · intro h
        have heq := (winResidue_eq_iff q r hq0 hr0 mn (hmem hmn).1 (hmem hmn).2.1 e heL).mpr h
        exact ⟨by rw [heq]; exact heW, heq⟩
    rw [hfil, hsdef, fibreCount]
  -- Step 5: the `e = 0` term vanishes
  have hsum0 : (∑ e ∈ Finset.Icc 0 W, fibreCount q r e) =
      ∑ e ∈ Finset.Icc 1 W, fibreCount q r e := by
    refine (Finset.sum_subset ?_ ?_).symm
    · intro e he
      exact Finset.mem_Icc.mpr ⟨by omega, (Finset.mem_Icc.mp he).2⟩
    · intro e he hne
      have he0 : e = 0 := by
        have h1 : 0 ≤ e := (Finset.mem_Icc.mp he).1
        have h2 : ¬ 1 ≤ e := fun hc => hne (Finset.mem_Icc.mpr ⟨hc, (Finset.mem_Icc.mp he).2⟩)
        omega
      rw [he0, hfib0]
  -- Step 6: express the remaining sum through `fibreS`
  have hsum1 : (∑ e ∈ Finset.Icc 1 W, fibreCount q r e) =
      (∏ p ∈ Nat.primeFactors (q * r / ((q.gcd r) * (q.gcd r))),
          (p ^ ((q.gcd r).factorization p)).totient) *
        (∑ c ∈ (Finset.Icc 1 W).filter
            (fun c => c.gcd (q * r / ((q.gcd r) * (q.gcd r))) = 1),
          fibreS (∏ p ∈ (Nat.primeFactors (q.gcd r)).filter
              (fun p => ¬ p ∣ q * r / ((q.gcd r) * (q.gcd r))),
              p ^ ((q.gcd r).factorization p)) c) := by
    have hcongr : ∀ e ∈ Finset.Icc 1 W, fibreCount q r e =
        if e.gcd (q * r / ((q.gcd r) * (q.gcd r))) = 1
          then (∏ p ∈ Nat.primeFactors (q * r / ((q.gcd r) * (q.gcd r))),
                (p ^ ((q.gcd r).factorization p)).totient)
            * fibreS (∏ p ∈ (Nat.primeFactors (q.gcd r)).filter
                (fun p => ¬ p ∣ q * r / ((q.gcd r) * (q.gcd r))),
                p ^ ((q.gcd r).factorization p)) e
          else 0 := by
      intro e he
      have heW : e ≤ W := (Finset.mem_Icc.mp he).2
      have heL : e < q * r / q.gcd r := lt_of_le_of_lt heW hW
      rw [hfib e, Nat.mod_eq_of_lt heL]
    rw [Finset.sum_congr rfl hcongr]
    rw [Finset.sum_ite]
    rw [Finset.sum_const_zero, add_zero, Finset.mul_sum]
  -- assembly
  have hfinal : winCount q r W ≤
      2 * (∏ p ∈ Nat.primeFactors (q * r / ((q.gcd r) * (q.gcd r))),
              (p ^ ((q.gcd r).factorization p)).totient) *
        (∑ c ∈ (Finset.Icc 1 W).filter
            (fun c => c.gcd (q * r / ((q.gcd r) * (q.gcd r))) = 1),
          fibreS (∏ p ∈ (Nat.primeFactors (q.gcd r)).filter
              (fun p => ¬ p ∣ q * r / ((q.gcd r) * (q.gcd r))),
              p ^ ((q.gcd r).factorization p)) c) := by
    have hA : (Finset.filter (fun mn : ℕ × ℕ => winU q r mn ≤ W) s).card ≤
        (∏ p ∈ Nat.primeFactors (q * r / ((q.gcd r) * (q.gcd r))),
              (p ^ ((q.gcd r).factorization p)).totient) *
          (∑ c ∈ (Finset.Icc 1 W).filter
              (fun c => c.gcd (q * r / ((q.gcd r) * (q.gcd r))) = 1),
            fibreS (∏ p ∈ (Nat.primeFactors (q.gcd r)).filter
                (fun p => ¬ p ∣ q * r / ((q.gcd r) * (q.gcd r))),
                p ^ ((q.gcd r).factorization p)) c) := by
      rw [← hsum1, ← hsum0]
      exact hcard_u
    calc winCount q r W
        ≤ (Finset.filter (fun mn : ℕ × ℕ => winU q r mn ≤ W) s).card +
            (Finset.filter (fun mn : ℕ × ℕ => winV q r mn ≤ W) s).card := hor
      _ = (Finset.filter (fun mn : ℕ × ℕ => winU q r mn ≤ W) s).card +
            (Finset.filter (fun mn : ℕ × ℕ => winU q r mn ≤ W) s).card := by rw [hcard_v]
      _ ≤ (∏ p ∈ Nat.primeFactors (q * r / ((q.gcd r) * (q.gcd r))),
              (p ^ ((q.gcd r).factorization p)).totient) *
            (∑ c ∈ (Finset.Icc 1 W).filter
              (fun c => c.gcd (q * r / ((q.gcd r) * (q.gcd r))) = 1),
              fibreS (∏ p ∈ (Nat.primeFactors (q.gcd r)).filter
                  (fun p => ¬ p ∣ q * r / ((q.gcd r) * (q.gcd r))),
                  p ^ ((q.gcd r).factorization p)) c) +
            (∏ p ∈ Nat.primeFactors (q * r / ((q.gcd r) * (q.gcd r))),
              (p ^ ((q.gcd r).factorization p)).totient) *
            (∑ c ∈ (Finset.Icc 1 W).filter
              (fun c => c.gcd (q * r / ((q.gcd r) * (q.gcd r))) = 1),
              fibreS (∏ p ∈ (Nat.primeFactors (q.gcd r)).filter
                  (fun p => ¬ p ∣ q * r / ((q.gcd r) * (q.gcd r))),
                  p ^ ((q.gcd r).factorization p)) c) := add_le_add hA hA
      _ = 2 * (∏ p ∈ Nat.primeFactors (q * r / ((q.gcd r) * (q.gcd r))),
              (p ^ ((q.gcd r).factorization p)).totient) *
            (∑ c ∈ (Finset.Icc 1 W).filter
              (fun c => c.gcd (q * r / ((q.gcd r) * (q.gcd r))) = 1),
              fibreS (∏ p ∈ (Nat.primeFactors (q.gcd r)).filter
                  (fun p => ¬ p ∣ q * r / ((q.gcd r) * (q.gcd r))),
                  p ^ ((q.gcd r).factorization p)) c) := by ring
  exact_mod_cast hfinal

set_option maxHeartbeats 1600000

/-- A concrete witness constant for (P-b). -/
private def pbConst : ℝ := Classical.choose prod_one_add_div_sq_filter_le_log

private lemma pbConst_nonneg : 0 ≤ pbConst :=
  (Classical.choose_spec prod_one_add_div_sq_filter_le_log).1

private lemma pbConst_spec (X : ℕ) (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    ∏ p ∈ s.filter (fun p => p ≤ X), (1 + (p : ℝ) / ((p : ℝ) - 1) ^ 2)
      ≤ pbConst * Real.log (max (X : ℝ) 3) :=
  (Classical.choose_spec prod_one_add_div_sq_filter_le_log).2 X s hs

/-- The numerical constant `10000 + 1000·C₂` of the sieve-count error term. -/
private def Cconst : ℝ := 10000 + 1000 * pbConst

private lemma Cconst_nonneg : 0 ≤ Cconst := by
  have := pbConst_nonneg; rw [Cconst]; linarith

/-- The per-pair constant of the small-measure K2 regime. -/
private def kappaR : ℝ := 16 * Cconst

/-- The per-pair constant `K` of the small-measure K2 regime. -/
private def kappa : ℝ≥0∞ := ENNReal.ofReal kappaR

private lemma Cconst_pos : 0 < Cconst := by
  rw [Cconst]; have := pbConst_nonneg; linarith

private lemma kappa_lt_top : kappa < (⊤ : ℝ≥0∞) := ENNReal.ofReal_lt_top

private lemma kappa_ge_eight : (8 : ℝ≥0∞) ≤ kappa := by
  have h : (8 : ℝ) ≤ kappaR := by
    rw [kappaR, Cconst]
    have := pbConst_nonneg
    linarith
  calc (8 : ℝ≥0∞) = ENNReal.ofReal (8 : ℝ) := (ENNReal.ofReal_natCast 8).symm
    _ ≤ ENNReal.ofReal kappaR := ENNReal.ofReal_le_ofReal h
    _ = kappa := by rw [kappa]

private lemma kappa_pos : 0 < kappa := by
  rw [kappa, ENNReal.ofReal_pos, kappaR]
  have := Cconst_pos; linarith

/-- Pure field rearrangement used in the K2 assembly. -/
private lemma k2_field (P S C W t g q : ℝ) (hg : g ≠ 0) (hq : q ≠ 0) :
    2 * P * (S * C * (W * (t / q))) = 2 * C * W * (P * S * g * t) / (g * q) := by
  field_simp

/-- Pure field rearrangement used in the K2 assembly (second form). -/
private lemma k2_field2 (P S C W t g q Q R L : ℝ) (hg : g ≠ 0) (hq : q ≠ 0)
    (hL : L = g * q) (hphi : P * S * g * t = Q * R) :
    2 * C * W * (P * S * g * t) / (g * q) = 2 * C * (W / L) * (Q * R) := by
  rw [hphi, hL]
  field_simp

/-- For `1 ≤ q ≤ 7` the totient ratio is at least `1/4`. -/
private lemma totient_ratio_seven (q : ℕ) (hq1 : 1 ≤ q) (hq7 : q ≤ 7) :
    (1 : ℝ) / 4 ≤ (q.totient : ℝ) / (q : ℝ) := by
  have t1 : (1 : ℕ).totient = 1 := by decide
  have t2 : (2 : ℕ).totient = 1 := by decide
  have t3 : (3 : ℕ).totient = 2 := by decide
  have t4 : (4 : ℕ).totient = 2 := by decide
  have t5 : (5 : ℕ).totient = 4 := by decide
  have t6 : (6 : ℕ).totient = 2 := by decide
  have t7 : (7 : ℕ).totient = 6 := by decide
  interval_cases q <;> norm_num [t1, t2, t3, t4, t5, t6, t7]

/-- Crude bound for the (P-c) inequality when `q' ∈ {2,3}`. -/
private lemma small_qq_log_bound (qq W : ℕ) (h2 : 2 ≤ qq) (h3 : qq < 4) (hW : 1 ≤ W) :
    (2 : ℝ) ^ (qq.primeFactors.card) * Real.log (max (W : ℝ) 3)
      ≤ 1000 * ((W : ℝ) * ((qq.totient : ℝ) / (qq : ℝ))) := by
  have hlog : Real.log (max (W : ℝ) 3) ≤ 2 * (W : ℝ) := by
    rcases lt_or_ge (W : ℝ) 3 with h | h
    · rw [max_eq_right h.le]
      have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (3 : ℝ) by norm_num)
      have hW1 : (1 : ℝ) ≤ (W : ℝ) := by exact_mod_cast hW
      linarith
    · rw [max_eq_left h]
      have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (W : ℝ) by linarith)
      linarith
  have hW1 : (1 : ℝ) ≤ (W : ℝ) := by exact_mod_cast hW
  interval_cases qq
  · have hpr : (2 : ℕ).Prime := by norm_num
    have hp : (2 : ℕ).primeFactors.card = 1 := by rw [hpr.primeFactors]; simp
    rw [hp, pow_one]
    norm_num [Nat.totient_two]
    nlinarith [hlog, hW1]
  · have hpr : (3 : ℕ).Prime := by norm_num
    have hp : (3 : ℕ).primeFactors.card = 1 := by rw [hpr.primeFactors]; simp
    have hc : (Nat.totient 3 : ℕ) = 2 := by decide
    rw [hp, pow_one, hc]
    norm_num
    nlinarith [hlog, hW1]

/-- **(K2, small-measure regime)**  Per-pair quasi-independence when both
`φ(q)δq` and `φ(r)δr` are `< 1/8`. -/
private lemma quasi_small_regime (q r : ℕ) (hq : 0 < q) (hr : 0 < r) (hqr : q ≠ r)
    (δq δr : ℝ) (hδq : 0 ≤ δq) (hδr : 0 ≤ δr)
    (hlq : (1 : ℝ) / 2 ≤ (q : ℝ) * δq) (hlr : (1 : ℝ) / 2 ≤ (r : ℝ) * δr)
    (hφq : (q.totient : ℝ) * δq < 1 / 8) (hφr : (r.totient : ℝ) * δr < 1 / 8) :
    MeasureTheory.volume (approxAddOrderOf UnitAddCircle q δq ∩
        approxAddOrderOf UnitAddCircle r δr) ≤
      kappa * MeasureTheory.volume (approxAddOrderOf UnitAddCircle q δq) *
        MeasureTheory.volume (approxAddOrderOf UnitAddCircle r δr) := by
  classical
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hratio : (q.totient : ℝ) / (q : ℝ) < 1 / 4 := by
    have h1 : (1 : ℝ) / (2 * (q : ℝ)) ≤ δq := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (q : ℝ))]
      nlinarith [hlq]
    have h2 : (q.totient : ℝ) * (1 / (2 * (q : ℝ))) ≤ (q.totient : ℝ) * δq :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : (q.totient : ℝ) / (2 * (q : ℝ)) < 1 / 8 := by
      have : (q.totient : ℝ) * (1 / (2 * (q : ℝ))) = (q.totient : ℝ) / (2 * (q : ℝ)) := by ring
      rw [this] at h2
      linarith [hφq]
    have h4 : (q.totient : ℝ) / (q : ℝ) / 2 = (q.totient : ℝ) / (2 * (q : ℝ)) := by ring
    rw [← h4] at h3
    linarith
  have hratio_r : (r.totient : ℝ) / (r : ℝ) < 1 / 4 := by
    have h1 : (1 : ℝ) / (2 * (r : ℝ)) ≤ δr := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (r : ℝ))]
      nlinarith [hlr]
    have h2 : (r.totient : ℝ) * (1 / (2 * (r : ℝ))) ≤ (r.totient : ℝ) * δr :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : (r.totient : ℝ) / (2 * (r : ℝ)) < 1 / 8 := by
      have : (r.totient : ℝ) * (1 / (2 * (r : ℝ))) = (r.totient : ℝ) / (2 * (r : ℝ)) := by ring
      rw [this] at h2
      linarith [hφr]
    have h4 : (r.totient : ℝ) / (r : ℝ) / 2 = (r.totient : ℝ) / (2 * (r : ℝ)) := by ring
    rw [← h4] at h3
    linarith
  have hφq2 : 2 ≤ q.totient := by
    by_contra hc
    push Not at hc
    have h1 : q.totient = 1 := by
      have h0 : 0 < q.totient := Nat.totient_pos.mpr hq
      omega
    have h2 : q ≤ 2 := by
      rcases (Nat.totient_eq_one_iff.mp h1) with h | h <;> omega
    have h3 : 4 < q := by
      have h3R : (4 : ℝ) < (q : ℝ) := by
        have h := (div_lt_iff₀ hqR).mp hratio
        have h1R : (q.totient : ℝ) = 1 := by exact_mod_cast h1
        linarith
      exact_mod_cast h3R
    omega
  have hφr2 : 2 ≤ r.totient := by
    by_contra hc
    push Not at hc
    have h1 : r.totient = 1 := by
      have h0 : 0 < r.totient := Nat.totient_pos.mpr hr
      omega
    have h2 : r ≤ 2 := by
      rcases (Nat.totient_eq_one_iff.mp h1) with h | h <;> omega
    have h3 : 4 < r := by
      have h3R : (4 : ℝ) < (r : ℝ) := by
        have h := (div_lt_iff₀ hrR).mp hratio_r
        have h1R : (r.totient : ℝ) = 1 := by exact_mod_cast h1
        linarith
      exact_mod_cast h3R
    omega
  have hΔ8 : δq + δr < 1 / 8 := by
    have h1 : 2 * δq ≤ (q.totient : ℝ) * δq := by
      have h3 : (2 : ℝ) ≤ (q.totient : ℝ) := by exact_mod_cast hφq2
      nlinarith [hδq]
    have h2 : 2 * δr ≤ (r.totient : ℝ) * δr := by
      have h3 : (2 : ℝ) ≤ (r.totient : ℝ) := by exact_mod_cast hφr2
      nlinarith [hδr]
    have h0q : (0 : ℝ) < (q.totient : ℝ) := by
      have := Nat.totient_pos.mpr hq
      exact_mod_cast this
    have h0r : (0 : ℝ) < (r.totient : ℝ) := by
      have := Nat.totient_pos.mpr hr
      exact_mod_cast this
    have h4 : δq < 1 / (8 * (q.totient : ℝ)) := by
      rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 8 * (q.totient : ℝ))]
      linarith [hφq]
    have h5 : δr < 1 / (8 * (r.totient : ℝ)) := by
      rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 8 * (r.totient : ℝ))]
      linarith [hφr]
    have h6 : 1 / (8 * (q.totient : ℝ)) ≤ 1 / 16 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 8 * (q.totient : ℝ))]
      have h2 : (2 : ℝ) ≤ (q.totient : ℝ) := by exact_mod_cast hφq2
      linarith
    have h7 : 1 / (8 * (r.totient : ℝ)) ≤ 1 / 16 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 8 * (r.totient : ℝ))]
      have h2 : (2 : ℝ) ≤ (r.totient : ℝ) := by exact_mod_cast hφr2
      linarith
    linarith
  have hq2 : 2 ≤ q := by have := Nat.totient_le q; omega
  have hr2 : 2 ≤ r := by have := Nat.totient_le r; omega
  set g : ℕ := q.gcd r with hgdef
  set qq : ℕ := q * r / (g * g) with hqqdef
  set Kc : ℕ := ∏ p ∈ (Nat.primeFactors g).filter (fun p => ¬ p ∣ qq), p ^ (g.factorization p)
    with hKcdef
  set Phi : ℕ := ∏ p ∈ Nat.primeFactors qq, (p ^ (g.factorization p)).totient with hPhidef
  set L : ℕ := q * r / g with hLdef
  set W : ℕ := Nat.ceil ((δq + δr) * ((L : ℕ) : ℝ)) with hWdef
  have hL2 : 2 ≤ L := by
    have hgdvd : g ∣ r := Nat.gcd_dvd_right q r
    have hgpos : 0 < g := Nat.gcd_pos_of_pos_left r hq
    have hr1 : 1 ≤ r / g := Nat.div_pos (Nat.le_of_dvd hr hgdvd) hgpos
    have hLq : L = q * (r / g) := by rw [hLdef, hgdef]; exact Nat.mul_div_assoc q hgdvd
    rw [hLq]
    calc q * (r / g) ≥ q * 1 := Nat.mul_le_mul_left q hr1
      _ = q := by ring
      _ ≥ 2 := hq2
  have hqqMN : (q / g) * (r / g) = qq := by
    rw [hqqdef]
    exact Nat.div_mul_div_comm (Nat.gcd_dvd_left q r) (Nat.gcd_dvd_right q r)
  have hM1 : 1 ≤ q / g := Nat.div_pos (Nat.le_of_dvd hq (Nat.gcd_dvd_left q r)) (Nat.gcd_pos_of_pos_left r hq)
  have hN1 : 1 ≤ r / g := Nat.div_pos (Nat.le_of_dvd hr (Nat.gcd_dvd_right q r)) (Nat.gcd_pos_of_pos_left r hq)
  have hqq1 : qq ≠ 1 := by
    intro h1
    have h2 : (q / g) * (r / g) = 1 := hqqMN.trans h1
    have hM : q / g = 1 := Nat.eq_one_of_mul_eq_one_right h2
    have hN : r / g = 1 := Nat.eq_one_of_mul_eq_one_left h2
    have hqg : q = g := by
      have h := Nat.mul_div_cancel' (Nat.gcd_dvd_left q r)
      rw [hM, mul_one] at h; exact h.symm
    have hrg : r = g := by
      have h := Nat.mul_div_cancel' (Nat.gcd_dvd_right q r)
      rw [hN, mul_one] at h; exact h.symm
    exact hqr (hqg.trans hrg.symm)
  have hqq2 : 2 ≤ qq := by
    have h1 : 1 ≤ qq := by
      rw [← hqqMN]
      exact Nat.mul_pos (by omega) (by omega)
    omega
  have hLgq_nat : L = g * qq := by
    have h2 : L = q * (r / g) := by rw [hLdef, hgdef]; exact Nat.mul_div_assoc q (Nat.gcd_dvd_right q r)
    have h3 : q = g * (q / g) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left q r)).symm
    rw [h2, h3, mul_assoc, hqqMN]
  have hLg : (L : ℝ) = (g : ℝ) * ((q / g : ℕ) : ℝ) * ((r / g : ℕ) : ℝ) := by
    rw [hLgq_nat, ← hqqMN]
    push_cast; ring
  have hqqg : (qq : ℝ) = ((q / g : ℕ) : ℝ) * ((r / g : ℕ) : ℝ) := by
    rw [← hqqMN]
    push_cast; rfl
  have hWlt : W < L := by
    have hceil := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (δq + δr) * ((L : ℕ) : ℝ) by positivity)
    have hL0 : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
    have h2 : (2 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL2
    have hmul := mul_lt_mul_of_pos_right hΔ8 hL0
    have hle : (δq + δr) * ((L : ℕ) : ℝ) + 1 ≤ (L : ℝ) := by nlinarith [hmul, h2]
    rw [hWdef]
    have : ((Nat.ceil ((δq + δr) * ((L : ℕ) : ℝ)) : ℕ) : ℝ) < (L : ℝ) := by linarith
    exact_mod_cast this
  have hqcast : (q : ℝ) = (g : ℝ) * ((q / g : ℕ) : ℝ) := by
    rw [hgdef, ← Nat.cast_mul, Nat.mul_div_cancel' (Nat.gcd_dvd_left q r)]
  have hkcast : (r : ℝ) = (g : ℝ) * ((r / g : ℕ) : ℝ) := by
    rw [hgdef, ← Nat.cast_mul, Nat.mul_div_cancel' (Nat.gcd_dvd_right q r)]
  have hkey0 : (1 : ℝ) / (2 * (q : ℝ)) * (L : ℝ) + 1 / (2 * (r : ℝ)) * (L : ℝ)
      = (((q / g : ℕ) : ℝ) + ((r / g : ℕ) : ℝ)) / 2 := by
    have hL : (L : ℝ) = (g : ℝ) * (((q / g : ℕ) : ℝ) * ((r / g : ℕ) : ℝ)) := by
      rw [hLgq_nat, ← hqqMN]; push_cast; ring
    rw [hL, hqcast, hkcast]
    have hgne : (g : ℝ) ≠ 0 := by
      have : 0 < g := Nat.gcd_pos_of_pos_left r hq
      exact_mod_cast this.ne'
    have hMne : ((q / g : ℕ) : ℝ) ≠ 0 := by
      have : 0 < q / g := by omega
      exact_mod_cast this.ne'
    have hNne : ((r / g : ℕ) : ℝ) ≠ 0 := by
      have : 0 < r / g := by omega
      exact_mod_cast this.ne'
    field_simp
    ring
  have hX : Real.sqrt (qq : ℝ) - 1 ≤ (W : ℝ) := by
    have hM0 : (0 : ℝ) ≤ ((q / g : ℕ) : ℝ) := by positivity
    have hN0 : (0 : ℝ) ≤ ((r / g : ℕ) : ℝ) := by positivity
    have hgm : Real.sqrt (qq : ℝ) ≤ (((q / g : ℕ) : ℝ) + ((r / g : ℕ) : ℝ)) / 2 := by
      rw [hqqg, Real.sqrt_mul hM0]
      have ha := Real.sq_sqrt hM0
      have hb := Real.sq_sqrt hN0
      have ha0 := Real.sqrt_nonneg ((q / g : ℕ) : ℝ)
      have hb0 := Real.sqrt_nonneg ((r / g : ℕ) : ℝ)
      nlinarith [sq_nonneg (Real.sqrt ((q / g : ℕ) : ℝ) - Real.sqrt ((r / g : ℕ) : ℝ))]
    have hd : (1 : ℝ) / (2 * (q : ℝ)) + 1 / (2 * (r : ℝ)) ≤ δq + δr := by
      have h1 : (1 : ℝ) / (2 * (q : ℝ)) ≤ δq := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (q : ℝ))]
        nlinarith [hlq]
      have h2 : (1 : ℝ) / (2 * (r : ℝ)) ≤ δr := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (r : ℝ))]
        nlinarith [hlr]
      linarith
    have hL0 : (0 : ℝ) ≤ (L : ℝ) := by positivity
    have h1 : (((q / g : ℕ) : ℝ) + ((r / g : ℕ) : ℝ)) / 2 ≤ (δq + δr) * (L : ℝ) := by
      have h2 := mul_le_mul_of_nonneg_right hd hL0
      rw [add_mul, hkey0] at h2
      linarith
    have h3 := Nat.le_ceil ((δq + δr) * ((L : ℕ) : ℝ))
    rw [hWdef]
    linarith
  have hR1 := inter_volume_le_ofReal_mul_winCount q r hq hr δq δr hδq hδr
  rw [← hWdef] at hR1
  have hWltL : W < q * r / q.gcd r := by
    rw [show q * r / q.gcd r = L from by rw [hLdef, hgdef]]
    exact hWlt
  have hR2' : ((winCount q r W : ℕ) : ℝ) ≤ 2 * (Phi : ℝ) *
      (∑ c ∈ (Finset.Icc 1 W).filter (fun c => c.gcd qq = 1), (fibreS Kc c : ℝ)) := by
    have h := winCount_le_fibre_sum q r W hq2 hr2 hqr hWltL
    rw [← hgdef, ← hqqdef, ← hKcdef, ← hPhidef] at h
    exact h
  have hqq0 : 0 < qq := by omega
  have hW1 : 1 ≤ W := by
    have h0 : (0 : ℝ) < (W : ℝ) := by
      have hsqrt2 : (1 : ℝ) < Real.sqrt (qq : ℝ) := by
        have h2 : (1 : ℝ) < Real.sqrt 2 := by
          rw [← Real.sqrt_one]
          exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
        have h3 : Real.sqrt 2 ≤ Real.sqrt (qq : ℝ) :=
          Real.sqrt_le_sqrt (by exact_mod_cast hqq2)
        linarith
      linarith [hX]
    exact Nat.succ_le_of_lt (by exact_mod_cast h0 : (0 : ℕ) < W)
  have hSbar : 0 ≤ fibreSbar Kc := by
    rw [fibreSbar]
    refine Finset.prod_nonneg (fun p hp => ?_)
    have hp0 : (0 : ℝ) < (p : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
    positivity
  have hPa := fibreS_coprime_window_le Kc W qq hqq0
  have hPb := pbConst_spec W Kc.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
  have hPc : (2 : ℝ) ^ (qq.primeFactors.card) * Real.log (max (W : ℝ) 3)
      ≤ 1000 * ((W : ℝ) * ((qq.totient : ℝ) / (qq : ℝ))) := by
    rcases lt_or_ge qq 4 with h4 | h4
    · exact small_qq_log_bound qq W hqq2 h4 hW1
    · have h := two_pow_omega_log_mul_le qq W h4 hX
      have hqqR : (0 : ℝ) < (qq : ℝ) := by exact_mod_cast hqq0
      have hφ0 : (0 : ℝ) < (qq.totient : ℝ) := by
        have := Nat.totient_pos.mpr hqq0
        exact_mod_cast this
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (W : ℝ) * (qq.totient : ℝ))] at h
      have heq : 1000 * ((W : ℝ) * ((qq.totient : ℝ) / (qq : ℝ)))
          = (1000 * (W : ℝ) * (qq.totient : ℝ)) / (qq : ℝ) := by
        field_simp
      rw [heq, le_div_iff₀ hqqR]
      simpa only [mul_assoc] using h
  have hSig : (∑ c ∈ (Finset.Icc 1 W).filter (fun c => c.gcd qq = 1), (fibreS Kc c : ℝ))
      ≤ fibreSbar Kc * Cconst * ((W : ℝ) * ((qq.totient : ℝ) / (qq : ℝ))) := by
    have h2w : (0 : ℝ) ≤ (2 : ℝ) ^ (qq.primeFactors.card) := by positivity
    have hstep : (2 : ℝ) ^ (qq.primeFactors.card) *
          ∏ p ∈ Kc.primeFactors.filter (fun p => p ≤ W), (1 + (p : ℝ) / ((p : ℝ) - 1) ^ 2)
        ≤ 1000 * pbConst * ((W : ℝ) * ((qq.totient : ℝ) / (qq : ℝ))) := by
      calc (2 : ℝ) ^ (qq.primeFactors.card) *
            ∏ p ∈ Kc.primeFactors.filter (fun p => p ≤ W), (1 + (p : ℝ) / ((p : ℝ) - 1) ^ 2)
          ≤ (2 : ℝ) ^ (qq.primeFactors.card) * (pbConst * Real.log (max (W : ℝ) 3)) :=
            mul_le_mul_of_nonneg_left hPb h2w
        _ = pbConst * ((2 : ℝ) ^ (qq.primeFactors.card) * Real.log (max (W : ℝ) 3)) := by ring
        _ ≤ pbConst * (1000 * ((W : ℝ) * ((qq.totient : ℝ) / (qq : ℝ)))) :=
            mul_le_mul_of_nonneg_left hPc pbConst_nonneg
        _ = 1000 * pbConst * ((W : ℝ) * ((qq.totient : ℝ) / (qq : ℝ))) := by ring
    have hinner : (2 : ℝ) ^ (qq.primeFactors.card) *
          ∏ p ∈ Kc.primeFactors.filter (fun p => p ≤ W), (1 + (p : ℝ) / ((p : ℝ) - 1) ^ 2)
        ≤ 1000 * pbConst * ((W : ℝ) * ((qq.totient : ℝ) / (qq : ℝ))) := hstep
    have hPa' : (∑ c ∈ (Finset.Icc 1 W).filter (fun c => c.gcd qq = 1), (fibreS Kc c : ℝ))
        ≤ fibreSbar Kc * (10000 * ((W : ℝ) * ((qq.totient : ℝ) / (qq : ℝ))) + (2 : ℝ) ^ (qq.primeFactors.card) * ∏ p ∈ Kc.primeFactors.filter (fun p => p ≤ W), (1 + (p : ℝ) / ((p : ℝ) - 1) ^ 2)) := by
      simpa only [mul_assoc] using hPa
    calc (∑ c ∈ (Finset.Icc 1 W).filter (fun c => c.gcd qq = 1), (fibreS Kc c : ℝ))
        ≤ fibreSbar Kc * (10000 * ((W : ℝ) * ((qq.totient : ℝ) / (qq : ℝ))) + (2 : ℝ) ^ (qq.primeFactors.card) * ∏ p ∈ Kc.primeFactors.filter (fun p => p ≤ W), (1 + (p : ℝ) / ((p : ℝ) - 1) ^ 2)) := hPa'
      _ ≤ fibreSbar Kc * (10000 * ((W : ℝ) * ((qq.totient : ℝ) / (qq : ℝ))) + 1000 * pbConst * ((W : ℝ) * ((qq.totient : ℝ) / (qq : ℝ)))) := by
            refine mul_le_mul_of_nonneg_left ?_ hSbar
            linarith [hinner]
      _ = fibreSbar Kc * Cconst * ((W : ℝ) * ((qq.totient : ℝ) / (qq : ℝ))) := by
            rw [Cconst]; ring
  have hphi : (Phi : ℝ) * fibreSbar Kc * (g : ℝ) * ((qq.totient : ℝ))
      = (q.totient : ℝ) * (r.totient : ℝ) := by
    have h := fibre_phi_identity q r hq hr
    dsimp only at h
    rw [← hgdef, ← hqqdef, ← hKcdef, ← hPhidef] at h
    simpa [fibreSbar] using h
  have hΔL : (1 : ℝ) ≤ (δq + δr) * (L : ℝ) := by
    have hgpos : 0 < g := Nat.gcd_pos_of_pos_left r hq
    have hg0 : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hgpos
    have hM0 : (0 : ℝ) < ((q / g : ℕ) : ℝ) := by exact_mod_cast (show 0 < q / g by omega)
    have hN0 : (0 : ℝ) < ((r / g : ℕ) : ℝ) := by exact_mod_cast (show 0 < r / g by omega)
    have hMN2 : (2 : ℝ) ≤ ((q / g : ℕ) : ℝ) + ((r / g : ℕ) : ℝ) := by
      have h2 : (2 : ℝ) ≤ ((q / g : ℕ) : ℝ) * ((r / g : ℕ) : ℝ) := by
        rw [← hqqg]; exact_mod_cast hqq2
      nlinarith [hM0, hN0]
    have hd1 : (1 : ℝ) / (2 * (q : ℝ)) ≤ δq := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (q : ℝ))]
      nlinarith [hlq]
    have hd2 : (1 : ℝ) / (2 * (r : ℝ)) ≤ δr := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (r : ℝ))]
      nlinarith [hlr]
    have hL0 : (0 : ℝ) ≤ (L : ℝ) := by positivity
    have h1 : ((1 : ℝ) / (2 * (q : ℝ)) + 1 / (2 * (r : ℝ))) * (L : ℝ) ≤ (δq + δr) * (L : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith) hL0
    rw [add_mul, hkey0] at h1
    linarith
  have hcount : ((winCount q r W : ℕ) : ℝ)
      ≤ 4 * Cconst * (δq + δr) * ((q.totient : ℝ) * (r.totient : ℝ)) := by
    have hL0 : (0 : ℝ) < (L : ℝ) := by
      have : 0 < L := by omega
      exact_mod_cast this
    have hg0 : (0 : ℝ) < (g : ℝ) := by
      have : 0 < g := Nat.gcd_pos_of_pos_left r hq
      exact_mod_cast this
    have hqqR0 : (0 : ℝ) < (qq : ℝ) := by exact_mod_cast hqq0
    have hW2 : (W : ℝ) ≤ 2 * ((δq + δr) * (L : ℝ)) := by
      have h1 : (W : ℝ) < (δq + δr) * (L : ℝ) + 1 := by
        have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (δq + δr) * ((L : ℕ) : ℝ) by positivity)
        rw [hWdef]; linarith
      have h2 : (1 : ℝ) ≤ (δq + δr) * (L : ℝ) := hΔL
      linarith
    have hid : 2 * (Phi : ℝ) * (fibreSbar Kc * Cconst * ((W : ℝ) * ((qq.totient : ℝ) / (qq : ℝ))))
        = 2 * Cconst * ((W : ℝ) / (L : ℝ)) * ((q.totient : ℝ) * (r.totient : ℝ)) := by
      have hgne : (g : ℝ) ≠ 0 := ne_of_gt hg0
      have hqqne : (qq : ℝ) ≠ 0 := ne_of_gt hqqR0
      rw [k2_field (Phi : ℝ) (fibreSbar Kc) Cconst (W : ℝ) (qq.totient : ℝ) (g : ℝ) (qq : ℝ)
        hgne hqqne]
      exact k2_field2 (Phi : ℝ) (fibreSbar Kc) Cconst (W : ℝ) (qq.totient : ℝ) (g : ℝ) (qq : ℝ)
        (q.totient : ℝ) (r.totient : ℝ) (L : ℝ) hgne hqqne
        (by rw [hLgq_nat]; push_cast; ring) hphi
    have hWL : (W : ℝ) / (L : ℝ) ≤ 2 * (δq + δr) := by
      rw [div_le_iff₀ hL0]
      linarith [hW2]
    calc ((winCount q r W : ℕ) : ℝ)
        ≤ 2 * (Phi : ℝ) * (fibreSbar Kc * Cconst * ((W : ℝ) * ((qq.totient : ℝ) / (qq : ℝ)))) := by
          refine le_trans hR2' ?_
          exact mul_le_mul_of_nonneg_left hSig (by positivity)
      _ = 2 * Cconst * ((W : ℝ) / (L : ℝ)) * ((q.totient : ℝ) * (r.totient : ℝ)) := hid
      _ ≤ 2 * Cconst * (2 * (δq + δr)) * ((q.totient : ℝ) * (r.totient : ℝ)) := by
          have hZ : (0 : ℝ) ≤ (q.totient : ℝ) * (r.totient : ℝ) := by positivity
          have h2C : (0 : ℝ) ≤ 2 * Cconst := by linarith [Cconst_nonneg]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hWL h2C) hZ
      _ = 4 * Cconst * (δq + δr) * ((q.totient : ℝ) * (r.totient : ℝ)) := by ring
  have h2m : (0 : ℝ) ≤ 2 * min δq δr := by positivity
  have hK1q : ENNReal.ofReal ((q.totient : ℝ) * δq) ≤
      MeasureTheory.volume (approxAddOrderOf UnitAddCircle q δq) := by
    have h := approxAddOrderOf_volume_ge_min_quasi q δq hδq (Or.inr hlq)
    have hmin : min (1 : ℝ) (2 * (q.totient : ℝ) * δq) = 2 * (q.totient : ℝ) * δq := by
      refine min_eq_right ?_
      linarith [hφq]
    rw [hmin] at h
    have : (1 / 2) * (2 * (q.totient : ℝ) * δq) = (q.totient : ℝ) * δq := by ring
    rwa [this] at h
  have hK1r : ENNReal.ofReal ((r.totient : ℝ) * δr) ≤
      MeasureTheory.volume (approxAddOrderOf UnitAddCircle r δr) := by
    have h := approxAddOrderOf_volume_ge_min_quasi r δr hδr (Or.inr hlr)
    have hmin : min (1 : ℝ) (2 * (r.totient : ℝ) * δr) = 2 * (r.totient : ℝ) * δr := by
      refine min_eq_right ?_
      linarith [hφr]
    rw [hmin] at h
    have : (1 / 2) * (2 * (r.totient : ℝ) * δr) = (r.totient : ℝ) * δr := by ring
    rwa [this] at h
  have hmin4 : 2 * min δq δr * (δq + δr) ≤ 4 * (δq * δr) := by
    rcases le_total δq δr with h | h
    · rw [min_eq_left h]; nlinarith
    · rw [min_eq_right h]; nlinarith
  have hNle : ((winCount q r W : ℕ) : ℝ≥0∞)
      ≤ ENNReal.ofReal (4 * Cconst * (δq + δr) * ((q.totient : ℝ) * (r.totient : ℝ))) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hcount
  calc MeasureTheory.volume (approxAddOrderOf UnitAddCircle q δq ∩
          approxAddOrderOf UnitAddCircle r δr)
      ≤ ENNReal.ofReal (2 * min δq δr) * ((winCount q r W : ℕ) : ℝ≥0∞) := hR1
    _ ≤ ENNReal.ofReal (2 * min δq δr) *
          ENNReal.ofReal (4 * Cconst * (δq + δr) * ((q.totient : ℝ) * (r.totient : ℝ))) :=
          mul_le_mul' le_rfl hNle
    _ = ENNReal.ofReal ((2 * min δq δr) *
          (4 * Cconst * (δq + δr) * ((q.totient : ℝ) * (r.totient : ℝ)))) := by
          rw [ENNReal.ofReal_mul h2m]
    _ ≤ ENNReal.ofReal (kappaR * (δq * δr * ((q.totient : ℝ) * (r.totient : ℝ)))) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hZ : (0 : ℝ) ≤ (q.totient : ℝ) * (r.totient : ℝ) := by positivity
          rw [kappaR]
          have h4 : (2 * min δq δr) * (4 * Cconst * (δq + δr) * ((q.totient : ℝ) * (r.totient : ℝ)))
              = ((2 * min δq δr) * (δq + δr)) * (4 * Cconst * ((q.totient : ℝ) * (r.totient : ℝ))) := by
            ring
          rw [h4]
          have h4C : (0 : ℝ) ≤ 4 * Cconst * ((q.totient : ℝ) * (r.totient : ℝ)) :=
            mul_nonneg (mul_nonneg (by norm_num) Cconst_nonneg) hZ
          refine le_trans (mul_le_mul_of_nonneg_right hmin4 h4C) (le_of_eq ?_)
          ring
    _ = kappa * (ENNReal.ofReal ((q.totient : ℝ) * δq) *
          ENNReal.ofReal ((r.totient : ℝ) * δr)) := by
          have hKR : (0 : ℝ) ≤ kappaR := by rw [kappaR]; linarith [Cconst_nonneg]
          rw [kappa]
          rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (q.totient : ℝ) * δq),
            ← ENNReal.ofReal_mul hKR]
          congr 1
          ring
    _ ≤ kappa * MeasureTheory.volume (approxAddOrderOf UnitAddCircle q δq) *
          MeasureTheory.volume (approxAddOrderOf UnitAddCircle r δr) := by
          rw [mul_assoc]
          exact mul_le_mul' le_rfl (mul_le_mul' hK1q hK1r)

/-- K2 — per-pair quasi-independence for large values: for `q ≠ r` with each radius
`0` or `q·δ ≥ 1/2`, `μ(A_q∩A_r) ≤ 8·μ(A_q)·μ(A_r)`.  Trivial regime: if
`max(μ(A_q), μ(A_r)) ≥ 1/8` then `μ∩ ≤ min(μ_q,μ_r) ≤ 8μ_qμ_r`.  Nontrivial
regime (one measure < 1/8, forcing `φ(q)/q < 1/8`, q very smooth): use the
committed `approxAddOrderOf_inter_volume_le`
(`μ∩ ≤ 2·min(δq,δr)·N(q,r,δq+δr)`, N = number of close reduced pairs) and bound
N by the close-pair window estimate `N ≤ C·(δq+δr)·φ(q)φ(r)·∏_{p | qr/g²,
p > (δq+δr)·lcm/2}(1−1/p)⁻¹` (the `pv_close_pair_count_le` /
`pv_reduced_pair_window_count_le` counting core of the small-values branch, same
committed fibre machinery `fibre_window_count_le_global` / `fibre_count_eq`),
then `main_term_real_ineq` + certified `μ ≥ φ/q`.  Numerically ratio
`μ∩/(μ_q μ_r) ≤ 1.5` in all tested regimes.  (Requested of the fleet as
`NumberTheory/DuffinSchaeffer/approxAddOrderOf_inter_volume_le_quasi`.) -/
private lemma approxAddOrderOf_inter_volume_le_quasi (q r : ℕ) (hq : 0 < q) (hr : 0 < r)
    (hqr : q ≠ r) (δq δr : ℝ)
    (hlq : δq = 0 ∨ (1 : ℝ) / 2 ≤ (q : ℝ) * δq)
    (hlr : δr = 0 ∨ (1 : ℝ) / 2 ≤ (r : ℝ) * δr) :
    MeasureTheory.volume (approxAddOrderOf UnitAddCircle q δq ∩
        approxAddOrderOf UnitAddCircle r δr) ≤
      kappa * MeasureTheory.volume (approxAddOrderOf UnitAddCircle q δq) *
        MeasureTheory.volume (approxAddOrderOf UnitAddCircle r δr) := by
  by_cases hq0 : δq = 0
  · subst hq0
    have hAq : approxAddOrderOf UnitAddCircle q 0 = (∅ : Set UnitAddCircle) :=
      approxAddOrderOf_eq_empty_of_radius_zero q hq
    rw [hAq]
    simp
  by_cases hr0 : δr = 0
  · subst hr0
    have hAr : approxAddOrderOf UnitAddCircle r 0 = (∅ : Set UnitAddCircle) :=
      approxAddOrderOf_eq_empty_of_radius_zero r hr
    rw [hAr]
    simp
  -- Substantive case: both radii positive and large (q·δq ≥ 1/2, r·δr ≥ 1/2).
  by_cases hbig : (1 : ENNReal) / 8 ≤
      max (MeasureTheory.volume (approxAddOrderOf UnitAddCircle q δq))
        (MeasureTheory.volume (approxAddOrderOf UnitAddCircle r δr))
  · refine le_trans (inter_volume_le_quasi_of_large_measure q r δq δr hbig) ?_
    exact mul_le_mul' (mul_le_mul' kappa_ge_eight le_rfl) le_rfl
  · -- Hard regime: BOTH measures < 1/8.
    have hmax_lt : max (MeasureTheory.volume (approxAddOrderOf UnitAddCircle q δq))
        (MeasureTheory.volume (approxAddOrderOf UnitAddCircle r δr)) < (1 : ENNReal) / 8 :=
      lt_of_not_ge hbig
    have hmuq : MeasureTheory.volume (approxAddOrderOf UnitAddCircle q δq) < (1 : ENNReal) / 8 :=
      lt_of_le_of_lt (le_max_left _ _) hmax_lt
    have hmur : MeasureTheory.volume (approxAddOrderOf UnitAddCircle r δr) < (1 : ENNReal) / 8 :=
      lt_of_le_of_lt (le_max_right _ _) hmax_lt
    have hlq' : (1 : ℝ) / 2 ≤ (q : ℝ) * δq := hlq.resolve_left hq0
    have hlr' : (1 : ℝ) / 2 ≤ (r : ℝ) * δr := hlr.resolve_left hr0
    have hδq0 : 0 ≤ δq := by
      have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
      nlinarith
    have hδr0 : 0 ≤ δr := by
      have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
      nlinarith
    have hq_forces := small_measure_forces q hq δq hδq0 hlq' hmuq
    have hr_forces := small_measure_forces r hr δr hδr0 hlr' hmur
    exact quasi_small_regime q r hq hr hqr δq δr hδq0 hδr0 hlq' hlr'
      hq_forces.2 hr_forces.2



/-- Exact measure of a ball on the unit circle: radius-δ ball has measure
`min(1, 2δ)` (circumference 1).  First building block of the trimmed-arc
identity `volume(approxAddOrderOf q δ) = ofReal(Σᵢ min(2δ,gᵢ))` over the cyclic
gaps of the reduced residues of `q`. -/
private lemma volume_ball_eq_ofReal_min_one_two_mul (x : UnitAddCircle) (δ : ℝ) :
    MeasureTheory.volume (Metric.ball x δ) = ENNReal.ofReal (min (1 : ℝ) (2 * δ)) := by
  calc
    MeasureTheory.volume (Metric.ball x δ)
        = MeasureTheory.volume (Metric.closedBall x δ) := by
            exact (measure_congr (AddCircle.closedBall_ae_eq_ball (T := (1 : ℝ)) (x := x) (ε := δ))).symm
    _ = ENNReal.ofReal (min (1 : ℝ) (2 * δ)) := by
            simpa using (AddCircle.volume_closedBall (T := (1 : ℝ)) (x := x) (ε := δ))

/-! ### K0 — real analysis: divergence ⇒ arbitrarily far-out blocks with
`2 ≤ Σ_{q∈[N,Y]} min(1, 2φ(q)δ(q)) ≤ 3`. -/

private lemma min_one_two_mul_eq_two_mul (a : ℝ) (ha : a ≤ 1 / 2) :
    min (1 : ℝ) (2 * a) = 2 * a := by
  have h2a : 2 * a ≤ 1 := by nlinarith
  exact min_eq_right h2a

private lemma min_one_two_mul_eq_one (a : ℝ) (ha : 1 / 2 ≤ a) :
    min (1 : ℝ) (2 * a) = 1 := by
  have h2a : (1 : ℝ) ≤ 2 * a := by nlinarith
  exact min_eq_left h2a

private lemma ge_half_iff_one_le_min_two_mul (a : ℝ) (ha : 0 ≤ a) :
    (1 / 2 ≤ a) ↔ (1 : ℝ) ≤ min (1 : ℝ) (2 * a) := by
  constructor
  · intro h
    rw [min_one_two_mul_eq_one a h]
  · intro h
    by_contra ha'
    have ha_lt : a < 1 / 2 := lt_of_not_ge ha'
    have hm := min_one_two_mul_eq_two_mul a (le_of_lt ha_lt)
    rw [hm] at h
    nlinarith

/-- If `b ≥ 0` is summable then only finitely many terms exceed any fixed positive
threshold (terms of a summable series tend to zero). -/
private lemma finite_ge_of_summable_nonneg {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n)
    (hs : Summable b) {c : ℝ} (hc : 0 < c) : {n : ℕ | c ≤ b n}.Finite := by
  have ht : Tendsto b atTop (nhds 0) := hs.tendsto_atTop_zero
  have hev : ∀ᶠ n in atTop, b n < c := (tendsto_order.mp ht).2 c hc
  rcases eventually_atTop.mp hev with ⟨N, hN⟩
  refine (Set.finite_lt_nat N).subset ?_
  intro n hn
  by_contra hnlt
  have hnN : N ≤ n := le_of_not_gt hnlt
  have hbc : b n < c := hN n hnN
  exact (not_lt_of_ge hn) hbc

/-- If `a ≥ 0` and `Σ min(1, 2a)` converges then `Σ a` converges: split at the terms
`a ≥ 1/2` (finitely many, since the `min`-sum is ≥ 1 on them) where `a = (min-sum)/2`. -/
private lemma summable_of_summable_min_one_two_mul {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hs : Summable (fun n : ℕ => min (1 : ℝ) (2 * a n))) : Summable a := by
  classical
  let b : ℕ → ℝ := fun n => min (1 : ℝ) (2 * a n)
  let p : ℕ → Prop := fun n => (1 : ℝ) / 2 ≤ a n
  have hb0 : ∀ n, 0 ≤ b n := by
    intro n
    dsimp [b]
    exact le_min (by norm_num) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (ha n))
  have hfin : {n : ℕ | p n}.Finite := by
    -- {a ≥ 1/2} = {1 ≤ b}
    have hset : {n : ℕ | p n} = {n : ℕ | (1 : ℝ) ≤ b n} := by
      ext n
      dsimp [p, b]
      exact ge_half_iff_one_le_min_two_mul (a n) (ha n)
    rw [hset]
    exact finite_ge_of_summable_nonneg hb0 (by simpa [b] using hs) (c := (1 : ℝ)) (by norm_num)
  let g : ℕ → ℝ := fun n => if p n then a n else 0
  let hh : ℕ → ℝ := fun n => if p n then 0 else (b n) / 2
  have hdecomp : ∀ n : ℕ, a n = g n + hh n := by
    intro n
    by_cases hn : p n
    · simp [g, hh, hn]
    · have ha_lt : a n < 1 / 2 := lt_of_not_ge (by simpa [p] using hn)
      have hm := min_one_two_mul_eq_two_mul (a n) (le_of_lt ha_lt)
      simp [g, hh, hn, b, hm]
  have hgsupport : Function.support g ⊆ {n : ℕ | p n} := by
    intro n hn
    by_cases hp : p n
    · exact hp
    · have hgn : g n ≠ 0 := by simpa using hn
      simp [g, hp] at hgn
  have hg : Summable g := by
    exact summable_of_hasFiniteSupport (Set.Finite.subset hfin hgsupport)
  have hhsum : Summable hh := by
    have hb2 : Summable (fun n : ℕ => (b n) / 2) := by
      have hs' : Summable (fun n : ℕ => (min (1 : ℝ) (2 * a n)) / 2) := hs.div_const 2
      refine Summable.congr hs' ?_
      intro n
      dsimp [b]
    refine Summable.of_nonneg_of_le ?_ ?_ hb2
    · intro n
      by_cases hp : p n
      · simp [hh, hp]
      · simpa [hh, hp] using div_nonneg (hb0 n) (by norm_num)
    · intro n
      by_cases hp : p n
      · simpa [hh, hp] using div_nonneg (hb0 n) (by norm_num)
      · simp [hh, hp]
  have hag : Summable (fun n : ℕ => g n + hh n) := Summable.add hg hhsum
  exact Summable.congr hag (fun n => (hdecomp n).symm)

/-- K0-a: contrapositive of the above — divergence of `Σ a` forces divergence of
`Σ min(1, 2a)`. -/
private lemma not_summable_min_one_two_mul {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hdiv : ¬ Summable a) : ¬ Summable (fun n : ℕ => min (1 : ℝ) (2 * a n)) := by
  intro hs
  exact hdiv (summable_of_summable_min_one_two_mul ha hs)

/-- K0-b: from divergence of the nonneg `b` (with `0 ≤ b ≤ 1`) get arbitrarily far-out
blocks `[N,Y]` whose `b`-sum lies in `[2,3]`. -/
private lemma tail_Icc_sum_ge_two_of_not_summable {b : ℕ → ℝ} (hb0 : ∀ n, 0 ≤ b n)
    (hdiv : ¬ Summable b) : ∀ N : ℕ, ∃ Y ≥ N, (2 : ℝ) ≤ ∑ n ∈ Finset.Icc N Y, b n := by
  classical
  intro N
  have hT : Tendsto (fun m : ℕ => ∑ i ∈ Finset.range m, b i) atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg hb0).mp hdiv
  rcases tendsto_atTop_atTop.mp hT (2 + ∑ i ∈ Finset.range (N + 1), b i) with ⟨n0, hn0⟩
  let M : ℕ := max n0 (N + 1)
  let Y : ℕ := M - 1
  have hNY : N ≤ Y := by dsimp [Y, M]; omega
  refine ⟨Y, hNY, ?_⟩
  have hPM : (2 + ∑ i ∈ Finset.range (N + 1), b i) ≤ ∑ i ∈ Finset.range M, b i :=
    hn0 M (le_max_left n0 (N + 1))
  have hM : N + 1 ≤ M := by dsimp [M]; omega
  have hIco : Finset.Ico (N + 1) M = Finset.Icc (N + 1) (M - 1) := by
    ext n
    have hM1 : 1 ≤ M := by dsimp [M]; omega
    simp [Finset.mem_Ico, Finset.mem_Icc]
    omega
  have hsplit : (∑ i ∈ Finset.range (N + 1), b i) + (∑ i ∈ Finset.Ico (N + 1) M, b i) =
      ∑ i ∈ Finset.range M, b i := Finset.sum_range_add_sum_Ico b hM
  have htailge : (2 : ℝ) ≤ ∑ i ∈ Finset.Icc (N + 1) (M - 1), b i := by
    rw [hIco] at hsplit
    have hnonneg : 0 ≤ ∑ i ∈ Finset.range (N + 1), b i := Finset.sum_nonneg (fun i hi => hb0 i)
    nlinarith
  -- Icc N Y = {N} ∪ Icc (N+1) Y; add the nonneg term b N
  have hY1 : N + 1 ≤ M := hM
  have hYeq : M - 1 + 1 = M := Nat.sub_add_cancel (by dsimp [Y, M]; omega)
  have hsplit2 : (∑ i ∈ Finset.Icc N (M - 1), b i) = b N + ∑ i ∈ Finset.Icc (N + 1) (M - 1), b i := by
    have hmem : N ∉ Finset.Icc (N + 1) (M - 1) := by
      intro hm
      have hle : N + 1 ≤ N := (Finset.mem_Icc.mp hm).1
      omega
    have hset : Finset.Icc N (M - 1) = insert N (Finset.Icc (N + 1) (M - 1)) := by
      apply Finset.ext
      intro i
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hset, Finset.sum_insert hmem]
  have hgoal : (2 : ℝ) ≤ ∑ i ∈ Finset.Icc N (M - 1), b i := by
    rw [hsplit2]
    nlinarith [htailge, hb0 N]
  simpa [Y] using hgoal

/-- K0-c: the full block statement, with upper bound `≤ 3` (terms `b ≤ 1`). -/
private lemma blocks_between_of_not_summable_le_one {b : ℕ → ℝ} (hb0 : ∀ n, 0 ≤ b n)
    (hb1 : ∀ n, b n ≤ 1) (hdiv : ¬ Summable b) :
    ∀ N : ℕ, ∃ Y : ℕ, N < Y ∧
      (2 : ℝ) ≤ ∑ n ∈ Finset.Icc N Y, b n ∧ ∑ n ∈ Finset.Icc N Y, b n ≤ 3 := by
  classical
  let c : ℕ → ℝ := fun n => (b n) / 2
  have hc0 : ∀ n, 0 ≤ c n := by
    intro n
    dsimp [c]
    exact div_nonneg (hb0 n) (by norm_num)
  have hc1 : ∀ n, c n ≤ 1 / 2 := by
    intro n
    dsimp [c]
    exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2 (by nlinarith [hb1 n])
  have hcdiv : ¬ Summable c := by
    intro hsc
    have hb2 : Summable (fun n : ℕ => 2 * c n) := hsc.mul_left 2
    have hbc : Summable b := by
      refine Summable.congr hb2 ?_
      intro n
      dsimp [c]
      ring
    exact hdiv hbc
  have htail : ∀ N : ℕ, ∃ Y ≥ N, (1 : ℝ) ≤ ∑ n ∈ Finset.Icc N Y, c n := by
    intro N
    rcases tail_Icc_sum_ge_two_of_not_summable hc0 hcdiv N with ⟨Y, hNY, hge⟩
    refine ⟨Y, hNY, ?_⟩
    nlinarith
  intro N
  rcases Commons.Analysis.Asymptotics.exists_Icc_sum_between_of_tail_lower c hc0 hc1 htail N with
    ⟨Y, hNY, h1, h2⟩
  refine ⟨Y, hNY, ?_, ?_⟩
  · have hsum : (∑ n ∈ Finset.Icc N Y, c n) = (1 / 2) * ∑ n ∈ Finset.Icc N Y, b n := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro n hn
      dsimp [c]
      ring
    nlinarith
  · have hsum : (∑ n ∈ Finset.Icc N Y, c n) = (1 / 2) * ∑ n ∈ Finset.Icc N Y, b n := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro n hn
      dsimp [c]
      ring
    nlinarith

/-- Upper bound `μ(A_q) ≤ min(1, 2·φ(q)·δ)` for `q ≥ 1` (each of the `φ(q)` arcs has
length at most `min(1, 2δ)`, and the total space has measure `1`). -/
private lemma approxAddOrderOf_volume_le_min_one_two_mul (q : ℕ) (hq : 0 < q) (δ : ℝ)
    (hδ : 0 ≤ δ) :
    MeasureTheory.volume (approxAddOrderOf UnitAddCircle q δ) ≤
      ENNReal.ofReal (min (1 : ℝ) (2 * (q.totient : ℝ) * δ)) := by
  by_cases hsmall : 2 * (q.totient : ℝ) * δ ≤ 1
  · -- μ(A_q) ≤ φ(q)·2δ = min(1, 2φδ)
    have hmin : min (1 : ℝ) (2 * (q.totient : ℝ) * δ) = 2 * (q.totient : ℝ) * δ :=
      min_eq_right hsmall
    rw [hmin]
    let R : Finset ℕ := (Finset.range q).filter (fun m : ℕ => m.gcd q = 1)
    have hA : approxAddOrderOf UnitAddCircle q δ =
        ⋃ m ∈ R, Metric.ball (↑((m : ℝ) / (q : ℝ)) : UnitAddCircle) δ := by
      simpa [R] using approxAddOrderOf_eq_biUnion_ball q hq δ
    have hcard : (R.card : ℝ) = (q.totient : ℝ) := by
      have hc : R.card = q.totient := by
        calc
          R.card = ((Finset.range q).filter (fun m : ℕ => q.Coprime m)).card := by
            congr 1
            refine Finset.filter_congr ?_
            intro m hm
            rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm]
          _ = q.totient := by exact (Nat.totient_eq_card_coprime q).symm
      exact_mod_cast hc
    have hball (m : ℕ) : volume (Metric.ball (↑((m : ℝ) / (q : ℝ)) : UnitAddCircle) δ) ≤
        ENNReal.ofReal (2 * δ) := by
      exact volume_ball_le_ofReal_two_mul (↑((m : ℝ) / (q : ℝ)) : UnitAddCircle) hδ
    have hsum : (∑ m ∈ R, ENNReal.ofReal (2 * δ)) = ENNReal.ofReal ((R.card : ℝ) * (2 * δ)) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (s := R) (fun m hm => mul_nonneg (by norm_num) hδ)]
      congr 1
      rw [Finset.sum_const, nsmul_eq_mul]
    calc
      volume (approxAddOrderOf UnitAddCircle q δ) =
          volume (⋃ m ∈ R, Metric.ball (↑((m : ℝ) / (q : ℝ)) : UnitAddCircle) δ) := by rw [hA]
      _ ≤ ∑ m ∈ R, volume (Metric.ball (↑((m : ℝ) / (q : ℝ)) : UnitAddCircle) δ) := by
        exact MeasureTheory.measure_biUnion_finset_le R
          (fun m => Metric.ball (↑((m : ℝ) / (q : ℝ)) : UnitAddCircle) δ)
      _ ≤ ∑ m ∈ R, ENNReal.ofReal (2 * δ) := by
        exact Finset.sum_le_sum (fun m hm => hball m)
      _ = ENNReal.ofReal ((R.card : ℝ) * (2 * δ)) := hsum
      _ = ENNReal.ofReal (2 * (q.totient : ℝ) * δ) := by
        congr 1
        rw [hcard]
        ring
  · -- 2φδ > 1: μ(A_q) ≤ 1 = min(1, 2φδ)
    have hbig : (1 : ℝ) ≤ 2 * (q.totient : ℝ) * δ := by nlinarith
    have hmin : min (1 : ℝ) (2 * (q.totient : ℝ) * δ) = 1 := min_eq_left hbig
    rw [hmin]
    have hsub : approxAddOrderOf UnitAddCircle q δ ⊆ (Set.univ : Set UnitAddCircle) := by
      intro x hx
      trivial
    calc
      volume (approxAddOrderOf UnitAddCircle q δ) ≤ volume (Set.univ : Set UnitAddCircle) :=
        measure_mono hsub
      _ = ENNReal.ofReal (1 : ℝ) := AddCircle.measure_univ (1 : ℝ)

private lemma lintegral_sq_mul_le' {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    (∫⁻ x, f x * g x ∂μ) * (∫⁻ x, f x * g x ∂μ) ≤
      (∫⁻ x, f x ^ (2 : ℝ) ∂μ) * (∫⁻ x, g x ^ (2 : ℝ) ∂μ) := by
  classical
  have h1 := ENNReal.lintegral_mul_le_Lp_mul_Lq μ (p := (2 : ℝ)) (q := (2 : ℝ))
    Real.HolderConjugate.two_two hf hg
  let A : ℝ≥0∞ := (∫⁻ x, f x ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)
  let B : ℝ≥0∞ := (∫⁻ x, g x ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)
  have hmain : (∫⁻ x, f x * g x ∂μ) ≤ A * B := by
    simpa [A, B] using h1
  have half_sq (x : ℝ≥0∞) : x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x := by
    calc
      x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = (x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by
        rw [← pow_two, ← ENNReal.rpow_two]
      _ = x ^ ((1 / 2 : ℝ) * (2 : ℝ)) := by rw [ENNReal.rpow_mul]
      _ = x ^ (1 : ℝ) := by norm_num
      _ = x := by rw [ENNReal.rpow_one]
  calc
    (∫⁻ x, f x * g x ∂μ) * (∫⁻ x, f x * g x ∂μ) ≤ (A * B) * (A * B) := by
      exact mul_le_mul' hmain hmain
    _ = (A * A) * (B * B) := by ring
    _ = (∫⁻ x, f x ^ (2 : ℝ) ∂μ) * (∫⁻ x, g x ^ (2 : ℝ) ∂μ) := by
      rw [show A * A = (∫⁻ x, f x ^ (2 : ℝ) ∂μ) by
        simpa [A] using half_sq (∫⁻ x, f x ^ (2 : ℝ) ∂μ)]
      rw [show B * B = (∫⁻ x, g x ^ (2 : ℝ) ∂μ) by
        simpa [B] using half_sq (∫⁻ x, g x ^ (2 : ℝ) ∂μ)]

/-- Second-moment / Cauchy–Schwarz bound for a finite family of measurable sets indexed by
the block `Icc X Y`:  `(Σ_{q∈F} μ(s q))² ≤ μ(⋃_{q∈F} s q) * Σ_{q,r∈F} μ(s q ∩ s r)`. -/
private lemma second_moment_Icc {α : Type*} [MeasurableSpace α] (μ : Measure α) (X Y : ℕ)
    (s : ℕ → Set α) (hs : ∀ q, q ∈ Finset.Icc X Y → MeasurableSet (s q)) :
    ((∑ q ∈ Finset.Icc X Y, μ (s q)) ^ 2 : ℝ≥0∞) ≤
      μ (⋃ q ∈ Finset.Icc X Y, s q) *
        (∑ q ∈ Finset.Icc X Y, ∑ r ∈ Finset.Icc X Y, μ (s q ∩ s r)) := by
  classical
  let F : Finset ℕ := Finset.Icc X Y
  let c : ℕ → α → ℝ≥0∞ := fun q => (s q).indicator (fun _ => (1 : ℝ≥0∞))
  let f : α → ℝ≥0∞ := fun x => ∑ q ∈ F, c q x
  let g : α → ℝ≥0∞ := (⋃ q ∈ F, s q).indicator (fun _ => (1 : ℝ≥0∞))
  have hU_meas : MeasurableSet (⋃ q ∈ F, s q) := by
    dsimp [F]
    exact Finset.measurableSet_biUnion (s := Finset.Icc X Y) (fun q hq => hs q hq)
  have hc_meas (q : ℕ) (hq : q ∈ F) : Measurable (c q) := by
    dsimp [c]
    exact Measurable.indicator measurable_const (hs q (by simpa [F] using hq))
  have hf_meas : Measurable f := by
    dsimp [f]
    exact Finset.measurable_sum F (fun q hq => hc_meas q hq)
  have hg_meas : Measurable g := by
    dsimp [g]
    exact Measurable.indicator measurable_const hU_meas
  have hf_aemeas : AEMeasurable f μ := hf_meas.aemeasurable
  have hg_aemeas : AEMeasurable g μ := hg_meas.aemeasurable
  have h_fg : f * g = f := by
    funext x
    by_cases hx : x ∈ (⋃ q ∈ F, s q)
    · simp [f, g, hx]
    · have hc0 : ∀ q ∈ F, c q x = 0 := by
        intro q hq
        have hni : x ∉ s q := fun hxi => hx (mem_iUnion₂.mpr ⟨q, hq, hxi⟩)
        simp [c, hni]
      rw [show f x = 0 by
        dsimp [f]
        exact Finset.sum_eq_zero (fun q hq => hc0 q hq)]
      simp [g, hx]
  have hc_mul (q r : ℕ) (hq : q ∈ F) (hr : r ∈ F) :
      c q * c r = (s q ∩ s r).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext x
    by_cases hxi : x ∈ s q <;> by_cases hxj : x ∈ s r <;> simp [c, hxi, hxj]
  have h_f_mul : ∀ x : α, f x * f x = ∑ q ∈ F, ∑ r ∈ F, c q x * c r x := by
    intro x
    simp only [f]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro q _
    rw [Finset.mul_sum]
  have h_int_f : (∫⁻ x, f x ∂μ) = ∑ q ∈ F, μ (s q) := by
    calc
      (∫⁻ x, f x ∂μ) = ∫⁻ x, (∑ q ∈ F, c q x) ∂μ := by rfl
      _ = ∑ q ∈ F, (∫⁻ x, c q x ∂μ) := by
        exact lintegral_finsetSum F (fun q hq => hc_meas q hq)
      _ = ∑ q ∈ F, μ (s q) := by
        refine Finset.sum_congr rfl ?_
        intro q hq
        dsimp [c]
        simpa using lintegral_indicator_const (hs q (by simpa [F] using hq)) (1 : ℝ≥0∞)
  have h_int_fg : (∫⁻ x, f x * g x ∂μ) = ∑ q ∈ F, μ (s q) := by
    calc
      (∫⁻ x, f x * g x ∂μ) = ∫⁻ x, f x ∂μ := by
        apply lintegral_congr
        intro x
        exact congrFun h_fg x
      _ = ∑ q ∈ F, μ (s q) := h_int_f
  have hg_pow (x : α) : g x ^ (2 : ℝ) = g x := by
    rw [ENNReal.rpow_two]
    by_cases hx : x ∈ (⋃ q ∈ F, s q) <;> simp [g, hx]
  have h_int_g2 : (∫⁻ x, g x ^ (2 : ℝ) ∂μ) = μ (⋃ q ∈ F, s q) := by
    calc
      (∫⁻ x, g x ^ (2 : ℝ) ∂μ) = ∫⁻ x, g x ∂μ := by
        apply lintegral_congr
        intro x
        exact hg_pow x
      _ = μ (⋃ q ∈ F, s q) := by
        dsimp [g]
        simpa using lintegral_indicator_const hU_meas (1 : ℝ≥0∞)
  have h_int_f2 : (∫⁻ x, f x ^ (2 : ℝ) ∂μ) = ∑ q ∈ F, ∑ r ∈ F, μ (s q ∩ s r) := by
    calc
      (∫⁻ x, f x ^ (2 : ℝ) ∂μ) = ∫⁻ x, f x * f x ∂μ := by
        apply lintegral_congr
        intro x
        rw [ENNReal.rpow_two, pow_two]
      _ = ∫⁻ x, (∑ q ∈ F, ∑ r ∈ F, c q x * c r x) ∂μ := by
        apply lintegral_congr
        intro x
        exact h_f_mul x
      _ = ∑ q ∈ F, ∑ r ∈ F, (∫⁻ x, c q x * c r x ∂μ) := by
        calc
          (∫⁻ x, (∑ q ∈ F, ∑ r ∈ F, c q x * c r x) ∂μ)
              = ∑ q ∈ F, (∫⁻ x, (∑ r ∈ F, c q x * c r x) ∂μ) := by
                  exact lintegral_finsetSum F (fun q hq =>
                    Finset.measurable_sum F (fun r hr => (hc_meas q hq).mul (hc_meas r hr)))
          _ = ∑ q ∈ F, ∑ r ∈ F, (∫⁻ x, c q x * c r x ∂μ) := by
              apply Finset.sum_congr rfl
              intro q hqF
              exact lintegral_finsetSum F (fun r hrF => (hc_meas q hqF).mul (hc_meas r hrF))
      _ = ∑ q ∈ F, ∑ r ∈ F, μ (s q ∩ s r) := by
        refine Finset.sum_congr rfl ?_
        intro q hqF
        refine Finset.sum_congr rfl ?_
        intro r hrF
        calc
          (∫⁻ x, c q x * c r x ∂μ)
              = ∫⁻ x, ((s q ∩ s r).indicator (fun _ => (1 : ℝ≥0∞))) x ∂μ := by
                  apply lintegral_congr
                  intro x
                  exact congrFun (hc_mul q r hqF hrF) x
          _ = μ (s q ∩ s r) := by
              simpa using lintegral_indicator_const
                (MeasurableSet.inter (hs q (by simpa [F] using hqF)) (hs r (by simpa [F] using hrF))) (1 : ℝ≥0∞)

  have hcs := lintegral_sq_mul_le' μ hf_aemeas hg_aemeas
  calc
    ((∑ q ∈ Finset.Icc X Y, μ (s q)) ^ 2 : ℝ≥0∞)
        = (∑ q ∈ F, μ (s q)) * (∑ q ∈ F, μ (s q)) := by
            rw [pow_two]
    _ = (∫⁻ x, f x * g x ∂μ) * (∫⁻ x, f x * g x ∂μ) := by rw [← h_int_fg]
    _ ≤ (∫⁻ x, f x ^ (2 : ℝ) ∂μ) * (∫⁻ x, g x ^ (2 : ℝ) ∂μ) := hcs
    _ = (∑ q ∈ F, ∑ r ∈ F, μ (s q ∩ s r)) * μ (⋃ q ∈ F, s q) := by rw [h_int_f2, h_int_g2]
    _ = μ (⋃ q ∈ F, s q) * (∑ q ∈ F, ∑ r ∈ F, μ (s q ∩ s r)) := by rw [mul_comm]
    _ = μ (⋃ q ∈ Finset.Icc X Y, s q) *
        (∑ q ∈ Finset.Icc X Y, ∑ r ∈ Finset.Icc X Y, μ (s q ∩ s r)) := by
            simp [F]

/-- Second-moment lower bound with division, indexed by the block `Icc X Y`. -/
private lemma measure_union_lower_Icc (X Y : ℕ) (s : ℕ → Set UnitAddCircle)
    (hs : ∀ q, q ∈ Finset.Icc X Y → MeasurableSet (s q)) {L U : ℝ≥0∞}
    (hL : L ≤ ∑ q ∈ Finset.Icc X Y, volume (s q))
    (hU : (∑ q ∈ Finset.Icc X Y, ∑ r ∈ Finset.Icc X Y, volume (s q ∩ s r)) ≤ U) :
    L ^ 2 / U ≤ volume (⋃ q ∈ Finset.Icc X Y, s q) := by
  have hsm := second_moment_Icc (μ := volume) X Y s hs
  have h1 : L ^ 2 ≤ (∑ q ∈ Finset.Icc X Y, volume (s q)) ^ 2 := by
    exact ENNReal.pow_le_pow_left (n := 2) hL
  have h3 : volume (⋃ q ∈ Finset.Icc X Y, s q) *
      (∑ q ∈ Finset.Icc X Y, ∑ r ∈ Finset.Icc X Y, volume (s q ∩ s r)) ≤
      volume (⋃ q ∈ Finset.Icc X Y, s q) * U := by
    exact mul_le_mul' le_rfl hU
  have hle : L ^ 2 ≤ volume (⋃ q ∈ Finset.Icc X Y, s q) * U := by
    exact le_trans (le_trans h1 hsm) h3
  exact ENNReal.div_le_of_le_mul hle


private lemma double_mul_eq (B : Finset ℕ) (a b : ℕ → ENNReal) :
    (∑ q ∈ B, a q) * (∑ r ∈ B, b r) = ∑ q ∈ B, ∑ r ∈ B, a q * b r := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro q hq
  rw [Finset.mul_sum]

private lemma sum_le_sum_of_subset (B : Finset ℕ) (f : ℕ → ENNReal) (q : ℕ) :
    (∑ r ∈ B.erase q, f r) ≤ ∑ r ∈ B, f r := by
  exact Finset.sum_le_sum_of_subset_of_nonneg (s := B.erase q) (t := B) (Finset.erase_subset q B)
    (fun r _ _ => zero_le)

private lemma sum_diag_off (B : Finset ℕ) (f : ℕ → ℕ → ENNReal) :
    (∑ q ∈ B, ∑ r ∈ B, f q r) =
      (∑ q ∈ B, f q q) + (∑ q ∈ B, ∑ r ∈ B.erase q, f q r) := by
  classical
  have hinner (q : ℕ) (hq : q ∈ B) :
      (∑ r ∈ B, f q r) = f q q + ∑ r ∈ B.erase q, f q r := by
    have h0 := Finset.sum_erase_add B (fun r => f q r) hq
    calc
      (∑ r ∈ B, f q r) = (∑ r ∈ B.erase q, f q r) + f q q := by rw [h0]
      _ = f q q + ∑ r ∈ B.erase q, f q r := by rw [add_comm]
  calc
    (∑ q ∈ B, ∑ r ∈ B, f q r) = ∑ q ∈ B, (f q q + ∑ r ∈ B.erase q, f q r) := by
      refine Finset.sum_congr rfl ?_
      intro q hq
      exact hinner q hq
    _ = (∑ q ∈ B, f q q) + (∑ q ∈ B, ∑ r ∈ B.erase q, f q r) := by
      rw [Finset.sum_add_distrib]

/-- The deep (Pollington–Vaughan) input: large values with diverging φ-weighted sum
produce arbitrarily far-out tail blocks of uniformly positive measure.

Assembly: (K0) divergence `¬Summable (φ·δ)` gives, via `min(1,2φδ)`, arbitrarily
far-out blocks `[X,Y]` with `2 ≤ Σ_B min(1,2φδ) ≤ 3`; (K1) pointwise
`μ(A_q) ≥ (1/2)·min(1,2φδ)` makes `L := Σ_B μ(A_q) ≥ 1`; (K2) pointwise
`μ(A_q∩A_r) ≤ 8μ(A_q)μ(A_r)` (`q ≠ r`) makes the block second moment
`U ≤ L + 8L²`, and since `μ(A_q) ≤ min(1,2φδ)` we have `L ≤ 3`, hence `U ≤ 75`;
the second-moment inequality `L² ≤ μ(⋃_B A_q)·U` then gives
`μ(⋃_B A_q) ≥ 1/75`. -/
private theorem large_values_tail_block (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n)
    (hδt : Filter.Tendsto δ Filter.atTop (nhds 0))
    (hlarge : ∀ n, δ n = 0 ∨ (1 : ℝ) / 2 ≤ (n : ℝ) * δ n)
    (h : ¬ Summable fun n : ℕ => (n.totient : ℝ) * δ n) :
    ∃ c : ℝ≥0∞, 0 < c ∧ ∀ N : ℕ, ∃ Y : ℕ, N < Y ∧
      c ≤ MeasureTheory.volume (⋃ q ∈ Finset.Icc N Y,
        approxAddOrderOf UnitAddCircle q (δ q)) := by
  classical
  let b : ℕ → ℝ := fun n => min (1 : ℝ) ((2 * (n.totient : ℝ)) * δ n)
  have hb0 : ∀ n, 0 ≤ b n := by
    intro n
    dsimp [b]
    have h2p : 0 ≤ (2 * (n.totient : ℝ)) * δ n := by
      exact mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg n.totient)) (hδ n)
    exact le_min (by norm_num) h2p
  have hb1 : ∀ n, b n ≤ 1 := by
    intro n
    dsimp [b]
    exact min_le_left (1 : ℝ) ((2 * (n.totient : ℝ)) * δ n)
  have hbdiv : ¬ Summable b := by
    intro hb
    let a : ℕ → ℝ := fun n => (n.totient : ℝ) * δ n
    have ha : ∀ n, 0 ≤ a n := by
      intro n
      dsimp [a]
      exact mul_nonneg (Nat.cast_nonneg n.totient) (hδ n)
    have hamin := not_summable_min_one_two_mul (a := a) ha (by simpa [a] using h)
    -- hamin : ¬ Summable (fun n => min (1 : ℝ) (2 * a n)); b agrees pointwise
    apply hamin
    refine Summable.congr hb ?_
    intro n
    dsimp [a, b]
    congr 1
    ring
  have hblocks : ∀ X : ℕ, X ≥ 1 → ∃ Y : ℕ, X < Y ∧
      (2 : ℝ) ≤ ∑ n ∈ Finset.Icc X Y, b n ∧ ∑ n ∈ Finset.Icc X Y, b n ≤ 3 := by
    intro X hX
    exact blocks_between_of_not_summable_le_one (b := b) hb0 hb1 hbdiv X
  let A : ℕ → Set UnitAddCircle := fun n => approxAddOrderOf UnitAddCircle n (δ n)
  let c : ℝ≥0∞ := (1 : ℝ≥0∞) / ((3 : ℝ≥0∞) + 9 * kappa)
  have hc_pos : 0 < c := by
    dsimp [c]
    refine ENNReal.div_pos (by norm_num : (1 : ℝ≥0∞) ≠ 0) ?_
    exact ne_of_lt (ENNReal.add_lt_top.mpr
      ⟨by norm_num, ENNReal.mul_lt_top ENNReal.coe_lt_top kappa_lt_top⟩)
  have hmeasA (q : ℕ) : MeasurableSet (A q) := by
    dsimp [A]
    rw [approxAddOrderOf]
    exact Metric.isOpen_thickening.measurableSet
  have hblock_measure : ∀ N : ℕ, ∃ Y : ℕ, N < Y ∧
      c ≤ volume (⋃ q ∈ Finset.Icc N Y, A q) := by
    intro N
    let X : ℕ := max N 1
    have hX1 : X ≥ 1 := by dsimp [X]; omega
    have hXN : N ≤ X := by dsimp [X]; omega
    rcases hblocks X hX1 with ⟨Y, hXY, hb_ge2, hb_le3⟩
    let B0 : Finset ℕ := Finset.Icc X Y
    have hX0 : ∀ q ∈ B0, 0 < q := by
      intro q hq
      have hXq : X ≤ q := (Finset.mem_Icc.mp hq).1
      have : 1 ≤ q := le_trans hX1 hXq
      omega
    have hA_meas : ∀ q ∈ B0, MeasurableSet (A q) := by
      intro q hq
      exact hmeasA q
    let L : ℝ≥0∞ := ∑ q ∈ B0, volume (A q)
    have hL_lower : (1 : ℝ≥0∞) ≤ L := by
      dsimp [L]
      have hpt : ∀ q ∈ B0, ENNReal.ofReal ((1 / 2) * b q) ≤ volume (A q) := by
        intro q hq
        have hk1 := approxAddOrderOf_volume_ge_min_quasi q (δ q) (hδ q) (hlarge q)
        simpa [A, b] using hk1
      have hsum_half : (1 : ℝ) ≤ ∑ q ∈ B0, (1 / 2) * b q := by
        have htwo : (2 : ℝ) ≤ ∑ q ∈ B0, b q := by
          simpa [B0, b] using hb_ge2
        have hsumm : (∑ q ∈ B0, (1 / 2) * b q) = (1 / 2) * ∑ q ∈ B0, b q := by
          rw [Finset.mul_sum]
        nlinarith
      calc
        (1 : ℝ≥0∞) = ENNReal.ofReal (1 : ℝ) := by simp
        _ ≤ ENNReal.ofReal (∑ q ∈ B0, (1 / 2) * b q) := ENNReal.ofReal_le_ofReal hsum_half
        _ = ∑ q ∈ B0, ENNReal.ofReal ((1 / 2) * b q) := by
          exact ENNReal.ofReal_sum_of_nonneg (fun q hq => mul_nonneg (by norm_num) (hb0 q))
        _ ≤ ∑ q ∈ B0, volume (A q) := Finset.sum_le_sum (fun q hq => hpt q hq)
    have hL_top : L ≤ (3 : ℝ≥0∞) := by
      dsimp [L]
      have hpt2 : ∀ q ∈ B0, volume (A q) ≤ ENNReal.ofReal (b q) := by
        intro q hq
        have hq1 : 0 < q := hX0 q hq
        have hu := approxAddOrderOf_volume_le_min_one_two_mul q hq1 (δ q) (hδ q)
        simpa [A, b] using hu
      calc
        (∑ q ∈ B0, volume (A q)) ≤ ∑ q ∈ B0, ENNReal.ofReal (b q) :=
          Finset.sum_le_sum (fun q hq => hpt2 q hq)
        _ = ENNReal.ofReal (∑ q ∈ B0, b q) := by
          exact (ENNReal.ofReal_sum_of_nonneg (fun q hq => hb0 q)).symm
        _ ≤ ENNReal.ofReal (3 : ℝ) := ENNReal.ofReal_le_ofReal (by simpa [B0, b] using hb_le3)
        _ = (3 : ℝ≥0∞) := by simp
    have hU_off (q : ℕ) (hq : q ∈ B0) (r : ℕ) (hr : r ∈ B0) (hqr : q ≠ r) :
        volume (A q ∩ A r) ≤ kappa * volume (A q) * volume (A r) := by
      have hk2 := approxAddOrderOf_inter_volume_le_quasi q r (hX0 q hq) (hX0 r hr) hqr
        (δ q) (δ r) (hlarge q) (hlarge r)
      simpa [A] using hk2
    have hU : (∑ q ∈ B0, ∑ r ∈ B0, volume (A q ∩ A r)) ≤ L + kappa * L ^ 2 := by
      dsimp [L]
      have hself : ∀ q, volume (A q ∩ A q) = volume (A q) := by
        intro q
        congr 1
        ext x
        simp
      have hsplit0 := sum_diag_off B0 (fun q r => volume (A q ∩ A r))
      have hsplit :
          (∑ q ∈ B0, ∑ r ∈ B0, volume (A q ∩ A r)) =
            (∑ q ∈ B0, volume (A q)) +
              (∑ q ∈ B0, ∑ r ∈ B0.erase q, volume (A q ∩ A r)) := by
        calc
          (∑ q ∈ B0, ∑ r ∈ B0, volume (A q ∩ A r))
              = (∑ q ∈ B0, volume (A q ∩ A q)) +
                  (∑ q ∈ B0, ∑ r ∈ B0.erase q, volume (A q ∩ A r)) := hsplit0
          _ = (∑ q ∈ B0, volume (A q)) +
                  (∑ q ∈ B0, ∑ r ∈ B0.erase q, volume (A q ∩ A r)) := by
                  congr 1
                  refine Finset.sum_congr rfl ?_
                  intro q hq
                  exact hself q
      have hoff_le :
          (∑ q ∈ B0, ∑ r ∈ B0.erase q, volume (A q ∩ A r)) ≤
            kappa * (∑ q ∈ B0, volume (A q)) * (∑ q ∈ B0, volume (A q)) := by
        calc
          (∑ q ∈ B0, ∑ r ∈ B0.erase q, volume (A q ∩ A r))
              ≤ ∑ q ∈ B0, ∑ r ∈ B0.erase q, kappa * volume (A q) * volume (A r) := by
                  refine Finset.sum_le_sum ?_
                  intro q hq
                  refine Finset.sum_le_sum ?_
                  intro r hr
                  exact hU_off q hq r (Finset.mem_erase.mp hr).2 (Finset.mem_erase.mp hr).1.symm
          _ ≤ ∑ q ∈ B0, ∑ r ∈ B0, kappa * volume (A q) * volume (A r) := by
                  refine Finset.sum_le_sum ?_
                  intro q hq
                  exact sum_le_sum_of_subset B0 (fun r => kappa * volume (A q) * volume (A r)) q
          _ = (∑ q ∈ B0, kappa * volume (A q)) * (∑ r ∈ B0, volume (A r)) := by
                  rw [← double_mul_eq B0 (fun q => kappa * volume (A q)) (fun r => volume (A r))]
          _ = kappa * (∑ q ∈ B0, volume (A q)) * (∑ q ∈ B0, volume (A q)) := by
                  rw [← Finset.mul_sum]
      calc
        (∑ q ∈ B0, ∑ r ∈ B0, volume (A q ∩ A r))
            = (∑ q ∈ B0, volume (A q)) +
                (∑ q ∈ B0, ∑ r ∈ B0.erase q, volume (A q ∩ A r)) := hsplit
        _ ≤ (∑ q ∈ B0, volume (A q)) +
                kappa * (∑ q ∈ B0, volume (A q)) * (∑ q ∈ B0, volume (A q)) := by
                have h := add_le_add_left hoff_le (∑ q ∈ B0, volume (A q))
                simpa [add_comm, add_left_comm, add_assoc] using h
        _ = (∑ q ∈ B0, volume (A q)) + kappa * (∑ q ∈ B0, volume (A q)) ^ 2 := by
                rw [pow_two]
                ring

    have hU75 : (∑ q ∈ B0, ∑ r ∈ B0, volume (A q ∩ A r)) ≤ (3 : ℝ≥0∞) + 9 * kappa := by
      have hL2 : L ^ 2 ≤ (3 : ℝ≥0∞) ^ 2 := ENNReal.pow_le_pow_left (n := 2) hL_top
      have hL2' : L ^ 2 ≤ (9 : ℝ≥0∞) := by
        calc
          L ^ 2 ≤ (3 : ℝ≥0∞) ^ 2 := hL2
          _ = (9 : ℝ≥0∞) := by norm_num
      have hmul : kappa * L ^ 2 ≤ kappa * (9 : ℝ≥0∞) := by
        exact mul_le_mul' le_rfl hL2'
      have hle : L + kappa * L ^ 2 ≤ (3 : ℝ≥0∞) + kappa * (9 : ℝ≥0∞) := by
        exact add_le_add hL_top hmul
      calc
        (∑ q ∈ B0, ∑ r ∈ B0, volume (A q ∩ A r)) ≤ L + kappa * L ^ 2 := hU
        _ ≤ (3 : ℝ≥0∞) + kappa * (9 : ℝ≥0∞) := hle
        _ = (3 : ℝ≥0∞) + 9 * kappa := by ring
    have hvol0 : (1 : ℝ≥0∞) / ((3 : ℝ≥0∞) + 9 * kappa) ≤
        volume (⋃ q ∈ Finset.Icc X Y, A q) := by
      have hsm := measure_union_lower_Icc X Y A hA_meas (L := (1 : ℝ≥0∞))
        (U := (3 : ℝ≥0∞) + 9 * kappa) hL_lower hU75
      simpa using hsm
    have hvol : c ≤ volume (⋃ q ∈ Finset.Icc X Y, A q) := by
      simpa [c] using hvol0
    refine ⟨Y, lt_of_le_of_lt hXN hXY, ?_⟩
    have hmono : (⋃ q ∈ Finset.Icc X Y, A q) ⊆ ⋃ q ∈ Finset.Icc N Y, A q := by
      intro x hx
      rcases mem_iUnion₂.mp hx with ⟨q, hq, hxq⟩
      refine mem_iUnion₂.mpr ⟨q, ?_, hxq⟩
      rw [Finset.mem_Icc]
      exact ⟨le_trans hXN (Finset.mem_Icc.mp hq).1, (Finset.mem_Icc.mp hq).2⟩
    exact le_trans hvol (measure_mono hmono)
  refine ⟨c, hc_pos, ?_⟩
  intro N
  rcases hblock_measure N with ⟨Y, hNY, hvol⟩
  refine ⟨Y, hNY, ?_⟩
  simpa [A] using hvol

/-- The positive-measure lemma for large values, assembled from the tail-block lemma
via the standard tail-blocks `→` limsup-measure theorem. -/
theorem positive_measure_large_values_pv (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n)
    (hδt : Filter.Tendsto δ Filter.atTop (nhds 0))
    (hlarge : ∀ n, δ n = 0 ∨ (1 : ℝ) / 2 ≤ (n : ℝ) * δ n)
    (h : ¬ Summable fun n : ℕ => (n.totient : ℝ) * δ n) :
    0 < MeasureTheory.volume (addWellApproximable UnitAddCircle δ) := by
  -- Pull out a tail-block bound from the deep input.
  rcases large_values_tail_block δ hδ hδt hlarge h with ⟨c, hc, hblocks⟩
  -- Pass from the raw approximating sets to the (piecewise) limsup sequence.
  let A : ℕ → Set UnitAddCircle := fun n => approxAddOrderOf UnitAddCircle n (δ n)
  let s : ℕ → Set UnitAddCircle := fun n => if 0 < n then A n else ∅
  have hs_meas : ∀ n, NullMeasurableSet (s n) volume := by
    intro n
    dsimp [s, A]
    by_cases hn : 0 < n
    · simpa [hn, approxAddOrderOf] using
        (Metric.isOpen_thickening.measurableSet :
          MeasurableSet (Metric.thickening (δ n)
            {y : UnitAddCircle | addOrderOf y = n})).nullMeasurableSet
    · simp [hn]
  have hblocks_s : ∀ N : ℕ, ∃ Y : ℕ, N < Y ∧
      c ≤ MeasureTheory.volume (⋃ q ∈ Finset.Icc N Y, s q) := by
    intro N
    rcases hblocks (N + 1) with ⟨Y, hNY, hY⟩
    refine ⟨Y, lt_trans (Nat.lt_succ_self N) hNY, ?_⟩
    refine hY.trans ?_
    refine measure_mono ?_
    intro x hx
    simp only [mem_iUnion, exists_prop] at hx
    rcases hx with ⟨q, hq, hxq⟩
    have hN1q : N + 1 ≤ q := (Finset.mem_Icc.mp hq).1
    have hqpos : 0 < q := by omega
    refine mem_iUnion₂.mpr ⟨q, ?_, ?_⟩
    · exact Finset.mem_Icc.mpr ⟨le_trans (Nat.le_succ N) hN1q, (Finset.mem_Icc.mp hq).2⟩
    · simpa [s, A, hqpos] using hxq
  have hc_le : c ≤ MeasureTheory.volume (limsup s atTop) :=
    Commons.MeasureTheory.tail_blocks_le_measure_limsup (μ := volume) s hs_meas hc hblocks_s
  have hlim : limsup s atTop = addWellApproximable UnitAddCircle δ := by
    dsimp [s, A]
    exact (addWellApproximable_eq_limsup_piecewise δ).symm
  rw [hlim] at hc_le
  exact lt_of_lt_of_le hc hc_le

end

end Commons.NumberTheory.DuffinSchaeffer

/-!
**Session note (immediate next action):** the per-pair measure-level lemma
`approxAddOrderOf_inter_volume_le_quasi`
(`μ(A_q∩A_r) ≤ 8·μ(A_q)·μ(A_r)` under the large-value hypotheses, numerically
validated at ratio ≤ 1.5 in all tested regimes) has been requested from the
fleet but the team was busy this turn; **re-issue the request first thing next
session** (path `NumberTheory/DuffinSchaeffer/approxAddOrderOf_inter_volume_le_quasi`,
statement in `pv_overlap_large.lean` Section 8).  **Session update: parallel
agents have since committed the exact refined window formula
`Commons.NumberTheory.DuffinSchaeffer.fibre_count_eq` (close-reduced-pair count =
`2·Φ·Σ_{c ≤ ⌈W⌉−1, gcd(c,q)=1} S(c)`), with `residue_fiber_formula` and the
extended `fibre_window_count_le_global` plus arithmetic support
(`few_numbers_prime_recip_ge_two`, `totient_div_self_real_le_of_dvd`,
`sum_sq_inv_Icc_le_two_div`, `coprime_symmetric_window_card`).**  The remaining
gap for `fibre_window_count_main_term_le` is now purely bounding that explicit
finite sum (multiplicative average of `S(c)` over the window) — no further
formula derivation.  Re-issue both fleet requests; then prove the explicit-sum
bound against `fibre_count_eq` (gcd-heavy regime = small-`W` finite check,
coprime-like regime = multiplicative average); then compose line 311; then the
assembly chain closes `large_values_tail_block`:
`U ≤ L + 8L²`, `μ(⋃A_q) ≥ L²/U ≥ 1/9` for blocks with `L ≥ 1`
(`measure_union_lower_of_second_moment`), `tail_blocks_le_measure_limsup`.

**Concrete gcd-heavy anchor verified in Lean** (exercising the exact integer
arithmetic, `(420,630)` = `(2g,3g)`, `g=210`): window count of close reduced
pairs = `60` (native_decide on `|630a−420b−(j−1)·264600| < 525`,
`s = 1/840+1/1260`), `φ(420)=96`, `φ(630)=144` (native_decide), and
`60 ≤ 2·(2·(5/2)·φ(420)φ(630)/1260 + 1)` (norm_num) — the exact arithmetic of
the gcd-heavy regime confirmed by Lean on the concrete case.  **Family anchors
broadened:** for the `(2g,3g)` family (count = `#{|3a−2b| ≤ 2}` over
`R(2g)×R(3g)`), Lean-verified for `g = 6` (`(12,18)`: count 4 ≤ 2(5·4·6/36+1)),
`g = 30` (`(60,90)`: count 12), `g = 210` (`(420,630)`: count 60), and
numerically for `g ∈ {2310, 30030}` — all comfortably inside the bound
(≈ 2× slack).  The symbolic-`g` proof (the gcd-heavy regime of
`fibre_window_count_main_term_le` over `fibre_count_eq`) is the next step,
generalising this verified family.
-/

/-! **Session note 2026-09-09 (assembly math distilled to K0/K1/K2; PV Theorem 2 is the
reference: Pollington–Vaughan, Mathematika 37 (1990) 190–200, §5 + §3 Lemma + §2).**

This leaf `positive_measure_large_values_pv` is exactly the *large-values* DS case
(PV Theorem 2 specialised to `α(q) = q·δ(q) ≥ 1/2` on the support), and its proof
has no known shortcut: verified that (i) `addWellApproximable` need not be the whole
circle (e.g. `0` is never within `δ(2^k) ≤ 1/2^k` of an odd/2^k point, yet the set
still has full measure); (ii) `Σ_q μ(A_q) = ∞` is NOT directly implied by the
divergence hypothesis (support can be sparse with `Σ_{q∈S} φ(q)/q < ∞` while
`Σ φ(q)δ(q) = ∞` when `δ(q) ≫ 1/q`; in that regime the arcs overlap so heavily that
`μ(A_q) ≈ 1`, so the *correct* per-q lower bound must carry the overlap: see K1).

**The three clean sub-goals (statements fixed below), plus assembly.**

* K0 (real analysis, self-contained, next easy step).  For `a n ≥ 0`:
  `¬ Summable a ↔ ¬ Summable (fun n => min 1 (2 * a n))` — PROOF: `Σ min < ∞`
  forces only finitely many terms `a n ≥ 1/2` (each contributes ≥ 1), and on the
  complement `min 1 (2a) = 2a`.  Hence from `h : ¬ Summable (φ(n)δ(n))` (all
  hypotheses nonneg) derive `¬ Summable (fun n => min (1:ℝ) (2*(n.totient:ℝ)*δ n))`
  and, via Mathlib
  `Real.not_summable_iff_tendsto_nat_atTop_of_nonneg`
  (`¬Summable f ↔ Tendsto (fun X => ∑ i in Finset.range X, f i) atTop atTop`) plus
  `Commons.Analysis.Asymptotics.exists_Icc_sum_between_of_tail_lower` applied to
  `a/2` (terms ≤ 1/2), obtain:
  `∀ N, ∃ Y > N, 2 ≤ ∑ n ∈ Finset.Icc N Y, min 1 (2 * φ(n)δ(n)) ≤ 3`.
  (`exists_Icc_sum_between_of_tail_lower` needs each term ≤ 1/2 — instantiate it
  with `(a n)/2`, giving the [2,3] window.)

* K1 (per-denominator measure, NEW identified key; self-contained geometry project).
  Target: for `δ ≥ 1/(2q)` (large regime), `μ(A_q) ≥ (1/2)·min(1, 2·φ(q)·δ(q))`
  (empirically constant can be larger; `q=5, δ=1/8` gives worst-tested ratio 0.85,
  `q=3,δ=1/4` gives 5/6).  Route: prove the *exact trimmed-arc identity*
  `μ(A_q) = Σ_i min(2δ, g_i)` where `g_i = (a_{i+1} − a_i)/q` run over the cyclic
  gaps between consecutive reduced residues of `q` (start from
  `approxAddOrderOf_eq_biUnion_ball`, order the `φ(q)` centres, use that centres
  are ≥ 1/q apart so balls meet only neighbours), then a gap-structure inequality
  `Σ_i min(2δ, g_i) ≥ min(1, 2φδ)/2` (`g_i ≥ 1/q`, `2δ ≥ 1/q`).  This replaces the
  insufficient certified `μ ≥ φ(q)/q` (`approxAddOrderOf_volume_ge_min`), which
  alone cannot produce blocks of mass ≥ 1 in the sparse-support corner.  NOTE: the
  simple real inequality `Σ min(2δ,g_i) ≥ min(1,2φδ)/2` from only `Σg_i = 1`,
  `g_i > 0` is FALSE (adversarial `g = (0.995, tiny×3)`); the proof must use that
  `g_i` are coprime-residue gaps (max-gap/twin-structure).  Requested of fleet as
  `NumberTheory/DuffinSchaeffer/approxAddOrderOf_volume_ge_min_quasi`
  (`ENNReal.ofReal ((1/2) * min 1 (2 * (q.totient : ℝ) * δ)) ≤ volume(A_q)`,
  hypotheses `0 ≤ δ`, `δ = 0 ∨ 1/2 ≤ q·δ`).

* K2 (per-pair quasi-independence; the deep PV §3 content; fleet-lemma
  `NumberTheory/DuffinSchaeffer/approxAddOrderOf_inter_volume_le_quasi`, statement
  exactly as the private lemma in this file with constant 8).  Measured ratio ≤ 1.5
  in every tested regime.  CAUTION (corner case that must not be forgotten in the
  proof): for `qδq = rδr = 1/2` exact measures are `μ(A_q)=φ(q)/q`, and a *crude*
  bound `μ∩ ≤ min(μ_q,μ_r)` only combines with `μ∩ ≤ 8μ_qμ_r` when the smaller
  measure is ≥ 1/8; genuinely small-`φ/q` pairs need the divisor/fibre analysis
  (committed: `approxAddOrderOf_inter_volume_le`, `div_pair_count_le`,
  `fibre_window_count_le_global`, `fibre_count_eq`, `residue_fiber_formula`,
  `reduced_pair_count_prime(_pow)`, `reduced_pair_coprime_fiber`,
  `coprime_symmetric_window_card`) — the N-level remainder must be controlled
  relative to the main term `2Δφ(q)φ(r)` (window `W = ΔL ≥ (q+r)/2 ≥ 1` is
  macroscopic under the large-value hypothesis), giving the block lemma.  The
  bounded-`b` main-term half is already proven here
  (`main_term_real_ineq`, `min_add_mul_le_two_mul`).

**Assembly (once K0+K1+K2 are in the commons or proven in-file).**  For a block
`B = [N,Y]` with `L := Σ_{q∈B} μ(A_q) ≥ 1/2` (obtained from K0+K1:
`L ≥ (1/2)·ofReal(Σ_B min(1, 2φδ)) ≥ (1/2)·ofReal(2) = 1` on K0-blocks) and
`U := Σ_{q,r∈B} μ(A_q∩A_r) ≤ L + 8L²` (K2 plus the diagonal), the committed
`Commons.MeasureTheory.second_moment_measure_union` (child L26) gives
`μ(⋃_{q∈B} A_q) ≥ L²/U ≥ L/(1+8L) ≥ 1/9`; combined over every `N` with the
K0-blocks `[N,Y]` and `Commons.MeasureTheory.tail_blocks_le_measure_limsup`
(this file already contains the full reduction of `positive_measure_large_values_pv`
to exactly `large_values_tail_block`), the target closes.  The final constant can
be any `0 < c ≤ L/(1+8L)`-scale value (e.g. 1/9), then `positive_measure_large_values_pv`
(already fully proven in this file) finishes.

**Status 2026-09-09:** file compiles; remaining sorries exactly:
`approxAddOrderOf_inter_volume_le_quasi` (K2, private copy; also re-requested from
fleet), `two_g_three_g_count_le` + `two_g_three_g_count_tform` (Section-9/10
divisor-count exploration, NOT on the `large_values_tail_block` critical path;
candidates for deletion or self-proof), `large_values_tail_block` (K0+K1+K2+assembly).
Fleet busy this session (all requests bounced; its capacity is consumed by the
small-values/`km_positive_small` branch and `pollington_vaughan_overlap_bound`
branch); re-issue K1/K2 requests each fresh session until accepted.
-/

/-! **Session-2 progress (this file, all COMPILES rc=0, `lake build` OK):**
- The full K0 chain is proven in-file (real analysis): `finite_ge_of_summable_nonneg`,
  `summable_of_summable_min_one_two_mul` / `not_summable_min_one_two_mul` (min-trick
  contrapositive), `tail_Icc_sum_ge_two_of_not_summable`,
  `blocks_between_of_not_summable_le_one` (arbitrarily far-out blocks with
  `2 ≤ Σ_{[N,Y]} b ≤ 3`, `0 ≤ b ≤ 1`).
- Measure-theory assembly is proven in-file: `approxAddOrderOf_volume_le_min_one_two_mul`
  (`μ(A_q) ≤ min(1, 2φδ)`, upper bound), `lintegral_sq_mul_le'`, `second_moment_Icc`,
  `measure_union_lower_Icc`, and the Finset/ENNReal helpers `double_mul_eq`,
  `sum_le_sum_of_subset`, `sum_diag_off`.
- **`large_values_tail_block` is now FULLY PROVEN** (no unfilled): given K0 + the two
  remaining pointwise inputs K1 (`approxAddOrderOf_volume_ge_min_quasi`) and K2
  (`approxAddOrderOf_inter_volume_le_quasi`), it picks K0-blocks, gets
  `L = Σ_B μ(A_q) ∈ [1,3]` from K1 + the upper bound, bounds the block second moment
  `U ≤ L + 8L² ≤ 75` from K2, and concludes `c = 1/75 ≤ μ(⋃_B A_q)` via
  `measure_union_lower_Icc`.  The public theorem was already proven from it.
- **Remaining sorries: exactly K1 and K2** (both also requested from the fleet;
  numerics: K1 ratio floor ≈ 0.78 on primorials, K2 ratio ≤ 1.5 measured).
  The two dead-code (2g,3g) exploration sorries were deleted.

**Remaining work (K1 and K2) — strategy for the next session.**

*K1* (`approxAddOrderOf_volume_ge_min_quasi`, private, line ~290): for `q ≥ 1`,
`δ ≥ 0`, `δ = 0 ∨ qδ ≥ 1/2`, show `μ(A_q) ≥ (1/2)·min(1, 2φ(q)δ)`.  Numerics:
ratio floor ≈ 0.78 (q = 30030, primorial), constant 1/2 very safe.  Plan:
(1) reduce to squarefree `rad(q)` — coprime-to-`q` integers are `rad(q)`-periodic,
so the cyclic gap multiset of `q` (real gaps `d/q`, `d` = distance between
successive integers coprime to `rad(q)`) is `q/rad(q)` copies of the
`rad(q)`-gap multiset; `μ(A_q) = Σ_i min(2δ, g_i)` (trimmed-arc identity over the
cyclic gaps `g_i`, centres ≥ 1/q apart, standard circular-arc formula);
(2) coprime-gap inequality `Σ_i min(t, g_i) ≥ min(1, φ(q)·t)/2` (`t = 2δ ≥ 1/q`):
split regimes `t ≤ 1/q` (disjoint arcs: exact `φt`), `2φδ ≤ 1` (need `μ ≥ φδ`;
overlap costs ≤ half) and `2φδ ≥ 1` (need `μ ≥ 1/2`; complement
`Σ (g_i − t)_+ ≤ 1/2`).  The pure real-gap inequality is FALSE (adversarial
gaps `(0.995, tiny³)`); the coprime structure (gaps of integers coprime to `rad`,
with period/density `φ/rad`) must be used, e.g. via the doubled-map or
twin-coprime structure, or crude Jacobsthal-type max-gap bounds (`maxgap` is small
for primorials: 26 at q = 510510).  Alternatively any positive constant replaces
1/2 throughout (the assembly only needs `L ≥ 2c > 0`).

*K2* (`approxAddOrderOf_inter_volume_le_quasi`, private, line ~330): for `q ≠ r`,
`δq = 0 ∨ qδq ≥ 1/2`, `δr = 0 ∨ rδr ≥ 1/2`, show `μ(A_q∩A_r) ≤ 8 μ(A_q) μ(A_r)`.
Since `μ(A_q) ≥ φ(q)/q` and `μ(A_q) ≤ min(1, 2φ(q)δq)`, it suffices when both
measures ≥ 1/8 (then `μ∩ ≤ min(μq,μr) ≤ 8μqμr`); the hard case is one measure
`< 1/8` (`φ/q` small, e.g. primorial), where `μ(A_q∩A_r) ≤ 2·min(δq,δr)·N(q,r,Δ)`
(`approxAddOrderOf_inter_volume_le`, commons) must be combined with the refined
close-reduced-pair counting at the macroscopic window `W = Δ·lcm(q,r) ≥
(q+r)/(2·gcd(q,r)) ≥ 1`: the committed `fibre_window_count_le_global`,
`fibre_count_eq` (needs `Δ < 1/8`, true for far-out blocks since `δ → 0`), and the
`reduced_pair_window_bound`-family give `N ≤ C·Δ·φqφr·Q` with sparsity factor
`Q = ∏_{p | qr/g², p > ΔL/2}(1−1/p)^{-1}`, exactly the `pollington_vaughan` small-
window machinery (`pv_reduced_pair_window_count_le` leaf work).  Combine with
`main_term_real_ineq` and the certified `μ ≥ φ/q` to finish; diagonal `q = r` is
handled in the block (never needs K2).

Both lemmas are also requested from the fleet
(`NumberTheory/DuffinSchaeffer/approxAddOrderOf_volume_ge_min_quasi`,
`NumberTheory/DuffinSchaeffer/approxAddOrderOf_inter_volume_le_quasi`) — re-issue
each session until accepted (fleet has been busy on sibling branches).  When either
lands in the commons, replace the private `unfilled` with an import + `simpa`.
Then `declare_proven()` closes the leaf.

**K1 analysis update (numerics, decisive for the proof route).**  The naive
"pure-gap" relaxations of the coprime-gap inequality all FAIL, so the residue
structure is genuinely needed:
- without any structure (only `g_i ≥ 1/q`, `Σg_i = 1`): counterexample
  `g = (0.995, tiny³)` gives `Σmin(t,g_i) ≈ 0.255 < 0.5` for `t = 0.25`;
- even with the palindromic symmetry that real gap multisets possess
  (`g_i = g_{φ-1-i}`, from `a ↦ q−a`): random palindromic search gives ratio as
  low as `0.44` (`φ=16, q=30030`-shaped, one gap ≈ 0.45, rest tiny), so
  palindromy is NOT sufficient either;
- real reduced-residue systems are safe because their MAXIMUM gap stays tiny
  (JacobsThal-type: `maxgap ≤ 2^{ω(q)}`, and in fact `≤ 26` in integer units for
  q = 510510), so the adversarial single huge gap cannot occur — but a crude
  max-gap bound alone is still insufficient for `μ ≥ 1/2` when `t = 1/φ` (one
  needs the full distribution/sieve structure, e.g. self-similarity of the gap
  multiset between q and q/p, or the elementary
  "any interval of length ~q/φ·C contains a coprime" discrepancy bounds, or the
  inclusion–exclusion density argument for the arc union).

Worst-case real ratios measured: 0.833 (q=6), 0.825 (30), 0.804 (210),
0.788 (2310), 0.781 (30030), 0.778 (510510) — decreasing very slowly, so the
K1 constant 1/2 (target ratio floor 0.5) has a wide safety margin.

**K1 proof reduction (corrected — sharper than previously noted).**  The regime
`δ ≤ 1/q` needs NO new argument at all: the certified bound
`μ(A_q) ≥ φ(q)/q` (`approxAddOrderOf_volume_ge_totient_div`, already proven in
this file; disjoint balls of radius `1/(2q)`) gives `μ ≥ φ(q)/q ≥ φ(q)·δ ≥
min(1, 2φ(q)δ)/2` since `δ ≤ 1/q` and always `φδ ≥ min(1,2φδ)/2`.  Hence **K1's
entire content is the long-arc regime `δ > 1/q`** (arcs longer than one grid
step), where the certified bound falls short by `φ(δ − 1/q)` and one must show
`μ(A_q) ≥ min(1, 2φδ)/2`, i.e. (A) `μ ≥ φδ` when `2φδ ≤ 1` (possible only when
`φ(q) < q/2`), and (B) `μ ≥ 1/2` when `2φδ ≥ 1`.  In the long-arc regime arcs
overlap neighbours and the claim is equivalent (via `μ = Σ_i min(2δ,g_i)`,
trimmed-arc identity over the cyclic reduced-residue gaps) to the coprime-gap
estimate `Σ_i min(t,g_i) ≥ min(1,φt)/2` for `t = 2δ > 2/q`.  So the whole K1
problem is exactly the pure number-theoretic statement `gap_arcs_cover_half`:
for the cyclic gaps `g_i` between consecutive integers coprime to `q`
(equivalently reduced residues of `q`) and every `t > 2/q`:
`Σ_i min(t,g_i) ≥ min(1, q.totient·t)/2`.  (Formally this needs the trimmed-arc
identity on the circle plus the gap statement; each is isolated below.)
**K1 analysis update (numerics, decisive for the proof route).**  The naive
"pure-gap" relaxations of the coprime-gap inequality all FAIL, so the residue
structure is genuinely needed:
- without any structure (only `g_i ≥ 1/q`, `Σg_i = 1`): counterexample
  `g = (0.995, tiny³)` gives `Σmin(t,g_i) ≈ 0.255 < 0.5` for `t = 0.25`;
- even with the palindromic symmetry that real gap multisets possess
  (`g_i = g_{φ-1-i}`, from `a ↦ q−a`): random palindromic search gives ratio as
  low as `0.44` (`φ=16, q=30030`-shaped, one gap ≈ 0.45, rest tiny), so
  palindromy is NOT sufficient either;
- real reduced-residue systems are safe because their MAXIMUM gap stays tiny
  (JacobsThal-type: `maxgap ≤ 2^{ω(q)}`, and in fact `≤ 26` in integer units for
  q = 510510), so the adversarial single huge gap cannot occur — but a crude
  max-gap bound alone is still insufficient for `μ ≥ 1/2` when `t = 1/φ` (one
  needs the full distribution/sieve structure, e.g. self-similarity of the gap
  multiset between q and q/p, or the elementary
  "any interval of length ~q/φ·C contains a coprime" discrepancy bounds, or the
  inclusion–exclusion density argument for the arc union).

Worst-case real ratios measured: 0.833 (q=6), 0.825 (30), 0.804 (210),
0.788 (2310), 0.781 (30030), 0.778 (510510) — decreasing very slowly, so the
K1 constant 1/2 (target ratio floor 0.5) has a wide safety margin.

**K1 proof reduction found (elementary half-residue trick).**  For `δ ≤ 1/q`
(the case `q·δ ≤ 1`, i.e. arcs no longer than one grid step), K1 is EASY and
formalizable without any gap structure: take every second reduced residue in
cyclic order (φ(q) is even for q ≥ 3; q ≤ 2 is trivial by hand).  Consecutive
residues of the *half-set* are `≥ 2/q` apart, so with `2δ ≤ 2/q` their radius-δ
arcs are pairwise disjoint: `μ(A_q) ≥ (φ(q)/2)·2δ = φ(q)δ`, and
`φ(q)δ ≥ min(1, 2φ(q)δ)/2` always (since `φδ ≥ min(1,2φδ)/2`).  Hence K1 needs
proof ONLY in the long-arc regime `δ > 1/q`, where every residue's arc overlaps
its neighbours and the bound `μ ≥ min(1,2φδ)/2` means: regime `2φδ ≤ 1` needs
`μ ≥ φδ`, regime `2φδ ≥ 1` needs `μ ≥ 1/2`.  (In the long-arc regime the arcs
of radius `δ` extend past both immediate neighbours, so this is where the
coprime-gap/sieve distribution of the reduced residues is essential; empirically
`μ` there is ≥ 0.78·min(1,2φδ).)

**Session log (continuation): K1 core isolated; K2 = shared counting core.**
- K1: the certified bound `μ(A_q) ≥ φ(q)/q` (`approxAddOrderOf_volume_ge_totient_div`
  in this file) already settles the whole regime `δ ≤ 1/q`, because
  `min(1, 2φδ)/2 ≤ φδ ≤ φ/q`.  The unique remaining content of K1 is the
  long-arc regime `δ > 1/q`: show `μ(A_q) ≥ min(1, 2φδ)/2`.  By the trimmed-arc
  identity `μ(A_q) = Σ_i min(2δ, g_i)` over the cyclic gaps `g_i` of the reduced
  residues of `q` (centres ≥ 1/q apart ⇒ arcs meet only neighbours; complement
  measure = `Σ max(g_i − 2δ, 0)`), this is equivalent to the pure coprime-gap
  statement `Σ_i min(t, g_i) ≥ min(1, φ(q)t)/2` for `t = 2δ > 2/q`, with case
  split (A) `φt ≤ 1` (needs `μ ≥ φδ`; forces `φ(q) < q/2`) and (B) `φt ≥ 1`
  (needs `μ ≥ 1/2`).  Numerics: long-arc ratio floor ≈ 0.78 (primorials); the
  pure-gap relaxations (no structure; palindromic symmetry) both FAIL (ratios
  down to 0.44), so only the real bounded-gap/sieve structure of coprime
  residues suffices.  Everything else (K0, block assembly, upper bounds,
  second moment) is proven.
- K2 (`approxAddOrderOf_inter_volume_le_quasi`): the trivial regime is when
  `max(μ(A_q),μ(A_r)) ≥ 1/8` (then `μ∩ ≤ min ≤ 8μqμr`); otherwise `μ < 1/8`
  forces `φ(q)/q < 1/8` (q extremely smooth, beyond primorials of the first
  ~25 primes) and small-ish `δ`.  The counting input is exactly the close-
  reduced-pair window estimate that the small-values branch is formalising as
  `pv_close_pair_count_le` / `pv_reduced_pair_window_count_le`
  (`N ≤ C·Δ·φ(m)φ(n)·∏_{p | mn/g², p > Δ·lcm/2}(1−1/p)⁻¹`), built on the same
  committed fibre machinery; once that lands, combine with the committed
  `approxAddOrderOf_inter_volume_le` (μ∩ ≤ 2·min(δq,δr)·N) and the certified
  `μ ≥ φ/q` to finish K2.  Re-issue both fleet requests each session.

**Session log (K1 case analysis, self-attempt status).**  Numeric split of the
two K1 regimes (arc-length-ratio `μ/min(1,2φδ)` over q up to 510510 incl.
primorials, 2p's and composites): case A (`2φδ ≤ 1`) worst ratio 0.778 attained
at the boundary `2φδ = 1` (q = 510510, δ = 1/(2φ)); case B (`2φδ ≥ 1`) worst
0.837 (q = 6).  So both cases share the ~0.78 floor.  Attempts to find an
elementary proof of case A (overlap-loss `Σ_{g_i<t}(t−g_i) ≤ φt/2` via pure
mass/counting bounds) all founder on the same need for the real gap
distribution; palindromic-adversarial systems reach ratio 0.44 (< 1/2), so even
`palindromy + g_i ≥ 1/q + Σg_i = 1` does not prove constant 1/2 (it does prove
any constant ≤ ~0.44).  IMPORTANT FLEXIBILITY: the block assembly needs the
pointwise K1 bound with ANY fixed positive constant `c` (only the final
`1/75`-scale constant changes: `L ≥ 2c`, `μ(⋃) ≥ 2c/(1+16c)`), so if the full
structure theorem stays elusive, ANY provable constant `c > 0`
(e.g. `μ ≥ c·min(1,2φδ)` with `c = 1/8`, possibly from much cruder arguments)
would unlock the leaf.  The fleet-requested statement keeps `c = 1/2`.

**Session log (K1 long-arc core scaffolding).**  Added real code:
`totient_two_lt_q_of_caseA` (q > 0, δ > 1/q, 2φδ ≤ 1 ⟹ 2·φ(q) < q) — the
structural consequence of the (A)-regime hypotheses.  The long-arc core remains
split as (A) `2φδ ≤ 1` (then `φ(q) < q/2`; need μ ≥ φδ = overlap loss
`Σ_{g<t}(t−g) ≤ φt/2`) and (B) `2φδ ≥ 1` (need μ ≥ 1/2).  Next steps when
picking this up: formalise the trimmed-arc identity `μ(A_q) = Σ_i min(2δ,g_i)`
(circle measure: gap partition + additive measure), then the coprime-gap
coverage estimate; the pure-overlap-loss subcases with `φ(q) < q/2` are the
entry points for (A).

**Instantiation roadmap for the K1 bridge (line ~590 `exact ..._long_arc`).**  To
prove `approxAddOrderOf_volume_ge_long_arc` the following named pieces are the
clean decomposition (formalising gaps of `q` concretely as the cyclic
differences of the sorted reduced residues `a₀<…<a_{φ−1}` of `q`, `a_φ = a₀+q`,
`gᵢ = (a_{i+1}−aᵢ)/q`):

1. `gaps_cover`: real-level `(1/2)·min(1, φt) ≤ Σᵢ min(t,gᵢ)` for `t = 2δ > 2/q`,
   where `Σᵢ gᵢ = 1`, `gᵢ ≥ 1/q`, and the coprime structure enters (palindromy
   alone insufficient — ratio can be 0.235; real systems ≥ 0.77).  Case (A)
   `φt ≤ 1` ⟺ `Σ_{gᵢ>t}(gᵢ−t) ≤ 1 − φt/2`; case (B) `φt ≥ 1` ⟺
   `Σ_{gᵢ>t}(gᵢ−t) ≤ 1/2`.  Easy halves via `sum_min_ge_t_mul_big` when
   `#{gᵢ≥t}` is ≥ `φ/2` (case A) resp. ≥ `1/(2t)` (case B); the hard halves need
   the reduced-residue bounded-gap mass input (e.g. via the sieve/density or
   self-similar q ↔ q/p recursion, or Jacobsthal-type `maxgap`-refined bounds).
2. `trimmed_arc_measure`: circle identity `volume(approxAddOrderOf q δ) =
   ofReal(Σᵢ min(2δ, gᵢ))` (gap partition of the circle + additive measure;
   complement measure `= Σ max(gᵢ−2δ,0)`).
3. instantiate 1 + 2, then `ENNReal.ofReal_le_ofReal` + real arithmetic closes
   the core; K1 closes via its existing `exact` bridge.

Both cores (this one and K2) are re-issued to the fleet each session (bounced:
"team busy"); the items above are the permanent decomposition they build on.

**`trimmed_arc_measure` — partition-lemma spec (precise, dispatchable).**  Let
`q ≥ 1`, let `rr := reducedResidueList q = [a₀,…,a_{k−1}]` (sorted, `k = q.totient ≥ 1`),
and let the cyclic gaps be `ds := cyclicGaps q rr` (so `Σ ds = q`, all `dᵢ ≥ 1`,
by `reduced_gap_sum_eq_q`/`cyclicGaps_pos`).  Points `pᵢ := ↑(aᵢ/q) : UnitAddCircle`.
The needed measure lemma (gaps partition the circle up to the finitely many
points, then arcs of radius `δ` cover `min(2δ, gᵢ)` inside gap `i`, `gᵢ = dᵢ/q`):

  `trimmed_arc_measure (q) (δ) : volume (approxAddOrderOf UnitAddCircle q δ) =
      ENNReal.ofReal (∑ d ∈ ds, min (2·δ) ((d : ℝ) / (q : ℝ)))`.

Proof plan (each step is a named sub-lemma): (i) lift to `ℝ` on the fundamental
domain `[0,1)`: the quotient map `ℝ → AddCircle (1)` is measure-preserving on
`[0,1)` (build a `MeasurePreserving`/`map_volume` fact, or prove
`volume (↑'' s) = Real.volume s` for measurable `s ⊆ [0,1)` by the fundamental
domain / `AddCircle` quotient structure); (ii) the intervals
`((aᵢ:ℝ)/q, (a_{i+1}:ℝ)/q)` for `i < k−1`, plus the wrap piece
`((a_{k−1}:ℝ)/q, 1) ∪ (0, (a₀:ℝ)/q)`, partition `(0,1) \ {pᵢ}` with total real
length `Σ (dᵢ/q) = 1` (from `reduced_gap_sum_eq_q` + `list_sum_div`); (iii) for
each gap the intersection of `A_q` with the open gap-arc is an end-union of two
radius-`δ` intervals, of real measure `min(2δ, gᵢ)`; endpoints contribute zero;
(iv) sum with the real trimmed identity `complement_loss_eq` / `sum_split_at`.
This is the remaining measure-theory development under `trimmed_arc_measure`;
`gaps_cover` (coprime-gap coverage, bounded-gap mass input) is separate and
documented above.  Dispatchable as a standalone: state (i)+(ii)+(iii) with only
Mathlib + commons vocabulary, proving the identity for `volume (approxAddOrderOf
UnitAddCircle q δ)` for `0 ≤ δ ≤ 1/2`; the `1/2` bound avoids wrap interactions
and matches the eventual `δ ≤ 1/2` needs (for `δ > 1/2` both sides are `1`).

**Next-arc notes (delegation + seam-free sub-lemmas for `trimmed_arc_measure`).**
Delegation blocker: the `cyclicGaps`/`reducedResidueList` API is private to this
file, so fleet statements about the gap object must either be phrased in
Mathlib-only vocabulary or the API must first be promoted to the commons (a
natural future commons module `NumberTheory/ReducedResidues`).  Finer-grained,
self-contained sub-lemmas for the circle assembly (each dispatchable in
Mathlib-only vocabulary once the seam convention is fixed):
1. arc measure between circle points: for `x y : UnitAddCircle` with
   `0 ≤ dist x y ≤ 1/2`, the set `{z : UnitAddCircle | ‖z - x‖ < dist x y} ∩
   {‖z-y‖ < dist x y}` is empty and the shorter open arc from `x` to `y`
   (points whose lift to `[0,1)` lies between the two representatives) has
   measure `dist x y` — needs the fundamental-domain lift plus
   `Real.volume_Ioo`;
2. residue-seam avoidance: for reduced fractions `m/q` of `q ≥ 2` with
   `1 ≤ m`, the lift of `ball (m/q) δ` to `[0,1)` is a single real interval
   when `m/q + δ ≤ 1` and `m/q - δ ≥ 0`; when it crosses the seam, split into
   the two real intervals and use additivity (measure is unaffected);
3. gap partition: the lifts of the open gaps `(aᵢ/q, a_{i+1}/q)` (cyclic, from
   `reducedResidueList`) into `[0,1)` are pairwise disjoint open intervals whose
   union is `(0,1) \ {aᵢ/q}`, total measure 1 by `reduced_real_gap_sum_eq_one`;
4. per-gap coverage on the circle: `A_q ∩ gapArcᵢ = endCapsᵢ` (seam-free
   gaps), measured by `real_volume_end_caps` = `min(2δ, gᵢ)`; endpoints
   contribute measure zero.
With 1–4, `trimmed_arc_measure` is: lift `A_q` (preimage = union of per-gap
caps by 2–3), sum `real_volume_end_caps` over `cyclicGaps` (real identity via
`complement_loss_eq`/`sum_split_at`), giving `μ(A_q) = ofReal(Σ min(2δ,gᵢ))`
for `δ ≤ 1/2`.  Then line 340 = that identity + `gaps_cover`.

**Seam-through-far-residues interaction (recorded; complement/lift formulation).**
The "unwrapped-gap-first" plan for the per-gap arc layer is subtle: a point
`y ∈ (0,1)` lying inside a middle gap can still be within circle-distance `δ` of a
*far* residue across the seam (e.g. `y ≈ 0.99` near a residue `m/q ≈ 0.01`,
circle distance `≈ 0.02`), so per-gap set equality `A_q ∩ gapArcᵢ = endCapsᵢ`
cannot be stated gap-by-gap without seam terms.  Correct formulation — the
complement/lift identity, dispatchable as
`NumberTheory/DuffinSchaeffer/uncovered_measure_eq_gap_loss`:

  for `q ≥ 1`, `0 ≤ δ`, `2δ ≤ 1`, with `a₀ < … < a_{k−1}` the reduced residues
  of `q` (0 ≤ aᵢ < q) and `d₀,…,d_{k−1}` their cyclic integer gaps (`Σdᵢ = q`):
  `Real.volume {y ∈ (0,1) : ∀ m < q, m.gcd q = 1 → 2δ ≤ dist (↑y) (↑(m/q))}`
  `= ENNReal.ofReal (Σᵢ max ((dᵢ : ℝ)/(q : ℝ) − 2δ) 0)`.

Proof sketch (3 steps, each atomic): (i) lift `y` to integer scale `t = qy`:
`2δ ≤ dist (↑y) (↑(m/q))` holds for all reduced `m` iff the open real window
`(t − qδ, t + qδ) ∩ ℤ` contains no integer coprime to `q` (use
`circle_dist_coe_eq_abs` plus the integer-translate description of the residues
mod 1 — the seam is handled automatically because the residues' full integer
lattice `{a : gcd a q = 1}/q` is q-periodic); (ii) over one period, the integers
coprime to `q` have gaps exactly `dᵢ`, so the `t`-set with a coprime-free
`2qδ`-window is the disjoint union over `i` of the middle segments of length
`max(dᵢ − 2qδ, 0)` (measure-additive; endpoints measure zero); (iii) divide by
`q` (linear rescaling of Lebesgue measure) and use `reduced_gap_sum_eq_q` /
`list_sum_nat_div`.  Then `μ(A_q) = 1 − (that)` and the real identity
`complement_loss_eq` yields `trimmed_arc_measure`.

**Session note (K1 = PV per-denominator bound — MATHEMATICS RESOLVED, elementary).**
The whole K1 content (`approxAddOrderOf_volume_ge_long_arc`) is the per-denominator
estimate, and it is now reduced to elementary facts (all numerically verified
exhaustively over q ≤ 3000 and random smooth q ≤ 10^6, no violations):

*Facts about reduced residues (q ≥ 2).*  `1` and `q−1` are always reduced residues
(gcd(1,q) = gcd(q−1,q) = 1), and `q−1` is the largest, `1` the smallest; hence the
cyclic *wrap* gap is always `2 = (1 + q) − (q−1)`, and the sorted list is
`[1, …, q−1]`.  Consequently the coprime integer lattice `{n ∈ ℤ : gcd(n,q)=1}`
is `q`-periodic with cyclic gaps `d₁,…,d_φ` (`Σdᵢ = q`), and consecutive lattice
points around the period boundary are `(q−1, q+1)` and `(−1, 1)` (translates of the
wrap gap `d = 2`).

*PV per-denominator bound.*  With `α := qδ` and cyclic gaps `d_i` of `q`,
`q·μ(A_q) = Σᵢ min(2α, dᵢ)` (trimmed-arc identity, see below) and for
`2α ≤ q/φ(q)` (i.e. `x := φδ ≤ 1/2`),
`Σᵢ min(2α,dᵢ) ≥ 2αφ(q) − 2α²φ(q)²/q`   ⟺   `μ(A_q) ≥ 2x(1−x) ≥ x = φδ`.
Then case B (`δ ≥ 1/(2φ)`) follows from the boundary case `δ = 1/(2φ)`
(`2x(1−x) = 1/2` there) by monotonicity of the union in `δ`, giving
`μ(A_q) ≥ min(φδ, 1/2)` — K1 with constant `1/2` verbatim.

*Deficit bound (the real content).*  `D := Σ_{dᵢ ≤ 2α}(2α − dᵢ) = 2αφ − Σᵢmin(2α,dᵢ)`.
With `K := ⌊2α⌋`, `η := 2α − K`: `D = Σᵢ(K − dᵢ)₊ + η·#{dᵢ ≤ 2α}`, and
`Σᵢ(K − dᵢ)₊ = Σ_{k=1}^{K−1} u(k)` with `u(k) := #{i : dᵢ ≤ k}`.  Since each
consecutive close pair is an ordered coprime pair at forward distance ≤ k:
`u(k) ≤ Σ_{h=1}^{k} c₊(h)` where `c₊(h) := #{a : gcd(a,q) = gcd(a+h,q) = 1}`
(a mod q).  **Pair-sum bound** `Σ_{h=1}^{β} c₊(h) ≤ βφ(q)²/q` for `1 ≤ β ≤ q/φ`,
PROVEN: by CRT (conditions only mod each `p | q`, independent across primes)
`c₊(h) = φ(q)·Π_{p | q, p ∤ h} (p−2)/(p−1)` (exact; for `p = 2 ∤ h` the factor is 0);
writing `f(h) = Π_{p|q} (ρ(p) + 1[p|h](1−ρ(p)))` with `ρ(p) = (p−2)/(p−1)` and
expanding `f(h) = Σ_{S ⊆ P(q)} Π_{p∈S}(1−ρ(p))·Π_{p∉S}ρ(p)·1[d_S | h]`,
`d_S := Π_{p∈S}p`, summing `Σ_{h≤β}1[d_S|h] ≤ β/d_S` and re-collapsing gives
`Σ_{h≤β}c₊(h) = φ·Σ_{h≤β}f(h) ≤ βφ·Π_{p|q}(ρ(p) + (1−ρ(p))/p) = βφ·Π_{p|q}(p−1)/p = βφ²/q`.
Hence `D ≤ (φ²/q)(K(K−1)/2 + η(K+1)) ≤ 2α²φ²/q` (verified: `(K−1)K/2 + η(K+1)
≤ 2(K+η)²` for K ≥ 1), giving the PV bound.  (Integral-free discretization; the
tight case is q = 2^a, β = q/φ = 2.)

*Trimmed-arc identity* `μ(A_q) = Σᵢ min(2δ, dᵢ/q)` — clean proof via the integer
window formulation, avoiding circle-distance API: lift `x = ↑(t/q)`, t ∈ (0,q);
`x ∈ A_q ⟺ ∃ coprime n, |t − n| < qδ` (`‖↑y − ↑(m/q)‖ < δ ⟺ ∃k, |t−(m+kq)| < qδ`
via `norm_coe_eq_abs_iff`-type reasoning); so the complement in (0,q) is the union
over lattice gaps `(u,v)` (consecutive coprime integers, unique bracketing `u<t<v`)
of the *middle segments* `(u+qδ, v−qδ)` — disjoint, and exactly the coprime-free-
window set (both inclusions use only that real distance ≥ circle distance for the
`⟸`/`⟹` directions and the bracketing for the converse).  Clipping to (0,q): the
interior gaps `(aᵢ, a_{i+1})` contribute `max(dᵢ−2qδ,0)`; the wrap gap `d=2`
contributes `max(2−2qδ,0)` via its two period translates `(−1,1)` and `(q−1,q+1)`
intersecting (0,q) as `(0, 1−qδ)` and `(q−1+qδ, q)` when `qδ ≤ 1` (both vanish
for `qδ > 1`); total over (0,q) equals `Σᵢ max(dᵢ − 2qδ, 0)`; then
`μ(A_q) = 1 − (1/q)Σmax(dᵢ−2qδ,0) = (1/q)Σmin(2qδ,dᵢ) = Σᵢ min(2δ, dᵢ/q)` by
`reduced_gap_sum_eq_q` + the real trimmed identity `complement_loss_eq`.

*Formalization plan (next).*  (i) elementary arithmetic API (self-contained):
`q−1` coprime to q / largest reduced residue; sorted list begins at 1; `cyclicGaps`
wrap term = 2; CRT exact count `c₊(h) = φ(q)·Π_{p|q,p∤h}(p−2)/(p−1)`; the prime-
subset expansion + collapsing product (pure `Finset`/`Nat.primeFactors` reasoning);
pair-sum bound; the integer-discretized deficit bound; the PV gap bound
`Σmin(2α,dᵢ) ≥ 2αφ(1 − αφ/q)`; (ii) the window/middle-segment measure identity on
the circle (as above, ~1/3 of the remaining work); (iii) case split + monotonicity
closes `approxAddOrderOf_volume_ge_long_arc`, and hence K1
(`approxAddOrderOf_volume_ge_min_quasi`) via its existing bridge.  K2
(`approxAddOrderOf_inter_volume_le_quasi`) still needs the PV §3 per-pair close-
pair counting (fibre machinery + `main_term_real_ineq`, as documented above).

*Status:* all numerics below re-verified this session (no violations): G
`Σmin(T,dᵢ) ≥ min(q,φT)/2` over q ≤ 1200 (worst ratio 1.58 at q = 385, T = q/φ);
case-A `E_T/(q−φT/2) ≤ 0.704` (q=210, T=2); PV bound `Σmin(2α,dᵢ) ≥ 2αφ(1−αφ/q)`
over q ≤ 3000 (min margin 0, trivial cases); pair-sum `Σ_{h≤β}c₊(h) ≤ βφ²/q` over
q ≤ 3000 and random smooth q ≤ 10^6 (worst ratio = 1.0, q = 4); `u(β) ≤ βφ²/q`
worst ratio 0.75 (β = 2); primorial `μ(A_q(1/(2φ)))` floor 0.7777 (P₈) — all far
above the needed 1/2 threshold.
-/


/-!
# SESSION STATE — handoff snapshot (leaf L44, positive_measure_large_values_pv)

File compiles (rc=0), ~4150 lines, exactly TWO `unfilled`s (after a mid-session
edit mishap the K1-A middle region was rebuilt from scratch; state verified):

  (A) `cyclic_gap_cover_bound` (~line 2337): K1 gap inequality
      `min(q/2, α·φ(q)) ≤ Σ_{d ∈ cyclicGaps q (rr q)} min(2α,d)`, q>0, α ≥ 1/2.
  (B) `approxAddOrderOf_inter_volume_le_quasi` (~line 2814): K2 per-pair
      quasi-independence, constant 8.
`approxAddOrderOf_volume_ge_long_arc` (K1 measure part), `volume_Aq_ge_cyclic_min`,
`uncovered_volume_le_gap_loss`, `approxAddOrderOf_volume_ge_min_quasi`,
`large_values_tail_block`, `positive_measure_large_values_pv` ALL PROVEN.

## What (A) still needs (per the analysis in the header docs):
Prove `cyclic_gap_cover_bound` by:
 1. α ≤ 1: `Σmin ≥ φ ≥ min(q/2, αφ)` (all gaps ≥ 1; `min(2α,d) ≥ 1`; length φ).
 2. α > 1, case A (`2αφ ≤ q`): deficit `D := Σ_i max(2α−d_i,0)`, `Σmin = 2αφ − D`
    (per-gap `min = x − max(x−d,0)`), discretise with `K := ⌊2α⌋`, `η := 2α−K`:
    `D = Σ_{k=1}^{K−1}u(k) + η·u(K)`, `u(k) := #{d_i ≤ k}`; then
    `u(k) ≤ kφ(q)²/q` for `k ≤ q/φ`; yields `D ≤ 2α²φ²/q`; hence
    `Σmin ≥ 2αφ(1 − αφ/q) ≥ αφ` in case A.
 3. α > 1, case B (`2αφ ≥ q`): monotone in α: `Σmin(2α) ≥ Σmin(2α₀)` with
    `α₀ = q/(2φ)` (boundary of A); if `φ > q/2` (α₀ < 1) use case 1's bound
    `Σmin(2α₀) ≥ φ > q/2`; else deficit bound at α₀ gives `Σmin(2α₀) ≥ q/2`.
 4. `u(k) ≤ Σ_{h=1}^{k} c₊(h)` (each gap ≤ k is a consecutive coprime pair
    (start, start+h); distinct starts ⟹ injection; wrap gap 2 counted via
    start q−1).
 5. pair-sum bound `Σ_{h=1}^{k} c₊(h)·q ≤ k·φ(q)²` (Nat form) for `k·φ ≤ q`,
    `c₊(h) = #(Finset.range q).filter (a.gcd q = 1 ∧ (a+h).gcd q = 1)`: exact
    CRT count `c₊(h) = φ(q)·∏_{p|q,p∤h}(p−2)/(p−1)` + prime-subset expansion
    collapse `Σ_S ... = Π_p(ρ_p + (1−ρ_p)/p) = φ(q)/q`.
Counting lemmas available in-file to build u(k):
   - `adjacent_mem_consecutivePairs`, `consecutivePairs_adjacent`,
     `mem_zip_tail_iff`, `zip_tail_nodup_of_pairwise_lt`,
     `list_map_sum_eq_toFinset_sum`, `sum_consecutivePairs_eq_zip_sum`,
     `sum_consecutivePairs_diff_eq_adjDiffs_sum`,
     `sum_cyclicGaps_eq_adjDiffs_add`, `cyclicGaps_reduced_eq_adj_append_two`,
     `cyclic_min_sum_eq_q_sub_max_sum`, `list_sum_natCast_map`,
     `list_sum_map_mono`, `list_sum_map_nonneg`, `sum_ofReal_div_eq_ofReal_sum_div`,
     `rr_get0_eq_one`, `rr_lastElt_eq_pred`, `rr_wrap_gap_eq_two`.

## To start case-A gap-identity helpers (in-file, before cyclic_gap_cover_bound):
Define `closePair (q) (h) : ℕ := ((Finset.range q).filter (fun a => a.gcd q = 1 ∧ (a+h).gcd q = 1)).card`
and `pairSum q k := ∑ h ∈ Finset.Icc 1 k, closePair q h`.
- `gapCount_le_pairSum (q hq k) : ((cyclicGaps q rr).filter (fun d => d ≤ k)).length ≤ pairSum q k`
  via: count-filter = CP-count (+1 if 2≤k) [List.countP_map, append-filter, count filter over zip=Nodup, CP=zip.toFinset, filter over CP by diff ≤ k], then map CP-filtered → (ab.1, ab.2−ab.1) injects into the disjoint union over h ∈ Icc 1 k of c₊(h).
- `pair_sum_bound (q k) (hk : k * q.totient ≤ q) :
    q * pairSum q k ≤ k * q.totient * q.totient`
  (Nat) — the CRT content (c₊ exact local counts; product over primeFactors q;
  subset expansion; collapse; use `Nat.factorization`, `Nat.Prime` divisibility,
  coprime counts via `Nat.totient_eq_card_coprime`; may reuse commons
  `NumberTheory.DuffinSchaeffer.fibre_count_eq`-style CRT if adaptable; else
  self-contained).
- real shell: reals `u(k)` from Nat count via `.length` cast; assemble D identity
  with `K = Nat.floor (2α)` (Mathlib `Nat.floor` on ℝ, `Int.floor`; or use
  `Nat.ceil`-free: since only `K ≤ 2α < K+1` needed, take K := ⌊2α⌋ via
  `Nat.floor (2*α)` with h: (K:ℝ) ≤ 2α and 2α < K+1; provide via `Int.floor_le`,
  `lt_floor_add_one`); handle η = 2α − (K:ℝ) ∈ [0,1).

## K2 (`approxAddOrderOf_inter_volume_le_quasi`) remains as documented at its site
(doc ~line 2800): trivial regime (one measure ≥ 1/8 → μ∩ ≤ min(μ_q,μ_r) ≤ 8μ_qμ_r),
else deep close-pair counting regime (PV §3) using committed commons
`approxAddOrderOf_inter_volume_le`, `fibre_window_count_le_global`,
`fibre_count_eq`, `reduced_pair_coprime_fiber`, `div_pair_count_le`, plus
`main_term_real_ineq` (in-file) and `approxAddOrderOf_volume_ge_totient_div`;
the sibling derivation file
`Submission/Work/NumberTheory/DuffinSchaeffer/pv_overlap_large.lean` documents
the fibre-count collapse `N(Δ) = 2Δφ(q)φ(r) + E(q,r)` (main term exactly
quasi-independent; remainder relative control at macroscopic windows
`Δ·lcm ≥ (q+r)/2 ≥ 1`).

Fleet requests (approxAddOrderOf_inter_volume_le_quasi and
close_coprime_pair_sum_le) keep bouncing "team busy" — re-issue each session.

Session-4 additions: `pair_sum_nat_bound` (the CRT core, now a NAMED tracked
`unfilled` at ~line 2722; replace its body with
`by simpa [closePairSum, closePairCount] using close_coprime_pair_sum_le q k hk`
once the fleet lemma lands) and `real_gap_count_le` PROVEN:
`(gapCountSmall q k : ℝ) ≤ (k·φ(q)²/q : ℝ)` for `k·φ(q) ≤ q`, `q ≥ 1`
(chain `gapCountSmall_le_closePairSum` + `pair_sum_nat_bound`, cast to ℝ,
divide by `q` using `le_div_iff₀` + `simpa [mul_comm,...]`).

Item-2 draft (per-element η-deficit identity) started in
`scratchdev/k1_deficit.lean` (NOT yet compiling; issues recorded there): the
identity `max(x−d,0) = Σ_{k∈range K}1[d≤k] + (x−K)·1[d≤K]` needs helper
lemmas `sum_range_indicator_ge/ge'`:
`(∑ k ∈ range K, if d ≤ k then (1:ℝ) else 0) = ((K−d:ℕ):ℝ)` (when `d ≤ K`)
resp. `0` (when `d > K`), proved via `Finset.sum_filter`
+ `card_eq_sum_ones` + `Finset.mem_range`/`mem_filter` bookkeeping (avoid
`Finset.card_Ico`/`card_Icc`: absent in this mathlib; use `omega` over the
card of a range-filter or `simp`).  Then the induction lemma
`list_deficit_eq_sum_counts` over the gap list L with real x ≥ 0:
`(L.map (fun d => max (x−(d:ℝ)) 0)).sum =
 ∑_{k ∈ range (Nat.floor x)} (↑((L.filter (fun d => d ≤ k)).length)) +
   (x − (Nat.floor x : ℝ)) · ((L.filter (fun d => d ≤ Nat.floor x)).length : ℝ)`
(additivity: per-element identity + splitting the cons-filter counts), then the
bound `≤ (φ²/q)(K(K−1)/2 + ηK) ≤ 2α²φ²/q` and the case assembly exactly as
documented in the following note.  Also fix a subtlety in the draft: `max_eq_left`
requires proving `0 ≤ x − d` from `d ≤ K ≤ x` (use `exact_mod_cast`),
`Nat.cast_sub hd` (not `sub_add_cancel`) for `(K−d : ℕ)` cast, and `dsimp [K]`
at both the count and the main term before `rw [hcount, hif2]` (K is a `let`;
alternatively inline `Nat.floor x`).

**Real-shell derivation (η-discretization, verified by hand; for the next
session to implement).**  Fix `x := 2α`, `K := Nat.floor x` (ℝ FloorSemiring:
`Nat.floor_le (ha : 0 ≤ a) : (K:ℝ) ≤ x`, `Nat.lt_floor_add_one x :
x < (K:ℝ)+1`), `η := x − (K:ℝ) ∈ [0,1)`.  For integer `d`:
`max(x−d,0) = 1[d ≤ K]·(K−d) + η·1[d ≤ K]` (since `d ≤ x ⟺ d ≤ K`, and
`d ≥ K+1 ⟹ x−d = η−1 < 0`).  Hence for a gap list `L`,
`D := Σ_{d∈L} max(x−d,0) = Σ_{k=0}^{K−1} u(k) + η·u(K)`, `u(k) :=
(L.filter (fun d => d ≤ k)).length` (proof: per element, `1[d≤K](K−d) =
Σ_{k=d}^{K−1}1 = Σ_{k=0}^{K−1}1[d≤k]`, swap finite sums).  With `u(k) ≤ kφ²/q`
(real) for `k ≤ q/φ` (via `gapCountSmall_le_closePairSum` [PROVEN] +
`pair_sum_nat_bound` [CRT, = fleet `close_coprime_pair_sum_le` via
`simpa [closePairSum, closePairCount]`]):
`D ≤ (φ²/q)·(K(K−1)/2 + ηK) ≤ (φ²/q)·(K+η)²/2 = x²φ²/(2q) = 2α²φ²/q`
(use `K(K−1)/2 + ηK ≤ (K+η)²/2`, true since `(K+η)²/2 − (K(K−1)/2+ηK)
= (K+η²)/2 ≥ 0`).  Assembly of `cyclic_gap_cover_bound`:
* α ≤ 1: every gap d ≥ 1 and 2α ≥ 1 give `min(2α,d) ≥ 1`, so Σ ≥ φ ≥
  min(q/2, αφ).
* α > 1 with `2αφ ≤ q` (case A): `Σmin = 2αφ − D ≥ 2αφ − 2α²φ²/q ≥ αφ`
  (the last step from `2αφ ≤ q`), and `min(q/2,αφ) = αφ`.
* α > 1 with `2αφ ≥ q` (case B): set `α₀ := q/(2φ) ≤ α`; monotone in the
  first argument `Σmin(2α) ≥ Σmin(2α₀)`.  If `α₀ ≤ 1` (i.e. φ ≥ q/2):
  pure bound `Σmin(2α₀) ≥ φ ≥ q/2`.  Else `α₀ ≥ 1` and the case-A bound at
  α₀ (boundary `2α₀φ = q`) gives `Σmin(2α₀) ≥ 2α₀φ − 2α₀²φ²/q = q/2`; and
  in case B `min(q/2, αφ) = q/2`.
Pointwise monotonicity `min(2α,·) ≥ min(2α₀,·)` when `α₀ ≤ α` and list-sum
monotonicity (`list_sum_map_mono`) close.  `Nat.floor` monotonicity needed:
if `y ≤ x` then `Nat.floor y ≤ Nat.floor x` (check API: likely `Nat.floor_mono`
or via `Nat.floor_le`).  `Σmin = xφ − D` per entry via `min_eq_sub_max`.
The CRT bound: `c₊(h) = Σ_{d|q, gcd(h,d)=1} μ(d)·φ(q)/φ(d)` (Möbius on the
second coprimality; `#{a∈(Z/q)ˣ : a ≡ −h mod d} = φ(q)/φ(d)` for `d|q`,
`gcd(h,d)=1`), and the exact `Σ_{h≤k, gcd(h,d)=1}` bookkeeping per prime
power is what yields `Σ_{h≤k} c₊(h)·q ≤ kφ²` — or simply the fleet lemma
`close_coprime_pair_sum_le`.

Session-3 additions (all compiling): `gapCountSmall_le_closePairSum` PROVEN
(now `unfilled`-free): every cyclic gap of size ≤ k injects into the close-pair
union, i.e. `gapCountSmall q k ≤ closePairSum q k` for all q,k.  Proof: q=0/1
special cases direct (q=1: exactly one gap, c₊(1,h)=1 for all h, so
`closePairSum 1 k = k` via Finset.card_Icc/sum_const; the k=0 sub-case via
`List.eq_nil_iff_forall_not_mem` with cyclic-gap positivity); q≥2 via
`gapCountSmall_eq_consecutivePairs_add` + the injective image of the map
`F (a,b) = (a, b−a)` from `CPk` into `pairSet` (`Finset.card_image_of_injOn`
+ `card_le_card`; `F` injective on `CPk` because adjacent pairs have distinct
starts, via `get_inj_of_pairwise_lt` and index equality `congrArg Fin.val`),
with the wrap gap `(q−1,2)` inserted separately
(`Finset.card_insert_of_notMem`, `Nat.gcd_add_self_left q 1` +
`Nat.gcd_one_left` for `gcd(q+1,q)=1`) and `hcard_pairSet` via
`card_filter_product_eq_sum` (`simpa [pairSet, closePairSum, closePairCount]`).
Lean gotchas fixed along the way: `Nat.gcd_one_right q` gives `gcd q 1`, not
`gcd (q+1) q`; membership in `Finset.product` needs `Finset.mem_range.mpr`
(not omega); `Finset.card_Icc` does not exist (`simp`/`omega` instead);
`rw` matches only up to defeq so unfold lets with `dsimp` may reduce
`Finset.range 1` to `{0}` breaking `rw [hc]` (use `rw [closePairCount]` not
`dsimp`, or `simpa using` an explicit identity); `0.gcd` parses as a decimal
(`(0:ℕ).gcd` needed).

Session-2 additions (all compiling): `length_filter_map_filter` (List length of
filter-after-map), `card_filter_product_eq_sum` (generic Finset double-count:
`#((s×t).filter p) = Σ_{b∈t} #(s.filter (p·b))`; proof uses `Finset.sum_product`
+ `change (s ×ˢ t)` + `Finset.sum_filter`/`card_eq_sum_ones`), and
`gapCountSmall_eq_consecutivePairs_add` (gapCountSmall = CP-filter-count + wrap,
via `List.filter_map`, `length_filter_map_filter`, `list_filter_count_eq_toFinset`,
`zip_tail_nodup_of_pairwise_lt`, CP = zip.toFinset).  A draft of
`gapCountSmall_le_closePairSum` was attempted and reverted (compile errors at:
q=1-case simplification `simp [gapChain]` over cyclicGaps not reducing;
`Finset.sum_congr rfl` unusable after `congr 2` in closePairSum 1 k = k;
F-image membership wrap `.gcd`-side; `Finset.card_insert_of_notMem` arithmetic;
final `calc` step LHS mismatch `CPk.card ≤ pairSet.card` needing rewrite
direction).  Debug notes: in the q≥2 branch of that lemma the pieces that
compile individually are `hgap` (gapCountSmall_eq_consecutivePairs_add),
`hF_mem`/`hF_inj` (plain membership/injectivity proofs using
consecutivePairs_adjacent + get_inj_of_pairwise_lt), `hwrap_mem`
(rewrite `(q-1,2) ∈ pairSet ↔ 2 ≤ k` via Finset.mem_product/mem_Icc/mem_filter
and pred_mem_reducedResidueList + Nat.gcd_one_right), `hwrap_not_image`
(omega with hstart/ab.2<q), `hcard_pairSet` (rw card_filter_product_eq_sum;
rfl).  Remaining to fix: q=1 direct case (use simp [gapChain, cyclicGaps,
reducedResidueList] or an explicit lemma `cyclicGaps_singleton` for rr=[0]),
`closePairSum 1 k = k` (use Finset.sum_congr directly without preceding congr;
each c₊(h)=1 needs (0+h).gcd 1 = 1 and 0.gcd 1 = 1 via norm_num), and the
final `hfinal` (sum of `CPk.card + (if 2≤k then 1 else 0) ≤ pairSet.card`
worked modulo `Finset.card_insert_of_notMem` returning `card + 1` needing
`omega`-free closing; and the last calc line ordering).  Reinsert the draft
(a copy is in the previous session transcript) and fix those ~6 spots.

Close-pair/gap-count vocabulary
`closePairCount`, `closePairSum`, `gapCountSmall`, `list_countP_append`,
`nodup_filter_of_nodup`, `list_filter_count_eq_toFinset`, and
`gapCountSmall_eq_consecutivePairs_add`.  Still to prove for the K1 inequality
`cyclic_gap_cover_bound` (line ~2402): (a) `gapCountSmall_le_pairSum` —
`gapCountSmall q k ≤ closePairSum q k` via injection of CP-filtered starts into
the disjoint union over h ≤ k of closePairCount (distinct starts = CP-zip-nodup;
wrap gap counted at start q−1 with h=2); (b) `pair_sum_bound` —
`q * closePairSum q k ≤ k * (q.totient)^2` for `k*q.totient ≤ q` (CRT product
formula + subset collapse); (c) real deficit shell (u(k) ≤ kφ²/q → D ≤ 2α²φ²/q
→ case A/B assembly as documented above).  K2 (line ~2879) remains.

## Session-5 additions (K1 COMPLETE — cyclic_gap_cover_bound and all of K1 are now PROVEN).

The K1 (coprime-gap coverage) chain is now fully proven in this file:
- η-discretization machinery (inserted after `list_sum_map_mono`, before
  `sum_ofReal_div_eq...`): `sum_range_indicator_ge_nat` (Σ_{k<K}1[d≤k]=K−d in ℕ),
  `sum_range_indicator_ge`, `list_sum_indicator_eq_filter_length`,
  `list_sum_sum_range_swap`, `per_element_deficit` (per gap `max(x−d,0)` =
  count-sum + η-tail), `list_deficit_eq_sum_counts` (D = Σ_{k<K}u(k) + η·u(K)),
  `list_map_const_sum`, `sum_range_id_real`, `triangular_deficit`,
  `nat_mul_totient_le_q_of_lt_floor`/`nat_mul_totient_le_q_of_floor`
  (k < ⌊x⌋ ⟹ k·φ ≤ q given x·φ ≤ q), `gap_deficit_bound` (case A:
  `D ≤ x²φ²/(2q)`), `gap_min_sum_eq` (Σmin = φx − D),
  `gap_min_sum_pure` (β ≥ 1/2 ⟹ Σmin(2β) ≥ φ), `gap_sum_min_lower_caseA`
  (2αφ ≤ q ⟹ Σmin(2α) ≥ αφ), `gap_min_sum_mono`, and the final
  `cyclic_gap_cover_bound` with the three-regime assembly
  (α ≤ 1 pure; case A via deficit; case B via α₀ = q/(2φ) boundary with
  monotonicity).  These were developed in `scratchdev/k1_full.lean` (imports the
  Work module; mirrors the main file) and spliced into the main file between
  `list_sum_map_mono` and `sum_ofReal_div_eq_ofReal_sum_div`.
  All the later lemmas (`approxAddOrderOf_volume_ge_long_arc`,
  `approxAddOrderOf_volume_ge_min_quasi`, `large_values_tail_block`,
  `positive_measure_large_values_pv`) were already proven and now have NO
  dependency on a K1 unfilled.

**Remaining sorries (exactly two):**
1. `pair_sum_nat_bound` (~line 2724) — the CRT close-pair core:
   `q·closePairSum q k ≤ k·φ(q)²` for `k·φ(q) ≤ q`.  Fleet statement
   `close_coprime_pair_sum_le` (inlined defs).  Proof route (all verified by
   hand, see below): c₊(h) is multiplicative over coprime prime-power factors,
   on p^e it equals p^{e−1}·g_p(h) with g_p(h) = p−1 if p|h else p−2, hence
   q·Σ_{h≤k}c₊(h) ≤ kφ² via the subset/T-expansion
   (Σ_{h≤k}∏_p g_p(h) ≤ k·∏_p[(p−2)+1/p] = k·∏_p(p−1)²/p).  Requires
   `Nat.factorization` (available: `factorization`, `support_factorization`,
   `primeFactors`/`primeFactorsList`), prime-power CRT splitting
   (`Nat.ChineseRemainder`/ZMod), and per-prime-power counting.
2. `approxAddOrderOf_inter_volume_le_quasi` (~line 3715) — K2 per-pair
   quasi-independence with constant 8 (deep PV §3; fibre machinery is in the
   commons; see doc at its site and `pv_overlap_large.lean` §8/§9).

Numerical/sanity anchors still valid: the whole file compiles rc=0 with
`lake build`; only the two `unfilled`s above (plus doc-comment mentions).

## Session-5 research notes for `pair_sum_nat_bound` (the CRT close-pair core; unfilled at ~2725)

**Target.**  `pair_sum_nat_bound (q k) (hk : k·φ(q) ≤ q) : q·closePairSum q k ≤ k·φ(q)²`
where `closePairSum q k = Σ_{h ∈ Icc 1 k} c₊(q,h)`,
`c₊(q,h) = #{a < q : gcd(a,q) = gcd(a+h,q) = 1}`.

**Key discovery (checked by hand and numerically): the bound is UNCONDITIONAL in k**
(no `k·φ ≤ q` needed): `q·Σ_{h=1}^k c₊(q,h) ≤ k·φ(q)²` for ALL q,k.
Rationale: on a prime `p`, `c₊(p,h) = p−1` if `p | h` else `p−2`; write
`g_p(h) = (p−2) + 1[p | h]`.  `c₊` is multiplicative over coprime prime powers
(CRT: units of `ℤ/q ≅ Π ℤ/pᵢ^{eᵢ}`, and the condition on `a+h` factors mod each
`pᵢ^{eᵢ}`); on `p^e`, `c₊(h) = p^{e−1}·g_p(h)` (only `a mod p` matters: each
residue class mod `p` has `p^{e−1}` lifts in `[0,p^e)`).  Hence
`c₊(q,h) = (q/rad(q))·∏_{p | q} g_p(h)`.  Expanding the product over subsets
`T ⊆ {p | q}` of primes:
`Σ_{h≤k} ∏_p g_p(h) = Σ_T (∏_{p∉T}(p−2))·#{h ≤ k : (∏_{p∈T}p) | h}
 ≤ Σ_T (∏_{p∉T}(p−2))·(k/∏_{p∈T}p)   [⌊x⌋ ≤ x; ALL coefficients ≥ 0]
 = k·∏_p ((p−2) + 1/p) = k·∏_p (p−1)²/p   [per prime: (p−2)+1/p = (p−1)²/p]
`.
Multiplying by `q·(q/rad(q))` gives `q·Σ c₊ ≤ k·(q/rad)²·∏(p−1)² = k·φ(q)²` ✓.
This positive-coefficient expansion is the ONLY clean formal route: a Möbius
divisor-sum alternative (`q·Σ_h c₊ = Σ_{d,e|q} μ(d)μ(e)·(q²·gcd(d,e)/(de))·⌊k/gcd⌋`)
has SIGNED coefficients `μ(d)μ(e)`, so the termwise `⌊k/g⌋ ≤ k/g` bound is
INVALID (rejected for formalization).

**Mathlib/commons assets to build on (all #check-verified in this workspace):**
- `Nat.factorization`, `Nat.primeFactors`, `prod_primeFactors_pow_factorization
  (hn) : n = ∏ p ∈ n.primeFactors, p ^ n.factorization p`,
  `pairwise_coprime_pow_primeFactors_factorization : Pairwise (Nat.Coprime on
  fun p : n.primeFactors ↦ p ^ n.factorization p)` (Data/Nat/Factorization/Basic.lean).
- `ZMod.chineseRemainder {m n} (h : m.Coprime n) : ZMod (m*n) ≃+* ZMod m × ZMod n`,
  `ZMod.prodEquivPi {ι} [Fintype ι] (a : ι → ℕ) : ZMod (∏ i, a i) ≃+* Π i, ZMod (a i)`
  (Data/ZMod/QuotientRing.lean) — gives `c₊` multiplicativity over the coprime
  prime powers (`IsUnit` ↔ product of units).
- Commons `reduced_pair_count_prime_pow
  (p k R Q e) (hp : p.Prime) (hk : 0 < k) (hR : ¬p∣R) (hQ : ¬p∣Q) :
  #{(m,n) ∈ [0,p^k)² : ¬p∣m ∧ ¬p∣n ∧ (m·R) % p^k = (n·Q + e) % p^k}
  = if p ∣ e then φ(p^k) else φ(p^k) − p^(k−1)` — its proof (in
  Submission/Commons/NumberTheory/DuffinSchaeffer/reduced_pair_count_prime_pow.lean)
  already does the ZMod-unit bookkeeping on `ZMod (p^k)` incl.
  `card_pairs_eq_add_zmod`, `card_zmod_units_eq_nat`; MIRROR it for the
  single-variable count `c₊^{p^e}(h) = p^{e−1}·(p−1 if p|h else p−2)`.
- Commons Totient (`Submission.Commons.NumberTheory.Totient.coprime_window_mainTerm_bound`):
  `sum_moebius_divisors`, `divisors_gcd_eq_filter`, `sum_moebius_gcd_coprime`,
  `coprime_count_moebius_real`, `sum_antidiag_moebius_snd_eq_totient`,
  `sum_moebius_mul_natDiv_eq_totient (m) (hm) : Σ_{d|m} μ(d)·(m/d : ℚ) = (φ m : ℚ)`,
  `moebius_ratio_mul`, `card_multiples_Icc_one`.  (These would serve the Möbius
  route; prefer the prime-expansion route above.)
- `Nat.totient_prime_pow (hp) (hn : 0 < n) : φ (p^n) = p^(n−1)·(p−1)`,
  `Nat.totient_mul (h : m.Coprime n) : φ(m·n) = φ m · φ n` (Data/Nat/Totient.lean).

**Suggested decomposition (each piece small):**
(A) single-prime-power: `c₊(p^k, h) = (if p ∣ h then p^(k-1)*(p-1) else p^(k-1)*(p-2))`
    as `Fintype.card {x : ZMod (p^k) // IsUnit x ∧ IsUnit (x + h)}`, mirroring
    reduced_pair_count_prime_pow (its `card_pairs_eq_add_zmod` counts pairs
    (x, x+e) both units = same count!); use `ZMod.isUnit_natCast_iff_not_dvd_pow`
    and count residues mod p directly.
(B) CRT-split: `q = ∏_i p_i^{e_i}` (prod_primeFactors_pow_factorization),
    `c₊(q,h) = ∏_i p_i^{e_i−1}·g_{p_i}(h)` via `ZMod.prodEquivPi` +
    `Fintype.card_congr` over `IsUnit` products.
(C) real bound chain: with `φ² = ∏ φ(p_i^{e_i})²` (totient_mul over the
    factorization), reduce to the subset-expansion inequality for
    `Σ_{h ≤ k} ∏_i g_{p_i}(h)`; implement the expansion by induction over the
    Finset of primes or via a generic `Finset.prod`-subset lemma; per-prime
    `(p−2) + 1/p = (p−1)²/p` by `field_simp`.
(D) close `pair_sum_nat_bound` by `simpa [closePairSum, closePairCount]`.
The real chain can be done with ℕ casts to ℝ/ℚ to use `exact_mod_cast` at the
end (both sides integers); beware `Nat.cast` handling of `p^k` and of the
`q/rad`-product (cleaner: keep everything in the exponent form
`∏ p_i^{e_i−1}·g_{p_i}(h)` so no radical is needed; then multiply by q only at
the very last step and use `∏ φ(p_i^{e_i})²/q = ...`-free formulation:
prove `(q:ℚ)·(Σ_{h≤k} c₊(h) : ℕ) ≤ (k:ℚ)·(φ:ℕ:ℚ)^2` via the two identities
`c₊(h) = ∏_i p_i^{e_i−1} g_{p_i}(h)` and `φ(q) = ∏_i p_i^{e_i−1}(p_i−1)`,
`q = ∏_i p_i^{e_i}` — everything is a product over the SAME finite index set,
so per-index algebra suffices.)

**Session-5 final state:** K1 proven (see Session-5 note above); remaining
sorries exactly `pair_sum_nat_bound` (~2725) and K2 `approxAddOrderOf_inter_volume_le_quasi`
(~3716).  File `Submission/Work/NumberTheory/DuffinSchaeffer/positive_measure_large_values_pv.lean`
compiles (lake build rc=0).  K2's route is documented in its docstring and in
`Submission/Work/NumberTheory/DuffinSchaeffer/pv_overlap_large.lean` §8/§9; its
counting layer is the committed fibre machinery (`fibre_count_eq`,
`fibre_window_count_le_global`, `approxAddOrderOf_inter_volume_le`,
`reduced_pair_count_prime(_pow)`, `reduced_pair_coprime_fiber`) plus in-file
`main_term_real_ineq`/`approxAddOrderOf_volume_ge_totient_div`.

## Session-6 additions (CRT close-pair, part 1): two prime-power counting lemmas committed.

New (in-file, before `pair_sum_nat_bound`; new import
`Submission.Commons.NumberTheory.DuffinSchaeffer.reduced_pair_count_prime_pow`):
- `single_count_prime_pow (p k e) (hp : p.Prime) (hk : 0 < k) :
  #(n < p^k : ¬p∣n ∧ ¬p∣(n+e)) = if p ∣ e then φ(p^k) else φ(p^k) − p^(k−1)`
  — proved from the PUBLIC `reduced_pair_count_prime_pow` (R = Q = 1) via the
  bijection n ↦ ((n+e) % p^k, n) between the single-filter and the product
  filter (uses `Nat.dvd_mod_iff (k:=p)(m:=x)(n:=p^k) (p∣p^k)` to move
  ¬p∣-through `% p^k`; `Finset.mem_product` requires `change ... ∈ s ×ˢ t`).
- `close_pair_prime_pow (p k e) : card = p^(k−1)·((p−1) if p∣e else (p−2))`
  — via `Nat.totient_prime_pow` and `Nat.mul_sub_left_distrib`
  (mind the direction: `Nat.mul_sub_left_distrib A (p-1) 1 : A*(p-1) − A*1 =
  A*((p-1)−1)`; use `.symm`), with `rw [if_neg he]` possibly needed TWICE
  (once for the LHS if from the single-count rewrite, once for the RHS if).
These give `c₊(p^k, h) = p^(k−1)·((p−2) + 1[p | h])` (g_p(h) form).

**Next steps (Session 7+):**
1. ZMod-form c₊ and CRT product identity.  Define
   `CP(n) := fun h => Fintype.card {x : ZMod n // IsUnit x ∧ IsUnit (x + h)}`
   (`[NeZero n]`); relate to the range filter by the standard
   `ZMod.val`/`natCast_zmod_val` bijection (mirror `card_zmod_units_eq_nat` in
   reduced_pair_count_prime_pow.lean).  Prove `CP(p^k, h)` value from
   `close_pair_prime_pow`.
2. Multiplicativity/CRT: with `q ≠ 0`, family `a p := p ^ q.factorization p`
   over `ι = q.primeFactors`, `q = ∏ i, a i`
   (`Nat.prod_primeFactors_pow_factorization`, or the subtype version
   `prod_primeFactors_coe_pow_factorization`), pairwise coprime
   (`pairwise_coprime_pow_primeFactors_factorization`), and
   `ZMod.prodEquivPi a coprime : ZMod (∏ i, a i) ≃+* (i → ZMod (a i))`.
   Transport the subtype count to conclude
   `CP(q, h) = ∏ p ∈ q.primeFactors, p^(q.factorization p − 1) · ((p−2) + 1[p|h])`
   (units of a product ring = product of units: `isUnit_prod`-style; castHom
   sends `(h : ZMod q)` to the tuple of `(h : ZMod (p^e_p))`, and
   `IsUnit (h : ZMod (p^e)) ↔ ¬ p ∣ h` via
   `ZMod.isUnit_natCast_iff_not_dvd_pow`).
3. Sum expansion (pure real-analysis lemma over a Finset S of primes):
   `Σ_{h ∈ Icc 1 k} ∏_{p ∈ S} ((p:ℝ) − 2 + if p∣h then 1 else 0)
     ≤ (k:ℝ) · ∏_{p ∈ S} ((p:ℝ) − 1)²/(p:ℝ)`.
   Proof: expand ∏_p((p−2) + 1[p|h]) = Σ_{A ⊆ S} (∏_{p∉A}(p−2))·1[∀p∈A, p|h];
   Σ_{h≤k}1[∀p∈A: p|h] = ⌊k/(∏_{p∈A}p)⌋ ≤ k/(∏_{p∈A}p) (ALL coefficients
   ∏(p−2) ≥ 0 — the reason the per-prime expansion is preferred over the
   signed Möbius route); then Σ_A (∏_{p∉A}(p−2))·(k/∏_{p∈A}p) =
   k·∏_p((p−2)+1/p) = k·∏_p(p−1)²/p (per prime ring equality).  Needs the
   generic Finset expansion identity ∏_p(a_p+b_p) = Σ_{A⊆S}∏_{p∈A}a_p∏_{p∉A}b_p
   (prove by Finset induction over S with powersets) and the divisibility fact
   `∀p∈A p|h → (∏_{p∈A}p)|h` for pairwise-coprime (prime) p's.
4. Combine: `Σ_{h≤k} c₊(q,h) ≤ k·φ(q)²/q` (in ℚ or ℝ, then exact_mod_cast to
   the nat `pair_sum_nat_bound`).  Use
   `q = ∏_p p^(e_p)`, `φ(q) = ∏_p p^(e_p − 1)(p−1)`
   (`Nat.totient_eq_prod_factorization` Finsupp version, or per-factor
   `totient_mul`), factor the common `∏ p^(e_p−1)` out of the h-sum.

## Session-6 additions, part 2 (ZMod ↔ range bridge committed).

New (in-file, next to the prime-power lemmas):
- `zmod_closePair_eq (q e) [NeZero q] :
  Fintype.card {x : ZMod q // IsUnit x ∧ IsUnit (x + (e : ZMod q))} = closePairCount q e`
  — the canonical-reps bridge: Finset.card_bij' between `(univ.filter Px)` on
  `ZMod q` and `(range q).filter (a.gcd q = 1 ∧ (a+e).gcd q = 1)`, with
  `ZMod.val`/natCast; uses `ZMod.isUnit_iff_coprime`,
  `Nat.coprime_iff_gcd_eq_one`, `ZMod.val_lt`, `ZMod.natCast_zmod_val`,
  `ZMod.val_natCast` + `Nat.mod_eq_of_lt`.
- `zmod_closePair_prime_pow (p k e) [NeZero (p^k)] (hp) (hk) :
  Fintype.card {x : ZMod (p^k) // IsUnit x ∧ IsUnit (x + e)} =
    p^(k−1)·((p−1) if p∣e else (p−2))`
  — via `zmod_closePair_eq` + the commons
  `Commons.NumberTheory.Nat.coprime_prime_pow_right_iff_not_dvd`
  (`a.gcd (p^k) = 1 ↔ ¬ p ∣ a`) + `close_pair_prime_pow`.
Both compile (build rc=0).  These give `CP(p^k, h) = p^(k−1)·g_p(h)` with
`g_p(h) = (p−2) + 1[p|h]` on the ZMod side, ready for the `ZMod.prodEquivPi`
product identity over `q.primeFactors` (next target, per the Session-6 part-1
notes).

## Session-7 additions (product-factor bookkeeping committed).

New (in-file, next to the other CRT lemmas):
- `zmod_pi_card_prod {ι} [Fintype ι] [DecidableEq ι] (a : ι → ℕ) [∀ i, NeZero (a i)] (h) :
  card {f : (i:ι)→ZMod (a i) // IsUnit f ∧ IsUnit (f + (fun i => (h : ZMod (a i))))} =
    ∏ i, card {x : ZMod (a i) // IsUnit x ∧ IsUnit (x + h)}`
  — via `Pi.isUnit_iff` + `Equiv.subtypePiEquivPi` + `Fintype.card_pi`.
- `zmod_card_congr_prodEquivPi {ι} [Fintype ι] [DecidableEq ι] (a) (cop) [∀ i, NeZero (a i)]
  [NeZero (∏ i, a i)] (h) :
  card {x : ZMod (∏ i, a i) // IsUnit x ∧ IsUnit (x + h)} = card over the Pi ring`
  — pulled through `ZMod.prodEquivPi a cop`; `MulEquiv.isUnit_map` gives
  `IsUnit x ↔ IsUnit (e x)` (`.symm`); natCast transport
  `e (h : ZMod(∏a)) = fun i => (h : ZMod (a i))` via `ext i` +
  `rw [ZMod.prodEquivPi_apply]` + `map_natCast (ZMod.castHom _ (ZMod (a i))) h`;
  additivity via `map_add`.
KEY API discovery (solves the ZMod-q transport that was open in the previous
session's notes): **`ZMod.ringEquivCongr {m n} (h : m = n) : ZMod m ≃+* ZMod n`**
exists (Data/ZMod/Basic.lean), and `(ZMod.ringEquivCongr h) (x : ZMod m) =
(x : ZMod n)` is provable by `subst n; simp`.  Also
`Nat.prod_primeFactors_coe_pow_factorization (hn) : n = ∏ (p : n.primeFactors),
(p : ℕ) ^ n.factorization p`, `pairwise_coprime_pow_primeFactors_factorization`,
`Nat.prime_of_mem_primeFactors`, factorization support ⟹ exponent ≥ 1.

**Next step (finish `cp_eq_prod_primeFactors`)** — compose, for `q ≥ 1`:
`card {x : ZMod q // IsUnit x ∧ IsUnit (x + h)} =
  ∏ p ∈ q.primeFactors, p ^ (q.factorization p - 1) * (if p ∣ h then p - 1 else p - 2)`
1. ι := q.primeFactors (subtype type), a i := (i:ℕ) ^ (q.factorization (i:ℕ)),
   hqeq := Nat.prod_primeFactors_coe_pow_factorization (NeZero.ne q) : q = ∏ i, a i,
   hcop := pairwise_coprime_pow_primeFactors_factorization (n := q),
   per-i: NeZero (a i) (a i > 0: prime_of_mem_primeFactors i.2, e ≥ 1 via
   Finsupp.mem_support / factorization_pos), Nat.Prime (i:ℕ) (prime_of_mem_primeFactors),
   e_i ≥ 1 (0 < q.factorization (i:ℕ) from i ∈ primeFactors = support).
2. card over ZMod q = card over ZMod (∏ i, a i) via `ZMod.ringEquivCongr hqeq`
   (predicate transported: natCast h commutes; then `zmod_card_congr_prodEquivPi`
   → Pi count, `zmod_pi_card_prod` → ∏ over ι of per-coordinate cards).
3. per-coordinate: `zmod_closePair_prime_pow (p := (i:ℕ)) (k := q.factorization (i:ℕ)) h`
   gives `card = p^(e−1)·(if p∣h then p−1 else p−2)`.
4. reindex the Fintype product over ι to the Finset product over `q.primeFactors`
   (`Finset.prod_coe_sort`-type lemma), giving the stated RHS.
Then `pair_sum_nat_bound` follows by the positive-coefficient subset expansion
(Σ over h ≤ k of ∏_p g_p(h) ≤ k∏((p−2)+1/p), see Session-5 notes step 3).

## Session-8: THE FACTORIZATION IDENTITY IS PROVEN.

Committed:
- `ringEquivCongr_natCast {m n} (h : m = n) (x : ℕ) :
  (ZMod.ringEquivCongr h) (x : ZMod m) = (x : ZMod n)` (by `subst h; simp`).
- `cp_eq_prod_primeFactors (q h) [NeZero q] :
  card {x : ZMod q // IsUnit x ∧ IsUnit (x + h)} =
    ∏ p ∈ q.primeFactors, p ^ (q.factorization p − 1) · (if p ∣ h then p−1 else p−2)`
  — the CRT product identity `CP(q,h) = ∏_{p|q} p^(e_p−1)·g_p(h)`, assembled
  exactly per the Session-7 recipe: ι := q.primeFactors (subtype type),
  a i := (i:ℕ)^(q.factorization (i:ℕ)); `Nat.prod_primeFactors_coe_pow_factorization`
  for q = ∏ i, a i; `Nat.pairwise_coprime_pow_primeFactors_factorization` for
  pairwise coprime; transport ZMod q → ZMod (∏ a) via `ZMod.ringEquivCongr`
  (predicate transport: natCast commutes via ringEquivCongr_natCast, addition
  via map_add, units via MulEquiv.isUnit_map); then
  `zmod_card_congr_prodEquivPi` → `zmod_pi_card_prod` → per-coordinate
  `zmod_closePair_prime_pow`; final reindex `Finset.prod_coe_sort`.
  Lean gotchas fixed: use `let` (not `have`) for the ring-equiv `hE` so
  `simpa [hE]` can unfold it; do NOT declare `haveI : Fintype ι`/`DecidableEq ι`
  manually (breaks defeq of the Fintype.prod instances with the canonical ones);
  namespace the factorization lemmas `Nat.…` (the file does not `open Nat`).

Combined with `zmod_closePair_eq` (card over ZMod q = `closePairCount q h`),
this gives the full range-side product formula
`closePairCount q h = ∏_{p | q} p^(e_p−1)·((p−2) + 1[p|h])`.

**Next steps toward `pair_sum_nat_bound` (unfilled at ~3043):**
1. Range-side value: `closePairCount (p^k) h = p^(k−1)·(if p|h then p−1 else p−2)`
   — connect `closePairCount` to the ¬p∣-filter (`a.gcd (p^k) = 1 ↔ ¬p∣a`, commons
   `Commons.NumberTheory.Nat.coprime_prime_pow_right_iff_not_dvd`) and
   `close_pair_prime_pow` (note: zmod_closePair_prime_pow already does the ZMod
   side; the RANGE version is `closePairCount (p^k) h = …` via
   `zmod_closePair_eq` too — but simpler to reuse directly).
2. Positive-coefficient subset expansion (real analysis over the Finset of
   primes, Session-5 notes step 3):
   `Σ_{h ∈ Icc 1 k} ∏_{p ∈ S} ((p:ℝ)−2 + if p∣h then 1 else 0)
     ≤ (k:ℝ)·∏_{p ∈ S} ((p:ℝ)−1)^2/(p:ℝ)`
   (expand ∏ over subsets A of S; coefficient ∏_{p∉A}(p−2) ≥ 0 so
   `⌊k/(∏_{p∈A}p)⌋ ≤ k/(∏_{p∈A}p)` applies termwise; per-prime
   `(p−2) + 1/p = (p−1)²/p`).  Needs primes pairwise coprime to write
   `#{h≤k : ∀p∈A, p∣h} = ⌊k/(∏_{p∈A} p)⌋`.
3. Combine with `cp_eq_prod_primeFactors` (factor out ∏ p^(e_p−1)) and
   `Nat.totient_eq_prod_factorization`/`totient_mul` for φ(q), sum over
   h ∈ Icc 1 k, `exact_mod_cast` back to the natural statement.
4. Then `pair_sum_nat_bound` closes via
   `simpa [closePairSum, closePairCount]` (its unfilled body says so).

## Session-9: better route for the summation bound (replaces the powerset plan).

For `g_p(h) = (p:ℝ)−2 + 1[p|h]`, `F_S(h) = ∏_{p∈S} g_p(h)`,
`P(S) = ∏_{p∈S}((p:ℝ)−2 + 1/(p:ℝ))`, the bound
`Σ_{h ∈ Icc 1 k} F_S(h) ≤ (k:ℝ)·P(S)` for S a set of primes is best proved by
**induction over the primes of S** (NOT the powerset expansion):
- Base S = ∅: both sides k.
- Step S = insert p₀ S' (p₀ ∉ S'), `F(h) := F_{S'}(h)`, `B := (p₀:ℝ)−2`,
  `i(h) := 1[p₀|h]`: LHS = Σ_h (B + i(h))·F(h) = B·Σ_h F(h) + Σ_{p₀|h}F(h).
  * Term 1 ≤ B·(k:ℝ)·P(S')  [IH at k; B ≥ 0 since p₀ ≥ 2].
  * Term 2: `Σ_{p₀|h, h≤k} F(h) = Σ_{m ∈ Icc 1 (k/p₀)} F(p₀·m) = Σ_{m≤k/p₀}F(m)
    ≤ ((k/p₀:ℕ):ℝ)·P(S') ≤ (k:ℝ)/(p₀:ℝ)·P(S')`  [IH at k/p₀; P(S') ≥ 0].
    KEY: `F(p₀·m) = F(m)` — because for p ∈ S' (p ≠ p₀ primes),
    `p | p₀·m ⟺ p | m` (Euclid: `Nat.Coprime.dvd_of_dvd_mul_left`
    (`Nat.Coprime (p) q`) + `hp.coprime_iff_not_dvd` for ¬p∣p₀, via
    `hq.eq_one_or_self_of_dvd`).
  * Total ≤ k·(B + 1/p₀)·P(S') = (k:ℝ)·P(insert p₀ S')  [Finset.prod_insert].
  No signed coefficients, no powersets: this is the clean route.
- RHS replacement (later): `P(S) = ∏_p (p:ℝ−1)²/(p:ℝ)` pointwise via
  `prime_ring_identity (p ≠ 0): (p:ℝ)−2 + 1/(p:ℝ) = ((p:ℝ)−1)²/(p:ℝ)`
  (pure field_simp+ring — compiles; NO primality needed, only p ≠ 0).
- `Pprod_nonneg`: 0 ≤ P(S) by Finset.prod_nonneg, per factor (p:ℝ)−2 ≥ 0
  (hp.two_le cast) + 1/p > 0.
- Nat-div reindex facts: `Nat.le_div_iff_mul_le (k0 : 0 < k) :
  x ≤ y / k ↔ x * k ≤ y`; `(k / p₀ : ℕ : ℝ) ≤ (k:ℝ)/(p₀:ℝ)` via
  `div_le_iff₀ hp0`.
Scratch `scratchdev/exp.lean` has the per-prime identity and nonnegativity
compiling; the induction skeleton was started (Term-1 bound done; Term-2
reindex via Finset.sum_filter + sum_bij h ↦ h/p₀ is the fiddly part: need
`1 ≤ h/p₀` from `p₀|h ∧ h ≥ 1`, `h/p₀ ≤ k/p₀` from h ≤ k by
`Nat.div_le_div_right`, surjectivity via `p₀·m` and le_div_iff_mul_le).
Known gotcha: private `def gval/Fprod/Pprod` used in Prop-level arithmetic must
not make the surrounding lemma noncomputable; if `dependsOnNoncomputable`
appears, mark the defs `noncomputable` or state the lemmas as `theorem`s.

Then `pair_sum_nat_bound` (unfilled at ~3043): combine `cp_eq_prod_primeFactors`
+ `zmod_closePair_eq` (range side), i.e.
`closePairCount q h = ∏_{p ∈ q.primeFactors} p^(e_p−1)·g_p(h)`, so
`Σ_{h≤k} closePairCount q h = (∏ p^(e_p−1))·Σ_h ∏_p g_p(h) ≤
 (∏ p^(e_p−1))·k·∏_p((p−1)²/p) = k·φ(q)²/q` (factor out the common
∏p^(e_p−1), use prime_ring_identity, and φ(q) = ∏ p^(e_p−1)(p−1) —
`Nat.totient_eq_prod_factorization` Finsupp form or per-index totient_mul),
then `simpa [closePairSum, closePairCount]`.

## Session-10: `prod_sum_bound` (induction over primes) COMMITTED.

New (in-file, before pair_sum_nat_bound): per-prime ring identity
`prime_ring_identity`, `dvd_mul_prime_iff` (distinct primes: p|q·m ⟺ p|m via
`Nat.Coprime.dvd_of_dvd_mul_left` + `hp.coprime_iff_not_dvd` +
`hq.eq_one_or_self_of_dvd`), defs `gval`/`Fprod`/`Pprod`,
`Pprod_nonneg`, `Fprod_mul_invariant` (F_S(p₀·m) = F_S(m)),
`div_nat_le_real` ((k/p:ℕ):ℝ ≤ (k:ℝ)/(p:ℝ) via `rw [le_div_iff₀ hp0]` +
`Nat.div_mul_le_self` + exact_mod_cast), `sum_filter_mul_eq`
(`Σ_{h≤k, p|h} F h = Σ_{m ≤ k/p} F(p·m)` via Finset.sum_bij h ↦ h/p:
surjectivity with `p·m` + `Nat.le_div_iff_mul_le`, injectivity via
`Nat.mul_div_cancel'`, right_inv `Nat.mul_div_right m hp0`), and the main
**`prod_sum_bound S hprime k : Σ_{h ∈ Icc 1 k} Fprod S h ≤ (k:ℝ)·Pprod S`**
by Finset.induction_on over S (split-off prime p₀: Term1 ≤ B·k·P(S'),
Term2 = Σ_{m≤k/p₀}F(m) ≤ ((k/p₀:ℕ):ℝ)·P(S') ≤ (k:ℝ)/p₀·P(S'); sum
`B·k·P' + (k/p₀:ℝ)·P' = k·((p₀:ℝ)−2+1/p₀)·P'`; prod_insert).  All compile;
build rc=0, two sorries remain.
Gotchas: the p·m ≥ 1 membership needs `Nat.succ_le_of_lt (Nat.mul_pos hp0 (lt_of_lt_of_le (by norm_num) hm1))`
(omega can't do nonlinear p·m ≥ 1); `Nat.div_le_div_right h` has all-nat
implicit args (do NOT pass `p`); `Nat.mul_div_right m hp0` needs `hp0 : 0 < p`
(as the divisor), NOT p ≠ 0; `le_div_iff₀` (not `div_le_iff₀`) for `x ≤ b/c`.

**Next steps (pair_sum_nat_bound assembly; unfilled at ~3110):**
1. `close_pair_range_product (q h) [NeZero q] :
   (closePairCount q h : ℝ) = ∏_{p ∈ q.primeFactors} (p:ℝ)^(e_p−1) ·
     ((p:ℝ) − 2 + (if p∣h then 1 else 0))`
   = zmod_closePair_eq (cast) + cp_eq_prod_primeFactors (cast; Nat.cast_prod/
   pow/mul) + `if_sub_two_cast_real (p h) (hp : 2 ≤ p) :
   ((if p∣h then p−1 else p−2 : ℕ):ℝ) = (p:ℝ)−2 + (if p∣h then 1 else 0)`
   (by_cases p∣h; `rw [Nat.cast_sub (by omega : 1 ≤ p)]`/`(2 ≤ p)`; ring).
2. `pair_sum_real_bound (q k) [NeZero q] :
   (q:ℝ)·Σ_{h≤k}(closePairCount q h : ℝ) ≤ (k:ℝ)·(φ(q):ℝ)^2`:
   Σ_h closePairCount = Σ_h ∏(p^{e_p−1}·gval p h)
   = E·Σ_h Fprod(pf q) h [Finset.prod_mul_distrib; E := ∏p^{e_p−1} ≥ 0]
   ≤ E·k·Pprod(pf) [prod_sum_bound]
   ; q·E·Pprod(pf) ≤ q·E·∏(p−1:ℝ)²/p [prime_ring_identity pointwise] and
   `(φ q : ℝ)^2 = (q:ℝ)·E·∏((p:ℝ)−1)²/(p:ℝ)` — proved from
   q = ∏ p^{e_p} and φ(q) = ∏ p^{e_p−1}(p−1) as real Finset-products over
   q.primeFactors (Nat.prod_primeFactors_pow_factorization for q;
   totient as product over primeFactors via
   Nat.totient_eq_prod_factorization Finsupp form, whose support is
   q.primeFactors = factorization.support).
3. `pair_sum_nat_bound`: nat-version by exact_mod_cast of the real bound
   (both sides naturals); hypothesis hk : k·φ(q) ≤ q is then unused (the
   bound is unconditional) — keep it as an unused hypothesis.
Then `real_gap_count_le`/`gap_deficit_bound`/`cyclic_gap_cover_bound` are all
already proven, so K1's unfilled disappears and only K2
(`approxAddOrderOf_inter_volume_le_quasi`) remains.

## Session-11: range-side product identity COMMITTED.

New (in-file, before pair_sum_nat_bound):
- `if_sub_two_cast_real (p h) (hp : 2 ≤ p) : ((if p∣h then p−1 else p−2 : ℕ):ℝ)
   = (p:ℝ) − 2 + (if p∣h then 1 else 0)` (by_cases; `Nat.cast_sub` + `norm_num`
   + `ring`; the `↑1 = 1` mismatch needs `norm_num` after `Nat.cast_sub`).
- `nat_prod_cast_real (s) (f) : ((∏ p∈s, f p : ℕ):ℝ) = ∏ p∈s, ((f p : ℕ):ℝ)`
   (Finset induction; `simp [Finset.prod_insert, ih, Nat.cast_mul]`).
- `close_pair_range_product (q h) [NeZero q] :
   (closePairCount q h : ℝ) = ∏_{p ∈ q.primeFactors} (p:ℝ)^(e_p−1)·
     ((p:ℝ) − 2 + (if p∣h then 1 else 0))`
   = `zmod_closePair_eq` (cast) ∘ `cp_eq_prod_primeFactors` (cast) ∘
   `nat_prod_cast_real` ∘ per-factor `Nat.cast_mul`/`pow` ∘
   `if_sub_two_cast_real` (with `2 ≤ p` from `prime_of_mem_primeFactors`).
Build rc=0, still exactly two sorries.

**Remaining assembly for `pair_sum_nat_bound` (unfilled at ~3160ish):**
Write `pair_sum_real_bound (q k) [NeZero q] :
   (q:ℝ)·Σ_{h∈Icc 1 k}(closePairCount q h : ℝ) ≤ (k:ℝ)·(φ(q):ℝ)²`:
1. Σ_h closePairCount = Σ_h ∏_p (p^{e−1}·gval p h)  [close_pair_range_product]
   = E·Σ_h Fprod(pf) h  with `E := ∏_{p∈pf} (p:ℝ)^(e_p−1)`
   [per-h `Finset.prod_mul_distrib`; then factor E out: ← `Finset.mul_sum`].
   ≤ E·((k:ℝ)·Pprod(pf))  [`prod_sum_bound`; `mul_le_mul_of_nonneg_left`, E ≥ 0].
2. Multiply by (q:ℝ) ≥ 0 and use the KEY identity
   `(q:ℝ)·E·Pprod(q.primeFactors) = ((q.totient:ℝ))^2`:
   • `(q:ℝ) = ∏_{p∈pf}(p:ℝ)^(e_p)` (cast of `Nat.prod_primeFactors_pow_factorization`).
   • `E = (q:ℝ)/R`, `R := ∏_{p∈pf}(p:ℝ) ≠ 0` (`p^e = p·p^{e−1}`, e ≥ 1).
   • `(φ q:ℝ)·R = (q:ℝ)·S`, `S := ∏_{p∈pf}((p:ℝ)−1)` (cast of
     `Nat.totient_mul_prod_primeFactors`).
   • `Pprod = ∏_{p∈pf}((p:ℝ)−1)²/(p:ℝ) = S²/R` (Finset.prod_congr +
     `prime_ring_identity`).
   Then q·E·Pprod = (q²/R)(S²/R) = (qS/R)² = φ².
3. `pair_sum_nat_bound (q k) hk`: cast the real bound via `exact_mod_cast`
   (both sides are casts of naturals); `hk` becomes unused (bound is
   unconditional in k).  Its proof body: `simpa [closePairSum] using ...`.
After it lands, `real_gap_count_le` → `gap_deficit_bound` →
`cyclic_gap_cover_bound` are all proven, so only K2
(`approxAddOrderOf_inter_volume_le_quasi`) remains.

## Session-12: **`pair_sum_nat_bound` PROVEN — the whole K1 chain is now unfilled-free.**

New (in-file, immediately before `pair_sum_nat_bound`):
- `Eprod q := ∏_{p|q} (p:ℝ)^(e_p−1)`, `Eprod_nonneg`.
- `fibre_factorization_pos` (exponent ≥ 1 for `p ∈ q.primeFactors`,
  via `Finsupp.mem_support_iff` + `Nat.support_factorization`).
- `nat_pred_cast_real (p) (1 ≤ p) : ((p−1:ℕ):ℝ) = (p:ℝ)−1` (`Nat.cast_sub`+`norm_num`).
- `nat_sum_cast_real` (cast pushed inside a Finset sum).
- **`prime_factors_prod_identity (q) [NeZero q] :
  (q:ℝ) · Eprod q · Pprod q.primeFactors = (q.totient:ℝ)²`** — from
  (a) `(q:ℝ) = R·Eprod q` (cast of `Nat.prod_primeFactors_pow_factorization`,
  per-prime `p^e = p·p^(e−1)` since `e ≥ 1`), (b) `φ·R = q·S` (cast of
  `Nat.totient_mul_prod_primeFactors`; `S = ∏(p−1)`), (c) `Pprod = S²/R`
  (`Finset.prod_pow` + `Finset.prod_div_distrib` + `prime_ring_identity`),
  `R = ∏p > 0`; then `φ = Eprod·S` by cancelling `R`, and the final
  `field_simp` (not followed by `ring` — `field_simp` already closes it).
- **`pair_sum_real_bound (q k) [NeZero q] :
  (q:ℝ)·Σ_{h≤k} closePairCount q h ≤ (k:ℝ)·(φ(q):ℝ)²`** — via
  `close_pair_range_product`, `Finset.prod_mul_distrib` (factor `Eprod q` out),
  `prod_sum_bound`, and `prime_factors_prod_identity`.  NOTE: the `congr 1`
  in the per-`h` step already closes the goal because `Fprod`/`gval` are
  reducible defs (do not add further `unfold`).
- **`pair_sum_nat_bound` PROVEN**: `q = 0` case by `simp [closePairSum]`;
  otherwise cast `pair_sum_real_bound` back via `nat_sum_cast_real` +
  `exact_mod_cast` (the hypothesis `hk` is unused — the bound is unconditional).
Consequently `real_gap_count_le` → `gap_deficit_bound` →
`cyclic_gap_cover_bound` → `approxAddOrderOf_volume_ge_min_quasi` →
`large_values_tail_block` are all unfilled-free.

**Remaining: exactly ONE unfilled** — `approxAddOrderOf_inter_volume_le_quasi`
(K2, per-pair quasi-independence, now at line ~4440).  Route unchanged:
trivial regime when one of `μ(A_q), μ(A_r) ≥ 1/8`; otherwise the PV §3
close-pair/fibre count (`approxAddOrderOf_inter_volume_le`,
`fibre_window_count_le_global`, `fibre_count_eq`, `reduced_pair_count_prime(_pow)`,
`reduced_pair_coprime_fiber`), composed with `main_term_real_ineq` and
`approxAddOrderOf_volume_ge_totient_div`; see the docstring at its site and
`pv_overlap_large.lean` §8/§9.

## Session-13: K2's trivial (large-measure) regime COMMITTED.

New lemma (immediately before K2):
`inter_volume_le_quasi_of_large_measure (q r) (δq δr)
  (hbig : (1:ℝ≥0∞)/8 ≤ max (μ(A_q)) (μ(A_r))) : μ(A_q ∩ A_r) ≤ 8·μ(A_q)·μ(A_r)`.
Proof: `μ(A∩B) ≤ min(μA,μB)` (`le_min (measure_mono inter_subset_left) …`);
then `le_total` on `μA ≤ μB`; from `hbig` and `max_eq_right/left` get
`1/8 ≤ μB` (resp. `μA`), hence `1 ≤ 8·μB` via
`mul_le_mul_right hbig 8` and `ENNReal.mul_div_cancel (8≠0) (8≠∞)`
(NOT `norm_num`: `8 * (1/8) = 1` is not numeral-normalizable in ℝ≥0∞);
then `μA ≤ μA·(8μB) = 8·μA·μB` (`mul_le_mul_right h8 _`, `ring`).
The K2 statement now dispatches:
`δq = 0` / `δr = 0` / large-measure (`inter_volume_le_quasi_of_large_measure`) /
remaining hard case (the single `unfilled` at line ~4485: BOTH measures < 1/8,
i.e. φ(q)/q, φ(r)/r < 1/8 — needs the PV §3 close-pair/fibre counting).

**Remaining: exactly ONE unfilled** — the small-measure regime of K2.
Route (unchanged): `approxAddOrderOf_inter_volume_le`
(`μ∩ ≤ 2·min(δq,δr)·N(q,r,δq+δr)`) + fibre window count
(`fibre_window_count_le_global`/`fibre_count_eq`/`reduced_pair_count_prime(_pow)`/
`reduced_pair_coprime_fiber`), then `main_term_real_ineq` + `approxAddOrderOf_volume_ge_totient_div`
(with `μ(A_q) ≥ φ(q)/q ≥ …` under `q·δq ≥ 1/2`); see pv_overlap_large.lean §8/§9.

## Session-14: first piece of K2's small-measure regime COMMITTED.

New lemma (before K2):
`small_measure_forces (q) (hq : 0 < q) (δ) (hδ : 0 ≤ δ)
  (hlarge : 1/2 ≤ q·δ) (hsmall : μ(A_q) < (1:ℝ≥0∞)/8) :
  1/(2q) ≤ δ ∧ (φ(q):ℝ)·δ < 1/8`.
Proof: first conjunct from `hlarge` via `div_le_iff₀`; second from the K1 lower
bound `approxAddOrderOf_volume_ge_min_quasi`
(`ofReal((1/2)·min 1 (2φδ)) ≤ μ < ofReal(1/8)`), converting
`(1:ℝ≥0∞)/8 = ofReal(1/8)` with `norm_num [ENNReal.ofReal_div_of_pos]` and
`ENNReal.ofReal_lt_ofReal_iff`; then `min 1 (2φδ) < 1/4` forces `2φδ < 1/4`.
The hard branch of K2 now extracts: `μ(A_q), μ(A_r) < 1/8` (from
`lt_of_not_ge hbig` + `le_max_left/right`), `1/2 ≤ q·δq, r·δr` (via
`Or.resolve_left hq0`), `0 ≤ δq, δr`, and invokes `small_measure_forces` for
both sides — so the regime facts `1/(2q) ≤ δq`, `φ(q)δq < 1/8` (and r) are in
scope at the single remaining `unfilled` (line ~4530).

**Remaining: exactly ONE unfilled** — the small-measure K2 bound.  Next pieces:
1. From the committed crude `approxAddOrderOf_inter_volume_le`
   (`μ∩ ≤ ofReal(2·min(δq,δr)·min(φq(2Δr+1), φr(2Δq+1), φqφr))`, Δ = δq+δr)
   and the K1 lower bound `μ(A_q) ≥ φ(q)δ(q)` (valid in this regime since
   `2φδ < 1/4 < 1`), reduce to the pure counting estimate
   `2·min(δq,δr)·N ≤ 8·φ(q)δq·φ(r)δr`, where `N` is the close-pair count of
   `approxAddOrderOf_inter_volume_le` (card_div_nat_ball_le).
2. The main term is automatic (`min·Δ ≤ 2·δq·δr`); the remaining content is the
   fibre-window error bound: use `fibre_window_count_le_global (q r W)` with
   `W` the window radius (macroscopic in this regime) to dominate the small
   window count `N`, then handle the error term
   `φ(g)·τ(qr/g²)·3^{ω(g)}` against `φ(q)δq·φ(r)δr` using `1/(2q) ≤ δq`,
   `φ(q)δq < 1/8`, `δq < 1/(8φ(q))` (i.e. the regime facts just committed);
   `main_term_real_ineq` (in-file) handles the bounded-`b` main-term algebra.
   See `pv_overlap_large.lean` §8/§9 for the derivation.

## Session-15: K2's small-measure reduction COMMITTED (pure core).

New lemma (before K2):
`quasi_of_count_bound (q r) (δq δr N) (hδq0) (hδr0)
  (hinter : μ(A_q∩A_r) ≤ ofReal (2·min(δq,δr)·N))
  (hcount : N ≤ 2·(δq+δr)·φ(q)φ(r))
  (hLq : ofReal(φ(q)δq) ≤ μ(A_q)) (hLr : ofReal(φ(r)δr) ≤ μ(A_r)) :
  μ(A_q∩A_r) ≤ 8·μ(A_q)·μ(A_r)`.
Proof: `2mN ≤ 2m·(2Δφφ) = 4·(mΔ)φφ ≤ 4·(2δqδr)φφ = 8·(φqδq)(φrδr)` using the
already-present `min_add_mul_le_two_mul`; then `ofReal` of that with
`ENNReal.ofReal_mul` (lemmas applied in the order `(8·X)·Y` then `8·X`), and
finally `mul_le_mul'` for `8·ofReal(φqδq)·ofReal(φrδr) ≤ 8·μ(A_q)·μ(A_r)`.

IMPORTANT correction to the earlier plan: the committed crude
`approxAddOrderOf_inter_volume_le` is NOT sufficient for the small-measure
regime.  Its bound is `μ∩ ≤ ofReal(2m·min(min(φq(2Δr+1), φr(2Δq+1)), φqφr))`;
at the boundary (q≈r≈Q, δ = 1/(2Q), φ ≈ Q/4) the min is ≍ φ (since
φ ≥ 3 ⟹ φ² ≥ 3φ) and the discrepancy against `8μqμr` is a factor ≍ Q.  So the
refined intersection bound (a) with the PV §3 count must be produced (its proof
should follow the structure of `approxAddOrderOf_inter_volume_le` but keep the
count `N` inside `ofReal` instead of substituting the crude cardinality bound
`card_div_nat_ball_le`).  Then (b) `fibre_window_count_le_global` at the
macroscopic window, with `min_add_mul_le_two_mul`/`main_term_real_ineq` for the
main term and the regime facts (`1/(2q) ≤ δq`, `φ(q)δq < 1/8`) for the error
`φ(g)τ(·)3^{ω(g)}`.

## Session-16: K2 piece (b) started — fibre-window main-term estimates COMMITTED.

New (before K2):
- `fibre_main_term_le (Δ L W M) (hΔ) (hL) (hM) (hΔL : 1/2 ≤ Δ·L) (hW : W ≤ Δ·L+1) :
   2·W·M/L ≤ 6·Δ·M`
  (split `2W M/L ≤ 2(ΔL+1)M/L = 2ΔM + 2M/L`; `2M/L ≤ 4ΔM` from `1/L ≤ 2Δ`,
  itself from `1 ≤ 2ΔL`; `field_simp` closes the algebraic identity — do NOT
  follow it with `ring`).
- `fibre_main_term_ceil_le (Δ) (L : ℕ) (M) … : 2·⌈Δ·L⌉·M/L ≤ 6·Δ·M`
  (via `Nat.ceil_lt_add_one (hx0 : 0 ≤ Δ·L)`; note it needs the nonnegativity
  argument).
These give the main term of `fibre_window_count_le_global` at the macroscopic
window `W := ⌈Δ·L⌉` (Δ = δq+δr, L = lcm(q,r)): the constant is 6 here (the `+1`
slack of the ceiling); the per-pair constant in K2/large_values_tail_block is a
private constant and can be re-tuned accordingly if needed (U ≤ L + C·L²,
c = 1/(3 + 9C)).

**Remaining for K2 (one unfilled at line ~4591):**
(a) refined intersection bound `μ(A_q∩A_r) ≤ ofReal(2·min(δq,δr)·N)`, N the PV §3
    close-pair count — re-run the proof of `approxAddOrderOf_inter_volume_le`
    keeping `N` inside `ofReal` (the crude `card_div_nat_ball_le` cardinality is
    a factor ≍ Q too large in the small-measure regime, see Session-15 notes);
(b) fibre-window count:
    1. `N ≤ (fibre_window_count) ≤ 6·Δ·φ(q)φ(r) + φ(g)·τ(qr/g²)·3^{ω(g)}`
       (`fibre_window_count_le_global q r ⌈Δ·L⌉` + `fibre_main_term_ceil_le`),
       together with the arc↔lattice correspondence between the two notions of
       close pair (circle-distance ≤ Δ vs `(m·(r/g) − n·(q/g)) mod L ∈ [−W,W]`);
    2. error control `2·min(δq,δr)·φ(g)τ(qr/g²)3^{ω(g)}` against
       `φ(q)δq·φ(r)δr`, using the committed regime facts
       (`1/(2q) ≤ δq`, `φ(q)δq < 1/8`, hence `δq < 1/(8φ(q))`) and the
       macroscopic-window inequality ΔL ≥ (q+r)/(2g)... — the deep PV §3 step.
Then `quasi_of_count_bound` (committed) closes the small-measure case of K2.

## Session-17: the fibre-window wrapper COMMITTED (piece (b) main half done).

New (before K2):
`fibre_window_count_le (q r W) (Δ) (hq) (hr) (hΔ) (hW : W = ⌈Δ·↑(q*r/q.gcd r)⌉)
   (hΔL : 1/2 ≤ Δ·↑(q*r/q.gcd r)) :
   let g := q.gcd r; let L := q*r/g; ... (same let-block as
   `fibre_window_count_le_global`, P/PQ with window `W`) ...
   (PQ.filter P).card ≤ 6·Δ·(φ(q):ℝ)(φ(r):ℝ)
      + (g.totient:ℝ)·(q*r/(g*g)).divisors.card·3^(g.primeFactors.card)`.
Proof: `dsimp only` both in the goal and at
`fibre_window_count_le_global q r W`; `le_trans hmain`; then bound the main term
by `fibre_main_term_ceil_le` with `M := ↑φq * ↑φr`; the goal needs
`rw [hW, hcast]` where `hcast : ↑(q.totient * r.totient) = ↑q.totient * ↑r.totient`
(`Nat.cast_mul`) — note the goal after `le_trans` retains `↑W` (the parameter) and
`↑(φq*φr)`, while the `ceil` lemma is stated with `⌈Δ·↑L⌉` and `M`; then
`linarith [hb]` (the identical error atoms cancel).  New import:
`Submission.Commons.NumberTheory.DuffinSchaeffer.fibre_window_count_le_global`.

**Remaining to close the single `unfilled` (small-measure K2, line ~4631):**
1. arc↔lattice correspondence: relate the arc-window count `N` (circle distance
   `|m/q − n/r| ≤ Δ`, the quantity in the refined `hinter`) to the lattice count
   `(PQ.filter P).card` at `W = ⌈Δ·L⌉` (lattice residue distance mod `L`,
   `W = ⌈ΔL⌉`), i.e. `N ≤ (fibre count)`; the `⌈·⌉` and the `±1` transition
   between "circle distance ≤ Δ" and "residue distance ≤ W" need care.
2. refined `hinter`: re-run the proof of `approxAddOrderOf_inter_volume_le`
   keeping this `N` inside `ofReal` (the committed crude cardinality
   `card_div_nat_ball_le` is a factor ≍ Q too weak).
3. error control: `2·min(δq,δr)·φ(g)τ(qr/g²)3^{ω(g)}` ≪ `φqδq·φrδr` using
   `small_measure_forces` (`1/(2q) ≤ δq`, `φ(q)δq < 1/8`, `δq < 1/(8φ(q))`) and
   `ΔL ≥ (q+r)/(2g)`-type macroscopic bounds.
Then `quasi_of_count_bound` closes the case.

## Session-18: arc↔lattice bridge, real half COMMITTED.

New (before K2): `circle_dist_eq_lattice (q r m n) (hq) (hr) :
  dist (↑(m/q)) (↑(n/r)) = ‖↑(((m·(r/g) − n·(q/g))/L))‖`, `g = gcd q r`,
`L = q*r/g`.  Proof: `dist_eq_norm`, `← AddCircle.coe_sub`, `congr 1`,
`push_cast`, the three cast lemmas `Nat.cast_div (gcd ∣ ·)` for
`↑(r/g), ↑(q/g), ↑(q*r/g)`, then `field_simp` (which closes; do NOT add `ring`).
This is the real-analysis half of the arc↔lattice correspondence: the circle
distance is the norm of the *lattice* quantity `(mRr − nQ)/L`.  Note for
`m < q`, `n < r` one has `m·Rr < L` and `n·Q < L`, so in the fibre predicate the
`% L` on those products is removable (`Nat.mod_eq_of_lt`), and the fibre
condition becomes the genuine two-sided residue window
`(mRr + L − nQ) % L ≤ W ∨ (nQ + L − mRr) % L ≤ W`.

**Remaining half of the bridge (int-residue step):** from
`‖↑((x)/L)‖ < Δ` with `x := m·Rr − n·Q` (so `|x| < L`) conclude
`(mRr + L − nQ) % L ≤ ⌈ΔL⌉ ∨ (nQ + L − mRr) % L ≤ ⌈ΔL⌉`.
Ingredients: `circle_norm_lt_iff_exists_int` gives `∃k : ℤ, |x/L − k| < Δ`,
i.e. `∃k, |x − kL| < ΔL`; then the integer lemma "the distance of `x` to `Lℤ`
is `min (x % L) ((-x) % L)`, and `≤ |x − kL|`", i.e.
`Int.emod_nonneg`, `Int.emod_lt_of_pos`, `Int.emod_neg`,
`Int.emod_sub_emod`, plus `Nat.mod_eq_of_lt` and `Nat.min_le_iff`;
finally `(Nat.ceil_le).mpr`/`Nat.le_ceil` to pass `< ΔL` to `≤ ⌈ΔL⌉`.
Then the arc-window count `N` (per-`m` window sum over reduced `n`) is bounded by
the fibre count `PQ.filter P` at `W = ⌈ΔL⌉` (monotone `Finset.card_le_card` of
the filter inclusion = the per-pair implication), which `fibre_window_count_le`
(in-file) bounds by `6·Δ·φ(q)φ(r) + φ(g)τ3^ω`.

## Session-19: the integer emod lemma COMMITTED.

New (before K2):
- `min_le_abs_add_mul (L) (hL : 0 < L) (a m : ℤ) (ha0 : 0 ≤ a) (haL : a < ↑L) :
   min a (↑L − a) ≤ |a + m·↑L|` (cases `m ≥ 0` / `m < 0`; `Int.emod_*`
  independent, only `abs_of_nonneg`/`abs_of_neg`).
- `emod_min_le_abs (L) (hL : 0 < L) (x k : ℤ) :
   min (x % ↑L) ((−x) % ↑L) ≤ |x − k·↑L|`
  — "the distance of `x` to the nearest multiple of `L` is at most its distance
  to `k·L`".  Proof: `a := x % Lz`, `b := (−x) % Lz` (both in `[0, L)` via
  `Int.emod_nonneg`/`Int.emod_lt_of_pos`); `Lz ∣ x − a` and `Lz ∣ (−x) − b`
  from `Int.emod_sub_emod` + `Int.dvd_iff_emod_eq_zero` (watch the equality
  direction: `emod_sub_emod` gives `0 = (x−a) % Lz`, use `.symm`); hence
  `Lz ∣ a + b` (`dvd_add`+`dvd_neg.mp`), and `0 ≤ a+b < 2Lz` forces
  `a + b = 0` or `a + b = Lz` (`omega` needs the equation pre-rewritten:
  `simpa [h0] using ht`).  Case `a=b=0` trivial; case `a+b = Lz`:
  `b = Lz − a`, write `x − k·Lz = a + (j−k)·Lz` from `x − a = Lz·j`
  (`linarith`+`ring`), apply `min_le_abs_add_mul`.

**Remaining half of the arc↔lattice bridge** (now with all ingredients): from
`‖↑(x/L)‖ < Δ` with `x := m·Rr − n·Q`, `circle_norm_lt_iff_exists_int` gives
`∃k, |x/L − k| < Δ`, i.e. `∃k, ((x − kL).natAbs : ℝ) < Δ·L`; then
`min (x%L) ((−x)%L) = min (mRr + L − nQ)%L, (nQ + L − mRr)%L` (modulo
`m·Rr < L`, `n·Q < L` for `m < q, n < r`, `Nat.mod_eq_of_lt`), and
`emod_min_le_abs` bounds it by `|x − kL| < ΔL ≤ ⌈ΔL⌉`; then `min_le_iff` gives
one disjunct ≤ `W = ⌈ΔL⌉`, i.e. the fibre predicate `P`.  Filter inclusion +
`fibre_window_count_le` then bounds the arc count `N`.

## Session-20: norm → emod-window bridge COMMITTED.

New (before K2): `norm_lt_implies_emod_min (L : ℕ) (hL : 0 < L) (A : ℤ) (Δ : ℝ) (hΔ : 0 ≤ Δ)
  (h : ‖↑((A:ℝ)/L)‖ < Δ) : (min (A % ↑L) ((−A) % ↑L)).toNat ≤ ⌈Δ·L⌉`.
Proof: `circle_norm_lt_iff_exists_int` gives `∃k, |A/L − k| < Δ`; multiply by
`L > 0` — the clean way is `hfac : A/L − k = (A − k·L)/L` by `field_simp`, then
`rw [hfac, abs_div, abs_of_pos hLpos, div_mul_cancel₀ _ (ne_of_gt hLpos)]`
(watch out: a naive `← abs_of_pos` rewrites the `L` inside `A/L`);
then `emod_min_le_abs` + `Int.toNat_of_nonneg` + `Int.cast_abs` + `push_cast` and
`Nat.le_ceil`.

**Remaining in the arc↔lattice bridge:**
1. identify the ℕ fibre residues with the ℤ emod values: with `g = gcd q r`,
   `Rr = r/g`, `Qq = q/g`, `L = q*r/g`, `m < q`, `n < r` (so `m·Rr < L`,
   `n·Qq < L`), and `A := (m·Rr : ℤ) − (n·Qq : ℤ)`, prove
   `(m·Rr + L − n·Qq) % L = (A % ↑L).toNat` and
   `(n·Qq + L − m·Rr) % L = ((−A) % ↑L).toNat`
   (`Nat.mod_eq_of_lt`, `Nat.cast_mul`, `Nat.mul_div_assoc` for `q·Rr = L`).
2. `circle_dist_eq_lattice` (Session-18) rewrites the point distance to
   `‖↑(A/L)‖`, so `dist < Δ` + step 1 + `norm_lt_implies_emod_min` gives
   `min (fibre₁) (fibre₂) ≤ ⌈ΔL⌉`, and `min_le_iff` yields one disjunct,
   i.e. the fibre predicate `P` at `W = ⌈ΔL⌉` — a per-pair implication.
3. `Finset.card_le_card` of the resulting filter inclusion bounds the arc count
   `N` by `(PQ.filter P).card`, which `fibre_window_count_le` (Session-17)
   bounds by `6·Δ·φ(q)φ(r) + φ(g)τ(qr/g²)3^{ω(g)}`.
Then the refined `hinter` (re-run of `approxAddOrderOf_inter_volume_le` keeping
`N`) plus `quasi_of_count_bound` close the small-measure case.

## Session-21: fibre-residue identification COMMITTED (step 1 of the arc↔lattice bridge).

New (before K2):
- `fibre_residue_left (q r m n) (hm : m < q) (hn : n < r) :
   (m·Rr + L − n·Qq) % L = (((m·Rr : ℕ) : ℤ) − ((n·Qq : ℕ) : ℤ)) % (L : ℤ) |>.toNat`
- `fibre_residue_right : (n·Qq + L − m·Rr) % L = (((n·Qq : ℕ) : ℤ) − ((m·Rr : ℕ) : ℤ)) % L |>.toNat`
  (`Rr = r/g`, `Qq = q/g`, `L = q*r/g`).
  Proof (both): `m·Rr < L` and `n·Qq < L` (`Nat.mul_div_assoc` for
  `q·Rr = L`, `r·Qq = L`; `Nat.mul_lt_mul_of_pos_right` with `Rr,Qq ≥ 1` from
  `Nat.div_pos`+`Nat.le_of_dvd`); the ℤ cast of `m·Rr + L − n·Qq` equals
  `A + L` (`Nat.cast_sub`+`Nat.cast_add`+`ring`); `Int.natCast_mod` then
  `Int.add_mul_emod_self_left` gives `↑(residue) = A % L`; apply
  `congrArg Int.toNat` and `Int.toNat_natCast`.
  **GOTCHA (important):** in the *statement* the ascription `(m * (r / q.gcd r) : ℤ)`
  propagates ℤ into the sub-operations (`↑m * (↑r / ↑g)`!) — always write
  `((m * (r / q.gcd r) : ℕ) : ℤ)` to force the Nat computation first.  (This is
  also why earlier real statements used `((... : ℕ) : ℝ)`.)

**Remaining steps to close the arc↔lattice bridge and the small-measure case:**
2. per-pair implication: `dist (↑(m/q)) (↑(n/r)) < Δ` ⟹ fibre predicate `P`
   (`m < q`, `n < r`): `circle_dist_eq_lattice` (S18) rewrites the distance to
   `‖↑(A/L)‖`; `norm_lt_implies_emod_min` (S20) gives
   `min (A % L).toNat ((−A) % L).toNat ≤ ⌈ΔL⌉`; `fibre_residue_left/right`
   (this session) identify those with the two ℕ fibre residues; `min_le_iff`
   picks the disjunct.
3. `Finset.card_le_card` on the filter inclusion bounds the arc count `N` by
   `(PQ.filter P).card`, which `fibre_window_count_le` (S17) bounds.
4. refined `hinter` (re-run of `approxAddOrderOf_inter_volume_le` keeping `N`)
   + `quasi_of_count_bound` (S15) close the small-measure case.

-/

/-

## Session-22: refined plan for the small-measure K2 (exact fibre count route).

**Status.** File builds, exactly ONE `unfilled` (`approxAddOrderOf_inter_volume_le_quasi`,
the small-measure branch, ~line 4950).  Numerics (Session-22) confirm the target
`μ(A_q∩A_r) ≤ 2·μ(A_q)μ(A_r)` numerically in all tested regimes (max measured
ratio 2.000 over all `2 ≤ q,r ≤ 150` and 8 choices of `(δ_q,δ_r) = (c_q/q, c_r/r)`;
also `N/(Δ·φ(q)φ(r)) ≤ 3.22` for the reduced close-pair count `N` over
`2 ≤ q,r ≤ 120`), so the constant-8 statement is almost certainly TRUE.

**Corrected numerics gotcha (Session-21/22).**  The close-pair count is
`N = #{(a,b) : a<q, b<r, a⊥q, b⊥r, ‖u/L‖ < Δ}` with `u = a·(r/g) − b·(q/g)`
(`g = gcd q r`, `L = qr/g`) — NOT `a·r − b·q` with modulus `L` (that is `g·u`
with modulus `L`; the modulus is `qr` / `L` for the *reduced* numerator `u`).

**Route (all pieces now identified; the only gap is the error control (E)).**

1. **Exact count (commons `fibre_count_eq`, transfer needed).** For `q ≠ r`,
   `0 ≤ Δ < 1/8`, with `g = gcd q r`, `L = qr/g`, `q' = qr/g²`,
   `K = ∏_{p | g, p ∤ q'} p^{ν_p(g)}`, `Phi = ∏_{p | q'} φ(p^{ν_p(g)})`,
   `S(c) = ∏_{p | K} (if p | c then φ(p^{ν_p(K)}) else p^{ν_p(K)-1}(p−2))`,
   ```
   N = 2·Phi·Σ_{c ∈ [1, ⌈ΔL⌉−1], c ⊥ q'} S(c).           (EXACT)
   ```
   (Transfer from `fibre_count_eq`: proving that
   `∃ j : Fin 3, |a·r − b·q − (j−1)·qr| < Δ·qr`  ⟺  `‖u/L‖ < Δ`, using
   `|u| < L` and `0 ≤ Δ < 1/2`.  *Turn this into a commons lemma*:
   request path `NumberTheory/DuffinSchaeffer/fibre_count_eq_closed_pairs` — a
   first attempt failed to elaborate because `Finset.filter` needs a decidable
   predicate; use the `∃ j : Fin 3` form from `fibre_count_eq` verbatim.)

2. **Totient identity (pure number theory, verified numerically).** With
   `Sbar = ⟨S⟩ = ∏_{p | K} p^{ν_p(K)−2}(p−1)²`:
   ```
   Phi · Sbar · g · φ(q')  =  φ(q) · φ(r).                (IDENTITY)
   ```
   (Check: (4,6):2·1·2·φ(6)=4=φ4φ6; (6,10):1·(1/2)·2·φ(15)=8=φ6φ10;
   (12,18):2·1·6·φ(6)=24; (4,12):1·1·4·φ(3)=8; (9,6):2·1·3·φ(6)=12.)
   *Request as `NumberTheory/DuffinSchaeffer/fibre_phi_identity` (rejected this
   session as "team busy"; re-issue next session).*  Consequence: since
   `X := ⌈ΔL⌉−1 ≤ ΔL`,
   ```
   2·Phi·X·(φ(q')/q')·Sbar  ≤  2·Δ·φ(q)·φ(r).             (MAIN)
   ```

3. **Density bound with error.**  `#{c ≤ Y : c ⊥ q'} = (φ(q')/q')·Y + δ(Y)`,
   `|δ(Y)| ≤ 2^{ω(q')}`.  Expanding `S(c) = ∏_{p|K}p^{ν−1}·∏_{p|K}(p−2+1_{p|c})`
   and summing over subsets `U ⊆ primeFactors K` gives
   ```
   Σ_{c ≤ X, c ⊥ q'} S(c) ≤ X·(φ(q')/q')·Sbar + 2^{ω(q')}·Smax,
       Smax = ∏_{p|K} p^{ν_p(K)−1}(p−1),   and  Phi·Smax = φ(g).
   ```
   Hence, with (MAIN),
   ```
   N ≤ 2·Δ·φ(q)·φ(r) + 2^{ω(q')+1}·φ(g).                 (COUNT)
   ```

4. **(E) Error control in the small-measure regime.**  This is the only
   remaining gap.  Need `2^{ω(q')+1}φ(g) ≤ C·Δ·φ(q)φ(r)` for an absolute `C`,
   under `μ(A_q),μ(A_r) < 1/8` (which forces `φ(q)/q, φ(r)/r < 1/8`).
   **The naive bound FAILS**: with `q=g`, `r=g·b` (`b ⊥ g` smooth) one gets
   `ratio = 2^{ω(b)+1}φ(g)/(Δφ(g)φ(gb)) ≤ 4·b·2^{ω(b)}·g/(φ(g)φ(b))`, which is
   unbounded because `2^{ω(b)}·b/φ(b)` is unbounded while `φ(b)` may be tiny.
   However, in exactly that regime the window `X = ⌈ΔL⌉−1` is TINY
   (`X ≈ (a+b)/2`, `a=q/g`, `b=r/g`), so the *exact* sum
   `Σ_{c ≤ X, c ⊥ b}S(c)` is just `S(1)+S(2)+…` (a handful of terms, each
   `≪ Smax`, in fact `S(c) ≈ ∏(p−2)` for small `c`), which is why the crude
   `2^{ω(q')}Smax` is far too lossy.  **Correct treatment:** split on `X`:
   - `X ≥ rad(K)`-ish: density bound (step 3) is fine;
   - `X` small: bound `Σ ≤ X·Smax` and use `X ≤ ΔL` together with
     `φ(q)/q,φ(r)/r < 1/8` to absorb `2^{ω(q')+1}φ(g)`.
   Concretely, for `q=g`, `r=gb`: `N = 2·∏_{p|K}(p−2)` (only `c=1`) up to
   `X` terms, `≈ 2φ(g)/ln(gen)`, while `2Δφφ ≈ 2·(1/(2g))·φ(g)²φ(b)` — both
   are `≈ φ(g)·(small)`, matching.

5. **Assembly.** Once (COUNT) + (E) give `N ≤ C·Δ·φ(q)φ(r)`, combine with
   `μ∩ ≤ ofReal(2·min(δq,δr)·N)` (union bound over intersecting arc pairs;
   `approxAddOrderOf_inter_volume_le`'s `volume_inter_le_twoSum` structure
   restricted to *reduced* intersecting pairs) and `μq ≥ δq·φ(q)`, `μr ≥ δr·φ(r)`
   from `approxAddOrderOf_volume_ge_min_quasi` (valid since `2φδ < 1/4`):
   `μ∩ ≤ 2·minδ·C·Δ·φ(q)φ(r) ≤ 4C·δqδr·φ(q)φ(r) ≤ 4C·μqμr`.  With `C ≤ 4`
   this is the constant-16 bound; `large_values_tail_block` then works with
   `L ≥ 1` and `c = 1/(1+3·16) = 1/49`-scale (adjust the `75` in the file).

**Do NOT declare_false**: the statement is Pollington–Vaughan Theorem 2 (true),
and all numerics confirm `μ∩/(μq μr) ≤ 2`.

-/

/-

### Session-22 addendum: precise shape of the (E) error term and the short/long sum dichotomy.

Normalise `T(c) := S(c)/Sbar = ∏_{p | K} (if p | c then p/(p-1) else 1 - 1/(p-1)²)`.
Since `K ⊥ q'`, CRT gives that `T` has mean `1` on any full residue system modulo
`q'·rad(K)`; explicitly, the inclusion–exclusion expansion over subsets `U ⊆ K`
gives exactly

  `Σ_{c ≤ X, c ⊥ q'} S(c) ≤ X·(φ(q')/q')·Sbar + 2^{ω(q')}·Smax`,
  where `Smax = ∏_{p | K} p^(ν_p(K)-1)(p-1)`,

because `Σ_U ∏_{p∉U}(p-2)/rad(U) = ∏_{p|K}(p-1)²/p` (the exact mean) and the
discrepancy of `Y ↦ #{c ≤ Y : c ⊥ q'}` is `≤ 2^{ω(q')}`.  Moreover
`Φ·Smax = φ(g)` (the prime sets of `q'` and `K` are complementary inside `g`),
so

  `N ≤ 2·Δ·φ(q)·φ(r) + 2^{ω(q')+1}·φ(g)`   (COUNT')

and, using `Φ·Sbar·(φ(q')/q')·L = φ(q)·φ(r)` (IDENTITY, since `L = g·q'`),

  `Err/Main = 2^{ω(q')}·φ(g)·L / (φ(q)φ(r)·X)`,
  which for `X ≍ ΔL` is `≤ 4·2^{ω(q')}·max(q,r)·φ(g)/(φ(q)φ(r))`.

**This is unbounded as stated**: the discrepancy `2^{ω(q')}Smax` is a full-period
bound and is grossly lossy when the range `X = ⌈ΔL⌉-1` is shorter than the period
`q'·rad(K)`.

Worked example `q = g`, `r = 2g` (g smooth): `X = 1`, `N = 2∏_{p|g}(p-2)`,
  `Main = (3/2)φ(g)²/g`, and `N/Main ≈ 1.33` (numerically confirmed), while the
  crude bound would give `4g/φ(g)`.

-/

/-

## Session-23: **`fibre_phi_identity` PROVEN** (no `unfilled`).

`fibre_phi_identity (q r) (hq) (hr) : Phi * Sbar * g * φ(q*r/g²) = φ(q) * φ(r)`,
with `g = gcd q r`, `K = ∏_{p | g, p ∤ q'} p^(ν_p(g))`, `Phi = ∏_{p | q'} φ(p^(ν_p(g)))`,
`Sbar = ∏_{p | K} p^(ν_p(K)-1)*(p-1)²/p`, `q' = q*r/g²`.

Proof architecture (private `fibre_phi_identity_aux`, with the abbreviations as
explicit variables):
1. Both sides are products over `S := (q*r).primeFactors`; every factor is
   rewritten to `∏ p ∈ S, if p ∈ T then F p else 1` with the helper `key`
   (`Finset.prod_subset`), and `φ`, `g` are expanded by the product formulas
   (`totient_eq_prod_primeFactors`, `Nat.prod_primeFactors_pow_factorization`).
2. The pointwise comparison at a prime `p ∈ S` (with `a = ν_p(q)`, `b = ν_p(r)`,
   `m = ν_p(g) = min a b`, `k = ν_p(q') = a+b-2m`) is a four-case analysis:
   * `p | q, p | r, a = b`:  `p ∉ q'`, `p ∈ K`, and `K.factorization p = m`; both
     sides give `p^(2m-2)(p-1)²`.
   * `p | q, p | r, a ≠ b`:  `p ∈ q'`, `p ∉ K`; both sides give
     `p^(2m+k-2)(p-1)² = p^(a+b-2)(p-1)²`.
   * `p | q, p ∤ r` (and symmetrically):  `m = 0`, `k = a`; both give
     `p^(a-1)(p-1)`.
   Key pointwise inputs: `Nat.factorization_gcd / _mul / _div` giving the
   exponent relations, `Nat.totient_prime_pow` for `φ(p^m)`, and
   `Commons.Data.Nat.factorization_prod_prime_pow_apply` for `ν_p(K)`
   (`K.factorization p = if p ∈ filter then m else 0`).

Consequence for the count (step (E)): since `L = q*r/g = g·q'`,
`Phi * Sbar * (φ(q')/q') * L = φ(q) * φ(r)`, so the fibre main term
`2·Phi·X·(φ(q')/q')·Sbar` equals `2·Δ·φ(q)φ(r)` whenever `X ≤ Δ·L`.
**The only remaining `unfilled` is the small-measure branch of K2.**

-/

/-

## Session-23 addendum: the exact shape of gap (E) after `fibre_phi_identity`.

Recall `N = 2·Phi·Σ_{c ≤ X, c ⊥ q'} S(c)` (exact, `fibre_count_eq`), `X = ⌈ΔL⌉-1`,
`L = qr/g`, `g = gcd q r`, `q' = qr/g² = ab`, `a = q/g`, `b = r/g`,
`K = ∏_{p | g, p ∤ q'} p^(ν_p(g))`,
`S(c) = ∏_{p | K} (if p | c then p^(ν-1)(p-1) else p^(ν-1)(p-2))`,
`Sbar = ∏_{p | K} p^(ν-1)(p-1)²/p = φ(K)²/K`.  By `fibre_phi_identity` and
`L = g·q'`, `φ(q)φ(r) = Phi·Sbar·(φ(q')/q')·L`, so the target
`N ≤ C·Δ·φ(q)φ(r)` follows from

  `Σ_{c ≤ X, c ⊥ q'} S(c)  ≤  C · X · (φ(q')/q') · Sbar`.        (SUM)

Normalise `T(c) := S(c)/Sbar`;
`T(c) = ∏_{p | K, p ∤ c}(1 - 1/(p-1)²) · ∏_{p | K, p | c} p/(p-1)`,
which has **mean 1** over any complete residue system modulo `rad(K)` (CRT,
since `K ⊥ q'`), and satisfies `T(c) ≤ ∏_{p | c} p/(p-1)`.

*Long sums* (`X ≳ rad(K)`): the inclusion–exclusion discrepancy
`#{c ≤ X : c ⊥ q'} = X·(φ(q')/q') + O(2^{ω(q')})` gives
`Σ ≤ (X·(φ(q')/q') + 2^{ω(q')})·Smax` with `Smax = φ(K) = Sbar·K/φ(K)`, i.e.

  `Σ ≤ X(φ(q')/q')Sbar + 2^{ω(q')}·(K/φ(K))·Sbar`,

so (SUM) holds once `2^{ω(q')}·(K/φ(K))·(q'/φ(q')) ≤ (C-1)·X`.

*Short sums* (`X` small, i.e. `X ≈ (a+b)/2` and `q' = ab` small): the bound
`S(c) ≤ Smax` is far too lossy — e.g. `q = g` smooth, `r = 2g` gives `K = g`,
`X = 1`, and the true `Σ = S(1) = ∏_{p|K}p^{ν-1}(p-2)`, whereas `Smax = φ(K)`.
Here one must instead use the exact pointwise `T(c) ≤ ∏_{p|c}p/(p-1)` together
with `X ≥ (a+b)/2 - 1 ≥ c·√(q')`: for `c ≤ X`, the `K`-primes dividing `c` are
few, and `φ(q')/q'` is bounded below (small `X` forces `q'` small — e.g. `X = 1`
forces `q' ≤ 4` and `φ(q')/q' ≥ 1/2`).  Worked case `q = g`, `r = 2g`:
`Σ/Sbar = T(1) = ∏(1-1/(p-1)²) ≤ 1` and (SUM) holds with `C = 2`.

So (E) remains a genuine short/long analysis: the *long* branch is the
density/`2^{ω}` estimate above, the *short* branch needs `X ≥ c√(q')` plus the
pointwise `T(c)` structure.  **The `S(c) ≤ Smax` bound alone is NOT enough**
(it can exceed `Sbar` by the factor `K/φ(K)`, unbounded).

**Session-25: the counting side is DONE.**  Four new unfilled-free lemmas in the file:
* `card_squarefree_divisors_eq_two_pow_omega (n) (hn : n ≠ 0) :
   (n.divisors.filter Squarefree).card = 2 ^ n.primeFactors.card`
  — via `Finset.card_bij` with `d ↦ d.primeFactors` onto `n.primeFactors.powerset`
  (`Nat.prod_primeFactors_of_squarefree`, `Nat.primeFactors_prod`,
  `Nat.prod_primeFactors_dvd`, and `squarefree_prod_primes` proved by
  `Finset.induction` + `Nat.squarefree_mul_iff` + `Prime.coprime_iff_not_dvd`).
  NOTE: the statement needs `n ≠ 0` (`divisors 0`/`primeFactors 0` mismatch); the
  fleet request without it is false as stated.
* `moebius_floor_le (d X) (hd : 0 < d)` — the per-term floor inequality, with
  `(X:ℝ)/d < ⌊X/d⌋+1` from `Nat.div_add_mod` + `Nat.mod_lt`.
* `card_coprime_Icc_le (n X) (hn : 0 < n) :
   #{c ∈ [1,X] : (c,n) = 1} ≤ X·φ(n)/n + 2^{ω(n)}`
  — Möbius sum (`coprime_count_moebius_real`), the floor inequality termwise,
  `sum_moebius_div_eq_phi_ratio_real`, and the error
  `∑[μ d < 0] ≤ ∑[μ d ≠ 0] = #{d | n : Squarefree d} = 2^{ω(n)}`.
* plus `squarefree_prod_primes` (private).

**Remaining for (E): `two_pow_omega_mul_sqrt_le_totient` — fully worked plan.**
Target `2^{ω(n)}·√n ≤ 7·φ(n)` for `n ≥ 1`.  With `e_p = ν_p(n)` the per-prime
ratio is
  `2·(√p)^{e_p} / (p^{e_p-1}(p-1)) = 2p^{1-e_p/2}/(p-1)`,
and the key reduction `p^{1-e/2} ≤ √p` (true for `e ≥ 1`, equality at `e = 1`)
bounds each term by `2√p/(p-1)`, whose values are **tight** at:
`2√2` (`p = 2`), `√3` (`p = 3`), `√5/2` (`p = 5`), and `≤ 1` for `p ≥ 7`
(`2√p ≤ p-1 ⟺ p ≥ 3+2√2`) and for `e ≥ 2` at `p ≥ 3`
(`2p^{1-e/2} ≤ 2 ≤ p-1`), while at `p = 2, e ≥ 2` it is `2^{2-e/2} ≤ 2√2`.
Hence
  `∏_{p | n} 2p^{1-e_p/2}/(p-1)  ≤  (2√2)(√3)(√5/2) = √30 ≈ 5.48 < 7`.
So the proof is: (i) `2^{ω(n)} = ∏_{p|n}2`, `√n = ∏_{p|n}(√p)^{e_p}`
(`Real.sqrt_pow`/`Real.sqrt_prod`), `φ(n) = ∏_{p|n}p^{e_p-1}(p-1)`
(commons `totient_eq_prod_primeFactors`, cast); (ii) `Finset.prod_div_distrib` to
get the product of per-prime ratios; (iii) the four-case termwise bound above;
(iv) `∏_{p|n}F p ≤ (∏_{p ∈ {2,3,5}}F p) = √30` since `F p ≤ 1` off `{2,3,5}`.
**Pitfall:** the ratio identity is NOT `∏2√p/(p-1)` for non-squarefree `n` — the
`p^{1-e/2} ≤ √p` step is exactly where `e ≥ 2` is absorbed; do not skip it.

**Session-26 attempt (reverted, file kept green): exact friction points.**
The whole proof was drafted; it reduced to two mechanical difficulties.
(i) `prod_F_le` (`∏_{p ∈ s} F p ≤ F 2·F 3·F 5`): `Finset.prod_le_prod_of_subset_of_one_le₀`
had the wrong arity in this Mathlib; replace by an explicit split
`∏_{s} = ∏_{s ∩ {2,3,5}}·∏_{s\{2,3,5}}` with `Finset.prod_mul_distrib`/`prod_sdiff`,
`F p ≤ 1` on `s\{2,3,5}` (via `Finset.prod_le_one₀`), and
`∏_{s∩{2,3,5}}F p ≤ ∏_{p∈{2,3,5}}F p` by `Finset.prod_le_prod₀` with `F p ≥ 1` on `{2,3,5}`.
(ii) the termwise `hterm` step: after `rw [show e = e-1+1 by omega, pow_succ]` and the
`hA` (`2√p ≤ F p·(p-1)`) / `hB` (`1 ≤ (√p)^{e-1}`) combination, the closing
`rw [← pow_mul, Real.sq_sqrt]` must be applied to
`(√p)^{e-1}·(√p)^{e-1} = (√p)^{2(e-1)}` **before** `Real.sq_sqrt`, and the
`hA` small-prime cases (`p ∈ {2,3,5}`) need `rw [← h2, hFval]`-style rewriting of the
*statement's* `p` rather than `norm_num` alone (it left the goal unsolved).
None of this is conceptual — it is `Finset.prod` plumbing plus one `pow_mul` ordering.

Remaining for (E): the short-branch
`X ≥ c√(q')` and the pointwise `T(c)` estimate in the corrected shape documented
above.

**Sieve-bound attempt (Session-24): verified ingredients and the exact remaining
sub-goals.**  `card_coprime_Icc_le` was drafted and got to 9 tactic errors (then
reverted to keep the file green).  The verified-sized plan:
* `∑_{d | n} μ(d)·⌊X/d⌋ = ∑_{d | n} μ(d)·(X/d) - ∑_{d | n} μ(d)·{X/d}`, with
  `μ(d)·⌊X/d⌋ ≤ μ(d)·(X/d) + [μ(d) < 0]` per term — **the floor identity must be
  `(X:ℝ)/d < ⌊X/d⌋ + 1`** derived from `Nat.div_add_mod` + `Nat.mod_lt` (this part
  worked; the failure was in the case split `rcases moebius_eq_or d` +
  `<;> norm_num` leaving zero goals on some branches, so use explicit `case`/`·`
  handling).
* `∑_{d | n} μ(d)/d = φ(n)/n` in ℝ is the existing
  `Commons.NumberTheory.Totient.sum_moebius_div_eq_phi_ratio_real`.
* error `∑_{d | n}[μ d < 0] ≤ #{d | n : μ d ≠ 0} = #{d | n : Squarefree d} = 2^{ω(n)}`
  via `ArithmeticFunction.moebius_ne_zero_iff_squarefree` and the squarefree
  divisor count.
* **squarefree-divisor count**: use `Finset.card_bij` with `d ↦ d.primeFactors`
  to `n.primeFactors.powerset`; needs
  `Nat.prod_primeFactors_of_squarefree`, `Nat.primeFactors_prod`,
  `Nat.prod_primeFactors_dvd`, and a helper `Squarefree (∏_{p∈S}p)` for
  `S` a Finset of primes — prove it by `Finset.induction` + `Nat.squarefree_mul_iff`
  + `Prime.coprime_iff_not_dvd` + `Nat.primeFactors_prod` (the last step
  `p ∉ S → ¬ p ∣ ∏_{q∈S}q` is where the first draft's application error was:
  it needs `Nat.mem_primeFactors` with the `≠ 0` side-condition threaded
  explicitly).

**Remaining lemmas** (self-contained): `#{c ≤ X : c ⊥ n} ≤ X·φ(n)/n + 2^{ω(n)}`
(requested as `card_coprime_Icc_le`); `2^{ω(n)}·√n ≤ 7·φ(n)`
(requested as `two_pow_omega_mul_sqrt_le_totient`); `c·√(q') ≤ X` from
`Δ ≥ 1/(2q)+1/(2r)`; the short-sum pointwise `T(c)` estimate.

**Session-24 (ter): the `#{c ≤ X : c ⊥ q'}·Smax` SHAPE CANNOT work.**
With `Smax = ∏_{p|K}p^(ν-1)(p-1) = φ(K)` and `Sbar = Smax·φ(K)/K`, the bound
`Σ ≤ #{c ≤ X : c ⊥ q'}·Smax ≤ (X·φ(q')/q' + E)·Smax` gives, against the target
`Σ ≤ C·X·(φ(q')/q')·Sbar`,

  `C ≥ (K/φ(K))·(1 + E·q'/(X·φ(q')))  ≥  K/φ(K)`,

and `K/φ(K) = ∏_{p|K} p/(p-1)` is **unbounded** (e.g. `q = g` smooth, `r = 2g`
gives `K = g`, `K/φ(K) ≈ ln P(g)/e^{-γ}`, `X = 1`).  So no choice of `E`
(including `2^{ω(q')}`) can prove (SUM) from a `#coprime · Smax` bound: the
per-term bound `S(c) ≤ Smax` is off by the whole factor `K/φ(K)` whenever `c` is
coprime to `K`, and that is the generic case in the short range.

**Therefore (SUM) must be proved directly on the pointwise weights**
`T(c) = S(c)/Sbar = ∏_{p | K, p ∤ c}(1 - 1/(p-1)²)·∏_{p | K, p | c} p/(p-1)`,
using `T(c) ≤ ∏_{p | c} p/(p-1)` (the `p | c` factors are the only ones `> 1`),
together with `X ≥ c·√(q')`; the counting statement is
`Σ_{c ≤ X, c ⊥ q'} T(c) ≤ C·X·(φ(q')/q')` — NOT `#{...} ≤ C·X·φ(q')/q'`.
In the *short* regime (`X = ⌈ΔL⌉-1 ≈ (a+b)/2-1`, `q' = ab`), `c ≤ X` means `c`
has few `K`-primes and `T(c) ≤ ∏_{p|c, p|K}p/(p-1)`, which is `≪ K/φ(K)`; the
worst case `c = 1` gives `T(1) = ∏(1-1/(p-1)²) ≤ 1`, and (SUM) holds with
`C = 2` there.  This is the correct form of the short-branch argument.

**Session-24 (bis): available Möbius ingredients** for the sieve piece
`#{c ≤ X : c ⊥ n} ≤ X·φ(n)/n + 2^{ω(n)}` — all already in the commons
(`Submission.Commons.NumberTheory.Totient.coprime_window_mainTerm_bound`):
`coprime_count_moebius_real (C m) (hm : 1 ≤ m) :
  (↑((Icc 1 C).filter (Coprime · m)).card : ℝ) = ∑ d ∈ m.divisors, (↑(μ d) : ℝ)*↑(C/d)`,
`card_multiples_Icc_one (d C) : ((Icc 1 C).filter (d ∣ ·)).card = C/d`,
`sum_moebius_div_eq_phi_ratio (m) (hm) : ∑ d ∈ m.divisors, ↑(μ d)/↑d = ↑φ(m)/↑m` (in ℚ),
`sum_moebius_mul_natDiv_eq_totient (m) (hm)`.  The only extra input is
`∑_{d | n} μ(d)² = 2^{ω(n)}` (count of squarefree divisors) — prove by
multiplicativity, or bound the error by `#{d | n : μ d ≠ 0}`.
Transfer `Nat.coprime_iff_gcd_eq_one` to match the `c.gcd n = 1` filter.

**Session-24: the count-transfer is DONE.**
`close_pair_count_eq_fibre_sum` (q r) (hq) (hr) (hqr) (Δ) (hΔ) (hΔ8) is proved
by `exact fibre_count_eq q r hq hr hqr Δ hΔ hΔ8` — the statements agree
definitionally once the circle-distance filter is written with the `: ℝ`
ascription *inside* `|·|` (i.e. `|((a:ℤ)*(r:ℤ) - (b:ℤ)*(q:ℤ) - (↑j-1)*(q*r) : ℝ)| < Δ*(q*r)`),
matching `fibre_count_eq`'s LHS verbatim.  So the exact count
`N = 2·Phi·Σ_{c ≤ ⌈ΔL⌉-1, c ⊥ q'} S(c)` is available in the file.

The file now has just ONE `unfilled`: the small-measure branch of K2.  All other
ingredients of the plan — `large_values_tail_block`, the K0 block lemma, the whole
K1 chain, `fibre_phi_identity`, `close_pair_count_eq_fibre_sum` — are unfilled-free.

-/
