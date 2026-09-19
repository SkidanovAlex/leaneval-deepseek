import Mathlib
import Submission.CrudeKernelBound

open scoped BigOperators
open Filter
open scoped Topology

noncomputable section

/-!
# The sieve criterion for DHL (Polymath8a, Lemma 3.4)

This module formalizes the "pigeonhole criterion for DHL" of Polymath8a,
*Variants of the Selberg sieve, and bounded intervals containing many primes*,
Res. Math. Sci. 1 (2014), Lemma 3.4 (see also Maynard, *Small gaps between
primes*, Ann. of Math. 181 (2015), Prop. 4.2 / Lemma 4.1).

Lemma 3.4 says: if, for each admissible `k`-tuple `H` and each residue class
`b (mod W)` with `(b + h_i, W) = 1`, one can find a non-negative weight
function `ν` and constants `α > 0`, `β_i ≥ 0` such that the *weighted sums*
(13), (14) are asymptotically `(α + o(1)) B^{-k} x/W` and
`(β_i - o(1)) B^{1-k} x/φ(W)`, and `(β_1 + ⋯ + β_k)/α > m`, then
`DHL[k, m+1]` holds: every admissible `k`-tuple has arbitrarily large
translates `n` with at least `m + 1` prime values among `n + h_i`.

The content of that criterion is *purely finitary/analytic*: it does not need
the sieve theory (which is only used to *construct* `ν` and to *verify* the
bounds (13), (14)).  This file therefore splits the criterion into

  * `exists_translate_of_sieve_bounds` -- the one-step finitary lemma at a
    fixed scale `N` (the content of the proof of Lemma 3.4), and
  * an asymptotic wrapper (`eventually_large_translate_of_bounds`) recording
    the "for all sufficiently large `N`, for some `W, b, ν` the bounds hold"
    hypothesis as a filter-event, plus the conclusion "arbitrarily large
    translates exist".

Notation follows Polymath8a (13)-(15): here `W : ℕ` is the modulus, `φ` is
Euler's totient, `B := φ(W)/W · log N`, and `θ(t) := log t` if `t` is prime,
`0` otherwise.  The main-term sizes are written out as `prefOne` (= `B^{-k}
N/W`) and `prefTwo` (= `B^{1-k} N/φ(W)`), so that later modules proving the
sieve bounds (13), (14) can `rw` to these expressions directly.
-/

namespace Commons.NumberTheory.MaynardSieve

/-- The pointwise prime logarithm `θ(t) := log t` if `t` is prime and `0`
otherwise, matching Polymath8a Lemma 3.4 (14). -/
def thetaNat (t : ℕ) : ℝ := if t.Prime then Real.log (t : ℝ) else 0

/-- The window of integers `N ≤ n ≤ 2N` in the residue class `b (mod W)`
(as a `Finset ℕ`). -/
def residueWindow (N W b : ℕ) : Finset ℕ :=
  (Finset.Icc N (2 * N)).filter fun n => n % W = b % W

/-- `∑_{N ≤ n ≤ 2N, n ≡ b (W)} ν n`, the quantity of (13). -/
def weightSum (W b N : ℕ) (ν : ℕ → ℝ) : ℝ :=
  ∑ n ∈ residueWindow N W b, ν n

/-- `∑_{N ≤ n ≤ 2N, n ≡ b (W)} ν n · θ(n + h)`, one summand of (14). -/
def thetaWeightSum (W b N : ℕ) (ν : ℕ → ℝ) (h : ℕ) : ℝ :=
  ∑ n ∈ residueWindow N W b, ν n * thetaNat (n + h)

/-- `m · log(3N)`. -/
def mlog (m N : ℕ) : ℝ := (m : ℝ) * Real.log (3 * (N : ℝ))

/-- `(W/φ(W))^k · (N/W) / (log N)^k` = `B^{-k} N/W` with `B = φ(W)/W · log N`,
the size of the main term in (13). -/
def prefOne (N W k : ℕ) : ℝ :=
  ((W : ℝ) / ((W.totient : ℕ) : ℝ)) ^ k * (N : ℝ) / (W : ℝ) /
    (Real.log (N : ℝ)) ^ k

/-- `(W/φ(W))^j · (N/φ(W)) / (log N)^j` = `B^{1-k} N/φ(W)` with `j = k - 1`,
the size of the main term in (14). -/
def prefTwo (N W j : ℕ) : ℝ :=
  ((W : ℝ) / ((W.totient : ℕ) : ℝ)) ^ j * (N : ℝ) / ((W.totient : ℕ) : ℝ) /
    (Real.log (N : ℝ)) ^ j

/-- Number of indices `i : Fin k` for which `t + H i` is prime. -/
def primeIndexCard {k : ℕ} (H : Fin k → ℕ) (t : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin k)).filter fun i => Nat.Prime (t + H i)).card

/-! ## Basic facts about the window sums -/

lemma mem_residueWindow_iff (N W b n : ℕ) :
    n ∈ residueWindow N W b ↔ N ≤ n ∧ n ≤ 2 * N ∧ n % W = b % W := by
  simp [residueWindow]
  aesop

lemma thetaNat_of_prime {t : ℕ} (ht : t.Prime) : thetaNat t = Real.log (t : ℝ) := by
  simp [thetaNat, ht]

lemma thetaNat_of_not_prime {t : ℕ} (ht : ¬ t.Prime) : thetaNat t = 0 := by
  simp [thetaNat, ht]

/-- `0 ≤ θ(t)` for every `t`. -/
lemma thetaNat_nonneg (t : ℕ) : 0 ≤ thetaNat t := by
  by_cases hp : t.Prime
  · rw [thetaNat_of_prime hp]
    have h2 : 2 ≤ (t : ℝ) := by exact_mod_cast Nat.Prime.two_le hp
    positivity
  · rw [thetaNat_of_not_prime hp]

/-- `θ(t) ≤ log M` whenever `2 ≤ t ≤ M`. -/
lemma thetaNat_le_log {t M : ℕ} (ht : 2 ≤ t) (hle : t ≤ M) :
    thetaNat t ≤ Real.log (M : ℝ) := by
  by_cases hp : t.Prime
  · rw [thetaNat_of_prime hp]
    apply Real.log_le_log
    · have h2 : 2 ≤ (t : ℝ) := by exact_mod_cast ht
      positivity
    · exact_mod_cast hle
  · rw [thetaNat_of_not_prime hp]
    exact Real.log_nonneg (by
      have hM1 : 1 ≤ M := by omega
      exact_mod_cast hM1)

/-- `0 < log N` once `2 ≤ N`. -/
lemma log_pos_of_two_le (N : ℕ) (hN : 2 ≤ N) : 0 < Real.log (N : ℝ) := by
  apply Real.log_pos
  have h2 : 2 ≤ (N : ℝ) := by exact_mod_cast hN
  linarith

lemma mlog_nonneg (m N : ℕ) : 0 ≤ mlog m N := by
  unfold mlog
  by_cases hN0 : N = 0
  · simp [hN0]
  · have hN : 1 ≤ N := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hN0)
    have hlog : 0 ≤ Real.log (3 * (N : ℝ)) := Real.log_nonneg (by
        have h3 : (1 : ℝ) ≤ 3 * (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ 3 * N)
        linarith)
    exact mul_nonneg (by exact_mod_cast (Nat.zero_le m)) hlog

/-- The totient is positive as a real once `W ≥ 1`. -/
lemma totient_real_pos (W : ℕ) (hW : 1 ≤ W) : 0 < ((W.totient : ℕ) : ℝ) := by
  have h : 0 < W.totient := Nat.totient_pos.mpr (by omega)
  positivity

/-- `prefOne N W k > 0` for `2 ≤ N`, `1 ≤ W`. -/
lemma prefOne_pos (N W k : ℕ) (hN : 2 ≤ N) (hW : 1 ≤ W) :
    0 < prefOne N W k := by
  unfold prefOne
  have hWr : 0 < (W : ℝ) := by exact_mod_cast (by omega : 0 < W)
  have hφ : 0 < ((W.totient : ℕ) : ℝ) := totient_real_pos W hW
  have hlog : 0 < Real.log (N : ℝ) := log_pos_of_two_le N hN
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hx : 0 < ((W : ℝ) / ((W.totient : ℕ) : ℝ)) ^ k := pow_pos (div_pos hWr hφ) k
  have hlogk : 0 < (Real.log (N : ℝ)) ^ k := pow_pos hlog k
  exact div_pos (div_pos (mul_pos hx hNpos) hWr) hlogk

/-- The relation `prefTwo N W (k-1) = prefOne N W k · log N`, i.e.
`B^{1-k} N/φ(W) = B^{-k} N/W · log N`. -/
lemma prefTwo_eq_prefOne_mul_log (N W k : ℕ) (hN : 2 ≤ N) (hW : 1 ≤ W) (hk : 1 ≤ k) :
    prefTwo N W (k - 1) = prefOne N W k * Real.log (N : ℝ) := by
  unfold prefTwo prefOne
  have hWr : (W : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (by omega : 0 < W))
  have hφ : ((W.totient : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Nat.totient_pos.mpr (by omega : 0 < W)))
  have hlog : Real.log (N : ℝ) ≠ 0 := ne_of_gt (log_pos_of_two_le N hN)
  let j := k - 1
  have hk' : k = j + 1 := by
    dsimp [j]
    omega
  rw [hk']
  have hsub : (j + 1) - 1 = j := by omega
  rw [hsub]
  rw [pow_succ, pow_succ]
  field_simp [hWr, hφ, hlog]

/-! ## The one-step criterion (content of the proof of Polymath8a Lemma 3.4) -/

/-- **One-step sieve criterion.**  Fix a scale `N`, a modulus `W ≥ 1`, a
residue class `b (mod W)` and a non-negative weight `ν`.  Suppose the weighted
window sum (13) is bounded above by `(α + e)·prefOne` and each weighted
`θ`-sum (14) is bounded below by `(β_i - e)·prefTwo`, with
`(Σ β_i - k e) log N > m (α + e) log(3N)`.  Then some `n ∈ [N, 2N]` has at
least `m + 1` prime values among `n + H i`.

This is exactly the pigeonhole step of Lemma 3.4 at the scale `N` (their
quantity `N > 0`), with the `o(1)` errors of (13), (14) all bounded by a
single `e ≥ 0`. -/
theorem exists_translate_of_sieve_bounds {k m N : ℕ} {H : Fin k → ℕ} {W b : ℕ}
    {ν : ℕ → ℝ} {α : ℝ} {β : Fin k → ℝ} {e : ℝ}
    (hk : 1 ≤ k) (hN : 2 ≤ N) (hW : 1 ≤ W) (hmax : ∀ i : Fin k, H i ≤ N)
    (_hα : 0 < α) (_he : 0 ≤ e) (hν : ∀ n : ℕ, 0 ≤ ν n)
    (hS1 : weightSum W b N ν ≤ (α + e) * prefOne N W k)
    (hS2 : ∀ i : Fin k,
      (β i - e) * prefTwo N W (k - 1) ≤ thetaWeightSum W b N ν (H i))
    (hmain : (∑ i : Fin k, β i - (k : ℝ) * e) * Real.log (N : ℝ) >
      (α + e) * mlog m N) :
    ∃ n : ℕ, N ≤ n ∧ n ≤ 2 * N ∧ ν n > 0 ∧ m + 1 ≤ primeIndexCard H n := by
  classical
  let ml := mlog m N
  let win := residueWindow N W b
  let S2 : Fin k → ℝ := fun i => thetaWeightSum W b N ν (H i)
  let g : ℕ → ℝ := fun n => (∑ i : Fin k, thetaNat (n + H i)) - ml
  let M : ℝ := ∑ n ∈ win, ν n * g n
  have hM_eq : M = (∑ i : Fin k, S2 i) - ml * weightSum W b N ν := by
    calc
      M = ∑ n ∈ win, (ν n * (∑ i : Fin k, thetaNat (n + H i)) - ν n * ml) := by
          simp [M, g, mul_sub]
      _ = (∑ n ∈ win, ν n * (∑ i : Fin k, thetaNat (n + H i))) -
            ∑ n ∈ win, ν n * ml := by
          rw [Finset.sum_sub_distrib]
      _ = (∑ i : Fin k, ∑ n ∈ win, ν n * thetaNat (n + H i)) -
            ml * (∑ n ∈ win, ν n) := by
          congr 1
          · calc
              (∑ n ∈ win, ν n * (∑ i : Fin k, thetaNat (n + H i)))
                  = ∑ n ∈ win, ∑ i : Fin k, ν n * thetaNat (n + H i) := by
                      refine Finset.sum_congr rfl ?_
                      intro n hn
                      rw [Finset.mul_sum]
              _ = ∑ i : Fin k, ∑ n ∈ win, ν n * thetaNat (n + H i) := by
                      simpa using (Finset.sum_comm (s := win)
                        (t := (Finset.univ : Finset (Fin k)))
                        (f := fun n i => ν n * thetaNat (n + H i)))
          · calc
              (∑ n ∈ win, ν n * ml) = (∑ n ∈ win, ν n) * ml := by
                      rw [← Finset.sum_mul]
              _ = ml * (∑ n ∈ win, ν n) := by rw [mul_comm]
      _ = (∑ i : Fin k, S2 i) - ml * weightSum W b N ν := by
          rfl
  have hml_nonneg : 0 ≤ ml := by
    dsimp [ml]
    exact mlog_nonneg m N
  have hS2_sum : ∑ i : Fin k, S2 i ≥
      ∑ i : Fin k, (β i - e) * prefTwo N W (k - 1) := by
    exact Finset.sum_le_sum (by intro i hi; exact hS2 i)
  have hS1_mul : ml * weightSum W b N ν ≤ ml * ((α + e) * prefOne N W k) := by
    exact mul_le_mul_of_nonneg_left hS1 hml_nonneg
  have hM_lower : (∑ i : Fin k, (β i - e) * prefTwo N W (k - 1)) -
      ml * ((α + e) * prefOne N W k) ≤ M := by
    nlinarith [hS2_sum, hS1_mul, hM_eq]
  have hpref : 0 < prefOne N W k := prefOne_pos N W k hN hW
  have hM_pos : 0 < M := by
    have hrel : prefTwo N W (k - 1) = prefOne N W k * Real.log (N : ℝ) :=
      prefTwo_eq_prefOne_mul_log N W k hN hW hk
    have hsum2 : (∑ i : Fin k, (β i - e)) = (∑ i : Fin k, β i) - (k : ℝ) * e := by
      rw [Finset.sum_sub_distrib]
      simp [Finset.sum_const, nsmul_eq_mul]
    have hsum : (∑ i : Fin k, (β i - e) * prefTwo N W (k - 1)) =
        ((∑ i : Fin k, β i) - (k : ℝ) * e) * prefTwo N W (k - 1) := by
      calc
        (∑ i : Fin k, (β i - e) * prefTwo N W (k - 1))
            = (∑ i : Fin k, (β i - e)) * prefTwo N W (k - 1) := by
                rw [← Finset.sum_mul]
        _ = ((∑ i : Fin k, β i) - (k : ℝ) * e) * prefTwo N W (k - 1) := by
                rw [hsum2]
    have hbr : 0 < ((∑ i : Fin k, β i) - (k : ℝ) * e) * Real.log (N : ℝ) -
        (α + e) * ml := by
      dsimp [ml]
      nlinarith [hmain]
    have hmain_est : 0 < prefOne N W k *
        (((∑ i : Fin k, β i) - (k : ℝ) * e) * Real.log (N : ℝ) - (α + e) * ml) := by
      exact mul_pos hpref hbr
    have hprod_eq : prefOne N W k *
        (((∑ i : Fin k, β i) - (k : ℝ) * e) * Real.log (N : ℝ) - (α + e) * ml) =
        ((∑ i : Fin k, (β i - e) * prefTwo N W (k - 1)) -
          ml * ((α + e) * prefOne N W k)) := by
      rw [hsum, hrel]
      ring
    have hpos : 0 < (∑ i : Fin k, (β i - e) * prefTwo N W (k - 1)) -
        ml * ((α + e) * prefOne N W k) := by
      simpa [hprod_eq] using hmain_est
    exact lt_of_lt_of_le hpos hM_lower
  -- find a window element with ν n > 0 and g n > 0
  have hex : ∃ n, n ∈ win ∧ ν n > 0 ∧ g n > 0 := by
    by_contra hnone
    have hall : ∀ n ∈ win, ν n * g n ≤ 0 := by
      intro n hn
      by_cases hg : g n ≤ 0
      · have hνn : 0 ≤ ν n := hν n
        nlinarith
      · have hgpos : 0 < g n := lt_of_not_ge hg
        have hνn0 : ¬ 0 < ν n := by
          intro hp
          exact hnone ⟨n, hn, hp, hgpos⟩
        have hνn : ν n ≤ 0 := not_lt.mp hνn0
        nlinarith
    have hMle : M ≤ 0 := by
      simp [M]
      exact Finset.sum_nonpos (by intro n hn; exact hall n hn)
    nlinarith
  rcases hex with ⟨n, hn, hνn, hgn⟩
  have hnlo : N ≤ n := (mem_residueWindow_iff N W b n).mp hn |>.1
  have hnhi : n ≤ 2 * N := (mem_residueWindow_iff N W b n).mp hn |>.2.1
  -- count the prime values
  have hlog3pos : 0 < Real.log (3 * (N : ℝ)) := by
    apply Real.log_pos
    have hN2 : 2 ≤ (N : ℝ) := by exact_mod_cast hN
    nlinarith
  have hle3N : ∀ i : Fin k, n + H i ≤ 3 * N := by
    intro i
    have hHi : H i ≤ N := hmax i
    have hsum : n + H i ≤ 2 * N + N := Nat.add_le_add hnhi hHi
    rw [show 2 * N + N = 3 * N by ring] at hsum
    exact hsum
  have hterm : ∀ i : Fin k, thetaNat (n + H i) ≤ Real.log (3 * (N : ℝ)) := by
    intro i
    by_cases hp : Nat.Prime (n + H i)
    · rw [thetaNat_of_prime hp]
      apply Real.log_le_log
      · have h2 : 2 ≤ n + H i := Nat.Prime.two_le hp
        positivity
      · exact_mod_cast hle3N i
    · rw [thetaNat_of_not_prime hp]
      exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 3 * N))
  have hθsum : (∑ i : Fin k, thetaNat (n + H i)) =
      ∑ i ∈ ((Finset.univ : Finset (Fin k)).filter fun i => Nat.Prime (n + H i)),
        Real.log ((n + H i : ℕ) : ℝ) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hp : Nat.Prime (n + H i)
    · rw [if_pos hp, thetaNat_of_prime hp]
    · rw [if_neg hp]
      simp [thetaNat, hp]
  have hprime_sum_le : (∑ i ∈
        ((Finset.univ : Finset (Fin k)).filter fun i => Nat.Prime (n + H i)),
          Real.log ((n + H i : ℕ) : ℝ)) ≤
      (primeIndexCard H n : ℝ) * Real.log (3 * (N : ℝ)) := by
    let P := (Finset.univ : Finset (Fin k)).filter fun i => Nat.Prime (n + H i)
    have hle : ∀ i ∈ P, Real.log ((n + H i : ℕ) : ℝ) ≤ Real.log (3 * (N : ℝ)) := by
      intro i hi
      have hprime : Nat.Prime (n + H i) := (Finset.mem_filter.mp hi).2
      apply Real.log_le_log
      · have h2 : 2 ≤ n + H i := Nat.Prime.two_le hprime
        positivity
      · exact_mod_cast hle3N i
    have hsumle : P.sum (fun i => Real.log ((n + H i : ℕ) : ℝ)) ≤
        P.card • Real.log (3 * (N : ℝ)) :=
      Finset.sum_le_card_nsmul P (fun i => Real.log ((n + H i : ℕ) : ℝ))
        (Real.log (3 * (N : ℝ))) hle
    have hP : P = ((Finset.univ : Finset (Fin k)).filter fun i => Nat.Prime (n + H i)) := rfl
    simpa [P, primeIndexCard, nsmul_eq_mul] using hsumle
  have hθgt : (∑ i : Fin k, thetaNat (n + H i)) > mlog m N := by
    have hg : 0 < (∑ i : Fin k, thetaNat (n + H i)) - ml := hgn
    dsimp [ml] at hg
    linarith
  have hcard_gt : (m : ℝ) < (primeIndexCard H n : ℝ) := by
    have h1 : (∑ i : Fin k, thetaNat (n + H i)) ≤
        (primeIndexCard H n : ℝ) * Real.log (3 * (N : ℝ)) := by
      rw [hθsum]
      exact hprime_sum_le
    have h3 : (m : ℝ) * Real.log (3 * (N : ℝ)) <
        (primeIndexCard H n : ℝ) * Real.log (3 * (N : ℝ)) := by
      simpa [mlog] using (lt_of_lt_of_le hθgt h1)
    exact (mul_lt_mul_iff_of_pos_right hlog3pos).mp h3
  refine ⟨n, hnlo, hnhi, hνn, ?_⟩
  exact_mod_cast hcard_gt


/-! ## Asymptotic plumbing (helper lemmas about `Tendsto` and `∀ᶠ`) -/

/-- `|ε N| < δ` eventually, for any `δ > 0`, when `|ε N| → 0`. -/
lemma eventually_abs_lt_of_tendsto {ε : ℕ → ℝ}
    (hε : Tendsto (fun N => |ε N|) atTop (𝓝 (0 : ℝ))) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N in atTop, |ε N| < δ := by
  have hb : Metric.ball (0 : ℝ) δ ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds 0 hδ
  have h : ∀ᶠ N in atTop, |ε N| ∈ Metric.ball (0 : ℝ) δ := hε hb
  refine h.mono ?_
  intro N hN
  simpa [Real.dist_eq] using (Metric.mem_ball.mp hN)

/-- `log N → +∞` as the natural `N → ∞`. -/
lemma tendsto_log_nat_atTop : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop := by
  exact Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- `log(3N) / log N → 1` as `N → ∞`. -/
lemma tendsto_log_three_ratio :
    Tendsto (fun N : ℕ => Real.log (3 * (N : ℝ)) / Real.log (N : ℝ)) atTop (𝓝 (1 : ℝ)) := by
  have hinv : Tendsto (fun N : ℕ => (Real.log (N : ℝ))⁻¹) atTop (𝓝 (0 : ℝ)) := by
    simpa [Function.comp_def] using (tendsto_inv_atTop_zero.comp tendsto_log_nat_atTop)
  have hlog3 : Tendsto (fun N : ℕ => Real.log (3 : ℝ) * (Real.log (N : ℝ))⁻¹) atTop (𝓝 (0 : ℝ)) := by
    have h := (tendsto_const_nhds.mul hinv :
      Tendsto (fun N : ℕ => Real.log (3 : ℝ) * (Real.log (N : ℝ))⁻¹) atTop (𝓝 (Real.log (3 : ℝ) * 0)))
    simpa using h
  have hmain : Tendsto (fun N : ℕ => Real.log (3 : ℝ) * (Real.log (N : ℝ))⁻¹ + 1) atTop (𝓝 (1 : ℝ)) := by
    simpa using (hlog3.add (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (1 : ℝ))))
  have heq : (fun N : ℕ => Real.log (3 : ℝ) * (Real.log (N : ℝ))⁻¹ + 1) =ᶠ[atTop]
      (fun N : ℕ => Real.log (3 * (N : ℝ)) / Real.log (N : ℝ)) := by
    refine (eventually_ge_atTop (2 : ℕ)).mono ?_
    intro N hN
    have hN0 : N ≠ 0 := by omega
    have hlog : Real.log (N : ℝ) ≠ 0 := by
      apply ne_of_gt
      apply Real.log_pos
      exact_mod_cast (by omega : 1 < N)
    have hlogmul : Real.log (3 * (N : ℝ)) = Real.log (3 : ℝ) + Real.log (N : ℝ) := by
      apply Real.log_mul
      · norm_num
      · exact_mod_cast (ne_of_gt (Nat.pos_of_ne_zero hN0))
    dsimp
    rw [hlogmul]
    field_simp [hlog]
  exact hmain.congr' heq

/-- If `a N → A` and `b N → B` with `B < A`, then `b N < a N` eventually. -/
lemma eventually_gt_of_tendsto {a b : ℕ → ℝ} {A B : ℝ}
    (ha : Tendsto a atTop (𝓝 A)) (hb : Tendsto b atTop (𝓝 B)) (hAB : B < A) :
    ∀ᶠ N in atTop, b N < a N := by
  let η := (A - B) / 2
  have hη : 0 < η := by
    dsimp [η]
    linarith
  have hA : ∀ᶠ N in atTop, |a N - A| < η := by
    have hb' : Metric.ball A η ∈ 𝓝 A := Metric.ball_mem_nhds A hη
    have h : ∀ᶠ N in atTop, a N ∈ Metric.ball A η := ha hb'
    refine h.mono ?_
    intro N hN
    simpa [Real.dist_eq] using (Metric.mem_ball.mp hN)
  have hB : ∀ᶠ N in atTop, |b N - B| < η := by
    have hb' : Metric.ball B η ∈ 𝓝 B := Metric.ball_mem_nhds B hη
    have h : ∀ᶠ N in atTop, b N ∈ Metric.ball B η := hb hb'
    refine h.mono ?_
    intro N hN
    simpa [Real.dist_eq] using (Metric.mem_ball.mp hN)
  refine (hA.and hB).mono ?_
  intro N hN
  rcases hN with ⟨hAe, hBe⟩
  have hbN : b N < B + η := by
    have hx := (abs_lt.mp hBe).2
    linarith
  have haN : A - η < a N := by
    have hx := (abs_lt.mp hAe).1
    linarith
  have h2 : 2 * η = A - B := by
    dsimp [η]
    ring
  have hbr : B + η ≤ A - η := by nlinarith
  exact lt_trans (lt_of_lt_of_le hbN hbr) haN

/-! ## The asymptotic wrapper (the filter form of Polymath8a Lemma 3.4) -/

/-- The sieve estimates (13), (14) of Polymath8a Lemma 3.4, for a family of
weights `ν N`, moduli `W N` and residue classes `b N`, with all `o(1)` errors
of (13), (14) bounded by a common `|ε N|`, where `|ε N| → 0`. -/
def SieveBounds {k : ℕ} (H : Fin k → ℕ) (α : ℝ) (β : Fin k → ℝ) (ε : ℕ → ℝ)
    (ν : ℕ → ℕ → ℝ) (W b : ℕ → ℕ) : Prop :=
  ∀ᶠ N : ℕ in atTop,
    (1 ≤ W N) ∧
    (∀ n : ℕ, 0 ≤ ν N n) ∧
    (weightSum (W N) (b N) N (ν N) ≤ (α + |ε N|) * prefOne N (W N) k) ∧
    (∀ i : Fin k,
      (β i - |ε N|) * prefTwo N (W N) (k - 1) ≤ thetaWeightSum (W N) (b N) N (ν N) (H i))

/-- **Asymptotic sieve criterion** (Polymath8a Lemma 3.4, filter form).

If a family of non-negative weights `ν` (with moduli `W N` and residue classes
`b N`) satisfies the asymptotic upper bound (13) `Σν ≤ (α + o(1)) B^{-k} N/W`
and the asymptotic lower bounds (14) `Σν θ(n + h_i) ≥ (β_i - o(1)) B^{1-k}
N/φ(W)` for all `i`, with `(β_1 + ⋯ + β_k)/α > m`, then arbitrarily large
translates `n` have at least `m + 1` prime values among `n + h_i`. -/
theorem eventually_large_translate_of_sieve_bounds {k m : ℕ} {H : Fin k → ℕ}
    (hk : 1 ≤ k) (hHmax : ∃ hmax : ℕ, ∀ i : Fin k, H i ≤ hmax)
    {α : ℝ} (hα : 0 < α) {β : Fin k → ℝ} (hβm : m * α < (∑ i : Fin k, β i))
    {ε : ℕ → ℝ} (hε : Tendsto (fun N => |ε N|) atTop (𝓝 (0 : ℝ)))
    {ν : ℕ → ℕ → ℝ} {W b : ℕ → ℕ} (hB : SieveBounds (k := k) H α β ε ν W b) :
    ∀ N0 : ℕ, ∃ n : ℕ, N0 ≤ n ∧ m + 1 ≤ primeIndexCard H n := by
  classical
  intro N0
  rcases hHmax with ⟨hmax, hHmax⟩
  have hν_ev : ∀ᶠ N : ℕ in atTop, ∀ n : ℕ, 0 ≤ ν N n := by
    exact hB.mono (by intro N h; exact h.2.1)
  have hS1_ev : ∀ᶠ N : ℕ in atTop,
      weightSum (W N) (b N) N (ν N) ≤ (α + |ε N|) * prefOne N (W N) k := by
    exact hB.mono (by intro N h; exact h.2.2.1)
  have hS2_ev : ∀ᶠ N : ℕ in atTop, ∀ i : Fin k,
      (β i - |ε N|) * prefTwo N (W N) (k - 1) ≤ thetaWeightSum (W N) (b N) N (ν N) (H i) := by
    exact hB.mono (by intro N h; exact h.2.2.2)
  have hmaine : ∀ᶠ N : ℕ in atTop,
      (∑ i : Fin k, β i - (k : ℝ) * |ε N|) * Real.log (N : ℝ) >
        (α + |ε N|) * mlog m N := by
    let aN : ℕ → ℝ := fun N => (∑ i : Fin k, β i) - (k : ℝ) * |ε N|
    let bN : ℕ → ℝ := fun N =>
      (m : ℝ) * (α + |ε N|) * (Real.log (3 * (N : ℝ)) / Real.log (N : ℝ))
    have hkeps : Tendsto (fun N : ℕ => (k : ℝ) * |ε N|) atTop (𝓝 (0 : ℝ)) := by
      have h := (tendsto_const_nhds.mul hε :
        Tendsto (fun N : ℕ => (k : ℝ) * |ε N|) atTop (𝓝 ((k : ℝ) * 0)))
      simpa using h
    have hA_const : Tendsto (fun N : ℕ => (∑ i : Fin k, β i)) atTop (𝓝 (∑ i : Fin k, β i)) :=
      tendsto_const_nhds
    have ha : Tendsto aN atTop (𝓝 (∑ i : Fin k, β i)) := by
      dsimp [aN]
      simpa using (hA_const.sub hkeps)
    have hαeps : Tendsto (fun N : ℕ => α + |ε N|) atTop (𝓝 α) := by
      simpa using (tendsto_const_nhds.add hε :
        Tendsto (fun N : ℕ => α + |ε N|) atTop (𝓝 (α + 0)))
    have hprod1 : Tendsto (fun N : ℕ => (m : ℝ) * (α + |ε N|)) atTop (𝓝 ((m : ℝ) * α)) := by
      simpa using ((tendsto_const_nhds.mul hαeps) :
        Tendsto (fun N : ℕ => (m : ℝ) * (α + |ε N|)) atTop (𝓝 ((m : ℝ) * α)))
    have hb : Tendsto bN atTop (𝓝 ((m : ℝ) * α)) := by
      dsimp [bN]
      simpa using (hprod1.mul tendsto_log_three_ratio)
    have hab : ∀ᶠ N : ℕ in atTop, bN N < aN N :=
      eventually_gt_of_tendsto ha hb (by simpa using hβm)
    have hlogpos : ∀ᶠ N : ℕ in atTop, 0 < Real.log (N : ℝ) := by
      refine (eventually_ge_atTop (2 : ℕ)).mono ?_
      intro N hN
      exact log_pos_of_two_le N hN
    refine (hab.and hlogpos).mono ?_
    intro N h
    rcases h with ⟨hlt, hlog⟩
    have hmul : bN N * Real.log (N : ℝ) < aN N * Real.log (N : ℝ) :=
      mul_lt_mul_of_pos_right hlt hlog
    have hbN : bN N * Real.log (N : ℝ) = (α + |ε N|) * mlog m N := by
      dsimp [bN, mlog]
      field_simp [ne_of_gt hlog]
    have hmainN : (α + |ε N|) * mlog m N < aN N * Real.log (N : ℝ) := by
      rwa [hbN] at hmul
    simpa [aN] using hmainN
  have hQ : ∀ᶠ N : ℕ in atTop,
      ∃ n : ℕ, N0 ≤ n ∧ m + 1 ≤ primeIndexCard H n := by
    have h0 : ∀ᶠ N : ℕ in atTop, 2 ≤ N := eventually_ge_atTop 2
    have h1 : ∀ᶠ N : ℕ in atTop, hmax ≤ N := eventually_ge_atTop hmax
    have h2 : ∀ᶠ N : ℕ in atTop, N0 ≤ N := eventually_ge_atTop N0
    refine ((((h0.and h1).and h2).and hB).and hmaine).mono ?_
    intro N h
    rcases h with ⟨hrest, hmain⟩
    rcases hrest with ⟨hmore, hBpart⟩
    rcases hmore with ⟨h01, hN0le⟩
    rcases h01 with ⟨h2N, hmaxN⟩
    rcases hBpart with ⟨hW1, hνn, hS1, hS2⟩
    have hHmaxN : ∀ i : Fin k, H i ≤ N := by
      intro i
      exact le_trans (hHmax i) hmaxN
    obtain ⟨n, hn1, hn2, hnν, hnc⟩ :=
      exists_translate_of_sieve_bounds (k := k) (m := m) (N := N) (H := H)
        (W := W N) (b := b N) (ν := ν N) (α := α) (β := β) (e := |ε N|)
        hk h2N hW1 hHmaxN hα (abs_nonneg (ε N)) hνn hS1 hS2 hmain
    exact ⟨n, le_trans hN0le hn1, hnc⟩
  rcases (Filter.eventually_atTop.mp hQ) with ⟨B, hB2⟩
  let M := max B N0
  have hM : B ≤ M := le_max_left B N0
  rcases (hB2 M hM) with ⟨n, hn⟩
  exact ⟨n, hn.1, hn.2⟩


/-- **Two-prime version of the sieve criterion** (the case `m = 1`, giving
`DHL[k,2]`): under the same hypotheses but with `α < Σ_i β_i`, arbitrarily
large translates `n` have at least two prime values among `n + H i`. -/
theorem translate_two_primes_of_sieve_bounds {k : ℕ} {H : Fin k → ℕ}
    (hk : 1 ≤ k) (hHmax : ∃ hmax : ℕ, ∀ i : Fin k, H i ≤ hmax)
    {α : ℝ} (hα : 0 < α) {β : Fin k → ℝ} (hβm : α < (∑ i : Fin k, β i))
    {ε : ℕ → ℝ} (hε : Tendsto (fun N : ℕ => |ε N|) atTop (𝓝 (0 : ℝ)))
    {ν : ℕ → ℕ → ℝ} {W b : ℕ → ℕ} (hB : SieveBounds (k := k) H α β ε ν W b) :
    ∀ N0 : ℕ, ∃ n : ℕ, N0 ≤ n ∧ 2 ≤ primeIndexCard H n := by
  intro N0
  rcases (eventually_large_translate_of_sieve_bounds (k := k) (m := 1)
      hk hHmax hα (β := β) (by simpa using hβm) (ε := ε) hε (ν := ν) (W := W) (b := b) hB N0)
    with ⟨n, hn1, hn2⟩
  exact ⟨n, hn1, by simpa using hn2⟩

end Commons.NumberTheory.MaynardSieve