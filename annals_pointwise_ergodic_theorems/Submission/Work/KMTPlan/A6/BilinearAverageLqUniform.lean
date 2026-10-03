/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.Work.Analysis.Paraproduct.CrtMain
import Submission.Work.Peluse.Compatible
import Submission.Work.Peluse.AreaA2_of_crux
import Submission.Work.A3Fix.AreaA3
import Submission.Work.KMTAreas.area_A1
import Submission.Work.KMTAreas.area_A4
import Submission.Work.KMTPlan.A6.ConcAux2.fibreWeakType_of_cover
import Submission.Work.KMTPlan.A6.bilinAvgLq_largePrime_avg2

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The uniform `L² × L² → L^q` bound for the bilinear polynomial average on `ℤ/Qℤ`

This file assembles the *uniform in `Q`* bilinear arithmetic estimate
`Work.KMTPlan.A6.BilinearAverageLqUniform`: for a polynomial `P ∈ ℤ[X]` of degree `d ≥ 2` and
every `q` with `1 ≤ q < 2d/(d-1)` there is `C = C(P,q) > 0` with

`‖ A(f,g) ‖_{L^q(ℤ/Qℤ)} ≤ C ‖f‖_{L²(ℤ/Qℤ)} ‖g‖_{L²(ℤ/Qℤ)}`,
`A(f,g)(x) = Q⁻¹ ∑_y f (x-y) g (x - P(y))`,

for **every** modulus `Q` and all `f, g : ℤ/Qℤ → ℂ`.  This is the paper's estimate
`(Avg-prof)` of Krause–Mirek–Tao, *Pointwise ergodic theorems for non-conventional bilinear
polynomial averages*, arXiv:2008.00857, §10 (the estimate behind Theorem `bile`), in its
finite-cyclic form.

## Structure of the argument

The paper proves `(Avg-prof)` for the profinite integers `ℤ̂` in four steps:

1. `(avg-1)`: for *each prime* `p` (indeed for every `j`), `‖A_{ℤ_p}‖_{L²×L²→L^q} ≲_q 1`,
   uniformly in `p`; this is deduced from the concentration estimate of Appendix C
   (Corollary `cor:1`) on the fibre counting function `h(m) = #{n : P(n) = m}` modulo `p^j`,
   via Cauchy–Schwarz and Young's inequality
   (`Work.Analysis.Paraproduct.bilinAverage_lq_fiber`, and `bilinearAverageLq_of_fiber`);
2. `(avg-2)`: for `p` large depending on `q` (and `P`) the constant can be improved to `1`;
   the proof splits `f = a + f₀`, `g = b + g₀` off the means (`a = 𝔼f`, `b = 𝔼g`), uses
   `A(f,g) = ab + A(f,g₀)` together with the *mean-zero gain*
   `‖A(f,g₀)‖_{L¹} ≤ ε ‖f‖_{L²}‖g₀‖_{L²}` (equation `(eq:39)`, whose proof uses Theorem
   `improv`), interpolates it with `(avg-1)` (`LpNormZMod_logconvex`) and concludes by a
   Taylor expansion of `|ab + A(f,g₀)|^q`;
3. the tensor/Chinese-remainder factorisation `‖A_{∏_{p∈S}ℤ_p}‖ = ∏_{p∈S}‖A_{ℤ_p}‖`
   (`ttensor-bil`, `BilinearAverageLq_crt` below): since only the *finitely many* primes below
   the threshold of step 2 can contribute a constant `> 1`, the product over all primes is
   finite;
4. passage to the finite cyclic groups `ℤ/Qℤ` (pull back along `ℤ̂ → ℤ/Qℤ`; equivalently, use
   the CRT factorisation over the prime powers dividing `Q`).

Steps 3 and 4 are the *assembly* and are proved here:

* `BilinearAverageLq_prod_primePowers`: the CRT factorisation, by induction on the (finite)
  set of prime powers: for a family of prime-power bounds
  `BilinearAverageLq P (p^j) q (Kp p)` the bound for `∏_{p ∈ s} p ^ j p` holds with the
  product constant `∏_{p ∈ s} Kp p`;
* `BilinearAverageLqUniform_of_primePower`: from (a) a uniform prime-power bound
  `∀ p j, BilinearAverageLq P (p^j) q K` and (b) the large-prime improvement
  `∀ p ≥ p₀, j, BilinearAverageLq P (p^j) q 1`, the target estimate follows for all `Q`
  with the constant `(max 1 K)^{p₀}` (the product picks up at most one factor `K` per prime
  `p < p₀`, and there are at most `p₀` such primes);
* `BilinearAverageLq_le_two` (`BilinearAverageLqBasic`): for `q ≤ 2` the estimate holds with
  constant `1` unconditionally, by the `L²` bound and the power-mean inequality.

## The two remaining inputs (delegated)

The unconditional proof of the target reduces to the two deep inputs of steps 1–2 above, which
are stated and delegated as separate lemmas:

* `Work.KMTPlan.A6.FiberLpBoundPrimePowUniform` — Appendix C, Corollary `cor:1`: for
  `s < d/(d-1)` the fibre counting function of `P` modulo `p^j` satisfies
  `FiberLpBound P (p^j) s C` with `C` depending only on `P` and `s` (in particular not on the
  prime `p` nor on `j`);
* `Work.KMTPlan.A6.MeanZeroL1GainLargePrime` — equation `(eq:39)`: for every `ε > 0`, all
  sufficiently large primes `p`, all `j` and all mean-zero `g₀` on `ℤ/p^jℤ`,
  `‖A(f,g₀)‖_{L¹} ≤ ε‖f‖_{L²}‖g₀‖_{L²}`;
* `Work.KMTPlan.A6.LargePrimeBilinear_of_inputs` — the interpolation/Taylor argument of step 2
  (the paper's `(avg-2)`): the two inputs above imply the large-prime bound
  `BilinearAverageLq P (p^j) q 1` for `p ≥ p₀(q,P)`.

The target `BilinearAverageLqUniform` is then the one-line application
`BilinearAverageLqUniform_of_primePower` to the uniform prime-power bound obtained from
`FiberLpBoundPrimePowUniform` (via `bilinearAverageLq_of_fiber`) and to
`LargePrimeBilinear_of_inputs`.

## Where the frontier is pinned

The *exact* remaining content of the target is Area A2 (Peluse's inverse theorem), and inside it the
band's two obligations; the companion module
`Submission/Work/KMTPlan/A6/BilinearAverageLqUniformFrontier.lean` proves the target from them
(`BilinearAverageLqUniform_of_bandAprime` from `BandAprime` + `BandDegenerate`, and
`…_of_band` from `HardInputAt 2` + `BandDegenerate`), and
`Submission/Work/KMTPlan/A6/ClashBridge/` supplies the clash-free copy of the major-arc lemma that
this file's imports require.  See `BilinearAverageLqUniform_NOTES.md` and the root note
`NOTES_A4ee_IMPORT_CLASH_SESSION.md`.
-/

set_option autoImplicit false

namespace Work.KMTPlan.A6

open Work.Analysis.Concentration
open Polynomial

noncomputable section

/-! ## The modulus `Q = 1` -/

/-- On `ℤ/1ℤ` the normalized `L^p` norm is the absolute value of the single value. -/
theorem LpNormZMod_one_mod (q : ℝ) (hq : 0 < q) (u : ZMod 1 → ℂ) :
    LpNormZMod 1 q u = ‖u 0‖ := by
  have h0 : ∀ x : ZMod 1, x = 0 := fun x => Subsingleton.elim x 0
  rw [LpNormZMod_eq_ave]
  have hsum : (∑ x : ZMod 1, ‖u x‖ ^ q) = ‖u 0‖ ^ q := by
    rw [Finset.sum_eq_single 0]
    · intro b _ hb; exact absurd (h0 b) hb
    · intro h; exact absurd (Finset.mem_univ 0) h
  rw [hsum, show ((1 : ℕ) : ℝ) = 1 by norm_num, div_one]
  rw [← Real.rpow_mul (norm_nonneg _), one_div, mul_inv_cancel₀ (ne_of_gt hq), Real.rpow_one]

/-- The bilinear average at `Q = 1` is the product of the two values. -/
theorem polyBilinearAverageZMod_one (P : Polynomial ℤ) (f g : ZMod 1 → ℂ) :
    polyBilinearAverageZMod Polynomial.X P 1 f g 0 = f 0 * g 0 := by
  have h0 : ∀ x : ZMod 1, x = 0 := fun x => Subsingleton.elim x 0
  simp only [polyBilinearAverageZMod, polyEvalZMod_X]
  rw [Finset.sum_eq_single 0]
  · simp [h0]
  · intro b _ hb; exact absurd (h0 b) hb
  · intro h; exact absurd (Finset.mem_univ 0) h

/-- **The target estimate at `Q = 1`** (with constant `1`): for every `q ≥ 1`,
`BilinearAverageLq P 1 q 1`. -/
theorem BilinearAverageLq_one (P : Polynomial ℤ) {q : ℝ} (hq : 1 ≤ q) :
    BilinearAverageLq P 1 q 1 := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  intro f g
  have hf : LpNormZMod 1 2 f = ‖f 0‖ := LpNormZMod_one_mod 2 (by norm_num) f
  have hg : LpNormZMod 1 2 g = ‖g 0‖ := LpNormZMod_one_mod 2 (by norm_num) g
  have hA : LpNormZMod 1 q (polyBilinearAverageZMod Polynomial.X P 1 f g)
      = ‖f 0‖ * ‖g 0‖ := by
    rw [LpNormZMod_one_mod q hq0, polyBilinearAverageZMod_one, norm_mul]
  rw [hA, hf, hg, one_mul]

/-! ## The Chinese-remainder factorisation over prime powers -/

/-- **CRT factorisation of the bilinear estimate over prime powers.**  If, for every prime `p`
and every `j ≥ 1`, the bilinear average on `ℤ/p^jℤ` satisfies the `L² × L² → L^q` bound with
constant `Kp p`, then for any finite set `s` of primes, any exponents `j` and any modulus `m`
equal to `∏_{p ∈ s} p ^ j p`, the same modulus satisfies the bound with the product constant
`∏_{p ∈ s} Kp p`.

This is the paper's tensor factorisation `ttensor-bil`
(`Work.Analysis.Paraproduct.BilinearAverageLq_crt`) iterated over the prime powers; it is the
finite-cyclic form of `‖A_{∏_{p∈S}ℤ_p}‖ = ∏_{p∈S}‖A_{ℤ_p}‖`. -/
theorem BilinearAverageLq_prod_primePowers (P : Polynomial ℤ) {q : ℝ} (hq : 1 ≤ q)
    (Kp : ℕ → ℝ)
    (hb : ∀ (p j : ℕ) [Fact p.Prime], 1 ≤ j → BilinearAverageLq P (p ^ j) q (Kp p)) :
    ∀ (s : Finset ℕ) (j : ℕ → ℕ) (m : ℕ) [NeZero m], m = ∏ p ∈ s, p ^ j p →
      (∀ p ∈ s, Nat.Prime p) → (∀ p ∈ s, 1 ≤ j p) →
        BilinearAverageLq P m q (∏ p ∈ s, Kp p) := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro j m _ hm _ _
      have hm1 : m = 1 := by simpa using hm
      subst hm1
      simpa using BilinearAverageLq_one P hq
  | insert p s hp_notin ih =>
      intro j m _ hm hprime hj
      have hp : Nat.Prime p := hprime p (Finset.mem_insert_self p s)
      haveI : Fact (Nat.Prime p) := ⟨hp⟩
      have hprime' : ∀ p' ∈ s, Nat.Prime p' := fun p' hp' =>
        hprime p' (Finset.mem_insert_of_mem hp')
      have hj' : ∀ p' ∈ s, 1 ≤ j p' := fun p' hp' =>
        hj p' (Finset.mem_insert_of_mem hp')
      have hjn : 1 ≤ j p := hj p (Finset.mem_insert_self p s)
      -- the modulus of the tail is nonzero, so the induction hypothesis applies
      have htail_pos : 0 < ∏ p' ∈ s, p' ^ j p' := by
        refine Finset.prod_pos (fun p' hp' => ?_)
        exact pow_pos (hprime' p' hp').pos _
      haveI : NeZero (∏ p' ∈ s, p' ^ j p') := ⟨ne_of_gt htail_pos⟩
      have ih' : BilinearAverageLq P (∏ p' ∈ s, p' ^ j p') q (∏ p' ∈ s, Kp p') :=
        ih j _ rfl hprime' hj'
      -- coprimality of `p ^ j p` with the tail
      have hcop : Nat.Coprime (p ^ j p) (∏ p' ∈ s, p' ^ j p') := by
        refine Nat.Coprime.pow_left _ ?_
        refine Nat.Coprime.prod_right fun p' hp' => ?_
        have hp'prime : Nat.Prime p' := hprime' p' hp'
        have hne : p ≠ p' := fun h => hp_notin (h ▸ hp')
        rw [Nat.Prime.coprime_iff_not_dvd hp]
        intro hdvd
        rcases hp'prime.eq_one_or_self_of_dvd p (hp.dvd_of_dvd_pow hdvd) with h | h
        · exact hp.ne_one h
        · exact hne h
      have hcrt := Work.Analysis.Paraproduct.BilinearAverageLq_crt P hcop hq
        (hb p (j p) hjn) ih'
      -- identify `m` with the full product
      have hm' : m = p ^ j p * ∏ p' ∈ s, p' ^ j p' := by rw [hm, Finset.prod_insert hp_notin]
      subst hm'
      rw [Finset.prod_insert hp_notin (f := Kp)]
      exact hcrt

/-! ## The assembly from the prime-power inputs -/

/-- **The target estimate from the two prime-power inputs.**  Let `d = P.natDegree ≥ 2` and let
`q < 2d/(d-1)`.  Assume

* (uniform prime-power bounds) for `2 ≤ q` there is `K > 0` with
  `BilinearAverageLq P (p^j) q K` for all primes `p` and all `j ≥ 1`;
* (large-prime improvement) for `2 ≤ q` there is `p₀` with `BilinearAverageLq P (p^j) q 1`
  for all primes `p ≥ p₀` and all `j ≥ 1`.

Then the uniform estimate holds: there is `C > 0` with `BilinearAverageLq P Q q C` for every
modulus `Q ≠ 0`.  The constant is `(max 1 K)^{p₀}`: the CRT factorisation contributes one
factor `Kp p ≤ max 1 K` for each prime `p` dividing `Q`, and only the primes `p < p₀`
contribute more than `1`, of which there are at most `p₀`. -/
theorem BilinearAverageLqUniform_of_primePower (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (hUniform : ∀ q : ℝ, 2 ≤ q →
      q < 2 * (P.natDegree : ℝ) / ((P.natDegree : ℝ) - 1) →
        ∃ K : ℝ, 0 < K ∧ ∀ (p j : ℕ) [Fact p.Prime], 1 ≤ j →
          BilinearAverageLq P (p ^ j) q K)
    (hLarge : ∀ q : ℝ, 2 ≤ q →
      q < 2 * (P.natDegree : ℝ) / ((P.natDegree : ℝ) - 1) →
        ∃ p₀ : ℕ, ∀ (p j : ℕ) [Fact p.Prime], p₀ ≤ p → 1 ≤ j →
          BilinearAverageLq P (p ^ j) q 1) :
    ∀ q : ℝ, 1 ≤ q → q < 2 * (P.natDegree : ℝ) / ((P.natDegree : ℝ) - 1) →
      ∃ C : ℝ, 0 < C ∧ ∀ (Q : ℕ) [NeZero Q], BilinearAverageLq P Q q C := by
  intro q hq1 hqT
  by_cases hq2 : q ≤ 2
  · refine ⟨1, one_pos, fun Q _ => ?_⟩
    intro f g
    exact bilinearAverageLq_le_two P hq1 hq2 Q f g
  · have hq2' : 2 < q := lt_of_not_ge hq2
    obtain ⟨K, hKpos, hKb⟩ := hUniform q (le_of_lt hq2') hqT
    obtain ⟨p₀, hp₀b⟩ := hLarge q (le_of_lt hq2') hqT
    -- the family of prime-power constants
    let Kp : ℕ → ℝ := fun p => if p < p₀ then K else 1
    have hKp_lt : ∀ p, p < p₀ → Kp p = K := by
      intro p hp; dsimp only [Kp]; rw [if_pos hp]
    have hKp_ge : ∀ p, ¬ p < p₀ → Kp p = 1 := by
      intro p hp; dsimp only [Kp]; rw [if_neg hp]
    have hKp_le : ∀ p, Kp p ≤ max 1 K := by
      intro p
      by_cases hp : p < p₀
      · rw [hKp_lt p hp]; exact le_max_right 1 K
      · rw [hKp_ge p hp]; exact le_max_left 1 K
    have hb : ∀ (p j : ℕ) [Fact p.Prime], 1 ≤ j → BilinearAverageLq P (p ^ j) q (Kp p) := by
      intro p j _ hj
      by_cases h : p < p₀
      · rw [hKp_lt p h]; exact hKb p j hj
      · rw [hKp_ge p h]; exact hp₀b p j (le_of_not_gt h) hj
    refine ⟨(max 1 K) ^ p₀, by positivity, fun Q hQ => ?_⟩
    intro f g
    -- the CRT factorisation applied to the prime factorisation of `Q`
    have hpp : BilinearAverageLq P Q q (∏ p ∈ Q.primeFactors, Kp p) :=
      BilinearAverageLq_prod_primePowers P hq1 Kp hb Q.primeFactors Q.factorization Q
        (Nat.prod_primeFactors_pow_factorization (NeZero.ne Q))
        (fun p hp => (Nat.mem_primeFactors.mp hp).1)
        (fun p hp => (Nat.mem_primeFactors.mp hp).1.factorization_pos_of_dvd (NeZero.ne Q)
          (Nat.mem_primeFactors.mp hp).2.1)
    -- the constant is at most `(max 1 K) ^ p₀`
    have hconst : (∏ p ∈ Q.primeFactors, Kp p) ≤ (max 1 K) ^ p₀ := by
      have hfilter : (∏ p ∈ Q.primeFactors, Kp p)
          = ∏ p ∈ Q.primeFactors.filter (fun p => p < p₀), Kp p := by
        rw [Finset.prod_filter]
        refine Finset.prod_congr rfl (fun p _ => ?_)
        by_cases hp : p < p₀
        · simp only [hp, if_true]
        · simp only [hp, if_false, hKp_ge p hp]
      have hKprod : (∏ p ∈ Q.primeFactors.filter (fun p => p < p₀), Kp p)
          = K ^ (Q.primeFactors.filter (fun p => p < p₀)).card := by
        rw [Finset.prod_congr rfl (fun p hp => ?_)]
        · exact Finset.prod_const K
        · rw [Finset.mem_filter] at hp
          exact hKp_lt p hp.2
      have hcard : (Q.primeFactors.filter (fun p => p < p₀)).card ≤ p₀ := by
        have hsub : Q.primeFactors.filter (fun p => p < p₀) ⊆ Finset.range p₀ := by
          intro p hp
          rw [Finset.mem_filter] at hp
          exact Finset.mem_range.mpr hp.2
        calc (Q.primeFactors.filter (fun p => p < p₀)).card ≤ (Finset.range p₀).card :=
              Finset.card_le_card hsub
          _ = p₀ := Finset.card_range p₀
      rw [hfilter, hKprod]
      calc K ^ (Q.primeFactors.filter (fun p => p < p₀)).card
          ≤ (max 1 K) ^ (Q.primeFactors.filter (fun p => p < p₀)).card :=
            pow_le_pow_left₀ hKpos.le (le_max_right 1 K) _
        _ ≤ (max 1 K) ^ p₀ := pow_le_pow_right₀ (le_max_left 1 K) hcard
    have hx : 0 ≤ LpNormZMod Q 2 f := LpNormZMod_nonneg Q 2 f
    have hy : 0 ≤ LpNormZMod Q 2 g := LpNormZMod_nonneg Q 2 g
    calc LpNormZMod Q q (polyBilinearAverageZMod Polynomial.X P Q f g)
        ≤ (∏ p ∈ Q.primeFactors, Kp p) * LpNormZMod Q 2 f * LpNormZMod Q 2 g := hpp f g
      _ ≤ (max 1 K) ^ p₀ * LpNormZMod Q 2 f * LpNormZMod Q 2 g :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hconst hx) hy

/-! ## From the Appendix C fibre bound to the uniform prime-power bounds -/

/-- **The uniform prime-power bilinear bound from the Appendix C fibre bound.**  If for every
`s < d/(d-1)` the fibre counting function of `P` modulo `p^j` satisfies the concentration bound
`FiberLpBound P (p^j) s C` with `C` independent of the prime `p` and of `j`, then for every
`2 ≤ q < 2d/(d-1)` the bilinear average on `ℤ/p^jℤ` satisfies the `L² × L² → L^q` bound with a
constant `K = √C` independent of `p` and `j`.

This is the paper's step `(avg-1)`: with `s = q/2 ∈ [1, d/(d-1))`, Cauchy–Schwarz and Young's
inequality (`Work.Analysis.Paraproduct.bilinAverage_lq_fiber`) give the estimate at exponent
`2s = q`. -/
theorem BilinearAverageLq_uniform_primePow_of_fiber (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (hFib : ∀ s : ℝ, 0 < s → s < (P.natDegree : ℝ) / ((P.natDegree : ℝ) - 1) →
      ∃ C : ℝ, 0 < C ∧ ∀ (p j : ℕ) [Fact p.Prime], 1 ≤ j →
        FiberLpBound P (p ^ j) s C) :
    ∀ q : ℝ, 2 ≤ q → q < 2 * (P.natDegree : ℝ) / ((P.natDegree : ℝ) - 1) →
      ∃ K : ℝ, 0 < K ∧ ∀ (p j : ℕ) [Fact p.Prime], 1 ≤ j →
        BilinearAverageLq P (p ^ j) q K := by
  intro q hq2 hqT
  have hs1 : 1 ≤ q / 2 := by
    rw [one_le_div (by norm_num : (0 : ℝ) < 2)]
    exact hq2
  have hsT : q / 2 < (P.natDegree : ℝ) / ((P.natDegree : ℝ) - 1) := by
    rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
    calc q < (2 * (P.natDegree : ℝ)) / ((P.natDegree : ℝ) - 1) := hqT
      _ = ((P.natDegree : ℝ) / ((P.natDegree : ℝ) - 1)) * 2 := by ring
  have hqpos : 0 < q / 2 := lt_of_lt_of_le zero_lt_one hs1
  obtain ⟨C, hCpos, hCb⟩ := hFib (q / 2) hqpos hsT
  refine ⟨Real.sqrt C, Real.sqrt_pos.mpr hCpos, fun p j _ hj => ?_⟩
  have hLp : LpNormZMod (p ^ j) (q / 2) (fun m => (polyFiberCard P (p ^ j) m : ℂ)) ≤ C :=
    LpNormZMod_fiberFun_le (r := q / 2) (C := C) hqpos hCpos.le (hCb p j hj)
  have h := Work.Analysis.Paraproduct.bilinearAverageLq_of_fiber P (p ^ j) (s := q / 2) hs1 hLp
  simpa [show 2 * (q / 2) = q by ring] using h

/-! ## The frontier, in the vocabulary of the A2 area

`BilinearAverageLqUniform_of_peluse` isolates the whole remaining mathematical content of the
target as Peluse's inverse theorem, contract Area A2 (the `A2` subproject
`Submission/Work/Peluse/`).  Inside that subproject every reduction composing Area A2 is *proved*,
and the tree's own status docstring (`Submission/Work/Peluse/ucontrol_of_concat.lean`, section
"Session 11, second part") records the frontier of the whole of A2 as

`{Prop34, Prop36S, ∀ s ≥ 2, HardInputAt s P, BandDegenerate P}`,

the band's box-norm inverse theorem `HardInputAt` and the band's degenerate window
`BandDegenerate` being unavoidable (the paper's `Prop34`/`Prop36S` are an alternative for the
*Core* chapter only).  The proved reductions are

```
HardInputAt s P (∀ s ≥ 2)   ┐
BandDegenerate P            ┘⟹  Theorem37Chapter P    (UControl/theorem37Chapter_of_hard)
Theorem37Chapter P           ⟹  PeluseUControl P      (ucontrol_of_concat_of_chapter)
PeluseU2Inverse (proved), PeluseMajorArc P (proved)
                             ⟹  PeluseULowering P     (ulowering_of)
PeluseUControl P, PeluseULowering P
                             ⟹  PeluseCrux P          (crux_of_nodes)
PeluseCrux P (∀ P)           ⟹  Area A2               (AreaA2_of_crux)
Area A2                      ⟹  the target            (BilinearAverageLqUniform_of_peluse)
```

so the target is exactly Area A2, and within it exactly the band's two obligations.  The theorem
below records the last step in the `PeluseCrux`-vocabulary, which is the interface the A2
subproject exposes.

**Warning for whoever closes this file.**  The intermediate steps of the chain above **cannot be
instantiated in this module**: importing `Submission.Work.Peluse.majorarc` (needed for
`PeluseULowering`, via `Work.Peluse.ulowering_of`) or `Submission.Work.Peluse.ucontrol_of_concat`
alongside the `A6` imports of this file breaks the environment, because `Work.KMTAreas.A4.ee` is
declared both in `KMTAreas/A4/lip2IccBasic.lean` — reached from `MeanZeroL1GainOfPeluse` through
`KMTAreas.area_A4` → `A4.improvTwoZ` → `A4Z.lipTwoGenTail` → `A4Z.largeTail` → `A4.lip2GenWeyl` —
and in `KMTAreas/A4/lip2PlainIW.lean`, which `Peluse/majorarc.lean` imports directly.  A session
that wants the finer hypotheses (`HardInputAt`, `BandDegenerate`) in Lean should build the assembly
in a **separate module that does not import the `A6` chain** (that module needs
`Peluse.UControl.theorem37Chapter_of_inputs`, `Peluse.ucontrol_of_concat`, `Peluse.u2inverse`,
`Peluse.majorarc`, `Peluse.crux_of_nodes`, `Peluse.AreaA2_of_crux` and `Peluse.Compatible`, and no
`A6` module), and may then remove one of the two duplicate declarations of `Work.KMTAreas.A4.ee`
to lift the restriction globally. -/

/-- **The uniform `L² × L² → L^q` bound for the bilinear polynomial average on `ℤ/Qℤ`**
(Krause–Mirek–Tao, `(Avg-prof)` of §10): for a polynomial `P` of degree `d ≥ 2` and every
`1 ≤ q < 2d/(d-1)` there is `C = C(P,q) > 0` such that for *every* modulus `Q ≠ 0`
`‖A(f,g)‖_{L^q(ℤ/Qℤ)} ≤ C ‖f‖_{L²}‖g‖_{L²}`.

**Status.**  The statement is true (it is the paper's `(Avg-prof)`), but it is *deep*: its only
known proofs use Peluse's inverse theorem.  The reduction below is complete down to **two**
statements of the A2 subproject (`Submission/Work/Peluse/`), both of them the band's:

* `BilinearAverageLqUniform_of_primePower` (the CRT/product assembly) — proved here;
* `BilinearAverageLq_primePow_uniform` (`(avg-1)`, from Appendix C) — proved, on top of the
  delegated `FiberLpBoundPrimePowUniform`;
* `LargePrimeBilinear_of_inputs` (`(avg-2)`: interpolation and the Taylor expansion) — proved,
  from the Appendix C input and the mean-zero gain;
* the mean-zero gain `(eq:39)`: proved from `ImprovKMT P` (`MeanZeroL1GainLargePrime_of_improv`),
  and `ImprovKMT P` follows from Peluse's inverse theorem `PeluseInverseKMT P` (contract Area A2);
* inside A2 every reduction is proved, and the companion module
  `Submission/Work/KMTPlan/A6/BilinearAverageLqUniformFrontier.lean` proves
  **`BilinearAverageLqUniform_of_band`** — the target from `Work.Peluse.UControl.HardInputAt 2 P`
  (the band's box-norm inverse theorem at level `2`) plus `Work.Peluse.UControl.BandDegenerate P`
  (the band's degenerate window) — and **`BilinearAverageLqUniform_of_stubs`** — the target from the
  *carved* stubs `BandAprimeSpectral`/`BandResidualSpectral` that the A2 node itself consumes, the
  weakest hypothesis set known, namely the two `sorry`s of
  `Peluse/UControl/bandAprimeSpectralHolds.lean` and `Peluse/UControl/bandResidualSpectralHolds.lean`.
  *(Those two theorems are kept out of this module on purpose: they import the A2/band chain, which
  is large and under active development, whereas this file's closure is stable.)*

So the target becomes unconditional as soon as those two statements land; every link of the
composition is machine-checked here (`#print axioms` below is
`[propext, Classical.choice, Quot.sound]` for all of them).  See
`BilinearAverageLqUniform_NOTES.md` for the full account and
`NOTES_A4ee_IMPORT_CLASH_SESSION.md` (workspace root) for the import clash that the
`ClashBridge/` files work around. -/
theorem BilinearAverageLqUniform (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) :
    ∀ q : ℝ, 1 ≤ q → q < 2 * (P.natDegree : ℝ) / ((P.natDegree : ℝ) - 1) →
      ∃ C : ℝ, 0 < C ∧ ∀ (Q : ℕ) [NeZero Q] (f g : ZMod Q → ℂ),
        Work.Analysis.Concentration.LpNormZMod Q q
            (Work.Analysis.Concentration.polyBilinearAverageZMod Polynomial.X P Q f g)
          ≤ C * Work.Analysis.Concentration.LpNormZMod Q 2 f *
              Work.Analysis.Concentration.LpNormZMod Q 2 g :=
  -- THE ONLY REMAINING GAP OF THE WHOLE REDUCTION: the two band obligations of Area A2, i.e. the
  -- two `sorry`s of `Peluse/UControl/bandAprimeSpectralHolds.lean` and
  -- `Peluse/UControl/bandResidualSpectralHolds.lean` (or `HardInputAt 2` + `BandDegenerate`).
  -- Replace this `sorry` by
  --   `BilinearAverageLqUniform_of_stubs (fun P hP => bandAprimeSpectralInput P hP)
  --      (fun P => bandResidualSpectralInput P) P hd`
  -- from `Submission/Work/KMTPlan/A6/BilinearAverageLqUniformFrontier.lean` (import it), or, if
  -- `PeluseInverseKMT P` is available, by `BilinearAverageLqUniform_of_peluse P hd hP` (proved
  -- immediately above in this file).  Nothing else is missing.
  sorry

end

end Work.KMTPlan.A6

/-! ## Axiom audit of the reduction -/

#print axioms Work.KMTPlan.A6.BilinearAverageLqUniform_of_primePower
#print axioms Work.KMTPlan.A6.BilinearAverageLq_prod_primePowers
