/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4, `Work.CORE4`)

# AREA CORE4 — the final arithmetic of §4 (Bender 1981, p. 228)

This file proves `Work.GW2.Case2ArithProp`: the system

* `q` odd, `7 ≤ q`, `{k, k'} = {(q+1)/2, (q−1)/2}` with `k` even,
* `p` prime, `3 ≤ p₀` odd, `p₀ ≤ p₁ ≤ p + 1`, `p₀ ≤ p`, `2p ≤ k`, `1 ≤ u ≤ p`,
* `q k' (p₁−1) q k' ((p₁−1)(q k'−1) − (q−1)q/p) ≤ 6k²u³p₀³`

has no solution.  The inequality is (12) of Bender's paper (p. 227); the argument below is the
chain of inequalities of p. 228, with the numerical constants made explicit.

## Mathematical content

Write `A = qk'` and `K = k`.  Then

* `A ≥ 2K² − 3K + 1` and `(q−1)q ≤ 2A` (both from `{2k, 2k'} = {q±1}`);
* `(p₁−1)(A−1) − (q−1)q/p ≥ ½ (p₁−1)(A−1)`, because `p ≥ 3`, `p₁ ≥ 3` and `A ≥ 3`;
* hence `A²(p₁−1)²(A−1) ≤ 12K²p³p₁³`
  (the left side is a lower bound for the LHS of (12), the right side an upper bound for its RHS,
  using `u ≤ p` and `p₀ ≤ p₁`);
* now `p ≤ K/2` gives `p³ ≤ (K/2)³`, `p₁ ≥ 3` gives `(p₁−1)² ≥ (4/9)p₁²`, and
  `p₁ ≤ p+1 ≤ K/2+1` gives `2p₁ ≤ K+2`; so it suffices that

  `27/16 · K⁵(K+2) < (2K²−3K+1)²(2K²−3K)`  for `K ≥ 6`,

  which is the polynomial identity
  `16(2K²−3K+1)²(2K²−3K) − 27K⁵(K+2) = K(101K⁵ − 630K⁴ + 992K³ − 816K² + 320K − 48)`,
  whose last factor is positive for `K ≥ 6` (at `K = 6` it is `155664`, and it is increasing).

The constants are `6` for `2p ≤ k` (`p ≥ 3`), `848 = 101·6² − 630·6 + 992`,
`4272 = 848·6 − 816`.
-/
import Submission.Work.CORE4.Defs

namespace Work.GW2

/-! ## The numerical inequality of p. 228 -/

/-- `16(2K²−3K+1)²(2K²−3K) > 27K⁵(K+2)` for `K ≥ 6`. -/
lemma arith_poly (k : ℕ) (hk : 6 ≤ k) :
    (27 : ℚ) * (k : ℚ) ^ 5 * ((k : ℚ) + 2) <
      16 * (2 * (k : ℚ) ^ 2 - 3 * (k : ℚ) + 1) ^ 2 * (2 * (k : ℚ) ^ 2 - 3 * (k : ℚ)) := by
  have hK : (6 : ℚ) ≤ (k : ℚ) := by exact_mod_cast hk
  have hid : 16 * (2 * (k : ℚ) ^ 2 - 3 * (k : ℚ) + 1) ^ 2 * (2 * (k : ℚ) ^ 2 - 3 * (k : ℚ)) -
        27 * (k : ℚ) ^ 5 * ((k : ℚ) + 2) =
      (k : ℚ) * (101 * (k : ℚ) ^ 5 - 630 * (k : ℚ) ^ 4 + 992 * (k : ℚ) ^ 3 -
        816 * (k : ℚ) ^ 2 + 320 * (k : ℚ) - 48) := by
    ring
  have hG : (0 : ℚ) < 101 * (k : ℚ) ^ 5 - 630 * (k : ℚ) ^ 4 + 992 * (k : ℚ) ^ 3 -
      816 * (k : ℚ) ^ 2 + 320 * (k : ℚ) - 48 := by
    have hfac : (101 : ℚ) * (k : ℚ) ^ 2 - 630 * (k : ℚ) + 992 - 848 =
        ((k : ℚ) - 6) * (101 * (k : ℚ) - 24) := by ring
    have h1 : (848 : ℚ) ≤ 101 * (k : ℚ) ^ 2 - 630 * (k : ℚ) + 992 := by
      have h2 : (0 : ℚ) ≤ ((k : ℚ) - 6) * (101 * (k : ℚ) - 24) :=
        mul_nonneg (by linarith) (by linarith)
      linarith
    have h3 : (101 : ℚ) * (k : ℚ) ^ 5 - 630 * (k : ℚ) ^ 4 + 992 * (k : ℚ) ^ 3 =
        (k : ℚ) ^ 3 * (101 * (k : ℚ) ^ 2 - 630 * (k : ℚ) + 992) := by ring
    have h4 : (848 : ℚ) * (k : ℚ) ^ 3 ≤
        (101 * (k : ℚ) ^ 2 - 630 * (k : ℚ) + 992) * (k : ℚ) ^ 3 :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h4' : (848 : ℚ) * (k : ℚ) ^ 3 ≤
        101 * (k : ℚ) ^ 5 - 630 * (k : ℚ) ^ 4 + 992 * (k : ℚ) ^ 3 := by
      rw [h3]
      linarith [h4]
    have h6 : (816 : ℚ) ≤ 848 * (k : ℚ) := by linarith
    have h7 : (0 : ℚ) ≤ (k : ℚ) ^ 2 * (848 * (k : ℚ) - 816) :=
      mul_nonneg (by positivity) (by linarith)
    have h8 : (48 : ℚ) ≤ 320 * (k : ℚ) := by linarith
    nlinarith [h4', h6, h7, h8]
  have hpos : (0 : ℚ) < 16 * (2 * (k : ℚ) ^ 2 - 3 * (k : ℚ) + 1) ^ 2 * (2 * (k : ℚ) ^ 2 - 3 * (k : ℚ)) -
        27 * (k : ℚ) ^ 5 * ((k : ℚ) + 2) := by
    rw [hid]
    exact mul_pos (by linarith) hG
  linarith

/-- `12K²p³p₁³ < (2K²−3K+1)²(p₁−1)²(2K²−3K)` for `K ≥ 6`, `3 ≤ p₁`, `p₁ ≤ p+1`, `2p ≤ K`.
This is the p. 228 chain with the four elementary bounds
`p ≤ K/2`, `(p₁−1)² ≥ (4/9)p₁²`, `2p₁ ≤ K+2` and `arith_poly`. -/
lemma arith_key (k p p1 : ℕ) (hk : 6 ≤ k) (hp1 : 3 ≤ p1) (hp1le : p1 ≤ p + 1)
    (h2p : 2 * p ≤ k) :
    12 * (k : ℚ) ^ 2 * (p : ℚ) ^ 3 * (p1 : ℚ) ^ 3 <
      (2 * (k : ℚ) ^ 2 - 3 * (k : ℚ) + 1) ^ 2 * ((p1 : ℚ) - 1) ^ 2 *
        (2 * (k : ℚ) ^ 2 - 3 * (k : ℚ)) := by
  have hK6 : (6 : ℚ) ≤ (k : ℚ) := by exact_mod_cast hk
  have hP1 : (3 : ℚ) ≤ (p1 : ℚ) := by exact_mod_cast hp1
  have h2P : (2 : ℚ) * (p : ℚ) ≤ (k : ℚ) := by exact_mod_cast h2p
  have hP1le : (p1 : ℚ) ≤ (p : ℚ) + 1 := by exact_mod_cast hp1le
  have hsq : ((4 : ℚ) / 9) * (p1 : ℚ) ^ 2 ≤ ((p1 : ℚ) - 1) ^ 2 := by nlinarith
  have hpoly := arith_poly k hk
  have h_a : (p : ℚ) ^ 3 ≤ ((k : ℚ) / 2) ^ 3 := by
    refine pow_le_pow_left₀ (by positivity) ?_ 3
    linarith
  have hstep : 12 * (k : ℚ) ^ 2 * (p : ℚ) ^ 3 * (p1 : ℚ) ^ 3 ≤
      ((27 : ℚ) / 16) * (k : ℚ) ^ 5 * ((k : ℚ) + 2) * ((p1 : ℚ) - 1) ^ 2 := by
    have hb : 12 * (k : ℚ) ^ 2 * (p : ℚ) ^ 3 * (p1 : ℚ) ^ 3 ≤
        12 * (k : ℚ) ^ 2 * ((k : ℚ) / 2) ^ 3 * (p1 : ℚ) ^ 3 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h_a (by positivity)) (by positivity)
    have hc : 12 * (k : ℚ) ^ 2 * ((k : ℚ) / 2) ^ 3 * (p1 : ℚ) ^ 3 =
        (3 / 2) * (k : ℚ) ^ 5 * (p1 : ℚ) ^ 3 := by ring
    have hd : (p1 : ℚ) ^ 3 ≤ ((9 : ℚ) / 4) * (p1 : ℚ) * ((p1 : ℚ) - 1) ^ 2 := by
      nlinarith [hsq, hP1]
    have he : (3 / 2) * (k : ℚ) ^ 5 * (p1 : ℚ) ^ 3 ≤
        (3 / 2) * (k : ℚ) ^ 5 * (((9 : ℚ) / 4) * (p1 : ℚ) * ((p1 : ℚ) - 1) ^ 2) :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    have hg : (3 / 2) * (k : ℚ) ^ 5 * (((9 : ℚ) / 4) * (p1 : ℚ) * ((p1 : ℚ) - 1) ^ 2) ≤
        ((27 : ℚ) / 16) * (k : ℚ) ^ 5 * ((k : ℚ) + 2) * ((p1 : ℚ) - 1) ^ 2 := by
      have h2 : (3 / 2) * (((9 : ℚ) / 4) * (p1 : ℚ)) ≤ ((27 : ℚ) / 16) * ((k : ℚ) + 2) := by
        linarith
      calc (3 / 2) * (k : ℚ) ^ 5 * (((9 : ℚ) / 4) * (p1 : ℚ) * ((p1 : ℚ) - 1) ^ 2)
          = ((3 / 2) * (((9 : ℚ) / 4) * (p1 : ℚ))) *
              ((k : ℚ) ^ 5 * ((p1 : ℚ) - 1) ^ 2) := by ring
        _ ≤ (((27 : ℚ) / 16) * ((k : ℚ) + 2)) * ((k : ℚ) ^ 5 * ((p1 : ℚ) - 1) ^ 2) :=
            mul_le_mul_of_nonneg_right h2 (by positivity)
        _ = ((27 : ℚ) / 16) * (k : ℚ) ^ 5 * ((k : ℚ) + 2) * ((p1 : ℚ) - 1) ^ 2 := by ring
    calc 12 * (k : ℚ) ^ 2 * (p : ℚ) ^ 3 * (p1 : ℚ) ^ 3
        ≤ 12 * (k : ℚ) ^ 2 * ((k : ℚ) / 2) ^ 3 * (p1 : ℚ) ^ 3 := hb
      _ = (3 / 2) * (k : ℚ) ^ 5 * (p1 : ℚ) ^ 3 := hc
      _ ≤ (3 / 2) * (k : ℚ) ^ 5 * (((9 : ℚ) / 4) * (p1 : ℚ) * ((p1 : ℚ) - 1) ^ 2) := he
      _ ≤ ((27 : ℚ) / 16) * (k : ℚ) ^ 5 * ((k : ℚ) + 2) * ((p1 : ℚ) - 1) ^ 2 := hg
  nlinarith [hpoly, hstep, sq_nonneg ((p1 : ℚ) - 1)]

/-! ## The number-theoretic steps -/

/-- From `{2k, 2k'} = {q+1, q−1}`: `A = qk' ≥ 2k² − 3k + 1`. -/
lemma A_ge (q k k' : ℕ)
    (hcases : (2 * k = q + 1 ∧ 2 * k' = q - 1) ∨ (2 * k = q - 1 ∧ 2 * k' = q + 1)) :
    (2 * (k : ℚ) ^ 2 - 3 * (k : ℚ) + 1) ≤ ((q * k' : ℕ) : ℚ) := by
  rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hq : q = 2 * k - 1 := by omega
    have hk' : k' = k - 1 := by omega
    have hqQ : (q : ℚ) = 2 * (k : ℚ) - 1 := by
      have h : ((q : ℕ) : ℚ) + 1 = 2 * (k : ℚ) := by
        have : q + 1 = 2 * k := by omega
        exact_mod_cast this
      linarith
    have hk'Q : (k' : ℚ) = (k : ℚ) - 1 := by
      have h : ((k' : ℕ) : ℚ) + 1 = (k : ℚ) := by
        have : k' + 1 = k := by omega
        exact_mod_cast this
      linarith
    push_cast
    rw [hqQ, hk'Q]
    nlinarith [sq_nonneg (k : ℚ)]
  · have hq : q = 2 * k + 1 := by omega
    have hk' : k' = k + 1 := by omega
    have hqQ : (q : ℚ) = 2 * (k : ℚ) + 1 := by
      rw [hq]
      push_cast
      ring
    have hk'Q : (k' : ℚ) = (k : ℚ) + 1 := by
      rw [hk']
      push_cast
      ring
    push_cast
    rw [hqQ, hk'Q]
    nlinarith [show (0 : ℚ) ≤ (k : ℚ) by positivity]

/-- From `{2k, 2k'} = {q+1, q−1}`: `(q−1)q ≤ 2A`. -/
lemma qq_le_twoA (q k k' : ℕ)
    (hcases : (2 * k = q + 1 ∧ 2 * k' = q - 1) ∨ (2 * k = q - 1 ∧ 2 * k' = q + 1)) :
    ((q : ℚ) - 1) * q ≤ 2 * ((q * k' : ℕ) : ℚ) := by
  rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hq : q = 2 * k' + 1 := by omega
    have hqQ : (q : ℚ) = 2 * (k' : ℚ) + 1 := by
      rw [hq]
      push_cast
      ring
    push_cast
    rw [hqQ]
    nlinarith [sq_nonneg (k' : ℚ)]
  · have hk' : (2 : ℚ) * (k' : ℚ) = (q : ℚ) + 1 := by exact_mod_cast h2
    have hq0 : (0 : ℚ) ≤ (q : ℚ) := by positivity
    push_cast
    nlinarith

/-! ## `Case2ArithProp` -/

theorem case2Arith : Case2ArithProp := by
  intro q k k' p p0 p1 u hq hqodd hcases hkeven hp hp03 hp0odd hp01 hp1 hpp0 h2p hu1 hup hineq
  have hp3 : 3 ≤ p := le_trans hp03 hpp0
  have hp13 : 3 ≤ p1 := le_trans hp03 hp01
  have hk6 : 6 ≤ k := by omega
  have hq1 : 1 ≤ q := by omega
  have hp11 : 1 ≤ p1 := by omega
  have hK6 : (6 : ℚ) ≤ (k : ℚ) := by exact_mod_cast hk6
  have hP3 : (3 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp3
  have hP13 : (3 : ℚ) ≤ (p1 : ℚ) := by exact_mod_cast hp13
  have hPpos : (0 : ℚ) < (p : ℚ) := by linarith
  set A : ℚ := ((q * k' : ℕ) : ℚ) with hAdef
  have hAge : 2 * (k : ℚ) ^ 2 - 3 * (k : ℚ) + 1 ≤ A := by
    rw [hAdef]
    exact A_ge q k k' hcases
  have hAge1 : 2 * (k : ℚ) ^ 2 - 3 * (k : ℚ) ≤ A - 1 := by linarith
  have hA3 : (3 : ℚ) ≤ A := by nlinarith [hAge, hK6]
  have hqqA : ((q : ℚ) - 1) * q ≤ 2 * A := by
    rw [hAdef]
    exact qq_le_twoA q k k' hcases
  have hAqk : (↑q * ↑k' : ℚ) = A := by
    rw [hAdef]
    push_cast
    ring
  have hXeq : ((q : ℚ) * k' - 1) = A - 1 := by
    rw [hAdef]
    push_cast
    ring
  rw [hAqk] at hineq
  -- the box `(p₁−1)(A−1) − (q−1)q/p` is at least half of `(p₁−1)(A−1)`
  have hbox : (1 / 2) * ((p1 : ℚ) - 1) * (A - 1) ≤
      ((p1 : ℚ) - 1) * (A - 1) - ((q : ℚ) - 1) * q / p := by
    have hnum : (0 : ℚ) ≤ ((q : ℚ) - 1) * q := by
      have : (1 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq1
      nlinarith
    have hstep1 : ((q : ℚ) - 1) * q / p ≤ ((q : ℚ) - 1) * q / 3 :=
      div_le_div_of_nonneg_left hnum (by norm_num) hP3
    have hstep2 : ((q : ℚ) - 1) * q / 3 ≤ 2 * A / 3 := by
      have h2A : ((q : ℚ) - 1) * q ≤ 2 * A := hqqA
      linarith
    have hstep3 : 2 * A / 3 ≤ (1 / 2) * ((p1 : ℚ) - 1) * (A - 1) := by
      nlinarith [hP13, hA3]
    linarith
  -- lower bound for the left-hand side of (12)
  have hLlow : (1 / 2) * A ^ 2 * ((p1 : ℚ) - 1) ^ 2 * (A - 1) ≤
      A * ((p1 : ℚ) - 1) * A *
        (((p1 : ℚ) - 1) * (A - 1) - ((q : ℚ) - 1) * q / p) := by
    have hnn : (0 : ℚ) ≤ A * ((p1 : ℚ) - 1) * A := by
      have h1 : (0 : ℚ) ≤ A * ((p1 : ℚ) - 1) := by nlinarith [hA3, hP13]
      exact mul_nonneg h1 (by linarith)
    calc (1 / 2) * A ^ 2 * ((p1 : ℚ) - 1) ^ 2 * (A - 1)
        = (A * ((p1 : ℚ) - 1) * A) * ((1 / 2) * ((p1 : ℚ) - 1) * (A - 1)) := by ring
      _ ≤ (A * ((p1 : ℚ) - 1) * A) *
            (((p1 : ℚ) - 1) * (A - 1) - ((q : ℚ) - 1) * q / p) :=
          mul_le_mul_of_nonneg_left hbox hnn
  -- upper bound for the right-hand side of (12)
  have hRu : 6 * (k : ℚ) ^ 2 * (u : ℚ) ^ 3 * (p0 : ℚ) ^ 3 ≤
      6 * (k : ℚ) ^ 2 * (p : ℚ) ^ 3 * (p1 : ℚ) ^ 3 := by
    have hu : (u : ℚ) ^ 3 ≤ (p : ℚ) ^ 3 := by
      have h : (u : ℚ) ≤ (p : ℚ) := by exact_mod_cast hup
      exact pow_le_pow_left₀ (by positivity) h 3
    have hp0 : (p0 : ℚ) ^ 3 ≤ (p1 : ℚ) ^ 3 := by
      have h : (p0 : ℚ) ≤ (p1 : ℚ) := by exact_mod_cast hp01
      exact pow_le_pow_left₀ (by positivity) h 3
    have hmul : (u : ℚ) ^ 3 * (p0 : ℚ) ^ 3 ≤ (p : ℚ) ^ 3 * (p1 : ℚ) ^ 3 :=
      mul_le_mul hu hp0 (by positivity) (by positivity)
    calc 6 * (k : ℚ) ^ 2 * (u : ℚ) ^ 3 * (p0 : ℚ) ^ 3
        = (6 * (k : ℚ) ^ 2) * ((u : ℚ) ^ 3 * (p0 : ℚ) ^ 3) := by ring
      _ ≤ (6 * (k : ℚ) ^ 2) * ((p : ℚ) ^ 3 * (p1 : ℚ) ^ 3) :=
          mul_le_mul_of_nonneg_left hmul (by positivity)
      _ = 6 * (k : ℚ) ^ 2 * (p : ℚ) ^ 3 * (p1 : ℚ) ^ 3 := by ring
  have hmain : (1 / 2) * A ^ 2 * ((p1 : ℚ) - 1) ^ 2 * (A - 1) ≤
      6 * (k : ℚ) ^ 2 * (p : ℚ) ^ 3 * (p1 : ℚ) ^ 3 :=
    le_trans hLlow (le_trans hineq hRu)
  have hsub : (2 * (k : ℚ) ^ 2 - 3 * (k : ℚ) + 1) ^ 2 * ((p1 : ℚ) - 1) ^ 2 *
        (2 * (k : ℚ) ^ 2 - 3 * (k : ℚ)) ≤ A ^ 2 * ((p1 : ℚ) - 1) ^ 2 * (A - 1) := by
    have h1 : (2 * (k : ℚ) ^ 2 - 3 * (k : ℚ) + 1) ^ 2 ≤ A ^ 2 :=
      pow_le_pow_left₀ (by nlinarith [hK6]) hAge 2
    have hab : (2 * (k : ℚ) ^ 2 - 3 * (k : ℚ) + 1) ^ 2 * ((p1 : ℚ) - 1) ^ 2 ≤
        A ^ 2 * ((p1 : ℚ) - 1) ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
    have hb : (0 : ℚ) ≤ 2 * (k : ℚ) ^ 2 - 3 * (k : ℚ) := by nlinarith [hK6]
    exact mul_le_mul hab hAge1 hb (by positivity)
  have hkey := arith_key k p p1 hk6 hp13 hp1 h2p
  nlinarith [hkey, hsub, hmain]

end Work.GW2
