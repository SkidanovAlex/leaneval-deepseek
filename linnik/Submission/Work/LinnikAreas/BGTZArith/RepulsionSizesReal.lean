import Mathlib
import Submission.Work.LinnikAreas.BGTZ.RepulsionSizes

namespace Work.LinnikAreas.BGTZArith

open Work.LinnikAreas.BGTZ

set_option maxHeartbeats 4000000

/-- Auxiliary arithmetic for the sieve level: if `X ≤ q` with `q ≥ 202` and `A ≥ 1`, then
`2 e ⌈max 200 X⌉ ≤ 2 + A²q³`. -/
lemma repulsionSizesRHeightAux {q A X : ℝ} (hq : 202 ≤ q) (hA : 1 ≤ A) (hX : X ≤ q) :
    2 * Real.exp 1 * ((⌈max 200 X⌉₊ : ℕ) : ℝ) ≤ 2 + A ^ 2 * q ^ 3 := by
  have hq0 : (0:ℝ) < q := by linarith
  have he1lt3 : Real.exp 1 < 3 := Real.exp_one_lt_three
  have hceil : ((⌈max 200 X⌉₊ : ℕ) : ℝ) < max 200 X + 1 :=
    Nat.ceil_lt_add_one (le_trans (by norm_num : (0:ℝ) ≤ 200) (le_max_left 200 X))
  have hRlt : ((⌈max 200 X⌉₊ : ℕ) : ℝ) < q + 1 := by
    have hmax : max 200 X ≤ q := max_le (by linarith) hX
    linarith
  have hq2 : (202:ℝ)^2 ≤ q^2 := pow_le_pow_left₀ (by norm_num) hq 2
  have hq3 : (202:ℝ)^3 ≤ q^3 := pow_le_pow_left₀ (by norm_num) hq 3
  have h1 : 2 * Real.exp 1 * q ≤ q^3 / 2 := by
    have h4e : 4 * Real.exp 1 ≤ q^2 := by nlinarith only [hq2, he1lt3]
    have hmul : 4 * Real.exp 1 * q ≤ q^2 * q := mul_le_mul_of_nonneg_right h4e hq0.le
    have hq3eq : q^2 * q = q^3 := by ring
    linarith [hmul, hq3eq]
  have h2 : 2 * Real.exp 1 * 1 ≤ q^3 / 2 := by nlinarith only [hq3, he1lt3]
  have h3 : 2 * Real.exp 1 * (q + 1) ≤ q^3 := by nlinarith only [h1, h2]
  have hA2 : (1:ℝ) ≤ A^2 := by nlinarith only [hA]
  have h4 : q^3 ≤ A^2 * q^3 := by nlinarith only [hA2, pow_nonneg hq0.le 3]
  have h5 : 2 * Real.exp 1 * ((⌈max 200 X⌉₊ : ℕ) : ℝ) < 2 * Real.exp 1 * (q + 1) :=
    mul_lt_mul_of_pos_left hRlt (by positivity)
  linarith [h5, h3, h4]

/-- Auxiliary arithmetic for the detection length: the ceiling of `max (max 2 X) Y` is at most
`q^{11/5}(5+|γ|)^{11/10}` when `X ≤ q^{2199/1000}(5+|γ|)^{26/25}`, `Y ≤ q^{1/50}`,
`Y ≥ 0`, `1 ≤ q` and `3 ≤ q^{1/1000}`. -/
lemma repulsionSizesNHeightAux {q X Y γ : ℝ} (hq1 : 1 ≤ q) (hq3 : 3 ≤ q ^ (1 / 1000 : ℝ))
    (hY0 : 0 ≤ Y)
    (hX : X ≤ q ^ (2199 / 1000 : ℝ) * (5 + |γ|) ^ (26 / 25 : ℝ))
    (hY : Y ≤ q ^ (1 / 50 : ℝ)) :
    ((⌈max (max 2 X) Y⌉₊ : ℕ) : ℝ) ≤ q ^ (11 / 5 : ℝ) * (5 + |γ|) ^ (11 / 10 : ℝ) := by
  have hq0 : (0:ℝ) < q := by linarith
  have h5g1 : (1:ℝ) ≤ 5 + |γ| := by have := abs_nonneg γ; linarith
  have h5g0 : (0:ℝ) ≤ 5 + |γ| := by linarith
  set P : ℝ := q ^ (11 / 5 : ℝ) * (5 + |γ|) ^ (11 / 10 : ℝ) with hPdef
  have h3_50 : (3:ℝ) ≤ q ^ (1 / 50 : ℝ) := by
    have hp : q ^ (1/50:ℝ) = (q ^ (1/1000:ℝ)) ^ (20:ℝ) := by
      rw [show (1/50:ℝ) = (1/1000:ℝ) * 20 by norm_num, Real.rpow_mul hq0.le]
    rw [hp]
    calc (3:ℝ) ≤ (3:ℝ) ^ (20:ℝ) := by
          have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3)
            (by norm_num : (1:ℝ) ≤ 20)
          rwa [Real.rpow_one] at h
      _ ≤ (q ^ (1/1000:ℝ)) ^ (20:ℝ) := Real.rpow_le_rpow (by norm_num) hq3 (by norm_num)
  have h9q : (9:ℝ) ≤ q ^ (11/5:ℝ) := by
    have hp : q ^ (11/5:ℝ) = (q ^ (1/1000:ℝ)) ^ (2200:ℝ) := by
      rw [show (11/5:ℝ) = (1/1000:ℝ) * 2200 by norm_num, Real.rpow_mul hq0.le]
    rw [hp]
    calc (9:ℝ) ≤ (3:ℝ) ^ (2:ℝ) := by norm_num
      _ ≤ (3:ℝ) ^ (2200:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3)
            (by norm_num : (2:ℝ) ≤ 2200)
      _ ≤ (q ^ (1/1000:ℝ)) ^ (2200:ℝ) := Real.rpow_le_rpow (by norm_num) hq3 (by norm_num)
  have h26 : (5+|γ|)^(26/25:ℝ) ≤ (5+|γ|)^(11/10:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le h5g1 (by norm_num)
  have h3X : 3 * X ≤ P := by
    rw [hPdef]
    calc 3 * X ≤ 3 * (q ^ (2199/1000:ℝ) * (5 + |γ|) ^ (26/25:ℝ)) :=
          mul_le_mul_of_nonneg_left hX (by norm_num)
      _ = (3 * q ^ (2199/1000:ℝ)) * (5 + |γ|) ^ (26/25:ℝ) := by ring
      _ ≤ (q ^ (1/1000:ℝ) * q ^ (2199/1000:ℝ)) * (5 + |γ|) ^ (26/25:ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hq3 (Real.rpow_nonneg hq0.le _))
            (Real.rpow_nonneg h5g0 _)
      _ = q ^ (11/5:ℝ) * (5 + |γ|) ^ (26/25:ℝ) := by
          have hpow : q ^ (1/1000:ℝ) * q ^ (2199/1000:ℝ) = q ^ (11/5:ℝ) := by
            rw [← Real.rpow_add hq0]; norm_num
          rw [hpow]
      _ ≤ q ^ (11/5:ℝ) * (5 + |γ|) ^ (11/10:ℝ) :=
          mul_le_mul_of_nonneg_left h26 (Real.rpow_nonneg hq0.le _)
  have h3Y : 3 * Y ≤ P := by
    rw [hPdef]
    calc 3 * Y ≤ 3 * q ^ (1/50:ℝ) := mul_le_mul_of_nonneg_left hY (by norm_num)
      _ ≤ q ^ (1/50:ℝ) * q ^ (1/50:ℝ) :=
          mul_le_mul_of_nonneg_right h3_50 (Real.rpow_nonneg hq0.le _)
      _ = q ^ (1/25:ℝ) := by rw [← Real.rpow_add hq0]; norm_num
      _ ≤ q ^ (11/5:ℝ) := Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num)
      _ ≤ q ^ (11/5:ℝ) * (5 + |γ|) ^ (11/10:ℝ) := by
          have h1 : (1:ℝ) ≤ (5 + |γ|) ^ (11/10:ℝ) := Real.one_le_rpow h5g1 (by norm_num)
          nlinarith only [h1, Real.rpow_nonneg hq0.le (11/5:ℝ)]
  have h9 : (9:ℝ) ≤ P := by
    rw [hPdef]
    have h1 : (1:ℝ) ≤ (5 + |γ|) ^ (11/10:ℝ) := Real.one_le_rpow h5g1 (by norm_num)
    nlinarith only [h9q, h1, Real.rpow_nonneg hq0.le (11/5:ℝ)]
  have h2le : (2:ℝ) ≤ P - 1 := by linarith [h9]
  have hXle : X ≤ P - 1 := by
    by_cases h : 0 ≤ X
    · linarith [h3X, h9]
    · simp only [not_le] at h; linarith [h9, h]
  have hYle : Y ≤ P - 1 := by linarith [h3Y, hY0, h9]
  have htle : max (max 2 X) Y ≤ P - 1 := max_le (max_le h2le hXle) hYle
  have hceil : ((⌈max (max 2 X) Y⌉₊ : ℕ) : ℝ) < max (max 2 X) Y + 1 :=
    Nat.ceil_lt_add_one (le_trans (by norm_num : (0:ℝ) ≤ 2)
      (le_trans (le_max_left 2 X) (le_max_left _ _)))
  linarith [htle, hceil]

/-- **The size conditions of the BGTZ assembly, with the exponents taken as REAL powers.**

This is the same statement as `Work.LinnikAreas.BGTZ.RepulsionSizes`, except that the three
exponents `2·(1/4+1/100)`, `8·(1/4+1/100)`, `4·(1/4+1/100)` are written with an explicit real
coercion `((2:ℝ) * (1/4+1/100))`, so that `(q:ℝ) ^ ((2:ℝ) * (1/4+1/100))` is `q` to the power
`0.52` and *not* the natural-number power `q ^ 0 = 1`.  With the implicit exponent type Lean
resolves `2 * (1/4 + 1/100)` to `ℕ` (where it is `0`), which makes the earlier statement
vacuous for our purposes: the users (`Work.LinnikAreas.BGTZ.DetectorMainProp`, whose condition is
`C * A^2 * q^(2*θ) * ... ≤ R` for a *real* `θ`) need the genuine real powers.

The reusable elementary estimates proved in `Submission.Work.LinnikAreas.BGTZ.RepulsionSizes`
(`repulsionSizesSiegelInv`, `repulsionSizesLogLeThreeRpowThird`, `repulsionSizesThreeQuartersLe`,
`repulsionSizesLogPow4LeRpow`, `repulsionSizesHundredLeRpowQuarter`) are exactly the inputs for
this, and that module may be imported.

Mathematically: from the Landau--Siegel input `B/(q^{1/100}(log q)^2) < 1-β₁` (so
`(1-β₁)^{-1} ≤ q^{1/100}(log q)^2`, as `B ≥ 1`) and `log Cd, log A, log B ≤ log q/1000`, the
two choices
`R = ⌈Cd A² q^{2θ} e^{2(log q)^{3/4}} (1-β₁)^{-2}⌉ + 1` and
`N = ⌈Cd A^8 e^{8(log q)^{3/4}} (log(2+A²q³))^24 q^{8θ} T^{4θ} (1-β₁)^{-2}⌉ + 1`
(with `θ = 1/4 + 1/100`) satisfy everything, for `log q ≥ 10^8` (the threshold may be raised
internally; only the given hypothesis `100000000 ≤ log q` may be *used*, no stronger one may be
assumed): `log(2+A²q³) ≤ 5 log q` gives the second R-condition, `T ≤ 5+|γ|` gives the
`T^{4θ} ≤ (5+|γ|)^{1.1}` part of the final bound, and the coefficients add up as
`8θ + 2ε = 2.10 ≤ 11/5`, `4θ = 1.04 ≤ 11/10` with `ε = 1/100`, the leftover
`log(log q)-terms` and `8(log q)^{3/4}` being absorbed by the slack. -/
theorem RepulsionSizesReal {q : ℕ} [NeZero q] {A B Cd cZ T β₁ γ : ℝ}
    (hA1 : 1 ≤ A) (hB1 : 1 ≤ B) (hCd : 0 < Cd) (hcZ : 0 < cZ) (hT : 4 ≤ T)
    (hγT : |γ| ≤ T) (hTγ : T ≤ 5 + |γ|) (hβ₁lt : β₁ < 1)
    (hβ₁big : 1 - 1 / (10 * Real.log q) < β₁)
    (hSiegel : B / ((q : ℝ) ^ (1 / 100 : ℝ) * (Real.log q) ^ 2) < 1 - β₁)
    (hlogq : 100000000 ≤ Real.log q)
    (hlogA : Real.log A ≤ Real.log q / 1000) (hlogB : Real.log B ≤ Real.log q / 1000)
    (hlogCd : Real.log Cd ≤ Real.log q / 1000) :
    ∃ R N : ℕ, 200 ≤ R ∧ 2 ≤ N ∧ 1 ≤ (N : ℝ) * (1 - β₁) ∧
      Cd * A ^ 2 * (q : ℝ) ^ ((2 : ℝ) * (1 / 4 + 1 / 100))
          * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) * (1 - β₁) ^ (-2 : ℝ) ≤ (R : ℝ) ∧
      Real.log (2 * Real.exp 1 * (R : ℝ)) ≤ Real.log (2 + A ^ 2 * (q : ℝ) ^ 3) ∧
      Cd * A ^ 8 * Real.exp (8 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ))
          * (Real.log (2 + A ^ 2 * (q : ℝ) ^ 3)) ^ 24 * (q : ℝ) ^ ((8 : ℝ) * (1 / 4 + 1 / 100))
          * T ^ ((4 : ℝ) * (1 / 4 + 1 / 100)) * (1 - β₁) ^ (-2 : ℝ) ≤ (N : ℝ) ∧
      Real.log (N : ℝ) ≤ Real.log (q : ℝ)
          * (11 / 5 + (11 / 10) * (Real.log (5 + |γ|) / Real.log (q : ℝ))) := by
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hxpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq1
  have hx1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq1
  have hLpos : 0 < Real.log (q:ℝ) := by linarith
  have hXe : Real.exp 100000000 ≤ (q:ℝ) := (Real.le_log_iff_exp_le hxpos).mp hlogq
  have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA1
  have hA2ge1 : (1:ℝ) ≤ A^2 := by nlinarith only [hA1]
  have hqcont : (1:ℝ) < (q:ℝ) := by
    have h1 : (1:ℝ) < Real.exp 100000000 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by norm_num)
    linarith [h1, hXe]
  have hsiege : 0 < 1 - β₁ ∧ (1-β₁)⁻¹ ≤ (q:ℝ)^(1/100:ℝ) * (Real.log (q:ℝ))^2 :=
    repulsionSizesSiegelInv hB1 hqcont hSiegel
  have hδpos : 0 < 1 - β₁ := hsiege.1
  have hδinv : (1-β₁)⁻¹ ≤ (q:ℝ)^(1/100:ℝ) * (Real.log (q:ℝ))^2 := hsiege.2
  have hδ2 : (1-β₁)^(-2:ℝ) ≤ (q:ℝ)^(1/50:ℝ) * (Real.log (q:ℝ))^4 := by
    have hsq : (1-β₁)^(-2:ℝ) = ((1-β₁)⁻¹)^2 := by
      have h1 : (-2:ℝ) = (-1) + (-1) := by norm_num
      rw [h1, Real.rpow_add hδpos, Real.rpow_neg_one]
      ring
    rw [hsq]
    have h1 : ((1-β₁)⁻¹)^2 ≤ ((q:ℝ)^(1/100:ℝ) * (Real.log (q:ℝ))^2)^2 :=
      (by simpa only [pow_two] using mul_self_le_mul_self (inv_pos.mpr hδpos).le hδinv)
    have h2 : ((q:ℝ)^(1/100:ℝ) * (Real.log (q:ℝ))^2)^2
        = (q:ℝ)^(1/50:ℝ) * (Real.log (q:ℝ))^4 := by
      have ha : ((q:ℝ)^(1/100:ℝ))^2 = (q:ℝ)^(1/50:ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]; norm_num
      have hb : ((Real.log (q:ℝ))^2)^2 = (Real.log (q:ℝ))^4 := by
        rw [← pow_mul]
      rw [mul_pow, ha, hb]
    linarith [h1, h2]
  have hCd_le : Cd ≤ (q:ℝ)^(1/1000:ℝ) := by
    rw [show Cd = Real.exp (Real.log Cd) from (Real.exp_log hCd).symm, Real.rpow_def_of_pos hxpos]
    apply Real.exp_le_exp.mpr
    have hdiv : Real.log (q:ℝ) / 1000 = Real.log (q:ℝ) * (1/1000) := by ring
    linarith [hlogCd, hdiv]
  have hA_le : A ≤ (q:ℝ)^(1/1000:ℝ) := by
    rw [show A = Real.exp (Real.log A) from (Real.exp_log hA0).symm, Real.rpow_def_of_pos hxpos]
    apply Real.exp_le_exp.mpr
    have hdiv : Real.log (q:ℝ) / 1000 = Real.log (q:ℝ) * (1/1000) := by ring
    linarith [hlogA, hdiv]
  have hA2_le : A^2 ≤ (q:ℝ)^(1/500:ℝ) := by
    have h1 : A^2 ≤ ((q:ℝ)^(1/1000:ℝ))^2 := pow_le_pow_left₀ hA0.le hA_le 2
    have h2 : ((q:ℝ)^(1/1000:ℝ))^2 = (q:ℝ)^(1/500:ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]; norm_num
    linarith [h1, h2]
  have hA8_le : A^8 ≤ (q:ℝ)^(1/125:ℝ) := by
    have h1 : A^8 ≤ ((q:ℝ)^(1/1000:ℝ))^8 := pow_le_pow_left₀ hA0.le hA_le 8
    have h2 : ((q:ℝ)^(1/1000:ℝ))^8 = (q:ℝ)^(1/125:ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]; norm_num
    linarith [h1, h2]
  have hq4 : (4:ℝ) ≤ (q:ℝ) := by
    have h1 : (4:ℝ) ≤ Real.exp 3 := by have := Real.add_one_le_exp (3:ℝ); linarith
    have h2 : Real.exp 3 ≤ Real.exp 100000000 := Real.exp_le_exp.mpr (by norm_num)
    linarith [h1, h2, hXe]
  have hlog2A : Real.log (2 + A^2 * (q:ℝ)^3) ≤ 4 * Real.log (q:ℝ) :=
    repulsionSizesLogTwoAddQ3Le hA1 hq4 hA_le
  have h100 : (100:ℝ) ≤ (Real.log (q:ℝ)) ^ (1/4:ℝ) := repulsionSizesHundredLeRpowQuarter hlogq
  have h34 : (Real.log (q:ℝ)) ^ (3/4:ℝ) ≤ Real.log (q:ℝ) / 100 :=
    repulsionSizesThreeQuartersLe hLpos h100
  have hexp2 : Real.exp (2 * (Real.log (q:ℝ))^(3/4:ℝ)) ≤ (q:ℝ)^(1/50:ℝ) := by
    have h1 : 2 * (Real.log (q:ℝ))^(3/4:ℝ) ≤ Real.log (q:ℝ) * (1/50) := by
      have h2 : Real.log (q:ℝ) / 100 = Real.log (q:ℝ) * (1/100) := by ring
      nlinarith only [h34, h2]
    calc Real.exp (2 * (Real.log (q:ℝ))^(3/4:ℝ))
        ≤ Real.exp (Real.log (q:ℝ) * (1/50)) := Real.exp_le_exp.mpr h1
      _ = (q:ℝ)^(1/50:ℝ) := by rw [Real.rpow_def_of_pos hxpos]
  have hexp8 : Real.exp (8 * (Real.log (q:ℝ))^(3/4:ℝ)) ≤ (q:ℝ)^(2/25:ℝ) := by
    have h1 : 8 * (Real.log (q:ℝ))^(3/4:ℝ) ≤ Real.log (q:ℝ) * (2/25) := by
      have h2 : 8 * (Real.log (q:ℝ) / 100) = Real.log (q:ℝ) * (2/25) := by ring
      nlinarith only [h34]
    calc Real.exp (8 * (Real.log (q:ℝ))^(3/4:ℝ))
        ≤ Real.exp (Real.log (q:ℝ) * (2/25)) := Real.exp_le_exp.mpr h1
      _ = (q:ℝ)^(2/25:ℝ) := by rw [Real.rpow_def_of_pos hxpos]
  have hL4 : (Real.log (q:ℝ))^4 ≤ (q:ℝ)^(1/100:ℝ) := repulsionSizesLogPow4LeRpow hXe
  have hmul28 : (Real.log (q:ℝ))^28 * (2:ℝ)^48 ≤ (q:ℝ)^(1/100:ℝ) :=
    repulsionSizesLogPow28Le hXe
  have hd24 : (Real.log (2 + A^2 * (q:ℝ)^3))^24 * (1-β₁)^(-2:ℝ) ≤ (q:ℝ)^(3/100:ℝ) :=
    repulsionSizesD24Bound hxpos hLpos hδpos hlog2A hmul28 hδ2
  -- bounds on q itself
  have hq202 : (202:ℝ) ≤ (q:ℝ) := by
    have h1 : (202:ℝ) ≤ Real.exp 201 := by have := Real.add_one_le_exp (201:ℝ); linarith
    have h2 : Real.exp 201 ≤ Real.exp 100000000 := Real.exp_le_exp.mpr (by norm_num)
    linarith [h1, h2, hXe]
  have hq3th : (3:ℝ) ≤ (q:ℝ)^(1/1000:ℝ) := by
    rw [Real.rpow_def_of_pos hxpos]
    have h1 : (3:ℝ) ≤ Real.exp 2 := by have := Real.add_one_le_exp (2:ℝ); linarith
    have h2 : Real.exp 2 ≤ Real.exp (Real.log (q:ℝ) * (1/1000)) := by
      apply Real.exp_le_exp.mpr; nlinarith only [hlogq]
    linarith [h1, h2]
  have hδ50 : (1-β₁)⁻¹ ≤ (q:ℝ)^(1/50:ℝ) := by
    have hLs : (Real.log (q:ℝ))^2 ≤ (Real.log (q:ℝ))^4 := by
      have hL1 : (1:ℝ) ≤ Real.log (q:ℝ) := by linarith
      have h2 : (Real.log (q:ℝ))^2 * 1 ≤ (Real.log (q:ℝ))^2 * (Real.log (q:ℝ))^2 := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hLpos.le 2)
        nlinarith only [hL1]
      have h3 : (Real.log (q:ℝ))^2 * (Real.log (q:ℝ))^2 = (Real.log (q:ℝ))^4 := by ring
      linarith [h2, h3]
    have h1 : (q:ℝ)^(1/100:ℝ) * (Real.log (q:ℝ))^2 ≤ (q:ℝ)^(1/100:ℝ) * (Real.log (q:ℝ))^4 :=
      mul_le_mul_of_nonneg_left hLs (Real.rpow_nonneg hxpos.le _)
    have h2 : (q:ℝ)^(1/100:ℝ) * (Real.log (q:ℝ))^4 ≤ (q:ℝ)^(1/100:ℝ) * (q:ℝ)^(1/100:ℝ) :=
      mul_le_mul_of_nonneg_left hL4 (Real.rpow_nonneg hxpos.le _)
    have h3 : (q:ℝ)^(1/100:ℝ) * (q:ℝ)^(1/100:ℝ) = (q:ℝ)^(1/50:ℝ) := by
      rw [← Real.rpow_add hxpos]; norm_num
    linarith [hδinv, h1, h2, h3]
  -- abbreviations for the two quantities
  set LR : ℝ := Cd * A ^ 2 * (q : ℝ) ^ ((2 : ℝ) * (1 / 4 + 1 / 100))
      * Real.exp (2 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) * (1 - β₁) ^ (-2 : ℝ) with hLRdef
  set LN : ℝ := Cd * A ^ 8 * Real.exp (8 * (Real.log (q : ℝ)) ^ (3 / 4 : ℝ))
      * (Real.log (2 + A ^ 2 * (q : ℝ) ^ 3)) ^ 24 * (q : ℝ) ^ ((8 : ℝ) * (1 / 4 + 1 / 100))
      * T ^ ((4 : ℝ) * (1 / 4 + 1 / 100)) * (1 - β₁) ^ (-2 : ℝ) with hLNdef
  have hLR : LR ≤ (q:ℝ)^(573/1000:ℝ) := by
    rw [hLRdef, show ((2:ℝ) * (1/4 + 1/100)) = (13/25:ℝ) by norm_num]
    have h0 : Cd * A^2 * Real.exp (2 * (Real.log (q:ℝ))^(3/4:ℝ)) * (1-β₁)^(-2:ℝ)
        ≤ (q:ℝ)^(53/1000:ℝ) :=
      repulsionSizesRBound hxpos hδpos hCd_le hA2_le hexp2 hδ2 hL4
    calc Cd * A^2 * (q:ℝ)^(13/25:ℝ) * Real.exp (2 * (Real.log (q:ℝ))^(3/4:ℝ))
          * (1-β₁)^(-2:ℝ)
        = (q:ℝ)^(13/25:ℝ)
            * (Cd * A^2 * Real.exp (2 * (Real.log (q:ℝ))^(3/4:ℝ)) * (1-β₁)^(-2:ℝ)) := by ring
      _ ≤ (q:ℝ)^(13/25:ℝ) * (q:ℝ)^(53/1000:ℝ) :=
          mul_le_mul_of_nonneg_left h0 (Real.rpow_nonneg hxpos.le _)
      _ = (q:ℝ)^(573/1000:ℝ) := by rw [← Real.rpow_add hxpos]; norm_num
  have hLN : LN ≤ (q:ℝ)^(2199/1000:ℝ) * (5+|γ|)^(26/25:ℝ) := by
    rw [hLNdef, show ((8:ℝ) * (1/4 + 1/100)) = (52/25:ℝ) by norm_num,
        show ((4:ℝ) * (1/4 + 1/100)) = (26/25:ℝ) by norm_num]
    have h0 : Cd * A^8 * Real.exp (8 * (Real.log (q:ℝ))^(3/4:ℝ))
        * (Real.log (2 + A^2 * (q:ℝ)^3))^24 * (1-β₁)^(-2:ℝ) ≤ (q:ℝ)^(119/1000:ℝ) :=
      repulsionSizesNBound hxpos hδpos hCd_le hA8_le hexp8 hd24
    have hTnn : (0:ℝ) ≤ T := by linarith
    have hT : T^(26/25:ℝ) ≤ (5+|γ|)^(26/25:ℝ) := Real.rpow_le_rpow hTnn hTγ (by norm_num)
    calc Cd * A^8 * Real.exp (8 * (Real.log (q:ℝ))^(3/4:ℝ))
          * (Real.log (2 + A^2 * (q:ℝ)^3))^24 * (q:ℝ)^(52/25:ℝ)
          * T^(26/25:ℝ) * (1-β₁)^(-2:ℝ)
        = (q:ℝ)^(52/25:ℝ) * T^(26/25:ℝ)
            * (Cd * A^8 * Real.exp (8 * (Real.log (q:ℝ))^(3/4:ℝ))
                * (Real.log (2 + A^2 * (q:ℝ)^3))^24 * (1-β₁)^(-2:ℝ)) := by ring
      _ ≤ (q:ℝ)^(52/25:ℝ) * T^(26/25:ℝ) * (q:ℝ)^(119/1000:ℝ) :=
          mul_le_mul_of_nonneg_left h0
            (mul_nonneg (Real.rpow_nonneg hxpos.le _) (Real.rpow_nonneg hTnn _))
      _ ≤ (q:ℝ)^(52/25:ℝ) * (5+|γ|)^(26/25:ℝ) * (q:ℝ)^(119/1000:ℝ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hT (Real.rpow_nonneg hxpos.le _))
            (Real.rpow_nonneg hxpos.le _)
      _ = (q:ℝ)^(2199/1000:ℝ) * (5+|γ|)^(26/25:ℝ) := by
          have hpow : (q:ℝ)^(52/25:ℝ) * (q:ℝ)^(119/1000:ℝ) = (q:ℝ)^(2199/1000:ℝ) := by
            rw [← Real.rpow_add hxpos]; norm_num
          calc (q:ℝ)^(52/25:ℝ) * (5+|γ|)^(26/25:ℝ) * (q:ℝ)^(119/1000:ℝ)
              = ((q:ℝ)^(52/25:ℝ) * (q:ℝ)^(119/1000:ℝ)) * (5+|γ|)^(26/25:ℝ) := by ring
            _ = (q:ℝ)^(2199/1000:ℝ) * (5+|γ|)^(26/25:ℝ) := by rw [hpow]
  have hLRq : LR ≤ (q:ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_le hx1 (show (573/1000:ℝ) ≤ 1 by norm_num)
    rw [Real.rpow_one] at h
    exact le_trans hLR h
  have hRht : 2 * Real.exp 1 * ((⌈max 200 LR⌉₊ : ℕ) : ℝ) ≤ 2 + A^2 * (q:ℝ)^3 :=
    repulsionSizesRHeightAux hq202 hA1 hLRq
  have hNht : ((⌈max (max 2 LN) ((1-β₁)⁻¹)⌉₊ : ℕ) : ℝ)
      ≤ (q:ℝ)^(11/5:ℝ) * (5+|γ|)^(11/10:ℝ) :=
    repulsionSizesNHeightAux hx1 hq3th (inv_nonneg.mpr hδpos.le) hLN hδ50
  refine ⟨⌈max 200 LR⌉₊, ⌈max (max 2 LN) ((1-β₁)⁻¹)⌉₊, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : (200:ℝ) ≤ max 200 LR := le_max_left _ _
    have h3 : (200:ℝ) ≤ ((⌈max 200 LR⌉₊ : ℕ) : ℝ) := le_trans h1 (Nat.le_ceil _)
    exact_mod_cast h3
  · have h1 : (2:ℝ) ≤ max (max 2 LN) ((1-β₁)⁻¹) :=
      le_trans (le_max_left 2 LN) (le_max_left _ _)
    have h3 : (2:ℝ) ≤ ((⌈max (max 2 LN) ((1-β₁)⁻¹)⌉₊ : ℕ) : ℝ) :=
      le_trans h1 (Nat.le_ceil _)
    exact_mod_cast h3
  · have hNge : (1-β₁)⁻¹ ≤ ((⌈max (max 2 LN) ((1-β₁)⁻¹)⌉₊ : ℕ) : ℝ) :=
      le_trans (le_max_right _ _) (Nat.le_ceil _)
    have hmul := mul_le_mul_of_nonneg_right hNge hδpos.le
    have hone : (1-β₁)⁻¹ * (1-β₁) = 1 := inv_mul_cancel₀ hδpos.ne'
    linarith [hmul, hone]
  · exact le_trans (le_max_right _ _) (Nat.le_ceil _)
  · have hRpos : (0:ℝ) < ((⌈max 200 LR⌉₊ : ℕ) : ℝ) := by
      have h1 : (200:ℝ) ≤ ((⌈max 200 LR⌉₊ : ℕ) : ℝ) :=
        le_trans (le_max_left _ _) (Nat.le_ceil _)
      linarith
    exact Real.log_le_log (mul_pos (by positivity) hRpos) hRht
  · exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (Nat.le_ceil _)
  · have hlogN : Real.log (((⌈max (max 2 LN) ((1-β₁)⁻¹)⌉₊ : ℕ) : ℝ))
        ≤ Real.log ((q:ℝ)^(11/5:ℝ) * (5+|γ|)^(11/10:ℝ)) :=
      Real.log_le_log (by positivity) hNht
    have hval : Real.log ((q:ℝ)^(11/5:ℝ) * (5+|γ|)^(11/10:ℝ))
        = Real.log (q:ℝ) * (11/5 + (11/10) * (Real.log (5+|γ|) / Real.log (q:ℝ))) := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hxpos,
        Real.log_rpow (by linarith : (0:ℝ) < 5 + |γ|)]
      field_simp
    linarith [hlogN, hval]

end Work.LinnikAreas.BGTZArith
