import Mathlib
import Submission.Work.FIArea4.A4varbounds

/-!
# FI §13: the numerical comparison `P·T12(D⁺) ≪ T13(D)·(RS)^{ε/2}` (small-`P` case)

This module proves the numerical input `P13_num_small` consumed by the §13 assembly
(`Submission/Work/FIArea4/P13Assembly.lean`).  With
`P = D^{-1/2}(R+S)^{-1/8}(RS)^{3/8}` and `D'` ranging over the enlargement window
`D P² / 2 ≤ D' ≤ 16 D P²`, it shows

`P · p14T12 D' R S (ε/8) ≤ K · p14T13 D R S ε · (RS)^{ε/2}`

for a constant `K` depending only on `ε > 0`.

Writing `a = D`, `b = R`, `c = S`, `X = bc`, `Y = b+c`, the bracket `p14T13` is
`A + B` with `A = a Y^{1/4} X^{1/4}` and `B = a^{-1/2} Y^{1/8} X^{9/8}`, and every term of
`P · p14T12` is bounded by a multiple of `B · X^{ε/2}`: the four terms of (12.4) give the
constants `16`, `16^{1/3}·C` (with `C` the logarithmic growth constant), `2` and `2`
(the last absorbing both `R S^{3/4}` and `S R^{3/4}`).  The only analytic input is the
elementary bound `(log(2x)+1)^4 ≤ C_ε x^{ε/2}` for `x ≥ 1`.
-/

namespace Work.FIArea4

noncomputable section

/-- `(log(2x)+1)^4 ≤ C x^{ε/2}` for `x ≥ 1`, with `C` depending only on `ε > 0`. -/
lemma P13_log_pow_le (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x →
      (Real.log (2 * x) + 1) ^ (4:ℕ) ≤ C * x ^ (ε / 2) := by
  have hlog2pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(8 / ε + Real.log 2 + 1) ^ (4:ℕ), by positivity, ?_⟩
  intro x hx1
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hd : (0:ℝ) < ε/8 := by linarith
  have hlog2x : Real.log (2 * x) = Real.log 2 + Real.log x := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hx0)]
  have hlogx : Real.log x ≤ x ^ (ε / 8) / (ε / 8) := Real.log_le_rpow_div hx0.le hd
  set t := x ^ (ε / 8) with ht
  have ht1 : 1 ≤ t := by
    rw [ht]
    calc (1:ℝ) = 1 ^ (ε / 8) := (Real.one_rpow _).symm
      _ ≤ x ^ (ε/8) := Real.rpow_le_rpow zero_le_one hx1 hd.le
  have hle : Real.log (2*x) + 1 ≤ (8/ε + Real.log 2 + 1) * t := by
    rw [hlog2x]
    have h1 : x ^ (ε/8) / (ε/8) = t * (8/ε) := by rw [ht]; field_simp
    have h2 : Real.log x ≤ t * (8/ε) := by rw [← h1]; exact hlogx
    have h3 : Real.log 2 + 1 ≤ (Real.log 2 + 1) * t := by nlinarith [hlog2pos, ht1]
    nlinarith [h2, h3]
  have hpos1 : (0:ℝ) ≤ Real.log (2*x) + 1 := by
    have : 0 ≤ Real.log (2*x) := Real.log_nonneg (by linarith)
    linarith
  have hpow : (Real.log (2*x)+1)^4 ≤ ((8/ε + Real.log 2 + 1) * t)^4 :=
    pow_le_pow_left₀ hpos1 hle 4
  have ht4 : t^4 = x ^ (ε/2) := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    congr 1
    ring
  calc (Real.log (2*x)+1)^4 ≤ ((8/ε + Real.log 2 + 1) * t)^4 := hpow
    _ = (8/ε + Real.log 2 + 1)^4 * x ^ (ε/2) := by rw [mul_pow, ht4]

/-- Normalisation of all powers of `p = a^{-1/2}(b+c)^{-1/8}(bc)^{3/8}`. -/
lemma P13_prpow (a b c p : ℝ) (ha : 0 < a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hp : p = a^(-(1:ℝ)/2) * (b + c)^(-(1:ℝ)/8) * (b * c)^((3:ℝ)/8)) (t : ℝ) :
    p^t = a^(-(t/2)) * (b + c)^(-(t/8)) * (b * c)^((3*t)/8) := by
  rw [hp]
  rw [Real.mul_rpow (by positivity) (by positivity)]
  rw [Real.mul_rpow (by positivity) (by positivity)]
  rw [← Real.rpow_mul ha.le, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ b + c),
      ← Real.rpow_mul (by positivity : (0:ℝ) ≤ b*c)]
  ring_nf

/-- The diagonal term `P·D'` of `P·p14T12(D')`. -/
lemma P13_term1 (a b c p d ε : ℝ) (ha : 0 < a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hε : 0 < ε)
    (hp : p = a^(-(1:ℝ)/2) * (b + c)^(-(1:ℝ)/8) * (b * c)^((3:ℝ)/8))
    (hhi : d ≤ 16 * a * p^2) :
    p * d ≤ 16 * (a^(-(1:ℝ)/2) * (b + c)^((1:ℝ)/8) * (b * c)^((9:ℝ)/8))
      * ((b * c)^(ε/2)) := by
  have hb0 : (0:ℝ) < b := lt_of_lt_of_le zero_lt_one hb
  have hc0 : (0:ℝ) < c := lt_of_lt_of_le zero_lt_one hc
  have hY1 : (1:ℝ) ≤ b + c := by linarith
  have hX1 : (1:ℝ) ≤ b * c := by nlinarith [hb, hc]
  have hX0 : (0:ℝ) < b * c := lt_of_lt_of_le zero_lt_one hX1
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  have hp3 : p^3 = a^(-(3:ℝ)/2) * (b+c)^(-(3:ℝ)/8) * (b*c)^((9:ℝ)/8) := by
    rw [show p^3 = p^((3:ℝ)) from (Real.rpow_natCast p 3).symm,
        P13_prpow a b c p ha hb hc hp (3:ℝ)]
    norm_num
  have hap3 : a * p^3 = a^(-(1:ℝ)/2) * (b+c)^(-(3:ℝ)/8) * (b*c)^((9:ℝ)/8) := by
    rw [hp3]
    have hA : a * a^(-(3:ℝ)/2) = a^(-(1:ℝ)/2) := by
      have h := Real.rpow_add ha (1:ℝ) (-(3:ℝ)/2)
      simp only [Real.rpow_one] at h
      rw [← h]; norm_num
    calc a * (a^(-(3:ℝ)/2) * (b+c)^(-(3:ℝ)/8) * (b*c)^((9:ℝ)/8))
        = (a * a^(-(3:ℝ)/2)) * ((b+c)^(-(3:ℝ)/8) * (b*c)^((9:ℝ)/8)) := by ring
      _ = a^(-(1:ℝ)/2) * ((b+c)^(-(3:ℝ)/8) * (b*c)^((9:ℝ)/8)) := by rw [hA]
      _ = a^(-(1:ℝ)/2) * (b+c)^(-(3:ℝ)/8) * (b*c)^((9:ℝ)/8) := by ring
  have hstep1 : p * (16 * a * p^2) = 16 * (a * p^3) := by ring
  have hkey : (b+c)^(-(3:ℝ)/8) ≤ (b+c)^((1:ℝ)/8) :=
    Real.rpow_le_rpow_of_exponent_le hY1 (by norm_num)
  have hB0 : 0 ≤ a^(-(1:ℝ)/2) * (b*c)^((9:ℝ)/8) := by positivity
  have hXh1 : (1:ℝ) ≤ (b*c)^(ε/2) := by
    calc (1:ℝ) = (b*c)^(0:ℝ) := (Real.rpow_zero _).symm
      _ ≤ (b*c)^(ε/2) := Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  calc p * d ≤ p * (16 * a * p^2) := mul_le_mul_of_nonneg_left hhi hp0
    _ = 16 * (a * p^3) := hstep1
    _ = 16 * (a^(-(1:ℝ)/2) * (b+c)^(-(3:ℝ)/8) * (b*c)^((9:ℝ)/8)) := by rw [hap3]
    _ ≤ 16 * (a^(-(1:ℝ)/2) * (b+c)^((1:ℝ)/8) * (b*c)^((9:ℝ)/8)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        calc a^(-(1:ℝ)/2) * (b+c)^(-(3:ℝ)/8) * (b*c)^((9:ℝ)/8)
            = (a^(-(1:ℝ)/2) * (b*c)^((9:ℝ)/8)) * (b+c)^(-(3:ℝ)/8) := by ring
          _ ≤ (a^(-(1:ℝ)/2) * (b*c)^((9:ℝ)/8)) * (b+c)^((1:ℝ)/8) :=
              mul_le_mul_of_nonneg_left hkey hB0
          _ = a^(-(1:ℝ)/2) * (b+c)^((1:ℝ)/8) * (b*c)^((9:ℝ)/8) := by ring
    _ ≤ 16 * (a^(-(1:ℝ)/2) * (b+c)^((1:ℝ)/8) * (b*c)^((9:ℝ)/8)) * ((b*c)^(ε/2)) := by
        have h16B : 0 ≤ 16 * (a^(-(1:ℝ)/2) * (b+c)^((1:ℝ)/8) * (b*c)^((9:ℝ)/8)) := by positivity
        calc 16 * (a^(-(1:ℝ)/2) * (b+c)^((1:ℝ)/8) * (b*c)^((9:ℝ)/8))
            = 16 * (a^(-(1:ℝ)/2) * (b+c)^((1:ℝ)/8) * (b*c)^((9:ℝ)/8)) * 1 := by ring
          _ ≤ 16 * (a^(-(1:ℝ)/2) * (b+c)^((1:ℝ)/8) * (b*c)^((9:ℝ)/8)) * ((b*c)^(ε/2)) :=
              mul_le_mul_of_nonneg_left hXh1 h16B

/-- The `D'^{1/3}(RS)^{2/3} log^4` term of `P·p14T12(D')`. -/
lemma P13_term2 (a b c p d C ε : ℝ) (ha : 0 < a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 0 ≤ d)
    (hp : p = a^(-(1:ℝ)/2) * (b + c)^(-(1:ℝ)/8) * (b * c)^((3:ℝ)/8))
    (hhi : d ≤ 16 * a * p^2)
    (hlog : (Real.log (2 * b * c) + 1) ^ (4:ℕ) ≤ C * (b * c)^(ε/2)) :
    p * (d^((1:ℝ)/3) * (b * c)^((2:ℝ)/3) * (Real.log (2 * b * c) + 1)^(4:ℕ))
      ≤ ((16:ℝ)^((1:ℝ)/3) * C)
        * (a^(-(1:ℝ)/2) * (b + c)^((1:ℝ)/8) * (b * c)^((9:ℝ)/8))
        * ((b * c)^(ε/2)) := by
  have hb0 : (0:ℝ) < b := lt_of_lt_of_le zero_lt_one hb
  have hc0 : (0:ℝ) < c := lt_of_lt_of_le zero_lt_one hc
  have hY0 : (0:ℝ) < b + c := by linarith
  have hX1 : (1:ℝ) ≤ b*c := by nlinarith [hb, hc]
  have hX0 : (0:ℝ) < b*c := lt_of_lt_of_le zero_lt_one hX1
  have hp0 : 0 < p := by rw [hp]; positivity
  have hL0 : (0:ℝ) ≤ (Real.log (2 * b * c) + 1) ^ (4:ℕ) := by
    have h1 : (0:ℝ) ≤ Real.log (2 * b * c) + 1 := by
      have h2 : (1:ℝ) ≤ 2 * b * c := by nlinarith [hb, hc]
      have := Real.log_nonneg h2; linarith
    positivity
  have hP53 : p * p^((2:ℝ)/3) = p^((5:ℝ)/3) := by
    have h := Real.rpow_add hp0 (1:ℝ) ((2:ℝ)/3)
    simp only [Real.rpow_one] at h
    rw [← h]; norm_num
  have hp53 : p^((5:ℝ)/3) = a^(-(5:ℝ)/6) * (b+c)^(-(5:ℝ)/24) * (b*c)^((5:ℝ)/8) := by
    rw [P13_prpow a b c p ha hb hc hp ((5:ℝ)/3)]; norm_num
  have hafac : a^((1:ℝ)/3) * a^(-(5:ℝ)/6) = a^(-(1:ℝ)/2) := by
    rw [← Real.rpow_add ha]; norm_num
  have hXfac : (b*c)^((5:ℝ)/8) * (b*c)^((2:ℝ)/3) = (b*c)^((31:ℝ)/24) := by
    rw [← Real.rpow_add hX0]; norm_num
  have hp2 : p^2 = p^(2:ℝ) := (Real.rpow_natCast p 2).symm
  have hdq : d^((1:ℝ)/3) ≤ (16:ℝ)^((1:ℝ)/3) * a^((1:ℝ)/3) * p^((2:ℝ)/3) := by
    rw [hp2] at hhi
    have hdq0 : d^((1:ℝ)/3) ≤ (16 * a * p^(2:ℝ))^((1:ℝ)/3) :=
      Real.rpow_le_rpow hd hhi (by norm_num)
    have hexp : (16 * a * p^(2:ℝ))^((1:ℝ)/3)
        = (16:ℝ)^((1:ℝ)/3) * a^((1:ℝ)/3) * p^((2:ℝ)/3) := by
      rw [show (16 * a * p^(2:ℝ)) = (16*a) * p^(2:ℝ) by ring]
      rw [Real.mul_rpow (by positivity) (by positivity)]
      rw [Real.mul_rpow (by positivity) (by positivity)]
      rw [← Real.rpow_mul hp0.le]; norm_num
    rw [hexp] at hdq0; exact hdq0
  have hQ : (b+c)^(-(1:ℝ)/3) * (b*c)^((1:ℝ)/6) ≤ 1 := by
    have hXle : b*c ≤ (b+c)^((2:ℝ)) := by
      have h : b*c ≤ (b+c)^2 := by nlinarith [mul_pos hb0 hc0, sq_nonneg b, sq_nonneg c]
      rw [← show (b+c)^((2:ℝ)) = (b+c)^2 from Real.rpow_natCast _ 2] at h
      exact h
    have hQ1 : (b*c)^((1:ℝ)/6) ≤ (b+c)^((1:ℝ)/3) := by
      calc (b*c)^((1:ℝ)/6) ≤ ((b+c)^((2:ℝ)))^((1:ℝ)/6) :=
            Real.rpow_le_rpow hX0.le hXle (by norm_num)
        _ = (b+c)^((2:ℝ) * ((1:ℝ)/6)) := (Real.rpow_mul hY0.le (2:ℝ) ((1:ℝ)/6)).symm
        _ = (b+c)^((1:ℝ)/3) := by norm_num
    calc (b+c)^(-(1:ℝ)/3) * (b*c)^((1:ℝ)/6)
        ≤ (b+c)^(-(1:ℝ)/3) * (b+c)^((1:ℝ)/3) := mul_le_mul_of_nonneg_left hQ1 (by positivity)
      _ = 1 := by rw [← Real.rpow_add hY0]; norm_num
  have h1 : (b+c)^(-(5:ℝ)/24) * (b*c)^((31:ℝ)/24)
      ≤ (b+c)^((1:ℝ)/8) * (b*c)^((9:ℝ)/8) := by
    have e1 : (b+c)^(-(5:ℝ)/24) * (b*c)^((31:ℝ)/24)
        = (b+c)^((1:ℝ)/8) * (b*c)^((9:ℝ)/8) * ((b+c)^(-(1:ℝ)/3) * (b*c)^((1:ℝ)/6)) := by
      rw [show (b+c)^(-(5:ℝ)/24) = (b+c)^((1:ℝ)/8) * (b+c)^(-(1:ℝ)/3) by
            rw [← Real.rpow_add hY0]; norm_num,
          show (b*c)^((31:ℝ)/24) = (b*c)^((9:ℝ)/8) * (b*c)^((1:ℝ)/6) by
            rw [← Real.rpow_add hX0]; norm_num]
      ring
    rw [e1]
    calc (b+c)^((1:ℝ)/8) * (b*c)^((9:ℝ)/8) * ((b+c)^(-(1:ℝ)/3) * (b*c)^((1:ℝ)/6))
        ≤ (b+c)^((1:ℝ)/8) * (b*c)^((9:ℝ)/8) * 1 := mul_le_mul_of_nonneg_left hQ (by positivity)
      _ = (b+c)^((1:ℝ)/8) * (b*c)^((9:ℝ)/8) := by ring
  have hmain : (b+c)^(-(5:ℝ)/24) * (b*c)^((31:ℝ)/24) * (Real.log (2*b*c)+1)^(4:ℕ)
      ≤ (b+c)^((1:ℝ)/8) * (b*c)^((9:ℝ)/8) * (C * (b*c)^(ε/2)) :=
    mul_le_mul h1 hlog hL0 (by positivity)
  have hcq : a^((1:ℝ)/3) * (a^(-(5:ℝ)/6) * (b+c)^(-(5:ℝ)/24) * (b*c)^((5:ℝ)/8))
        * (b*c)^((2:ℝ)/3) * (Real.log (2*b*c)+1)^(4:ℕ)
      = a^(-(1:ℝ)/2) * ((b+c)^(-(5:ℝ)/24) * (b*c)^((31:ℝ)/24)
        * (Real.log (2*b*c)+1)^(4:ℕ)) := by
    calc a^((1:ℝ)/3) * (a^(-(5:ℝ)/6) * (b+c)^(-(5:ℝ)/24) * (b*c)^((5:ℝ)/8))
            * (b*c)^((2:ℝ)/3) * (Real.log (2*b*c)+1)^(4:ℕ)
        = (a^((1:ℝ)/3) * a^(-(5:ℝ)/6)) * ((b+c)^(-(5:ℝ)/24) * (b*c)^((5:ℝ)/8)
            * ((b*c)^((2:ℝ)/3) * (Real.log (2*b*c)+1)^(4:ℕ))) := by ring
      _ = a^(-(1:ℝ)/2) * ((b+c)^(-(5:ℝ)/24) * (b*c)^((5:ℝ)/8)
            * ((b*c)^((2:ℝ)/3) * (Real.log (2*b*c)+1)^(4:ℕ))) := by rw [hafac]
      _ = a^(-(1:ℝ)/2) * ((b+c)^(-(5:ℝ)/24) * (((b*c)^((5:ℝ)/8) * (b*c)^((2:ℝ)/3))
            * (Real.log (2*b*c)+1)^(4:ℕ))) := by ring
      _ = a^(-(1:ℝ)/2) * ((b+c)^(-(5:ℝ)/24) * ((b*c)^((31:ℝ)/24)
            * (Real.log (2*b*c)+1)^(4:ℕ))) := by rw [hXfac]
      _ = a^(-(1:ℝ)/2) * ((b+c)^(-(5:ℝ)/24) * (b*c)^((31:ℝ)/24)
            * (Real.log (2*b*c)+1)^(4:ℕ)) := by ring
  calc p * (d^((1:ℝ)/3) * (b*c)^((2:ℝ)/3) * (Real.log (2*b*c)+1)^(4:ℕ))
      = p * d^((1:ℝ)/3) * (b*c)^((2:ℝ)/3) * (Real.log (2*b*c)+1)^(4:ℕ) := by ring
    _ ≤ p * ((16:ℝ)^((1:ℝ)/3) * a^((1:ℝ)/3) * p^((2:ℝ)/3)) * (b*c)^((2:ℝ)/3)
          * (Real.log (2*b*c)+1)^(4:ℕ) := by
        gcongr
    _ = (16:ℝ)^((1:ℝ)/3) * a^((1:ℝ)/3) * (p * p^((2:ℝ)/3)) * (b*c)^((2:ℝ)/3)
          * (Real.log (2*b*c)+1)^(4:ℕ) := by ring
    _ = (16:ℝ)^((1:ℝ)/3) * a^((1:ℝ)/3) * (a^(-(5:ℝ)/6) * (b+c)^(-(5:ℝ)/24) * (b*c)^((5:ℝ)/8))
          * (b*c)^((2:ℝ)/3) * (Real.log (2*b*c)+1)^(4:ℕ) := by rw [hP53, hp53]
    _ = (16:ℝ)^((1:ℝ)/3) * (a^((1:ℝ)/3) * (a^(-(5:ℝ)/6) * (b+c)^(-(5:ℝ)/24) * (b*c)^((5:ℝ)/8))
          * (b*c)^((2:ℝ)/3) * (Real.log (2*b*c)+1)^(4:ℕ)) := by ring
    _ = (16:ℝ)^((1:ℝ)/3) * (a^(-(1:ℝ)/2) * ((b+c)^(-(5:ℝ)/24) * (b*c)^((31:ℝ)/24)
          * (Real.log (2*b*c)+1)^(4:ℕ))) := by rw [hcq]
    _ ≤ (16:ℝ)^((1:ℝ)/3) * (a^(-(1:ℝ)/2) * ((b+c)^((1:ℝ)/8) * (b*c)^((9:ℝ)/8)
          * (C * (b*c)^(ε/2)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmain (by positivity)) (by positivity)
    _ = ((16:ℝ)^((1:ℝ)/3) * C) * (a^(-(1:ℝ)/2) * (b + c)^((1:ℝ)/8) * (b * c)^((9:ℝ)/8))
          * ((b * c)^(ε/2)) := by ring

/-- The `D'^{-1}(RS)^{3/2}(RS)^{ε/8}` term of `P·p14T12(D')`. -/
lemma P13_term3 (a b c p d ε : ℝ) (ha : 0 < a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hε : 0 < ε)
    (hp : p = a^(-(1:ℝ)/2) * (b + c)^(-(1:ℝ)/8) * (b * c)^((3:ℝ)/8))
    (hlo : a * p^2 / 2 ≤ d) :
    p * (d⁻¹ * (b * c)^((3:ℝ)/2) * ((b * c)^(ε/8)))
      ≤ 2 * (a^(-(1:ℝ)/2) * (b + c)^((1:ℝ)/8) * (b * c)^((9:ℝ)/8))
        * ((b * c)^(ε/2)) := by
  have hX1 : (1:ℝ) ≤ b * c := by nlinarith [hb, hc]
  have hX0 : (0:ℝ) < b * c := lt_of_lt_of_le zero_lt_one hX1
  have hp0 : 0 < p := by rw [hp]; positivity
  have happ : 0 < a * p^2 / 2 := by positivity
  have hdinv : d⁻¹ ≤ (a * p^2 / 2)⁻¹ := inv_anti₀ happ hlo
  have hstep : p * d⁻¹ ≤ 2 * (a⁻¹ * p⁻¹) := by
    have h1 : p * d⁻¹ ≤ p * (a * p^2 / 2)⁻¹ := mul_le_mul_of_nonneg_left hdinv hp0.le
    have h2 : p * (a * p^2 / 2)⁻¹ = 2 * (a⁻¹ * p⁻¹) := by field_simp
    exact h1.trans h2.le
  have hp_inv : p⁻¹ = a^((1:ℝ)/2) * (b+c)^((1:ℝ)/8) * (b*c)^(-(3:ℝ)/8) := by
    rw [← Real.rpow_neg_one p, P13_prpow a b c p ha hb hc hp (-(1:ℝ))]
    norm_num
  have hAinv : a⁻¹ * p⁻¹ = a^(-(1:ℝ)/2) * (b+c)^((1:ℝ)/8) * (b*c)^(-(3:ℝ)/8) := by
    rw [hp_inv, (Real.rpow_neg_one a).symm]
    have hA : a^(-(1:ℝ)) * a^((1:ℝ)/2) = a^(-(1:ℝ)/2) := by
      have h := Real.rpow_add ha (-(1:ℝ)) ((1:ℝ)/2)
      rw [← h]; norm_num
    calc a^(-(1:ℝ)) * (a^((1:ℝ)/2) * (b+c)^((1:ℝ)/8) * (b*c)^(-(3:ℝ)/8))
        = (a^(-(1:ℝ)) * a^((1:ℝ)/2)) * ((b+c)^((1:ℝ)/8) * (b*c)^(-(3:ℝ)/8)) := by ring
      _ = a^(-(1:ℝ)/2) * ((b+c)^((1:ℝ)/8) * (b*c)^(-(3:ℝ)/8)) := by rw [hA]
      _ = a^(-(1:ℝ)/2) * (b+c)^((1:ℝ)/8) * (b*c)^(-(3:ℝ)/8) := by ring
  have key : a⁻¹ * p⁻¹ * (b*c)^((3:ℝ)/2)
      = a^(-(1:ℝ)/2) * (b+c)^((1:ℝ)/8) * (b*c)^((9:ℝ)/8) := by
    rw [hAinv]
    have hX : (b*c)^(-(3:ℝ)/8) * (b*c)^((3:ℝ)/2) = (b*c)^((9:ℝ)/8) := by
      rw [← Real.rpow_add hX0]; norm_num
    calc (a^(-(1:ℝ)/2) * (b+c)^((1:ℝ)/8) * (b*c)^(-(3:ℝ)/8)) * (b*c)^((3:ℝ)/2)
        = a^(-(1:ℝ)/2) * (b+c)^((1:ℝ)/8) * ((b*c)^(-(3:ℝ)/8) * (b*c)^((3:ℝ)/2)) := by ring
      _ = a^(-(1:ℝ)/2) * (b+c)^((1:ℝ)/8) * (b*c)^((9:ℝ)/8) := by rw [hX]
  have hXeps : (b*c)^(ε/8) ≤ (b*c)^(ε/2) :=
    Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  calc p * (d⁻¹ * (b*c)^((3:ℝ)/2) * ((b*c)^(ε/8)))
      = (p * d⁻¹) * ((b*c)^((3:ℝ)/2) * ((b*c)^(ε/8))) := by ring
    _ ≤ (2 * (a⁻¹ * p⁻¹)) * ((b*c)^((3:ℝ)/2) * ((b*c)^(ε/8))) :=
        mul_le_mul_of_nonneg_right hstep (by positivity)
    _ = 2 * (a⁻¹ * p⁻¹ * (b*c)^((3:ℝ)/2)) * (b*c)^(ε/8) := by ring
    _ = 2 * (a^(-(1:ℝ)/2) * (b+c)^((1:ℝ)/8) * (b*c)^((9:ℝ)/8)) * (b*c)^(ε/8) := by rw [key]
    _ ≤ 2 * (a^(-(1:ℝ)/2) * (b+c)^((1:ℝ)/8) * (b*c)^((9:ℝ)/8)) * (b*c)^(ε/2) :=
        mul_le_mul_of_nonneg_left hXeps (by positivity)

/-- The two "off-diagonal" terms `P·R S^{3/4}` and `P·S R^{3/4}` of `P·p14T12(D')`. -/
lemma P13_term45_half (a b c p : ℝ) (ha : 0 < a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hp : p = a^(-(1:ℝ)/2) * (b + c)^(-(1:ℝ)/8) * (b * c)^((3:ℝ)/8)) :
    p * (b * c^((3:ℝ)/4)) ≤ a^(-(1:ℝ)/2) * (b + c)^((1:ℝ)/8) * (b * c)^((9:ℝ)/8) := by
  have hb0 : (0:ℝ) < b := lt_of_lt_of_le zero_lt_one hb
  have hc0 : (0:ℝ) < c := lt_of_lt_of_le zero_lt_one hc
  have hY0 : (0:ℝ) < b + c := by linarith
  have hX1 : (1:ℝ) ≤ b * c := by nlinarith [hb, hc]
  have hX0 : (0:ℝ) < b * c := lt_of_lt_of_le zero_lt_one hX1
  have hid : (b*c)^((3:ℝ)/8) * (b * c^((3:ℝ)/4)) = b^((1:ℝ)/4) * (b*c)^((9:ℝ)/8) := by
    have h1 : b * c^((3:ℝ)/4) = b^((1:ℝ)/4) * (b*c)^((3:ℝ)/4) := by
      rw [Real.mul_rpow hb0.le hc0.le, ← mul_assoc, ← Real.rpow_add hb0]; norm_num
    calc (b*c)^((3:ℝ)/8) * (b * c^((3:ℝ)/4))
        = (b*c)^((3:ℝ)/8) * (b^((1:ℝ)/4) * (b*c)^((3:ℝ)/4)) := by rw [h1]
      _ = ((b*c)^((3:ℝ)/8) * (b*c)^((3:ℝ)/4)) * b^((1:ℝ)/4) := by ring
      _ = (b*c)^((3:ℝ)/8 + (3:ℝ)/4) * b^((1:ℝ)/4) := by rw [← Real.rpow_add hX0]
      _ = (b*c)^((9:ℝ)/8) * b^((1:ℝ)/4) := by norm_num
      _ = b^((1:ℝ)/4) * (b*c)^((9:ℝ)/8) := by ring
  have hbq : b^((1:ℝ)/4) ≤ (b+c)^((1:ℝ)/4) :=
    Real.rpow_le_rpow hb0.le (by linarith) (by norm_num)
  have hfac : (b+c)^(-(1:ℝ)/8) * b^((1:ℝ)/4) ≤ (b+c)^((1:ℝ)/8) := by
    have h1 : (b+c)^(-(1:ℝ)/8) * (b+c)^((1:ℝ)/4) = (b+c)^((1:ℝ)/8) := by
      rw [← Real.rpow_add hY0]; norm_num
    calc (b+c)^(-(1:ℝ)/8) * b^((1:ℝ)/4)
        ≤ (b+c)^(-(1:ℝ)/8) * (b+c)^((1:ℝ)/4) :=
          mul_le_mul_of_nonneg_left hbq (by positivity)
      _ = (b+c)^((1:ℝ)/8) := h1
  have hred : (b+c)^(-(1:ℝ)/8) * ((b*c)^((3:ℝ)/8) * (b * c^((3:ℝ)/4)))
      ≤ (b+c)^((1:ℝ)/8) * (b*c)^((9:ℝ)/8) := by
    rw [hid]
    calc (b+c)^(-(1:ℝ)/8) * (b^((1:ℝ)/4) * (b*c)^((9:ℝ)/8))
        = ((b+c)^(-(1:ℝ)/8) * b^((1:ℝ)/4)) * (b*c)^((9:ℝ)/8) := by ring
      _ ≤ (b+c)^((1:ℝ)/8) * (b*c)^((9:ℝ)/8) := mul_le_mul_of_nonneg_right hfac (by positivity)
  rw [hp]
  calc a^(-(1:ℝ)/2) * (b+c)^(-(1:ℝ)/8) * (b*c)^((3:ℝ)/8) * (b * c^((3:ℝ)/4))
      = a^(-(1:ℝ)/2) * ((b+c)^(-(1:ℝ)/8) * ((b*c)^((3:ℝ)/8) * (b * c^((3:ℝ)/4)))) := by ring
    _ ≤ a^(-(1:ℝ)/2) * ((b+c)^((1:ℝ)/8) * (b*c)^((9:ℝ)/8)) :=
        mul_le_mul_of_nonneg_left hred (by positivity)
    _ = a^(-(1:ℝ)/2) * (b+c)^((1:ℝ)/8) * (b*c)^((9:ℝ)/8) := by ring

lemma P13_term45 (a b c p ε : ℝ) (ha : 0 < a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hε : 0 < ε)
    (hp : p = a^(-(1:ℝ)/2) * (b + c)^(-(1:ℝ)/8) * (b * c)^((3:ℝ)/8)) :
    p * ((b * c^((3:ℝ)/4) + c * b^((3:ℝ)/4)) * ((b * c)^(ε/8)))
      ≤ 2 * (a^(-(1:ℝ)/2) * (b + c)^((1:ℝ)/8) * (b * c)^((9:ℝ)/8))
        * ((b * c)^(ε/2)) := by
  have hX1 : (1:ℝ) ≤ b * c := by nlinarith [hb, hc]
  have hkey1 := P13_term45_half a b c p ha hb hc hp
  have hkey2 : p * (c * b^((3:ℝ)/4)) ≤ a^(-(1:ℝ)/2) * (b + c)^((1:ℝ)/8) * (b * c)^((9:ℝ)/8) := by
    have h := P13_term45_half a c b p ha hc hb (by rw [hp]; ring_nf)
    simpa only [add_comm c b, mul_comm c b] using h
  have hXeps : (b*c)^(ε/8) ≤ (b*c)^(ε/2) := Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  calc p * ((b * c^((3:ℝ)/4) + c * b^((3:ℝ)/4)) * ((b*c)^(ε/8)))
      = (p * (b * c^((3:ℝ)/4))) * (b*c)^(ε/8) + (p * (c * b^((3:ℝ)/4))) * (b*c)^(ε/8) := by ring
    _ ≤ (a^(-(1:ℝ)/2) * (b + c)^((1:ℝ)/8) * (b * c)^((9:ℝ)/8)) * (b*c)^(ε/8)
          + (a^(-(1:ℝ)/2) * (b + c)^((1:ℝ)/8) * (b * c)^((9:ℝ)/8)) * (b*c)^(ε/8) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right hkey1 (by positivity)
        · exact mul_le_mul_of_nonneg_right hkey2 (by positivity)
    _ = 2 * (a^(-(1:ℝ)/2) * (b + c)^((1:ℝ)/8) * (b * c)^((9:ℝ)/8)) * (b*c)^(ε/8) := by ring
    _ ≤ 2 * (a^(-(1:ℝ)/2) * (b + c)^((1:ℝ)/8) * (b * c)^((9:ℝ)/8)) * (b*c)^(ε/2) :=
        mul_le_mul_of_nonneg_left hXeps (by positivity)

theorem P13_num_small (ε : ℝ) (hε : 0 < ε) : ∃ K : ℝ, 0 < K ∧
    ∀ (D R S : ℕ) (P : ℝ) (D' : ℕ), 1 ≤ D → 1 ≤ R → 1 ≤ S →
      P = (D : ℝ) ^ (-(1:ℝ)/2) * ((R : ℝ) + (S : ℝ)) ^ (-(1:ℝ)/8)
            * ((R : ℝ) * (S : ℝ)) ^ ((3:ℝ)/8) →
      1 < P → 1 ≤ D' → (D : ℝ) * P ^ 2 / 2 ≤ (D' : ℝ) → (D' : ℝ) ≤ 16 * (D : ℝ) * P ^ 2 →
        P * p14T12 D' R S (ε/8) ≤ K * p14T13 D R S ε * (((R : ℝ) * (S : ℝ)) ^ (ε/2)) := by
  obtain ⟨C, hC0, hlogC⟩ := P13_log_pow_le ε hε
  refine ⟨20 + (16:ℝ)^((1:ℝ)/3) * C, by positivity, ?_⟩
  intro D R S P D' hD hR hS hP _hP1 hD1 hlo hhi
  have ha1 : (1:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
  have hb1 : (1:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR
  have hc1 : (1:ℝ) ≤ (S:ℝ) := by exact_mod_cast hS
  have ha0 : (0:ℝ) < (D:ℝ) := lt_of_lt_of_le zero_lt_one ha1
  have hd0 : (0:ℝ) ≤ (D':ℝ) := by positivity
  have hbc1 : (1:ℝ) ≤ (R:ℝ)*(S:ℝ) := by nlinarith [hb1, hc1]
  have hlog2 : (Real.log (2 * (R:ℝ) * (S:ℝ)) + 1)^(4:ℕ) ≤ C * ((R:ℝ)*(S:ℝ))^(ε/2) := by
    have h := hlogC ((R:ℝ)*(S:ℝ)) hbc1
    rw [← show (2:ℝ) * (R:ℝ) * (S:ℝ) = 2 * ((R:ℝ)*(S:ℝ)) by ring] at h
    exact h
  have ht1 := P13_term1 (D:ℝ) (R:ℝ) (S:ℝ) P (D':ℝ) ε ha0 hb1 hc1 hε hP hhi
  have ht2 := P13_term2 (D:ℝ) (R:ℝ) (S:ℝ) P (D':ℝ) C ε ha0 hb1 hc1 hd0 hP hhi hlog2
  have ht3 := P13_term3 (D:ℝ) (R:ℝ) (S:ℝ) P (D':ℝ) ε ha0 hb1 hc1 hε hP hlo
  have ht45 := P13_term45 (D:ℝ) (R:ℝ) (S:ℝ) P ε ha0 hb1 hc1 hε hP
  rw [p14T12, p14T13]
  set B : ℝ := (D:ℝ)^(-(1:ℝ)/2) * ((R:ℝ)+(S:ℝ))^((1:ℝ)/8) * ((R:ℝ)*(S:ℝ))^((9:ℝ)/8) with hB
  set Xh : ℝ := ((R:ℝ)*(S:ℝ))^(ε/2) with hXh
  set A : ℝ := (D:ℝ) * ((R:ℝ)+(S:ℝ))^((1:ℝ)/4) * ((R:ℝ)*(S:ℝ))^((1:ℝ)/4) with hA
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hXh0 : 0 ≤ Xh := by rw [hXh]; positivity
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hexp : P * ((D':ℝ)
        + (D':ℝ)^((1:ℝ)/3) * ((R:ℝ)*(S:ℝ))^((2:ℝ)/3) * (Real.log (2*(R:ℝ)*(S:ℝ))+1)^(4:ℕ)
        + (((D':ℝ)⁻¹ * ((R:ℝ)*(S:ℝ))^((3:ℝ)/2) + (R:ℝ)*(S:ℝ)^((3:ℝ)/4) + (S:ℝ)*(R:ℝ)^((3:ℝ)/4))
            * (((R:ℝ)*(S:ℝ))^(ε/8))))
      = P * (D':ℝ)
        + P * ((D':ℝ)^((1:ℝ)/3) * ((R:ℝ)*(S:ℝ))^((2:ℝ)/3) * (Real.log (2*(R:ℝ)*(S:ℝ))+1)^(4:ℕ))
        + P * ((D':ℝ)⁻¹ * ((R:ℝ)*(S:ℝ))^((3:ℝ)/2) * (((R:ℝ)*(S:ℝ))^(ε/8)))
        + P * (((R:ℝ)*(S:ℝ)^((3:ℝ)/4) + (S:ℝ)*(R:ℝ)^((3:ℝ)/4)) * (((R:ℝ)*(S:ℝ))^(ε/8))) := by
    ring
  rw [hexp]
  have hsum : P * (D':ℝ)
        + P * ((D':ℝ)^((1:ℝ)/3) * ((R:ℝ)*(S:ℝ))^((2:ℝ)/3) * (Real.log (2*(R:ℝ)*(S:ℝ))+1)^(4:ℕ))
        + P * ((D':ℝ)⁻¹ * ((R:ℝ)*(S:ℝ))^((3:ℝ)/2) * (((R:ℝ)*(S:ℝ))^(ε/8)))
        + P * (((R:ℝ)*(S:ℝ)^((3:ℝ)/4) + (S:ℝ)*(R:ℝ)^((3:ℝ)/4)) * (((R:ℝ)*(S:ℝ))^(ε/8)))
      ≤ (20 + (16:ℝ)^((1:ℝ)/3) * C) * (B * Xh) := by
    nlinarith [ht1, ht2, ht3, ht45]
  have hstep : (20 + (16:ℝ)^((1:ℝ)/3) * C) * (B * Xh)
      ≤ (20 + (16:ℝ)^((1:ℝ)/3) * C) * (A + B) * Xh := by
    have hK0 : (0:ℝ) ≤ 20 + (16:ℝ)^((1:ℝ)/3) * C := by positivity
    have hBA : B ≤ A + B := by linarith
    calc (20 + (16:ℝ)^((1:ℝ)/3) * C) * (B * Xh)
        ≤ (20 + (16:ℝ)^((1:ℝ)/3) * C) * ((A + B) * Xh) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hBA hXh0) hK0
      _ = (20 + (16:ℝ)^((1:ℝ)/3) * C) * (A + B) * Xh := by ring
  linarith [hsum, hstep]

end

end Work.FIArea4
