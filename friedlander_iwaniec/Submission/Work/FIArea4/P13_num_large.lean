import Mathlib
import Submission.Work.FIArea4.A4varbounds

/-!
# `P13_num_large`: the numerical comparison of `p14T12` and `p14T13` for `P ≤ 1`

Friedlander–Iwaniec, §13.  The scale attached to `(D,R,S)` is

  `P = D^{-1/2} (R+S)^{-1/8} (RS)^{3/8}`,

and the paper needs the elementary numerical comparison of the two brackets
`p14T12` (Proposition 12.1) and `p14T13` (Proposition 13.1) in the range `P ≤ 1`:

  `p14T12(D,R,S,ε/8) ≤ K(ε) · p14T13(D,R,S,ε) · (RS)^{ε/2}`.

The hypothesis `P ≤ 1` is equivalent to the *arithmetic* constraint

  `(RS)^3 ≤ D^4 (R+S)`,

which is the only place where `P` is used.  With it, the three "large-`D`" summands of `T12`
(the `D`, the `D^{1/3}(RS)^{2/3}log⁴`, and the `D^{-1}(RS)^{3/2}` terms) and the two symmetric
`RS^{3/4}`, `SR^{3/4}` terms are each absorbed by `T13`; the `log⁴` factor is absorbed into
`(RS)^{ε/2}` with a constant depending on `ε`.

## Proof outline

With `A = RS`, `B = R+S`, `d = D`, `T₁ = d B^{1/4} A^{1/4}` and `T₂ = d^{-1/2}B^{1/8}A^{9/8}`
(the two summands of `T13`):

* `d ≤ T₁` and `A ≤ T₁` come from `A^3 ≤ d^4 B` (i.e. `A^{3/4} ≤ d B^{1/4}`);
* `d^{-1}A^{3/2} ≤ T₂` likewise;
* `d^{1/3}A^{2/3} ≤ 2^{-7/36}(T₁+T₂)`: the weighted AM–GM
  `T₁^{5/9}T₂^{4/9} ≤ T₁+T₂` together with `B^2 ≥ 4A` (`B ≥ 2√A`), which gives
  `T₁^{5/9}T₂^{4/9} = d^{1/3}B^{7/36}A^{23/36} ≥ 2^{7/36}d^{1/3}A^{53/72} ≥ 2^{7/36}d^{1/3}A^{2/3}`;
* `a b^{3/4} ≤ A` and `b a^{3/4} ≤ A`;
* `(log(2A)+1)^4 ≤ C_ε A^{ε/2}` (the elementary `log t ≤ t^{δ}/δ`).
-/

namespace Work.FIArea4

noncomputable section

/-- For every `ε > 0` there is `C` with `(log(2A)+1)^4 ≤ C A^{ε/2}` for all `A ≥ 1`. -/
private lemma p13nl_log_four_le (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 1 ≤ A →
      (Real.log (2 * A) + 1) ^ 4 ≤ C * A ^ (ε / 2) := by
  refine ⟨(8 * (2:ℝ)^(ε/8) / ε + 1)^4, by positivity, ?_⟩
  intro A hA
  have hA1 : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have h2A : 0 < 2*A := by positivity
  have h1 : Real.log (2*A) ≤ (8 * (2:ℝ)^(ε/8) / ε) * A^(ε/8) := by
    have hlog := Real.log_le_rpow_div (le_of_lt h2A) (show 0 < ε/8 by positivity)
    rw [Real.mul_rpow (by norm_num) (le_of_lt hA1)] at hlog
    calc Real.log (2*A) ≤ ((2:ℝ)^(ε/8)*A^(ε/8))/(ε/8) := hlog
      _ = (8 * (2:ℝ)^(ε/8) / ε) * A^(ε/8) := by field_simp
  have hAε8 : 1 ≤ A^(ε/8) := Real.one_le_rpow hA (by positivity)
  have h2 : Real.log (2*A) + 1 ≤ (8 * (2:ℝ)^(ε/8) / ε + 1) * A^(ε/8) := by
    have hrw : (8 * (2:ℝ)^(ε/8) / ε + 1) * A^(ε/8)
        = (8 * (2:ℝ)^(ε/8) / ε) * A^(ε/8) + A^(ε/8) := by ring
    rw [hrw]; linarith
  have h3 : 0 ≤ Real.log (2*A) + 1 := by
    have h : (1:ℝ) ≤ 2*A := by linarith
    have := Real.log_nonneg h
    linarith
  calc (Real.log (2*A) + 1)^4
      ≤ ((8 * (2:ℝ)^(ε/8) / ε + 1) * A^(ε/8))^4 := pow_le_pow_left₀ h3 h2 4
    _ = (8 * (2:ℝ)^(ε/8) / ε + 1)^4 * A^(ε/2) := by
          rw [mul_pow, ← Real.rpow_natCast (A^((ε:ℝ)/8)) 4, ← Real.rpow_mul (le_of_lt hA1),
              show ε/8*((4:ℕ):ℝ) = ε/2 by ring]

/-- `d^{1/3}A^{2/3} ≤ 2^{-7/36}(T₁+T₂)` where `A = ab`, `B = a+b` and `T₁, T₂` are the two
summands of `p14T13`. -/
private lemma p13nl_third_mul_le (a b d : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hd : 1 ≤ d) :
    d ^ ((1:ℝ)/3) * (a*b) ^ ((2:ℝ)/3)
      ≤ (2:ℝ)^(-(7:ℝ)/36) * (d * (a+b)^((1:ℝ)/4) * (a*b)^((1:ℝ)/4)
          + d ^ (-(1:ℝ)/2) * (a+b)^((1:ℝ)/8) * (a*b)^((9:ℝ)/8)) := by
  generalize hAdef : a*b = A
  generalize hBdef : a+b = B
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hb0 : 0 < b := lt_of_lt_of_le zero_lt_one hb
  have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have hA0 : 0 < A := by rw [← hAdef]; positivity
  have hB0 : 0 < B := by rw [← hBdef]; positivity
  have hA1 : 1 ≤ A := by rw [← hAdef]; nlinarith
  have hB2 : 4*A ≤ (B^2 : ℝ) := by rw [← hAdef, ← hBdef]; nlinarith [sq_nonneg (a-b)]
  have hB2r : 4*A ≤ B^(2:ℝ) := by
    rw [show B^(2:ℝ) = (B:ℝ)^(2:ℕ) by exact Real.rpow_natCast B 2]
    exact hB2
  set T1 : ℝ := d * B^((1:ℝ)/4) * A^((1:ℝ)/4) with hT1
  set T2 : ℝ := d ^ (-(1:ℝ)/2) * B^((1:ℝ)/8) * A^((9:ℝ)/8) with hT2
  have hT1nn : 0 ≤ T1 := by rw [hT1]; positivity
  have hT2nn : 0 ≤ T2 := by rw [hT2]; positivity
  have hAMGM : T1^((5:ℝ)/9) * T2^((4:ℝ)/9) ≤ T1 + T2 := by
    have h := Real.geom_mean_le_arith_mean2_weighted (w₁ := (5:ℝ)/9) (w₂ := (4:ℝ)/9)
      (p₁ := T1) (p₂ := T2) (by norm_num) (by norm_num) hT1nn hT2nn (by norm_num)
    have e1 : (5:ℝ)/9 * T1 ≤ T1 := by nlinarith
    have e2 : (4:ℝ)/9 * T2 ≤ T2 := by nlinarith
    linarith
  have hkey : T1^((5:ℝ)/9) * T2^((4:ℝ)/9) = d^((1:ℝ)/3)*B^((7:ℝ)/36)*A^((23:ℝ)/36) := by
    rw [hT1, hT2]
    rw [Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_mul (le_of_lt hB0), ← Real.rpow_mul (le_of_lt hA0),
        ← Real.rpow_mul (le_of_lt hB0), ← Real.rpow_mul (le_of_lt hA0),
        ← Real.rpow_mul (le_of_lt hd0)]
    rw [show (1:ℝ)/4 * (5 / 9) = (5:ℝ)/36 by norm_num,
        show (1:ℝ)/8 * (4 / 9) = (1:ℝ)/18 by norm_num,
        show (9:ℝ)/8 * (4 / 9) = (1:ℝ)/2 by norm_num,
        show -(1:ℝ)/2 * (4 / 9) = -(2:ℝ)/9 by norm_num]
    have h1 : d^((5:ℝ)/9) * d^(-(2:ℝ)/9) = d^((1:ℝ)/3) := by
      rw [← Real.rpow_add hd0]; norm_num
    have h2 : B^((5:ℝ)/36) * B^((1:ℝ)/18) = B^((7:ℝ)/36) := by
      rw [← Real.rpow_add hB0]; norm_num
    have h3 : A^((5:ℝ)/36) * A^((1:ℝ)/2) = A^((23:ℝ)/36) := by
      rw [← Real.rpow_add hA0]; norm_num
    calc d^((5:ℝ)/9) * B^((5:ℝ)/36) * A^((5:ℝ)/36) * (d^(-(2:ℝ)/9) * B^((1:ℝ)/18) * A^((1:ℝ)/2))
        = (d^((5:ℝ)/9)*d^(-(2:ℝ)/9)) * (B^((5:ℝ)/36)*B^((1:ℝ)/18)) * (A^((5:ℝ)/36)*A^((1:ℝ)/2)) := by ring
      _ = d^((1:ℝ)/3)*B^((7:ℝ)/36)*A^((23:ℝ)/36) := by rw [h1,h2,h3]
  have hstep : (2:ℝ)^((7:ℝ)/36) * A^((7:ℝ)/72) ≤ B^((7:ℝ)/36) := by
    have h1 : (4*A)^((7:ℝ)/72) ≤ (B^(2:ℝ))^((7:ℝ)/72) :=
      Real.rpow_le_rpow (by positivity) hB2r (by norm_num)
    have h2 : (4*A)^((7:ℝ)/72) = (2:ℝ)^((7:ℝ)/36) * A^((7:ℝ)/72) := by
      rw [Real.mul_rpow (by norm_num) (by positivity)]
      congr 1
      rw [show (4:ℝ) = (2:ℝ)^(2:ℝ) by norm_num [Real.rpow_natCast]]
      rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
    have h3 : (B^(2:ℝ))^((7:ℝ)/72) = B^((7:ℝ)/36) := by
      rw [← Real.rpow_mul (le_of_lt hB0)]; norm_num
    linarith
  have hAexp : A^((2:ℝ)/3) ≤ A^((53:ℝ)/72) :=
    Real.rpow_le_rpow_of_exponent_le hA1 (by norm_num)
  have hA53 : A^((53:ℝ)/72) = A^((7:ℝ)/72) * A^((23:ℝ)/36) := by
    rw [← Real.rpow_add hA0]; norm_num
  have hmid : (2:ℝ)^((7:ℝ)/36) * A^((2:ℝ)/3) ≤ B^((7:ℝ)/36) * A^((23:ℝ)/36) := by
    have h := mul_le_mul_of_nonneg_right hstep (show (0:ℝ) ≤ A^((23:ℝ)/36) by positivity)
    rw [mul_assoc] at h
    calc (2:ℝ)^((7:ℝ)/36) * A^((2:ℝ)/3)
        ≤ (2:ℝ)^((7:ℝ)/36) * A^((53:ℝ)/72) :=
          mul_le_mul_of_nonneg_left hAexp (by positivity)
      _ = (2:ℝ)^((7:ℝ)/36) * (A^((7:ℝ)/72) * A^((23:ℝ)/36)) := by rw [hA53]
      _ ≤ B^((7:ℝ)/36)*A^((23:ℝ)/36) := h
  have hmain : (2:ℝ)^((7:ℝ)/36) * (d^((1:ℝ)/3) * A^((2:ℝ)/3)) ≤ T1 + T2 := by
    calc (2:ℝ)^((7:ℝ)/36) * (d^((1:ℝ)/3) * A^((2:ℝ)/3))
        = d^((1:ℝ)/3) * ((2:ℝ)^((7:ℝ)/36) * A^((2:ℝ)/3)) := by ring
      _ ≤ d^((1:ℝ)/3) * (B^((7:ℝ)/36) * A^((23:ℝ)/36)) :=
          mul_le_mul_of_nonneg_left hmid (by positivity)
      _ = T1^((5:ℝ)/9) * T2^((4:ℝ)/9) := by rw [hkey]; ring
      _ ≤ T1 + T2 := hAMGM
  have hconj : d^((1:ℝ)/3) * A^((2:ℝ)/3)
      = (2:ℝ)^(-(7:ℝ)/36) * ((2:ℝ)^((7:ℝ)/36) * (d^((1:ℝ)/3) * A^((2:ℝ)/3))) := by
    rw [← mul_assoc, ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    rw [show -(7:ℝ)/36 + (7:ℝ)/36 = 0 by norm_num, Real.rpow_zero, one_mul]
  rw [hT1, hT2] at hmain
  calc d^((1:ℝ)/3) * A^((2:ℝ)/3)
      = (2:ℝ)^(-(7:ℝ)/36) * ((2:ℝ)^((7:ℝ)/36) * (d^((1:ℝ)/3) * A^((2:ℝ)/3))) := hconj
    _ ≤ (2:ℝ)^(-(7:ℝ)/36) * (d * B^((1:ℝ)/4) * A^((1:ℝ)/4)
          + d ^ (-(1:ℝ)/2) * B^((1:ℝ)/8) * A^((9:ℝ)/8)) :=
        mul_le_mul_of_nonneg_left hmain (by positivity)

/-- `d^{-1}A^{3/2} ≤ T₂` under the constraint `A^3 ≤ d^4 B`. -/
private lemma p13nl_inv_mul_le (a b d : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hd : 1 ≤ d)
    (hcon : (a*b)^3 ≤ d^4 * (a+b)) :
    d⁻¹ * (a*b) ^ ((3:ℝ)/2) ≤ d ^ (-(1:ℝ)/2) * (a+b)^((1:ℝ)/8) * (a*b)^((9:ℝ)/8) := by
  generalize hAdef : a*b = A
  generalize hBdef : a+b = B
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have hA0 : 0 < A := by rw [← hAdef]; positivity
  have hB0 : 0 < B := by rw [← hBdef]; positivity
  have hconr : A^(3:ℝ) ≤ d^(4:ℝ) * B := by
    rw [show A^(3:ℝ) = A^3 by exact Real.rpow_natCast A 3,
        show d^(4:ℝ) = d^4 by exact Real.rpow_natCast d 4,
        ← hAdef, ← hBdef]
    exact hcon
  have h1 : (A^(3:ℝ))^((1:ℝ)/8) ≤ (d^(4:ℝ)*B)^((1:ℝ)/8) :=
    Real.rpow_le_rpow (by positivity) hconr (by norm_num)
  have h2 : (A^(3:ℝ))^((1:ℝ)/8) = A^((3:ℝ)/8) := by
    rw [← Real.rpow_mul (le_of_lt hA0)]; norm_num
  have h3 : (d^(4:ℝ)*B)^((1:ℝ)/8) = d^((1:ℝ)/2) * B^((1:ℝ)/8) := by
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (le_of_lt hd0)]
    norm_num
  have hstep : A^((3:ℝ)/8) ≤ d^((1:ℝ)/2) * B^((1:ℝ)/8) := by
    rw [← h2, ← h3]; exact h1
  have hstep2 : d^(-(1:ℝ)/2) * A^((3:ℝ)/8) ≤ B^((1:ℝ)/8) := by
    have h := mul_le_mul_of_nonneg_left hstep (show (0:ℝ) ≤ d^(-(1:ℝ)/2) by positivity)
    have e : d^(-(1:ℝ)/2) * (d^((1:ℝ)/2) * B^((1:ℝ)/8)) = B^((1:ℝ)/8) := by
      rw [← mul_assoc, ← Real.rpow_add hd0, show -(1:ℝ)/2 + (1:ℝ)/2 = 0 by norm_num,
          Real.rpow_zero, one_mul]
    rwa [e] at h
  have e1 : d^(-(1:ℝ)/2) * d^(-(1:ℝ)/2) = d⁻¹ := by
    rw [← Real.rpow_add hd0, show -(1:ℝ)/2 + -(1:ℝ)/2 = -1 by norm_num, Real.rpow_neg_one]
  have e2 : A^((3:ℝ)/8) * A^((9:ℝ)/8) = A^((3:ℝ)/2) := by
    rw [← Real.rpow_add hA0]; norm_num
  have heq : d^(-(1:ℝ)/2) * A^((3:ℝ)/8) * (d^(-(1:ℝ)/2) * A^((9:ℝ)/8)) = d⁻¹ * A^((3:ℝ)/2) := by
    rw [show d^(-(1:ℝ)/2) * A^((3:ℝ)/8) * (d^(-(1:ℝ)/2) * A^((9:ℝ)/8))
          = (d^(-(1:ℝ)/2)*d^(-(1:ℝ)/2)) * (A^((3:ℝ)/8)*A^((9:ℝ)/8)) by ring, e1, e2]
  calc d⁻¹ * A^((3:ℝ)/2)
      = d^(-(1:ℝ)/2) * A^((3:ℝ)/8) * (d^(-(1:ℝ)/2) * A^((9:ℝ)/8)) := heq.symm
    _ ≤ B^((1:ℝ)/8) * (d^(-(1:ℝ)/2) * A^((9:ℝ)/8)) :=
        mul_le_mul_of_nonneg_right hstep2 (by positivity)
    _ = d^(-(1:ℝ)/2) * B^((1:ℝ)/8) * A^((9:ℝ)/8) := by ring

/-- `a b^{3/4} ≤ T₁` and `b a^{3/4} ≤ T₁` under the constraint `A^3 ≤ d^4 B`. -/
private lemma p13nl_mul_quarter_le (a b d : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hd : 1 ≤ d)
    (hcon : (a*b)^3 ≤ d^4 * (a+b)) :
    a * b^((3:ℝ)/4) ≤ d * (a+b)^((1:ℝ)/4) * (a*b)^((1:ℝ)/4) ∧
    b * a^((3:ℝ)/4) ≤ d * (a+b)^((1:ℝ)/4) * (a*b)^((1:ℝ)/4) := by
  generalize hAdef : a*b = A
  generalize hBdef : a+b = B
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hb0 : 0 < b := lt_of_lt_of_le zero_lt_one hb
  have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have hA0 : 0 < A := by rw [← hAdef]; positivity
  have hB0 : 0 < B := by rw [← hBdef]; positivity
  have hconr : A^(3:ℝ) ≤ d^(4:ℝ) * B := by
    rw [show A^(3:ℝ) = A^3 by exact Real.rpow_natCast A 3,
        show d^(4:ℝ) = d^4 by exact Real.rpow_natCast d 4,
        ← hAdef, ← hBdef]
    exact hcon
  have h1 : (A^(3:ℝ))^((1:ℝ)/4) ≤ (d^(4:ℝ)*B)^((1:ℝ)/4) :=
    Real.rpow_le_rpow (by positivity) hconr (by norm_num)
  have h2 : (A^(3:ℝ))^((1:ℝ)/4) = A^((3:ℝ)/4) := by
    rw [← Real.rpow_mul (le_of_lt hA0)]; norm_num
  have h3 : (d^(4:ℝ)*B)^((1:ℝ)/4) = d * B^((1:ℝ)/4) := by
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (le_of_lt hd0),
        show (4:ℝ)*(1/4) = 1 by norm_num, Real.rpow_one]
  have hstep : A^((3:ℝ)/4) ≤ d * B^((1:ℝ)/4) := by rw [← h2, ← h3]; exact h1
  have hAsplit : A^((3:ℝ)/4) * A^((1:ℝ)/4) = A := by
    rw [← Real.rpow_add hA0, show (3:ℝ)/4 + (1:ℝ)/4 = 1 by norm_num, Real.rpow_one]
  have hAle : A ≤ d * B^((1:ℝ)/4) * A^((1:ℝ)/4) := by
    calc A = A^((3:ℝ)/4) * A^((1:ℝ)/4) := hAsplit.symm
      _ ≤ (d * B^((1:ℝ)/4)) * A^((1:ℝ)/4) := mul_le_mul_of_nonneg_right hstep (by positivity)
      _ = d * B^((1:ℝ)/4) * A^((1:ℝ)/4) := by ring
  have hb34 : b^((3:ℝ)/4) ≤ b := by
    have h : b^((3:ℝ)/4) ≤ b^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hb (by norm_num)
    rwa [Real.rpow_one] at h
  have ha34 : a^((3:ℝ)/4) ≤ a := by
    have h : a^((3:ℝ)/4) ≤ a^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le ha (by norm_num)
    rwa [Real.rpow_one] at h
  have h1a : a * b^((3:ℝ)/4) ≤ A := by
    rw [← hAdef]
    exact mul_le_mul_of_nonneg_left hb34 (le_of_lt ha0)
  have h2a : b * a^((3:ℝ)/4) ≤ A := by
    rw [← hAdef]
    calc b * a^((3:ℝ)/4) ≤ b * a := mul_le_mul_of_nonneg_left ha34 (le_of_lt hb0)
      _ = a * b := by ring
  constructor
  · calc a * b^((3:ℝ)/4) ≤ A := h1a
      _ ≤ d * B^((1:ℝ)/4) * A^((1:ℝ)/4) := hAle
  · calc b * a^((3:ℝ)/4) ≤ A := h2a
      _ ≤ d * B^((1:ℝ)/4) * A^((1:ℝ)/4) := hAle

/-- The constraint `(RS)^3 ≤ D^4(R+S)` is equivalent to the hypothesis `P ≤ 1`. -/
private lemma p13nl_constraint (D R S : ℕ) (P : ℝ) (hD : 1 ≤ D) (hR : 1 ≤ R) (hS : 1 ≤ S)
    (hP : P = (D:ℝ)^(-(1:ℝ)/2) * ((R:ℝ)+(S:ℝ))^(-(1:ℝ)/8) * ((R:ℝ)*(S:ℝ))^((3:ℝ)/8))
    (hPle : P ≤ 1) :
    ((R:ℝ)*(S:ℝ))^3 ≤ (D:ℝ)^4 * ((R:ℝ)+(S:ℝ)) := by
  have hd0 : (0:ℝ) < (D:ℝ) := by positivity
  have hB0 : (0:ℝ) < (R:ℝ)+(S:ℝ) := by positivity
  have hA0 : (0:ℝ) < (R:ℝ)*(S:ℝ) := by positivity
  rw [hP] at hPle
  have hd1 : (D:ℝ)^((1:ℝ)/2) * (D:ℝ)^(-(1:ℝ)/2) = 1 := by
    rw [← Real.rpow_add hd0, show (1:ℝ)/2 + (-(1:ℝ)/2) = 0 by norm_num, Real.rpow_zero]
  have hB1 : ((R:ℝ)+(S:ℝ))^((1:ℝ)/8) * ((R:ℝ)+(S:ℝ))^(-(1:ℝ)/8) = 1 := by
    rw [← Real.rpow_add hB0, show (1:ℝ)/8 + (-(1:ℝ)/8) = 0 by norm_num, Real.rpow_zero]
  have hstep : ((R:ℝ)*(S:ℝ))^((3:ℝ)/8) ≤ (D:ℝ)^((1:ℝ)/2) * ((R:ℝ)+(S:ℝ))^((1:ℝ)/8) := by
    have h := mul_le_mul_of_nonneg_left hPle
      (show 0 ≤ (D:ℝ)^((1:ℝ)/2) * ((R:ℝ)+(S:ℝ))^((1:ℝ)/8) by positivity)
    have e : (D:ℝ)^((1:ℝ)/2) * ((R:ℝ)+(S:ℝ))^((1:ℝ)/8)
            * ((D:ℝ)^(-(1:ℝ)/2) * ((R:ℝ)+(S:ℝ))^(-(1:ℝ)/8) * ((R:ℝ)*(S:ℝ))^((3:ℝ)/8))
        = ((R:ℝ)*(S:ℝ))^((3:ℝ)/8) := by
      rw [show (D:ℝ)^((1:ℝ)/2) * ((R:ℝ)+(S:ℝ))^((1:ℝ)/8)
              * ((D:ℝ)^(-(1:ℝ)/2) * ((R:ℝ)+(S:ℝ))^(-(1:ℝ)/8) * ((R:ℝ)*(S:ℝ))^((3:ℝ)/8))
            = ((D:ℝ)^((1:ℝ)/2) * (D:ℝ)^(-(1:ℝ)/2))
              * (((R:ℝ)+(S:ℝ))^((1:ℝ)/8) * ((R:ℝ)+(S:ℝ))^(-(1:ℝ)/8))
              * ((R:ℝ)*(S:ℝ))^((3:ℝ)/8) by ring, hd1, hB1]
      ring
    rw [e, mul_one] at h
    exact h
  have hpow : (((R:ℝ)*(S:ℝ))^((3:ℝ)/8))^(8:ℝ)
      ≤ ((D:ℝ)^((1:ℝ)/2) * ((R:ℝ)+(S:ℝ))^((1:ℝ)/8))^(8:ℝ) :=
    Real.rpow_le_rpow (by positivity) hstep (by norm_num)
  have h1 : (((R:ℝ)*(S:ℝ))^((3:ℝ)/8))^(8:ℝ) = ((R:ℝ)*(S:ℝ))^(3:ℝ) := by
    rw [← Real.rpow_mul (le_of_lt hA0), show (3:ℝ)/8 * (8:ℝ) = 3 by norm_num]
  have h2 : ((D:ℝ)^((1:ℝ)/2) * ((R:ℝ)+(S:ℝ))^((1:ℝ)/8))^(8:ℝ)
      = (D:ℝ)^(4:ℝ) * ((R:ℝ)+(S:ℝ)) := by
    rw [Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_mul (le_of_lt hd0), ← Real.rpow_mul (le_of_lt hB0)]
    norm_num
  rw [h1, h2] at hpow
  rwa [show (D:ℝ)^(4:ℝ) = (D:ℝ)^4 by exact Real.rpow_natCast (D:ℝ) 4,
       show ((R:ℝ)*(S:ℝ))^(3:ℝ) = ((R:ℝ)*(S:ℝ))^3 by exact Real.rpow_natCast ((R:ℝ)*(S:ℝ)) 3] at hpow

/-- The master numerical inequality, in the variables `a = R`, `b = S`, `d = D`. -/
private lemma p13nl_master (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (a b d : ℝ), 1 ≤ a → 1 ≤ b → 1 ≤ d →
      (a*b)^3 ≤ d^4 * (a+b) →
      d + d ^ ((1:ℝ)/3) * (a*b) ^ ((2:ℝ)/3) * (Real.log (2 * (a*b)) + 1) ^ (4:ℕ)
        + (d⁻¹ * (a*b) ^ ((3:ℝ)/2) + a * b ^ ((3:ℝ)/4) + b * a ^ ((3:ℝ)/4)) * (a*b) ^ (ε/8)
      ≤ K * (d * (a+b) ^ ((1:ℝ)/4) * (a*b) ^ ((1:ℝ)/4)
             + d ^ (-(1:ℝ)/2) * (a+b) ^ ((1:ℝ)/8) * (a*b) ^ ((9:ℝ)/8)) * (a*b) ^ (ε/2) := by
  obtain ⟨C, hC0, hC⟩ := p13nl_log_four_le ε hε
  refine ⟨4 + (2:ℝ)^(-(7:ℝ)/36) * C, ?_, ?_⟩
  · have h1 : (0:ℝ) < (2:ℝ)^(-(7:ℝ)/36) := Real.rpow_pos_of_pos (by norm_num) _
    nlinarith [hC0, h1]
  · intro a b d ha hb hd hcon
    generalize hAdef : a*b = A
    generalize hBdef : a+b = B
    have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
    have hb0 : 0 < b := lt_of_lt_of_le zero_lt_one hb
    have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd
    have hA0 : 0 < A := by rw [← hAdef]; positivity
    have hB0 : 0 < B := by rw [← hBdef]; positivity
    have hA1 : 1 ≤ A := by rw [← hAdef]; nlinarith
    have hB1 : 1 ≤ B := by rw [← hBdef]; linarith
    have hA2 : (1:ℝ) ≤ A^(ε/2) := Real.one_le_rpow hA1 (by positivity)
    have hAexp8 : A^(ε/8) ≤ A^(ε/2) := Real.rpow_le_rpow_of_exponent_le hA1 (by linarith)
    set T1 : ℝ := d * B^((1:ℝ)/4) * A^((1:ℝ)/4) with hT1
    set T2 : ℝ := d ^ (-(1:ℝ)/2) * B^((1:ℝ)/8) * A^((9:ℝ)/8) with hT2
    have hT1nn : 0 ≤ T1 := by rw [hT1]; positivity
    have hT2nn : 0 ≤ T2 := by rw [hT2]; positivity
    have hthird := p13nl_third_mul_le a b d ha hb hd
    rw [hAdef, hBdef, ← hT1, ← hT2] at hthird
    have hinv := p13nl_inv_mul_le a b d ha hb hd hcon
    rw [hAdef, hBdef, ← hT2] at hinv
    have hq := p13nl_mul_quarter_le a b d ha hb hd hcon
    rw [hAdef, hBdef, ← hT1] at hq
    have h1 : d ≤ (T1+T2) * A^(ε/2) := by
      have hb1 : (1:ℝ) ≤ B^((1:ℝ)/4) := Real.one_le_rpow hB1 (by norm_num)
      have ha1q : (1:ℝ) ≤ A^((1:ℝ)/4) := Real.one_le_rpow hA1 (by norm_num)
      have hT1ge : d ≤ T1 := by
        rw [hT1]
        have hBA : (1:ℝ) ≤ B^((1:ℝ)/4) * A^((1:ℝ)/4) := by nlinarith
        calc d = d * 1 := (mul_one d).symm
          _ ≤ d * (B^((1:ℝ)/4) * A^((1:ℝ)/4)) := mul_le_mul_of_nonneg_left hBA (le_of_lt hd0)
          _ = d * B^((1:ℝ)/4) * A^((1:ℝ)/4) := by ring
      calc d ≤ T1 := hT1ge
        _ ≤ (T1+T2) * A^(ε/2) := by
            have hle : T1 ≤ T1 * A^(ε/2) := by
              nth_rewrite 1 [← mul_one T1]
              exact mul_le_mul_of_nonneg_left hA2 hT1nn
            have hle2 : T1 * A^(ε/2) ≤ (T1+T2)*A^(ε/2) :=
              mul_le_mul_of_nonneg_right (by linarith [hT2nn]) (by positivity)
            linarith
    have h2 : d^((1:ℝ)/3)*A^((2:ℝ)/3)*(Real.log (2*A)+1)^4
        ≤ ((2:ℝ)^(-(7:ℝ)/36)*C) * ((T1+T2)*A^(ε/2)) := by
      have hlogb : (Real.log (2*A)+1)^4 ≤ C * A^(ε/2) := hC A hA1
      calc d^((1:ℝ)/3)*A^((2:ℝ)/3)*(Real.log (2*A)+1)^4
          ≤ d^((1:ℝ)/3)*A^((2:ℝ)/3)*(C*A^(ε/2)) := mul_le_mul_of_nonneg_left hlogb (by positivity)
        _ ≤ ((2:ℝ)^(-(7:ℝ)/36)*(T1+T2))*(C*A^(ε/2)) :=
            mul_le_mul_of_nonneg_right hthird (by positivity)
        _ = ((2:ℝ)^(-(7:ℝ)/36)*C) * ((T1+T2)*A^(ε/2)) := by ring
    have h3 : d⁻¹*A^((3:ℝ)/2)*A^(ε/8) ≤ (T1+T2)*A^(ε/2) :=
      calc d⁻¹*A^((3:ℝ)/2)*A^(ε/8)
          ≤ T2*A^(ε/8) := mul_le_mul_of_nonneg_right hinv (by positivity)
        _ ≤ T2*A^(ε/2) := mul_le_mul_of_nonneg_left hAexp8 (by positivity)
        _ ≤ (T1+T2)*A^(ε/2) := mul_le_mul_of_nonneg_right (by linarith [hT1nn]) (by positivity)
    have h4 : a*b^((3:ℝ)/4)*A^(ε/8) ≤ (T1+T2)*A^(ε/2) :=
      calc a*b^((3:ℝ)/4)*A^(ε/8)
          ≤ T1*A^(ε/8) := mul_le_mul_of_nonneg_right hq.1 (by positivity)
        _ ≤ T1*A^(ε/2) := mul_le_mul_of_nonneg_left hAexp8 (by positivity)
        _ ≤ (T1+T2)*A^(ε/2) := mul_le_mul_of_nonneg_right (by linarith [hT2nn]) (by positivity)
    have h5 : b*a^((3:ℝ)/4)*A^(ε/8) ≤ (T1+T2)*A^(ε/2) :=
      calc b*a^((3:ℝ)/4)*A^(ε/8)
          ≤ T1*A^(ε/8) := mul_le_mul_of_nonneg_right hq.2 (by positivity)
        _ ≤ T1*A^(ε/2) := mul_le_mul_of_nonneg_left hAexp8 (by positivity)
        _ ≤ (T1+T2)*A^(ε/2) := mul_le_mul_of_nonneg_right (by linarith [hT2nn]) (by positivity)
    have hgoal : d + d^((1:ℝ)/3)*A^((2:ℝ)/3)*(Real.log (2*A)+1)^4
        + (d⁻¹*A^((3:ℝ)/2) + a*b^((3:ℝ)/4) + b*a^((3:ℝ)/4))*A^(ε/8)
        ≤ (4 + (2:ℝ)^(-(7:ℝ)/36)*C) * ((T1+T2)*A^(ε/2)) := by
      have hAsum : (d⁻¹*A^((3:ℝ)/2) + a*b^((3:ℝ)/4) + b*a^((3:ℝ)/4))*A^(ε/8)
          = d⁻¹*A^((3:ℝ)/2)*A^(ε/8) + a*b^((3:ℝ)/4)*A^(ε/8) + b*a^((3:ℝ)/4)*A^(ε/8) := by ring
      rw [hAsum]
      linarith [h1, h2, h3, h4, h5]
    linarith [hgoal]

theorem P13_num_large (ε : ℝ) (hε : 0 < ε) : ∃ K : ℝ, 0 < K ∧
    ∀ (D R S : ℕ) (P : ℝ), 1 ≤ D → 1 ≤ R → 1 ≤ S →
      P = (D : ℝ) ^ (-(1:ℝ)/2) * ((R : ℝ) + (S : ℝ)) ^ (-(1:ℝ)/8)
            * ((R : ℝ) * (S : ℝ)) ^ ((3:ℝ)/8) →
      P ≤ 1 → p14T12 D R S (ε/8) ≤ K * p14T13 D R S ε * (((R : ℝ) * (S : ℝ)) ^ (ε/2)) := by
  obtain ⟨K, hK, h⟩ := p13nl_master ε hε
  refine ⟨K, hK, ?_⟩
  intro D R S P hD hR hS hP hPle
  have hcon : ((R:ℝ)*(S:ℝ))^3 ≤ (D:ℝ)^4 * ((R:ℝ)+(S:ℝ)) :=
    p13nl_constraint D R S P hD hR hS hP hPle
  rw [p14T12, p14T13]
  rw [show (2:ℝ)*(R:ℝ)*(S:ℝ) = 2*((R:ℝ)*(S:ℝ)) by ring]
  exact h (R:ℝ) (S:ℝ) (D:ℝ)
    (by exact_mod_cast hR) (by exact_mod_cast hS) (by exact_mod_cast hD) hcon

end

end Work.FIArea4
