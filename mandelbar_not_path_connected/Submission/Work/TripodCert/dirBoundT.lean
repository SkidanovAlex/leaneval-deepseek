/-
# `Work.TripodCert.dirBoundT` — the six base ray directions of the `22/63`-orbit

The `b₂`-tripod certificate of `Submission/Work/TripodCert/` needs, for each of the six angles
`θ j = (T^[j]) (22/63)` of the `22/63`-orbit (`T θ = Int.fract (-2 θ)`, i.e.
`22 → 19 → 25 → 13 → 37 → 52 → 22`), the fact that the *exact* direction `e^{2πiθ_j}` of the
external ray is within `10⁻⁴` of the rational model `qdirT j` emitted by the generator (the
mantissas `dirBaseT` at scale `2 ^ 40`).

This is the `63`-denominator analogue of `Work.SeedCertRay.dir_bound` (the ten base directions of
the `α₁`-orbit); the proof is the same rigorous, kernel-checked numerical computation, in three
steps.  Writing `x = 2πi·(m/63)` (so that `rayDirection (m/63) = exp x`) and
`w = 2π*i·(m/63)` with the 20-digit rational `π* = 3.14159265358979323846`:

* `‖exp x - Etrunc x‖ ≤ 10⁻⁶` — the `24`-term Taylor remainder at `‖x‖ ≤ 53/10` (`m ≤ 52`, so
  `2π·52/63 ≈ 5.186 < 5.3`), via `Work.SeedCertRay.exp_taylor_trunc`;
* `‖Etrunc x - Etrunc w‖ ≤ 10⁻⁵` — the polynomial difference, `‖x - w‖ ≤ 10⁻⁸` by
  `|π - π*| ≤ 10⁻²⁰`, amplified by the derivative bound `250`
  (`Work.SeedCertRay.norm_sum_taylor_diff_le`);
* `‖Etrunc w - qdirT j‖ ≤ 1/50000` — the *rational* part: `Work.SeedCertRay.taylor_split` splits
  the partial sum of `exp (i t)` into its real (even) and imaginary (odd) parts, which are then
  evaluated in exact rational arithmetic by `norm_num` (`dirnumT_re_j`, `dirnumT_im_j`).

The total `10⁻⁶ + 10⁻⁵ + 2·10⁻⁵ < 10⁻⁴` gives the claim.  The angle orbit of `22/63` is
`22, 19, 25, 13, 37, 52` (see `Submission/Work/TripodCert/Basic.lean`), and the mantissas are the
ones of `Submission/Work/TripodCert/Data.lean` (`dirBaseT`).
-/
import Mathlib
import Submission.Work.TripodCert.Data
import Submission.Work.TripodCert.Basic
import Submission.Work.SeedCertRay.dir_bound

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.TripodCert

open Work.SeedCertRay

noncomputable section

/-! ## The rational model of the angle denominator -/

/-- The model exponent `2 π* m / 63` of the angle `m/63`. -/
def tqT (m : ℕ) : ℝ := 2 * (piq : ℝ) * m / 63

/-! ## The abstract step: a rational model direction is close to the true one -/

/-- If the real and imaginary parts of the `24`-term Taylor polynomial of `exp (i tqT m)` are
within `10⁻⁵` of `a` and `b`, then the direction `e^{2πi m/63}` is within `10⁻⁴` of `a + b I`.
(The `63`-denominator analogue of `Work.SeedCertRay.dir_close`.) -/
theorem dir_closeT (m : ℕ) (hm : m ≤ 52) (a b : ℝ)
    (hre : |(∑ k ∈ Finset.range 12, (-((tqT m)^2))^k / (((2*k).factorial : ℕ) : ℝ)) - a|
      ≤ (1 / 100000 : ℝ))
    (him : |tqT m * (∑ k ∈ Finset.range 12, (-((tqT m)^2))^k / (((2*k+1).factorial : ℕ) : ℝ)) - b|
      ≤ (1 / 100000 : ℝ)) :
    ‖Work.Landing.rayDirection ((m : ℝ) / 63) - ((a : ℂ) + (b : ℂ) * Complex.I)‖
      ≤ (1 / 10000 : ℝ) := by
  set x : ℂ := Complex.I * (((2 * Real.pi * (m : ℝ) / 63 : ℝ)) : ℂ) with hxdef
  set w : ℂ := Complex.I * ((tqT m : ℝ) : ℂ) with hwdef
  have hray : Work.Landing.rayDirection ((m : ℝ) / 63) = Complex.exp x := by
    rw [Work.Landing.rayDirection, hxdef]
    congr 1
    push_cast
    ring
  rw [hray]
  have hm52 : (m : ℝ) ≤ 52 := by exact_mod_cast hm
  have hxnorm : ‖x‖ ≤ 53 / 10 := by
    have hnorm : ‖x‖ = 2 * Real.pi * (m : ℝ) / 63 := by
      rw [hxdef, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
    rw [hnorm]
    have h1 : (2 : ℝ) * Real.pi * (m : ℝ) ≤ 2 * 3.14159265358979323847 * 52 :=
      mul_le_mul (mul_le_mul_of_nonneg_left (le_of_lt Real.pi_lt_d20) (by norm_num)) hm52
        (Nat.cast_nonneg m) (by norm_num)
    have hfin : (2 : ℝ) * 3.14159265358979323847 * 52 / 63 ≤ 53 / 10 := by norm_num
    linarith
  have hwnorm : ‖w‖ ≤ 53 / 10 := by
    have hp : (piq : ℝ) = 3.14159265358979323846 := by norm_num [piq]
    have hnorm : ‖w‖ = tqT m := by
      rw [hwdef, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, tqT,
        abs_of_nonneg (by rw [hp]; positivity)]
    rw [hnorm, tqT, hp]
    have h1 : (2 : ℝ) * 3.14159265358979323846 * (m : ℝ)
        ≤ 2 * 3.14159265358979323846 * 52 :=
      mul_le_mul_of_nonneg_left hm52 (by norm_num)
    have hfin : (2 : ℝ) * 3.14159265358979323846 * 52 / 63 ≤ 53 / 10 := by norm_num
    linarith
  have hxw : ‖x - w‖ ≤ 1 / 100000000 := by
    have hsub : x - w = Complex.I * (((2 * Real.pi * (m : ℝ) / 63 - tqT m) : ℝ) : ℂ) := by
      rw [hxdef, hwdef]
      push_cast
      ring
    rw [hsub, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have hsplit : 2 * Real.pi * (m : ℝ) / 63 - tqT m
        = (2 * (m : ℝ) / 63) * (Real.pi - (piq : ℝ)) := by
      rw [tqT]
      ring
    rw [hsplit, abs_mul]
    have hm0 : (0 : ℝ) ≤ 2 * (m : ℝ) / 63 := by positivity
    have hm2 : 2 * (m : ℝ) / 63 ≤ 2 := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 63)]
      linarith
    have hpi : |Real.pi - (piq : ℝ)| ≤ 1 / 10 ^ 20 := by
      rw [abs_sub_comm]
      exact piq_close
    rw [abs_of_nonneg hm0]
    calc (2 * (m : ℝ) / 63) * |Real.pi - (piq : ℝ)|
        ≤ 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ 1 / 100000000 := by norm_num
  have h1 : ‖Complex.exp x - Etrunc x‖ ≤ (1 / 1000000 : ℝ) := exp_taylor_trunc hxnorm
  have h2 : ‖Etrunc x - Etrunc w‖ ≤ (1 / 100000 : ℝ) := by
    have hsum : Etrunc x - Etrunc w
        = ∑ k ∈ Finset.range 24, (x ^ k - w ^ k) / ((k.factorial : ℕ) : ℂ) := by
      simp only [Etrunc, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ => by rw [sub_div]
    rw [hsum]
    calc _ ≤ ‖x - w‖ * 250 := norm_sum_taylor_diff_le hxnorm hwnorm
      _ ≤ 1 / 100000 := by linarith
  have h3 : ‖Etrunc w - ((a : ℂ) + (b : ℂ) * Complex.I)‖ ≤ (1 / 50000 : ℝ) := by
    have hw' : Etrunc w = (∑ k ∈ Finset.range (2*12), (Complex.I * ((tqT m : ℝ) : ℂ))^k
        / ((k.factorial : ℕ) : ℂ)) := by
      simp only [Etrunc, hwdef]
    rw [hw', taylor_split (tqT m) 12]
    exact norm_ofReal_pair_sub_le hre him
  calc ‖Complex.exp x - ((a : ℂ) + (b : ℂ) * Complex.I)‖
      = ‖(Complex.exp x - Etrunc x) + (Etrunc x - Etrunc w)
          + (Etrunc w - ((a : ℂ) + (b : ℂ) * Complex.I))‖ := by ring_nf
    _ ≤ ‖Complex.exp x - Etrunc x‖ + ‖Etrunc x - Etrunc w‖
          + ‖Etrunc w - ((a : ℂ) + (b : ℂ) * Complex.I)‖ := by
        calc ‖(Complex.exp x - Etrunc x) + (Etrunc x - Etrunc w)
              + (Etrunc w - ((a : ℂ) + (b : ℂ) * Complex.I))‖
            ≤ ‖(Complex.exp x - Etrunc x) + (Etrunc x - Etrunc w)‖
              + ‖Etrunc w - ((a : ℂ) + (b : ℂ) * Complex.I)‖ := norm_add_le _ _
          _ ≤ (‖Complex.exp x - Etrunc x‖ + ‖Etrunc x - Etrunc w‖)
              + ‖Etrunc w - ((a : ℂ) + (b : ℂ) * Complex.I)‖ := by
              gcongr
              exact norm_add_le _ _
    _ ≤ 1 / 10000 := by linarith

/-! ## The twelve exact rational evaluations

The even (real) and odd (imaginary) parts of the 24-term Taylor sum at `tqT m`, against the
mantissas of `dirBaseT` (scale `2 ^ 40`), for `m = 22, 19, 25, 13, 37, 52`.  Each is a one-line
`norm_num` call.
-/

/-- Angle `22/63`: the real part of the Taylor sum against the mantissa `-641832955263`. -/
theorem dirnumT_re_0 :
    |(∑ k ∈ Finset.range 12, (-((tqT 22)^2))^k / (((2*k).factorial : ℕ) : ℝ))
      - ((-641832955263 : ℝ)/2^40)| ≤ (1 / 100000 : ℝ) := by
  norm_num [tqT, piq, Finset.sum_range_succ]

/-- Angle `22/63`: the imaginary part of the Taylor sum against the mantissa `892735278318`. -/
theorem dirnumT_im_0 :
    |tqT 22 * (∑ k ∈ Finset.range 12, (-((tqT 22)^2))^k / (((2*k+1).factorial : ℕ) : ℝ))
      - ((892735278318 : ℝ)/2^40)| ≤ (1 / 100000 : ℝ) := by
  norm_num [tqT, piq, Finset.sum_range_succ]

/-- Angle `19/63`: the real part of the Taylor sum against the mantissa `-350179775243`. -/
theorem dirnumT_re_1 :
    |(∑ k ∈ Finset.range 12, (-((tqT 19)^2))^k / (((2*k).factorial : ℕ) : ℝ))
      - ((-350179775243 : ℝ)/2^40)| ≤ (1 / 100000 : ℝ) := by
  norm_num [tqT, piq, Finset.sum_range_succ]

/-- Angle `19/63`: the imaginary part of the Taylor sum against the mantissa `1042257139398`. -/
theorem dirnumT_im_1 :
    |tqT 19 * (∑ k ∈ Finset.range 12, (-((tqT 19)^2))^k / (((2*k+1).factorial : ℕ) : ℝ))
      - ((1042257139398 : ℝ)/2^40)| ≤ (1 / 100000 : ℝ) := by
  norm_num [tqT, piq, Finset.sum_range_succ]

/-- Angle `25/63`: the real part of the Taylor sum against the mantissa `-876456460570`. -/
theorem dirnumT_re_2 :
    |(∑ k ∈ Finset.range 12, (-((tqT 25)^2))^k / (((2*k).factorial : ℕ) : ℝ))
      - ((-876456460570 : ℝ)/2^40)| ≤ (1 / 100000 : ℝ) := by
  norm_num [tqT, piq, Finset.sum_range_succ]

/-- Angle `25/63`: the imaginary part of the Taylor sum against the mantissa `663889970055`. -/
theorem dirnumT_im_2 :
    |tqT 25 * (∑ k ∈ Finset.range 12, (-((tqT 25)^2))^k / (((2*k+1).factorial : ℕ) : ℝ))
      - ((663889970055 : ℝ)/2^40)| ≤ (1 / 100000 : ℝ) := by
  norm_num [tqT, piq, Finset.sum_range_succ]

/-- Angle `13/63`: the real part of the Taylor sum against the mantissa `297792243996`. -/
theorem dirnumT_re_3 :
    |(∑ k ∈ Finset.range 12, (-((tqT 13)^2))^k / (((2*k).factorial : ℕ) : ℝ))
      - ((297792243996 : ℝ)/2^40)| ≤ (1 / 100000 : ℝ) := by
  norm_num [tqT, piq, Finset.sum_range_succ]

/-- Angle `13/63`: the imaginary part of the Taylor sum against the mantissa `1058416552701`. -/
theorem dirnumT_im_3 :
    |tqT 13 * (∑ k ∈ Finset.range 12, (-((tqT 13)^2))^k / (((2*k+1).factorial : ℕ) : ℝ))
      - ((1058416552701 : ℝ)/2^40)| ≤ (1 / 100000 : ℝ) := by
  norm_num [tqT, piq, Finset.sum_range_succ]

/-- Angle `37/63`: the real part of the Taylor sum against the mantissa `-938203246230`. -/
theorem dirnumT_re_4 :
    |(∑ k ∈ Finset.range 12, (-((tqT 37)^2))^k / (((2*k).factorial : ℕ) : ℝ))
      - ((-938203246230 : ℝ)/2^40)| ≤ (1 / 100000 : ℝ) := by
  norm_num [tqT, piq, Finset.sum_range_succ]

/-- Angle `37/63`: the imaginary part of the Taylor sum against the mantissa `-573324069248`. -/
theorem dirnumT_im_4 :
    |tqT 37 * (∑ k ∈ Finset.range 12, (-((tqT 37)^2))^k / (((2*k+1).factorial : ℕ) : ℝ))
      - ((-573324069248 : ℝ)/2^40)| ≤ (1 / 100000 : ℝ) := by
  norm_num [tqT, piq, Finset.sum_range_succ]

/-- Angle `52/63`: the real part of the Taylor sum against the mantissa `501608922475`. -/
theorem dirnumT_re_5 :
    |(∑ k ∈ Finset.range 12, (-((tqT 52)^2))^k / (((2*k).factorial : ℕ) : ℝ))
      - ((501608922475 : ℝ)/2^40)| ≤ (1 / 100000 : ℝ) := by
  norm_num [tqT, piq, Finset.sum_range_succ]

/-- Angle `52/63`: the imaginary part of the Taylor sum against the mantissa `-978424401018`. -/
theorem dirnumT_im_5 :
    |tqT 52 * (∑ k ∈ Finset.range 12, (-((tqT 52)^2))^k / (((2*k+1).factorial : ℕ) : ℝ))
      - ((-978424401018 : ℝ)/2^40)| ≤ (1 / 100000 : ℝ) := by
  norm_num [tqT, piq, Finset.sum_range_succ]

/-! ## The six directions
-/

/-- The direction of the `j = 0` ray: `e^{2πi·22/63}` against `qdirT 0`. -/
theorem dirjT_0 : ‖Work.Landing.rayDirection (theta 0) - qdirT 0‖ ≤ (1 / 10000 : ℝ) := by
  have hth : theta 0 = (22 : ℝ)/63 := theta_zero
  have hq : qdirT 0 = (((-641832955263 : ℝ)/2^40 : ℝ) : ℂ)
      + (((892735278318 : ℝ)/2^40 : ℝ) : ℂ) * Complex.I := by
    simp only [qdirT, Q, MS, gI, dirBaseT]
    norm_num
  rw [hth, hq]
  exact dir_closeT 22 (by norm_num) _ _ dirnumT_re_0 dirnumT_im_0

/-- The direction of the `j = 1` ray: `e^{2πi·19/63}` against `qdirT 1`. -/
theorem dirjT_1 : ‖Work.Landing.rayDirection (theta 1) - qdirT 1‖ ≤ (1 / 10000 : ℝ) := by
  have hth : theta 1 = (19 : ℝ)/63 := theta_one
  have hq : qdirT 1 = (((-350179775243 : ℝ)/2^40 : ℝ) : ℂ)
      + (((1042257139398 : ℝ)/2^40 : ℝ) : ℂ) * Complex.I := by
    simp only [qdirT, Q, MS, gI, dirBaseT]
    norm_num
  rw [hth, hq]
  exact dir_closeT 19 (by norm_num) _ _ dirnumT_re_1 dirnumT_im_1

/-- The direction of the `j = 2` ray: `e^{2πi·25/63}` against `qdirT 2`. -/
theorem dirjT_2 : ‖Work.Landing.rayDirection (theta 2) - qdirT 2‖ ≤ (1 / 10000 : ℝ) := by
  have hth : theta 2 = (25 : ℝ)/63 := theta_two
  have hq : qdirT 2 = (((-876456460570 : ℝ)/2^40 : ℝ) : ℂ)
      + (((663889970055 : ℝ)/2^40 : ℝ) : ℂ) * Complex.I := by
    simp only [qdirT, Q, MS, gI, dirBaseT]
    norm_num
  rw [hth, hq]
  exact dir_closeT 25 (by norm_num) _ _ dirnumT_re_2 dirnumT_im_2

/-- The direction of the `j = 3` ray: `e^{2πi·13/63}` against `qdirT 3`. -/
theorem dirjT_3 : ‖Work.Landing.rayDirection (theta 3) - qdirT 3‖ ≤ (1 / 10000 : ℝ) := by
  have hth : theta 3 = (13 : ℝ)/63 := theta_three
  have hq : qdirT 3 = (((297792243996 : ℝ)/2^40 : ℝ) : ℂ)
      + (((1058416552701 : ℝ)/2^40 : ℝ) : ℂ) * Complex.I := by
    simp only [qdirT, Q, MS, gI, dirBaseT]
    norm_num
  rw [hth, hq]
  exact dir_closeT 13 (by norm_num) _ _ dirnumT_re_3 dirnumT_im_3

/-- The direction of the `j = 4` ray: `e^{2πi·37/63}` against `qdirT 4`. -/
theorem dirjT_4 : ‖Work.Landing.rayDirection (theta 4) - qdirT 4‖ ≤ (1 / 10000 : ℝ) := by
  have hth : theta 4 = (37 : ℝ)/63 := theta_four
  have hq : qdirT 4 = (((-938203246230 : ℝ)/2^40 : ℝ) : ℂ)
      + (((-573324069248 : ℝ)/2^40 : ℝ) : ℂ) * Complex.I := by
    simp only [qdirT, Q, MS, gI, dirBaseT]
    norm_num
  rw [hth, hq]
  exact dir_closeT 37 (by norm_num) _ _ dirnumT_re_4 dirnumT_im_4

/-- The direction of the `j = 5` ray: `e^{2πi·52/63}` against `qdirT 5`. -/
theorem dirjT_5 : ‖Work.Landing.rayDirection (theta 5) - qdirT 5‖ ≤ (1 / 10000 : ℝ) := by
  have hth : theta 5 = (52 : ℝ)/63 := theta_five
  have hq : qdirT 5 = (((501608922475 : ℝ)/2^40 : ℝ) : ℂ)
      + (((-978424401018 : ℝ)/2^40 : ℝ) : ℂ) * Complex.I := by
    simp only [qdirT, Q, MS, gI, dirBaseT]
    norm_num
  rw [hth, hq]
  exact dir_closeT 52 (by norm_num) _ _ dirnumT_re_5 dirnumT_im_5

/-! ## The target -/

theorem dirBoundT (j : ℕ) (hj : j < 6) :
    ‖Work.Landing.rayDirection (Work.TripodCert.theta j) - Work.TripodCert.qdirT j‖ ≤ 1 / 10000 := by
  have h : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · exact dirjT_0
  · exact dirjT_1
  · exact dirjT_2
  · exact dirjT_3
  · exact dirjT_4
  · exact dirjT_5

end

end Work.TripodCert
