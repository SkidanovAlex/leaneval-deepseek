/-
# `Work.SeedCertRay.dir_bound` — the ten base ray directions of the `α₁`-orbit

The chain certificate of `Submission/Work/SeedCertRay/` needs, for each of the ten angles
`θ j = (T^[j]) α₁` of the `α₁`-orbit (`T θ = Int.fract (-2 θ)`, `α₁ = 371/1023`), the fact that
the *exact* direction `e^{2πiθ_j}` of the external ray is within `10⁻⁴` of the rational model
`qdirC j` emitted by the generator (the mantissas `dirBase` at scale `2 ^ 40`).

The proof is a rigorous, kernel-checked numerical computation, in three steps.  Writing
`x = 2πi·(m/1023)` (so that `rayDirection (m/1023) = exp x`) and `w = 2π*i·(m/1023)` with the
20-digit rational `π* = 3.14159265358979323846`:

* `‖exp x - Etrunc x‖ ≤ 10⁻⁶` — the `24`-term Taylor remainder at `‖x‖ ≤ 53/10`
  (`Complex.exp_bound'`, `exp_taylor_trunc`);
* `‖Etrunc x - Etrunc w‖ ≤ 10⁻⁵` — the polynomial difference, `‖x - w‖ ≤ 10⁻⁸` by
  `|π - π*| ≤ 10⁻²⁰`, amplified by the derivative bound `250`
  (`norm_sum_taylor_diff_le`);
* `‖Etrunc w - qdirC j‖ ≤ 1/50000` — the *rational* part: `taylor_split` splits the partial sum
  of `exp (i t)` into its real (even) and imaginary (odd) parts, which are then evaluated in
  exact rational arithmetic by `norm_num` (`dirnum_re_j`, `dirnum_im_j`).

The total `10⁻⁶ + 10⁻⁵ + 2·10⁻⁵ < 10⁻⁴` gives the claim.  The numbers, and the fact that
`qdirC j` is the mantissa pair `(dirBase[2j], dirBase[2j+1])`, are the ones of
`Submission/Work/SeedCertRay/DataAll.lean` (`NOTES.md` §5: the angle orbit of `α₁` is
`371, 281, 461, 101, 821, 404, 215, 593, 860, 326`).
-/
import Mathlib
import Submission.Work.SeedCertRay.Q
import Submission.Work.SeedCertRay.taylor_split
import Submission.Work.SeedCertRay.norm_sum_taylor_diff_le

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCertRay

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

noncomputable section

/-! ## The rational model of `π` -/

/-- The rational approximation `π* = 3.14159265358979323846` of `π`, correct to `10⁻²⁰`. -/
def piq : ℚ := 314159265358979323846 / 10 ^ 20

/-- The model exponent `2 π* m / 1023` of the angle `m/1023`. -/
def tq (m : ℕ) : ℝ := 2 * (piq : ℝ) * m / 1023

/-- The `24`-term Taylor polynomial of `exp` at `z`. -/
def Etrunc (z : ℂ) : ℂ := ∑ k ∈ Finset.range 24, z ^ k / ((k.factorial : ℕ) : ℂ)

/-- `π*` is within `10⁻²⁰` of `π` (`Real.pi_gt_d20`, `Real.pi_lt_d20`). -/
lemma piq_close : |(piq : ℝ) - Real.pi| ≤ 1 / 10 ^ 20 := by
  have hp : (piq : ℝ) = 3.14159265358979323846 := by norm_num [piq]
  rw [abs_le, hp]
  constructor
  · linarith [Real.pi_lt_d20]
  · linarith [Real.pi_gt_d20]

/-! ## Two elementary estimates for complex numbers of the form `u + v I` -/

/-- `‖u + v I‖ ≤ |u| + |v|`. -/
lemma norm_ofReal_add_mul_I_le (u v : ℝ) :
    ‖((u : ℂ) + (v : ℂ) * Complex.I)‖ ≤ |u| + |v| := by
  calc ‖((u : ℂ) + (v : ℂ) * Complex.I)‖
      ≤ ‖((u : ℂ))‖ + ‖((v : ℂ) * Complex.I)‖ := norm_add_le _ _
    _ = |u| + |v| := by simp

/-- A two-sided form of `norm_ofReal_add_mul_I_le`. -/
lemma norm_ofReal_pair_sub_le {u v a b : ℝ}
    (h1 : |u - a| ≤ (1 / 100000 : ℝ)) (h2 : |v - b| ≤ (1 / 100000 : ℝ)) :
    ‖((u : ℂ) + (v : ℂ) * Complex.I) - ((a : ℂ) + (b : ℂ) * Complex.I)‖ ≤ (1 / 50000 : ℝ) := by
  have h : ((u : ℂ) + (v : ℂ) * Complex.I) - ((a : ℂ) + (b : ℂ) * Complex.I)
      = (((u - a : ℝ)) : ℂ) + (((v - b : ℝ)) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h]
  calc ‖(((u - a : ℝ)) : ℂ) + (((v - b : ℝ)) : ℂ) * Complex.I‖ ≤ |u - a| + |v - b| :=
        norm_ofReal_add_mul_I_le _ _
    _ ≤ 1 / 50000 := by linarith

/-! ## The Taylor remainder -/

/-- The `24`-term Taylor polynomial of `exp` is `10⁻⁶`-close to `exp` on the disc `‖z‖ ≤ 53/10`. -/
theorem exp_taylor_trunc {z : ℂ} (hz : ‖z‖ ≤ 53 / 10) :
    ‖Complex.exp z - Etrunc z‖ ≤ (1 / 1000000 : ℝ) := by
  have harg : ‖z‖ / (25 : ℝ) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 25)]
    linarith
  have h := Complex.exp_bound' (x := z) (n := 24) harg
  have hE : (∑ m ∈ Finset.range 24, z ^ m / ((m.factorial : ℕ) : ℂ)) = Etrunc z := by
    simp [Etrunc]
  rw [hE] at h
  refine h.trans ?_
  have hnum : ‖z‖ ^ 24 / ((24 : ℕ).factorial : ℝ) * 2 ≤ (1 / 1000000 : ℝ) := by
    calc ‖z‖ ^ 24 / ((24 : ℕ).factorial : ℝ) * 2
        ≤ (53 / 10) ^ 24 / ((24 : ℕ).factorial : ℝ) * 2 := by gcongr
      _ ≤ (1 / 1000000 : ℝ) := by norm_num
  exact hnum

/-! ## The abstract step: a rational model direction is close to the true one -/

/-- If the real and imaginary parts of the `24`-term Taylor polynomial of `exp (i tq m)` are
within `10⁻⁵` of `a` and `b`, then the direction `e^{2πi m/1023}` is within `10⁻⁴` of
`a + b I`. -/
theorem dir_close (m : ℕ) (hm : m ≤ 860) (a b : ℝ)
    (hre : |(∑ k ∈ Finset.range 12, (-((tq m)^2))^k / (((2*k).factorial : ℕ) : ℝ)) - a|
      ≤ (1 / 100000 : ℝ))
    (him : |tq m * (∑ k ∈ Finset.range 12, (-((tq m)^2))^k / (((2*k+1).factorial : ℕ) : ℝ)) - b|
      ≤ (1 / 100000 : ℝ)) :
    ‖Work.Landing.rayDirection ((m : ℝ) / 1023) - ((a : ℂ) + (b : ℂ) * Complex.I)‖
      ≤ (1 / 10000 : ℝ) := by
  set x : ℂ := Complex.I * (((2 * Real.pi * (m : ℝ) / 1023 : ℝ)) : ℂ) with hxdef
  set w : ℂ := Complex.I * ((tq m : ℝ) : ℂ) with hwdef
  have hray : Work.Landing.rayDirection ((m : ℝ) / 1023) = Complex.exp x := by
    rw [Work.Landing.rayDirection, hxdef]
    congr 1
    push_cast
    ring
  rw [hray]
  have hm860 : (m : ℝ) ≤ 860 := by exact_mod_cast hm
  have hxnorm : ‖x‖ ≤ 53 / 10 := by
    have hnorm : ‖x‖ = 2 * Real.pi * (m : ℝ) / 1023 := by
      rw [hxdef, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
    rw [hnorm]
    have h1 : (2 : ℝ) * Real.pi * (m : ℝ) ≤ 2 * 3.14159265358979323847 * 860 :=
      mul_le_mul (mul_le_mul_of_nonneg_left (le_of_lt Real.pi_lt_d20) (by norm_num))
        hm860 (Nat.cast_nonneg m) (by norm_num)
    have hfin : (2 : ℝ) * 3.14159265358979323847 * 860 / 1023 ≤ 53 / 10 := by norm_num
    linarith
  have hwnorm : ‖w‖ ≤ 53 / 10 := by
    have hp : (piq : ℝ) = 3.14159265358979323846 := by norm_num [piq]
    have hnorm : ‖w‖ = tq m := by
      rw [hwdef, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, tq,
        abs_of_nonneg (by rw [hp]; positivity)]
    rw [hnorm, tq, hp]
    have h1 : (2 : ℝ) * 3.14159265358979323846 * (m : ℝ)
        ≤ 2 * 3.14159265358979323846 * 860 :=
      mul_le_mul_of_nonneg_left hm860 (by norm_num)
    have hfin : (2 : ℝ) * 3.14159265358979323846 * 860 / 1023 ≤ 53 / 10 := by norm_num
    linarith
  have hxw : ‖x - w‖ ≤ 1 / 100000000 := by
    have hsub : x - w = Complex.I * (((2 * Real.pi * (m : ℝ) / 1023 - tq m) : ℝ) : ℂ) := by
      rw [hxdef, hwdef]
      push_cast
      ring
    rw [hsub, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have hsplit : 2 * Real.pi * (m : ℝ) / 1023 - tq m
        = (2 * (m : ℝ) / 1023) * (Real.pi - (piq : ℝ)) := by
      rw [tq]
      ring
    rw [hsplit, abs_mul]
    have hm0 : (0 : ℝ) ≤ 2 * (m : ℝ) / 1023 := by positivity
    have hm2 : 2 * (m : ℝ) / 1023 ≤ 2 := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 1023)]
      linarith
    have hpi : |Real.pi - (piq : ℝ)| ≤ 1 / 10 ^ 20 := by
      rw [abs_sub_comm]
      exact piq_close
    rw [abs_of_nonneg hm0]
    calc (2 * (m : ℝ) / 1023) * |Real.pi - (piq : ℝ)|
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
    have hw' : Etrunc w = (∑ k ∈ Finset.range (2*12), (Complex.I * ((tq m : ℝ) : ℂ))^k
        / ((k.factorial : ℕ) : ℂ)) := by
      simp only [Etrunc, hwdef]
    rw [hw', taylor_split (tq m) 12]
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

/-! ## The twenty exact rational evaluations

The even (real) and odd (imaginary) parts of the 24-term Taylor sum at `tq m`, against the
mantissas of `dirBase` (scale `2 ^ 40`).  All twenty are one-line `norm_num` calls.
-/

/-- `j = 0`: the real part of the Taylor sum at `tq 371` against the mantissa `-714909780021`. -/
lemma dirnum_re_0 :
    |(∑ k ∈ Finset.range 12, (-((tq 371)^2))^k / (((2*k).factorial : ℕ) : ℝ)) - ((-714909780021 : ℝ)/2^40)|
      ≤ (1 / 100000 : ℝ) := by
  norm_num [tq, piq, Finset.sum_range_succ]

/-- `j = 0`: the imaginary part of the Taylor sum at `tq 371` against the mantissa `835362092775`. -/
lemma dirnum_im_0 :
    |tq 371 * (∑ k ∈ Finset.range 12, (-((tq 371)^2))^k / (((2*k+1).factorial : ℕ) : ℝ))
        - ((835362092775 : ℝ)/2^40)| ≤ (1 / 100000 : ℝ) := by
  norm_num [tq, piq, Finset.sum_range_succ]

/-- `j = 1`: the real part of the Taylor sum at `tq 281` against the mantissa `-169833431278`. -/
lemma dirnum_re_1 :
    |(∑ k ∈ Finset.range 12, (-((tq 281)^2))^k / (((2*k).factorial : ℕ) : ℝ)) - ((-169833431278 : ℝ)/2^40)|
      ≤ (1 / 100000 : ℝ) := by
  norm_num [tq, piq, Finset.sum_range_succ]

/-- `j = 1`: the imaginary part of the Taylor sum at `tq 281` against the mantissa `1086315987747`. -/
lemma dirnum_im_1 :
    |tq 281 * (∑ k ∈ Finset.range 12, (-((tq 281)^2))^k / (((2*k+1).factorial : ℕ) : ℝ))
        - ((1086315987747 : ℝ)/2^40)| ≤ (1 / 100000 : ℝ) := by
  norm_num [tq, piq, Finset.sum_range_succ]

/-- `j = 2`: the real part of the Taylor sum at `tq 461` against the mantissa `-1047045799037`. -/
lemma dirnum_re_2 :
    |(∑ k ∈ Finset.range 12, (-((tq 461)^2))^k / (((2*k).factorial : ℕ) : ℝ)) - ((-1047045799037 : ℝ)/2^40)|
      ≤ (1 / 100000 : ℝ) := by
  norm_num [tq, piq, Finset.sum_range_succ]

/-- `j = 2`: the imaginary part of the Taylor sum at `tq 461` against the mantissa `335590396664`. -/
lemma dirnum_im_2 :
    |tq 461 * (∑ k ∈ Finset.range 12, (-((tq 461)^2))^k / (((2*k+1).factorial : ℕ) : ℝ))
        - ((335590396664 : ℝ)/2^40)| ≤ (1 / 100000 : ℝ) := by
  norm_num [tq, piq, Finset.sum_range_succ]

/-- `j = 3`: the real part of the Taylor sum at `tq 101` against the mantissa `894655377986`. -/
lemma dirnum_re_3 :
    |(∑ k ∈ Finset.range 12, (-((tq 101)^2))^k / (((2*k).factorial : ℕ) : ℝ)) - ((894655377986 : ℝ)/2^40)|
      ≤ (1 / 100000 : ℝ) := by
  norm_num [tq, piq, Finset.sum_range_succ]

/-- `j = 3`: the imaginary part of the Taylor sum at `tq 101` against the mantissa `639153795463`. -/
lemma dirnum_im_3 :
    |tq 101 * (∑ k ∈ Finset.range 12, (-((tq 101)^2))^k / (((2*k+1).factorial : ℕ) : ℝ))
        - ((639153795463 : ℝ)/2^40)| ≤ (1 / 100000 : ℝ) := by
  norm_num [tq, piq, Finset.sum_range_succ]

/-- `j = 4`: the real part of the Taylor sum at `tq 821` against the mantissa `356422489044`. -/
lemma dirnum_re_4 :
    |(∑ k ∈ Finset.range 12, (-((tq 821)^2))^k / (((2*k).factorial : ℕ) : ℝ)) - ((356422489044 : ℝ)/2^40)|
      ≤ (1 / 100000 : ℝ) := by
  norm_num [tq, piq, Finset.sum_range_succ]

/-- `j = 4`: the imaginary part of the Taylor sum at `tq 821` against the mantissa `-1040138850787`. -/
lemma dirnum_im_4 :
    |tq 821 * (∑ k ∈ Finset.range 12, (-((tq 821)^2))^k / (((2*k+1).factorial : ℕ) : ℝ))
        - ((-1040138850787 : ℝ)/2^40)| ≤ (1 / 100000 : ℝ) := by
  norm_num [tq, piq, Finset.sum_range_succ]

/-- `j = 5`: the real part of the Taylor sum at `tq 404` against the mantissa `-868432687839`. -/
lemma dirnum_re_5 :
    |(∑ k ∈ Finset.range 12, (-((tq 404)^2))^k / (((2*k).factorial : ℕ) : ℝ)) - ((-868432687839 : ℝ)/2^40)|
      ≤ (1 / 100000 : ℝ) := by
  norm_num [tq, piq, Finset.sum_range_succ]

/-- `j = 5`: the imaginary part of the Taylor sum at `tq 404` against the mantissa `674351900941`. -/
lemma dirnum_im_5 :
    |tq 404 * (∑ k ∈ Finset.range 12, (-((tq 404)^2))^k / (((2*k+1).factorial : ℕ) : ℝ))
        - ((674351900941 : ℝ)/2^40)| ≤ (1 / 100000 : ℝ) := by
  norm_num [tq, piq, Finset.sum_range_succ]

/-- `j = 6`: the real part of the Taylor sum at `tq 215` against the mantissa `272325311930`. -/
lemma dirnum_re_6 :
    |(∑ k ∈ Finset.range 12, (-((tq 215)^2))^k / (((2*k).factorial : ℕ) : ℝ)) - ((272325311930 : ℝ)/2^40)|
      ≤ (1 / 100000 : ℝ) := by
  norm_num [tq, piq, Finset.sum_range_succ]

/-- `j = 6`: the imaginary part of the Taylor sum at `tq 215` against the mantissa `1065253370841`. -/
lemma dirnum_im_6 :
    |tq 215 * (∑ k ∈ Finset.range 12, (-((tq 215)^2))^k / (((2*k+1).factorial : ℕ) : ℝ))
        - ((1065253370841 : ℝ)/2^40)| ≤ (1 / 100000 : ℝ) := by
  norm_num [tq, piq, Finset.sum_range_succ]

/-- `j = 7`: the real part of the Taylor sum at `tq 593` against the mantissa `-964613417246`. -/
lemma dirnum_re_7 :
    |(∑ k ∈ Finset.range 12, (-((tq 593)^2))^k / (((2*k).factorial : ℕ) : ℝ)) - ((-964613417246 : ℝ)/2^40)|
      ≤ (1 / 100000 : ℝ) := by
  norm_num [tq, piq, Finset.sum_range_succ]

/-- `j = 7`: the imaginary part of the Taylor sum at `tq 593` against the mantissa `-527680561388`. -/
lemma dirnum_im_7 :
    |tq 593 * (∑ k ∈ Finset.range 12, (-((tq 593)^2))^k / (((2*k+1).factorial : ℕ) : ℝ))
        - ((-527680561388 : ℝ)/2^40)| ≤ (1 / 100000 : ℝ) := by
  norm_num [tq, piq, Finset.sum_range_succ]

/-- `j = 8`: the real part of the Taylor sum at `tq 860` against the mantissa `593019894827`. -/
lemma dirnum_re_8 :
    |(∑ k ∈ Finset.range 12, (-((tq 860)^2))^k / (((2*k).factorial : ℕ) : ℝ)) - ((593019894827 : ℝ)/2^40)|
      ≤ (1 / 100000 : ℝ) := by
  norm_num [tq, piq, Finset.sum_range_succ]

/-- `j = 8`: the imaginary part of the Taylor sum at `tq 860` against the mantissa `-925879702726`. -/
lemma dirnum_im_8 :
    |tq 860 * (∑ k ∈ Finset.range 12, (-((tq 860)^2))^k / (((2*k+1).factorial : ℕ) : ℝ))
        - ((-925879702726 : ℝ)/2^40)| ≤ (1 / 100000 : ℝ) := by
  norm_num [tq, piq, Finset.sum_range_succ]

/-- `j = 9`: the real part of the Taylor sum at `tq 326` against the mantissa `-459822902721`. -/
lemma dirnum_re_9 :
    |(∑ k ∈ Finset.range 12, (-((tq 326)^2))^k / (((2*k).factorial : ℕ) : ℝ)) - ((-459822902721 : ℝ)/2^40)|
      ≤ (1 / 100000 : ℝ) := by
  norm_num [tq, piq, Finset.sum_range_succ]

/-- `j = 9`: the imaginary part of the Taylor sum at `tq 326` against the mantissa `998743569531`. -/
lemma dirnum_im_9 :
    |tq 326 * (∑ k ∈ Finset.range 12, (-((tq 326)^2))^k / (((2*k+1).factorial : ℕ) : ℝ))
        - ((998743569531 : ℝ)/2^40)| ≤ (1 / 100000 : ℝ) := by
  norm_num [tq, piq, Finset.sum_range_succ]

/-! ## The ten directions
-/

/-- The direction of the `j = 0` ray: `e^{2πi·371/1023}` against `qdirC 0`. -/
theorem dirj_0 :
    ‖Work.Landing.rayDirection ((Work.EL.T^[0]) Work.EL.alpha1) - qdirC 0‖ ≤ (1 / 10000 : ℝ) := by
  have hth : (Work.EL.T^[0]) Work.EL.alpha1 = (371 : ℝ)/1023 := by
    simp [Function.iterate_zero, Work.EL.alpha1]
  have hq : qdirC 0 = (((-714909780021 : ℝ)/2^40 : ℝ) : ℂ) + (((835362092775 : ℝ)/2^40 : ℝ) : ℂ) * Complex.I := by
    simp only [qdirC, Q, MS, gI, dirBase]
    norm_num
  rw [hth, hq]
  exact dir_close 371 (by norm_num) ((-714909780021 : ℝ)/2^40) ((835362092775 : ℝ)/2^40) dirnum_re_0 dirnum_im_0

/-- The direction of the `j = 1` ray: `e^{2πi·281/1023}` against `qdirC 1`. -/
theorem dirj_1 :
    ‖Work.Landing.rayDirection ((Work.EL.T^[1]) Work.EL.alpha1) - qdirC 1‖ ≤ (1 / 10000 : ℝ) := by
  have hth : (Work.EL.T^[1]) Work.EL.alpha1 = (281 : ℝ)/1023 := by
    norm_num [Function.iterate_succ_apply', Work.EL.T, Work.EL.alpha1, Int.fract]
  have hq : qdirC 1 = (((-169833431278 : ℝ)/2^40 : ℝ) : ℂ) + (((1086315987747 : ℝ)/2^40 : ℝ) : ℂ) * Complex.I := by
    simp only [qdirC, Q, MS, gI, dirBase]
    norm_num
  rw [hth, hq]
  exact dir_close 281 (by norm_num) ((-169833431278 : ℝ)/2^40) ((1086315987747 : ℝ)/2^40) dirnum_re_1 dirnum_im_1

/-- The direction of the `j = 2` ray: `e^{2πi·461/1023}` against `qdirC 2`. -/
theorem dirj_2 :
    ‖Work.Landing.rayDirection ((Work.EL.T^[2]) Work.EL.alpha1) - qdirC 2‖ ≤ (1 / 10000 : ℝ) := by
  have hth : (Work.EL.T^[2]) Work.EL.alpha1 = (461 : ℝ)/1023 := by
    norm_num [Function.iterate_succ_apply', Work.EL.T, Work.EL.alpha1, Int.fract]
  have hq : qdirC 2 = (((-1047045799037 : ℝ)/2^40 : ℝ) : ℂ) + (((335590396664 : ℝ)/2^40 : ℝ) : ℂ) * Complex.I := by
    simp only [qdirC, Q, MS, gI, dirBase]
    norm_num
  rw [hth, hq]
  exact dir_close 461 (by norm_num) ((-1047045799037 : ℝ)/2^40) ((335590396664 : ℝ)/2^40) dirnum_re_2 dirnum_im_2

/-- The direction of the `j = 3` ray: `e^{2πi·101/1023}` against `qdirC 3`. -/
theorem dirj_3 :
    ‖Work.Landing.rayDirection ((Work.EL.T^[3]) Work.EL.alpha1) - qdirC 3‖ ≤ (1 / 10000 : ℝ) := by
  have hth : (Work.EL.T^[3]) Work.EL.alpha1 = (101 : ℝ)/1023 := by
    norm_num [Function.iterate_succ_apply', Work.EL.T, Work.EL.alpha1, Int.fract]
  have hq : qdirC 3 = (((894655377986 : ℝ)/2^40 : ℝ) : ℂ) + (((639153795463 : ℝ)/2^40 : ℝ) : ℂ) * Complex.I := by
    simp only [qdirC, Q, MS, gI, dirBase]
    norm_num
  rw [hth, hq]
  exact dir_close 101 (by norm_num) ((894655377986 : ℝ)/2^40) ((639153795463 : ℝ)/2^40) dirnum_re_3 dirnum_im_3

/-- The direction of the `j = 4` ray: `e^{2πi·821/1023}` against `qdirC 4`. -/
theorem dirj_4 :
    ‖Work.Landing.rayDirection ((Work.EL.T^[4]) Work.EL.alpha1) - qdirC 4‖ ≤ (1 / 10000 : ℝ) := by
  have hth : (Work.EL.T^[4]) Work.EL.alpha1 = (821 : ℝ)/1023 := by
    norm_num [Function.iterate_succ_apply', Work.EL.T, Work.EL.alpha1, Int.fract]
  have hq : qdirC 4 = (((356422489044 : ℝ)/2^40 : ℝ) : ℂ) + (((-1040138850787 : ℝ)/2^40 : ℝ) : ℂ) * Complex.I := by
    simp only [qdirC, Q, MS, gI, dirBase]
    norm_num
  rw [hth, hq]
  exact dir_close 821 (by norm_num) ((356422489044 : ℝ)/2^40) ((-1040138850787 : ℝ)/2^40) dirnum_re_4 dirnum_im_4

/-- The direction of the `j = 5` ray: `e^{2πi·404/1023}` against `qdirC 5`. -/
theorem dirj_5 :
    ‖Work.Landing.rayDirection ((Work.EL.T^[5]) Work.EL.alpha1) - qdirC 5‖ ≤ (1 / 10000 : ℝ) := by
  have hth : (Work.EL.T^[5]) Work.EL.alpha1 = (404 : ℝ)/1023 := by
    norm_num [Function.iterate_succ_apply', Work.EL.T, Work.EL.alpha1, Int.fract]
  have hq : qdirC 5 = (((-868432687839 : ℝ)/2^40 : ℝ) : ℂ) + (((674351900941 : ℝ)/2^40 : ℝ) : ℂ) * Complex.I := by
    simp only [qdirC, Q, MS, gI, dirBase]
    norm_num
  rw [hth, hq]
  exact dir_close 404 (by norm_num) ((-868432687839 : ℝ)/2^40) ((674351900941 : ℝ)/2^40) dirnum_re_5 dirnum_im_5

/-- The direction of the `j = 6` ray: `e^{2πi·215/1023}` against `qdirC 6`. -/
theorem dirj_6 :
    ‖Work.Landing.rayDirection ((Work.EL.T^[6]) Work.EL.alpha1) - qdirC 6‖ ≤ (1 / 10000 : ℝ) := by
  have hth : (Work.EL.T^[6]) Work.EL.alpha1 = (215 : ℝ)/1023 := by
    norm_num [Function.iterate_succ_apply', Work.EL.T, Work.EL.alpha1, Int.fract]
  have hq : qdirC 6 = (((272325311930 : ℝ)/2^40 : ℝ) : ℂ) + (((1065253370841 : ℝ)/2^40 : ℝ) : ℂ) * Complex.I := by
    simp only [qdirC, Q, MS, gI, dirBase]
    norm_num
  rw [hth, hq]
  exact dir_close 215 (by norm_num) ((272325311930 : ℝ)/2^40) ((1065253370841 : ℝ)/2^40) dirnum_re_6 dirnum_im_6

/-- The direction of the `j = 7` ray: `e^{2πi·593/1023}` against `qdirC 7`. -/
theorem dirj_7 :
    ‖Work.Landing.rayDirection ((Work.EL.T^[7]) Work.EL.alpha1) - qdirC 7‖ ≤ (1 / 10000 : ℝ) := by
  have hth : (Work.EL.T^[7]) Work.EL.alpha1 = (593 : ℝ)/1023 := by
    norm_num [Function.iterate_succ_apply', Work.EL.T, Work.EL.alpha1, Int.fract]
  have hq : qdirC 7 = (((-964613417246 : ℝ)/2^40 : ℝ) : ℂ) + (((-527680561388 : ℝ)/2^40 : ℝ) : ℂ) * Complex.I := by
    simp only [qdirC, Q, MS, gI, dirBase]
    norm_num
  rw [hth, hq]
  exact dir_close 593 (by norm_num) ((-964613417246 : ℝ)/2^40) ((-527680561388 : ℝ)/2^40) dirnum_re_7 dirnum_im_7

/-- The direction of the `j = 8` ray: `e^{2πi·860/1023}` against `qdirC 8`. -/
theorem dirj_8 :
    ‖Work.Landing.rayDirection ((Work.EL.T^[8]) Work.EL.alpha1) - qdirC 8‖ ≤ (1 / 10000 : ℝ) := by
  have hth : (Work.EL.T^[8]) Work.EL.alpha1 = (860 : ℝ)/1023 := by
    norm_num [Function.iterate_succ_apply', Work.EL.T, Work.EL.alpha1, Int.fract]
  have hq : qdirC 8 = (((593019894827 : ℝ)/2^40 : ℝ) : ℂ) + (((-925879702726 : ℝ)/2^40 : ℝ) : ℂ) * Complex.I := by
    simp only [qdirC, Q, MS, gI, dirBase]
    norm_num
  rw [hth, hq]
  exact dir_close 860 (by norm_num) ((593019894827 : ℝ)/2^40) ((-925879702726 : ℝ)/2^40) dirnum_re_8 dirnum_im_8

/-- The direction of the `j = 9` ray: `e^{2πi·326/1023}` against `qdirC 9`. -/
theorem dirj_9 :
    ‖Work.Landing.rayDirection ((Work.EL.T^[9]) Work.EL.alpha1) - qdirC 9‖ ≤ (1 / 10000 : ℝ) := by
  have hth : (Work.EL.T^[9]) Work.EL.alpha1 = (326 : ℝ)/1023 := by
    norm_num [Function.iterate_succ_apply', Work.EL.T, Work.EL.alpha1, Int.fract]
  have hq : qdirC 9 = (((-459822902721 : ℝ)/2^40 : ℝ) : ℂ) + (((998743569531 : ℝ)/2^40 : ℝ) : ℂ) * Complex.I := by
    simp only [qdirC, Q, MS, gI, dirBase]
    norm_num
  rw [hth, hq]
  exact dir_close 326 (by norm_num) ((-459822902721 : ℝ)/2^40) ((998743569531 : ℝ)/2^40) dirnum_re_9 dirnum_im_9

/-! ## The target -/

theorem dir_bound (j : ℕ) (hj : j < 10) :
    ‖Work.Landing.rayDirection ((Work.EL.T^[j]) Work.EL.alpha1) - Work.SeedCertRay.qdirC j‖ ≤ 1 / 10000 := by
  have h : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by
    omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact dirj_0
  · exact dirj_1
  · exact dirj_2
  · exact dirj_3
  · exact dirj_4
  · exact dirj_5
  · exact dirj_6
  · exact dirj_7
  · exact dirj_8
  · exact dirj_9

end

end Work.SeedCertRay
