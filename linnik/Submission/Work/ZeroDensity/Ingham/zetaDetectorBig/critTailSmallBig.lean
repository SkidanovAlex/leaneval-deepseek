import Mathlib
import Submission.Work.ZeroDensity.Ingham.Defs
import Submission.Work.ZeroDensity.Ingham.zetaDetectorDefs
import Submission.Work.ZeroDensity.Ingham.setIntegral_Ioi_add_const
import Submission.Work.ZeroDensity.Ingham.MK_critical_bound
import Submission.Work.ZeroDensity.Ingham.integrableOn_one_add_pow_mul_exp_neg
import Submission.Work.ZeroDensity.Ingham.zetaDetectorBig.gammaShim
import Submission.Work.Sieve.zeta_critical_line_bound

/-!
# The critical-line tails of the wide (un-smoothed) zero detector are small

This file proves `Work.ZeroDensity.Ingham.zetaDetectorBig.critTailSmallBig`: in the *wide* range
`A ≥ 6`, `T ≥ 2`, `1 ≤ K ≤ T⁴`, `1 ≤ Y ≤ (A T)²`, and for every `ρ` with `1/2 ≤ Re ρ ≤ 1`,
`(log (A T))² ≤ |Im ρ| ≤ T`, the sum of the two tails (`v > A log (A T)` and
`v ≤ -A log (A T)`) of the critical-line integral of `critIntegrand K ρ` is at most
`Y^{Re ρ - 1/2} · π/10`.

Everything is explicit: `x := log (A T) ≥ 5` (from `(log (A T))² ≤ T ≤ e^x/6` and `6x² ≤ e^x`),
so `H := A x ≥ 30`; on `|v| > H` the three factors are bounded by
* `Work.Sieve.zeta_critical_line_aux`: `‖ζ(1/2 + iτ)‖ ≤ 9 (1+|τ|)^{1/2}`,
* `MK_critical_bound`: `‖M_K(1/2 + it)‖ ≤ 2√K ≤ 2T²` (as `K ≤ T⁴`),
* the sharp vertical `Γ` bound `‖Γ(u+iv)‖ ≤ 64 (1+|v|)^{-1/2} e^{-(π/2)|v|}` for
  `-1/2 ≤ u ≤ 0` and `|v| ≥ 5/2` (shift `Γ(w) = Γ(w+1)/w` plus the strip bound of
  `Commons.Analysis.SpecialFunctions.Gamma.log_Gamma_vertical_le`),

and the remaining exponential tail integral and the final numerical comparison are elementary.
-/

namespace Work.ZeroDensity.Ingham.zetaDetectorBig

open scoped Classical BigOperators
open MeasureTheory

set_option maxHeartbeats 1000000

/-! ## Elementary arithmetic: `log (A T) ≥ 5` -/

/-- `e^5 < 150` (Taylor remainder `Real.exp_bound` at `x = 1`, `n = 8`). -/
private lemma exp5_lt_150_big : Real.exp 5 < 150 := by
  have hb := Real.exp_bound (x := (1 : ℝ)) (by norm_num) (n := 8) (by norm_num)
  have hsum : (∑ m ∈ Finset.range 8, (1 : ℝ) ^ m / (m.factorial : ℝ)) = (13700 : ℝ) / 5040 := by
    norm_num [Finset.sum_range_succ]
  rw [hsum] at hb
  have he : Real.exp 1 ≤ 2.7182819 := by
    have h2 : |Real.exp 1 - 13700 / 5040| ≤ 9 / 322560 := by
      convert hb using 1 <;> norm_num
    have := (abs_le.mp h2).2
    linarith
  have h5 : Real.exp 5 = (Real.exp 1) ^ 5 := by
    simpa using Real.exp_nsmul (1 : ℝ) 5
  rw [h5]
  have h6 : (Real.exp 1) ^ 5 ≤ (2.7182819 : ℝ) ^ 5 :=
    pow_le_pow_left₀ (Real.exp_pos 1).le he 5
  have h7 : (2.7182819 : ℝ) ^ 5 < 150 := by norm_num
  linarith

/-- `e^x/x²` is decreasing on `[2,5]`, with endpoint value `e^5/25`. -/
private lemma exp_div_sq_le_five_big {x : ℝ} (h2 : 2 ≤ x) (h5 : x ≤ 5) :
    Real.exp x / x ^ 2 ≤ Real.exp 5 / 25 := by
  have hx0 : 0 < x := by linarith
  have hlog : Real.log (Real.exp x / x ^ 2) = x - 2 * Real.log x := by
    rw [Real.log_div (Real.exp_ne_zero x) (by positivity), Real.log_exp, Real.log_pow]
    push_cast
    ring
  have hlog5 : Real.log (Real.exp 5 / 25) = 5 - 2 * Real.log 5 := by
    rw [Real.log_div (Real.exp_ne_zero 5) (by norm_num), Real.log_exp]
    rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  rw [← Real.log_le_log_iff (div_pos (Real.exp_pos x) (by positivity))
      (div_pos (Real.exp_pos 5) (by norm_num)), hlog, hlog5]
  have hsplit : Real.log x = Real.log 5 + Real.log (x / 5) := by
    rw [← Real.log_mul (by norm_num : (5 : ℝ) ≠ 0) (by positivity : x / 5 ≠ 0)]
    congr 1
    field_simp
  have hge : 1 - 5 / x ≤ Real.log (x / 5) := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < x / 5 by positivity)
    have hinv : (x / 5)⁻¹ = 5 / x := by field_simp
    rwa [hinv] at h
  have hx5' : x - 5 ≤ 2 - 10 / x := by
    have h : (x - 5) * x ≤ (2 - 10 / x) * x := by
      have e : (2 - 10 / x) * x = 2 * x - 10 := by field_simp
      rw [e]
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x - 2) (by linarith : (0 : ℝ) ≤ 5 - x)]
    exact le_of_mul_le_mul_right h hx0
  have hge2 : 2 - 10 / x ≤ 2 * Real.log (x / 5) := by
    have h := mul_le_mul_of_nonneg_left hge (by norm_num : (0 : ℝ) ≤ 2)
    have e : (2 : ℝ) * (1 - 5 / x) = 2 - 10 / x := by field_simp; ring
    linarith [h, e.le, e.ge]
  rw [hsplit]
  nlinarith [hx5', hge2]

/-- Under `A ≥ 6`, `T ≥ 2` and `(log (A T))² ≤ T` one has `log (A T) ≥ 5`. -/
private lemma logAT_ge_five_big {A T : ℝ} (hA : 6 ≤ A) (hT : 2 ≤ T)
    (h : (Real.log (A * T)) ^ 2 ≤ T) : 5 ≤ Real.log (A * T) := by
  have hApos : 0 < A := by linarith
  have hTpos : 0 < T := by linarith
  have hAT1 : 1 < A * T := by nlinarith
  set x : ℝ := Real.log (A * T) with hxdef
  have hx2 : 2 ≤ x := by
    have h12 : Real.log 12 ≤ x := by
      rw [hxdef]
      exact Real.log_le_log (by norm_num) (by nlinarith)
    have h2log : (2 : ℝ) ≤ Real.log 12 := by
      have h := Real.log_two_gt_d9
      have hlog6 : Real.log 6 = Real.log 2 + Real.log 3 := by
        rw [show (6 : ℝ) = 2 * 3 by norm_num,
          Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)]
      have h3 : (1 : ℝ) < Real.log 3 := by
        rw [Real.lt_log_iff_exp_lt (by norm_num)]
        linarith [Real.exp_one_lt_three]
      rw [show (12 : ℝ) = 6 * 2 by norm_num,
        Real.log_mul (by norm_num : (6 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0), hlog6]
      linarith
    linarith
  have hTle : T ≤ Real.exp x / 6 := by
    have h1 : Real.log T = x - Real.log A := by
      rw [hxdef, Real.log_mul (ne_of_gt hApos) (ne_of_gt hTpos)]
      ring
    have h2 : Real.log 6 ≤ Real.log A := Real.log_le_log (by norm_num) hA
    have h3 : Real.exp (Real.log T) ≤ Real.exp (x - Real.log 6) := by
      apply Real.exp_le_exp.mpr
      rw [h1]
      linarith
    rw [Real.exp_log hTpos, Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 6)] at h3
    linarith
  have h6 : 6 * x ^ 2 ≤ Real.exp x := by
    have hx2T : x ^ 2 ≤ T := by rw [hxdef]; exact h
    nlinarith
  by_contra hlt
  push_neg at hlt
  have hratio : Real.exp x / x ^ 2 ≤ Real.exp 5 / 25 := exp_div_sq_le_five_big hx2 (le_of_lt hlt)
  have hx2pos : 0 < x ^ 2 := by positivity
  have h6' : 6 ≤ Real.exp x / x ^ 2 := by
    rw [le_div_iff₀ hx2pos]
    linarith
  have h4 : Real.exp 5 / 25 < 6 := by
    have := exp5_lt_150_big
    linarith
  linarith

/-! ## The exponential tail integral -/

/-- `s ↦ s^n e^{-s}` is integrable on `(0,∞)` for `n ≤ 4`, by domination from
`(1+s)^4 e^{-s}`. -/
private lemma integrableOn_pow_mul_exp_neg_one (n : ℕ) (hn : n ≤ 4) :
    IntegrableOn (fun s : ℝ => s ^ n * Real.exp (-s)) (Set.Ioi 0) := by
  have hdom : IntegrableOn (fun s : ℝ => (1 + s) ^ 4 * Real.exp (-s)) (Set.Ioi 0) := by
    have h := integrableOn_one_add_pow_mul_exp_neg 4 (b := 1) (by norm_num)
    simpa only [one_mul] using h
  refine MeasureTheory.Integrable.mono' hdom ?_ ?_
  · exact (by fun_prop : Continuous fun s : ℝ => s ^ n * Real.exp (-s)).aestronglyMeasurable
  · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
    have hs0 : 0 ≤ s := le_of_lt hs
    have hle : s ^ n ≤ (1 + s) ^ 4 := by
      calc s ^ n ≤ (1 + s) ^ n := pow_le_pow_left₀ hs0 (by linarith) n
        _ ≤ (1 + s) ^ 4 := pow_le_pow_right₀ (by linarith) hn
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hs0 n) (Real.exp_pos _).le)]
    exact mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le

/-- `∫_{s>0} s^n e^{-s} = n!`. -/
private lemma integral_Ioi_pow_mul_exp_neg_one (n : ℕ) :
    (∫ s in Set.Ioi 0, s ^ n * Real.exp (-s)) = (n.factorial : ℝ) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (n : ℝ) + 1) (r := 1)
    (by positivity) (by norm_num : (0 : ℝ) < 1)
  have hcongr : (∫ t in Set.Ioi 0, t ^ (((n : ℝ) + 1) - 1) * Real.exp (-(1 * t)))
      = ∫ t in Set.Ioi 0, t ^ n * Real.exp (-t) := by
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro t _
    simp only [show ((n : ℝ) + 1) - 1 = (n : ℝ) by ring, Real.rpow_natCast, one_mul]
  rw [hcongr] at h
  rw [h]
  simp [Real.Gamma_nat_eq_factorial]

/-- `∫_{s>0} (1+s)^4 e^{-s} = 1 + 4·1! + 6·2! + 4·3! + 4! = 65`. -/
private lemma integral_Ioi_oneAdd4_exp_neg_one :
    (∫ s in Set.Ioi 0, (1 + s) ^ 4 * Real.exp (-s)) = 65 := by
  have hpoly : ∀ s : ℝ, (1 + s) ^ 4
      = ∑ k ∈ Finset.range 5, (Nat.choose 4 k : ℝ) * s ^ k := by
    intro s
    norm_num [Finset.sum_range_succ, Nat.choose]
    ring
  have hfun : (fun s : ℝ => (1 + s) ^ 4 * Real.exp (-s))
      = fun s : ℝ => ∑ k ∈ Finset.range 5,
          (Nat.choose 4 k : ℝ) * (s ^ k * Real.exp (-s)) := by
    funext s
    rw [hpoly s, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [hfun, MeasureTheory.integral_finsetSum]
  · simp_rw [MeasureTheory.integral_const_mul, integral_Ioi_pow_mul_exp_neg_one]
    norm_num [Nat.factorial, Finset.sum_range_succ, Nat.choose]
  · intro k hk
    have hk4 : k ≤ 4 := by have := Finset.mem_range.mp hk; omega
    exact (integrableOn_pow_mul_exp_neg_one k hk4).const_mul _

/-- `∫_{s>0} (1+s)^4 e^{-(π/2)s} ≤ 65`: compare with `e^{-s}` (as `1 ≤ π/2`). -/
private lemma integral_Ioi_oneAdd4_exp_neg_pi_half_le :
    (∫ s in Set.Ioi 0, (1 + s) ^ 4 * Real.exp (-(Real.pi / 2) * s)) ≤ 65 := by
  have hmono : (∫ s in Set.Ioi 0, (1 + s) ^ 4 * Real.exp (-(Real.pi / 2) * s))
      ≤ (∫ s in Set.Ioi 0, (1 + s) ^ 4 * Real.exp (-s)) := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
    · filter_upwards with s
      exact mul_nonneg (by positivity) (Real.exp_nonneg _)
    · have h : IntegrableOn (fun s : ℝ => (1 + s) ^ 4 * Real.exp (-(1 * s))) (Set.Ioi 0) :=
        integrableOn_one_add_pow_mul_exp_neg 4 (b := 1) (by norm_num)
      have h' : IntegrableOn (fun s : ℝ => (1 + s) ^ 4 * Real.exp (-s)) (Set.Ioi 0) := by
        simpa only [one_mul] using h
      exact h'
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
      have hs0 : 0 ≤ s := le_of_lt hs
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [Real.exp_le_exp]
      nlinarith [Real.pi_gt_three, hs0]
  rw [integral_Ioi_oneAdd4_exp_neg_one] at hmono
  exact hmono

/-- **Tail bound.**  If `f ≥ 0` on `(H,∞)` and `f v ≤ C (3+T+v)^4 e^{-(π/2)v}` there, then
`∫_{v>H} f ≤ C e^{-(π/2)H} (3+T+H)^4 · 65`. -/
private lemma tailIntegralHalfBoundBig (T H : ℝ) (hT : 0 ≤ T) (hH : 1 ≤ H) (C : ℝ)
    (hC : 0 ≤ C) (f : ℝ → ℝ) (hf0 : ∀ v ∈ Set.Ioi H, 0 ≤ f v)
    (hfe : ∀ v ∈ Set.Ioi H, f v ≤ C * ((3 + T + v) ^ 4 * Real.exp (-(Real.pi / 2) * v))) :
    (∫ v in Set.Ioi H, f v) ≤ C * (Real.exp (-(Real.pi / 2) * H) * (3 + T + H) ^ 4 * 65) := by
  rw [setIntegral_Ioi_add_const f H]
  set K : ℝ := C * (Real.exp (-(Real.pi / 2) * H) * (3 + T + H) ^ 4) with hKdef
  have hK : 0 ≤ K := by
    rw [hKdef]
    exact mul_nonneg hC (mul_nonneg (Real.exp_nonneg _) (pow_nonneg (by linarith) 4))
  have hdom : ∀ s ∈ Set.Ioi (0 : ℝ),
      f (s + H) ≤ K * ((1 + s) ^ 4 * Real.exp (-(Real.pi / 2) * s)) := by
    intro s hs
    have hs0 : 0 ≤ s := le_of_lt hs
    have h1 : f (s + H) ≤ C * ((3 + T + (s + H)) ^ 4 * Real.exp (-(Real.pi / 2) * (s + H))) :=
      hfe (s + H) (by simpa using hs)
    have h2 : (3 + T + (s + H)) ^ 4 ≤ ((3 + T + H) * (1 + s)) ^ 4 := by
      refine pow_le_pow_left₀ (by linarith) ?_ 4
      nlinarith
    have h3 : ((3 + T + H) * (1 + s)) ^ 4
        = (3 + T + H) ^ 4 * (1 + s) ^ 4 := mul_pow _ _ _
    have h4 : Real.exp (-(Real.pi / 2) * (s + H))
        = Real.exp (-(Real.pi / 2) * H) * Real.exp (-(Real.pi / 2) * s) := by
      rw [show -(Real.pi / 2) * (s + H) = (-(Real.pi / 2) * H) + (-(Real.pi / 2) * s) by ring,
        Real.exp_add]
    have hmid : (3 + T + (s + H)) ^ 4 * Real.exp (-(Real.pi / 2) * (s + H))
        ≤ ((3 + T + H) * (1 + s)) ^ 4
          * (Real.exp (-(Real.pi / 2) * H) * Real.exp (-(Real.pi / 2) * s)) := by
      rw [h4]
      exact mul_le_mul_of_nonneg_right h2 (by positivity)
    calc f (s + H)
        ≤ C * ((3 + T + (s + H)) ^ 4 * Real.exp (-(Real.pi / 2) * (s + H))) := h1
      _ ≤ C * (((3 + T + H) * (1 + s)) ^ 4
            * (Real.exp (-(Real.pi / 2) * H) * Real.exp (-(Real.pi / 2) * s))) :=
          mul_le_mul_of_nonneg_left hmid hC
      _ = K * ((1 + s) ^ 4 * Real.exp (-(Real.pi / 2) * s)) := by
          rw [h3, hKdef]; ring
  have hInt : (∫ s in Set.Ioi 0, f (s + H))
      ≤ ∫ s in Set.Ioi 0, K * ((1 + s) ^ 4 * Real.exp (-(Real.pi / 2) * s)) := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
      exact hf0 (s + H) (by simpa using hs)
    · have h : IntegrableOn (fun s : ℝ => (1 + s) ^ 4 * Real.exp (-(Real.pi / 2 * s)))
          (Set.Ioi 0) :=
        integrableOn_one_add_pow_mul_exp_neg 4 (by positivity)
      have h' : IntegrableOn (fun s : ℝ => (1 + s) ^ 4 * Real.exp (-(Real.pi / 2) * s))
          (Set.Ioi 0) := by
        simpa only [neg_mul] using h
      exact h'.const_mul K
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
      exact hdom s hs
  have hval : (∫ s in Set.Ioi 0, K * ((1 + s) ^ 4 * Real.exp (-(Real.pi / 2) * s)))
      ≤ K * 65 := by
    rw [MeasureTheory.integral_const_mul]
    exact mul_le_mul_of_nonneg_left integral_Ioi_oneAdd4_exp_neg_pi_half_le hK
  calc (∫ s in Set.Ioi 0, f (s + H))
      ≤ ∫ s in Set.Ioi 0, K * ((1 + s) ^ 4 * Real.exp (-(Real.pi / 2) * s)) := hInt
    _ ≤ K * 65 := hval
    _ = C * (Real.exp (-(Real.pi / 2) * H) * (3 + T + H) ^ 4 * 65) := by rw [hKdef]; ring

/-! ## The vertical `Γ` bound on the strip `-1/2 ≤ Re ≤ 0` -/

/-- Sharp vertical upper bound for `Γ` on the strip `1/2 ≤ Re ≤ 2`, explicit constant. -/
private lemma gamma_strip_sharp (u v : ℝ) (h1 : 1 / 2 ≤ u) (h2 : u ≤ 2) :
    ‖Complex.Gamma ((u : ℂ) + (v : ℂ) * Complex.I)‖ ≤
      8 * Real.exp 1 * (1 + |v|) ^ (u - 1 / 2) * Real.exp (-(Real.pi / 2) * |v|) := by
  have hlog := Commons.Analysis.SpecialFunctions.Gamma.log_Gamma_vertical_le u v h1 (by linarith)
  have hpos : 0 < ‖Complex.Gamma ((u : ℂ) + (v : ℂ) * Complex.I)‖ := by
    rw [norm_pos_iff]
    apply Complex.Gamma_ne_zero_of_re_pos
    simp [Complex.add_re, Complex.mul_re]
    linarith
  have hv1 : (0 : ℝ) < 1 + |v| := by positivity
  have hle : 4 + 2 * |v| ≤ 4 * (1 + |v|) := by
    have := abs_nonneg v
    linarith
  have hexp : Real.exp ((u - 1 / 2) * Real.log (4 + 2 * |v|))
      = (4 + 2 * |v|) ^ (u - 1 / 2) := by
    rw [Real.rpow_def_of_pos (by positivity)]
    ring_nf
  have h4 : (4 + 2 * |v|) ^ (u - 1 / 2) ≤ (4 * (1 + |v|)) ^ (u - 1 / 2) :=
    Real.rpow_le_rpow (by positivity) hle (by linarith)
  have h5 : (4 * (1 + |v|)) ^ (u - 1 / 2)
      = 4 ^ (u - 1 / 2) * (1 + |v|) ^ (u - 1 / 2) :=
    Real.mul_rpow (by norm_num) (by positivity)
  have h6 : (4 : ℝ) ^ (u - 1 / 2) ≤ 8 := by
    calc (4 : ℝ) ^ (u - 1 / 2) ≤ (4 : ℝ) ^ ((3 : ℝ) / 2) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 8 := by norm_num
  have hpow_nn : 0 ≤ (1 + |v|) ^ (u - 1 / 2) := Real.rpow_nonneg (by positivity) _
  have h1' : Real.exp ((u - 1 / 2) * Real.log (4 + 2 * |v|) + 1)
      ≤ 8 * Real.exp 1 * (1 + |v|) ^ (u - 1 / 2) := by
    have h7 : (4 + 2 * |v|) ^ (u - 1 / 2) ≤ 8 * (1 + |v|) ^ (u - 1 / 2) := by
      calc (4 + 2 * |v|) ^ (u - 1 / 2) ≤ (4 * (1 + |v|)) ^ (u - 1 / 2) := h4
        _ = 4 ^ (u - 1 / 2) * (1 + |v|) ^ (u - 1 / 2) := h5
        _ ≤ 8 * (1 + |v|) ^ (u - 1 / 2) := mul_le_mul_of_nonneg_right h6 hpow_nn
    calc Real.exp ((u - 1 / 2) * Real.log (4 + 2 * |v|) + 1)
        = Real.exp ((u - 1 / 2) * Real.log (4 + 2 * |v|)) * Real.exp 1 := Real.exp_add _ _
      _ = (4 + 2 * |v|) ^ (u - 1 / 2) * Real.exp 1 := by rw [hexp]
      _ ≤ (8 * (1 + |v|) ^ (u - 1 / 2)) * Real.exp 1 :=
          mul_le_mul_of_nonneg_right h7 (Real.exp_pos 1).le
      _ = 8 * Real.exp 1 * (1 + |v|) ^ (u - 1 / 2) := by ring
  rw [← Real.exp_log hpos]
  refine le_trans (Real.exp_le_exp.mpr hlog) ?_
  rw [show (u - 1 / 2) * Real.log (4 + 2 * |v|) + 1 - (Real.pi / 2) * |v|
      = ((u - 1 / 2) * Real.log (4 + 2 * |v|) + 1) + (-((Real.pi / 2) * |v|)) by ring,
    Real.exp_add]
  calc Real.exp ((u - 1 / 2) * Real.log (4 + 2 * |v|) + 1)
        * Real.exp (-((Real.pi / 2) * |v|))
      ≤ (8 * Real.exp 1 * (1 + |v|) ^ (u - 1 / 2)) * Real.exp (-((Real.pi / 2) * |v|)) :=
        mul_le_mul_of_nonneg_right h1' (Real.exp_nonneg _)
    _ = 8 * Real.exp 1 * (1 + |v|) ^ (u - 1 / 2) * Real.exp (-(Real.pi / 2) * |v|) := by ring

/-- **The `Γ` factor.**  For `-1/2 ≤ u ≤ 0` and `|v| ≥ 5/2`,
`‖Γ(u+iv)‖ ≤ 64 (1+|v|)^{-1/2} e^{-(π/2)|v|}`. -/
private lemma gammaHalfNegBoundBig (u v : ℝ) (h1 : -(1 / 2 : ℝ) ≤ u) (h2 : u ≤ 0)
    (hv : 5 / 2 ≤ |v|) :
    ‖Complex.Gamma ((u : ℂ) + (v : ℂ) * Complex.I)‖ ≤
      64 * (1 + |v|) ^ (-(1 / 2) : ℝ) * Real.exp (-(Real.pi / 2) * |v|) := by
  set w : ℂ := (u : ℂ) + (v : ℂ) * Complex.I with hw
  have hvre : w.re = u := by simp [hw]
  have hvim : w.im = v := by simp [hw]
  have hvn : (1 : ℝ) ≤ |v| := by linarith
  have hvpos : 0 < |v| := by linarith
  have hwn : (5 : ℝ) / 2 ≤ ‖w‖ := by
    calc (5 : ℝ) / 2 ≤ |v| := hv
      _ = |w.im| := by rw [hvim]
      _ ≤ ‖w‖ := Complex.abs_im_le_norm w
  have hwne : w ≠ 0 := by
    intro h0
    rw [h0] at hwn
    simp at hwn
    linarith
  have hwnpos : 0 < ‖w‖ := by linarith
  have hshift : Complex.Gamma (w + 1) = w * Complex.Gamma w := Complex.Gamma_add_one w hwne
  have hnorm : ‖Complex.Gamma w‖ = ‖Complex.Gamma (w + 1)‖ / ‖w‖ := by
    rw [hshift, norm_mul]
    field_simp
  have hw1 : w + 1 = (((u + 1 : ℝ)) : ℂ) + (v : ℂ) * Complex.I := by
    rw [hw]; push_cast; ring
  have hstrip := gamma_strip_sharp (u + 1) v (by linarith) (by linarith)
  have hstep : ‖Complex.Gamma (w + 1)‖
      ≤ 8 * Real.exp 1 * (1 + |v|) ^ ((1 : ℝ) / 2) * Real.exp (-(Real.pi / 2) * |v|) := by
    rw [hw1]
    refine le_trans hstrip ?_
    have hb : (1 : ℝ) ≤ 1 + |v| := by linarith
    have hexp : (u + 1) - 1 / 2 ≤ (1 : ℝ) / 2 := by linarith
    have hmono := Real.rpow_le_rpow_of_exponent_le hb hexp
    have hrest : 0 ≤ Real.exp (-(Real.pi / 2) * |v|) := Real.exp_nonneg _
    have h8 : 0 ≤ 8 * Real.exp 1 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hmono h8
    exact mul_le_mul_of_nonneg_right hmul hrest
  have hvle : |v| ≤ ‖w‖ := by
    rw [← hvim]
    exact Complex.abs_im_le_norm w
  have hmain : ‖Complex.Gamma (w + 1)‖ / ‖w‖
      ≤ (8 * Real.exp 1 * (1 + |v|) ^ ((1 : ℝ) / 2) * Real.exp (-(Real.pi / 2) * |v|)) / |v| := by
    have h1 : ‖Complex.Gamma (w + 1)‖ / ‖w‖
        ≤ (8 * Real.exp 1 * (1 + |v|) ^ ((1 : ℝ) / 2)
            * Real.exp (-(Real.pi / 2) * |v|)) / ‖w‖ :=
      div_le_div_of_nonneg_right hstep (norm_nonneg _)
    have h2 : (8 * Real.exp 1 * (1 + |v|) ^ ((1 : ℝ) / 2)
            * Real.exp (-(Real.pi / 2) * |v|)) / ‖w‖
        ≤ (8 * Real.exp 1 * (1 + |v|) ^ ((1 : ℝ) / 2)
            * Real.exp (-(Real.pi / 2) * |v|)) / |v| :=
      div_le_div_of_nonneg_left (by positivity) hvpos hvle
    exact le_trans h1 h2
  have harm : (8 * Real.exp 1 * (1 + |v|) ^ ((1 : ℝ) / 2)
        * Real.exp (-(Real.pi / 2) * |v|)) / |v|
      ≤ 64 * (1 + |v|) ^ (-(1 / 2) : ℝ) * Real.exp (-(Real.pi / 2) * |v|) := by
    have hb : (0 : ℝ) < 1 + |v| := by linarith
    have hdecay_pos : 0 < (1 + |v|) ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos hb _
    have hexppos : 0 < Real.exp (-(Real.pi / 2) * |v|) := Real.exp_pos _
    have hkey : (1 + |v|) ^ ((1 : ℝ) / 2) / |v| ≤ 2 * (1 + |v|) ^ (-(1 / 2) : ℝ) := by
      rw [div_le_iff₀ hvpos]
      have hrewrite : (1 + |v|) ^ ((1 : ℝ) / 2)
          = (1 + |v|) * (1 + |v|) ^ (-(1 / 2) : ℝ) := by
        conv_lhs => rw [show ((1 : ℝ) / 2) = (-(1 / 2) : ℝ) + 1 by norm_num]
        rw [Real.rpow_add hb, Real.rpow_one]
        ring
      rw [hrewrite]
      calc (1 + |v|) * (1 + |v|) ^ (-(1 / 2) : ℝ)
          ≤ (2 * |v|) * (1 + |v|) ^ (-(1 / 2) : ℝ) := by
            refine mul_le_mul_of_nonneg_right ?_ hdecay_pos.le
            linarith
        _ = 2 * (1 + |v|) ^ (-(1 / 2) : ℝ) * |v| := by ring
    have hconst : 8 * Real.exp 1 * 2 ≤ 64 := by
      have := Real.exp_one_lt_three
      linarith
    have h1' : 8 * Real.exp 1 * ((1 + |v|) ^ ((1 : ℝ) / 2) / |v|)
        ≤ 64 * (1 + |v|) ^ (-(1 / 2) : ℝ) := by
      have h8 : 0 ≤ 8 * Real.exp 1 := by positivity
      calc 8 * Real.exp 1 * ((1 + |v|) ^ ((1 : ℝ) / 2) / |v|)
          ≤ 8 * Real.exp 1 * (2 * (1 + |v|) ^ (-(1 / 2) : ℝ)) :=
            mul_le_mul_of_nonneg_left hkey h8
        _ = (8 * Real.exp 1 * 2) * (1 + |v|) ^ (-(1 / 2) : ℝ) := by ring
        _ ≤ 64 * (1 + |v|) ^ (-(1 / 2) : ℝ) :=
            mul_le_mul_of_nonneg_right hconst hdecay_pos.le
    have hfac : (8 * Real.exp 1 * (1 + |v|) ^ ((1 : ℝ) / 2) * Real.exp (-(Real.pi / 2) * |v|)) / |v|
        = (8 * Real.exp 1 * ((1 + |v|) ^ ((1 : ℝ) / 2) / |v|))
          * Real.exp (-(Real.pi / 2) * |v|) := by
      rw [div_eq_mul_inv]
      ring
    rw [hfac]
    have h2' : (8 * Real.exp 1 * ((1 + |v|) ^ ((1 : ℝ) / 2) / |v|))
        * Real.exp (-(Real.pi / 2) * |v|)
        ≤ 64 * (1 + |v|) ^ (-(1 / 2) : ℝ) * Real.exp (-(Real.pi / 2) * |v|) :=
      le_trans (mul_le_mul_of_nonneg_right h1' hexppos.le) (le_of_eq (by ring))
    exact h2'
  rw [hnorm]
  exact le_trans hmain harm

/-! ## The pointwise bound on the critical-line integrand -/

private lemma critIntegrand_nonneg (K : ℕ) (ρ : ℂ) (v : ℝ) : 0 ≤ critIntegrand K ρ v :=
  mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)

/-- Pointwise bound for the critical-line integrand in the wide range, at height `w` with
`|w| ≥ 5/2`. -/
private lemma critIntegrand_abs_le (K : ℕ) (T : ℝ) (ρ : ℂ) (w : ℝ) (hKT : (K : ℝ) ≤ T ^ 4)
    (hT0 : 0 ≤ T) (hρ1 : 1 / 2 ≤ ρ.re) (hρ2 : ρ.re ≤ 1) (hγ : |ρ.im| ≤ T) (hw : 5 / 2 ≤ |w|) :
    critIntegrand K ρ w ≤ 1152 * T ^ 2 * ((3 + T + |w|) ^ 4 * Real.exp (-(Real.pi / 2) * |w|)) := by
  -- the ζ factor
  have hz : ‖riemannZeta (((1 : ℂ) / 2) + (ρ.im : ℂ) * Complex.I + (w : ℂ) * Complex.I)‖
      ≤ 9 * (3 + T + |w|) ^ 4 := by
    have harg : ((1 : ℂ) / 2) + (ρ.im : ℂ) * Complex.I + (w : ℂ) * Complex.I
        = (1 / 2 : ℂ) + ((ρ.im + w : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [harg]
    refine le_trans (Work.Sieve.zeta_critical_line_aux (ρ.im + w)) ?_
    have h1 : |ρ.im + w| ≤ T + |w| := by
      calc |ρ.im + w| ≤ |ρ.im| + |w| := abs_add_le _ _
        _ ≤ T + |w| := by linarith
    have hbase : (1 : ℝ) ≤ 1 + |ρ.im + w| := by linarith [abs_nonneg (ρ.im + w)]
    have hr : (1 + |ρ.im + w|) ^ ((1 : ℝ) / 2) ≤ 1 + |ρ.im + w| := by
      calc (1 + |ρ.im + w|) ^ ((1 : ℝ) / 2) ≤ (1 + |ρ.im + w|) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hbase (by norm_num)
        _ = 1 + |ρ.im + w| := Real.rpow_one _
    have h3 : (1 : ℝ) ≤ 3 + T + |w| := by linarith [abs_nonneg w]
    have h4 : 1 + |ρ.im + w| ≤ (3 + T + |w|) ^ 4 := by
      have h2 : 1 + |ρ.im + w| ≤ 3 + T + |w| := by linarith
      calc 1 + |ρ.im + w| ≤ 3 + T + |w| := h2
        _ ≤ (3 + T + |w|) ^ 4 := by
            have h := pow_le_pow_right₀ h3 (by norm_num : (1 : ℕ) ≤ 4)
            simpa using h
    nlinarith [hr, h4, h1]
  -- the mollifier factor
  have hM : ‖MK K (((1 : ℂ) / 2) + (ρ.im : ℂ) * Complex.I + (w : ℂ) * Complex.I)‖ ≤ 2 * T ^ 2 := by
    have hargs : (((1 : ℂ) / 2) + (ρ.im : ℂ) * Complex.I + (w : ℂ) * Complex.I).re = 1 / 2 := by
      simp [Complex.add_re, Complex.mul_re]
    refine le_trans (MK_critical_bound K _ (by rw [hargs])) ?_
    have hsqrt : Real.sqrt (K : ℝ) ≤ T ^ 2 := by
      have h4 : T ^ 4 = (T ^ 2) ^ 2 := by ring
      have hK4 : (K : ℝ) ≤ (T ^ 2) ^ 2 := by rw [← h4]; exact hKT
      calc Real.sqrt (K : ℝ) ≤ Real.sqrt ((T ^ 2) ^ 2) := Real.sqrt_le_sqrt hK4
        _ = T ^ 2 := Real.sqrt_sq (by positivity)
    linarith
  -- the Γ factor
  have hG : ‖Complex.Gamma (((1 / 2 : ℝ) - ρ.re : ℝ) + (w : ℝ) * Complex.I)‖
      ≤ 64 * (1 + |w|) ^ (-(1 / 2) : ℝ) * Real.exp (-(Real.pi / 2) * |w|) :=
    gammaHalfNegBoundBig (1 / 2 - ρ.re) w (by linarith) (by linarith) hw
  rw [critIntegrand]
  have h1 : ‖riemannZeta (((1 : ℂ) / 2) + (ρ.im : ℂ) * Complex.I + (w : ℂ) * Complex.I)‖
        * ‖MK K (((1 : ℂ) / 2) + (ρ.im : ℂ) * Complex.I + (w : ℂ) * Complex.I)‖
      ≤ (9 * (3 + T + |w|) ^ 4) * (2 * T ^ 2) :=
    mul_le_mul hz hM (norm_nonneg _) (by positivity)
  have h2 : ‖riemannZeta (((1 : ℂ) / 2) + (ρ.im : ℂ) * Complex.I + (w : ℂ) * Complex.I)‖
        * ‖MK K (((1 : ℂ) / 2) + (ρ.im : ℂ) * Complex.I + (w : ℂ) * Complex.I)‖
        * ‖Complex.Gamma (((1 / 2 : ℝ) - ρ.re : ℝ) + (w : ℝ) * Complex.I)‖
      ≤ ((9 * (3 + T + |w|) ^ 4) * (2 * T ^ 2))
        * (64 * (1 + |w|) ^ (-(1 / 2) : ℝ) * Real.exp (-(Real.pi / 2) * |w|)) :=
    mul_le_mul h1 hG (norm_nonneg _) (by positivity)
  refine le_trans h2 ?_
  have hone : (1 + |w|) ^ (-(1 / 2) : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg w]) (by norm_num)
  have hstep : ((9 * (3 + T + |w|) ^ 4) * (2 * T ^ 2))
        * (64 * (1 + |w|) ^ (-(1 / 2) : ℝ) * Real.exp (-(Real.pi / 2) * |w|))
      ≤ ((9 * (3 + T + |w|) ^ 4) * (2 * T ^ 2)) * (64 * Real.exp (-(Real.pi / 2) * |w|)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc 64 * (1 + |w|) ^ (-(1 / 2) : ℝ) * Real.exp (-(Real.pi / 2) * |w|)
        ≤ 64 * 1 * Real.exp (-(Real.pi / 2) * |w|) := by
          gcongr
      _ = 64 * Real.exp (-(Real.pi / 2) * |w|) := by ring
  refine le_trans hstep (le_of_eq ?_)
  ring

/-! ## The numerical core -/

/-- Polynomial-versus-exponential monotonicity: for `x ≥ x0 > 0` and `a ≥ n/x0`,
`x^n e^{-a x} ≤ x0^n e^{-a x0}`. -/
private lemma pow_mul_exp_le_of_le {x0 x a : ℝ} {n : ℕ} (hx0 : 0 < x0) (hx : x0 ≤ x)
    (ha : (n : ℝ) / x0 ≤ a) :
    x ^ n * Real.exp (-(a * x)) ≤ x0 ^ n * Real.exp (-(a * x0)) := by
  obtain ⟨s, hs0, rfl⟩ : ∃ s : ℝ, 0 ≤ s ∧ x = x0 + s := ⟨x - x0, by linarith, by ring⟩
  have hpow : (1 + s / x0) ^ n ≤ Real.exp ((n : ℝ) * (s / x0)) := by
    rw [Real.exp_nat_mul]
    refine pow_le_pow_left₀ (by positivity) ?_ n
    linarith [Real.add_one_le_exp (s / x0)]
  have hsplit : (x0 + s) ^ n = x0 ^ n * (1 + s / x0) ^ n := by
    rw [show x0 + s = x0 * (1 + s / x0) by field_simp]
    rw [mul_pow]
  have hexp : Real.exp (-(a * (x0 + s)))
      = Real.exp (-(a * x0)) * Real.exp (-(a * s)) := by
    rw [show -(a * (x0 + s)) = (-(a * x0)) + (-(a * s)) by ring, Real.exp_add]
  have hle : Real.exp ((n : ℝ) * (s / x0) + (-(a * s))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : (n : ℝ) * (s / x0) + (-(a * s)) = ((n : ℝ) / x0 - a) * s := by field_simp; ring
    rw [this]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hs0
  calc (x0 + s) ^ n * Real.exp (-(a * (x0 + s)))
      = x0 ^ n * ((1 + s / x0) ^ n * (Real.exp (-(a * x0)) * Real.exp (-(a * s)))) := by
        rw [hsplit, hexp]; ring
    _ ≤ x0 ^ n * (Real.exp ((n : ℝ) * (s / x0))
          * (Real.exp (-(a * x0)) * Real.exp (-(a * s)))) := by
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hx0.le n)
        exact mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = (x0 ^ n * Real.exp (-(a * x0)))
          * (Real.exp ((n : ℝ) * (s / x0)) * Real.exp (-(a * s))) := by ring
    _ = (x0 ^ n * Real.exp (-(a * x0)))
          * Real.exp ((n : ℝ) * (s / x0) + (-(a * s))) := by rw [Real.exp_add]
    _ ≤ (x0 ^ n * Real.exp (-(a * x0))) * 1 := by
        refine mul_le_mul_of_nonneg_left hle ?_
        exact mul_nonneg (pow_nonneg hx0.le n) (Real.exp_nonneg _)
    _ = x0 ^ n * Real.exp (-(a * x0)) := by ring

/-- `e^{-15} ≤ 10^{-6}`. -/
private lemma exp_neg15_le : Real.exp (-15) ≤ 1 / 1000000 := by
  have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by
    have h := Real.exp_one_gt_d9
    linarith
  have h5 : (2.7 : ℝ) ^ 5 ≤ Real.exp 5 := by
    rw [show Real.exp 5 = Real.exp 1 ^ 5 by rw [← Real.exp_nat_mul]; norm_num]
    exact pow_le_pow_left₀ (by norm_num) he1 5
  have h15 : (2.7 : ℝ) ^ 15 ≤ Real.exp 15 := by
    calc (2.7 : ℝ) ^ 15 = ((2.7 : ℝ) ^ 5) ^ 3 := by ring
      _ ≤ (Real.exp 5) ^ 3 := pow_le_pow_left₀ (by positivity) h5 3
      _ = Real.exp 15 := by
          rw [show Real.exp 15 = Real.exp 5 ^ 3 by rw [← Real.exp_nat_mul]; norm_num]
  have hnum : (1000000 : ℝ) ≤ (2.7 : ℝ) ^ 15 := by norm_num
  rw [Real.exp_neg, show (1 : ℝ) / 1000000 = ((1000000 : ℝ))⁻¹ by norm_num]
  exact (inv_le_inv₀ (Real.exp_pos 15) (by norm_num)).mpr (le_trans hnum h15)

/-- `e^{-35} ≤ 10^{-15}`. -/
private lemma exp_neg35_le : Real.exp (-35) ≤ 1 / 1000000000000000 := by
  have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by
    have h := Real.exp_one_gt_d9
    linarith
  have h5 : (2.7 : ℝ) ^ 5 ≤ Real.exp 5 := by
    rw [show Real.exp 5 = Real.exp 1 ^ 5 by rw [← Real.exp_nat_mul]; norm_num]
    exact pow_le_pow_left₀ (by norm_num) he1 5
  have h35 : (2.7 : ℝ) ^ 35 ≤ Real.exp 35 := by
    calc (2.7 : ℝ) ^ 35 = ((2.7 : ℝ) ^ 5) ^ 7 := by ring
      _ ≤ (Real.exp 5) ^ 7 := pow_le_pow_left₀ (by positivity) h5 7
      _ = Real.exp 35 := by
          rw [show Real.exp 35 = Real.exp 5 ^ 7 by rw [← Real.exp_nat_mul]; norm_num]
  have hnum : (1000000000000000 : ℝ) ≤ (2.7 : ℝ) ^ 35 := by norm_num
  rw [Real.exp_neg, show (1 : ℝ) / 1000000000000000 = ((1000000000000000 : ℝ))⁻¹ by norm_num]
  exact (inv_le_inv₀ (Real.exp_pos 35) (by norm_num)).mpr (le_trans hnum h35)

/-- **The numerical core.**  For `A ≥ 6`, `T ≥ 1` and `x = log (A T) ≥ 5`,
`T² (3 + T + A x)^4 e^{-(π/2) A x} ≤ 10^{-6}` (the true maximum is about `2.3 · 10^{-11}`). -/
private lemma tailNumericAuxBig (A T : ℝ) (hA : 6 ≤ A) (hT : 1 ≤ T)
    (hx : 5 ≤ Real.log (A * T)) :
    T ^ 2 * (3 + T + A * Real.log (A * T)) ^ 4
      * Real.exp (-(Real.pi / 2) * (A * Real.log (A * T))) ≤ 1 / 1000000 := by
  set x : ℝ := Real.log (A * T) with hxdef
  set H : ℝ := A * x with hHdef
  have hApos : 0 < A := by linarith
  have hTpos : 0 < T := by linarith
  have hATpos : 0 < A * T := by positivity
  have hx5 : 5 ≤ x := hx
  have hxpos : 0 < x := by linarith
  have hexpx : Real.exp x = A * T := by rw [hxdef]; exact Real.exp_log hATpos
  have hTexp : T = Real.exp x / A := by rw [hexpx]; field_simp
  have hHne : H ≠ 0 := by rw [hHdef]; nlinarith
  have hTx : T = x * Real.exp x / H := by
    rw [hTexp, hHdef]
    field_simp
  have hH6 : 6 * x ≤ H := by rw [hHdef]; nlinarith
  have hHnn : 0 ≤ H := by linarith
  have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by
    have h := Real.exp_one_gt_d9
    linarith
  have hexp90 : (90 : ℝ) ≤ Real.exp x := by
    have h2 : (90 : ℝ) ≤ (2.7 : ℝ) ^ 5 := by norm_num
    have h3 : (2.7 : ℝ) ^ 5 ≤ Real.exp 5 := by
      rw [show Real.exp 5 = Real.exp 1 ^ 5 by rw [← Real.exp_nat_mul]; norm_num]
      exact pow_le_pow_left₀ (by norm_num) he1 5
    have h4 : Real.exp 5 ≤ Real.exp x := Real.exp_le_exp.mpr hx5
    linarith
  have he15 : Real.exp (-15) ≤ 1 / 1000000 := exp_neg15_le
  have he35 : Real.exp (-35) ≤ 1 / 1000000000000000 := exp_neg35_le
  -- the split `(3+T+H)^4 ≤ 16((3+T)^4 + H^4)`
  have hsplit : (3 + T + H) ^ 4 ≤ 16 * ((3 + T) ^ 4 + H ^ 4) := by
    have ha : 0 ≤ 3 + T := by linarith
    have hb : 0 ≤ H := hHnn
    have h1 : 3 + T + H ≤ 2 * max (3 + T) H := by
      rcases le_total (3 + T) H with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith
    have h2 : (2 * max (3 + T) H) ^ 4 = 16 * (max (3 + T) H) ^ 4 := by ring
    have h3 : (max (3 + T) H) ^ 4 ≤ (3 + T) ^ 4 + H ^ 4 := by
      rcases le_total (3 + T) H with h | h
      · rw [max_eq_right h]; linarith [pow_nonneg ha 4]
      · rw [max_eq_left h]; linarith [pow_nonneg hb 4]
    calc (3 + T + H) ^ 4 ≤ (2 * max (3 + T) H) ^ 4 := pow_le_pow_left₀ (by linarith) h1 4
      _ = 16 * (max (3 + T) H) ^ 4 := h2
      _ ≤ 16 * ((3 + T) ^ 4 + H ^ 4) := by linarith
  -- the two summands
  have hT2' : T ^ 2 ≤ Real.exp (2 * x) / 36 := by
    have hA2 : (36 : ℝ) ≤ A ^ 2 := by nlinarith
    rw [hTexp, div_pow, show (Real.exp x) ^ 2 = Real.exp (2 * x) by
      rw [show (2 : ℝ) * x = ((2 : ℕ) : ℝ) * x by norm_num, Real.exp_nat_mul]]
    exact div_le_div_of_nonneg_left (Real.exp_nonneg _) (by norm_num) hA2
  have h34' : (3 + T) ^ 4 ≤ Real.exp (4 * x) / 625 := by
    have h1 : 3 + T ≤ Real.exp x / 5 := by
      have hAx : Real.exp x / A ≤ Real.exp x / 6 :=
        div_le_div_of_nonneg_left (Real.exp_nonneg _) (by norm_num) hA
      rw [hTexp]
      linarith
    have h2 : (3 + T) ^ 4 ≤ (Real.exp x / 5) ^ 4 := pow_le_pow_left₀ (by linarith) h1 4
    refine le_trans h2 (le_of_eq ?_)
    rw [div_pow, show (Real.exp x) ^ 4 = Real.exp (4 * x) by
      rw [show (4 : ℝ) * x = ((4 : ℕ) : ℝ) * x by norm_num, Real.exp_nat_mul]]
    norm_num
  have hdecay : Real.exp (-(Real.pi / 2) * H) ≤ Real.exp (-9 * x) := by
    rw [Real.exp_le_exp]
    nlinarith [Real.pi_gt_three, hH6]
  -- first summand
  have hTerm1 : 16 * T ^ 2 * (3 + T) ^ 4 * Real.exp (-(Real.pi / 2) * H)
      ≤ 16 / 22500 * Real.exp (-15) := by
    have hstep : T ^ 2 * (3 + T) ^ 4 ≤ Real.exp (6 * x) / 22500 := by
      have h := mul_le_mul hT2' h34' (by positivity) (by positivity)
      refine le_trans h (le_of_eq ?_)
      rw [div_mul_div_comm, ← Real.exp_add]
      norm_num
      congr 1
      ring
    have h1 : 16 * T ^ 2 * (3 + T) ^ 4 * Real.exp (-(Real.pi / 2) * H)
        ≤ 16 * (Real.exp (6 * x) / 22500) * Real.exp (-9 * x) := by
      calc 16 * T ^ 2 * (3 + T) ^ 4 * Real.exp (-(Real.pi / 2) * H)
          = 16 * (T ^ 2 * (3 + T) ^ 4) * Real.exp (-(Real.pi / 2) * H) := by ring
        _ ≤ 16 * (Real.exp (6 * x) / 22500) * Real.exp (-9 * x) := by gcongr
    refine le_trans h1 ?_
    calc 16 * (Real.exp (6 * x) / 22500) * Real.exp (-9 * x)
        = 16 / 22500 * (Real.exp (6 * x) * Real.exp (-9 * x)) := by ring
      _ = 16 / 22500 * Real.exp (-(3 * x)) := by
          rw [show Real.exp (6 * x) * Real.exp (-9 * x) = Real.exp (-(3 * x)) by
            rw [← Real.exp_add]; ring_nf]
      _ ≤ 16 / 22500 * Real.exp (-15) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          rw [Real.exp_le_exp]; linarith
  -- second summand
  have hTerm2 : 16 * T ^ 2 * H ^ 4 * Real.exp (-(Real.pi / 2) * H)
      ≤ 576 * 625 * Real.exp (-35) := by
    have hsq2 : (Real.exp x) ^ 2 = Real.exp (2 * x) := (Real.exp_nat_mul x 2).symm
    have hstep2 : (x * Real.exp x / H) ^ 2 * H ^ 4 = x ^ 2 * (Real.exp x) ^ 2 * H ^ 2 := by
      field_simp
    have hT2eq : T ^ 2 * H ^ 4 = x ^ 2 * Real.exp (2 * x) * H ^ 2 := by
      rw [hTx, hstep2, hsq2]
    have ha2 : (2 : ℝ) / (6 * x) ≤ Real.pi / 2 := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < 6 * x)]
      nlinarith [Real.pi_gt_three, hx5]
    have hHpow : H ^ 2 * Real.exp (-(Real.pi / 2) * H)
        ≤ (6 * x) ^ 2 * Real.exp (-(Real.pi / 2) * (6 * x)) := by
      have h := pow_mul_exp_le_of_le (x0 := 6 * x) (x := H) (a := Real.pi / 2) (n := 2)
        (by linarith) hH6 ha2
      simpa only [neg_mul] using h
    have hHdec : Real.exp (-(Real.pi / 2) * (6 * x)) ≤ Real.exp (-9 * x) := by
      rw [Real.exp_le_exp]; nlinarith [Real.pi_gt_three]
    have hx4 : x ^ 4 * Real.exp (-(7 * x)) ≤ 5 ^ 4 * Real.exp (-(7 * 5)) :=
      pow_mul_exp_le_of_le (x0 := 5) (x := x) (a := 7) (n := 4) (by norm_num) hx5 (by norm_num)
    calc 16 * T ^ 2 * H ^ 4 * Real.exp (-(Real.pi / 2) * H)
        = 16 * (T ^ 2 * H ^ 4) * Real.exp (-(Real.pi / 2) * H) := by ring
      _ = 16 * (x ^ 2 * Real.exp (2 * x) * H ^ 2) * Real.exp (-(Real.pi / 2) * H) := by
          rw [hT2eq]
      _ = 16 * (x ^ 2 * Real.exp (2 * x)) * (H ^ 2 * Real.exp (-(Real.pi / 2) * H)) := by ring
      _ ≤ 16 * (x ^ 2 * Real.exp (2 * x))
            * ((6 * x) ^ 2 * Real.exp (-(Real.pi / 2) * (6 * x))) := by gcongr
      _ ≤ 16 * (x ^ 2 * Real.exp (2 * x)) * ((6 * x) ^ 2 * Real.exp (-9 * x)) := by gcongr
      _ = 576 * (x ^ 4 * Real.exp (-(7 * x))) := by
          rw [show (16 : ℝ) * (x ^ 2 * Real.exp (2 * x)) * ((6 * x) ^ 2 * Real.exp (-9 * x))
              = 576 * (x ^ 4 * (Real.exp (2 * x) * Real.exp (-9 * x))) by ring,
            show Real.exp (2 * x) * Real.exp (-9 * x) = Real.exp (-(7 * x)) by
              rw [← Real.exp_add]; ring_nf]
      _ ≤ 576 * (5 ^ 4 * Real.exp (-(7 * 5))) := by gcongr
      _ = 576 * 625 * Real.exp (-35) := by ring
  have hfin : 16 / 22500 * Real.exp (-15) + 576 * 625 * Real.exp (-35) ≤ 1 / 1000000 := by
    have h1 : 16 / 22500 * Real.exp (-15) ≤ 16 / 22500 * (1 / 1000000) :=
      mul_le_mul_of_nonneg_left he15 (by norm_num)
    have h2 : 576 * 625 * Real.exp (-35) ≤ 576 * 625 * (1 / 1000000000000000) :=
      mul_le_mul_of_nonneg_left he35 (by norm_num)
    linarith
  have hbig : T ^ 2 * (3 + T + H) ^ 4 * Real.exp (-(Real.pi / 2) * H)
      ≤ 16 * T ^ 2 * (3 + T) ^ 4 * Real.exp (-(Real.pi / 2) * H)
        + 16 * T ^ 2 * H ^ 4 * Real.exp (-(Real.pi / 2) * H) := by
    have hp : 0 ≤ T ^ 2 * Real.exp (-(Real.pi / 2) * H) := by positivity
    have h := mul_le_mul_of_nonneg_left hsplit hp
    nlinarith [h]
  have key : T ^ 2 * (3 + T + H) ^ 4 * Real.exp (-(Real.pi / 2) * H) ≤ 1 / 1000000 := by
    linarith [hbig, hTerm1, hTerm2, hfin]
  exact key

/-! ## The main theorem -/

theorem critTailSmallBig :
    ∀ (A : ℝ), 6 ≤ A → ∀ (T : ℝ), 2 ≤ T → ∀ (K : ℕ) (Y : ℝ),
      1 ≤ K → (K : ℝ) ≤ T ^ 4 → 1 ≤ Y → Y ≤ (A * T) ^ 2 →
      ∀ ρ : ℂ, 1 / 2 ≤ ρ.re → ρ.re ≤ 1 → |ρ.im| ≤ T →
        (Real.log (A * T)) ^ 2 ≤ |ρ.im| →
        Y ^ (1 / 2 - ρ.re) *
          ((∫ v in Set.Ioi (A * Real.log (A * T)), Work.ZeroDensity.Ingham.critIntegrand K ρ v)
            + (∫ v in Set.Iic (-(A * Real.log (A * T))),
                Work.ZeroDensity.Ingham.critIntegrand K ρ v)) ≤ Real.pi / 10 := by
  intro A hA T hT K Y hK1 hKT hY1 hYT ρ hρ1 hρ2 hγ hxc
  have hApos : 0 < A := by linarith
  have hTpos : 0 < T := by linarith
  have hTnn : 0 ≤ T := by linarith
  have hATpos : 0 < A * T := by positivity
  set x : ℝ := Real.log (A * T) with hxdef
  set H : ℝ := A * x with hHdef
  have hx5 : 5 ≤ Real.log (A * T) :=
    logAT_ge_five_big hA hT (by rw [← hxdef]; exact le_trans hxc hγ)
  have hx5' : 5 ≤ x := hx5
  have hH30 : 30 ≤ H := by
    have h6 : 6 * x ≤ H := by rw [hHdef]; nlinarith
    linarith
  have hH1 : 1 ≤ H := by linarith
  have hYpow : Y ^ (1 / 2 - ρ.re) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hY1 (by linarith)
  have hCnn : (0 : ℝ) ≤ 1152 * T ^ 2 := by positivity
  have hI1 : (∫ v in Set.Ioi H, Work.ZeroDensity.Ingham.critIntegrand K ρ v)
      ≤ (1152 * T ^ 2) * (Real.exp (-(Real.pi / 2) * H) * (3 + T + H) ^ 4 * 65) := by
    refine tailIntegralHalfBoundBig T H hTnn hH1 (1152 * T ^ 2) hCnn
      (fun v => Work.ZeroDensity.Ingham.critIntegrand K ρ v) ?_ ?_
    · intro v _
      exact critIntegrand_nonneg K ρ v
    · intro v hv
      have hvH : H < v := hv
      have hv0 : 0 ≤ v := by linarith
      have hvabs : |v| = v := abs_of_nonneg hv0
      have hv30 : 5 / 2 ≤ |v| := by rw [hvabs]; linarith
      have h := critIntegrand_abs_le K T ρ v hKT hTnn hρ1 hρ2 hγ hv30
      rwa [hvabs] at h
  have hI2 : (∫ v in Set.Iic (-H), Work.ZeroDensity.Ingham.critIntegrand K ρ v)
      ≤ (1152 * T ^ 2) * (Real.exp (-(Real.pi / 2) * H) * (3 + T + H) ^ 4 * 65) := by
    rw [← integral_comp_neg_Ioi H (fun x => Work.ZeroDensity.Ingham.critIntegrand K ρ x)]
    refine tailIntegralHalfBoundBig T H hTnn hH1 (1152 * T ^ 2) hCnn
      (fun v => Work.ZeroDensity.Ingham.critIntegrand K ρ (-v)) ?_ ?_
    · intro v _
      exact critIntegrand_nonneg K ρ (-v)
    · intro v hv
      have hvH : H < v := hv
      have hv0 : 0 ≤ v := by linarith
      have hvabs : |(-v)| = v := by rw [abs_neg, abs_of_nonneg hv0]
      have hv30 : 5 / 2 ≤ |(-v)| := by rw [hvabs]; linarith
      have h := critIntegrand_abs_le K T ρ (-v) hKT hTnn hρ1 hρ2 hγ hv30
      rwa [hvabs] at h
  have hsum : (∫ v in Set.Ioi H, Work.ZeroDensity.Ingham.critIntegrand K ρ v)
        + (∫ v in Set.Iic (-H), Work.ZeroDensity.Ingham.critIntegrand K ρ v)
      ≤ 2 * ((1152 * T ^ 2) * (Real.exp (-(Real.pi / 2) * H) * (3 + T + H) ^ 4 * 65)) := by
    linarith
  have hsum_nn : 0 ≤ (∫ v in Set.Ioi H, Work.ZeroDensity.Ingham.critIntegrand K ρ v)
        + (∫ v in Set.Iic (-H), Work.ZeroDensity.Ingham.critIntegrand K ρ v) := by
    refine add_nonneg ?_ ?_
    · exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun v => critIntegrand_nonneg K ρ v)
    · exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun v => critIntegrand_nonneg K ρ v)
  have hnum := tailNumericAuxBig A T hA (by linarith) hx5
  have hnumH : T ^ 2 * (3 + T + H) ^ 4 * Real.exp (-(Real.pi / 2) * H) ≤ 1 / 1000000 := by
    rw [hHdef, hxdef]
    exact hnum
  have hmain : Y ^ (1 / 2 - ρ.re) *
      ((∫ v in Set.Ioi H, Work.ZeroDensity.Ingham.critIntegrand K ρ v)
        + (∫ v in Set.Iic (-H), Work.ZeroDensity.Ingham.critIntegrand K ρ v))
      ≤ 149760 * (T ^ 2 * (3 + T + H) ^ 4 * Real.exp (-(Real.pi / 2) * H)) := by
    calc Y ^ (1 / 2 - ρ.re) *
          ((∫ v in Set.Ioi H, Work.ZeroDensity.Ingham.critIntegrand K ρ v)
            + (∫ v in Set.Iic (-H), Work.ZeroDensity.Ingham.critIntegrand K ρ v))
        ≤ 1 * (2 * ((1152 * T ^ 2) * (Real.exp (-(Real.pi / 2) * H) * (3 + T + H) ^ 4 * 65))) :=
          mul_le_mul hYpow hsum hsum_nn (by norm_num)
      _ = 149760 * (T ^ 2 * (3 + T + H) ^ 4 * Real.exp (-(Real.pi / 2) * H)) := by ring
  refine le_trans hmain ?_
  have h2 : 149760 * (T ^ 2 * (3 + T + H) ^ 4 * Real.exp (-(Real.pi / 2) * H))
      ≤ 149760 * (1 / 1000000) :=
    mul_le_mul_of_nonneg_left hnumH (by norm_num)
  refine le_trans h2 ?_
  have h3 : (149760 : ℝ) * (1 / 1000000) = 0.14976 := by norm_num
  rw [h3]
  linarith [Real.pi_gt_three]

end Work.ZeroDensity.Ingham.zetaDetectorBig
