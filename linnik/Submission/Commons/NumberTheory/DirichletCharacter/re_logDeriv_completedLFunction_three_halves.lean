import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.completedLogDeriv_two_le
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_logDeriv_eq_neg_LSeries_vonMangoldt
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_logRem_le

open Complex DirichletCharacter Filter Set MeasureTheory
open scoped Real Topology

set_option autoImplicit false
noncomputable section

namespace Commons.NumberTheory.DirichletCharacter

/-! ### A sharp bound for `∑' n, log n / n ^ (3/2)` -/

/-- The summand `log x / x ^ (3/2)`. -/
private noncomputable def logDivPow (x : ℝ) : ℝ := Real.log x / x ^ ((3 : ℝ) / 2)

private lemma logDivPow_antitone : AntitoneOn logDivPow (Ici (2 : ℝ)) := by
  have hanti : AntitoneOn (fun x : ℝ => Real.log x / x ^ ((3 : ℝ) / 2))
      (Ici (Real.exp ((3 : ℝ) / 2)⁻¹)) :=
    Real.log_div_self_rpow_antitoneOn (a := (3 : ℝ) / 2) (by norm_num)
  have hexp : Real.exp ((3 : ℝ) / 2)⁻¹ ≤ (2 : ℝ) := by
    have h : ((3 : ℝ) / 2)⁻¹ = 2 / 3 := by norm_num
    rw [h]
    have h2 : (2 : ℝ) / 3 < Real.log 2 := by linarith [Real.log_two_gt_d9]
    calc Real.exp (2 / 3) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr h2.le
      _ = 2 := Real.exp_log (by norm_num)
  exact hanti.mono (fun x hx => by simp only [mem_Ici] at hx ⊢; linarith)

private lemma logDivPow_nonneg : ∀ x ∈ Ioi (2 : ℝ), 0 ≤ logDivPow x := by
  intro x hx
  have hx2 : (2 : ℝ) < x := hx
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hx0 : (0 : ℝ) < x := by linarith
  exact div_nonneg hlog (Real.rpow_nonneg hx0.le _)

private lemma hasDerivAt_logDivPow (x : ℝ) (hx : x ∈ Ici (2 : ℝ)) :
    HasDerivAt (fun y : ℝ => -((2 * Real.log y + 4) / Real.sqrt y)) (logDivPow x) x := by
  have hx2 : (2 : ℝ) ≤ x := hx
  have hxpos : (0 : ℝ) < x := by linarith
  have hx0 : x ≠ 0 := hxpos.ne'
  have hsq : 0 < Real.sqrt x := Real.sqrt_pos.mpr hxpos
  have hsqrt : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt x)) x := Real.hasDerivAt_sqrt hx0
  have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx0
  have hnum : HasDerivAt (fun y : ℝ => 2 * Real.log y + 4) (2 * x⁻¹) x :=
    (hlog.const_mul 2).add_const 4
  have hdiv := hnum.div hsqrt hsq.ne'
  have h3 := hdiv.neg
  have hder : -(((2 * x⁻¹) * Real.sqrt x - (2 * Real.log x + 4) * (1 / (2 * Real.sqrt x)))
      / Real.sqrt x ^ 2) = logDivPow x := by
    rw [logDivPow, Real.sq_sqrt hxpos.le]
    have hxr : x ^ ((3 : ℝ) / 2) = x * Real.sqrt x := by
      rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hxpos, Real.rpow_one,
        ← Real.sqrt_eq_rpow]
    rw [hxr]
    field_simp
    rw [Real.sq_sqrt hxpos.le]
    ring
  rwa [hder] at h3

private lemma tendsto_logDivPow_anti :
    Tendsto (fun y : ℝ => -((2 * Real.log y + 4) / Real.sqrt y)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun y : ℝ => Real.log y / Real.sqrt y) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
    have heq : (fun y : ℝ => Real.log y / y ^ ((1:ℝ)/2)) =
        (fun y : ℝ => Real.log y / Real.sqrt y) := by
      funext y; rw [Real.sqrt_eq_rpow]
    rwa [heq] at h
  have h2 : Tendsto (fun y : ℝ => (4 : ℝ) / Real.sqrt y) atTop (𝓝 0) := by
    have hsqrt : Tendsto (fun y : ℝ => Real.sqrt y) atTop atTop := Real.tendsto_sqrt_atTop
    have hinv : Tendsto (fun y : ℝ => (Real.sqrt y)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hsqrt
    have := (tendsto_const_nhds (x := (4:ℝ))).mul hinv
    simpa [div_eq_mul_inv, mul_comm] using this
  have h3 : Tendsto (fun y : ℝ => (2 * Real.log y + 4) / Real.sqrt y) atTop (𝓝 0) := by
    have heq : (fun y : ℝ => (2 * Real.log y + 4) / Real.sqrt y)
        = (fun y : ℝ => 2 * (Real.log y / Real.sqrt y) + 4 / Real.sqrt y) := by
      funext y; ring
    rw [heq]
    have h := (tendsto_const_nhds (x := (2:ℝ))).mul h1
    simpa using h.add h2
  simpa using h3.neg

private lemma integral_logDivPow :
    ∫ x in Ioi (2 : ℝ), logDivPow x = Real.sqrt 2 * (Real.log 2 + 2) := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg'
    (g := fun y : ℝ => -((2 * Real.log y + 4) / Real.sqrt y)) (g' := logDivPow)
    hasDerivAt_logDivPow logDivPow_nonneg tendsto_logDivPow_anti
  have h2pos : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hval : (0 : ℝ) - (-((2 * Real.log 2 + 4) / Real.sqrt 2)) =
      Real.sqrt 2 * (Real.log 2 + 2) := by
    have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    field_simp
    rw [hsq]
    ring
  rw [h, hval]

private lemma integrableOn_logDivPow : IntegrableOn logDivPow (Ioi (2 : ℝ)) :=
  integrableOn_Ioi_deriv_of_nonneg'
    (g := fun y : ℝ => -((2 * Real.log y + 4) / Real.sqrt y)) (g' := logDivPow)
    hasDerivAt_logDivPow logDivPow_nonneg tendsto_logDivPow_anti

private lemma tsum_logDivPow_le : (∑' n : ℕ, logDivPow n) ≤ (4.5 : ℝ) := by
  have hanti' : AntitoneOn logDivPow (Ici (((3:ℕ):ℝ) - 1)) := by
    rw [show (((3:ℕ):ℝ) - 1) = 2 by norm_num]; exact logDivPow_antitone
  have hint' : IntegrableOn logDivPow (Ioi (((3:ℕ):ℝ) - 1)) := by
    rw [show (((3:ℕ):ℝ) - 1) = 2 by norm_num]; exact integrableOn_logDivPow
  have hnonneg' : ∀ t ∈ Ioi (((3:ℕ):ℝ) - 1), 0 ≤ logDivPow t := by
    intro t ht
    rw [show (((3:ℕ):ℝ) - 1) = 2 by norm_num] at ht
    exact logDivPow_nonneg t ht
  have hb := AntitoneOn.abs_tsum_sub_sum_range_le_integral (f := logDivPow) (N := 3)
    (by norm_num) hanti' hint' hnonneg'
  rw [show (((3:ℕ):ℝ) - 1) = 2 by norm_num, integral_logDivPow] at hb
  have h1 : (∑' n : ℕ, logDivPow n) - ∑ n ∈ Finset.range 3, logDivPow n ≤
      Real.sqrt 2 * (Real.log 2 + 2) := le_trans (le_abs_self _) hb
  have hsum3 : ∑ n ∈ Finset.range 3, logDivPow n = Real.log 2 / (2 * Real.sqrt 2) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    simp only [Finset.sum_range_zero, zero_add, logDivPow, Nat.cast_ofNat, Nat.cast_zero,
      Nat.cast_one, Real.log_zero, Real.log_one, zero_div]
    have h2 : (2:ℝ) ^ ((3:ℝ)/2) = 2 * Real.sqrt 2 := by
      rw [show (3:ℝ)/2 = 1 + 1/2 by norm_num, Real.rpow_add (by norm_num : (0:ℝ) < 2),
        Real.rpow_one, ← Real.sqrt_eq_rpow]
    rw [h2]
  rw [hsum3] at h1
  have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hs2u : Real.sqrt 2 < 3 / 2 := Real.sqrt_two_lt_three_halves
  have hs2one : (1:ℝ) < Real.sqrt 2 := Real.one_lt_sqrt_two
  have hb1 : Real.log 2 / (2 * Real.sqrt 2) ≤ 0.3465735904 := by
    have hstep : Real.log 2 / (2 * Real.sqrt 2) ≤ Real.log 2 / 2 :=
      div_le_div_of_nonneg_left hlog2pos.le (by norm_num) (by linarith)
    have hstep2 : Real.log 2 / 2 ≤ 0.3465735904 := by
      rw [div_le_iff₀ (by norm_num)]; linarith
    linarith
  have hb2 : Real.sqrt 2 * (Real.log 2 + 2) ≤ 4.0397207712 := by
    have hstep : Real.sqrt 2 * (Real.log 2 + 2) ≤ (3/2) * (Real.log 2 + 2) :=
      mul_le_mul_of_nonneg_right hs2u.le (by linarith)
    have hstep2 : (3/2 : ℝ) * (Real.log 2 + 2) ≤ 4.0397207712 := by
      nlinarith [hlog2]
    linarith
  linarith


private lemma summable_logDivPow : Summable (fun n : ℕ => logDivPow n) :=
  AntitoneOn.summable_of_integrableOn_Ioi (N := 2) logDivPow_antitone integrableOn_logDivPow
    logDivPow_nonneg

/-! ### An upper bound for the real part of the digamma function

On the strip `1/2 ≤ Re z ≤ 2` we have `Re ψ(z) ≤ log (2 + |Im z|) + 1/2`, an immediate
consequence of the Binet-type remainder bound `digamma_logRem_le`. -/

private lemma re_digamma_le (x y : ℝ) (hx1 : (1 : ℝ) / 2 ≤ x) (hx2 : x ≤ 2) :
    (Complex.digamma ((x : ℂ) + (y : ℂ) * Complex.I)).re ≤ Real.log (2 + |y|) + 1 / 2 := by
  have h := Commons.Analysis.SpecialFunctions.Gamma.digamma_logRem_le x y hx1 (by linarith)
  set z : ℂ := (x : ℂ) + (y : ℂ) * Complex.I with hz
  have hzre : z.re = x := by simp [z]
  have hz0 : z ≠ 0 := by
    intro h0
    have hre := congrArg Complex.re h0
    rw [hzre] at hre
    simp at hre
    linarith
  have hkey : Complex.digamma z =
      (Complex.digamma z - Complex.log z + ((2 : ℂ)⁻¹) * z⁻¹) + Complex.log z
        - ((2 : ℂ)⁻¹) * z⁻¹ := by ring
  have hrem : (Complex.digamma z - Complex.log z + ((2 : ℂ)⁻¹) * z⁻¹).re ≤ 1 / 2 := by
    refine le_trans (Complex.re_le_norm _) ?_
    simpa [z] using h
  have hnonneg : 0 ≤ (((2 : ℂ)⁻¹) * z⁻¹).re := by
    have heq : ((2 : ℂ)⁻¹) * z⁻¹ = (2 * z)⁻¹ := (mul_inv (2 : ℂ) z).symm
    rw [heq, Complex.inv_re]
    have h2z : (0 : ℝ) ≤ (2 * z).re := by
      rw [Complex.mul_re]
      simp [hzre]
      linarith
    exact div_nonneg h2z (Complex.normSq_nonneg _)
  have hnorm : ‖z‖ ≤ 2 + |y| := by
    have h1 : ‖z‖ ≤ ‖(x : ℂ)‖ + ‖(y : ℂ) * Complex.I‖ := by
      rw [hz]; exact norm_add_le _ _
    have h2 : ‖(x : ℂ)‖ = |x| := by simp
    have h3 : ‖(y : ℂ) * Complex.I‖ = |y| := by
      rw [norm_mul]; simp
    rw [h2, h3] at h1
    have hxabs : |x| = x := abs_of_nonneg (by linarith)
    rw [hxabs] at h1
    linarith
  have hlogmono : Real.log ‖z‖ ≤ Real.log (2 + |y|) :=
    Real.log_le_log (norm_pos_iff.mpr hz0) hnorm
  have hlogre : (Complex.log z).re = Real.log ‖z‖ := Complex.log_re z
  rw [hkey, Complex.sub_re, Complex.add_re, hlogre]
  linarith

/-! ### The real part of `logDeriv (Gammaℝ) ` on a short vertical line -/

private lemma re_logDeriv_GammaR_at (a T : ℝ) (ha1 : (1 : ℝ) ≤ a) (ha2 : a ≤ 4) :
    (logDeriv Complex.Gammaℝ ((a : ℂ) + Complex.I * (T : ℂ))).re ≤
      (1 / 2) * Real.log (2 + |T|) + (1 / 4 - Real.log Real.pi / 2) := by
  set w : ℂ := (a : ℂ) + Complex.I * (T : ℂ) with hw
  have hwre : w.re = a := by simp [w]
  have hwpos : 0 < w.re := by rw [hwre]; linarith
  have hmain : (logDeriv Complex.Gammaℝ w).re ≤
      (1 / 2) * Real.log (2 + |T|) + (1 / 4 - Real.log Real.pi / 2) := by
    rw [logDeriv_Gammaℝ_formula w hwpos]
    rw [Complex.add_re]
    have hneg : (-(Complex.log (Real.pi : ℂ)) / 2).re = -Real.log Real.pi / 2 := by
      rw [← Complex.ofReal_log (le_of_lt Real.pi_pos)]
      simp
    rw [hneg, re_div_two]
    have hdig2 : (Complex.digamma (w / 2)).re ≤ Real.log (2 + |T|) + 1 / 2 := by
      have hw2 : w / 2 = ((a / 2 : ℝ) : ℂ) + ((T / 2 : ℝ) : ℂ) * Complex.I := by
        rw [hw]; push_cast; ring
      have hdig := re_digamma_le (a / 2) (T / 2) (by linarith) (by linarith)
      rw [← hw2] at hdig
      refine le_trans hdig ?_
      have hT2 : |T / 2| ≤ |T| := by
        rw [abs_div]
        simp only [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
        exact div_le_self (abs_nonneg T) (by norm_num)
      have h1 : Real.log (2 + |T / 2|) ≤ Real.log (2 + |T|) :=
        Real.log_le_log (by positivity) (by linarith)
      linarith
    linarith
  simpa [hw] using hmain

/-! ### The gamma factor at `3/2 + iT` -/

private lemma re_logDeriv_gammaFactor_three_halves_le {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (T : ℝ) :
    (logDeriv (gammaFactor χ) ((3 / 2 : ℂ) + Complex.I * (T : ℂ))).re ≤
      (1 / 2) * Real.log (2 + |T|) + 1 / 4 := by
  set s : ℂ := (3 / 2 : ℂ) + Complex.I * (T : ℂ) with hsdef
  have hlogpi_nonneg : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hbase : (1 / 2) * Real.log (2 + |T|) + (1 / 4 - Real.log Real.pi / 2) ≤
      (1 / 2) * Real.log (2 + |T|) + 1 / 4 := by linarith
  rcases χ.even_or_odd with hE | hO
  · have hfun : gammaFactor χ = Complex.Gammaℝ := by
      funext z; exact hE.gammaFactor_def z
    have hgoal : (logDeriv Complex.Gammaℝ s).re ≤
        (1 / 2) * Real.log (2 + |T|) + (1 / 4 - Real.log Real.pi / 2) := by
      have := re_logDeriv_GammaR_at (3 / 2) T (by norm_num) (by norm_num)
      simpa [s] using this
    rw [hfun]
    linarith
  · have hfun : gammaFactor χ = (fun z : ℂ => Complex.Gammaℝ (z + 1)) := by
      funext z; exact hO.gammaFactor_def z
    rw [hfun]
    have hsre : s.re = 3 / 2 := by simp [s]
    have hs1b : 0 < (s + 1).re := by
      rw [Complex.add_re]; simp; linarith
    have hldcomp : logDeriv (fun z : ℂ => Complex.Gammaℝ (z + 1)) s =
        logDeriv Complex.Gammaℝ (s + 1) := by
      have hf : DifferentiableAt ℂ Complex.Gammaℝ (s + 1) :=
        differentiableAt_Gammaℝ (s + 1) hs1b
      have hg : DifferentiableAt ℂ (fun z : ℂ => z + 1) s := by fun_prop
      have h := logDeriv_comp (f := Complex.Gammaℝ) (g := fun z : ℂ => z + 1) (x := s) hf hg
      have hder : deriv (fun z : ℂ => z + 1) s = 1 := by simp
      rw [hder] at h
      simpa [Function.comp_def, mul_comm] using h
    rw [hldcomp]
    have hS : s + 1 = ((5 / 2 : ℝ) : ℂ) + Complex.I * (T : ℂ) := by
      rw [hsdef]; push_cast; ring
    have hgoal : (logDeriv Complex.Gammaℝ (s + 1)).re ≤
        (1 / 2) * Real.log (2 + |T|) + (1 / 4 - Real.log Real.pi / 2) := by
      rw [hS]
      exact re_logDeriv_GammaR_at (5 / 2 : ℝ) T (by norm_num) (by norm_num)
    linarith

/-! ### The real part of `logDeriv (LFunction χ)` at `Re s ≥ 3/2` -/

private lemma re_logDeriv_LFunction_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : (3 : ℝ) / 2 ≤ s.re) :
    (logDeriv (LFunction χ) s).re ≤ 4.5 := by
  have hs1 : 1 < s.re := by linarith
  rw [LFunction_logDeriv_eq_neg_LSeries_vonMangoldt χ hs1]
  set f : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ) with hf
  have hterm : ∀ n : ℕ, ‖LSeries.term f s n‖ ≤ logDivPow n := by
    intro n
    rw [LSeries.norm_term_eq]
    rcases eq_or_ne n 0 with hn | hn
    · subst hn
      simp [logDivPow]
    · rw [if_neg hn]
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have hposn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hnormχ : ‖(χ (n : ZMod N) : ℂ)‖ ≤ 1 := χ.norm_le_one _
      have hΛnonneg : (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt n :=
        ArithmeticFunction.vonMangoldt_nonneg
      have hfn : ‖f n‖ ≤ Real.log (n : ℝ) := by
        have h1 : ‖f n‖ =
            (ArithmeticFunction.vonMangoldt n : ℝ) * ‖(χ (n : ZMod N) : ℂ)‖ := by
          rw [hf, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΛnonneg]
        calc ‖f n‖ = (ArithmeticFunction.vonMangoldt n : ℝ) * ‖(χ (n : ZMod N) : ℂ)‖ := h1
          _ ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * 1 :=
              mul_le_mul_of_nonneg_left hnormχ hΛnonneg
          _ = (ArithmeticFunction.vonMangoldt n : ℝ) := mul_one _
          _ ≤ Real.log (n : ℝ) := ArithmeticFunction.vonMangoldt_le_log
      have hpow : (n : ℝ) ^ ((3 : ℝ) / 2) ≤ (n : ℝ) ^ s.re :=
        Real.rpow_le_rpow_of_exponent_le hn1 hs
      have hpowpos : (0 : ℝ) < (n : ℝ) ^ s.re := Real.rpow_pos_of_pos hposn _
      have hstep1 : ‖f n‖ / (n : ℝ) ^ s.re ≤ Real.log (n : ℝ) / (n : ℝ) ^ s.re :=
        div_le_div_of_nonneg_right hfn hpowpos.le
      have hstep2 : Real.log (n : ℝ) / (n : ℝ) ^ s.re ≤ Real.log (n : ℝ) / (n : ℝ) ^ ((3:ℝ)/2) :=
        div_le_div_of_nonneg_left (Real.log_nonneg hn1) (Real.rpow_pos_of_pos hposn _) hpow
      exact le_trans hstep1 (by simpa [logDivPow] using hstep2)
  have hsum_term : Summable (fun n : ℕ => ‖LSeries.term f s n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm summable_logDivPow
  have hbound : ‖LSeries f s‖ ≤ (4.5 : ℝ) := by
    calc ‖LSeries f s‖ = ‖∑' n : ℕ, LSeries.term f s n‖ := rfl
      _ ≤ ∑' n : ℕ, ‖LSeries.term f s n‖ := norm_tsum_le_tsum_norm hsum_term
      _ ≤ ∑' n : ℕ, logDivPow n := Summable.tsum_le_tsum hterm hsum_term summable_logDivPow
      _ ≤ 4.5 := tsum_logDivPow_le
  have h1 : (-LSeries f s).re ≤ ‖LSeries f s‖ := by
    rw [Complex.neg_re]
    linarith [neg_le_abs (LSeries f s).re, Complex.abs_re_le_norm (LSeries f s)]
  linarith

/-! ### The main bound -/

theorem re_logDeriv_completedLFunction_three_halves {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (T : ℝ) :
    (logDeriv (DirichletCharacter.completedLFunction χ) ((3 / 2 : ℂ) + Complex.I * (T : ℂ))).re
      ≤ (1 / 2) * Real.log (2 + |T|) + 5 := by
  have hre : ((3 / 2 : ℂ) + Complex.I * (T : ℂ)).re = 3 / 2 := by
    rw [Complex.add_re, Complex.mul_re]; simp
  have hpos : 0 < ((3 / 2 : ℂ) + Complex.I * (T : ℂ)).re := by rw [hre]; norm_num
  have hLs : DirichletCharacter.LFunction χ ((3 / 2 : ℂ) + Complex.I * (T : ℂ)) ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by rw [hre]; norm_num)
  rw [logDeriv_completedLFunction_eq_add χ hχ _ hpos hLs]
  have hL := re_logDeriv_LFunction_le χ (s := (3 / 2 : ℂ) + Complex.I * (T : ℂ)) (by rw [hre])
  have hγ := re_logDeriv_gammaFactor_three_halves_le χ T
  rw [Complex.add_re]
  linarith

end Commons.NumberTheory.DirichletCharacter
