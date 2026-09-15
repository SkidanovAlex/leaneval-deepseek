import Mathlib.Analysis.SumIntegralComparisons
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_logDeriv_eq_neg_LSeries_vonMangoldt

/-!
# The logarithmic derivative of a Dirichlet L-function is bounded for `Re s ≥ 3/2`

For `Re s > 1` the logarithmic derivative of `L(·, χ)` is (minus) the `L`-series of the
twist of the von Mangoldt function by `χ`
(`LFunction_logDeriv_eq_neg_LSeries_vonMangoldt`):

  `L'/L (s, χ) = - ∑_{n} Λ(n) χ(n) n^{-s}`.

On the half-plane `Re s ≥ 3/2` the right hand side is dominated, uniformly in `χ` and `s`,
by the convergent positive series `∑_{n} Λ(n) n^{-3/2}`, which in turn is at most `20`
(Λ(n) ≤ log n ≤ 4 n^{1/4}, so `Λ(n) n^{-3/2} ≤ 4 n^{-5/4}`, and `∑ n^{-5/4} ≤ 1 + 4 = 5`).
-/

open scoped LSeries.notation
open MeasureTheory Set Filter

namespace Commons.NumberTheory.DirichletCharacter

/-- An explicit bound for the convergent `p`-series: for `1 < p`,
`∑' n, n^{-p} ≤ 1 + (p - 1)⁻¹`.  (The sum from `n = 2` on is compared with the integral
`∫_1^∞ x^{-p} dx = 1/(p-1)`.) -/
private lemma tsum_nat_rpow_neg_le {p : ℝ} (hp : 1 < p) :
    ∑' n : ℕ, (n : ℝ) ^ (-p) ≤ 1 + (p - 1)⁻¹ := by
  have hne : (-p : ℝ) ≠ 0 := by linarith
  have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (-p)) :=
    Real.summable_nat_rpow.mpr (by linarith : -p < -1)
  have hcmp : ∑' n : ℕ, (((n + 2 : ℕ)) : ℝ) ^ (-p) ≤ (p - 1)⁻¹ := by
    have hanti : AntitoneOn (fun x : ℝ => x ^ (-p)) (Set.Ici ((1:ℕ) : ℝ)) :=
      (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith : -p ≤ 0)).mono (by
        intro x hx
        exact lt_of_lt_of_le (by norm_num : (0:ℝ) < ((1:ℕ):ℝ)) hx)
    have hint : IntegrableOn (fun x : ℝ => x ^ (-p)) (Set.Ioi ((1:ℕ) : ℝ)) :=
      integrableOn_Ioi_rpow_of_lt (by linarith : -p < -1) (by norm_num)
    have hnonneg : ∀ t ∈ Set.Ioi ((1:ℕ):ℝ), 0 ≤ t ^ (-p) := by
      intro t ht
      exact Real.rpow_nonneg (le_of_lt (lt_trans (by norm_num : (0:ℝ) < ((1:ℕ):ℝ)) ht)) _
    have h1 : ∑' n : ℕ, (((n + 1 + 1 : ℕ)) : ℝ) ^ (-p)
        ≤ ∫ x : ℝ in Set.Ioi ((1:ℕ):ℝ), x ^ (-p) :=
      AntitoneOn.tsum_comp_add_le_integral (N := 1) hanti hint hnonneg
    have h2 : (∑' n : ℕ, (((n + 2 : ℕ)) : ℝ) ^ (-p))
        = ∑' n : ℕ, (((n + 1 + 1 : ℕ)) : ℝ) ^ (-p) :=
      tsum_congr (fun n => by congr 1)
    have h3 : (∫ x : ℝ in Set.Ioi ((1:ℕ):ℝ), x ^ (-p)) = (p - 1)⁻¹ := by
      rw [integral_Ioi_rpow_of_lt (by linarith : -p < -1) (c := ((1:ℕ):ℝ)) (by norm_num)]
      rw [show (((1:ℕ):ℝ)) ^ (-p + 1) = 1 by norm_num]
      have h1 : -p + 1 = -(p-1) := by ring
      rw [h1]
      field_simp
    rw [h2, h3] at h1
    exact h1
  have hstep : ∑' n : ℕ, (n : ℝ) ^ (-p) = 1 + ∑' n : ℕ, (((n + 2 : ℕ)) : ℝ) ^ (-p) := by
    rw [hsum.tsum_eq_zero_add]
    have h0 : (((0:ℕ)) : ℝ) ^ (-p) = 0 := by simpa using Real.zero_rpow (x := (-p)) hne
    rw [h0, zero_add]
    have hsum1 : Summable (fun n : ℕ => (((n + 1 : ℕ)) : ℝ) ^ (-p)) :=
      (summable_nat_add_iff 1).mpr hsum
    rw [hsum1.tsum_eq_zero_add]
    have h1v : (((0 + 1 : ℕ)) : ℝ) ^ (-p) = 1 := by norm_num
    rw [h1v]
  rw [hstep]
  linarith

/-- `log x ≤ 4 x^{1/4}` for `x ≥ 1`. -/
private lemma log_le_four_rpow {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ≤ 4 * x ^ ((1:ℝ)/4) := by
  have h := Real.log_le_rpow_div (x := x) (by linarith) (by norm_num : (0:ℝ) < 1/4)
  have hdiv : x ^ ((1:ℝ)/4) / ((1:ℝ)/4) = 4 * x ^ ((1:ℝ)/4) := by
    rw [div_eq_mul_inv, show (((1:ℝ)/4))⁻¹ = 4 by norm_num, mul_comm]
  linarith [hdiv ▸ h]

/-- The `L`-series of the von Mangoldt function is bounded by `20` on the half-plane `σ ≥ 3/2`:
`∑' n, Λ(n) n^{-σ} ≤ 20`. -/
private lemma tsum_vonMangoldt_le (σ : ℝ) (hσ : (3:ℝ)/2 ≤ σ) :
    ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) ≤ 20 := by
  have hG : Summable (fun n : ℕ => 4 * ((n : ℝ) ^ (-(5:ℝ)/4))) :=
    (Real.summable_nat_rpow.mpr (by norm_num : (-(5:ℝ)/4) < -1)).mul_left 4
  have hle : ∀ n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ)
      ≤ 4 * ((n : ℝ) ^ (-(5:ℝ)/4)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp [Real.zero_rpow (by norm_num : (-(5:ℝ)/4) ≠ 0)]
    · have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
      have hposn : (0:ℝ) < n := by exact_mod_cast hn
      have hlog : (ArithmeticFunction.vonMangoldt n : ℝ) ≤ Real.log (n:ℝ) :=
        ArithmeticFunction.vonMangoldt_le_log
      have hlog2 : Real.log (n:ℝ) ≤ 4 * (n:ℝ) ^ ((1:ℝ)/4) := log_le_four_rpow hn1
      have hpow : (n:ℝ) ^ (-σ) ≤ (n:ℝ) ^ (-(3:ℝ)/2) :=
        Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
      have h1 : (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ)
          ≤ Real.log (n:ℝ) * (n:ℝ) ^ (-σ) :=
        mul_le_mul_of_nonneg_right hlog (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      have h2 : Real.log (n:ℝ) * (n:ℝ) ^ (-σ)
          ≤ 4 * (n:ℝ) ^ ((1:ℝ)/4) * (n:ℝ) ^ (-σ) :=
        mul_le_mul_of_nonneg_right hlog2 (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      have h3 : 4 * (n:ℝ) ^ ((1:ℝ)/4) * (n:ℝ) ^ (-σ)
          ≤ 4 * (n:ℝ) ^ ((1:ℝ)/4) * (n:ℝ) ^ (-(3:ℝ)/2) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      have hrw : 4 * (n:ℝ) ^ ((1:ℝ)/4) * (n:ℝ) ^ (-(3:ℝ)/2) = 4 * (n:ℝ) ^ (-(5:ℝ)/4) := by
        rw [mul_assoc, ← Real.rpow_add hposn]
        norm_num
      linarith
  have hH : Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ)) :=
    Summable.of_nonneg_of_le
      (fun n => mul_nonneg (by exact_mod_cast ArithmeticFunction.vonMangoldt_nonneg)
        (Real.rpow_nonneg (Nat.cast_nonneg n) _)) hle hG
  have hfin : ∑' n : ℕ, 4 * ((n : ℝ) ^ (-(5:ℝ)/4)) ≤ 20 := by
    rw [tsum_mul_left]
    have hp := tsum_nat_rpow_neg_le (p := (5:ℝ)/4) (by norm_num)
    have h : (∑' n : ℕ, (n : ℝ) ^ (-((5:ℝ)/4))) ≤ 5 := by
      have h5 : (1:ℝ) + ((5:ℝ)/4 - 1)⁻¹ = 5 := by norm_num
      linarith [h5 ▸ hp]
    linarith
  calc ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ)
      ≤ ∑' n : ℕ, 4 * ((n : ℝ) ^ (-(5:ℝ)/4)) :=
        Summable.tsum_le_tsum hle hH hG
    _ ≤ 20 := hfin

/-- For a Dirichlet character `χ` mod `N` and `s` with `3/2 ≤ Re s`, the logarithmic
derivative of `L(·, χ)` is bounded by `20`. -/
theorem logDeriv_LFunction_re_ge_three_halves_bound {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : (3 : ℝ) / 2 ≤ s.re) :
    ‖logDeriv (DirichletCharacter.LFunction χ) s‖ ≤ 20 := by
  have hs1 : 1 < s.re := lt_of_lt_of_le (by norm_num) hs
  rw [LFunction_logDeriv_eq_neg_LSeries_vonMangoldt χ hs1, norm_neg]
  set f : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ) with hf
  have hG : Summable (fun n : ℕ => 4 * ((n : ℝ) ^ (-(5:ℝ)/4))) :=
    (Real.summable_nat_rpow.mpr (by norm_num : (-(5:ℝ)/4) < -1)).mul_left 4
  have hterm : ∀ n : ℕ, ‖LSeries.term f s n‖ ≤ 4 * ((n : ℝ) ^ (-(5:ℝ)/4)) := by
    intro n
    rw [LSeries.norm_term_eq]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp [Real.zero_rpow (by norm_num : (-(5:ℝ)/4) ≠ 0)]
    · rw [if_neg (Nat.pos_iff_ne_zero.mp hn)]
      have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
      have hposn : (0:ℝ) < n := by exact_mod_cast hn
      have hnormΛ : ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)‖
          = (ArithmeticFunction.vonMangoldt n : ℝ) := by
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      have hfn : ‖f n‖ ≤ Real.log (n:ℝ) := by
        have h1 : ‖f n‖ = (ArithmeticFunction.vonMangoldt n : ℝ) * ‖(χ (n : ZMod N) : ℂ)‖ := by
          rw [hf, norm_mul, hnormΛ]
        have h2 : ‖(χ (n : ZMod N) : ℂ)‖ ≤ 1 := χ.norm_le_one _
        calc ‖f n‖ = (ArithmeticFunction.vonMangoldt n : ℝ) * ‖(χ (n : ZMod N) : ℂ)‖ := h1
          _ ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * 1 :=
              mul_le_mul_of_nonneg_left h2 (by exact_mod_cast ArithmeticFunction.vonMangoldt_nonneg)
          _ = (ArithmeticFunction.vonMangoldt n : ℝ) := mul_one _
          _ ≤ Real.log (n:ℝ) := ArithmeticFunction.vonMangoldt_le_log
      have hlog2 : Real.log (n:ℝ) ≤ 4 * (n:ℝ) ^ ((1:ℝ)/4) := log_le_four_rpow hn1
      have hpow : (n:ℝ) ^ ((3:ℝ)/2) ≤ (n:ℝ) ^ (s.re) :=
        Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
      have hpowpos : (0:ℝ) < (n:ℝ) ^ (s.re) := Real.rpow_pos_of_pos hposn _
      have hstep1 : ‖f n‖ / (n:ℝ) ^ s.re ≤ Real.log (n:ℝ) / (n:ℝ) ^ ((3:ℝ)/2) := by
        have ha : ‖f n‖ / (n:ℝ) ^ s.re ≤ Real.log (n:ℝ) / (n:ℝ) ^ s.re :=
          div_le_div_of_nonneg_right hfn (le_of_lt hpowpos)
        have hb : Real.log (n:ℝ) / (n:ℝ) ^ s.re ≤ Real.log (n:ℝ) / (n:ℝ) ^ ((3:ℝ)/2) :=
          div_le_div_of_nonneg_left (Real.log_nonneg hn1) (Real.rpow_pos_of_pos hposn _) hpow
        linarith
      have hstep2 : Real.log (n:ℝ) / (n:ℝ) ^ ((3:ℝ)/2)
          ≤ 4 * (n:ℝ) ^ ((1:ℝ)/4) / (n:ℝ) ^ ((3:ℝ)/2) :=
        div_le_div_of_nonneg_right hlog2 (le_of_lt (Real.rpow_pos_of_pos hposn _))
      have hstep3 : 4 * (n:ℝ) ^ ((1:ℝ)/4) / (n:ℝ) ^ ((3:ℝ)/2)
          = 4 * (n:ℝ) ^ (-(5:ℝ)/4) := by
        rw [div_eq_mul_inv, ← Real.rpow_neg (le_of_lt hposn)]
        rw [mul_assoc, ← Real.rpow_add hposn]
        norm_num
      linarith
  have hsum_term : Summable (fun n : ℕ => ‖LSeries.term f s n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hG
  have hfin : ∑' n : ℕ, 4 * ((n : ℝ) ^ (-(5:ℝ)/4)) ≤ 20 := by
    rw [tsum_mul_left]
    have hp := tsum_nat_rpow_neg_le (p := (5:ℝ)/4) (by norm_num)
    have h : (∑' n : ℕ, (n : ℝ) ^ (-((5:ℝ)/4))) ≤ 5 := by
      have h5 : (1:ℝ) + ((5:ℝ)/4 - 1)⁻¹ = 5 := by norm_num
      linarith [h5 ▸ hp]
    linarith
  calc ‖LSeries f s‖ = ‖∑' n : ℕ, LSeries.term f s n‖ := rfl
    _ ≤ ∑' n : ℕ, ‖LSeries.term f s n‖ := norm_tsum_le_tsum_norm hsum_term
    _ ≤ ∑' n : ℕ, 4 * ((n : ℝ) ^ (-(5:ℝ)/4)) :=
        Summable.tsum_le_tsum hterm hsum_term hG
    _ ≤ 20 := hfin

end Commons.NumberTheory.DirichletCharacter