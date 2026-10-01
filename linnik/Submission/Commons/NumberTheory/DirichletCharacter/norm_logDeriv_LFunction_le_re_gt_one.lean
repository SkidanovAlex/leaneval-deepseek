import Mathlib.Analysis.SumIntegralComparisons
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_logDeriv_eq_neg_LSeries_vonMangoldt

open scoped LSeries.notation
open MeasureTheory

namespace Commons.NumberTheory.DirichletCharacter

/-!
# Uniform bound for the logarithmic derivative of a Dirichlet L-function

For `1 < Re s ≤ 2` we prove the completely explicit bound

    ‖ (L(·,χ))′/L(·,χ) (s) ‖ ≤ 100 / (Re s − 1)² + 100,

uniformly in the modulus `N` and the character `χ`.

The proof uses the von Mangoldt expansion on `Re s > 1`

    (logDeriv L(·,χ))(s) = − ∑_n Λ(n)χ(n) n^{−s}

together with `‖χ(n)‖ ≤ 1` and `Λ(n) ≥ 0`, which dominates the norm by the real sum
`∑_n Λ(n) n^{−σ}`, `σ = Re s`.  Since `Λ(n) ≤ log n` and `log n ≤ 2 (σ − 1)⁻¹ n^{(σ−1)/2}`,
the latter sum is at most `2/(σ−1) + 4/(σ−1)²`, which is `≤ 100/(σ−1)² + 100` on `σ ≤ 2`.
-/

/-- The real majorant `Λ(n)·n^{-σ}` is summable for `σ > 1`. -/
private lemma summable_vonMangoldt_mul_rpow_neg (σ : ℝ) (hσ : 1 < σ) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ)) := by
  have h := (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (σ : ℂ))
    (by simpa using hσ)).norm
  refine h.congr (fun n => ?_)
  rw [LSeries.norm_term_eq]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [if_neg hn, Complex.ofReal_re,
      Complex.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      Real.rpow_neg (Nat.cast_nonneg n) σ, div_eq_mul_inv]

/-- **Norm bound for the twisted von Mangoldt series.**  For `Re s > 1`,

    ‖ logDeriv (L(·,χ)) s ‖ ≤ ∑_n Λ(n) n^{-Re s}. -/
private lemma norm_logDeriv_LFunction_le_tsum {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    ‖logDeriv (DirichletCharacter.LFunction χ) s‖ ≤
      ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-s.re) := by
  rw [LFunction_logDeriv_eq_neg_LSeries_vonMangoldt χ hs, norm_neg]
  have hfsumm : LSeriesSummable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
      (χ (n : ZMod N) : ℂ)) s := by
    have hg : LSeriesSummable
        ((fun n : ℕ => (χ (n : ZMod N) : ℂ)) *
          fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) s :=
      DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs
    refine (LSeriesSummable_congr s (f := fun n : ℕ =>
        (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ))
      (g := (fun n : ℕ => (χ (n : ZMod N) : ℂ)) *
        fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) ?_).mpr hg
    intro n _
    simp only [Pi.mul_apply]
    ring
  have hsummN : Summable (fun n : ℕ =>
      ‖LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
        (χ (n : ZMod N) : ℂ)) s n‖) := hfsumm.norm
  have hterm : ∀ n : ℕ, ‖LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
        (χ (n : ZMod N) : ℂ)) s n‖ ≤
      (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-s.re) := by
    intro n
    rcases eq_or_ne n 0 with hn0 | hn0
    · subst hn0; simp [LSeries.term_zero]
    · rw [LSeries.norm_term_eq, if_neg hn0]
      have hnormχ : ‖(χ (n : ZMod N) : ℂ)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
      have hΛnn : (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt n :=
        ArithmeticFunction.vonMangoldt_nonneg
      have hmul : ‖(ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ)‖
          ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := by
        rw [norm_mul, Complex.norm_of_nonneg hΛnn]
        exact mul_le_of_le_one_right hΛnn hnormχ
      have hpow : (0 : ℝ) ≤ (n : ℝ) ^ s.re := Real.rpow_nonneg (Nat.cast_nonneg n) _
      calc ‖(ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ)‖ / (n : ℝ) ^ s.re
          ≤ (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ s.re :=
            div_le_div_of_nonneg_right hmul hpow
        _ = (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-s.re) := by
            rw [Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
  calc ‖LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
          (χ (n : ZMod N) : ℂ)) s‖
      ≤ ∑' n : ℕ, ‖LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
          (χ (n : ZMod N) : ℂ)) s n‖ := norm_tsum_le_tsum_norm hsummN
    _ ≤ ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-s.re) :=
        Summable.tsum_le_tsum hterm hsummN (summable_vonMangoldt_mul_rpow_neg s.re hs)

/-- The real `p`-series, `p > 1`:  `∑_{n ≥ 0} n^{-p} ≤ 1 + 1/(p−1)`. -/
private lemma tsum_nat_rpow_neg_le (p : ℝ) (hp : 1 < p) :
    (∑' n : ℕ, (n : ℝ) ^ (-p)) ≤ 1 + 1 / (p - 1) := by
  set f : ℝ → ℝ := fun x => x ^ (-p) with hf
  have hp1 : (-p) < -1 := by linarith
  have hanti : AntitoneOn f (Set.Ici (((1 : ℕ) : ℝ))) := by
    intro a ha b _ hab
    have ha1 : (0 : ℝ) < a := by
      have := Set.mem_Ici.mp ha; simp only [Nat.cast_one] at this; linarith
    exact Real.rpow_le_rpow_of_nonpos ha1 hab (by linarith)
  have hint : IntegrableOn f (Set.Ioi (((1 : ℕ) : ℝ))) :=
    integrableOn_Ioi_rpow_of_lt hp1 (by norm_num)
  have hnonneg : ∀ t ∈ Set.Ioi (((1 : ℕ) : ℝ)), 0 ≤ f t := by
    intro t ht
    exact Real.rpow_nonneg
      (by have := Set.mem_Ioi.mp ht; simp only [Nat.cast_one] at this; linarith) _
  have hb := AntitoneOn.tsum_comp_add_le_integral (f := f) 1 hanti hint hnonneg
  have hiv : ∫ x in Set.Ioi (((1 : ℕ) : ℝ)), f x = 1 / (p - 1) := by
    simp only [hf]
    rw [integral_Ioi_rpow_of_lt hp1 (by norm_num : (0 : ℝ) < (((1 : ℕ) : ℝ))),
      show ((((1 : ℕ) : ℝ))) = 1 by norm_num, Real.one_rpow]
    rw [show -p + 1 = -(p - 1) by ring]
    field_simp
  have hsumm : Summable (fun n : ℕ => f n) := by
    simpa [hf] using Real.summable_nat_rpow.mpr hp1
  have hf0 : f (0 : ℝ) = 0 := by
    simp only [hf]; exact Real.zero_rpow (by linarith : -p ≠ 0)
  have hf1 : f (1 : ℝ) = 1 := by simp [hf]
  have hrange : ∑ i ∈ Finset.range 2, f i = 1 := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    have h0 : f (((0 : ℕ) : ℝ)) = 0 := by simpa using hf0
    have h1 : f (((1 : ℕ) : ℝ)) = 1 := by simpa using hf1
    rw [h0, h1]; norm_num
  have hsplit : ∑' n : ℕ, f n = (∑ i ∈ Finset.range 2, f i) + ∑' i : ℕ, f ((i + 2 : ℕ) : ℝ) :=
    (hsumm.sum_add_tsum_nat_add 2).symm
  have hb' : ∑' i : ℕ, f ((i + 2 : ℕ) : ℝ) ≤ ∫ x in Set.Ioi (((1 : ℕ) : ℝ)), f x := by
    have heq : (∑' (n : ℕ), f ↑(n + 1 + 1)) = ∑' (i : ℕ), f ((i + 2 : ℕ) : ℝ) := by
      apply tsum_congr; intro n
      congr 1
    rwa [heq] at hb
  calc (∑' n : ℕ, f n)
      = (∑ i ∈ Finset.range 2, f i) + ∑' i : ℕ, f ↑(i + 2) := hsplit
    _ = 1 + ∑' i : ℕ, f ↑(i + 2) := by rw [hrange]
    _ ≤ 1 + 1 / (p - 1) := by
        have hle : ∑' i : ℕ, f ↑(i + 2) ≤ 1 / (p - 1) := hb'.trans hiv.le
        linarith

/-- For `1 < σ`, the von Mangoldt sum is at most `2/(σ−1) + 4/(σ−1)²`. -/
private lemma tsum_vonMangoldt_mul_rpow_neg_le (σ : ℝ) (hσ : 1 < σ) :
    (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ)) ≤
      2 / (σ - 1) + 4 / (σ - 1) ^ 2 := by
  set c : ℝ := 2 / (σ - 1) with hc
  set p : ℝ := (σ + 1) / 2 with hp
  have hp1 : 1 < p := by rw [hp]; linarith
  have hpne : -p ≠ 0 := by linarith
  have hcnonneg : 0 ≤ c := by rw [hc]; positivity
  have hg_summ : Summable (fun n : ℕ => c * (n : ℝ) ^ (-p)) :=
    (Real.summable_nat_rpow.mpr (by linarith : -p < -1)).mul_left c
  have hpoint : ∀ n : ℕ,
      (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) ≤ c * (n : ℝ) ^ (-p) := by
    intro n
    rcases eq_or_ne n 0 with hn0 | hn0
    · subst hn0
      have h0 : (ArithmeticFunction.vonMangoldt 0 : ℝ) = 0 := by
        rw [ArithmeticFunction.vonMangoldt_apply]; simp [not_isPrimePow_zero]
      rw [h0, Nat.cast_zero, Real.zero_rpow (by linarith : -σ ≠ 0), Real.zero_rpow hpne,
        mul_zero, mul_zero]
    · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
      have hε : 0 < (σ - 1) / 2 := by linarith
      have hlog : Real.log (n : ℝ) ≤ c * (n : ℝ) ^ ((σ - 1) / 2) := by
        have h := Real.log_le_rpow_div (x := (n : ℝ)) (ε := (σ - 1) / 2)
          (le_of_lt hnpos) hε
        rw [div_eq_mul_inv] at h
        rw [hc]
        calc Real.log (n : ℝ) ≤ (n : ℝ) ^ ((σ - 1) / 2) * ((σ - 1) / 2)⁻¹ := h
          _ = (2 / (σ - 1)) * (n : ℝ) ^ ((σ - 1) / 2) := by
              rw [inv_div]; ring
      calc (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ)
          ≤ Real.log (n : ℝ) * (n : ℝ) ^ (-σ) :=
            mul_le_mul_of_nonneg_right ArithmeticFunction.vonMangoldt_le_log
              (Real.rpow_nonneg (Nat.cast_nonneg n) _)
        _ ≤ (c * (n : ℝ) ^ ((σ - 1) / 2)) * (n : ℝ) ^ (-σ) :=
            mul_le_mul_of_nonneg_right hlog (Real.rpow_nonneg (Nat.cast_nonneg n) _)
        _ = c * (n : ℝ) ^ (-p) := by
            rw [mul_assoc, ← Real.rpow_add hnpos,
              show (σ - 1) / 2 + (-σ) = -p by rw [hp]; ring]
  have hf_summ : Summable (fun n : ℕ =>
      (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ)) :=
    Summable.of_nonneg_of_le
      (fun n => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (Real.rpow_nonneg (Nat.cast_nonneg n) _)) hpoint hg_summ
  calc (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ))
      ≤ ∑' n : ℕ, c * (n : ℝ) ^ (-p) := Summable.tsum_le_tsum hpoint hf_summ hg_summ
    _ = c * ∑' n : ℕ, (n : ℝ) ^ (-p) := tsum_mul_left
    _ ≤ c * (1 + 1 / (p - 1)) :=
        mul_le_mul_of_nonneg_left (tsum_nat_rpow_neg_le p hp1) hcnonneg
    _ = 2 / (σ - 1) + 4 / (σ - 1) ^ 2 := by
        have hσne : σ - 1 ≠ 0 := by linarith
        have hp' : 1 / (p - 1) = 2 / (σ - 1) := by
          rw [hp, show (σ + 1) / 2 - 1 = (σ - 1) / 2 by ring, one_div, inv_div]
        rw [hp', hc]
        field_simp
        ring

theorem norm_logDeriv_LFunction_le_re_gt_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs1 : 1 < s.re) (hs2 : s.re ≤ 2) :
    ‖logDeriv (DirichletCharacter.LFunction χ) s‖ ≤ 100 / (s.re - 1) ^ 2 + 100 := by
  have h1 := norm_logDeriv_LFunction_le_tsum χ hs1
  have h2 := tsum_vonMangoldt_mul_rpow_neg_le s.re hs1
  have hx0 : 0 < s.re - 1 := by linarith
  have h3 : 2 / (s.re - 1) + 4 / (s.re - 1) ^ 2 ≤ 100 / (s.re - 1) ^ 2 + 100 := by
    have hnum : 2 * (s.re - 1) + 4 ≤ 100 + 100 * (s.re - 1) ^ 2 := by
      nlinarith [sq_nonneg (s.re - 1), hs2]
    have hden : (0 : ℝ) < (s.re - 1) ^ 2 := pow_pos hx0 2
    have e1 : 2 / (s.re - 1) + 4 / (s.re - 1) ^ 2
        = (2 * (s.re - 1) + 4) / (s.re - 1) ^ 2 := by field_simp
    have e2 : 100 / (s.re - 1) ^ 2 + 100
        = (100 + 100 * (s.re - 1) ^ 2) / (s.re - 1) ^ 2 := by field_simp
    rw [e1, e2]
    exact div_le_div_of_nonneg_right hnum (le_of_lt hden)
  linarith [h1, h2, h3]

end Commons.NumberTheory.DirichletCharacter