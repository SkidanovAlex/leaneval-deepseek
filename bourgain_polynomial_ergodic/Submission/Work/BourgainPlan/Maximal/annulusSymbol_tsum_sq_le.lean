import Mathlib
import Submission.Work.BourgainPlan.Maximal.annulusSymbolDefs

/-!
# Uniform bound and ℓ²-summability of an annulus symbol family

Let `b` be an annulus symbol family in the sense of `AnnulusSymbolSmooth`: `b m` lives at
frequency scale `2^{-m}` (`2⁻¹ < |2^m ξ| < 2` on its support) and its `k`-th derivative obeys the
scale bound `‖(d/dξ)^k b_m(ξ)‖ ≤ C_k · 2^{m k}`.

This file proves `annulusSymbol_tsum_sq_le`, the two quantitative consequences that every later
estimate in this area uses:

* a **uniform sup bound** `‖b m ξ‖ ≤ C`, which is the case `k = 0` of the derivative bound
  (`iteratedDeriv 0 = id`, and the scale factor `2^{m·0} = 1`);
* **bounded overlap**, i.e. the square sum over the distinguished scale variable,
  `∑'_n ‖b (j+n) ξ‖² ≤ C`: for fixed `ξ ≠ 0` the annulus condition `2⁻¹ < |2^m ξ| < 2` forces
  `2^{m'} / 2^m < 4` for any two admissible levels `m < m'`, hence `m' - m ≤ 1`; the admissible
  levels therefore lie in a window of three consecutive integers and only boundedly many (at most
  two) of the terms `b (j+n) ξ` can be non-zero.  This is exactly the "genuine square function"
  property that turns `∑_n |U_n S_{j+n} f|²` into a sum over a constant number of scales rather
  than a `√N`-loss.

The constant produced is `C₀ + 3 C₀²` where `C₀` is the `k = 0` derivative bound of `b`.
-/

open scoped BigOperators ENNReal

namespace Work.BourgainPlan.Maximal

/-- **Bounded overlap / separation of the annulus levels.**  Two levels `m < m'` at which `b`
does not vanish are at distance at most one: the annulus condition gives
`(2^{m'} |ξ|) / (2^m |ξ|) < 2 / (1/2) = 4`, i.e. `2^{m'-m} < 4`, so `m' - m ≤ 1`. -/
lemma annulus_level_close (b : ℤ → ℝ → ℂ) (hb : AnnulusSymbolSmooth b) {ξ : ℝ}
    {m m' : ℤ} (hm : b m ξ ≠ 0) (hm' : b m' ξ ≠ 0) :
    m' - m ≤ 1 := by
  obtain ⟨hlo_m, hhi_m⟩ := hb.1 m ξ hm
  obtain ⟨hlo_m', hhi_m'⟩ := hb.1 m' ξ hm'
  have h2m : 0 < (2:ℝ)^m := zpow_pos (by norm_num) m
  have h2m' : 0 < (2:ℝ)^m' := zpow_pos (by norm_num) m'
  rw [abs_mul, abs_of_pos h2m] at hlo_m hhi_m
  rw [abs_mul, abs_of_pos h2m'] at hlo_m' hhi_m'
  by_contra hcon
  push Not at hcon
  have hge : (2:ℤ) ≤ m' - m := by omega
  have hpow : (2:ℝ)^2 ≤ (2:ℝ)^(m'-m) :=
    zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2) hge
  have hpow4 : (4:ℝ) ≤ (2:ℝ)^(m'-m) := by
    rw [show (2:ℝ)^2 = 4 from by norm_num] at hpow; exact hpow
  have hprod : (2:ℝ)^(m'-m) * ((2:ℝ)^m * |ξ|) = (2:ℝ)^m' * |ξ| := by
    rw [← mul_assoc, ← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0), sub_add_cancel]
  have h2 : (2:ℝ) ≤ (2:ℝ)^(m'-m) * ((2:ℝ)^m * |ξ|) := by
    calc (2:ℝ) = 4 * (2:ℝ)⁻¹ := by norm_num
      _ ≤ (2:ℝ)^(m'-m) * ((2:ℝ)^m * |ξ|) :=
          mul_le_mul hpow4 (le_of_lt hlo_m) (by norm_num) (by positivity)
  rw [hprod] at h2
  linarith

theorem annulusSymbol_tsum_sq_le (b : ℤ → ℝ → ℂ)
    (hb : Work.BourgainPlan.Maximal.AnnulusSymbolSmooth b) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ (m : ℤ) (ξ : ℝ), ‖b m ξ‖ₑ ≤ ENNReal.ofReal C) ∧
      (∀ (j : ℤ) (ξ : ℝ), ∑' n : ℤ, ‖b (j + n) ξ‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal C) := by
  obtain ⟨C₀, hC₀, hC₀b⟩ := hb.2 0
  -- the `k = 0` derivative bound is a uniform sup bound
  have hb0 : ∀ m ξ, ‖b m ξ‖ ≤ C₀ := by
    intro m ξ
    have h := hC₀b m ξ
    simpa using h
  refine ⟨C₀ + 3 * C₀^2, by nlinarith [sq_nonneg C₀], ?_, ?_⟩
  · intro m ξ
    rw [← ofReal_norm]
    exact le_trans (ENNReal.ofReal_le_ofReal (hb0 m ξ))
      (ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg C₀]))
  · intro j ξ
    have hterm : ∀ n : ℤ, ‖b (j+n) ξ‖ₑ ^ (2:ℝ) ≤ ENNReal.ofReal (C₀^2) := by
      intro n
      have h1 : ‖b (j+n) ξ‖ₑ ≤ ENNReal.ofReal C₀ := by
        rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hb0 (j+n) ξ)
      rw [show ‖b (j+n) ξ‖ₑ ^ (2:ℝ) = ‖b (j+n) ξ‖ₑ ^ (2:ℕ) from
        ENNReal.rpow_natCast _ 2]
      calc ‖b (j+n) ξ‖ₑ ^ 2 ≤ (ENNReal.ofReal C₀) ^ 2 := pow_le_pow_left' h1 2
        _ = ENNReal.ofReal (C₀^2) := (ENNReal.ofReal_pow hC₀ 2).symm
    by_cases hex : ∃ m : ℤ, b m ξ ≠ 0
    · -- the non-zero levels all lie in the three-integer window `m₀ - 1 ≤ m ≤ m₀ + 1`
      obtain ⟨m₀, hm₀⟩ := hex
      set s := Finset.Icc (m₀ - 1 - j) (m₀ + 1 - j) with hs
      have hmem : ∀ n : ℤ, b (j+n) ξ ≠ 0 → n ∈ s := by
        intro n hn
        have h1 : (j + n) - m₀ ≤ 1 := annulus_level_close b hb (m := m₀) (m' := j+n) hm₀ hn
        have h2 : m₀ - (j + n) ≤ 1 := annulus_level_close b hb (m := j+n) (m' := m₀) hn hm₀
        rw [hs, Finset.mem_Icc]
        constructor <;> omega
      have hsuff : ∀ n ∉ s, ‖b (j+n) ξ‖ₑ ^ (2:ℝ) = 0 := by
        intro n hn
        have hzero : b (j+n) ξ = 0 := by
          by_contra hne
          exact hn (hmem n hne)
        rw [hzero, enorm_zero, ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ) < 2)]
      have hcard : s.card = 3 := by
        rw [hs, Int.card_Icc]
        have h3 : (m₀ + 1 - j + 1 - (m₀ - 1 - j) : ℤ) = 3 := by ring
        rw [h3]
        decide
      have h3c : ((3:ℕ) : ENNReal) = ENNReal.ofReal 3 := by norm_num
      calc ∑' n : ℤ, ‖b (j+n) ξ‖ₑ ^ (2:ℝ)
          = ∑ n ∈ s, ‖b (j+n) ξ‖ₑ ^ (2:ℝ) := tsum_eq_sum hsuff
        _ ≤ ∑ n ∈ s, ENNReal.ofReal (C₀^2) := Finset.sum_le_sum (fun n _ => hterm n)
        _ ≤ ENNReal.ofReal 3 * ENNReal.ofReal (C₀^2) := by
              rw [Finset.sum_const, nsmul_eq_mul, hcard, h3c]
        _ = ENNReal.ofReal (3 * C₀^2) := by
              rw [← ENNReal.ofReal_mul (show (0:ℝ) ≤ (3:ℝ) by norm_num)]
        _ ≤ ENNReal.ofReal (C₀ + 3 * C₀^2) :=
              ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg C₀])
    · -- if `b` vanishes identically at `ξ` the series is zero
      push Not at hex
      have hzero : ∀ n : ℤ, ‖b (j+n) ξ‖ₑ ^ (2:ℝ) = 0 := by
        intro n
        rw [hex (j+n), enorm_zero, ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ) < 2)]
      rw [tsum_eq_sum (s := (∅ : Finset ℤ)) (fun n _ => hzero n)]
      simp

end Work.BourgainPlan.Maximal
