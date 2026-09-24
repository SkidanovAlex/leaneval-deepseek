import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Tail estimate for a dyadic annulus

`Commons.Analysis.Asymptotics.dyadicAnnulusTail` bounds the contribution of a
sequence of weights `b k` living on dyadic annuli of radius about
`2 ^ (k+1) * R`, each `b k ≤ C * 2^(k+1) * R * (log (2^(k+1) * R + 2) + L)`,
against the decreasing weights `M / (4^k * R^2)`.

The proof is a termwise comparison to the summable geometric series
`∑ (k+1) (1/2)^k = 4` and `∑ (1/2)^k = 2`, followed by an elementary
linear estimate.
-/

open scoped BigOperators

namespace Commons.Analysis.Asymptotics

/-- The dyadic weight `2^(k+1) / 4^k` equals `2 / 2^k`. -/
private lemma dyadic_pow_ratio (k : ℕ) : (2 : ℝ) ^ (k + 1) / (4 : ℝ) ^ k = 2 / (2 : ℝ) ^ k := by
  have hk2 : (2 : ℝ) ^ k ≠ 0 := pow_ne_zero k (by norm_num : (2 : ℝ) ≠ 0)
  have hk4 : (4 : ℝ) ^ k ≠ 0 := pow_ne_zero k (by norm_num : (4 : ℝ) ≠ 0)
  field_simp [hk2, hk4]
  calc
    (2 : ℝ) ^ (k + 1) * (2 : ℝ) ^ k = (2 : ℝ) ^ ((k + 1) + k) := by rw [← pow_add]
    _ = (2 : ℝ) ^ (2 * k + 1) := by rw [show ((k + 1) + k : ℕ) = 2 * k + 1 by omega]
    _ = (2 : ℝ) ^ (2 * k) * 2 := by rw [pow_succ]
    _ = 2 * (2 : ℝ) ^ (2 * k) := by rw [mul_comm]
    _ = 2 * ((2 : ℝ) ^ 2) ^ k := by rw [← pow_mul]
    _ = 2 * (4 : ℝ) ^ k := by rw [show (2 : ℝ) ^ 2 = 4 by norm_num]
    _ = (4 : ℝ) ^ k * 2 := by rw [mul_comm]

/-- `(1/2)^k = 1 / 2^k`. -/
private lemma dyadic_half_inv (k : ℕ) : ((1 / 2 : ℝ) ^ k) = 1 / (2 : ℝ) ^ k := by
  exact one_div_pow (2 : ℝ) k

/-- `2 ≤ 2^(k+1)`. -/
private lemma dyadic_two_le_two_pow (k : ℕ) : (2 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by
  have := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ (2 : ℝ)) (by omega : (1 : ℕ) ≤ k + 1)
  simpa using this

/-- Split the logarithm: `log (2^(k+1) R + 2) ≤ (k+1) log 2 + log (R+2)` for `2 ≤ R`. -/
private lemma dyadic_log_split {R : ℝ} (hR : 2 ≤ R) (k : ℕ) :
    Real.log ((2 : ℝ) ^ (k + 1) * R + 2) ≤ (k + 1 : ℝ) * Real.log 2 + Real.log (R + 2) := by
  have h1 : 0 < ((2 : ℝ) ^ (k + 1) * R + 2) := by positivity
  have hle0 : 2 ≤ (2 : ℝ) ^ (k + 1) * 2 := by
    have h4 : (2 : ℝ) * 2 ≤ (2 : ℝ) ^ (k + 1) * 2 :=
      mul_le_mul_of_nonneg_right (dyadic_two_le_two_pow k) (by norm_num : (0 : ℝ) ≤ 2)
    exact le_trans (by norm_num : (2 : ℝ) ≤ 2 * 2) h4
  have hle : (2 : ℝ) ^ (k + 1) * R + 2 ≤ (2 : ℝ) ^ (k + 1) * (R + 2) := by
    calc
      (2 : ℝ) ^ (k + 1) * R + 2 ≤ (2 : ℝ) ^ (k + 1) * R + (2 : ℝ) ^ (k + 1) * 2 :=
        add_le_add_right hle0 ((2 : ℝ) ^ (k + 1) * R)
      _ = (2 : ℝ) ^ (k + 1) * (R + 2) := by ring
  have hlog := Real.log_le_log h1 hle
  have hmul := Real.log_mul (pow_ne_zero (k + 1) (by norm_num : (2 : ℝ) ≠ 0)) (by nlinarith : R + 2 ≠ 0)
  rw [hmul] at hlog
  have hpow := Real.log_pow (2 : ℝ) (k + 1)
  rw [hpow] at hlog
  simpa using hlog

/-- Clears the rational factors out of one dyadic term. -/
private lemma dyadic_coeff_step {C R M s : ℝ} (hR : R ≠ 0) (k : ℕ) :
    (C * (2 : ℝ) ^ (k + 1) * R * s) * (M / ((4 : ℝ) ^ k * R ^ 2))
      = (C * M / R) * ((2 : ℝ) ^ (k + 1) / (4 : ℝ) ^ k) * s := by
  have h4 : (4 : ℝ) ^ k ≠ 0 := pow_ne_zero k (by norm_num : (4 : ℝ) ≠ 0)
  field_simp [hR, h4]

/-- Termwise bound for a single weight on the dyadic annulus. -/
private lemma dyadic_term_bound {C R M L : ℝ} (hC : 0 ≤ C) (hR2 : 2 ≤ R) (hM : 0 ≤ M) (k : ℕ)
    (b : ℝ) (hb : b ≤ C * (2 : ℝ) ^ (k + 1) * R * (Real.log ((2 : ℝ) ^ (k + 1) * R + 2) + L)) :
    b * (M / ((4 : ℝ) ^ k * R ^ 2)) ≤
      (2 * C * M / R) * ((1 / 2 : ℝ) ^ k) * (((k : ℝ) + 1) * Real.log 2 + Real.log (R + 2) + L) := by
  have hRpos : 0 < R := by linarith
  have hRne : R ≠ 0 := ne_of_gt hRpos
  have hw : 0 ≤ M / ((4 : ℝ) ^ k * R ^ 2) := by
    have hwpos : 0 < (4 : ℝ) ^ k * R ^ 2 := by positivity
    exact div_nonneg hM (le_of_lt hwpos)
  have h1 := mul_le_mul_of_nonneg_right hb hw
  have hsplit : Real.log ((2 : ℝ) ^ (k + 1) * R + 2) + L ≤
      ((k : ℝ) + 1) * Real.log 2 + Real.log (R + 2) + L := by
    have hs := dyadic_log_split (R := R) hR2 k
    have hs' := add_le_add hs (le_refl L)
    simpa [add_assoc] using hs'
  have hcoeff : 0 ≤ (2 * C * M / R) * ((1 / 2 : ℝ) ^ k) := by
    have h2CM : 0 ≤ 2 * C * M := by positivity
    have hc : 0 ≤ (2 * C * M) / R := div_nonneg h2CM (le_of_lt hRpos)
    exact mul_nonneg hc (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) k)
  calc
    b * (M / ((4 : ℝ) ^ k * R ^ 2)) ≤
        (C * (2 : ℝ) ^ (k + 1) * R * (Real.log ((2 : ℝ) ^ (k + 1) * R + 2) + L)) * (M / ((4 : ℝ) ^ k * R ^ 2)) := h1
    _ = (C * M / R) * ((2 : ℝ) ^ (k + 1) / (4 : ℝ) ^ k) * (Real.log ((2 : ℝ) ^ (k + 1) * R + 2) + L) := by
        exact dyadic_coeff_step (R := R) (C := C) (M := M) (s := Real.log ((2 : ℝ) ^ (k + 1) * R + 2) + L) hRne k
    _ = (C * M / R) * (2 / (2 : ℝ) ^ k) * (Real.log ((2 : ℝ) ^ (k + 1) * R + 2) + L) := by
        rw [dyadic_pow_ratio k]
    _ = (2 * C * M / R) * ((1 / 2 : ℝ) ^ k) * (Real.log ((2 : ℝ) ^ (k + 1) * R + 2) + L) := by
        rw [show 2 / (2 : ℝ) ^ k = 2 * ((1 / 2 : ℝ) ^ k) by
              rw [dyadic_half_inv k]; ring]
        ring
    _ ≤ (2 * C * M / R) * ((1 / 2 : ℝ) ^ k) * (((k : ℝ) + 1) * Real.log 2 + Real.log (R + 2) + L) := by
        exact mul_le_mul_of_nonneg_left hsplit hcoeff

/-- `∑ (n+1) (1/2)^n = 4`. -/
private lemma dyadic_tsum_succ_half :
    (∑' n : ℕ, (((n + 1 : ℕ) : ℝ) * ((1 / 2 : ℝ) ^ n))) = 4 := by
  have h := hasSum_choose_mul_geometric_of_norm_lt_one (k := 1) (r := (1/2 : ℝ))
    (by norm_num : ‖(1/2 : ℝ)‖ < 1)
  calc
    (∑' n : ℕ, (((n + 1 : ℕ) : ℝ) * ((1 / 2 : ℝ) ^ n)))
        = ∑' n : ℕ, (((n + 1).choose 1 : ℕ) : ℝ) * ((1 / 2 : ℝ) ^ n) := by
          apply tsum_congr; intro n
          have cn : (n + 1).choose 1 = n + 1 := Nat.choose_one_right (n + 1)
          conv_rhs => rw [cn]
    _ = 4 := by
          rw [h.tsum_eq]
          norm_num

/-- The arithmetico-geometric series `∑ (n+1) (1/2)^n` converges. -/
private lemma dyadic_summable_succ_half :
    Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) * ((1 / 2 : ℝ) ^ n))) := by
  have h := hasSum_choose_mul_geometric_of_norm_lt_one (k := 1) (r := (1/2 : ℝ))
    (by norm_num : ‖(1/2 : ℝ)‖ < 1)
  simpa [Nat.choose_one_right] using h.summable

/-- The geometric series `∑ (1/2)^n` converges. -/
private lemma dyadic_summable_geom_half :
    Summable (fun n : ℕ => (((1 / 2 : ℝ) ^ n))) := by
  exact summable_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)

/-- Value of a `tsum` of a linear combination of the two summable sequences. -/
private lemma dyadic_tsum_lincomb {A B : ℝ} :
    (∑' n : ℕ, (A * (((n + 1 : ℕ) : ℝ) * ((1 / 2 : ℝ) ^ n)) + B * ((1 / 2 : ℝ) ^ n)))
      = 4 * A + 2 * B := by
  calc
    (∑' n, (A * (((n + 1 : ℕ) : ℝ) * ((1 / 2 : ℝ) ^ n)) + B * ((1 / 2 : ℝ) ^ n)))
        = (∑' n, (A * (((n + 1 : ℕ) : ℝ) * ((1 / 2 : ℝ) ^ n)))) + ∑' n, (B * ((1 / 2 : ℝ) ^ n)) := by
          rw [← Summable.tsum_add (Summable.mul_left A dyadic_summable_succ_half)
            (Summable.mul_left B dyadic_summable_geom_half)]
    _ = A * (∑' n, (((n + 1 : ℕ) : ℝ) * ((1 / 2 : ℝ) ^ n))) + B * (∑' n, ((1 / 2 : ℝ) ^ n)) := by
          rw [tsum_mul_left, tsum_mul_left]
    _ = A * 4 + B * 2 := by rw [dyadic_tsum_succ_half, tsum_geometric_two]
    _ = 4 * A + 2 * B := by ring

/-- The dyadic-annulus tail bound: a termwise comparison to two convergent
geometric series turns into the explicit constant `64`. -/
theorem dyadicAnnulusTail {C R M L : ℝ} (hC : 0 ≤ C) (hR : 2 ≤ R) (hM : 0 ≤ M)
    (hL : 0 ≤ L) (b : ℕ → ℝ) (hb0 : ∀ k : ℕ, 0 ≤ b k)
    (hb : ∀ k : ℕ, b k ≤ C * (2 : ℝ) ^ (k + 1) * R * (Real.log ((2 : ℝ) ^ (k + 1) * R + 2) + L)) :
    (∑' k : ℕ, b k * (M / ((4 : ℝ) ^ k * R ^ 2))) ≤
      (64 : ℝ) * C * M * (Real.log (R + 2) + L + 1) / R := by
  have hRpos : 0 < R := by linarith
  let A : ℝ := (2 * C * M / R) * Real.log 2
  let B : ℝ := (2 * C * M / R) * (Real.log (R + 2) + L)
  have hpt : ∀ k : ℕ,
      b k * (M / ((4 : ℝ) ^ k * R ^ 2)) ≤
        A * (((k + 1 : ℕ) : ℝ) * ((1 / 2 : ℝ) ^ k)) + B * ((1 / 2 : ℝ) ^ k) := by
    intro k
    calc
      b k * (M / ((4 : ℝ) ^ k * R ^ 2)) ≤
          (2 * C * M / R) * ((1 / 2 : ℝ) ^ k) * (((k : ℝ) + 1) * Real.log 2 + Real.log (R + 2) + L) :=
            dyadic_term_bound (hC := hC) (hR2 := hR) (hM := hM) k (b k) (hb k)
      _ = (2 * C * M / R) * ((1 / 2 : ℝ) ^ k) * (((k + 1 : ℕ) : ℝ) * Real.log 2 + Real.log (R + 2) + L) := by
          congr 2
          norm_cast
      _ = A * (((k + 1 : ℕ) : ℝ) * ((1 / 2 : ℝ) ^ k)) + B * ((1 / 2 : ℝ) ^ k) := by
          dsimp [A, B]
          ring
  have hf0 : ∀ k : ℕ, 0 ≤ b k * (M / ((4 : ℝ) ^ k * R ^ 2)) := by
    intro k
    have hwpos : 0 < (4 : ℝ) ^ k * R ^ 2 := by positivity
    exact mul_nonneg (hb0 k) (div_nonneg hM (le_of_lt hwpos))
  have hsumV : Summable (fun k : ℕ =>
      A * (((k + 1 : ℕ) : ℝ) * ((1 / 2 : ℝ) ^ k)) + B * ((1 / 2 : ℝ) ^ k)) := by
    exact Summable.add (Summable.mul_left A dyadic_summable_succ_half)
      (Summable.mul_left B dyadic_summable_geom_half)
  have hsA : Summable (fun k : ℕ => b k * (M / ((4 : ℝ) ^ k * R ^ 2))) :=
    Summable.of_nonneg_of_le hf0 hpt hsumV
  have hmain := Summable.tsum_le_tsum hpt hsA hsumV
  have hv : (∑' k : ℕ, (A * (((k + 1 : ℕ) : ℝ) * ((1 / 2 : ℝ) ^ k)) + B * ((1 / 2 : ℝ) ^ k))) = 4 * A + 2 * B := by
    exact dyadic_tsum_lincomb (A := A) (B := B)
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hx : 0 ≤ Real.log (R + 2) := by
    exact Real.log_nonneg (by linarith : (1 : ℝ) ≤ R + 2)
  have hin : 8 * Real.log 2 + 4 * Real.log (R + 2) + 4 * L ≤
      64 * (Real.log (R + 2) + L + 1) := by
    nlinarith
  have hcm : 0 ≤ C * M / R := by
    exact div_nonneg (mul_nonneg hC hM) (le_of_lt hRpos)
  have hmul := mul_le_mul_of_nonneg_left hin hcm
  calc
    (∑' k : ℕ, b k * (M / ((4 : ℝ) ^ k * R ^ 2))) ≤
        ∑' k : ℕ, (A * (((k + 1 : ℕ) : ℝ) * ((1 / 2 : ℝ) ^ k)) + B * ((1 / 2 : ℝ) ^ k)) := hmain
    _ = 4 * A + 2 * B := hv
    _ = (C * M / R) * (8 * Real.log 2 + 4 * Real.log (R + 2) + 4 * L) := by
        dsimp [A, B]
        ring
    _ ≤ (C * M / R) * (64 * (Real.log (R + 2) + L + 1)) := hmul
    _ = (64 : ℝ) * C * M * (Real.log (R + 2) + L + 1) / R := by ring

end Commons.Analysis.Asymptotics