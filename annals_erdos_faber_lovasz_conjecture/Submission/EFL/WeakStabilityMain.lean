import Submission.EFL.WeakStability
import Submission.Commons.Data.List.length_mul_le_sum
import Submission.EFL.DeepInputs
import Submission.EFL.LocallySparse

/-!
# The assembly of Theorem 1.3 (weak stability)

This module contains the (long) numeric preparation for the proof of
Theorem 1.3 (`WeakStabilityInstance`) and the final assembly.  The numeric
estimates are split off into separate top-level lemmas
(`weakStability_margins`, `weakStability_sizeFactor_le`,
`weakStability_Csf2`, `weakStability_Csf3`, `weakStability_volBound_ge`,
`weakStability_hc2`, `weakStability_hc3`, `weakStability_hfinal`) so that
each is checked in a small local context; the assembly then just combines
them.

The constants of the proof are

* `τ = 1 − ε/6`, `K = ⌈(1/ε)²⌉₊`,  `η = ζc/ε¹⁰`, `r₁ = ⌊1/η⌋₊ + 1`,
* `ζc = (1/4)·min(ζ₀,1)·min(e^{−C₁},1)·ε³⁰`, `C₁ = 10⁹·K_AKS·(1/ε)²¹ + 1`,
* `M = ⌈1/volBound τ K⌉₊ + 1`, `εb = ε/(10M)`, `Δ = 4ε^{−10}n`.
-/

set_option autoImplicit false

set_option maxHeartbeats 1000000

namespace ErdosFaberLovaszConjecture

open Filter

/-! ## Elementary power bounds for `ε` -/

/-- `ε ^ 20 ≤ ε ^ 2` for `0 < ε ≤ 1`. -/
lemma eps20_le_eps2 {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) : ε ^ 20 ≤ ε ^ 2 := by
  have h : ε ^ 18 ≤ 1 := pow_le_one₀ (le_of_lt hε0) hε1
  have h2 : ε ^ 20 = ε ^ 2 * ε ^ 18 := by ring
  nlinarith [h, h2, pow_pos hε0 2]

/-- `4η² ≤ ε/4` when `η ≤ ε²/4` and `0 < ε ≤ 1`. -/
lemma four_mul_sq_le {ε η : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hη0 : 0 < η)
    (hη : η ≤ ε ^ 2 / 4) : 4 * η ^ 2 ≤ ε / 4 := by
  have h4 : η ^ 2 ≤ (ε ^ 2 / 4) ^ 2 := by nlinarith [hη, hη0]
  have h5 : (ε ^ 2 / 4) ^ 2 = ε ^ 4 / 16 := by ring
  have h6 : ε ^ 4 ≤ ε := by
    have h : ε ^ 3 ≤ 1 := pow_le_one₀ (le_of_lt hε0) hε1
    have h7 : ε ^ 4 = ε * ε ^ 3 := by ring
    nlinarith [h, h7, hε0]
  nlinarith [h4, h5, h6, hε0]

/-- `8η ≤ ε/24` when `η ≤ ε²/4` and `0 < ε ≤ 1/1000`. -/
lemma eight_mul_le {ε η : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 1000) (hη : η ≤ ε ^ 2 / 4) :
    8 * η ≤ ε / 24 := by
  have h : 48 * ε ≤ 1 := by linarith
  have h2 : ε ^ 2 = ε * ε := by ring
  nlinarith [hη, h, h2, hε0]

/-- `(3/2)η ≤ ε/8` when `η ≤ ε²/4` and `0 < ε ≤ 1/1000`. -/
lemma three_halves_mul_le {ε η : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 1000)
    (hη : η ≤ ε ^ 2 / 4) : (3 / 2) * η ≤ ε / 8 := by
  have h : 3 * ε ≤ 1 := by linarith
  have h2 : ε ^ 2 = ε * ε := by ring
  nlinarith [hη, h, h2, hε0]

/-- `1/(K:ℝ) ≤ ε²` when `(1/ε)² ≤ K`. -/
lemma one_div_ceil_inv_sq_le {ε : ℝ} {K : ℕ} (hε0 : 0 < ε) (hKpos : (0 : ℝ) < (K : ℝ))
    (hKge : (1 / ε) ^ 2 ≤ (K : ℝ)) : (1 : ℝ) / (K : ℝ) ≤ ε ^ 2 := by
  rw [div_le_iff₀ hKpos]
  have h2 : (1 / ε) ^ 2 = 1 / ε ^ 2 := one_div_pow ε 2
  rw [h2] at hKge
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < ε ^ 2)] at hKge
  linarith [hKge]

/-- `ε²/2 ≤ 1/(K:ℝ)` when `(K:ℝ) ≤ 2(1/ε)²`. -/
lemma half_sq_le_one_div_ceil {ε : ℝ} {K : ℕ} (hε0 : 0 < ε) (hKpos : (0 : ℝ) < (K : ℝ))
    (hKle : (K : ℝ) ≤ 2 * (1 / ε) ^ 2) : ε ^ 2 / 2 ≤ (1 : ℝ) / (K : ℝ) := by
  rw [le_div_iff₀ hKpos]
  have h := mul_le_mul_of_nonneg_left hKle (by positivity : (0 : ℝ) ≤ ε ^ 2 / 2)
  have h2 : ε ^ 2 / 2 * (2 * (1 / ε) ^ 2) = 1 := by
    rw [one_div_pow]
    field_simp
  linarith [h, h2.le, h2.ge]

/-! ## The margin block of the Theorem 1.3 constants -/

/-- `ReorderingMargins r₁ (1−ε/6) ⌈(1/ε)²⌉₊` for `ε ≤ 1/1000` and
`r₁ ≥ 4(1/ε)²⁰`. -/
theorem weakStability_margins {ε : ℝ} {r₁ : ℕ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 1000)
    (hr₁_20 : 4 * (1 / ε) ^ 20 ≤ (r₁ : ℝ)) :
    ReorderingMargins r₁ (1 - ε / 6) ⌈(1 / ε) ^ 2⌉₊ := by
  set τ : ℝ := 1 - ε / 6 with hτdef
  set K : ℕ := ⌈(1 / ε) ^ 2⌉₊ with hKdef
  have hε1' : ε ≤ 1 := by linarith
  have hεinv1 : (1 : ℝ) ≤ 1 / ε := by rw [le_div_iff₀ hε0]; linarith
  have hτ0 : 0 < τ := by rw [hτdef]; linarith
  have hτ1 : τ < 1 := by rw [hτdef]; linarith
  have hτhalf : (1 : ℝ) / 2 ≤ τ := by rw [hτdef]; linarith
  have h1mτ : 1 - τ = ε / 6 := by rw [hτdef]; ring
  have hτsqrt_ge : (1 / 2 : ℝ) ≤ Real.sqrt τ := by
    have h4 : Real.sqrt (1 / 4 : ℝ) ≤ Real.sqrt τ := Real.sqrt_le_sqrt (by linarith [hτhalf])
    have h5 : Real.sqrt (1 / 4 : ℝ) = (1 / 2 : ℝ) := by
      rw [show (1 / 4 : ℝ) = (1 / 2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    linarith [h4, h5]
  have hτsqrt_le : Real.sqrt τ ≤ 1 := Real.sqrt_le_one.mpr (le_of_lt hτ1)
  have hτq_ge : (1 / 2 : ℝ) ≤ tauQuarter τ := by
    have h6 := Real.sqrt_le_sqrt hτsqrt_ge
    simp only [tauQuarter]
    nlinarith [h6, Real.sqrt_nonneg (1 / 2 : ℝ), Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hτq_le : tauQuarter τ ≤ 1 := tauQuarter_le_one (le_of_lt hτ1)
  have hK1 : 1 ≤ K := Nat.one_le_ceil_iff.mpr (by positivity)
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK1
  have hKge : (1 / ε) ^ 2 ≤ (K : ℝ) := Nat.le_ceil _
  have hKle : (K : ℝ) ≤ 2 * (1 / ε) ^ 2 := by
    have h1 : ((K : ℕ) : ℝ) < (1 / ε) ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
    have h2 : (1 : ℝ) ≤ (1 / ε) ^ 2 := by nlinarith [hεinv1]
    linarith
  have hK4 : (K : ℝ) ^ 4 ≤ 16 * (1 / ε) ^ 8 := by
    calc (K : ℝ) ^ 4 ≤ (2 * (1 / ε) ^ 2) ^ 4 := pow_le_pow_left₀ (by positivity) hKle 4
      _ = 16 * (1 / ε) ^ 8 := by ring
  have h1K : (1 : ℝ) / (K : ℝ) ≤ ε ^ 2 := one_div_ceil_inv_sq_le hε0 hKpos hKge
  have h1K' : ε ^ 2 / 2 ≤ (1 : ℝ) / (K : ℝ) := half_sq_le_one_div_ceil hε0 hKpos hKle
  have hE : (1000 : ℝ) ≤ 1 / ε := inv_ge_1000 hε0 hε1
  have hx2 : (1 : ℝ) ≤ (1 / ε) ^ 2 := one_le_inv_pow hε0 hε1' 2
  have hx20 : (1 : ℝ) ≤ (1 / ε) ^ 20 := one_le_inv_pow hε0 hε1' 20
  have hq0 : 0 < 1 - τ - 7 * tauQuarter τ / (K : ℝ) := by
    have h7 : 7 * tauQuarter τ / (K : ℝ) ≤ 7 * ε ^ 2 := by
      calc 7 * tauQuarter τ / (K : ℝ) = 7 * tauQuarter τ * (1 / (K : ℝ)) := by ring
        _ ≤ 7 * 1 * ε ^ 2 := by
            have h3 : (0 : ℝ) ≤ 7 * tauQuarter τ :=
              mul_nonneg (by norm_num) (tauQuarter_nonneg τ)
            nlinarith [h1K, hτq_le, tauQuarter_nonneg τ]
        _ = 7 * ε ^ 2 := by ring
    have h8 : ε / 6 - 7 * ε ^ 2 > 0 := by nlinarith [hε1]
    linarith [h1mτ]
  have hKle4 : (K : ℝ) * Real.sqrt τ ≤ 4 * (1 / ε) ^ 2 := by
    nlinarith [hKle, hτsqrt_le, Real.sqrt_nonneg τ, hx2]
  refine ReorderingMargins_follows_from_large r₁ τ K hq0 ?_ ?_ ?_ ?_ ?_ ?_
  · -- hL1 : 1 ≤ τ(r₁−1)
    have h1 : (1 : ℝ) / τ ≤ 2 := by rw [div_le_iff₀ hτ0]; nlinarith [hτhalf]
    have h2 : (1 : ℝ) + 1 / τ ≤ 4 * (1 / ε) ^ 20 := by nlinarith [h1, hx20]
    exact margin_tau_of_bound hτ0 (by linarith [h2, hr₁_20])
  · -- hL2 : K ≤ τ^{1/4}(r₁−1)
    have ht0 : 0 < tauQuarter τ := tauQuarter_pos hτ0
    have h1 : (1 : ℝ) / tauQuarter τ ≤ 2 := by rw [div_le_iff₀ ht0]; linarith [hτq_ge]
    have h2 : (K : ℝ) / tauQuarter τ ≤ 4 * (1 / ε) ^ 2 := by
      rw [div_le_iff₀ ht0]
      nlinarith [hKle, ht0, hτq_ge, hx2]
    have h4 : (1 : ℝ) + (K : ℝ) / tauQuarter τ ≤ 4 * (1 / ε) ^ 20 := by
      have h5 : (1 : ℝ) + 4 * (1 / ε) ^ 2 ≤ 4 * (1 / ε) ^ 20 := one_add_four_mul_sq_le_pow hE
      linarith [h2, h5]
    exact margin_mar_of_bound hτ0 (by linarith [h4, hr₁_20])
  · -- hL3 : 1 + K√τ ≤ r₁/2
    have h1 : 2 * (1 + 4 * (1 / ε) ^ 2) ≤ 4 * (1 / ε) ^ 20 := two_mul_le_pow hE
    exact margin_M1_of_bound (by linarith [h1, hKle4, hr₁_20])
  · -- hL4 : 2(1 + K√τ) ≤ K²√τ·r₁
    have h1 : 2 * (1 + 4 * (1 / ε) ^ 2) ≤ 4 * (1 / ε) ^ 20 := two_mul_le_pow hE
    have hKge4 : (1 / ε) ^ 4 ≤ (K : ℝ) ^ 2 := by
      calc (1 / ε) ^ 4 = ((1 / ε) ^ 2) ^ 2 := by ring
        _ ≤ (K : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hKge 2
    have hden : ((1 / ε) ^ 4) * (1 / 2) ≤ (K : ℝ) ^ 2 * Real.sqrt τ :=
      mul_le_mul hKge4 hτsqrt_ge (by norm_num) (by positivity)
    have h3 : 4 * (1 / ε) ^ 20 ≤ ((1 / ε) ^ 4) * (1 / 2) * (4 * (1 / ε) ^ 20) := by
      have h4 : ((1 / ε) ^ 4) * (1 / 2) * (4 * (1 / ε) ^ 20) = 2 * (1 / ε) ^ 24 := by ring
      rw [h4]
      have h5 : (2 : ℝ) ≤ (1 / ε) ^ 4 := by
        have h6 : (1000 : ℝ) ^ 4 ≤ (1 / ε) ^ 4 := pow_le_pow_left₀ (by norm_num) hE 4
        nlinarith [h6]
      have h7 : (1 / ε) ^ 24 = (1 / ε) ^ 4 * (1 / ε) ^ 20 := by ring
      rw [h7]
      have h8 : (0 : ℝ) < (1 / ε) ^ 20 := by positivity
      nlinarith [h5, h8]
    have h8 : ((1 / ε) ^ 4) * (1 / 2) * (4 * (1 / ε) ^ 20) ≤
        (K : ℝ) ^ 2 * Real.sqrt τ * (r₁ : ℝ) :=
      mul_le_mul hden hr₁_20 (by positivity) (by positivity)
    linarith [h1, hKle4, h3, h8]
  · -- hL5
    have h1 : (3 / 4 : ℝ) * (1 / ε) ^ 8 ≤ sizeFactor τ K - 1 - (K : ℝ) * Real.sqrt τ := by
      have h2 : sizeFactor τ K = 1 + 3 * tauQuarter τ * (K : ℝ) ^ 4 := rfl
      have hK4ge : (1 / ε) ^ 8 ≤ (K : ℝ) ^ 4 := by
        have h3 : (1 / ε) ^ 2 ≤ (K : ℝ) := hKge
        calc (1 / ε) ^ 8 = ((1 / ε) ^ 2) ^ 4 := by ring
          _ ≤ (K : ℝ) ^ 4 := pow_le_pow_left₀ (by positivity) h3 4
      have h4 : (3 / 2 : ℝ) * (1 / ε) ^ 8 ≤ 3 * tauQuarter τ * (K : ℝ) ^ 4 := by
        have h5 : 3 * (1 / 2 : ℝ) * (1 / ε) ^ 8 ≤ 3 * tauQuarter τ * (K : ℝ) ^ 4 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hτq_ge (by norm_num)) hK4ge (by positivity)
            (by positivity)
        linarith [h5]
      have h7 : 4 * (1 / ε) ^ 2 ≤ (3 / 4 : ℝ) * (1 / ε) ^ 8 := by
        have h8 : (1000 : ℝ) ^ 6 ≤ (1 / ε) ^ 6 := pow_le_pow_left₀ (by norm_num) hE 6
        have h9 : (0 : ℝ) < (1 / ε) ^ 2 := by positivity
        nlinarith [h8, h9]
      rw [h2]
      linarith [h4, h7, hKle4]
    have h2 : (16 : ℝ) * (1 / ε) ^ 40 ≤ (r₁ : ℝ) ^ 2 := by
      calc (16 : ℝ) * (1 / ε) ^ 40 = (4 * (1 / ε) ^ 20) ^ 2 := by ring
        _ ≤ (r₁ : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hr₁_20 2
    have h3 : (3 / 4 : ℝ) * (1 / ε) ^ 8 * (16 * (1 / ε) ^ 40) ≤
        (sizeFactor τ K - 1 - (K : ℝ) * Real.sqrt τ) * (r₁ : ℝ) ^ 2 :=
      mul_le_mul h1 h2 (by positivity : (0 : ℝ) ≤ 16 * (1 / ε) ^ 40)
        (by linarith [h1, (by positivity : (0 : ℝ) < (1 / ε) ^ 8)])
    have h4 : (3 / 4 : ℝ) * (1 / ε) ^ 8 * (16 * (1 / ε) ^ 40) = 12 * (1 / ε) ^ 48 := by ring
    have h5 : (1 : ℝ) ≤ 12 * (1 / ε) ^ 48 := by
      have h6 : (1 : ℝ) ≤ (1 / ε) ^ 48 := one_le_inv_pow hε0 hε1' 48
      linarith [h6]
    linarith [h3, h4 ▸ h3, h5]
  · -- hL6
    have hq : 1 - τ - 7 * tauQuarter τ / (K : ℝ) ≤ 1 - τ - 2 * Real.sqrt τ / (K : ℝ) := by
      have h1 : 2 * Real.sqrt τ ≤ 7 * tauQuarter τ := by
        have h2 : Real.sqrt τ ≤ tauQuarter τ := by
          rw [tauQuarter]
          apply Real.sqrt_le_sqrt
          rw [Real.le_sqrt (le_of_lt hτ0) (le_of_lt hτ0)]
          nlinarith [hτ0, hτ1]
        linarith [h2]
      have h2 : 2 * Real.sqrt τ / (K : ℝ) ≤ 7 * tauQuarter τ / (K : ℝ) :=
        div_le_div_of_nonneg_right h1 (le_of_lt hKpos)
      linarith
    have huq : (1 - τ - 2 * Real.sqrt τ / (K : ℝ)) -
        (1 - τ - 7 * tauQuarter τ / (K : ℝ)) ≥ ε ^ 2 / 2 := by
      have h1 : (7 * tauQuarter τ - 2 * Real.sqrt τ) ≥ (3 / 2 : ℝ) := by
        linarith [hτq_ge, hτsqrt_le]
      have h3 : ε ^ 2 / 2 ≤ (K : ℝ)⁻¹ := by
        rw [← one_div]
        exact h1K'
      have h4 : (0 : ℝ) ≤ 7 * tauQuarter τ - 2 * Real.sqrt τ := by linarith [h1]
      have h2 : (3 / 2 : ℝ) * (ε ^ 2 / 2) ≤ (7 * tauQuarter τ - 2 * Real.sqrt τ) / (K : ℝ) := by
        rw [div_eq_mul_inv]
        exact mul_le_mul h1 h3 (by positivity) (by linarith [h1])
      have h5 : (7 * tauQuarter τ - 2 * Real.sqrt τ) / (K : ℝ) =
          7 * tauQuarter τ / (K : ℝ) - 2 * Real.sqrt τ / (K : ℝ) := by ring
      have h6 : 7 * tauQuarter τ / (K : ℝ) - 2 * Real.sqrt τ / (K : ℝ) =
          (1 - τ - 2 * Real.sqrt τ / (K : ℝ)) - (1 - τ - 7 * tauQuarter τ / (K : ℝ)) := by ring
      linarith [h2, h5.le, h5.ge, h6.le, h6.ge]
    have hu1 : (1 : ℝ) - τ - 2 * Real.sqrt τ / (K : ℝ) ≤ 1 := by
      have h1 : (0 : ℝ) ≤ 2 * Real.sqrt τ / (K : ℝ) := by positivity
      have h2 : (0 : ℝ) ≤ 1 - τ := by rw [h1mτ]; positivity
      linarith
    have h4 : (1 : ℝ) / (r₁ : ℝ) ≤ ε ^ 2 / 2 := by
      have h5 : (1 : ℝ) / (r₁ : ℝ) ≤ 1 / (4 * (1 / ε) ^ 20) :=
        one_div_le_one_div_of_le (by positivity) hr₁_20
      have h6 : (1 : ℝ) / (4 * (1 / ε) ^ 20) = ε ^ 20 / 4 := by
        rw [one_div_pow]; field_simp
      have h7 : ε ^ 20 / 4 ≤ ε ^ 2 / 2 := by
        have h8 : ε ^ 18 ≤ 2 := by
          have h9 : ε ^ 18 ≤ 1 := pow_le_one₀ (le_of_lt hε0) hε1'
          linarith [h9]
        nlinarith [pow_pos hε0 2, h8]
      linarith [h5, h6.le, h6.ge, h7]
    have h8 : (1 - τ - 2 * Real.sqrt τ / (K : ℝ)) * (1 / (r₁ : ℝ)) ≤ ε ^ 2 / 2 := by
      have h9 : (0 : ℝ) ≤ 1 / (r₁ : ℝ) := by positivity
      nlinarith [hu1, h4, h9]
    have h11 : (1 - τ - 2 * Real.sqrt τ / (K : ℝ)) * (1 - 1 / (r₁ : ℝ)) =
        (1 - τ - 2 * Real.sqrt τ / (K : ℝ)) -
          (1 - τ - 2 * Real.sqrt τ / (K : ℝ)) * (1 / (r₁ : ℝ)) := by ring
    rw [h11]
    linarith [huq, h8, hq]

/-- `sizeFactor (1−ε/6) ⌈(1/ε)²⌉₊ + 2 ≤ 100(1/ε)⁸` for `ε ≤ 1/1000`. -/
theorem weakStability_sizeFactor_le {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 1000) :
    sizeFactor (1 - ε / 6) ⌈(1 / ε) ^ 2⌉₊ + 2 ≤ 100 * (1 / ε) ^ 8 := by
  set τ : ℝ := 1 - ε / 6 with hτdef
  set K : ℕ := ⌈(1 / ε) ^ 2⌉₊ with hKdef
  have hε1' : ε ≤ 1 := by linarith
  have hτ1 : τ < 1 := by rw [hτdef]; linarith
  have hτq_le : tauQuarter τ ≤ 1 := tauQuarter_le_one (le_of_lt hτ1)
  have hK1 : 1 ≤ K := Nat.one_le_ceil_iff.mpr (by positivity)
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK1
  have hεinv1 : (1 : ℝ) ≤ 1 / ε := by rw [le_div_iff₀ hε0]; linarith
  have hKge : (1 / ε) ^ 2 ≤ (K : ℝ) := Nat.le_ceil _
  have hKle : (K : ℝ) ≤ 2 * (1 / ε) ^ 2 := by
    have h1 : ((K : ℕ) : ℝ) < (1 / ε) ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
    have h2 : (1 : ℝ) ≤ (1 / ε) ^ 2 := by nlinarith [hεinv1]
    linarith
  have hK4 : (K : ℝ) ^ 4 ≤ 16 * (1 / ε) ^ 8 := by
    calc (K : ℝ) ^ 4 ≤ (2 * (1 / ε) ^ 2) ^ 4 := pow_le_pow_left₀ (by positivity) hKle 4
      _ = 16 * (1 / ε) ^ 8 := by ring
  have h1 : sizeFactor τ K = 1 + 3 * tauQuarter τ * (K : ℝ) ^ 4 := rfl
  have h2 : 3 * tauQuarter τ * (K : ℝ) ^ 4 ≤ 48 * (1 / ε) ^ 8 := by
    have h3 : 3 * tauQuarter τ * (K : ℝ) ^ 4 ≤ 3 * 1 * (16 * (1 / ε) ^ 8) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hτq_le (by norm_num)) hK4 (by positivity) (by norm_num)
    linarith [h3]
  have h4 : (1 : ℝ) ≤ (1 / ε) ^ 8 := by
    calc (1 : ℝ) = 1 ^ 8 := by norm_num
      _ ≤ (1 / ε) ^ 8 := pow_le_pow_left₀ (by norm_num) hεinv1 8
  rw [h1]
  linarith [h2, h4]

/-- `2·(sizeFactor (1−ε/6) ⌈(1/ε)²⌉₊ + 2) ≤ 4/ε¹⁰`. -/
theorem weakStability_Csf2 {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 1000) :
    2 * (sizeFactor (1 - ε / 6) ⌈(1 / ε) ^ 2⌉₊ + 1 + 1) ≤ 4 / ε ^ 10 := by
  set τ : ℝ := 1 - ε / 6 with hτdef
  set K : ℕ := ⌈(1 / ε) ^ 2⌉₊ with hKdef
  have hsf_le := weakStability_sizeFactor_le (ε := ε) hε0 hε1
  rw [← hτdef, ← hKdef] at hsf_le
  have h1 : 2 * (sizeFactor τ K + 1 + 1) ≤ 2 * (100 * (1 / ε) ^ 8) := by linarith
  have hx : (0 : ℝ) < (1 / ε) ^ 8 := by positivity
  have h6 : (50 : ℝ) ≤ (1 / ε) ^ 2 := by
    have h9 : (1000 : ℝ) ≤ 1 / ε := inv_ge_1000 hε0 hε1
    nlinarith [h9]
  have h7 : (4 : ℝ) / ε ^ 10 = 4 * (1 / ε) ^ 10 := div_pow_eq_mul 4 ε 10
  have h2 : 2 * (100 * (1 / ε) ^ 8) ≤ 4 / ε ^ 10 := by
    rw [h7]
    have h8 : (1 / ε) ^ 10 = (1 / ε) ^ 8 * (1 / ε) ^ 2 := by ring
    rw [h8]
    nlinarith [hx, h6]
  linarith [h1, h2]

/-- `(sizeFactor (1−ε/6) ⌈(1/ε)²⌉₊ + 2)² · (ε²⁰/4) ≤ 2`. -/
theorem weakStability_Csf3 {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 1000) :
    (sizeFactor (1 - ε / 6) ⌈(1 / ε) ^ 2⌉₊ + 1 + 1) ^ 2 * (ε ^ 20 / 4) ≤ 2 := by
  set τ : ℝ := 1 - ε / 6 with hτdef
  set K : ℕ := ⌈(1 / ε) ^ 2⌉₊ with hKdef
  have hsf_le := weakStability_sizeFactor_le (ε := ε) hε0 hε1
  rw [← hτdef, ← hKdef] at hsf_le
  have h1 : (sizeFactor τ K + 1 + 1) ^ 2 ≤ (100 * (1 / ε) ^ 8) ^ 2 := by
    have hsfp : (0 : ℝ) < sizeFactor τ K := sizeFactor_pos τ K
    have h := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ sizeFactor τ K + 2) hsf_le 2
    have h2 : (sizeFactor τ K + 2 : ℝ) = sizeFactor τ K + 1 + 1 := by ring
    rwa [h2] at h
  have h2 : (100 * (1 / ε) ^ 8) ^ 2 = 10000 * (1 / ε) ^ 16 := by ring
  have h3 : (10000 * (1 / ε) ^ 16) * (ε ^ 20 / 4) ≤ 2 := by
    have h4 : (1 / ε) ^ 16 = 1 / ε ^ 16 := one_div_pow ε 16
    rw [h4]
    have h5 : 10000 * (1 / ε ^ 16) * (ε ^ 20 / 4) = 2500 * ε ^ 4 := by
      field_simp
      ring
    rw [h5]
    have h6 : ε ^ 4 ≤ (1 / 1000 : ℝ) ^ 4 := pow_le_pow_left₀ (le_of_lt hε0) hε1 4
    nlinarith [h6]
  calc (sizeFactor τ K + 1 + 1) ^ 2 * (ε ^ 20 / 4)
      ≤ (100 * (1 / ε) ^ 8) ^ 2 * (ε ^ 20 / 4) := by
        have h7 : (0 : ℝ) ≤ ε ^ 20 / 4 := by positivity
        nlinarith [h1, h7]
    _ = (10000 * (1 / ε) ^ 16) * (ε ^ 20 / 4) := by rw [h2]
    _ ≤ 2 := h3

/-- `ε¹⁰/14400 ≤ volBound (1−ε/6) ⌈(1/ε)²⌉₊`. -/
theorem weakStability_volBound_ge {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 1000) :
    ε ^ 10 / 14400 ≤ volBound (1 - ε / 6) ⌈(1 / ε) ^ 2⌉₊ := by
  set τ : ℝ := 1 - ε / 6 with hτdef
  set K : ℕ := ⌈(1 / ε) ^ 2⌉₊ with hKdef
  have hsf_le := weakStability_sizeFactor_le (ε := ε) hε0 hε1
  rw [← hτdef, ← hKdef] at hsf_le
  have hτ1 : τ < 1 := by rw [hτdef]; linarith
  have hτhalf : (1 / 2 : ℝ) ≤ τ := by rw [hτdef]; linarith
  have h1mτ : 1 - τ = ε / 6 := by rw [hτdef]; ring
  have hτq_le : tauQuarter τ ≤ 1 := tauQuarter_le_one (le_of_lt hτ1)
  have hK1 : 1 ≤ K := Nat.one_le_ceil_iff.mpr (by positivity)
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK1
  have hKge : (1 / ε) ^ 2 ≤ (K : ℝ) := Nat.le_ceil _
  have h1K : (1 : ℝ) / (K : ℝ) ≤ ε ^ 2 := one_div_ceil_inv_sq_le hε0 hKpos hKge
  have hq : ε / 12 ≤ 1 - τ - 7 * tauQuarter τ / (K : ℝ) := by
    have h7 : 7 * tauQuarter τ / (K : ℝ) ≤ 7 * ε ^ 2 := by
      calc 7 * tauQuarter τ / (K : ℝ) = 7 * tauQuarter τ * (1 / (K : ℝ)) := by ring
        _ ≤ 7 * 1 * ε ^ 2 := by
            have h3 : (0 : ℝ) ≤ 7 * tauQuarter τ :=
              mul_nonneg (by norm_num) (tauQuarter_nonneg τ)
            nlinarith [h1K, hτq_le, tauQuarter_nonneg τ]
        _ = 7 * ε ^ 2 := by ring
    have h9 : ε ^ 2 ≤ ε / 1000 := by
      have h10 : ε * ε ≤ ε * (1 / 1000) := mul_le_mul_of_nonneg_left hε1 (le_of_lt hε0)
      nlinarith [h10]
    have h8 : 7 * ε ^ 2 ≤ ε / 12 := by linarith
    linarith [h1mτ]
  have hsf_pos : 0 < sizeFactor τ K := sizeFactor_pos τ K
  have hmain : (ε / 12) ^ 2 / (100 * (1 / ε) ^ 8) ≤
      (1 - τ - 7 * tauQuarter τ / (K : ℝ)) ^ 2 / sizeFactor τ K :=
    div_le_div₀ (by positivity) (pow_le_pow_left₀ (by linarith [hε0]) hq 2) hsf_pos
      (by linarith [hsf_le])
  have h2 : (ε / 12) ^ 2 / (100 * (1 / ε) ^ 8) = ε ^ 10 / 14400 := by
    have h3 : (1 / ε) ^ 8 = 1 / ε ^ 8 := one_div_pow ε 8
    rw [h3]
    field_simp
    ring
  rw [volBound, ← h2]
  exact hmain

/-! ## The bounds on the three colour classes -/

/-- The `𝓗₃` estimate: if `2η² ≤ ε/4` and `n ≥ 1000` then the number of
colours `n(n−1)/(s₃(s₃−1))` with `s₃ = ⌈√n/η⌉₊` is at most `εn/4`. -/
theorem weakStability_hc3 {ε η : ℝ} {n : ℕ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hη0 : 0 < η)
    (hηsq : 4 * η ^ 2 ≤ ε / 4) (hn : 1000 ≤ n) :
    (((n * (n - 1) / (⌈Real.sqrt n / η⌉₊ * (⌈Real.sqrt n / η⌉₊ - 1))) : ℕ) : ℝ) ≤
      ε * (n : ℝ) / 4 := by
  set s₃ : ℕ := ⌈Real.sqrt n / η⌉₊ with hs₃def
  have hn1000 : (1000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hs₃2 : 2 ≤ s₃ := by
    rw [hs₃def]
    have h1 : (1 : ℝ) < Real.sqrt n / η := by
      rw [lt_div_iff₀ hη0]
      have h4 : 4 * η ^ 2 ≤ (n : ℝ) := by nlinarith [hηsq, hε0, hε1, hn1000]
      have h3 : 2 * η ≤ Real.sqrt n := by
        rw [Real.le_sqrt (by positivity) (by positivity)]
        nlinarith [h4]
      nlinarith [h3, hη0]
    have h2 : 1 < ⌈Real.sqrt n / η⌉₊ := Nat.lt_ceil.mpr (by simpa using h1)
    omega
  have hs₃pos : (0 : ℝ) < (s₃ : ℝ) := by
    have h : (2 : ℝ) ≤ (s₃ : ℝ) := by exact_mod_cast hs₃2
    linarith
  have hs₃real : (2 : ℝ) ≤ (s₃ : ℝ) := by exact_mod_cast hs₃2
  have h1 : (n : ℝ) / (2 * η ^ 2) ≤ (s₃ : ℝ) ^ 2 := by
    have h2 : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hnpos
    have h3 : Real.sqrt n / η * (Real.sqrt n / η) ≤ (s₃ : ℝ) * (s₃ : ℝ) := by
      have hb : Real.sqrt n / η ≤ (s₃ : ℝ) := by rw [hs₃def]; exact Nat.le_ceil _
      exact mul_le_mul hb hb (by positivity) (by positivity)
    have h4 : Real.sqrt n / η * (Real.sqrt n / η) = (n : ℝ) / η ^ 2 := by
      field_simp
      rw [Real.sq_sqrt (le_of_lt hnpos)]
    have h5 : (n : ℝ) / (2 * η ^ 2) ≤ (n : ℝ) / η ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hnpos, hη0]
    calc (n : ℝ) / (2 * η ^ 2) ≤ (n : ℝ) / η ^ 2 := h5
      _ = Real.sqrt n / η * (Real.sqrt n / η) := h4.symm
      _ ≤ (s₃ : ℝ) * (s₃ : ℝ) := h3
      _ = (s₃ : ℝ) ^ 2 := by ring
  have hspos : 0 < s₃ * (s₃ - 1) := by
    have h3 : 1 ≤ s₃ - 1 := by omega
    exact Nat.mul_pos (by omega) h3
  have hcast : 0 < (s₃ : ℝ) * ((s₃ : ℝ) - 1) := by
    have h : ((s₃ * (s₃ - 1) : ℕ) : ℝ) = (s₃ : ℝ) * ((s₃ : ℝ) - 1) := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ s₃)]; ring
    rw [← h]
    exact_mod_cast hspos
  have hnn : (((n * (n - 1) / (s₃ * (s₃ - 1))) : ℕ) : ℝ) ≤
      (n : ℝ) * ((n : ℝ) - 1) / ((s₃ : ℝ) * ((s₃ : ℝ) - 1)) := by
    have h4 : ((n * (n - 1) : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
      rcases Nat.eq_zero_or_pos (n - 1) with h | h
      · have : n = 1 := by omega
        simp [this]
      · push_cast [Nat.cast_sub (by omega : 1 ≤ n)]; ring
    have h5 : ((s₃ * (s₃ - 1) : ℕ) : ℝ) = (s₃ : ℝ) * ((s₃ : ℝ) - 1) := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ s₃)]; ring
    have h6 := Nat.cast_div_le (α := ℝ) (m := n * (n - 1)) (n := s₃ * (s₃ - 1))
    rw [h4, h5] at h6
    exact h6
  have h3 : (s₃ : ℝ) * ((s₃ : ℝ) - 1) ≥ (s₃ : ℝ) * (s₃ : ℝ) / 2 := by
    nlinarith [hs₃real]
  have h4 : (n : ℝ) / (2 * η ^ 2) / 2 ≤ (s₃ : ℝ) * (s₃ : ℝ) / 2 := by linarith [h1]
  have hmid : (n : ℝ) / (4 * η ^ 2) ≤ (s₃ : ℝ) * ((s₃ : ℝ) - 1) := by
    have h6 : (n : ℝ) / (2 * η ^ 2) / 2 = (n : ℝ) / (4 * η ^ 2) := by field_simp; ring
    linarith [h3, h4, h6.le, h6.ge]
  have h6 : (n : ℝ) * ((n : ℝ) - 1) ≤ (n : ℝ) * (n : ℝ) := by
    have : (1 : ℝ) ≤ (n : ℝ) := by linarith
    nlinarith
  have h7 : (n : ℝ) * ((n : ℝ) - 1) / ((s₃ : ℝ) * ((s₃ : ℝ) - 1)) ≤ 4 * η ^ 2 * (n : ℝ) := by
    rw [div_le_iff₀ hcast]
    have h8 : (n : ℝ) * (n : ℝ) ≤ (4 * η ^ 2 * (n : ℝ)) * ((n : ℝ) / (4 * η ^ 2)) := by
      have heq : (4 * η ^ 2 * (n : ℝ)) * ((n : ℝ) / (4 * η ^ 2)) = (n : ℝ) * (n : ℝ) := by
        rw [← mul_div_assoc]
        field_simp
      exact le_of_eq heq.symm
    have h8' : (4 * η ^ 2 * (n : ℝ)) * ((n : ℝ) / (4 * η ^ 2)) ≤
        (4 * η ^ 2 * (n : ℝ)) * ((s₃ : ℝ) * ((s₃ : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_left hmid (by positivity)
    linarith [h6, h8, h8']
  have h9 : 4 * η ^ 2 * (n : ℝ) ≤ ε * (n : ℝ) / 4 := by nlinarith [hηsq, hnpos]
  linarith [hnn, h7, h9]

/-- The `𝓗₂` estimate: if `(3/2)η ≤ ε/8` and `8/ε ≤ n` then
`⌈(3/2)·ηn⌉₊ ≤ εn/4`. -/
theorem weakStability_hc2 {ε η : ℝ} {n : ℕ} (hε0 : 0 < ε) (hη0 : 0 < η)
    (hη3 : (3 / 2) * η ≤ ε / 8) (hn : 8 / ε ≤ (n : ℝ)) :
    ((⌈(3 / 2) * (η * (n : ℝ))⌉₊ : ℕ) : ℝ) ≤ ε * (n : ℝ) / 4 := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have h : 0 < 8 / ε := by positivity
    linarith
  have h3 : (⌈(3 / 2) * (η * (n : ℝ))⌉₊ : ℝ) < (3 / 2) * (η * (n : ℝ)) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have h5 : 8 ≤ ε * (n : ℝ) := by
    rw [div_le_iff₀ hε0] at hn
    linarith [hn]
  have h4 : ε * (n : ℝ) / 4 ≥ 2 := by linarith
  have h6 : (3 / 2) * (η * (n : ℝ)) ≤ ε * (n : ℝ) / 8 := by
    have h7 := mul_le_mul_of_nonneg_right hη3 (le_of_lt hnpos)
    nlinarith [h7]
  linarith [h3, h4, h6]

/-- The AKS logarithmic estimate of Theorem 1.3. -/
theorem weakStability_hfinal {ε KAKS C₁ η εb : ℝ} {n : ℕ}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 1000) (hKAKS0 : 0 < KAKS) (hC₁pos : 0 < C₁)
    (hC₁log : C₁ ≤ Real.log (1 / (η * ε ^ 10)))
    (hC₁ge : 10 ^ 9 * KAKS / ε ^ 21 ≤ C₁)
    (hεbge : ε ^ 11 / 10 ^ 6 ≤ εb) (hεb0 : 0 < εb) (hη0 : 0 < η) (hnpos : 0 < (n : ℝ)) :
    KAKS * (4 / ε ^ 10 * (n : ℝ)) / Real.log (1 / (η * ε ^ 10)) ≤ εb * (n : ℝ) := by
  have hε10 : (0 : ℝ) < ε ^ 10 := by positivity
  have hlogpos : 0 < Real.log (1 / (η * ε ^ 10)) := lt_of_lt_of_le hC₁pos hC₁log
  have h2 : KAKS * (4 / ε ^ 10 * (n : ℝ)) / Real.log (1 / (η * ε ^ 10)) ≤
      KAKS * (4 / ε ^ 10 * (n : ℝ)) / C₁ :=
    div_le_div_of_nonneg_left (by positivity) hC₁pos hC₁log
  have h3 : KAKS * (4 / ε ^ 10 * (n : ℝ)) / C₁ ≤ εb * (n : ℝ) := by
    rw [div_le_iff₀ hC₁pos]
    have h15 : (ε ^ 11 / 10 ^ 6) * (10 ^ 9 * KAKS / ε ^ 21) ≤ εb * C₁ :=
      mul_le_mul hεbge hC₁ge (by positivity) (le_of_lt hεb0)
    have h16 : KAKS * 4 / ε ^ 10 ≤ (ε ^ 11 / 10 ^ 6) * (10 ^ 9 * KAKS / ε ^ 21) := by
      have h17 : (ε ^ 11 / 10 ^ 6) * (10 ^ 9 * KAKS / ε ^ 21) = 1000 * KAKS / ε ^ 10 := by
        field_simp
        ring
      rw [h17]
      have h18 : KAKS * 4 ≤ 1000 * KAKS := by linarith [hKAKS0]
      rw [div_le_div_iff₀ hε10 hε10]
      nlinarith [h18, hε10]
    have h19 : KAKS * (4 / ε ^ 10 * (n : ℝ)) = (KAKS * 4 / ε ^ 10) * (n : ℝ) := by ring
    rw [h19]
    nlinarith [h15, h16, hnpos]
  linarith [h2, h3]

/-! ## The assembly: Theorem 1.3 for `ε ≤ 1/1000` -/

set_option maxHeartbeats 4000000 in
/-- **Theorem 1.3 of the paper** (weak stability), for `ε ≤ 1/1000`, from the
two deep inputs Kahn (Theorem 4.6) and Alon–Krivelevich–Sudakov (Theorem
6.6). -/
theorem weakStability_small (hK : KahnStatement) (hAKS : AKSStatement) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 1000) : WeakStabilityInstance ε := by
  classical
  obtain ⟨KAKS, hKAKS0, ζ₀, hζ₀0, hAKS'⟩ := hAKS
  have hε1' : ε ≤ 1 := by linarith
  have hε10 : (0 : ℝ) < ε ^ 10 := by positivity
  have hε20le2 : ε ^ 20 ≤ ε ^ 2 := eps20_le_eps2 hε0 hε1'
  -- the constants `C₁`, `ζc`
  let C₁ : ℝ := 10 ^ 9 * KAKS * (1 / ε) ^ 21 + 1
  have hC₁pos : 0 < C₁ := by
    have h : (0 : ℝ) < 10 ^ 9 * KAKS * (1 / ε) ^ 21 := by positivity
    simp only [C₁]; linarith
  let ζc : ℝ := (1 / 4) * min ζ₀ 1 * min (Real.exp (-C₁)) 1 * ε ^ 30
  have hexp0 : 0 < Real.exp (-C₁) := Real.exp_pos _
  have hmin1 : 0 < min ζ₀ 1 := lt_min hζ₀0 one_pos
  have hmin2 : 0 < min (Real.exp (-C₁)) 1 := lt_min hexp0 one_pos
  have hζcpos : 0 < ζc := by
    have h' : (0 : ℝ) < (1 / 4) * min ζ₀ 1 * min (Real.exp (-C₁)) 1 := by positivity
    simp only [ζc]; positivity
  have hmin1le : min ζ₀ 1 ≤ 1 := min_le_right _ _
  have hmin2le : min (Real.exp (-C₁)) 1 ≤ 1 := min_le_right _ _
  have hmin2le' : min (Real.exp (-C₁)) 1 ≤ Real.exp (-C₁) := min_le_left _ _
  have hmin1le' : min ζ₀ 1 ≤ ζ₀ := min_le_left _ _
  have hε30le : ε ^ 30 ≤ 1 := pow_le_one₀ (le_of_lt hε0) hε1'
  have hζcle₀ : ζc ≤ ζ₀ := by
    have hAB : (1 / 4) * min ζ₀ 1 * min (Real.exp (-C₁)) 1 ≤ (1 / 4) * ζ₀ * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hmin1le' (by norm_num)) hmin2le (le_of_lt hmin2)
        (by positivity)
    have hABC : (1 / 4) * min ζ₀ 1 * min (Real.exp (-C₁)) 1 * ε ^ 30 ≤ (1 / 4) * ζ₀ * 1 * 1 :=
      mul_le_mul hAB hε30le (by positivity) (by positivity)
    have hfin : ζc ≤ (1 / 4) * ζ₀ * 1 * 1 := by simpa only [ζc] using hABC
    linarith [hfin, hζ₀0]
  have hζcle_exp : ζc ≤ (1 / 4) * Real.exp (-C₁) := by
    have hAB : (1 / 4) * min ζ₀ 1 * min (Real.exp (-C₁)) 1 ≤ (1 / 4) * 1 * Real.exp (-C₁) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hmin1le (by norm_num)) hmin2le' (le_of_lt hmin2)
        (by positivity)
    have hABC : (1 / 4) * min ζ₀ 1 * min (Real.exp (-C₁)) 1 * ε ^ 30 ≤
        (1 / 4) * 1 * Real.exp (-C₁) * 1 :=
      mul_le_mul hAB hε30le (by positivity) (by positivity)
    have hfin : ζc ≤ (1 / 4) * 1 * Real.exp (-C₁) * 1 := by simpa only [ζc] using hABC
    linarith [hfin]
  have hζcle : ζc ≤ ε ^ 30 / 4 := by
    have hAB : (1 / 4) * min ζ₀ 1 * min (Real.exp (-C₁)) 1 ≤ (1 / 4) * 1 * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hmin1le (by norm_num)) hmin2le (le_of_lt hmin2)
        (by positivity)
    have hfin : ζc ≤ (1 / 4) * 1 * 1 * ε ^ 30 := by
      simpa only [ζc] using mul_le_mul_of_nonneg_right hAB (by positivity : (0 : ℝ) ≤ ε ^ 30)
    linarith [hfin]
  have hζclog : C₁ ≤ Real.log (1 / ζc) := by
    have hexp1 : Real.exp (-C₁) ≤ 1 := by
      rw [Real.exp_le_one_iff]; linarith [hC₁pos]
    have h1 : (1 / 4) * Real.exp (-C₁) * 4 * Real.exp C₁ = 1 := by
      have h2 : Real.exp (-C₁) * Real.exp C₁ = 1 := by
        rw [← Real.exp_add]; simp
      linarith [h2]
    have h2 : 1 / ζc ≥ 4 * Real.exp C₁ := by
      rw [ge_iff_le, le_div_iff₀ hζcpos]
      nlinarith [hζcle_exp, h1, Real.exp_pos C₁]
    have h3 : Real.log (4 * Real.exp C₁) ≤ Real.log (1 / ζc) :=
      Real.log_le_log (by positivity) h2
    have h4 : Real.log (4 * Real.exp C₁) = Real.log 4 + C₁ := by
      rw [Real.log_mul (by norm_num) (Real.exp_ne_zero C₁), Real.log_exp]
    have h5 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith [h3, h4.le, h4.ge, h5]
  have hC₁ge : 10 ^ 9 * KAKS / ε ^ 21 ≤ C₁ := by
    have h14 : (1 / ε) ^ 21 = 1 / ε ^ 21 := one_div_pow ε 21
    have h15 : 10 ^ 9 * KAKS * (1 / ε ^ 21) = 10 ^ 9 * KAKS / ε ^ 21 := by ring
    simp only [C₁]
    rw [h14]
    linarith [h15.le, h15.ge]
  -- the constants `η`, `r₁`
  let η : ℝ := ζc / ε ^ 10
  have hη0 : 0 < η := by
    have h : (0 : ℝ) < ε ^ 10 := by positivity
    simp only [η]; positivity
  have hηeq : η * ε ^ 10 = ζc := by
    simp only [η]
    field_simp
  have hη20 : η ≤ ε ^ 20 / 4 := by
    have h2 : (0 : ℝ) < ε ^ 10 := by positivity
    have h3 : ζc / ε ^ 10 ≤ (ε ^ 30 / 4) / ε ^ 10 :=
      div_le_div_of_nonneg_right hζcle (le_of_lt h2)
    have h4 : (ε ^ 30 / 4) / ε ^ 10 = ε ^ 20 / 4 := by
      field_simp
    linarith [h3, h4.le, h4.ge]
  have hη2le : η ≤ ε ^ 2 / 4 := le_trans hη20 (by linarith [hε20le2])
  have hηhalf : η ≤ 1 / 2 := by
    have h2 : ε ^ 2 ≤ 1 := pow_le_one₀ (le_of_lt hε0) hε1'
    linarith [hη2le, h2]
  have hηsq : 4 * η ^ 2 ≤ ε / 4 := four_mul_sq_le hε0 hε1' hη0 hη2le
  have hη3 : 8 * η ≤ ε / 24 := eight_mul_le hε0 hε1 hη2le
  have hη32 : (3 / 2) * η ≤ ε / 8 := three_halves_mul_le hε0 hε1 hη2le
  let r₁ : ℕ := ⌊1 / η⌋₊ + 1
  have hr₁_ge : (1 : ℝ) / η ≤ (r₁ : ℝ) := by
    have h1 : (1 : ℝ) / η < (⌊1 / η⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    simp only [r₁]
    push_cast
    linarith
  have hηinv : 4 * (1 / ε) ^ 20 ≤ 1 / η := by
    have h1 : (1 : ℝ) / η = ε ^ 10 / ζc := by
      simp only [η]
      field_simp
    rw [h1]
    have h2 : ε ^ 10 / (ε ^ 30 / 4) ≤ ε ^ 10 / ζc :=
      div_le_div_of_nonneg_left (by positivity) hζcpos hζcle
    have h3 : ε ^ 10 / (ε ^ 30 / 4) = 4 * (1 / ε) ^ 20 := by
      field_simp
    linarith [h2, h3.le, h3.ge]
  have hr₁_20 : 4 * (1 / ε) ^ 20 ≤ (r₁ : ℝ) := le_trans hηinv hr₁_ge
  have hr₂2 : 2 ≤ r₁ := by
    have h1 : (2 : ℝ) ≤ (r₁ : ℝ) := by
      have h3 : (1 : ℝ) ≤ (1 / ε) ^ 20 := one_le_inv_pow hε0 hε1' 20
      linarith [hr₁_20, h3]
    exact_mod_cast h1
  obtain ⟨DK, hDK0, hKahn⟩ := kahn_colorable hK (by norm_num : (0 : ℝ) < 1 / 2) hr₂2
  -- `τ`, `K` and the reordering margins
  let τ : ℝ := 1 - ε / 6
  let K : ℕ := ⌈(1 / ε) ^ 2⌉₊
  have hτ0 : 0 < τ := by simp only [τ]; linarith
  have hτ1 : τ < 1 := by simp only [τ]; linarith
  have h1mτ : 1 - τ = ε / 6 := by simp only [τ]; ring
  have hK1 : 1 ≤ K := Nat.one_le_ceil_iff.mpr (by positivity)
  have hmarg : ReorderingMargins r₁ τ K := by
    have h := weakStability_margins (ε := ε) (r₁ := r₁) hε0 hε1 hr₁_20
    simpa only [τ, K] using h
  have hvolBound_ge : ε ^ 10 / 14400 ≤ volBound τ K := by
    have h := weakStability_volBound_ge (ε := ε) hε0 hε1
    simpa only [τ, K] using h
  have hvolBound_pos : 0 < volBound τ K :=
    lt_of_lt_of_le (by positivity : (0 : ℝ) < ε ^ 10 / 14400) hvolBound_ge
  have hCsf2 : 2 * (sizeFactor τ K + 1 + 1) ≤ 4 / ε ^ 10 := by
    have h := weakStability_Csf2 (ε := ε) hε0 hε1
    simpa only [τ, K] using h
  have hCsf3 : (sizeFactor τ K + 1 + 1) ^ 2 * η ≤ 2 := by
    have h := weakStability_Csf3 (ε := ε) hε0 hε1
    have h' : (sizeFactor τ K + 1 + 1) ^ 2 * (ε ^ 20 / 4) ≤ 2 := by simpa only [τ, K] using h
    have hnn : (0 : ℝ) ≤ (sizeFactor τ K + 1 + 1) ^ 2 := sq_nonneg _
    nlinarith [h', hη20, hnn]
  -- `M`, `εb`
  let M : ℕ := ⌈1 / volBound τ K⌉₊ + 1
  have hMvol : (1 : ℝ) ≤ (M : ℝ) * volBound τ K := by
    have h1 : 1 / volBound τ K ≤ (M : ℝ) := by
      have h := Nat.le_ceil (1 / volBound τ K)
      simp only [M] at h ⊢
      push_cast
      linarith
    rw [div_le_iff₀ hvolBound_pos] at h1
    linarith
  have hMle : (M : ℝ) ≤ 10 ^ 5 * (1 / ε) ^ 10 := by
    have hceil : ((⌈1 / volBound τ K⌉₊ : ℕ) : ℝ) < 1 / volBound τ K + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have h1 : 1 / volBound τ K ≤ 14400 * (1 / ε) ^ 10 := by
      have h2 : (1 : ℝ) / volBound τ K ≤ 1 / (ε ^ 10 / 14400) :=
        one_div_le_one_div_of_le (by positivity) hvolBound_ge
      have h3 : (1 : ℝ) / (ε ^ 10 / 14400) = 14400 / ε ^ 10 := by field_simp
      have h4 : (14400 : ℝ) / ε ^ 10 = 14400 * (1 / ε) ^ 10 := div_pow_eq_mul 14400 ε 10
      linarith [h2, h3.le, h3.ge, h4.le, h4.ge]
    have h5 : (1 : ℝ) ≤ 14400 * (1 / ε) ^ 10 := by
      have h6 : (1 : ℝ) ≤ (1 / ε) ^ 10 := one_le_inv_pow hε0 hε1' 10
      linarith [h6]
    simp only [M]
    push_cast
    linarith
  let εb : ℝ := ε / (10 * (M : ℝ))
  have hεb0 : 0 < εb := by
    have h : (0 : ℝ) < 10 * (M : ℝ) := by positivity
    simp only [εb]; positivity
  have hεbge : ε ^ 11 / 10 ^ 6 ≤ εb := by
    have hM10 : 10 * (M : ℝ) ≤ 10 * (10 ^ 5 * (1 / ε) ^ 10) := by linarith [hMle]
    have h10 : ε / (10 * (10 ^ 5 * (1 / ε) ^ 10)) ≤ εb := by
      simp only [εb]
      exact div_le_div_of_nonneg_left (le_of_lt hε0) (by positivity) hM10
    have h11 : ε / (10 * (10 ^ 5 * (1 / ε) ^ 10)) = ε ^ 11 / 10 ^ 6 := by
      rw [one_div_pow]
      field_simp
    linarith [h10, h11.le, h11.ge]
  -- the AKS threshold function `Δ₀`
  let Δ₀ : ℝ → ℝ := fun ζ => if h : 0 < ζ ∧ ζ ≤ ζ₀ then (hAKS' ζ h.1 h.2).choose else 0
  have hAKSfn : ∀ (ζ : ℝ), 0 < ζ → ζ ≤ ζ₀ → ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℝ), Δ₀ ζ ≤ Δ →
      (G.maxDegree : ℝ) ≤ Δ →
      (∀ v : V, (nbrEdges G v : ℝ) ≤ ζ * Δ ^ 2) →
      ∃ k : ℕ, (k : ℝ) ≤ KAKS * Δ / Real.log (1 / ζ) ∧ G.Colorable k := by
    intro ζ hζ0 hζζ₀ V _ _ G _ Δ hΔ hmax hdeg
    have hval : Δ₀ ζ = (hAKS' ζ hζ0 hζζ₀).choose := by
      simp only [Δ₀]
      rw [dif_pos ⟨hζ0, hζζ₀⟩]
    rw [hval] at hΔ
    exact (hAKS' ζ hζ0 hζζ₀).choose_spec V G Δ hΔ hmax hdeg
  -- the threshold `n₀`
  let E₀ : ℝ := max (Δ₀ (η * ε ^ 10) * ε ^ 10 / 4 + 1) 0
  let R : ℝ := 1000 + E₀ + (DK / η + 1) + (16 * η ^ 2 + 1) + (8 / ε + 1) +
    (24 * ((M : ℝ) + 2) / ε + 4)
  let N₀ : ℕ := ⌈R⌉₊ + 1
  refine ⟨η, hη0, N₀, ?_⟩
  intro n hn 𝓗 hlin hΔ hno
  have hnR : R ≤ (n : ℝ) := by
    have h1 : (⌈R⌉₊ : ℝ) ≤ ((N₀ : ℕ) : ℝ) := by
      simp only [N₀]; push_cast; linarith
    have h2 : R ≤ (⌈R⌉₊ : ℝ) := Nat.le_ceil R
    have h3 : ((N₀ : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hE0ge : (0 : ℝ) ≤ E₀ := le_max_right _ _
  have hR2 : (0 : ℝ) ≤ DK / η + 1 := by positivity
  have hR3 : (0 : ℝ) ≤ 16 * η ^ 2 + 1 := by positivity
  have hR4 : (0 : ℝ) ≤ 8 / ε + 1 := by positivity
  have hR5 : (0 : ℝ) ≤ 24 * ((M : ℝ) + 2) / ε + 4 := by positivity
  have hmax1 : 1000 ≤ (n : ℝ) := by
    have h : (1000 : ℝ) ≤ R := by simp only [R]; linarith
    linarith [h, hnR]
  have hn1000 : 1000 ≤ n := by exact_mod_cast hmax1
  have hmax2 : Δ₀ (η * ε ^ 10) * ε ^ 10 / 4 + 1 ≤ (n : ℝ) := by
    have h0 : Δ₀ (η * ε ^ 10) * ε ^ 10 / 4 + 1 ≤ E₀ := le_max_left _ _
    have h : E₀ ≤ R := by simp only [R]; linarith
    linarith [h0, h, hnR]
  have hmax3 : DK / η + 1 ≤ (n : ℝ) := by
    have h : DK / η + 1 ≤ R := by simp only [R]; linarith
    linarith [h, hnR]
  have hmax4 : 16 * η ^ 2 + 1 ≤ (n : ℝ) := by
    have h : 16 * η ^ 2 + 1 ≤ R := by simp only [R]; linarith
    linarith [h, hnR]
  have hmax5 : 8 / ε + 1 ≤ (n : ℝ) := by
    have h : 8 / ε + 1 ≤ R := by simp only [R]; linarith
    linarith [h, hnR]
  have hmax6 : 24 * ((M : ℝ) + 2) / ε + 4 ≤ (n : ℝ) := by
    have h : 24 * ((M : ℝ) + 2) / ε + 4 ≤ R := by simp only [R]; linarith
    linarith [h, hnR]
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith [hmax1]
  have h2n : 2 ≤ n := by exact_mod_cast (by linarith : (2 : ℝ) ≤ (n : ℝ))
  have hDKle : DK ≤ η * (n : ℝ) := by
    have h : DK / η ≤ (n : ℝ) - 1 := by linarith [hmax3]
    rw [div_le_iff₀ hη0] at h
    nlinarith [h, hη0, hnpos]
  -- the three size classes
  set 𝓗₁ : Hypergraph (Fin n) := 𝓗.sizeBetween (1 / η) (η * Real.sqrt n) with hdef₁
  set 𝓗₂ : Hypergraph (Fin n) := 𝓗.sizeLE (1 / η) with hdef₂
  set 𝓗₃ : Hypergraph (Fin n) := 𝓗.sizeGE (Real.sqrt n / η) with hdef₃
  have hlin₁ : 𝓗₁.IsLinear := by rw [hdef₁]; exact IsLinear.sizeBetween hlin _ _
  have hlin₂ : 𝓗₂.IsLinear := by rw [hdef₂]; exact IsLinear.sizeLE hlin _
  have hlin₃ : 𝓗₃.IsLinear := by rw [hdef₃]; exact IsLinear.sizeGE hlin _
  -- `𝓗₃`: the huge edges
  set s₃ : ℕ := ⌈Real.sqrt n / η⌉₊ with hdefs₃
  have hs₃2 : 2 ≤ s₃ := by
    rw [hdefs₃]
    have h1 : (1 : ℝ) < Real.sqrt n / η := by
      rw [lt_div_iff₀ hη0]
      have h3 : 2 * η ≤ Real.sqrt n := by
        rw [Real.le_sqrt (by positivity) (by positivity)]
        nlinarith [hmax4, hη0]
      nlinarith [h3, hη0]
    have h2 : 1 < ⌈Real.sqrt n / η⌉₊ := Nat.lt_ceil.mpr (by simpa using h1)
    omega
  have hcol₃ : 𝓗₃.Colorable (n * (n - 1) / (s₃ * (s₃ - 1))) :=
    colorable_sizeGE (𝓗 := 𝓗) hlin (a := Real.sqrt n / η) (s := s₃) hs₃2 le_rfl
  have hc₃ : (((n * (n - 1) / (s₃ * (s₃ - 1))) : ℕ) : ℝ) ≤ ε * (n : ℝ) / 4 :=
    weakStability_hc3 (ε := ε) (η := η) (n := n) hε0 hε1' hη0 hηsq hn1000
  -- `𝓗₂`: the tiny edges, via Kahn
  have hcol₂ : 𝓗₂.Colorable ⌈(3 / 2) * (η * (n : ℝ))⌉₊ := by
    have h2' : (1 + 1 / 2 : ℝ) = 3 / 2 := by norm_num
    have h := colorable_sizeLE_of_kahn (α := 1 / 2) (by norm_num) (r := r₁) hr₂2 (D₀ := DK)
      hDK0 hKahn hη0 hr₁_ge hDKle (𝓗 := 𝓗) hlin hΔ
    rw [h2'] at h
    exact h
  have hc₂ : ((⌈(3 / 2) * (η * (n : ℝ))⌉₊ : ℕ) : ℝ) ≤ ε * (n : ℝ) / 4 :=
    weakStability_hc2 (ε := ε) (η := η) (n := n) hε0 hη0 hη32 (by linarith [hmax5])
  -- `𝓗₁`: the middle edges, via the loop
  have hsize₁ : ∀ e ∈ 𝓗₁, (r₁ : ℝ) ≤ (edgeSize e : ℝ) := by
    intro e he
    have h := (mem_sizeBetween 𝓗 (1 / η) (η * Real.sqrt n) e).mp he
    have h1 : ((⌊1 / η⌋₊ : ℕ) : ℝ) ≤ 1 / η := Nat.floor_le (by positivity)
    have h2 : ((⌊1 / η⌋₊ : ℕ) : ℝ) < (edgeSize e : ℝ) := lt_of_le_of_lt h1 h.2.1
    have h3 : ⌊1 / η⌋₊ < edgeSize e := by exact_mod_cast h2
    have h4 : r₁ ≤ edgeSize e := by
      have hr : r₁ = ⌊1 / η⌋₊ + 1 := rfl
      omega
    exact_mod_cast h4
  have hvol_le : volume n 𝓗₁ ≤ (M : ℝ) * volBound τ K := by
    have h1 : volume n 𝓗₁ ≤ 1 := volume_le_one_of_linear hlin₁
    linarith [h1, hMvol]
  obtain ⟨D⟩ := exists_volumeDecomposition (r₁ := r₁) (τ := τ) (K := K) h2n hr₂2 hτ0 hτ1
    hK1 hmarg M 𝓗₁ hlin₁ hsize₁ hvol_le
  have hsmin : ∀ B ∈ D.blocks, 1 / η ≤ (edgeSize (B.2 : Set (Fin n)) : ℝ) := by
    intro B hB
    have h := (mem_sizeBetween 𝓗 (1 / η) (η * Real.sqrt n) _).mp (D.hBlockSub B hB B.2.2)
    exact le_of_lt h.2.1
  have hsmax : ∀ B ∈ D.blocks, (edgeSize (B.2 : Set (Fin n)) : ℝ) ≤ η * Real.sqrt n := by
    intro B hB
    have h := (mem_sizeBetween 𝓗 (1 / η) (η * Real.sqrt n) _).mp (D.hBlockSub B hB B.2.2)
    exact h.2.2
  have hΔthr : Δ₀ (η * ε ^ 10) ≤ 4 / ε ^ 10 * (n : ℝ) := by
    have h1 : Δ₀ (η * ε ^ 10) * ε ^ 10 / 4 ≤ (n : ℝ) := by linarith [hmax2]
    have h2 : (4 : ℝ) / ε ^ 10 * (n : ℝ) = 4 * (n : ℝ) / ε ^ 10 := by ring
    rw [h2, le_div_iff₀ hε10]
    nlinarith [h1, hnpos, hε10, le_of_lt hε0]
  have hC₁log : C₁ ≤ Real.log (1 / (η * ε ^ 10)) := by
    rw [hηeq]; exact hζclog
  have hfinal : KAKS * (4 / ε ^ 10 * (n : ℝ)) / Real.log (1 / (η * ε ^ 10)) ≤ εb * (n : ℝ) :=
    weakStability_hfinal hε0 hε1 hKAKS0 hC₁pos hC₁log hC₁ge hεbge hεb0 hη0 hnpos
  have hζ0f : η * ε ^ 10 ≤ ζ₀ := by rw [hηeq]; exact hζcle₀
  have hblocks : (famUnion (D.blocks.map (fun B => B.1))).Colorable
      (D.blocks.length * ⌈εb * (n : ℝ)⌉₊) :=
    colorable_block_of_decomposition (ε := ε) hε0 (K_AKS := KAKS) (Δ₀ := Δ₀) (ζ₀ := ζ₀)
      (η := η) (εb := εb) hAKSfn hη0 hηhalf hεb0 hζ0f hCsf2 hCsf3 hΔthr hfinal D hlin₁
      hsmin hsmax
  -- the good part
  have hgoodlin : D.good.IsLinear := hlin₁.mono D.hGoodSub
  have hgoodsize : ∀ e : D.good, (r₁ : ℝ) ≤ (edgeSize (e : Set (Fin n)) : ℝ) :=
    fun e => hsize₁ _ (D.hGoodSub e.2)
  have hm1 : 4 * (n : ℝ) / ((r₁ : ℝ) - 1) < (ε / 6) * (n : ℝ) / 4 := by
    have hr1pos : (0 : ℝ) < (r₁ : ℝ) - 1 := by
      have h : (2 : ℝ) ≤ (r₁ : ℝ) := by exact_mod_cast hr₂2
      linarith
    have hr1r : (2 : ℝ) ≤ (r₁ : ℝ) := by exact_mod_cast hr₂2
    have h1 : 4 * (n : ℝ) / ((r₁ : ℝ) - 1) ≤ 4 * (n : ℝ) / ((r₁ : ℝ) / 2) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      linarith [hr1r]
    have h2 : 4 * (n : ℝ) / ((r₁ : ℝ) / 2) = 8 * (n : ℝ) / (r₁ : ℝ) := by field_simp; ring
    rw [h2] at h1
    have h3 : 8 * (n : ℝ) / (r₁ : ℝ) ≤ 8 * η * (n : ℝ) := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (r₁ : ℝ))]
      have h4 : (1 : ℝ) ≤ η * (r₁ : ℝ) := by
        have h : (1 : ℝ) / η ≤ (r₁ : ℝ) := hr₁_ge
        rw [div_le_iff₀ hη0] at h
        linarith [h]
      nlinarith [h4, hnpos]
    have h5 : 8 * η * (n : ℝ) < (ε / 6) * (n : ℝ) / 4 := by
      have h6 : 8 * η ≤ ε / 24 := hη3
      nlinarith [h6, hnpos]
    linarith [h1, h3, h5]
  have hbig : (((bigFinset (1 / 2) D.good).card : ℕ) : ℝ) < (ε / 6) * (n : ℝ) / 2 := by
    have hempty : bigFinset (1 / 2) D.good = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨e, he⟩
      rw [mem_bigFinset] at he
      have h1 : (edgeSize (e : Set (Fin n)) : ℝ) ≤ η * Real.sqrt n := by
        have h2 := (mem_sizeBetween 𝓗 (1 / η) (η * Real.sqrt n) _).mp (D.hGoodSub e.2)
        exact h2.2.2
      have h3 : η * Real.sqrt n < (n : ℝ) / 4 := by
        have h4 : Real.sqrt n ≤ (n : ℝ) := by
          rw [Real.sqrt_le_iff]
          exact ⟨hnpos.le, by nlinarith [hnpos, hmax1]⟩
        have h6 : η * (n : ℝ) ≤ (n : ℝ) / 4 := by
          have h7 : η ≤ 1 / 4 := by linarith [hηhalf]
          nlinarith [h7, hnpos]
        nlinarith [h4, h6, hη0, hnpos]
      have h8 : (1 / 2 : ℝ) / 2 * (n : ℝ) = (n : ℝ) / 4 := by ring
      rw [h8] at he
      linarith [h1, h3]
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    have : (0 : ℝ) < (ε / 6) * (n : ℝ) / 2 := by positivity
    linarith
  have hgood' : ∀ e : D.good, (precedingDegree D.good D.ord e : ℝ) ≤ (ε / 6) * (n : ℝ) := by
    intro e
    have h := D.hGood e
    rw [h1mτ] at h
    exact h
  have hgood : D.good.Colorable ⌈ε * (n : ℝ) / 3⌉₊ :=
    colorable_good_of_ordering hε0 hε1' h2n hr₂2 hgoodlin hgoodsize D.ord hgood' hm1 hbig
  -- combine the three pieces
  have h₁ : 𝓗₁.Colorable (D.blocks.length * ⌈εb * (n : ℝ)⌉₊ + ⌈ε * (n : ℝ) / 3⌉₊) := by
    refine Hypergraph.Colorable.union ?_ ?_ ?_ hblocks hgood
    · intro e he
      obtain ⟨W, hW, heW⟩ := he
      obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hW
      exact D.hBlockSub B hB heW
    · exact D.hGoodSub
    · intro e he
      rcases (D.hCover e).mp he with h | ⟨B, hB, heB⟩
      · exact Or.inr h
      · exact Or.inl ⟨B.1, List.mem_map.mpr ⟨B, hB, rfl⟩, heB⟩
  -- the block count
  have hpairwise : (D.blocks.map (fun B => B.1)).Pairwise Disjoint :=
    pairwise_map_sub D.hBlocksDisj
  have hsubmap : ∀ W ∈ D.blocks.map (fun B => B.1), W ⊆ 𝓗₁ := by
    intro W hW
    obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hW
    exact D.hBlockSub B hB
  have hsum_le : (D.blocks.map (fun B => volume n B.1)).sum ≤ 1 := by
    have h1 := volume_sum_le_one (l := D.blocks.map (fun B => B.1)) (𝓖 := 𝓗₁) hpairwise
      hsubmap hlin₁
    simpa [List.map_map, Function.comp_def] using h1
  have hlen : (D.blocks.length : ℝ) ≤ (M : ℝ) := by
    have h1 : (D.blocks.length : ℝ) * volBound τ K ≤
        (D.blocks.map (fun B => volume n B.1)).sum :=
      Commons.Data.List.length_mul_le_sum D.blocks (fun B => volume n B.1) (volBound τ K)
        D.hBlockVol
    have h4 : (D.blocks.length : ℝ) * volBound τ K ≤ (M : ℝ) * volBound τ K := by
      linarith [h1, hsum_le, hMvol]
    exact le_of_mul_le_mul_right h4 hvolBound_pos
  -- the colour budget
  have ha : (((D.blocks.length * ⌈εb * (n : ℝ)⌉₊ : ℕ) : ℕ) : ℝ) ≤
      ε * (n : ℝ) / 10 + (M : ℝ) := by
    have hceil : (⌈εb * (n : ℝ)⌉₊ : ℝ) ≤ εb * (n : ℝ) + 1 :=
      le_of_lt (Nat.ceil_lt_add_one (by positivity))
    have h1 : ((D.blocks.length * ⌈εb * (n : ℝ)⌉₊ : ℕ) : ℝ) =
        (D.blocks.length : ℝ) * (⌈εb * (n : ℝ)⌉₊ : ℝ) := by push_cast; ring
    have h2 : (D.blocks.length : ℝ) * (⌈εb * (n : ℝ)⌉₊ : ℝ) ≤
        (M : ℝ) * (εb * (n : ℝ) + 1) :=
      mul_le_mul hlen hceil (by positivity) (by positivity)
    have h3 : (M : ℝ) * (εb * (n : ℝ) + 1) = ε * (n : ℝ) / 10 + (M : ℝ) := by
      have hMne : (M : ℝ) ≠ 0 := by positivity
      simp only [εb]
      field_simp
    linarith [h1, h2, h3.le, h3.ge]
  have hgoodceil : ((⌈ε * (n : ℝ) / 3⌉₊ : ℕ) : ℝ) ≤ ε * (n : ℝ) / 3 + 1 :=
    le_of_lt (Nat.ceil_lt_add_one (by positivity))
  have hMn : (M : ℝ) + 1 ≤ ε * (n : ℝ) / 24 := by
    have h1 : 24 * ((M : ℝ) + 2) / ε ≤ (n : ℝ) - 4 := by linarith [hmax6]
    rw [div_le_iff₀ hε0] at h1
    nlinarith [h1, hε0, hnpos]
  have htot : (((⌈(3 / 2) * (η * (n : ℝ))⌉₊ +
      (D.blocks.length * ⌈εb * (n : ℝ)⌉₊ + ⌈ε * (n : ℝ) / 3⌉₊) +
      n * (n - 1) / (s₃ * (s₃ - 1))) : ℕ) : ℝ) ≤ ε * (n : ℝ) := by
    have hsplit : (((⌈(3 / 2) * (η * (n : ℝ))⌉₊ +
        (D.blocks.length * ⌈εb * (n : ℝ)⌉₊ + ⌈ε * (n : ℝ) / 3⌉₊) +
        n * (n - 1) / (s₃ * (s₃ - 1))) : ℕ) : ℝ) =
        ((⌈(3 / 2) * (η * (n : ℝ))⌉₊ : ℕ) : ℝ) +
        (((D.blocks.length * ⌈εb * (n : ℝ)⌉₊ : ℕ) : ℝ) +
          ((⌈ε * (n : ℝ) / 3⌉₊ : ℕ) : ℝ)) +
        (((n * (n - 1) / (s₃ * (s₃ - 1))) : ℕ) : ℝ) := by push_cast; ring
    rw [hsplit]
    linarith [hc₂, ha, hgoodceil, hc₃, hMn]
  refine ⟨_, htot, ?_⟩
  refine Hypergraph.Colorable.union3 (𝓖₁ := 𝓗₂) (𝓖₂ := 𝓗₁) (𝓖₃ := 𝓗₃)
    (sizeLE_subset 𝓗 _) (sizeBetween_subset 𝓗 _ _) (sizeGE_subset 𝓗 _) ?_ hcol₂ h₁ hcol₃
  intro e he
  exact (cover_size_classes (𝓗 := 𝓗) (η := η) hno e he).imp id (fun h => h)


/-- **Theorem 1.3 of the paper** (weak stability), for every `ε > 0`, from the
two deep inputs Kahn (Theorem 4.6) and Alon–Krivelevich–Sudakov (Theorem
6.6).  For `ε > 1/1000` one applies the case `ε₁ = min ε (1/1000)` and uses
that the number of colours is at most `ε₁n ≤ εn`. -/
theorem weakStability_of_deep (hK : KahnStatement) (hAKS : AKSStatement) (ε : ℝ)
    (hε0 : 0 < ε) : WeakStabilityInstance ε := by
  rcases le_or_gt ε (1 / 1000) with hε1 | hε1
  · exact weakStability_small hK hAKS hε0 hε1
  · have hε1pos : 0 < min ε (1 / 1000) := lt_min hε0 (by norm_num)
    have hε1le : min ε (1 / 1000) ≤ 1 / 1000 := min_le_right _ _
    obtain ⟨η, hη0, n₀, hn₀⟩ := weakStability_small hK hAKS hε1pos hε1le
    refine ⟨η, hη0, n₀, ?_⟩
    intro n hn 𝓗 hlin hΔ hno
    obtain ⟨k, hk, hcol⟩ := hn₀ n hn 𝓗 hlin hΔ hno
    exact ⟨k, le_trans hk (mul_le_mul_of_nonneg_right (min_le_left _ _)
      (Nat.cast_nonneg n)), hcol⟩

end ErdosFaberLovaszConjecture
