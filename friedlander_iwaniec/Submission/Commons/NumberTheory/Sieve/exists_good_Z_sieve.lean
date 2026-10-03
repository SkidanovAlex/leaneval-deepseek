import Mathlib
import Submission.Commons.NumberTheory.Sieve.exists_large_L_good_Z

namespace Commons.NumberTheory.Sieve

open Filter Asymptotics

/-- Given `α > 0`, `c > 0`, `γ : ℝ`, there is a threshold `L₀` such that for every
`L ≥ L₀` there is a natural number `Z` satisfying a list of "good Z" conditions for
the Friedlander–Iwaniec sieve: `Z ≥ 3`, `log Z ≥ 200`, `(log Z)^10 ≤ √Z`,
`4 log Z ≤ L`, `3α L^8 ≤ (log Z)^9`, an upper bound relating `log Z`, `log L` and
`log log Z` to `c log Z`, and finally `γ + 8 log L + 8 log log Z ≤ L/(4 log Z)`. -/
theorem exists_good_Z_sieve
    (α : ℝ) (hα : 0 < α) (c : ℝ) (hc : 0 < c) (γ : ℝ) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ L : ℝ, L₀ ≤ L → ∃ Z : ℕ,
      3 ≤ Z ∧
      200 ≤ Real.log (Z : ℝ) ∧
      (Real.log (Z : ℝ)) ^ 10 ≤ Real.sqrt (Z : ℝ) ∧
      4 * Real.log (Z : ℝ) ≤ L ∧
      3 * α * L ^ 8 ≤ (Real.log (Z : ℝ)) ^ 9 ∧
      Real.log (3 * α * Real.log (Z : ℝ)) + 8 * Real.log L + 8 * Real.log (Real.log (Z : ℝ))
        ≤ c * Real.log (Z : ℝ) ∧
      γ + 8 * Real.log L + 8 * Real.log (Real.log (Z : ℝ)) ≤ L / (4 * Real.log (Z : ℝ)) := by
  set k : ℝ := (3 * α) ^ (1 / 9 : ℝ) with hk
  have hkpos : 0 < k := by rw [hk]; exact Real.rpow_pos_of_pos (by positivity) _
  have hkle : 0 ≤ k := le_of_lt hkpos
  have hk9 : k ^ 9 = 3 * α := by
    rw [hk, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 3 * α)]
    norm_num
  set B : ℝ := k + 200 with hB
  have hBpos : 0 < B := by rw [hB]; linarith
  have hLe : ∀ᶠ L : ℝ in atTop, (1 : ℝ) ≤ L := eventually_ge_atTop 1
  have hy_tendsto : Tendsto (fun L : ℝ => goodY k L) atTop atTop := by
    rw [tendsto_atTop] at ⊢
    intro b
    have hkL : Tendsto (fun L : ℝ => k * L ^ (8 / 9 : ℝ)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 8 / 9)).const_mul_atTop hkpos
    filter_upwards [hkL.eventually_ge_atTop (b - 200)] with L hL
    rw [goodY]; linarith
  -- (C1) `3 ≤ Z`
  have hC1 : ∀ᶠ L : ℝ in atTop, 3 ≤ goodZ k L := by
    filter_upwards [hLe] with L hL
    have h3 : (3 : ℝ) ≤ Real.exp (goodY k L) := by
      refine (Real.log_le_iff_le_exp (show (0 : ℝ) < 3 by norm_num)).mp ?_
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
      have h200 : 200 ≤ goodY k L := goodY_ge_const hkle (by linarith)
      linarith
    have h := le_trans h3 (exp_goodY_le_goodZ k L)
    exact_mod_cast h
  -- (C2) `200 ≤ log Z`
  have hC2 : ∀ᶠ L : ℝ in atTop, 200 ≤ Real.log (goodZ k L : ℝ) := by
    filter_upwards [hLe] with L hL
    exact le_trans (goodY_ge_const hkle (by linarith)) (goodY_le_log_goodZ k L)
  -- (C3) `(log Z)^10 ≤ sqrt Z`
  have hC3 : ∀ᶠ L : ℝ in atTop,
      (Real.log (goodZ k L : ℝ)) ^ 10 ≤ Real.sqrt (goodZ k L : ℝ) := by
    have hpy : ∀ᶠ L : ℝ in atTop,
        (2 * goodY k L) ^ 10 ≤ Real.exp (goodY k L / 2) :=
      hy_tendsto.eventually eventually_two_mul_pow_ten_le_exp_half
    filter_upwards [hpy, hLe] with L hL hL0
    calc (Real.log (goodZ k L : ℝ)) ^ 10 ≤ (2 * goodY k L) ^ 10 :=
          pow_le_pow_left₀ (log_goodZ_nonneg hkle (by linarith)) (log_goodZ_le_two_goodY hkle (by linarith)) 10
      _ ≤ Real.exp (goodY k L / 2) := hL
      _ ≤ Real.sqrt (goodZ k L : ℝ) := exp_half_le_sqrt_goodZ k L
  -- (C4) `4 log Z ≤ L`
  have hC4 : ∀ᶠ L : ℝ in atTop, 4 * Real.log (goodZ k L : ℝ) ≤ L := by
    have h1 : ∀ᶠ L : ℝ in atTop, Real.log (goodZ k L : ℝ) ≤ 2 * B * L ^ (8 / 9 : ℝ) := by
      filter_upwards [hLe] with L hL
      exact log_goodZ_le hkle hL hB
    have h2 : ∀ᶠ L : ℝ in atTop, 8 * B * L ^ (8 / 9 : ℝ) ≤ L := by
      have h9 : ∀ᶠ L : ℝ in atTop, (8 * B : ℝ) ≤ L ^ (1 / 9 : ℝ) :=
        (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 9)).eventually_ge_atTop (8 * B)
      filter_upwards [h9, hLe] with L h9L hL1
      have hL0 : (0 : ℝ) < L := lt_of_lt_of_le one_pos hL1
      have hLr : 0 < L ^ (8 / 9 : ℝ) := Real.rpow_pos_of_pos hL0 _
      have hsplit : L ^ (1 / 9 : ℝ) * L ^ (8 / 9 : ℝ) = L := by
        rw [← Real.rpow_add hL0]; norm_num
      calc 8 * B * L ^ (8 / 9 : ℝ) ≤ L ^ (1 / 9 : ℝ) * L ^ (8 / 9 : ℝ) := by nlinarith
        _ = L := hsplit
    filter_upwards [h1, h2] with L h1L h2L
    calc 4 * Real.log (goodZ k L : ℝ) ≤ 4 * (2 * B * L ^ (8 / 9 : ℝ)) := by linarith
      _ = 8 * B * L ^ (8 / 9 : ℝ) := by ring
      _ ≤ L := h2L
  -- (C5) `3 α L^8 ≤ (log Z)^9`
  have hC5 : ∀ᶠ L : ℝ in atTop, 3 * α * L ^ 8 ≤ (Real.log (goodZ k L : ℝ)) ^ 9 := by
    filter_upwards [hLe] with L hL1
    have hL0 : (0 : ℝ) < L := lt_of_lt_of_le one_pos hL1
    have hstep : k * L ^ (8 / 9 : ℝ) ≤ Real.log (goodZ k L : ℝ) :=
      le_trans (goodY_ge_rpow k L) (goodY_le_log_goodZ k L)
    have hkL0 : 0 ≤ k * L ^ (8 / 9 : ℝ) := mul_nonneg hkle (Real.rpow_nonneg hL0.le _)
    have hpow := pow_le_pow_left₀ hkL0 hstep 9
    have hLrpow : (L ^ (8 / 9 : ℝ)) ^ 9 = L ^ 8 := rpow_eight_ninths_pow_nine hL0.le
    calc 3 * α * L ^ 8 = k ^ 9 * L ^ 8 := by rw [hk9]
      _ = k ^ 9 * (L ^ (8 / 9 : ℝ)) ^ 9 := by rw [hLrpow]
      _ = (k * L ^ (8 / 9 : ℝ)) ^ 9 := by rw [mul_pow]
      _ ≤ (Real.log (goodZ k L : ℝ)) ^ 9 := hpow
  -- (C6) `log(3α log Z) + 8 log L + 8 log log Z ≤ c log Z`
  have hC6 : ∀ᶠ L : ℝ in atTop,
      Real.log (3 * α * Real.log (goodZ k L : ℝ)) + 8 * Real.log L
        + 8 * Real.log (Real.log (goodZ k L : ℝ))
        ≤ c * Real.log (goodZ k L : ℝ) := by
    have hup : ∀ᶠ L : ℝ in atTop,
        Real.log (3 * α * Real.log (goodZ k L : ℝ)) + 8 * Real.log L
          + 8 * Real.log (Real.log (goodZ k L : ℝ))
          ≤ (Real.log (3 * α) + 9 * Real.log (2 * B)) + 16 * Real.log L := by
      filter_upwards [hLe] with L hL1
      have hL0 : (0 : ℝ) < L := lt_of_lt_of_le one_pos hL1
      have hlogZpos : 0 < Real.log (goodZ k L : ℝ) := log_goodZ_pos hkle hL0.le
      have h3a : 0 < 3 * α := by positivity
      have hsplit : Real.log (3 * α * Real.log (goodZ k L : ℝ))
          = Real.log (3 * α) + Real.log (Real.log (goodZ k L : ℝ)) :=
        Real.log_mul h3a.ne' hlogZpos.ne'
      have hloglog := log_log_goodZ_le hkle hL1 hB
      rw [hsplit]
      linarith
    have hdom := eventually_add_log_le_rpow (Real.log (3 * α) + 9 * Real.log (2 * B)) 16
      (c * k / 3) (8 / 9) (by positivity) (by norm_num)
    have hlow : ∀ᶠ L : ℝ in atTop,
        (c * k / 3) * L ^ (8 / 9 : ℝ) ≤ c * Real.log (goodZ k L : ℝ) := by
      filter_upwards [hLe] with L hL1
      have hL0 : (0 : ℝ) < L := lt_of_lt_of_le one_pos hL1
      have hstep : k * L ^ (8 / 9 : ℝ) ≤ Real.log (goodZ k L : ℝ) :=
        le_trans (goodY_ge_rpow k L) (goodY_le_log_goodZ k L)
      have hLr : 0 ≤ L ^ (8 / 9 : ℝ) := Real.rpow_nonneg hL0.le _
      have hA : c * (k * L ^ (8 / 9 : ℝ)) ≤ c * Real.log (goodZ k L : ℝ) :=
        mul_le_mul_of_nonneg_left hstep (le_of_lt hc)
      have hck : 0 ≤ c * k := mul_nonneg (le_of_lt hc) hkle
      have hle3 : c * k / 3 ≤ c * k := by linarith
      have hB2 : (c * k / 3) * L ^ (8 / 9 : ℝ) ≤ c * (k * L ^ (8 / 9 : ℝ)) := by
        have := mul_le_mul_of_nonneg_right hle3 hLr
        rwa [mul_assoc] at this
      exact le_trans hB2 hA
    filter_upwards [hup, hdom, hlow] with L h1 h2 h3
    linarith
  -- common lower bound for `L / (4 log Z)`
  have hClow : ∀ᶠ L : ℝ in atTop,
      (1 / (8 * B)) * L ^ (1 / 9 : ℝ) ≤ L / (4 * Real.log (goodZ k L : ℝ)) := by
    filter_upwards [hLe] with L hL1
    have hL0 : (0 : ℝ) < L := lt_of_lt_of_le one_pos hL1
    have hlogZ_le : Real.log (goodZ k L : ℝ) ≤ 2 * goodY k L := log_goodZ_le_two_goodY hkle hL0.le
    have hy_le : goodY k L ≤ B * L ^ (8 / 9 : ℝ) := goodY_le_mul hL1 hB
    have h8ypos : 0 < 8 * goodY k L := by have h := goodY_ge_const hkle hL0.le; linarith
    have h4logpos : 0 < 4 * Real.log (goodZ k L : ℝ) := by
      have h := log_goodZ_pos hkle hL0.le; linarith
    have heq : L / (8 * B * L ^ (8 / 9 : ℝ)) = (1 / (8 * B)) * L ^ (1 / 9 : ℝ) := by
      have h := mul_div_rpow_gen 1 (8 * B) L hL0
      simpa using h
    have hs1 : L / (8 * B * L ^ (8 / 9 : ℝ)) ≤ L / (8 * goodY k L) :=
      div_le_div_of_nonneg_left (by positivity) h8ypos (by linarith)
    have hs2 : L / (8 * goodY k L) ≤ L / (4 * Real.log (goodZ k L : ℝ)) :=
      div_le_div_of_nonneg_left (by positivity) h4logpos (by linarith)
    calc (1 / (8 * B)) * L ^ (1 / 9 : ℝ) = L / (8 * B * L ^ (8 / 9 : ℝ)) := heq.symm
      _ ≤ L / (8 * goodY k L) := hs1
      _ ≤ L / (4 * Real.log (goodZ k L : ℝ)) := hs2
  -- (C7) `γ + 8 log L + 8 log log Z ≤ L / (4 log Z)`
  have hC7 : ∀ᶠ L : ℝ in atTop,
      γ + 8 * Real.log L + 8 * Real.log (Real.log (goodZ k L : ℝ))
        ≤ L / (4 * Real.log (goodZ k L : ℝ)) := by
    have hE8 : 0 < 1 / (8 * B) := by positivity
    have hup : ∀ᶠ L : ℝ in atTop,
        Real.log (Real.log (goodZ k L : ℝ)) ≤ Real.log (2 * B) + (8 / 9) * Real.log L := by
      filter_upwards [hLe] with L hL1
      exact log_log_goodZ_le hkle hL1 hB
    have hdom := eventually_add_log_le_rpow (γ + 8 * Real.log (2 * B)) (136 / 9) (1 / (8 * B))
      (1 / 9) hE8 (by norm_num)
    filter_upwards [hup, hdom, hClow] with L hupL hdomL hlowL
    calc (γ + 8 * Real.log L + 8 * Real.log (Real.log (goodZ k L : ℝ)))
        ≤ γ + 8 * Real.log L + 8 * (Real.log (2 * B) + (8 / 9) * Real.log L) := by linarith
      _ = (γ + 8 * Real.log (2 * B)) + (136 / 9) * Real.log L := by ring
      _ ≤ (1 / (8 * B)) * L ^ (1 / 9 : ℝ) := hdomL
      _ ≤ L / (4 * Real.log (goodZ k L : ℝ)) := hlowL
  have hall : ∀ᶠ L : ℝ in atTop, ∃ Z : ℕ,
      3 ≤ Z ∧
      200 ≤ Real.log (Z : ℝ) ∧
      (Real.log (Z : ℝ)) ^ 10 ≤ Real.sqrt (Z : ℝ) ∧
      4 * Real.log (Z : ℝ) ≤ L ∧
      3 * α * L ^ 8 ≤ (Real.log (Z : ℝ)) ^ 9 ∧
      Real.log (3 * α * Real.log (Z : ℝ)) + 8 * Real.log L + 8 * Real.log (Real.log (Z : ℝ))
        ≤ c * Real.log (Z : ℝ) ∧
      γ + 8 * Real.log L + 8 * Real.log (Real.log (Z : ℝ)) ≤ L / (4 * Real.log (Z : ℝ)) := by
    filter_upwards [hC1, hC2, hC3, hC4, hC5, hC6, hC7] with L h1 h2 h3 h4 h5 h6 h7
    exact ⟨goodZ k L, h1, h2, h3, h4, h5, h6, h7⟩
  obtain ⟨L₁, hL₁⟩ := Filter.eventually_atTop.mp hall
  exact ⟨max L₁ 1, lt_of_lt_of_le one_pos (le_max_right _ _),
    fun L hL => hL₁ L (le_trans (le_max_left _ _) hL)⟩

end Commons.NumberTheory.Sieve
