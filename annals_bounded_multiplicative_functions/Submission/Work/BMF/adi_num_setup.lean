import Mathlib
import Submission.Work.BMF.adi_all_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `adi_num_setup` : the numerical setup for the `X`-threshold

Given `k`, `C`, `θ > 0`, `ε > 0` with `ε ≤ θ/100`, there are an even length `ℓ ≥ 1` and a
threshold `X₀ > 0` such that for all `X ≥ X₀` and all `H, P₁, P₂` with

`Xᶿ ≤ H ≤ X^{1-θ}`,  `X^{ε²/2} ≤ P₁, P₂ ≤ X^ε`

all the numerical constraints used in the ADI (average dilation) argument hold: positivity,
`3 ≤ X/H`, `X/H ≤ P₁^{ℓ-1}`, `1 ≤ π₀(P_i)`, the cancellation of `P₁P₂` in the ratio, the
strict bound `8000 P₁² < X/H`, and the domination of the constant
`2 · symmConst k (max C (symmConst k C)) · (k+1) k^k k!` by `H/(2P₁²P₂)`.

The proof is entirely numerical: `X` is taken large enough that `X^{θ-2ε}` and `X^{θ-3ε}`
(whose exponents are positive because `ε ≤ θ/100`) dominate all the constants.
-/

namespace Work.BMF

open Real

/-- Threshold lemma: for `a > 0` and `r > 0`, `a^{1/r} ≤ X` implies `a ≤ X^r`. -/
lemma rpow_threshold {a r X : ℝ} (ha : 0 < a) (hr : 0 < r) (hX : a ^ (1 / r) ≤ X) :
    a ≤ X ^ r := by
  have hpow : (a ^ (1 / r)) ^ r = a := by
    rw [← Real.rpow_mul ha.le]
    have h1 : (1 / r) * r = 1 := by field_simp
    rw [h1, Real.rpow_one]
  calc a = (a ^ (1 / r)) ^ r := hpow.symm
    _ ≤ X ^ r := Real.rpow_le_rpow (Real.rpow_nonneg ha.le _) hX hr.le

/-- `π₀(P) = P/log P ≥ 1` for `P ≥ 3`. -/
lemma one_le_pi0 {P : ℝ} (hP : 3 ≤ P) : 1 ≤ pi0 P := by
  rw [pi0]
  have hP0 : (0 : ℝ) < P := by linarith
  have hl : 0 < Real.log P := Real.log_pos (by linarith)
  rw [one_le_div hl]
  have := Real.log_le_sub_one_of_pos hP0
  linarith

/-- `(X^ε)^n = X^{n·ε}`. -/
lemma rpow_natpow (X ε : ℝ) (hX : 0 ≤ X) (n : ℕ) : (X ^ ε) ^ n = X ^ (n * ε) := by
  rw [show (X ^ ε) ^ n = (X ^ ε) ^ ((n : ℕ) : ℝ) from (Real.rpow_natCast (X ^ ε) n).symm]
  rw [← Real.rpow_mul hX]
  congr 1
  push_cast
  ring

theorem adi_num_setup (k : ℕ) (C θ ε : ℝ) (hθ : 0 < θ) (hε : 0 < ε)
    (hεθ : ε ≤ θ / 100) :
    ∃ ℓ : ℕ, 1 ≤ ℓ ∧ Even ℓ ∧ ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ (X H P₁ P₂ : ℝ), X₀ ≤ X → X ^ θ ≤ H → H ≤ X ^ (1 - θ) →
        X ^ (ε ^ 2 / 2) ≤ P₁ → P₁ ≤ X ^ ε → X ^ (ε ^ 2 / 2) ≤ P₂ → P₂ ≤ X ^ ε →
        0 < X ∧ 0 < P₁ ∧ 0 < P₂ ∧ 0 < H ∧ 3 ≤ X / H ∧ X / H ≤ P₁ ^ (ℓ - 1) ∧
        1 ≤ Work.BMF.pi0 P₁ ∧ 1 ≤ Work.BMF.pi0 P₂ ∧
        (X / (P₁ * P₂)) / (H / (P₁ * P₂)) = X / H ∧
        8000 * P₁ ^ 2 < X / H ∧ 1 ≤ (H / (P₁ * P₂)) / (2 * P₁) ∧
        2 * Work.BMF.symmConst k (max C (Work.BMF.symmConst k C)) * ((k : ℝ) + 1) *
          (k : ℝ) ^ k * (k.factorial : ℝ) < (H / (P₁ * P₂)) / (2 * P₁) := by
  have hε2 : (0 : ℝ) < ε ^ 2 := by positivity
  have hε2h : (0 : ℝ) < ε ^ 2 / 2 := by positivity
  have hth2 : (0 : ℝ) < θ - 2 * ε := by nlinarith [hθ, hεθ]
  have hth3 : (0 : ℝ) < θ - 3 * ε := by nlinarith [hθ, hεθ]
  set B : ℝ := 2 * symmConst k (max C (symmConst k C)) * ((k : ℝ) + 1) *
      (k : ℝ) ^ k * (k.factorial : ℝ) with hB
  set L : ℕ := 2 * Nat.ceil (2 / ε ^ 2) + 2 with hLdef
  have hLge : 1 ≤ L := by omega
  have hLeven : Even L := by
    refine ⟨Nat.ceil (2 / ε ^ 2) + 1, ?_⟩
    rw [hLdef]; ring
  have hLsub : L - 1 = 2 * Nat.ceil (2 / ε ^ 2) + 1 := by omega
  have hLkey : 1 ≤ (ε ^ 2 / 2) * ((L - 1 : ℕ) : ℝ) := by
    have hnc : 2 / ε ^ 2 ≤ ((Nat.ceil (2 / ε ^ 2) : ℕ) : ℝ) := Nat.le_ceil _
    have hc0 : (0 : ℝ) ≤ ((Nat.ceil (2 / ε ^ 2) : ℕ) : ℝ) := by positivity
    have hcast : ((L - 1 : ℕ) : ℝ) = 2 * ((Nat.ceil (2 / ε ^ 2) : ℕ) : ℝ) + 1 := by
      rw [hLsub]; push_cast; ring
    have h4 : (2 / ε ^ 2 : ℝ) ≤ ((L - 1 : ℕ) : ℝ) := by
      rw [hcast]; linarith
    have hstep := mul_le_mul_of_nonneg_left h4 (le_of_lt hε2h)
    have hsimp : (ε ^ 2 / 2) * (2 / ε ^ 2) = 1 := by
      rw [div_mul_div_comm]
      rw [show ε ^ 2 * 2 = 1 * (2 * ε ^ 2) by ring]
      rw [mul_div_cancel_right₀ 1 (by positivity : (2 : ℝ) * ε ^ 2 ≠ 0)]
    linarith
  refine ⟨L, hLge, hLeven, ?_⟩
  · -- the threshold `X₀`
    refine ⟨max 2 (max (3 ^ (1 / θ)) (max (3 ^ (1 / (ε ^ 2 / 2)))
        (max (8001 ^ (1 / (θ - 2 * ε))) ((2 * max B 0 + 2) ^ (1 / (θ - 3 * ε)))))),
      ?_, ?_⟩
    · exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    · intro X H P₁ P₂ hX hHlo hHhi hP1lo hP1hi hP2lo hP2hi
      obtain ⟨hm2, hT⟩ := max_le_iff.mp hX
      obtain ⟨hA1, hT2⟩ := max_le_iff.mp hT
      obtain ⟨hA2, hT3⟩ := max_le_iff.mp hT2
      obtain ⟨hA3, hA4⟩ := max_le_iff.mp hT3
      have hXpos : 0 < X := by linarith
      have hX1 : 1 ≤ X := by linarith
      have h3θ : 3 ≤ X ^ θ := rpow_threshold (by norm_num) hθ hA1
      have h3ε : 3 ≤ X ^ (ε ^ 2 / 2) := rpow_threshold (by norm_num) hε2h hA2
      have h8001 : 8001 ≤ X ^ (θ - 2 * ε) := rpow_threshold (by norm_num) hth2 hA3
      have hBle : 2 * max B 0 + 2 ≤ X ^ (θ - 3 * ε) :=
        rpow_threshold (by nlinarith [le_max_right B 0]) hth3 hA4
      have hP1ge3 : 3 ≤ P₁ := le_trans h3ε hP1lo
      have hP2ge3 : 3 ≤ P₂ := le_trans h3ε hP2lo
      have hP1pos : 0 < P₁ := by linarith
      have hP2pos : 0 < P₂ := by linarith
      have hHpos : 0 < H := by linarith
      have hHge1 : 1 ≤ H := by linarith
      -- `X^θ ≤ X/H`
      have hXH_ge : X ^ θ ≤ X / H := by
        have h1 : X / X ^ (1 - θ) ≤ X / H :=
          div_le_div_of_nonneg_left (le_of_lt hXpos) hHpos hHhi
        have h2 : X / X ^ (1 - θ) = X ^ θ := by
          have h4 : X ^ θ = X / X ^ (1 - θ) := by
            have h5 : X ^ θ = X ^ (1 - (1 - θ)) := by rw [show 1 - (1 - θ) = θ by ring]
            rw [h5, Real.rpow_sub hXpos, Real.rpow_one]
          exact h4.symm
        linarith [h1, h2.symm.le]
      -- `X/H ≤ X`
      have hXH_le_X : X / H ≤ X := by
        rw [div_le_iff₀ hHpos]
        nlinarith
      have hℓstep : X / H ≤ P₁ ^ (L - 1) := by
        calc X / H ≤ X := hXH_le_X
          _ = X ^ (1 : ℝ) := (Real.rpow_one X).symm
          _ ≤ X ^ ((ε ^ 2 / 2) * ((L - 1 : ℕ) : ℝ)) :=
              Real.rpow_le_rpow_of_exponent_le hX1 hLkey
          _ = (X ^ (ε ^ 2 / 2)) ^ ((L - 1 : ℕ) : ℝ) := Real.rpow_mul hXpos.le _ _
          _ ≤ P₁ ^ ((L - 1 : ℕ) : ℝ) :=
              Real.rpow_le_rpow (Real.rpow_nonneg hXpos.le _) hP1lo (by positivity)
          _ = P₁ ^ (L - 1) := Real.rpow_natCast P₁ (L - 1)
      have hP1sq : P₁ ^ 2 ≤ X ^ (2 * ε) := by
        have h1 : P₁ ^ 2 ≤ (X ^ ε) ^ 2 := pow_le_pow_left₀ (le_of_lt hP1pos) hP1hi 2
        have h2 : (X ^ ε) ^ 2 = X ^ (2 * ε) := rpow_natpow X ε hXpos.le 2
        linarith [h1, h2.le]
      have hfield : (X / (P₁ * P₂)) / (H / (P₁ * P₂)) = X / H := by
        have h1 : P₁ * P₂ ≠ 0 := by positivity
        have h2 : H ≠ 0 := ne_of_gt hHpos
        field_simp
      have h8000 : 8000 * P₁ ^ 2 < X / H := by
        have hX2ε : 0 < X ^ (2 * ε) := Real.rpow_pos_of_pos hXpos _
        have h1 : 8000 * P₁ ^ 2 ≤ 8000 * X ^ (2 * ε) :=
          mul_le_mul_of_nonneg_left hP1sq (by norm_num)
        have h2 : 8000 * X ^ (2 * ε) < 8001 * X ^ (2 * ε) :=
          mul_lt_mul_of_pos_right (by norm_num) hX2ε
        have h3 : 8001 * X ^ (2 * ε) ≤ X ^ (θ - 2 * ε) * X ^ (2 * ε) :=
          mul_le_mul_of_nonneg_right h8001 hX2ε.le
        have h4 : X ^ (θ - 2 * ε) * X ^ (2 * ε) = X ^ θ := by
          rw [← Real.rpow_add hXpos, show θ - 2 * ε + 2 * ε = θ by ring]
        linarith [h1, h2, h3, h4.le, hXH_ge]
      have hden_eq : (H / (P₁ * P₂)) / (2 * P₁) = H / (2 * P₁ ^ 2 * P₂) := by
        rw [div_div]
        congr 1
        ring
      have hdenpos : (0 : ℝ) < 2 * P₁ ^ 2 * P₂ := by positivity
      have hkey : X ^ (θ - 3 * ε) * (2 * P₁ ^ 2 * P₂) ≤ 2 * H := by
        have hX2ε : 0 < X ^ (2 * ε) := Real.rpow_pos_of_pos hXpos _
        have hP2c : P₁ ^ 2 * P₂ ≤ X ^ (2 * ε) * X ^ ε :=
          mul_le_mul hP1sq hP2hi (le_of_lt hP2pos) (le_of_lt hX2ε)
        have h3εadd : X ^ (2 * ε) * X ^ ε = X ^ (3 * ε) := by
          rw [← Real.rpow_add hXpos, show 2 * ε + ε = 3 * ε by ring]
        have hprod : 2 * P₁ ^ 2 * P₂ ≤ 2 * X ^ (3 * ε) := by
          have h := mul_le_mul_of_nonneg_left hP2c (by norm_num : (0 : ℝ) ≤ 2)
          rw [h3εadd] at h
          linarith [h]
        have h4 : X ^ (θ - 3 * ε) * X ^ (3 * ε) = X ^ θ := by
          rw [← Real.rpow_add hXpos, show θ - 3 * ε + 3 * ε = θ by ring]
        have h5 : X ^ (θ - 3 * ε) * (2 * X ^ (3 * ε)) = 2 * X ^ θ := by
          rw [← h4]; ring
        have h6 : X ^ (θ - 3 * ε) * (2 * P₁ ^ 2 * P₂) ≤
            X ^ (θ - 3 * ε) * (2 * X ^ (3 * ε)) :=
          mul_le_mul_of_nonneg_left hprod (le_of_lt (Real.rpow_pos_of_pos hXpos _))
        have h7 : 2 * X ^ θ ≤ 2 * H := by linarith
        linarith [h6, h5.le, h7]
      have hden_lb : X ^ (θ - 3 * ε) / 2 ≤ (H / (P₁ * P₂)) / (2 * P₁) := by
        rw [hden_eq, le_div_iff₀ hdenpos]
        rw [div_mul_eq_mul_div, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
        linarith [hkey]
      have hbig : max B 0 + 1 ≤ (H / (P₁ * P₂)) / (2 * P₁) := by
        have hstep : (2 * max B 0 + 2) / 2 ≤ X ^ (θ - 3 * ε) / 2 := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right hBle (by norm_num)
        rw [show (2 * max B 0 + 2) / 2 = max B 0 + 1 by ring_nf] at hstep
        exact le_trans hstep hden_lb
      exact ⟨hXpos, hP1pos, hP2pos, hHpos, le_trans h3θ hXH_ge, hℓstep,
        one_le_pi0 hP1ge3, one_le_pi0 hP2ge3, hfield, h8000,
        le_trans (by linarith [le_max_right B 0]) hbig,
        by linarith [le_max_left B 0, hbig]⟩

end Work.BMF
