import Mathlib
import Submission.Work.BourgainPlan.Oscillation.lacunary_defs

namespace Work.BourgainPlan.Oscillation

/-- For `ρ > 1` and any integer threshold `K₁`, the lacunary scale sequence `⌊ρ^i⌋` reaches any
bound of the form `max K₁ (2 ^ (4m+4))` at an index `j₀` that is `O(m+2)` — the "cutoff index"
used to switch the sharp core on only from a scale threshold. -/
theorem lacScale_cutoff_exists (ρ : ℝ) (hρ : 1 < ρ) (K₁ : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ), ∃ j₀ : ℕ,
      max K₁ (2 ^ (4 * m + 4)) ≤ Work.BourgainPlan.Oscillation.lacScale ρ j₀ ∧
      (j₀ : ℝ) ≤ C * ((m : ℝ) + 2) := by
  -- a fixed index `j₁` with `ρ^{j₁} ≥ 32 = 2^5`
  obtain ⟨j₁, hj₁⟩ : ∃ j : ℕ, (32:ℝ) ≤ ρ^j := by
    have h : ∀ᶠ n : ℕ in Filter.atTop, (32:ℝ) ≤ ρ^n :=
      (tendsto_pow_atTop_atTop_of_one_lt hρ).eventually (Filter.eventually_ge_atTop 32)
    obtain ⟨j, hj⟩ := Filter.eventually_atTop.1 h
    exact ⟨j, hj j le_rfl⟩
  -- a fixed index `j₂` with `ρ^{j₂} ≥ 2 · max K₁ 1`
  obtain ⟨j₂, hj₂⟩ : ∃ j : ℕ, 2 * ((max K₁ 1 : ℕ) : ℝ) ≤ ρ^j := by
    have hpos : (0:ℝ) < 2 * ((max K₁ 1 : ℕ) : ℝ) := by
      have : (1:ℝ) ≤ ((max K₁ 1 : ℕ) : ℝ) := by exact_mod_cast le_max_right K₁ 1
      linarith
    have h : ∀ᶠ n : ℕ in Filter.atTop, 2 * ((max K₁ 1 : ℕ) : ℝ) ≤ ρ^n :=
      (tendsto_pow_atTop_atTop_of_one_lt hρ).eventually (Filter.eventually_ge_atTop _)
    obtain ⟨j, hj⟩ := Filter.eventually_atTop.1 h
    exact ⟨j, hj j le_rfl⟩
  refine ⟨max 1 ((j₁ + j₂ : ℕ) : ℝ), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro m
  refine ⟨j₁ * (m + 1) + j₂, ?_, ?_⟩
  · rw [Work.BourgainPlan.Oscillation.lacScale]
    apply Nat.le_floor
    have hcast : ((max K₁ (2 ^ (4 * m + 4)) : ℕ) : ℝ) = max (K₁:ℝ) ((2:ℝ)^(4 * m + 4)) := by
      push_cast; ring
    have hpow : ρ ^ (j₁ * (m + 1) + j₂) = ρ ^ j₂ * (ρ ^ j₁) ^ (m + 1) := by
      rw [pow_add, pow_mul, mul_comm]
    rw [hcast, hpow]
    have hPpos : (0:ℝ) < 32 ^ (m + 1) := by positivity
    have hK'1 : (1:ℝ) ≤ ((max K₁ 1 : ℕ) : ℝ) := by exact_mod_cast le_max_right K₁ 1
    have hK'K : (K₁:ℝ) ≤ ((max K₁ 1 : ℕ) : ℝ) := by exact_mod_cast le_max_left K₁ 1
    have hK'nn : (0:ℝ) ≤ ((max K₁ 1 : ℕ) : ℝ) := le_trans zero_le_one hK'1
    have hB : (32:ℝ) ^ (m + 1) ≤ (ρ ^ j₁) ^ (m + 1) := pow_le_pow_left₀ (by norm_num) hj₁ (m + 1)
    have hge : 2 * ((max K₁ 1 : ℕ) : ℝ) * 32 ^ (m + 1) ≤ ρ ^ j₂ * (ρ ^ j₁) ^ (m + 1) :=
      mul_le_mul hj₂ hB (by positivity) (by positivity)
    refine le_trans (max_le ?_ ?_) hge
    · have hP1 : (1:ℝ) ≤ 32 ^ (m + 1) := one_le_pow₀ (by norm_num)
      calc (K₁:ℝ) ≤ ((max K₁ 1 : ℕ):ℝ) := hK'K
        _ = ((max K₁ 1 : ℕ):ℝ) * 1 := (mul_one _).symm
        _ ≤ ((max K₁ 1 : ℕ):ℝ) * 32 ^ (m + 1) := mul_le_mul_of_nonneg_left hP1 hK'nn
        _ ≤ 2 * ((max K₁ 1 : ℕ):ℝ) * 32 ^ (m + 1) := by
              linarith [mul_nonneg hK'nn hPpos.le]
    · have h32 : (32:ℝ) ^ (m + 1) = (2:ℝ) ^ (5 * (m + 1)) := by
        rw [show (32:ℝ) = 2^5 by norm_num, ← pow_mul]
      have hmono : (2:ℝ) ^ (4 * m + 4) ≤ (32:ℝ) ^ (m + 1) := by
        rw [h32]; exact pow_le_pow_right₀ (by norm_num) (by omega)
      have hK'P : (32:ℝ) ^ (m + 1) ≤ 2 * ((max K₁ 1 : ℕ):ℝ) * 32 ^ (m + 1) := by
        have hstep : (1:ℝ) * 32 ^ (m + 1) ≤ ((max K₁ 1 : ℕ):ℝ) * 32 ^ (m + 1) :=
          mul_le_mul_of_nonneg_right hK'1 hPpos.le
        nlinarith [hstep, hPpos]
      exact le_trans hmono hK'P
  · have hCge : ((j₁ + j₂ : ℕ):ℝ) ≤ max 1 ((j₁ + j₂:ℕ):ℝ) := le_max_right _ _
    have hm2pos : (0:ℝ) < (m:ℝ) + 2 := by positivity
    have hmain : ((j₁ * (m + 1) + j₂ : ℕ):ℝ) ≤ ((j₁ + j₂:ℕ):ℝ) * ((m:ℝ) + 2) := by
      push_cast
      have hj1 : (0:ℝ) ≤ (j₁:ℝ) := by positivity
      have hj2 : (0:ℝ) ≤ (j₂:ℝ) := by positivity
      have hm : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
      nlinarith [hj1, hj2, hm]
    calc ((j₁ * (m + 1) + j₂ : ℕ):ℝ) ≤ ((j₁ + j₂:ℕ):ℝ) * ((m:ℝ) + 2) := hmain
      _ ≤ max 1 ((j₁ + j₂:ℕ):ℝ) * ((m:ℝ) + 2) := mul_le_mul_of_nonneg_right hCge hm2pos.le

end Work.BourgainPlan.Oscillation
