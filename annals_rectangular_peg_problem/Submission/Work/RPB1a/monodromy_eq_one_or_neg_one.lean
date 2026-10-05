import Mathlib
import Submission.Work.RPB1a.Defs

namespace Work.RPB1a

open Complex Set Metric
open scoped ContDiff Real
open Work.RPB1a

/-- If `σ` is a continuous reparametrisation of the parameter circle of a smooth loop `v`,
and `v ∘ σ` is again a smooth loop, then the "monodromy" integer `k` of `σ`,
characterised by `σ (t + 2π) = σ t + 2π k`, can only be `± 1` when `σ` is strictly
monotone.

The mathematical content: `v` is injective mod `2π`, hence so is `v ∘ σ`.  Therefore
any two parameters whose `σ`-images differ by a multiple of `2π` must themselves differ
by a multiple of `2π`.  If `σ` is strictly increasing with `k ≥ 2` then `σ` overshoots
`σ 0 + 2π` strictly inside `[0, 2π]`, producing such a forbidden pair; if `k = 1` the
overshoot point is exactly `2π`, which is allowed.  The strictly decreasing case is
symmetric. -/
lemma monodromy_eq_one_or_neg_one (v : ℝ → ℂ) (hv : IsSmoothLoop v) (σ : ℝ → ℝ)
    (hσ : Continuous σ) (hw : IsSmoothLoop (fun t => v (σ t))) (k : ℤ)
    (hk : ∀ t, σ (t + 2 * π) = σ t + 2 * π * k) (hmono : StrictMono σ ∨ StrictAnti σ) :
    k = 1 ∨ k = -1 := by
  have h2pi : (0 : ℝ) < 2 * π := by positivity
  have h2pine : (2 * π : ℝ) ≠ 0 := ne_of_gt h2pi
  have hper : ∀ t, v (t + 2 * π) = v t := hv.2.1
  have hinj : ∀ t t', v (σ t) = v (σ t') → ∃ m : ℤ, t' = t + 2 * π * m := hw.2.2.1
  have hσ2 : σ (2 * π) = σ 0 + 2 * π * (k : ℝ) := by simpa using hk 0
  have hcont : ContinuousOn σ (Icc (0 : ℝ) (2 * π)) := hσ.continuousOn
  -- Intermediate value, in the two orientations.
  have ivt_up : ∀ c : ℝ, σ 0 ≤ c → c ≤ σ (2 * π) → ∃ t₁ ∈ Icc (0 : ℝ) (2 * π), σ t₁ = c := by
    intro c h1 h2
    have hmem : c ∈ Icc (σ 0) (σ (2 * π)) := ⟨h1, h2⟩
    rcases intermediate_value_Icc h2pi.le hcont hmem with ⟨t₁, ht, he⟩
    exact ⟨t₁, ht, he⟩
  have ivt_dn : ∀ c : ℝ, σ (2 * π) ≤ c → c ≤ σ 0 → ∃ t₁ ∈ Icc (0 : ℝ) (2 * π), σ t₁ = c := by
    intro c h1 h2
    have hmem : c ∈ Icc (σ (2 * π)) (σ 0) := ⟨h1, h2⟩
    rcases intermediate_value_Icc' h2pi.le hcont hmem with ⟨t₁, ht, he⟩
    exact ⟨t₁, ht, he⟩
  -- Engine: a parameter `t₁ ∈ [0, 2π]` with `v (σ t₁) = v (σ 0)` must be `0` or `2π`.
  have engine : ∀ t₁ ∈ Icc (0 : ℝ) (2 * π), v (σ t₁) = v (σ 0) →
      ∃ m : ℤ, t₁ = 2 * π * (m : ℝ) ∧ (m = 0 ∨ m = 1) := by
    intro t₁ ht₁ hv₁
    obtain ⟨m, hm⟩ := hinj t₁ 0 hv₁
    -- hm : (0 : ℝ) = t₁ + 2 * π * m
    have ht : t₁ = 2 * π * ((-m : ℤ) : ℝ) := by
      have h : t₁ = -(2 * π * (m : ℝ)) := by linarith [hm]
      rw [h]; push_cast; ring
    refine ⟨-m, ht, ?_⟩
    have hlo : (0 : ℝ) ≤ ((-m : ℤ) : ℝ) := by
      have h : (0 : ℝ) ≤ 2 * π * ((-m : ℤ) : ℝ) := by rw [← ht]; exact ht₁.1
      exact (mul_nonneg_iff_of_pos_left h2pi).mp h
    have hhi : ((-m : ℤ) : ℝ) ≤ 1 := by
      have h : 2 * π * ((-m : ℤ) : ℝ) ≤ 2 * π * 1 := by rw [← ht]; simpa using ht₁.2
      exact (mul_le_mul_iff_of_pos_left h2pi).mp h
    have h0 : (0 : ℤ) ≤ -m := by exact_mod_cast hlo
    have h1 : (-m : ℤ) ≤ 1 := by exact_mod_cast hhi
    omega
  rcases hmono with hm | hm
  · -- strictly increasing: `k = 1`
    left
    have hlt : σ 0 < σ (2 * π) := by simpa using hm h2pi
    have hkpos : (0 : ℝ) < (k : ℝ) := by
      have h : (0 : ℝ) < 2 * π * (k : ℝ) := by linarith [hlt, hσ2]
      exact (mul_pos_iff_of_pos_left h2pi).mp h
    have hk1 : (1 : ℤ) ≤ k := by
      have : (0 : ℤ) < k := by exact_mod_cast hkpos
      omega
    have hk1R : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    have hle : σ 0 + 2 * π ≤ σ (2 * π) := by
      rw [hσ2]
      have h := mul_le_mul_of_nonneg_left hk1R h2pi.le
      linarith
    obtain ⟨t₁, ht₁, ht₁eq⟩ := ivt_up (σ 0 + 2 * π) (by linarith) hle
    have hv₁ : v (σ t₁) = v (σ 0) := by
      rw [ht₁eq]; exact hper (σ 0)
    obtain ⟨m, htm, hm01⟩ := engine t₁ ht₁ hv₁
    rcases hm01 with hm0 | hm1
    · exfalso
      have ht0 : t₁ = 0 := by rw [hm0] at htm; simpa using htm
      rw [ht0] at ht₁eq
      linarith [ht₁eq, h2pi]
    · have ht2 : t₁ = 2 * π := by rw [hm1] at htm; simpa using htm
      have hkR : (k : ℝ) = 1 := by
        have hσ2' : σ (2 * π) = σ 0 + 2 * π := by
          have h := ht₁eq; rw [ht2] at h; exact h
        rw [hσ2] at hσ2'
        have hcan : 2 * π * (k : ℝ) = 2 * π * 1 := by linarith
        exact mul_left_cancel₀ h2pine hcan
      exact_mod_cast hkR
  · -- strictly decreasing: `k = -1`
    right
    have hlt : σ (2 * π) < σ 0 := by simpa using hm h2pi
    have hkneg : (k : ℝ) < 0 := by
      have h : 2 * π * (k : ℝ) < 0 := by linarith [hlt, hσ2]
      by_contra hcon
      push Not at hcon
      have := mul_nonneg h2pi.le hcon
      linarith
    have hkneg1 : k ≤ -1 := by
      have : k < 0 := by exact_mod_cast hkneg
      omega
    have hkneg1R : (k : ℝ) ≤ -1 := by exact_mod_cast hkneg1
    have hle : σ (2 * π) ≤ σ 0 - 2 * π := by
      rw [hσ2]
      have h := mul_le_mul_of_nonneg_left hkneg1R h2pi.le
      linarith
    obtain ⟨t₁, ht₁, ht₁eq⟩ := ivt_dn (σ 0 - 2 * π) hle (by linarith)
    have hv₁ : v (σ t₁) = v (σ 0) := by
      rw [ht₁eq]
      have hp := hper (σ 0 - 2 * π)
      have heq : (σ 0 - 2 * π) + 2 * π = σ 0 := by ring
      rw [heq] at hp
      exact hp.symm
    obtain ⟨m, htm, hm01⟩ := engine t₁ ht₁ hv₁
    rcases hm01 with hm0 | hm1
    · exfalso
      have ht0 : t₁ = 0 := by rw [hm0] at htm; simpa using htm
      rw [ht0] at ht₁eq
      linarith [ht₁eq, h2pi]
    · have ht2 : t₁ = 2 * π := by rw [hm1] at htm; simpa using htm
      have hkR : (k : ℝ) = -1 := by
        have hσ2' : σ (2 * π) = σ 0 - 2 * π := by
          have h := ht₁eq; rw [ht2] at h; exact h
        rw [hσ2] at hσ2'
        have hcan : 2 * π * (k : ℝ) = 2 * π * (-1 : ℝ) := by linarith
        exact mul_left_cancel₀ h2pine hcan
      exact_mod_cast hkR

end Work.RPB1a
