import Mathlib
import Submission.Work.Interfaces.Parabolic

namespace Work.Repel

open MandelDim Complex Set Metric Filter Topology

/-- For `c > 0` and any real `B`, the function `η ↦ c * η - B * log η` tends to `+∞`.
The linear term dominates the logarithmic one. -/
private lemma tendsto_linear_sub_log (c B : ℝ) (hc : 0 < c) :
    Tendsto (fun η : ℝ => c * η - B * Real.log η) atTop atTop := by
  have hlog : Tendsto (fun η : ℝ => Real.log η / η) atTop (𝓝 0) := by
    simpa using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hf : Tendsto (fun η : ℝ => c - B * (Real.log η / η)) atTop (𝓝 c) := by
    have h1 : Tendsto (fun η : ℝ => B * (Real.log η / η)) atTop (𝓝 (B * 0)) :=
      hlog.const_mul B
    have h2 : Tendsto (fun η : ℝ => c - B * (Real.log η / η)) atTop (𝓝 (c - B * 0)) :=
      tendsto_const_nhds.sub h1
    simpa using h2
  have hprod : Tendsto (fun η : ℝ => (c - B * (Real.log η / η)) * η) atTop atTop :=
    hf.pos_mul_atTop hc tendsto_id
  refine hprod.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with η hη
  have hη' : η ≠ 0 := ne_of_gt hη
  rw [sub_mul, mul_assoc, div_mul_cancel₀ _ hη']

/-- The eventual lower bound corresponding to `tendsto_linear_sub_log`. -/
private lemma exists_ge_linear_sub_log (c B D : ℝ) (hc : 0 < c) :
    ∃ Γ : ℝ, ∀ η : ℝ, Γ ≤ η → D ≤ c * η - B * Real.log η := by
  have h := (Filter.tendsto_atTop.mp (tendsto_linear_sub_log c B hc)) D
  rw [Filter.eventually_atTop] at h
  exact h

theorem dim_arith (ε C γ : ℝ) (hε : 0 < ε) (hC : 0 < C) (hγ : 0 < γ) :
    ∃ Γ : ℝ, ∀ η N K : ℝ, Γ ≤ η →
      γ * η * (Real.exp (2 * Real.pi * η)) ^ 2 ≤ N →
      K ≤ C * η ^ 2 * Real.exp (2 * Real.pi * η) → 1 < K →
      2 - ε ≤ Real.log N / Real.log K := by
  -- Write `a = max (2 - ε) 0`; then `0 ≤ a` and `2 - ε ≤ a`, and `a < 2` (because `ε > 0`).
  set a : ℝ := max (2 - ε) 0 with ha
  have ha0 : 0 ≤ a := by rw [ha]; exact le_max_right _ _
  have ha2 : 2 - ε ≤ a := by rw [ha]; exact le_max_left _ _
  have ha_lt : a < 2 := by rw [ha]; exact max_lt (by linarith) (by norm_num)
  have he : 0 < 4 - 2 * a := by linarith
  have hc : 0 < (4 - 2 * a) * Real.pi := mul_pos he Real.pi_pos
  -- Threshold at which the "logarithmic corrections" are dominated.
  obtain ⟨Γ₁, hΓ₁⟩ := exists_ge_linear_sub_log ((4 - 2 * a) * Real.pi) (2 * a - 1)
      (a * Real.log C - Real.log γ) hc
  refine ⟨max Γ₁ 1, ?_⟩
  intro η N K hη hN hK hK1
  have hη1 : 1 ≤ η := le_trans (le_max_right _ _) hη
  have hηΓ : Γ₁ ≤ η := le_trans (le_max_left _ _) hη
  have hηpos : 0 < η := lt_of_lt_of_le one_pos hη1
  have hηne : η ≠ 0 := ne_of_gt hηpos
  -- Key eventual estimate: `a · (log C + 2 log η + 2πη) ≤ log γ + log η + 4πη`.
  have hkey : a * (Real.log C + 2 * Real.log η + 2 * Real.pi * η) ≤
      Real.log γ + Real.log η + 4 * Real.pi * η := by
    have := hΓ₁ η hηΓ
    nlinarith [this]
  -- Lower bound on `log N`.
  have hPpos : 0 < γ * η * (Real.exp (2 * Real.pi * η)) ^ 2 :=
    mul_pos (mul_pos hγ hηpos) (pow_pos (Real.exp_pos _) 2)
  have hlogN : Real.log γ + Real.log η + 4 * Real.pi * η ≤ Real.log N := by
    have hP := Real.log_le_log hPpos hN
    have hlogP : Real.log (γ * η * (Real.exp (2 * Real.pi * η)) ^ 2) =
        Real.log γ + Real.log η + 4 * Real.pi * η := by
      rw [Real.log_mul (mul_ne_zero (ne_of_gt hγ) hηne) (pow_ne_zero 2 (Real.exp_ne_zero _))]
      rw [Real.log_mul (ne_of_gt hγ) hηne]
      rw [Real.log_pow, Real.log_exp]
      push_cast
      ring
    linarith [hlogP]
  -- Upper bound on `log K`.
  have hKpos : 0 < K := lt_trans one_pos hK1
  have hlogK : Real.log K ≤ Real.log C + 2 * Real.log η + 2 * Real.pi * η := by
    have hQ := Real.log_le_log hKpos hK
    have hlogQ : Real.log (C * η ^ 2 * Real.exp (2 * Real.pi * η)) =
        Real.log C + 2 * Real.log η + 2 * Real.pi * η := by
      rw [Real.log_mul (mul_ne_zero (ne_of_gt hC) (pow_ne_zero 2 hηne)) (Real.exp_ne_zero _)]
      rw [Real.log_mul (ne_of_gt hC) (pow_ne_zero 2 hηne)]
      rw [Real.log_pow, Real.log_exp]
      push_cast
      ring
    linarith [hlogQ]
  have hlogKpos : 0 < Real.log K := Real.log_pos hK1
  rw [le_div_iff₀ hlogKpos]
  calc (2 - ε) * Real.log K ≤ a * Real.log K :=
        mul_le_mul_of_nonneg_right ha2 (le_of_lt hlogKpos)
    _ ≤ a * (Real.log C + 2 * Real.log η + 2 * Real.pi * η) :=
        mul_le_mul_of_nonneg_left hlogK ha0
    _ ≤ Real.log γ + Real.log η + 4 * Real.pi * η := hkey
    _ ≤ Real.log N := hlogN

end Work.Repel
