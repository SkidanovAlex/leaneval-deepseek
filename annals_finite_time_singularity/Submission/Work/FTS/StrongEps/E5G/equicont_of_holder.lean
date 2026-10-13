import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5G

lemma equicont_of_holder {K : Set (ℝ × ℝ)} {F : ℕ → ℝ × ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ n : ℕ, ∀ p ∈ K, ∀ q ∈ K, |F n p - F n q| ≤ C * dist p q ^ (1 / 2 : ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ, ∀ p ∈ K, ∀ q ∈ K,
      dist p q < δ → |F n p - F n q| < ε := by
  intro ε hε
  have hC1 : (0 : ℝ) < C + 1 := by linarith
  refine ⟨(ε / (C + 1)) ^ 2, by positivity, ?_⟩
  intro n p hp q hq hpq
  -- the half-power of the distance is bounded by ε/(C+1)
  have ha : (0 : ℝ) < ε / (C + 1) := by positivity
  have hsqrt : Real.sqrt (dist p q) < ε / (C + 1) := by
    have h1 := Real.sqrt_lt_sqrt (dist_nonneg) hpq
    rwa [Real.sqrt_sq (le_of_lt ha)] at h1
  have h2 := h n p hp q hq
  rw [← Real.sqrt_eq_rpow] at h2
  have h3 : C * (ε / (C + 1)) < ε := by
    rw [← mul_div_assoc, div_lt_iff₀ hC1]
    nlinarith [hε]
  have h4 : C * Real.sqrt (dist p q) ≤ C * (ε / (C + 1)) :=
    mul_le_mul_of_nonneg_left (le_of_lt hsqrt) hC
  linarith

end Work.FTS.StrongEps.E5G
