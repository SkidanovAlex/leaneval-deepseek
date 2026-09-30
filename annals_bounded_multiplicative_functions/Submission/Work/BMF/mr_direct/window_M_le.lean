import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

/-- The function `x ↦ (1 + x) * exp (-x)` is antitone on `[0, ∞)`:
for `0 ≤ a ≤ b` it satisfies `(1 + b) e^{-b} ≤ (1 + a) e^{-a}`. -/
lemma one_add_mul_exp_neg_antitone {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (1 + b) * Real.exp (-b) ≤ (1 + a) * Real.exp (-a) := by
  have hc : 0 ≤ b - a := by linarith
  have h1 : 1 + (b - a) ≤ Real.exp (b - a) := by
    linarith [Real.add_one_le_exp (b - a)]
  have h2 : (1 + a) * (1 + (b - a)) ≤ (1 + a) * Real.exp (b - a) :=
    mul_le_mul_of_nonneg_left h1 (by linarith)
  have h3 : 1 + b ≤ (1 + a) * (1 + (b - a)) := by
    nlinarith [mul_nonneg ha hc]
  have h4 : 1 + b ≤ (1 + a) * Real.exp (b - a) := le_trans h3 h2
  have hexp : Real.exp (b - a) * Real.exp (-b) = Real.exp (-a) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc (1 + b) * Real.exp (-b)
      ≤ ((1 + a) * Real.exp (b - a)) * Real.exp (-b) :=
        mul_le_mul_of_nonneg_right h4 (le_of_lt (Real.exp_pos _))
    _ = (1 + a) * (Real.exp (b - a) * Real.exp (-b)) := by ring
    _ = (1 + a) * Real.exp (-a) := by rw [hexp]

theorem window_M_le (f : ℕ → ℂ) (M₀ T₀ t y : ℝ)
    (hM₀ : 0 < M₀) (ht : |t| ≤ 2 * T₀)
    (hD : ∀ w : ℝ, |w| ≤ 4 * T₀ →
        M₀ ≤ BoundedMultiplicativeFunctions.𝔻 f (fun n ↦ (n : ℂ) ^ (Complex.I * w)) y ^ 2) :
    (1 + (⨅ (u : {u : ℝ // |u| ≤ 2 * T₀}),
        BoundedMultiplicativeFunctions.𝔻 f (fun n ↦ (n : ℂ) ^ (Complex.I * (t + u.1))) y ^ 2)) *
      Real.exp (-(⨅ (u : {u : ℝ // |u| ≤ 2 * T₀}),
        BoundedMultiplicativeFunctions.𝔻 f (fun n ↦ (n : ℂ) ^ (Complex.I * (t + u.1))) y ^ 2))
      ≤ (1 + M₀) * Real.exp (-M₀) := by
  -- `ht` forces `T₀ ≥ 0`, hence the index type of the infimum is nonempty.
  have hT₀ : 0 ≤ T₀ := by
    have := abs_nonneg t
    linarith
  have hn : Nonempty {u : ℝ // |u| ≤ 2 * T₀} := ⟨⟨0, by
    simp only [abs_zero]
    linarith⟩⟩
  -- Every value occurring in the infimum is at least `M₀`.
  have hinf : M₀ ≤ ⨅ (u : {u : ℝ // |u| ≤ 2 * T₀}),
      BoundedMultiplicativeFunctions.𝔻 f (fun n ↦ (n : ℂ) ^ (Complex.I * (t + u.1))) y ^ 2 := by
    apply le_ciInf
    intro u
    have hb : |t + u.1| ≤ 4 * T₀ := by
      calc |t + u.1| ≤ |t| + |u.1| := abs_add_le t u.1
        _ ≤ 2 * T₀ + 2 * T₀ := add_le_add ht u.2
        _ = 4 * T₀ := by ring
    have h := hD (t + u.1) hb
    simpa only [Complex.ofReal_add] using h
  -- `x ↦ (1 + x) exp (-x)` is antitone on `[0, ∞)`, and `M₀ > 0`.
  exact one_add_mul_exp_neg_antitone (le_of_lt hM₀) hinf

end Work.BMF.mr_direct
