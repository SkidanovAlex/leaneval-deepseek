import Mathlib
import Submission.Work.LT.lr_class_ops

namespace Work.LT

/-- For mean-zero `z`, the mixed form `2⟨w, POp A z⟩` is at most `μ(‖w‖² + ‖z‖²)` whenever the
left walk contracts mean-zero functions by `μ`. -/
theorem lr_class_dot_bound {G : Type} [Group G] [Fintype G] {Δ : ℕ} (A : Fin Δ → G) (μ : ℝ)
    (hA : leftExpander A μ) (hμ : 0 ≤ μ) (w z : G → ℝ) (hz : ∑ g, z g = 0) :
    2 * (∑ g, w g * POp A z g) ≤ μ * ((∑ g, w g ^ 2) + ∑ g, z g ^ 2) := by
  classical
  -- The contraction hypothesis says `‖POp A z‖ ≤ μ‖z‖` on mean-zero functions.
  have hNw : 0 ≤ ∑ g, w g ^ 2 := Finset.sum_nonneg fun g _ => sq_nonneg _
  have hNz : 0 ≤ ∑ g, z g ^ 2 := Finset.sum_nonneg fun g _ => sq_nonneg _
  have hcontr : ∑ g, POp A z g ^ 2 ≤ μ ^ 2 * ∑ g, z g ^ 2 := by
    simpa [POp] using hA z hz
  -- Cauchy–Schwarz bounds the mixed form by `‖w‖ · ‖POp A z‖`.
  have hCS : ∑ g, w g * POp A z g ≤
      Real.sqrt (∑ g, w g ^ 2) * Real.sqrt (∑ g, POp A z g ^ 2) := by
    simpa using Real.sum_mul_le_sqrt_mul_sqrt Finset.univ w (fun g => POp A z g)
  have hmono : Real.sqrt (∑ g, POp A z g ^ 2) ≤ μ * Real.sqrt (∑ g, z g ^ 2) := by
    calc Real.sqrt (∑ g, POp A z g ^ 2) ≤ Real.sqrt (μ ^ 2 * ∑ g, z g ^ 2) :=
          Real.sqrt_le_sqrt hcontr
      _ = Real.sqrt (μ ^ 2) * Real.sqrt (∑ g, z g ^ 2) := Real.sqrt_mul (sq_nonneg μ) _
      _ = μ * Real.sqrt (∑ g, z g ^ 2) := by rw [Real.sqrt_sq hμ]
  have h1 : ∑ g, w g * POp A z g ≤
      Real.sqrt (∑ g, w g ^ 2) * (μ * Real.sqrt (∑ g, z g ^ 2)) :=
    hCS.trans (mul_le_mul_of_nonneg_left hmono (Real.sqrt_nonneg _))
  -- AM–GM: `2√a√b ≤ a + b`, multiplied by the nonnegative `μ`.
  have hAM : 2 * (Real.sqrt (∑ g, w g ^ 2) * Real.sqrt (∑ g, z g ^ 2)) ≤
      (∑ g, w g ^ 2) + ∑ g, z g ^ 2 := by
    have h := two_mul_le_add_sq (Real.sqrt (∑ g, w g ^ 2)) (Real.sqrt (∑ g, z g ^ 2))
    rw [Real.sq_sqrt hNw, Real.sq_sqrt hNz] at h
    linarith
  have h2 : 2 * (Real.sqrt (∑ g, w g ^ 2) * (μ * Real.sqrt (∑ g, z g ^ 2))) ≤
      μ * ((∑ g, w g ^ 2) + ∑ g, z g ^ 2) := by
    have h := mul_le_mul_of_nonneg_left hAM hμ
    linarith
  linarith

end Work.LT
