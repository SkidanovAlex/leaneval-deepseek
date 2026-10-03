import Mathlib
import Submission.Work.Pert.PinLogDev.AnchorWalk
import Submission.Work.Pert.PinLogDev.anchor_walk
import Submission.Work.Pert.Ksub2.Setup

namespace Work.Pert.PinLogDev

/-- **The elementary growth bound behind the `wc_`-layer of margin estimates.**

If `1 ≤ X₁ ≤ x` and `64 K² ≤ X₁` then `K log x ≤ x/4`.  Indeed `K ≤ √X₁/8` (from
`64K² ≤ X₁`), `log x ≤ 2√x` (from `x ≥ 1`, via `Real.log_le_rpow_div` at exponent `1/2`),
and `√X₁ · √x = √(X₁x) ≤ x` since `X₁ ≤ x` and `x ≥ 0`. -/
lemma mul_log_le_div_four {X x K : ℝ} (hK : 0 ≤ K) (hX1 : 1 ≤ X) (hXx : X ≤ x)
    (h64 : 64 * K ^ 2 ≤ X) : K * Real.log x ≤ x / 4 := by
  have hx1 : (1 : ℝ) ≤ x := le_trans hX1 hXx
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hXpos : (0 : ℝ) < X := by linarith
  have hlogx0 : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx1
  have hlog : Real.log x ≤ 2 * Real.sqrt x := by
    have h1 := Real.log_le_rpow_div hx0 (by norm_num : (0 : ℝ) < 1 / 2)
    rw [Real.sqrt_eq_rpow]
    rw [div_eq_mul_inv] at h1
    nlinarith [h1]
  have hKsqrt : K ≤ Real.sqrt X / 8 := by
    have h8 : (0 : ℝ) ≤ 8 * K := by linarith
    have h2 : (8 * K) ^ 2 ≤ X := by nlinarith [h64]
    have h3 : 8 * K ≤ Real.sqrt X := (Real.le_sqrt h8 (by linarith)).mpr h2
    linarith
  have hqnn : (0 : ℝ) ≤ Real.sqrt X / 8 := by positivity
  have step1 : K * Real.log x ≤ (Real.sqrt X / 8) * (2 * Real.sqrt x) := by
    have ha : K * Real.log x ≤ (Real.sqrt X / 8) * Real.log x :=
      mul_le_mul_of_nonneg_right hKsqrt hlogx0
    have hb : (Real.sqrt X / 8) * Real.log x ≤ (Real.sqrt X / 8) * (2 * Real.sqrt x) :=
      mul_le_mul_of_nonneg_left hlog hqnn
    linarith
  have step2 : (Real.sqrt X / 8) * (2 * Real.sqrt x) = Real.sqrt X * Real.sqrt x / 4 := by ring
  have step3 : Real.sqrt X * Real.sqrt x = Real.sqrt (X * x) := (Real.sqrt_mul hXpos.le x).symm
  have step4 : Real.sqrt (X * x) ≤ x := by
    have h1 : X * x ≤ x * x := by nlinarith
    have h2 := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_mul_self hx0] at h2
  linarith [step1, step2, step3, step4]

theorem wc_margB_axis_ge {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {a b : ℂ} {R Ξ : ℝ}
    (hasym : ∀ x : ℝ, R ≤ x →
      ‖Work.Pert.Xc d (-(x : ℂ)) - (-(x : ℂ) + a * Complex.log (x : ℂ) + b)‖ ≤ 1 / 1024)
    {α : ℂ} {x X₁ Rd : ℝ} (hRx : R ≤ x) (hX₁x : X₁ ≤ x) (hX₁1 : 1 ≤ X₁)
    (hX₁exp : Real.exp Real.pi ≤ X₁) (hKkX : |a.re| + |a.im| ≤ X₁)
    (h64 : 64 * (|a.re| + |a.im|) ^ 2 ≤ X₁)
    (hlin : Rd + (|a.re| + |a.im|) * Real.pi + |b.re| + |b.im| + Ξ + 1 ≤ 3 * X₁ / 4) :
    Rd ≤ Work.Pert.margB Ξ α (Work.Pert.Xc d (-(x : ℂ))) := by
  have hlogb : (|a.re| + |a.im|) * Real.log x ≤ x / 4 :=
    mul_log_le_div_four (by positivity) hX₁1 hX₁x (by simpa using h64)
  have hmB := margB_Xc_axis_ge (d := d) (hasym := hasym) (α := α) (Ξ := Ξ) hRx
    (le_trans hX₁exp hX₁x)
  have hx : 3 * X₁ / 4 ≤ x - (|a.re| + |a.im|) * Real.log x := by linarith
  linarith

end Work.Pert.PinLogDev
