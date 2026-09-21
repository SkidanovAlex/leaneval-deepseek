import Mathlib
import Submission.Work.OddCurve.LowSlope.Peano2

namespace Work.OddCurve.LowSlope

open Filter Asymptotics
open scoped Topology

/-- The product rule for second-order Peano expansions: the product of two functions with
second-order expansions at `x₀` has the expansion whose coefficients are given by the Leibniz
rule (with the factor `2` in the second coefficient because the expansion is
`f x₀ + c₁ h + c₂ / 2 * h ^ 2 + o (h ^ 2)`). -/
theorem peano2_mul {f g : ℝ → ℝ} {x₀ c₁ c₂ d₁ d₂ : ℝ}
    (hf : Work.OddCurve.LowSlope.Peano2 f x₀ c₁ c₂)
    (hg : Work.OddCurve.LowSlope.Peano2 g x₀ d₁ d₂) :
    Work.OddCurve.LowSlope.Peano2 (fun v : ℝ => f v * g v) x₀ (c₁ * g x₀ + f x₀ * d₁)
      (c₂ * g x₀ + 2 * c₁ * d₁ + f x₀ * d₂) := by
  unfold Peano2 at hf hg ⊢
  -- the two error terms, each `o (h ^ 2)`
  set F : ℝ → ℝ := fun h => f (x₀ + h) - f x₀ - c₁ * h - c₂ / 2 * h ^ 2 with hFdef
  set G : ℝ → ℝ := fun h => g (x₀ + h) - g x₀ - d₁ * h - d₂ / 2 * h ^ 2 with hGdef
  have hF : F =o[𝓝 0] fun h : ℝ => h ^ 2 := by rw [hFdef]; exact hf
  have hG : G =o[𝓝 0] fun h : ℝ => h ^ 2 := by rw [hGdef]; exact hg
  -- the two "low order" factors are bounded near `0`
  have hB1 : (fun h : ℝ => g x₀ + d₁ * h + d₂ / 2 * h ^ 2) =O[𝓝 0] fun _ : ℝ => (1 : ℝ) :=
    ContinuousAt.isBigO (by fun_prop : ContinuousAt (fun h : ℝ => g x₀ + d₁ * h + d₂ / 2 * h ^ 2) 0)
  have hB2 : (fun h : ℝ => f x₀ + c₁ * h + c₂ / 2 * h ^ 2) =O[𝓝 0] fun _ : ℝ => (1 : ℝ) :=
    ContinuousAt.isBigO (by fun_prop : ContinuousAt (fun h : ℝ => f x₀ + c₁ * h + c₂ / 2 * h ^ 2) 0)
  have hp1 : (fun h : ℝ => F h * (g x₀ + d₁ * h + d₂ / 2 * h ^ 2)) =o[𝓝 0] fun h : ℝ => h ^ 2 :=
    (hF.mul_isBigO hB1).congr' EventuallyEq.rfl (by filter_upwards with h; simp)
  have hp2 : (fun h : ℝ => G h * (f x₀ + c₁ * h + c₂ / 2 * h ^ 2)) =o[𝓝 0] fun h : ℝ => h ^ 2 :=
    (hG.mul_isBigO hB2).congr' EventuallyEq.rfl (by filter_upwards with h; simp)
  have hp3 : (fun h : ℝ => F h * G h) =o[𝓝 0] fun h : ℝ => h ^ 2 := by
    have h1 : (fun h : ℝ => F h * G h) =o[𝓝 0] fun h : ℝ => h ^ 2 * h ^ 2 := hF.mul hG
    have h2 : (fun h : ℝ => h ^ 2 * h ^ 2) =o[𝓝 0] fun h : ℝ => h ^ 2 :=
      (isLittleO_pow_pow (m := 2) (n := 4) (by norm_num)).congr'
        (by filter_upwards with h; ring) EventuallyEq.rfl
    exact h1.trans h2
  -- the polynomial residual of the two first-order factors
  have hp4 : (fun h : ℝ => (c₁ * d₂ / 2 + c₂ * d₁ / 2) * h ^ 3 + (c₂ * d₂ / 4) * h ^ 4)
      =o[𝓝 0] fun h : ℝ => h ^ 2 := by
    have h3 : (fun h : ℝ => (c₁ * d₂ / 2 + c₂ * d₁ / 2) * h ^ 3) =o[𝓝 0] fun h : ℝ => h ^ 2 :=
      IsLittleO.const_mul_left (isLittleO_pow_pow (m := 2) (n := 3) (by norm_num)) _
    have h4 : (fun h : ℝ => (c₂ * d₂ / 4) * h ^ 4) =o[𝓝 0] fun h : ℝ => h ^ 2 :=
      IsLittleO.const_mul_left (isLittleO_pow_pow (m := 2) (n := 4) (by norm_num)) _
    exact h3.add h4
  refine ((hp1.add hp2).add hp3).add hp4 |>.congr' ?_ EventuallyEq.rfl
  filter_upwards with h
  simp only [hFdef, hGdef]
  ring

end Work.OddCurve.LowSlope
