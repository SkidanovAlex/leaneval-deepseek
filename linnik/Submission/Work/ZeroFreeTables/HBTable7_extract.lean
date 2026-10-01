/-
# ZeroFreeTables — HBTable7_extract

The *extraction* step of Heath-Brown's Table 7: the passage from the engine
inequality of HB (8.11) (HB Lemma 8.7)

`0 ≤ (k² + 1/2)(F(-λ₂) - F(λ₁ - λ₂)) - 2k F(0) + f(0)(ψ + E)`

to a *lower bound* for `λ₂`, using

* the certificate (`tfF` at the row values `(b, c)` strictly violating (8.11)), and
* the **monotonicity** of (8.11)'s left hand side in `λ₁` and in `λ₂`.

The point of this file is that the monotonicity is *pointwise* in the variable of
integration: for `t ≥ 0`,

`e^{λ₂ t} - e^{(λ₂-λ₁)t} = e^{λ₂ t}(1 - e^{-λ₁ t})`,

and on `[0, x₀]` the right hand side is increasing in `λ₂` (as `e^{λ₂t}` is) and in
`λ₁` (as `1 - e^{-λ₁t}` is, for `λ₁ ≥ 0`).  Hence the comparison of the two
integrals is elementary (`intervalIntegral.integral_mono_on`).

The functions `F` are always of the form `z ↦ ∫₀^{x₀} e^{-zt} f(t) dt` with `f ≥ 0`
supported on `[0, x₀]` (the Laplace transform of a `TestFn`), so the exact form of
`f` never enters the extraction.
-/
import Mathlib

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

/-- HB (8.11)'s left hand side, with `F` the Laplace transform of the test function,
`k` the parameter of (8.11) and `A = f(0)(ψ + E)` its constant term. -/
def LHS811 (F : ℝ → ℝ) (k A z₁ z₂ : ℝ) : ℝ :=
  (k ^ 2 + 1/2) * (F (-z₂) - F (z₁ - z₂)) - 2 * k * F 0 + A

/-- `e^{λ₂t} - e^{(λ₂-λ₁)t} = e^{λ₂t}(1 - e^{-λ₁t})`: the factorisation that makes the
monotonicity of HB (8.11) pointwise. -/
theorem exp_bracket_eq (z₁ z₂ t : ℝ) :
    Real.exp (z₂ * t) - Real.exp ((z₂ - z₁) * t) = Real.exp (z₂ * t) * (1 - Real.exp (-(z₁ * t))) := by
  rw [show (z₂ - z₁) * t = z₂ * t + (-(z₁ * t)) by ring, Real.exp_add]
  ring

/-- Pointwise comparison on the positive half line: the bracket of HB (8.11) with
`(λ₁, λ₂) = (z₁, z₂)` is at most the one with the row values `(b, c)`, whenever
`0 ≤ z₁ ≤ b` and `z₂ ≤ c`. -/
theorem bracket_le_bracket {z₁ b z₂ c t : ℝ} (h1 : 0 ≤ z₁) (hz₁ : z₁ ≤ b) (hz₂ : z₂ ≤ c)
    (ht : 0 ≤ t) :
    Real.exp (z₂ * t) - Real.exp ((z₂ - z₁) * t) ≤ Real.exp (c * t) - Real.exp ((c - b) * t) := by
  have hb : 0 ≤ b := le_trans h1 hz₁
  rw [exp_bracket_eq, exp_bracket_eq]
  have hA : Real.exp (z₂ * t) ≤ Real.exp (c * t) := Real.exp_le_exp.mpr (by nlinarith)
  have hB : (1 : ℝ) - Real.exp (-(z₁ * t)) ≤ 1 - Real.exp (-(b * t)) := by
    have h : Real.exp (-(b * t)) ≤ Real.exp (-(z₁ * t)) := Real.exp_le_exp.mpr (by nlinarith)
    linarith
  have hA0 : 0 ≤ Real.exp (z₂ * t) := Real.exp_nonneg _
  have hB0 : 0 ≤ (1 : ℝ) - Real.exp (-(z₁ * t)) := by
    have h : Real.exp (-(z₁ * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    linarith
  have hB0' : 0 ≤ (1 : ℝ) - Real.exp (-(b * t)) := by
    have h : Real.exp (-(b * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    linarith
  calc Real.exp (z₂ * t) * (1 - Real.exp (-(z₁ * t)))
      ≤ Real.exp (z₂ * t) * (1 - Real.exp (-(b * t))) := by nlinarith [hA0, hB]
    _ ≤ Real.exp (c * t) * (1 - Real.exp (-(b * t))) := by nlinarith [hA, hB0']

/-- The bracket of (8.11) is monotone in the pair `(λ₁, λ₂)` on the region
`0 ≤ λ₁ ≤ λ₂`, in the sense needed by the extraction: the value at `(z₁, z₂)` is at
most the value at the row's `(b, c)`. -/
theorem bracket_integral_le {x₀ : ℝ} (hx₀ : 0 ≤ x₀) {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Set.Icc 0 x₀)) (hfnn : ∀ t ∈ Set.Icc 0 x₀, 0 ≤ f t)
    {z₁ b z₂ c : ℝ} (h1 : 0 ≤ z₁) (hz₁ : z₁ ≤ b) (hz₂ : z₂ ≤ c) :
    (∫ t in (0:ℝ)..x₀, Real.exp (z₂ * t) * f t)
        - (∫ t in (0:ℝ)..x₀, Real.exp ((z₂ - z₁) * t) * f t)
      ≤ (∫ t in (0:ℝ)..x₀, Real.exp (c * t) * f t)
        - (∫ t in (0:ℝ)..x₀, Real.exp ((c - b) * t) * f t) := by
  have hmem : Set.uIcc (0:ℝ) x₀ = Set.Icc 0 x₀ := Set.uIcc_of_le hx₀
  have hcontExp : ∀ m : ℝ, ContinuousOn (fun t : ℝ => Real.exp (m * t)) (Set.Icc 0 x₀) :=
    fun m => (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
  have hint : ∀ m : ℝ, IntervalIntegrable (fun t : ℝ => Real.exp (m * t) * f t) MeasureTheory.volume 0 x₀ := by
    intro m
    apply ContinuousOn.intervalIntegrable
    rw [hmem]
    exact ((hcontExp m).mul hcont)
  have hsub₁ : (∫ t in (0:ℝ)..x₀, Real.exp (z₂ * t) * f t)
      - (∫ t in (0:ℝ)..x₀, Real.exp ((z₂ - z₁) * t) * f t)
      = ∫ t in (0:ℝ)..x₀, (Real.exp (z₂ * t) - Real.exp ((z₂ - z₁) * t)) * f t := by
    rw [← intervalIntegral.integral_sub (hint z₂) (hint (z₂ - z₁))]
    exact intervalIntegral.integral_congr (fun t _ => by ring)
  have hsub₂ : (∫ t in (0:ℝ)..x₀, Real.exp (c * t) * f t)
      - (∫ t in (0:ℝ)..x₀, Real.exp ((c - b) * t) * f t)
      = ∫ t in (0:ℝ)..x₀, (Real.exp (c * t) - Real.exp ((c - b) * t)) * f t := by
    rw [← intervalIntegral.integral_sub (hint c) (hint (c - b))]
    exact intervalIntegral.integral_congr (fun t _ => by ring)
  rw [hsub₁, hsub₂]
  refine intervalIntegral.integral_mono_on hx₀ ?_ ?_ ?_
  · apply ContinuousOn.intervalIntegrable
    rw [hmem]
    exact ((hcontExp z₂).sub (hcontExp (z₂ - z₁))).mul hcont
  · apply ContinuousOn.intervalIntegrable
    rw [hmem]
    exact ((hcontExp c).sub (hcontExp (c - b))).mul hcont
  · intro t ht
    exact mul_le_mul_of_nonneg_right (bracket_le_bracket h1 hz₁ hz₂ ht.1) (hfnn t ht)

/-- **The extraction.**  If the row certificate strictly violates HB (8.11) at the row
values `(b, c)`, and (8.11) holds at the true pair `(λ₁, λ₂) = (z₁, z₂)`, then
`z₂ > c`: the failure of (8.11) at `λ₂ = c` forces the true `λ₂` to be larger.  Here
`F` is the Laplace transform of a non-negative test function supported in `[0, x₀]`,
given by its integral representation at the three points used. -/
theorem row_extract {x₀ : ℝ} (hx₀ : 0 ≤ x₀) {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Set.Icc 0 x₀)) (hfnn : ∀ t ∈ Set.Icc 0 x₀, 0 ≤ f t)
    {k A b c z₁ z₂ : ℝ} (h1 : 0 ≤ z₁) (hz₁ : z₁ ≤ b) (hz₂ : z₂ ≤ c)
    (heng : 0 ≤ (k ^ 2 + 1/2) *
        ((∫ t in (0:ℝ)..x₀, Real.exp (z₂ * t) * f t)
          - (∫ t in (0:ℝ)..x₀, Real.exp ((z₂ - z₁) * t) * f t))
        - 2 * k * (∫ t in (0:ℝ)..x₀, f t) + A)
    (hcert : (k ^ 2 + 1/2) *
        ((∫ t in (0:ℝ)..x₀, Real.exp (c * t) * f t)
          - (∫ t in (0:ℝ)..x₀, Real.exp ((c - b) * t) * f t))
        - 2 * k * (∫ t in (0:ℝ)..x₀, f t) + A < 0) (_hk : 0 ≤ k) : False := by
  have hkey := bracket_integral_le hx₀ hcont hfnn h1 hz₁ hz₂
  have hcoef : 0 ≤ k ^ 2 + 1/2 := by positivity
  have hmono := mul_le_mul_of_nonneg_left hkey hcoef
  linarith

end Work.ZeroFreeTables
