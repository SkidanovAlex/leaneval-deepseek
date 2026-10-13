import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Weighted Hardy inequality with a boundary term (`hardyBoundaryPower`)

For `λ > -1` and `0 < a < b`, and `f` of class `C¹` on `(0,∞)`:

```
(1+λ)²/4 ∫_a^b x^{-(2+λ)} f(x)² dx
    ≤ ∫_a^b x^{-λ} f'(x)² dx
      - (1+λ)/2 ( b^{-(1+λ)} f(b)² - a^{-(1+λ)} f(a)² ).
```

This is the sharp weighted Hardy inequality *with* the boundary term kept
(the case `a = 0`, `f(0) = 0` reduces to the classical
`(1+λ)²/4 ∫ x^{-(2+λ)}f² ≤ ∫ x^{-λ}f'²`).

The proof is the standard completion of squares.  Writing
`X := (1+λ)/2`, `I₁ := ∫_a^b x^{-λ}f'²`, `I₂ := ∫_a^b x^{-(2+λ)}f²` and
`D := b^{-(1+λ)}f(b)² - a^{-(1+λ)}f(a)²`:

* (FTC) `d/dx (x^{-(1+λ)} f(x)²) = -(1+λ) x^{-(2+λ)} f² + 2 x^{-(1+λ)} f f'`,
  hence `∫_a^b x^{-(1+λ)} f f' = D/2 + X I₂`;
* pointwise, `x^{-λ}(f' - X f/x)² = x^{-λ}f'² - X (d/dx (x^{-(1+λ)}f²)) - X² x^{-(2+λ)}f²`.

Integrating the last identity over `[a,b]` and inserting the FTC identity yields

`0 ≤ ∫_a^b x^{-λ}(f' - X f/x)² = I₁ - X D - X² I₂`,

i.e. `X² I₂ ≤ I₁ - X D`, which is the claim since `X² = (1+λ)²/4`.
-/

open MeasureTheory

namespace Work.EllipticEst.Core

/-- `deriv f` is continuous on `(0,∞)` when `f` is of class `C¹` there. -/
lemma hardyPower_contOn_deriv {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) :
    ContinuousOn (deriv f) (Set.Ioi 0) := by
  refine (hf.continuousOn_derivWithin (uniqueDiffOn_Ioi 0) le_rfl).congr ?_
  intro x hx
  exact (derivWithin_of_isOpen isOpen_Ioi hx).symm

/-- `x ↦ x ^ c` is continuous on `(0,∞)`. -/
lemma hardyPower_contOn_rpow (c : ℝ) : ContinuousOn (fun x : ℝ => x ^ c) (Set.Ioi 0) := by
  intro x hx
  exact (Real.continuousAt_rpow_const x c (Or.inl (ne_of_gt hx))).continuousWithinAt

/-- The pointwise completion-of-squares identity behind the inequality.  For `x > 0`
and `X := (1+λ)/2`:
`x^{-λ}(v - X u/x)² = x^{-λ}v² - X(-(1+λ)x^{-(2+λ)}u² + 2x^{-(1+λ)}uv) - X² x^{-(2+λ)}u²`. -/
lemma hardyPower_sq_deriv_pointwise (lam x u v : ℝ) (hx : 0 < x) :
    x ^ (-lam) * (v - (1+lam)/2 * x⁻¹ * u)^2
      = x ^ (-lam) * v^2
        - (1+lam)/2 * (-(1+lam) * x ^ (-(2+lam)) * u^2 + 2 * x ^ (-(1+lam)) * u * v)
        - ((1+lam)/2)^2 * (x ^ (-(2+lam)) * u^2) := by
  have h1 : x ^ (-(1+lam)) = x ^ (-lam) * x⁻¹ := by
    rw [show -(1+lam) = -lam + (-1) by ring, Real.rpow_add hx, Real.rpow_neg_one]
  have h2 : x ^ (-(2+lam)) = x ^ (-lam) * x⁻¹ * x⁻¹ := by
    rw [show -(2+lam) = -lam + (-1) + (-1) by ring, Real.rpow_add hx, Real.rpow_add hx,
      Real.rpow_neg_one]
  rw [h1, h2]
  ring

/-- Fundamental-theorem-of-calculus identity: the integral of
`-(1+λ)x^{-(2+λ)}f² + 2x^{-(1+λ)}ff'` is the boundary term `D`. -/
lemma hardyPower_ftc (lam : ℝ) (f : ℝ → ℝ) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) :
    (∫ x in a..b, (-(1+lam) * x ^ (-(2+lam)) * (f x)^2 + 2 * x ^ (-(1+lam)) * f x * deriv f x))
      = b ^ (-(1+lam)) * (f b)^2 - a ^ (-(1+lam)) * (f a)^2 := by
  have hab' : a ≤ b := le_of_lt hab
  have hsubI : Set.uIcc a b ⊆ Set.Ioi 0 := by
    rw [Set.uIcc_of_le hab']
    exact fun x hx => lt_of_lt_of_le ha hx.1
  have hd : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun y : ℝ => y ^ (-(1+lam)) * (f y)^2)
        (-(1+lam) * x ^ (-(2+lam)) * (f x)^2 + 2 * x ^ (-(1+lam)) * f x * deriv f x) x := by
    intro x hx
    have hx0 : 0 < x := hsubI hx
    have h1 : HasDerivAt (fun y : ℝ => y ^ (-(1+lam))) (-(1+lam) * x ^ (-(2+lam))) x := by
      have h := Real.hasDerivAt_rpow_const (x := x) (p := -(1+lam)) (Or.inl (ne_of_gt hx0))
      convert h using 1
      rw [show -(1+lam) - 1 = -(2+lam) by ring]
    have h2 : HasDerivAt (fun y : ℝ => f y ^ 2) (2 * f x * deriv f x) x := by
      have hf' : HasDerivAt f (deriv f x) x :=
        (hf.differentiableOn (by simp)).hasDerivAt (isOpen_Ioi.mem_nhds hx0)
      have h := hf'.pow 2
      convert h using 1
      norm_num
    have h3 := h1.mul h2
    convert h3 using 1
    ring
  have hint : IntervalIntegrable
      (fun x : ℝ => -(1+lam) * x ^ (-(2+lam)) * (f x)^2 + 2 * x ^ (-(1+lam)) * f x * deriv f x)
      volume a b := by
    have hdf : ContinuousOn (deriv f) (Set.Ioi 0) := hardyPower_contOn_deriv hf
    have hf0 : ContinuousOn f (Set.Ioi 0) := hf.continuousOn
    have hB1 : ContinuousOn (fun x : ℝ => -(1+lam) * x ^ (-(2+lam)) * (f x)^2) (Set.Ioi 0) :=
      (continuousOn_const.mul (hardyPower_contOn_rpow _)).mul (hf0.pow 2)
    have hB2 : ContinuousOn (fun x : ℝ => 2 * x ^ (-(1+lam)) * f x * deriv f x) (Set.Ioi 0) :=
      ((continuousOn_const.mul (hardyPower_contOn_rpow _)).mul hf0).mul hdf
    exact ((hB1.add hB2).mono hsubI).intervalIntegrable
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]

/-- The three integrands appearing in the argument are interval-integrable on `[a,b]`
for `0 < a ≤ b` and `f` of class `C¹` on `(0,∞)`. -/
lemma hardyPower_intervalIntegrable (lam : ℝ) (f : ℝ → ℝ) (a b : ℝ) (ha : 0 < a)
    (hab : a ≤ b) (hf : ContDiffOn ℝ 1 f (Set.Ioi 0)) :
    IntervalIntegrable (fun x : ℝ => x ^ (-lam) * (deriv f x)^2) volume a b
      ∧ IntervalIntegrable (fun x : ℝ => x ^ (-(2+lam)) * (f x)^2) volume a b
      ∧ IntervalIntegrable (fun x : ℝ => -(1+lam) * x ^ (-(2+lam)) * (f x)^2
          + 2 * x ^ (-(1+lam)) * f x * deriv f x) volume a b := by
  have hsubI : Set.uIcc a b ⊆ Set.Ioi 0 := by
    rw [Set.uIcc_of_le hab]
    exact fun x hx => lt_of_lt_of_le ha hx.1
  have hdf : ContinuousOn (deriv f) (Set.Ioi 0) := hardyPower_contOn_deriv hf
  have hf0 : ContinuousOn f (Set.Ioi 0) := hf.continuousOn
  refine ⟨?_, ?_, ?_⟩
  · exact (((hardyPower_contOn_rpow _).mul (hdf.pow 2)).mono hsubI).intervalIntegrable
  · exact (((hardyPower_contOn_rpow _).mul (hf0.pow 2)).mono hsubI).intervalIntegrable
  · have hB1 : ContinuousOn (fun x : ℝ => -(1+lam) * x ^ (-(2+lam)) * (f x)^2) (Set.Ioi 0) :=
      (continuousOn_const.mul (hardyPower_contOn_rpow _)).mul (hf0.pow 2)
    have hB2 : ContinuousOn (fun x : ℝ => 2 * x ^ (-(1+lam)) * f x * deriv f x) (Set.Ioi 0) :=
      ((continuousOn_const.mul (hardyPower_contOn_rpow _)).mul hf0).mul hdf
    exact ((hB1.add hB2).mono hsubI).intervalIntegrable

/-- **Weighted Hardy inequality with boundary term.**  See the module docstring for the
mathematical content and the (completion-of-squares) proof. -/
theorem hardyBoundaryPower : ∀ (lam : ℝ) (f : ℝ → ℝ) (a b : ℝ), -1 < lam → 0 < a → a < b → ContDiffOn ℝ 1 f (Set.Ioi 0) → (1+lam)^2/4 * (∫ x in a..b, x ^ (-(2+lam)) * (f x)^2) ≤ (∫ x in a..b, x ^ (-lam) * (deriv f x)^2) - (1+lam)/2 * (b ^ (-(1+lam)) * (f b)^2 - a ^ (-(1+lam)) * (f a)^2) := by
  intro lam f a b _hlam ha hab hf
  have hab' : a ≤ b := le_of_lt hab
  have hsubI : Set.uIcc a b ⊆ Set.Ioi 0 := by
    rw [Set.uIcc_of_le hab']
    exact fun x hx => lt_of_lt_of_le ha hx.1
  obtain ⟨hA, hC, hB⟩ := hardyPower_intervalIntegrable lam f a b ha hab' hf
  -- the completed square is nonnegative
  have hsq : 0 ≤ ∫ x in a..b, x ^ (-lam) * (deriv f x - (1+lam)/2 * x⁻¹ * f x)^2 := by
    refine intervalIntegral.integral_nonneg hab' (fun u hu => ?_)
    have hu0 : 0 < u := hsubI (by rw [Set.uIcc_of_le hab']; exact hu)
    exact mul_nonneg (Real.rpow_nonneg hu0.le _) (sq_nonneg _)
  -- the pointwise identity
  have hpt : Set.EqOn (fun x : ℝ => x ^ (-lam) * (deriv f x - (1+lam)/2 * x⁻¹ * f x)^2)
      (fun x : ℝ => x ^ (-lam) * (deriv f x)^2
        - (1+lam)/2 * (-(1+lam) * x ^ (-(2+lam)) * (f x)^2 + 2 * x ^ (-(1+lam)) * f x * deriv f x)
        - ((1+lam)/2)^2 * (x ^ (-(2+lam)) * (f x)^2)) (Set.uIcc a b) := by
    intro x hx
    exact hardyPower_sq_deriv_pointwise lam x (f x) (deriv f x) (hsubI hx)
  rw [intervalIntegral.integral_congr hpt] at hsq
  -- split the integral
  have hXB : IntervalIntegrable (fun x : ℝ => (1+lam)/2 *
      (-(1+lam) * x ^ (-(2+lam)) * (f x)^2 + 2 * x ^ (-(1+lam)) * f x * deriv f x)) volume a b :=
    hB.const_mul _
  have hX2C : IntervalIntegrable (fun x : ℝ => ((1+lam)/2)^2 * (x ^ (-(2+lam)) * (f x)^2))
      volume a b := hC.const_mul _
  have hAB : IntervalIntegrable (fun x : ℝ => x ^ (-lam) * (deriv f x)^2
      - (1+lam)/2 * (-(1+lam) * x ^ (-(2+lam)) * (f x)^2 + 2 * x ^ (-(1+lam)) * f x * deriv f x))
      volume a b := hA.sub hXB
  rw [intervalIntegral.integral_sub hAB hX2C, intervalIntegral.integral_sub hA hXB,
    intervalIntegral.integral_const_mul ((1+lam)/2),
    intervalIntegral.integral_const_mul (((1+lam)/2)^2)] at hsq
  -- the FTC identity
  rw [hardyPower_ftc lam f a b ha hab hf] at hsq
  -- conclude
  have hsq2 : ((1+lam)/2)^2 = (1+lam)^2/4 := by ring
  rw [hsq2] at hsq
  linarith [hsq]

end Work.EllipticEst.Core
