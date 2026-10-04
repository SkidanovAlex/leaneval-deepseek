import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.C.ShapeAux

open scoped Topology InnerProductSpace

/-- Derivative at `0` of the `sqrt` of a quadratic `s ↦ α + 2 s β + s² γ` (with `α > 0`). -/
private lemma hasDerivAt_quad (α β γ : ℝ) (s : ℝ) :
    HasDerivAt (fun t : ℝ => α + 2 * t * β + t ^ 2 * γ) (2 * β + 2 * s * γ) s := by
  have h1 : HasDerivAt (fun t : ℝ => α + 2 * t * β) (2 * β) s := by
    have h := ((hasDerivAt_id s).const_mul 2).mul_const β
    simpa using h.const_add α
  have h2 : HasDerivAt (fun t : ℝ => t ^ 2 * γ) (2 * s * γ) s := by
    simpa using (hasDerivAt_pow 2 s).mul_const γ
  exact h1.add h2

/-- First derivative at `0` of `s ↦ √(α + 2 s β + s² γ)`. -/
private lemma deriv_sqrt_quad (α β γ : ℝ) (hα : 0 < α) :
    deriv (fun s : ℝ => Real.sqrt (α + 2 * s * β + s ^ 2 * γ)) 0 = β / Real.sqrt α := by
  have h0 : α + 2 * (0 : ℝ) * β + (0 : ℝ) ^ 2 * γ = α := by ring
  have hd : DifferentiableAt ℝ (fun t : ℝ => α + 2 * t * β + t ^ 2 * γ) 0 :=
    (hasDerivAt_quad α β γ 0).differentiableAt
  have hne : (fun t : ℝ => α + 2 * t * β + t ^ 2 * γ) 0 ≠ 0 := by
    simp only [h0]; exact hα.ne'
  rw [deriv_sqrt hd hne, (hasDerivAt_quad α β γ 0).deriv]
  simp only [h0]
  field_simp
  ring

/-- Second derivative at `0` of `s ↦ √(α + 2 s β + s² γ)`: it equals
`(α γ - β²)/(√α)³`. -/
private lemma deriv_deriv_sqrt_quad (α β γ : ℝ) (hα : 0 < α) :
    HasDerivAt (deriv (fun s : ℝ => Real.sqrt (α + 2 * s * β + s ^ 2 * γ)))
      ((α * γ - β ^ 2) / (Real.sqrt α) ^ 3) 0 := by
  have h0 : α + 2 * (0 : ℝ) * β + (0 : ℝ) ^ 2 * γ = α := by ring
  have hq0ne : (fun t : ℝ => α + 2 * t * β + t ^ 2 * γ) 0 ≠ 0 := by
    simp only [h0]; exact hα.ne'
  have hnum : HasDerivAt (fun s : ℝ => 2 * β + 2 * s * γ) (2 * γ) 0 := by
    simpa using (hasDerivAt_quad (2 * β) γ 0 (0 : ℝ))
  have hden : HasDerivAt (fun s : ℝ => 2 * Real.sqrt (α + 2 * s * β + s ^ 2 * γ))
      (2 * ((2 * β + 2 * 0 * γ) / (2 * Real.sqrt (α + 2 * 0 * β + 0 ^ 2 * γ)))) 0 :=
    ((hasDerivAt_quad α β γ 0).sqrt hq0ne).const_mul 2
  have hdenne : 2 * Real.sqrt (α + 2 * 0 * β + 0 ^ 2 * γ) ≠ 0 := by
    rw [h0]; positivity
  have hdiv := hnum.div hden hdenne
  have hval : ((2 * γ) * (2 * Real.sqrt (α + 2 * 0 * β + 0 ^ 2 * γ)) -
        (2 * β + 2 * 0 * γ) * (2 * ((2 * β + 2 * 0 * γ) /
          (2 * Real.sqrt (α + 2 * 0 * β + 0 ^ 2 * γ))))) /
        (2 * Real.sqrt (α + 2 * 0 * β + 0 ^ 2 * γ)) ^ 2 =
      (α * γ - β ^ 2) / (Real.sqrt α) ^ 3 := by
    rw [h0]
    field_simp
    ring_nf
    rw [Real.sq_sqrt hα.le]
  rw [hval] at hdiv
  have hcont : ContinuousAt (fun t : ℝ => α + 2 * t * β + t ^ 2 * γ) 0 :=
    (hasDerivAt_quad α β γ 0).continuousAt
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), (fun t : ℝ => α + 2 * t * β + t ^ 2 * γ) s ≠ 0 :=
    hcont.eventually_ne hq0ne
  have heq : deriv (fun s : ℝ => Real.sqrt (α + 2 * s * β + s ^ 2 * γ)) =ᶠ[𝓝 0]
      (fun s : ℝ => (2 * β + 2 * s * γ) / (2 * Real.sqrt (α + 2 * s * β + s ^ 2 * γ))) := by
    filter_upwards [hev] with s hs
    rw [deriv_sqrt ((hasDerivAt_quad α β γ s).differentiableAt) (by simpa using hs),
        (hasDerivAt_quad α β γ s).deriv]
  exact hdiv.congr_of_eventuallyEq heq

/-- First and second derivative at `0` of `s ↦ ‖a + s • b‖` in an inner product space: the first
derivative is `⟪a,b⟫/‖a‖` and the second is `(‖a‖²‖b‖² - ⟪a,b⟫²)/‖a‖³`.  (Used with `a = d • u`,
`‖u‖ = 1`, where they become `⟪u,b⟫` and `(‖b‖² - ⟪u,b⟫²)/d`.) -/
theorem norm_add_smul_deriv_deriv
    {T : Type*} [NormedAddCommGroup T] [InnerProductSpace ℝ T]
    {a b : T} (ha : a ≠ 0) :
    deriv (fun s : ℝ => ‖a + s • b‖) 0 = Inner.inner ℝ a b / ‖a‖ ∧
    HasDerivAt (deriv (fun s : ℝ => ‖a + s • b‖))
      ((‖a‖ ^ 2 * ‖b‖ ^ 2 - (Inner.inner ℝ a b) ^ 2) / ‖a‖ ^ 3) 0 := by
  have hsq : ∀ s : ℝ,
      ‖a + s • b‖ ^ 2 = ‖a‖ ^ 2 + 2 * s * (Inner.inner ℝ a b) + s ^ 2 * ‖b‖ ^ 2 := by
    intro s
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have hfeq : (fun s : ℝ => ‖a + s • b‖)
      = (fun s : ℝ => Real.sqrt (‖a‖ ^ 2 + 2 * s * (Inner.inner ℝ a b) + s ^ 2 * ‖b‖ ^ 2)) := by
    funext s
    rw [← hsq s, Real.sqrt_sq (norm_nonneg _)]
  have hna2 : 0 < ‖a‖ ^ 2 := pow_pos (norm_pos_iff.mpr ha) 2
  have hsqrt : Real.sqrt (‖a‖ ^ 2) = ‖a‖ := Real.sqrt_sq (norm_nonneg a)
  constructor
  · rw [Filter.EventuallyEq.deriv_eq (Filter.EventuallyEq.of_eq hfeq),
        deriv_sqrt_quad (‖a‖ ^ 2) (Inner.inner ℝ a b) (‖b‖ ^ 2) hna2, hsqrt]
  · have h2 : HasDerivAt
        (deriv (fun s : ℝ => Real.sqrt (‖a‖ ^ 2 + 2 * s * (Inner.inner ℝ a b) + s ^ 2 * ‖b‖ ^ 2)))
        (((‖a‖ ^ 2) * (‖b‖ ^ 2) - (Inner.inner ℝ a b) ^ 2) / (Real.sqrt (‖a‖ ^ 2)) ^ 3) 0 :=
      deriv_deriv_sqrt_quad (‖a‖ ^ 2) (Inner.inner ℝ a b) (‖b‖ ^ 2) hna2
    rw [hsqrt] at h2
    have hev : deriv (fun s : ℝ => ‖a + s • b‖)
        =ᶠ[𝓝 0] deriv (fun s : ℝ =>
          Real.sqrt (‖a‖ ^ 2 + 2 * s * (Inner.inner ℝ a b) + s ^ 2 * ‖b‖ ^ 2)) :=
      Filter.EventuallyEq.deriv (Filter.EventuallyEq.of_eq hfeq)
    exact h2.congr_of_eventuallyEq hev

end Work.Diff.C.ShapeAux
