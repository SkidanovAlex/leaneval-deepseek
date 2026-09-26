import Mathlib
import Submission.Work.Drive.Mono.Residual

/-!
# Reduction of the parameter plane to the fundamental domain `[0, 2π] × [0, 2π]`

The parametrisation of the challenge's surface is

  `par ψ (x, y) = ψ (torusMap x y)`,

and `torusMap` is `2π`-periodic in each variable (`Work.Core.torusMap_add_two_pi_left`,
`Work.Core.torusMap_add_two_pi_right`).  Consequently the whole one-parameter family built on `par ψ`
— its values, and (because `par ψ` is `C^∞`) also its derivative — is invariant under the
translation `(x, y) ↦ (x + 2πk, y + 2πm)` of the parameter plane by an element of the period
lattice `(2πℤ)²`.

This module records that invariance in the form used downstream: every parameter `p : ℝ × ℝ` has a
translate `p₀` in the *fundamental domain* `[0, 2π] × [0, 2π]` which is indistinguishable from `p`
as far as `par ψ` is concerned, both in value and in derivative.

## Main results

* `par_add_int_mul_two_pi_left`, `par_add_int_mul_two_pi_right` — the periodicity of `par ψ` in each
  variable by an integer multiple of `2π`;
* `fderiv_par_add_int_mul_two_pi_left`, `fderiv_par_add_int_mul_two_pi_right` — the same invariance
  for the Fréchet derivative (the chain rule for a translation, plus the invariance of the function);
* `exists_int_sub_mul_mem_Icc_two_pi` — every real number has a translate into `[0, 2π]` by an
  integer multiple of `2π`;
* `fundamentalDomain_reduction` — the reduction statement.
-/

namespace Work.Drive.Mono.Band

open LeanEval.KnotTheory.PardonDistortion

noncomputable section

/-! ## Periodicity of `par ψ` by integer multiples of `2π` -/

/-- `torusMap` is periodic in its first variable with period any integer multiple of `2π`. -/
theorem torusMap_add_int_mul_two_pi_left' (k : ℤ) (θ φ : ℝ) :
    Work.Core.torusMap (θ + k * (2 * Real.pi)) φ = Work.Core.torusMap θ φ := by
  unfold Work.Core.torusMap
  simp [Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

/-- `torusMap` is periodic in its second variable with period any integer multiple of `2π`. -/
theorem torusMap_add_int_mul_two_pi_right' (k : ℤ) (θ φ : ℝ) :
    Work.Core.torusMap θ (φ + k * (2 * Real.pi)) = Work.Core.torusMap θ φ := by
  unfold Work.Core.torusMap
  simp [Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

/-- `par ψ` is invariant under translation of the first parameter by an integer multiple of `2π`. -/
theorem par_add_int_mul_two_pi_left (ψ : Submission.Diffeo) (k : ℤ) (p : ℝ × ℝ) :
    Work.BoxShrink.Pinch.par ψ (p + (k * (2 * Real.pi), 0))
      = Work.BoxShrink.Pinch.par ψ p := by
  obtain ⟨x, y⟩ := p
  simp only [Prod.mk_add_mk, add_zero]
  simp only [Work.BoxShrink.Pinch.par_apply]
  rw [torusMap_add_int_mul_two_pi_left']

/-- `par ψ` is invariant under translation of the second parameter by an integer multiple of `2π`. -/
theorem par_add_int_mul_two_pi_right (ψ : Submission.Diffeo) (k : ℤ) (p : ℝ × ℝ) :
    Work.BoxShrink.Pinch.par ψ (p + (0, k * (2 * Real.pi)))
      = Work.BoxShrink.Pinch.par ψ p := by
  obtain ⟨x, y⟩ := p
  simp only [Prod.mk_add_mk, add_zero]
  simp only [Work.BoxShrink.Pinch.par_apply]
  rw [torusMap_add_int_mul_two_pi_right']

/-! ## The same invariance for the derivative

`par ψ` is `C^∞`, so the derivative of the translate `q ↦ par ψ (q + a)` is the derivative of
`par ψ` at `q + a`; since the translate *is* `par ψ` (periodicity), the derivative is unchanged. -/

/-- The derivative of `par ψ` is invariant under translation of the first parameter by an integer
multiple of `2π`. -/
theorem fderiv_par_add_int_mul_two_pi_left (ψ : Submission.Diffeo) (k : ℤ) (p : ℝ × ℝ) :
    fderiv ℝ (Work.BoxShrink.Pinch.par ψ) (p + (k * (2 * Real.pi), 0))
      = fderiv ℝ (Work.BoxShrink.Pinch.par ψ) p := by
  have hfun : (fun q : ℝ × ℝ => Work.BoxShrink.Pinch.par ψ (q + (k * (2 * Real.pi), 0)))
      = Work.BoxShrink.Pinch.par ψ := funext fun q => par_add_int_mul_two_pi_left ψ k q
  have h := fderiv_comp_add_right (𝕜 := ℝ) (k * (2 * Real.pi), 0)
    (f := Work.BoxShrink.Pinch.par ψ) (x := p)
  rw [hfun] at h
  exact h.symm

/-- The derivative of `par ψ` is invariant under translation of the second parameter by an integer
multiple of `2π`. -/
theorem fderiv_par_add_int_mul_two_pi_right (ψ : Submission.Diffeo) (k : ℤ) (p : ℝ × ℝ) :
    fderiv ℝ (Work.BoxShrink.Pinch.par ψ) (p + (0, k * (2 * Real.pi)))
      = fderiv ℝ (Work.BoxShrink.Pinch.par ψ) p := by
  have hfun : (fun q : ℝ × ℝ => Work.BoxShrink.Pinch.par ψ (q + (0, k * (2 * Real.pi))))
      = Work.BoxShrink.Pinch.par ψ := funext fun q => par_add_int_mul_two_pi_right ψ k q
  have h := fderiv_comp_add_right (𝕜 := ℝ) (0, k * (2 * Real.pi))
    (f := Work.BoxShrink.Pinch.par ψ) (x := p)
  rw [hfun] at h
  exact h.symm

/-! ## Reduction into `[0, 2π]` -/

/-- Every real number has a translate into `[0, 2π]` differing from it by an integer multiple of
`2π` (take the integer part of `x / 2π`). -/
theorem exists_int_sub_mul_mem_Icc_two_pi (x : ℝ) :
    ∃ k : ℤ, x - k * (2 * Real.pi) ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := by
  have hc : (0 : ℝ) < 2 * Real.pi := by positivity
  refine ⟨⌊x / (2 * Real.pi)⌋, ?_, ?_⟩
  · have h1 : ((⌊x / (2 * Real.pi)⌋ : ℤ) : ℝ) * (2 * Real.pi) ≤ x := by
      have h := Int.floor_le (x / (2 * Real.pi))
      have h2 : ((⌊x / (2 * Real.pi)⌋ : ℤ) : ℝ) * (2 * Real.pi)
          ≤ (x / (2 * Real.pi)) * (2 * Real.pi) :=
        mul_le_mul_of_nonneg_right h (le_of_lt hc)
      rwa [div_mul_cancel₀ x (ne_of_gt hc)] at h2
    linarith
  · have h2 : x < ((⌊x / (2 * Real.pi)⌋ : ℤ) : ℝ) * (2 * Real.pi) + 2 * Real.pi := by
      have h := Int.lt_floor_add_one (x / (2 * Real.pi))
      have hm : (x / (2 * Real.pi)) * (2 * Real.pi)
          < (((⌊x / (2 * Real.pi)⌋ : ℤ) : ℝ) + 1) * (2 * Real.pi) :=
        mul_lt_mul_of_pos_right h hc
      rw [div_mul_cancel₀ x (ne_of_gt hc)] at hm
      calc x < (((⌊x / (2 * Real.pi)⌋ : ℤ) : ℝ) + 1) * (2 * Real.pi) := hm
        _ = ((⌊x / (2 * Real.pi)⌋ : ℤ) : ℝ) * (2 * Real.pi) + 2 * Real.pi := by ring
    linarith

/-- **Reduction to the fundamental domain.**  Every parameter in the plane of the parametrisation
`par ψ = ψ ∘ torusMap` has a translate in `[0, 2π] × [0, 2π]` at which both the value of `par ψ` and
its derivative are the same. -/
theorem fundamentalDomain_reduction (ψ : Submission.Diffeo) (p : ℝ × ℝ) :
    ∃ p₀ : ℝ × ℝ, p₀ ∈ Set.Icc 0 (2 * Real.pi) ×ˢ Set.Icc 0 (2 * Real.pi) ∧
      Work.BoxShrink.Pinch.par ψ p₀ = Work.BoxShrink.Pinch.par ψ p ∧
      fderiv ℝ (Work.BoxShrink.Pinch.par ψ) p₀ = fderiv ℝ (Work.BoxShrink.Pinch.par ψ) p := by
  obtain ⟨x, y⟩ := p
  obtain ⟨k, hk⟩ := exists_int_sub_mul_mem_Icc_two_pi x
  obtain ⟨m, hm⟩ := exists_int_sub_mul_mem_Icc_two_pi y
  set X : ℝ := x - k * (2 * Real.pi) with hX
  set Y : ℝ := y - m * (2 * Real.pi) with hY
  have hx : x = X + k * (2 * Real.pi) := by rw [hX]; ring
  have hy : y = Y + m * (2 * Real.pi) := by rw [hY]; ring
  have hxy : (x, y) = (X + k * (2 * Real.pi), Y + m * (2 * Real.pi)) := by rw [hx, hy]
  refine ⟨(X, Y), ⟨hk, hm⟩, ?_, ?_⟩
  · have ha := par_add_int_mul_two_pi_left ψ k (X, Y + m * (2 * Real.pi))
    simp only [Prod.mk_add_mk, add_zero] at ha
    have hb := par_add_int_mul_two_pi_right ψ m (X, Y)
    simp only [Prod.mk_add_mk, add_zero] at hb
    rw [hxy, ha, hb]
  · have ha := fderiv_par_add_int_mul_two_pi_left ψ k (X, Y + m * (2 * Real.pi))
    simp only [Prod.mk_add_mk, add_zero] at ha
    have hb := fderiv_par_add_int_mul_two_pi_right ψ m (X, Y)
    simp only [Prod.mk_add_mk, add_zero] at hb
    rw [hxy, ha, hb]

end

end Work.Drive.Mono.Band
