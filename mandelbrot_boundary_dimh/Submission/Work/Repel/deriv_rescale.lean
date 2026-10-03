import Mathlib

namespace Work.Repel

/-- Rescaling does not change the derivative at `0`: the affine conjugation
`ζ ↦ s * f (ζ / s)` (with `s ≠ 0`) has the same derivative at `0` as `f`.
The statement is unconditional: when `f` is not complex differentiable at `0`
both sides vanish, since `ζ ↦ ζ / s` is a biholomorphism of a neighbourhood
of `0` fixing `0`. -/
theorem deriv_rescale (f : ℂ → ℂ) (s : ℂ) (hs : s ≠ 0) :
    deriv (fun ζ : ℂ => s * f (ζ / s)) 0 = deriv f 0 := by
  rcases em (DifferentiableAt ℂ f 0) with hf | hf
  · -- `f` is differentiable at `0`: chain rule, then simplify `s * (f' * s⁻¹) = f'`.
    have hd : DifferentiableAt ℂ (fun ζ : ℂ => ζ / s) 0 := differentiableAt_id.div_const s
    have hcomp := deriv_comp (x := (0 : ℂ)) (h₂ := f) (h := fun ζ : ℂ => ζ / s)
      (by simpa using hf) hd
    simp only [Function.comp_def, zero_div] at hcomp
    rw [deriv_const_mul_field s, hcomp, deriv_div_const, deriv_id'']
    field_simp
  · -- `f` is not differentiable at `0`: both derivatives vanish.
    have hF : ¬ DifferentiableAt ℂ (fun ζ : ℂ => s * f (ζ / s)) 0 := by
      intro hF
      -- otherwise `f = fun w => (1/s) * (s * f ((w * s) / s))` would be differentiable.
      have hid : DifferentiableAt ℂ (fun w : ℂ => w * s) 0 :=
        differentiableAt_id.mul_const s
      have hF' : DifferentiableAt ℂ (fun ζ : ℂ => s * f (ζ / s))
          ((fun w : ℂ => w * s) 0) := by
        simpa using hF
      have h1 : DifferentiableAt ℂ (fun w : ℂ => s * f ((w * s) / s)) 0 :=
        DifferentiableAt.comp (x := (0 : ℂ)) (f := fun w : ℂ => w * s)
          (g := fun ζ : ℂ => s * f (ζ / s)) hF' hid
      have h2 : DifferentiableAt ℂ (fun w : ℂ => (1/s) * (s * f ((w * s) / s))) 0 :=
        h1.const_mul (1/s)
      have hfe : (fun w : ℂ => (1/s) * (s * f ((w * s) / s))) = f := by
        funext w
        have hws : (w * s) / s = w := by
          rw [div_eq_mul_inv, mul_assoc, mul_inv_cancel₀ hs, mul_one]
        rw [hws, ← mul_assoc, one_div, inv_mul_cancel₀ hs, one_mul]
      rw [hfe] at h2
      exact hf h2
    rw [deriv_zero_of_not_differentiableAt hF, deriv_zero_of_not_differentiableAt hf]

end Work.Repel
