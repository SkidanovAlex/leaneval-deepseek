import Mathlib
import Submission.Work.Smooth.Morse.ParamDeriv

/-!
# The derivative of the torus parametrisation is injective

The two partial derivatives of the torus parametrisation,
`dtheta = (-(2 + cos φ) sin θ, (2 + cos φ) cos θ, 0)` and
`dphi = (- sin φ cos θ, - sin φ sin θ, cos φ)`, are linearly independent at every point, so the
derivative `torusDeriv p = (a₁, a₂) ↦ a₁ • dtheta p + a₂ • dphi p` is injective.  Equivalently
`torusMap` is an immersion.

The proof extracts the three components of the relation `a₁ • dtheta p + a₂ • dphi p = 0`, namely

`a₁ (2 + cos φ) sin θ + a₂ sin φ cos θ = 0`,
`-a₁ (2 + cos φ) cos θ + a₂ sin φ sin θ = 0`,
`a₂ cos φ = 0`,

and eliminates: pairing the first two with `sin θ, cos θ` and with `cos θ, sin θ` (using
`sin²θ + cos²θ = 1`) gives `a₁ (2 + cos φ) = 0` and `a₂ sin φ = 0`, whence `a₁ = 0` (as
`2 + cos φ ≥ 1`) and `a₂ = a₂ (sin²φ + cos²φ) = 0`.
-/

open LeanEval.KnotTheory.PardonDistortion

namespace Work.Smooth.Morse.Immersion

/-- The kernel of the derivative of the torus parametrisation is trivial. -/
lemma torusDeriv_eq_zero (p a : ℝ × ℝ) (h : Work.Smooth.Morse.torusDeriv p a = 0) :
    a = 0 := by
  rw [Work.Smooth.Morse.torusDeriv_apply] at h
  have h' : ∀ i : Fin 3,
      (a.1 • Work.Smooth.Morse.dtheta p + a.2 • Work.Smooth.Morse.dphi p) i = 0 :=
    fun i => by have := congrArg (fun v : R3 => v i) h; simpa using this
  have h0 := h' 0
  have h1 := h' 1
  have h2 := h' 2
  simp only [PiLp.add_apply, PiLp.smul_apply, Work.Smooth.Morse.dtheta_zero,
    Work.Smooth.Morse.dtheta_one, Work.Smooth.Morse.dtheta_two, Work.Smooth.Morse.dphi_zero,
    Work.Smooth.Morse.dphi_one, Work.Smooth.Morse.dphi_two, smul_eq_mul] at h0 h1 h2
  have hApos : (0 : ℝ) < 2 + Real.cos p.2 := by
    have := Real.neg_one_le_cos p.2; linarith
  have hfirst : a.1 * (2 + Real.cos p.2) = 0 := by
    linear_combination (-Real.sin p.1) * h0 + (Real.cos p.1) * h1 -
      (a.1 * (2 + Real.cos p.2)) * Real.sin_sq_add_cos_sq p.1
  have hsecond : a.2 * Real.sin p.2 = 0 := by
    linear_combination (-(Real.cos p.1)) * h0 + (-(Real.sin p.1)) * h1 -
      (a.2 * Real.sin p.2) * Real.sin_sq_add_cos_sq p.1
  have hthird : a.2 = 0 := by
    linear_combination (Real.sin p.2) * hsecond + (Real.cos p.2) * h2 -
      a.2 * Real.sin_sq_add_cos_sq p.2
  have hfst : a.1 = 0 := by
    rcases mul_eq_zero.mp hfirst with h' | h'
    · exact h'
    · exact absurd h' (ne_of_gt hApos)
  exact Prod.ext hfst hthird

theorem torusDeriv_injective (p : ℝ × ℝ) : Function.Injective (Work.Smooth.Morse.torusDeriv p) := by
  intro a b hab
  have hzero : Work.Smooth.Morse.torusDeriv p (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  exact sub_eq_zero.mp (torusDeriv_eq_zero p (a - b) hzero)

end Work.Smooth.Morse.Immersion
