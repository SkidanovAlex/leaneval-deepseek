import Mathlib

namespace Work.RPB.B5

theorem deriv_comp_sqrt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (ρ : ℝ → ℝ) (x : ℝ) (hx : ρ x ≠ 0)
    (hf : DifferentiableAt ℝ f (Real.sqrt (ρ x))) (hρ : DifferentiableAt ℝ ρ x) :
    deriv (fun y : ℝ => f (Real.sqrt (ρ y))) x
      = deriv (fun y : ℝ => Real.sqrt (ρ y)) x • deriv f (Real.sqrt (ρ x)) := by
  have hg : HasDerivAt (fun y : ℝ => Real.sqrt (ρ y))
      (deriv ρ x / (2 * Real.sqrt (ρ x))) x :=
    hρ.hasDerivAt.sqrt hx
  have hcomp : HasDerivAt (fun y : ℝ => f (Real.sqrt (ρ y)))
      (fderiv ℝ f (Real.sqrt (ρ x)) (deriv ρ x / (2 * Real.sqrt (ρ x)))) x :=
    hf.hasFDerivAt.comp_hasDerivAt x hg
  rw [hcomp.deriv, hg.deriv, fderiv_eq_smul_deriv]

end Work.RPB.B5
