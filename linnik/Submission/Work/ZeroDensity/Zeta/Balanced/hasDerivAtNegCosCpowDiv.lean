import Mathlib

namespace Work.ZeroDensity.Zeta.Balanced

open Complex

theorem hasDerivAtNegCosCpowDiv (s : ℂ) (a : ℝ) (ha : a ≠ 0) {x : ℝ} (hx : 0 < x) :
    HasDerivAt
      (fun u : ℝ => -(((Real.cos (a * u) : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)) / (a : ℂ))
      (((Real.sin (a * x) : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)
        + (s + 1) / (a : ℂ) * (((Real.cos (a * x) : ℝ) : ℂ) * (x : ℂ) ^ (-s - 2))) x := by
  have hA : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  -- `x` is a positive real, hence lies in the slit plane, so `z ↦ z ^ c` is complex differentiable
  -- at `(x : ℂ)`.
  have hslit : ((x : ℂ)) ∈ Complex.slitPlane := by
    left; simpa using hx
  -- Derivative of `u ↦ (u : ℂ) ^ (-s - 1)` along the real axis.
  have hpow : HasDerivAt (fun u : ℝ => (u : ℂ) ^ (-s - 1))
      ((-s - 1) * (x : ℂ) ^ ((-s - 1) - 1)) x :=
    (Complex.hasStrictDerivAt_cpow_const (c := -s - 1) (x := (x : ℂ)) hslit).hasDerivAt.comp_ofReal
  -- Derivative of `u ↦ (Real.cos (a * u) : ℂ)`.
  have hcos : HasDerivAt (fun u : ℝ => ((Real.cos (a * u) : ℝ) : ℂ))
      (-(((Real.sin (a * x) : ℝ) : ℂ) * (a : ℂ))) x := by
    have h1 := (Real.hasDerivAt_cos (a * x)).comp x (hasDerivAt_const_mul (x := x) a)
    have h2 := h1.ofReal_comp
    simpa using h2
  -- Product rule, then the outer negation and division by `a`.
  have hprod := hcos.mul hpow
  have hfin := (hprod.neg).div_const (a : ℂ)
  refine hfin.congr_deriv ?_
  rw [show (-s - 1 : ℂ) - 1 = -s - 2 by ring]
  field_simp
  ring

end Work.ZeroDensity.Zeta.Balanced
