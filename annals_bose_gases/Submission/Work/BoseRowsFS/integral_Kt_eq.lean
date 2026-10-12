import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseRowsFS.KernelDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsFS.integral_Kt_eq` — the time-integral of the heat kernel

`Kt s z = (4πs)^{-3/2} e^{-‖z‖²/(4s)}` is the heat kernel of `∂_s = Δ` on `ℝ³`.  The heat
kernel is the kernel of `e^{sΔ}`, so its integral in the time variable `s` is the kernel of
`(-Δ)^{-1}`, i.e. the fundamental-solution (Newtonian) kernel of `-Δ` in three dimensions:

  `∫_{s>0} Kt s z ds = 1/(4π‖z‖)`   for `z ≠ 0`.

The analytic content of this identity is the Laplace-type integral

  `∫_0^∞ (4πs)^{-3/2} e^{-a²/(4s)} ds = 1/(4πa)`  (`a > 0`),

which the shared library already contains as
`Commons.Analysis.Integral.integral_heat_coulomb_three`: the substitution `s ↦ 1/s` turns it
into the Euler integral `∫_0^∞ y^{-1/2} e^{-a y} dy = a^{-1/2}Γ(1/2) = √(π/a)`, and the constant
`(4π)^{-3/2}√π = 1/(8π)` normalises it.  With `a = ‖z‖` the integrand of that lemma *is*
`Kt · z`, the only difference being that `Kt` writes the exponent as `-‖z‖²/(4s)` rather than
`-(‖z‖²/(4s))`.  The present lemma is the bookkeeping which states the result in the
`BoseRowsFS` vocabulary.
-/

noncomputable section

open MeasureTheory Set
open scoped Real BigOperators

namespace Work.BoseRowsFS

set_option autoImplicit false

/-- `Kt · z` is, pointwise on `(0,∞)`, the integrand of
`Commons.Analysis.Integral.integral_heat_coulomb_three` at `a = ‖z‖`
(the exponent `-‖z‖²/(4s)` and `-(‖z‖²/(4s))` agree). -/
lemma integral_Kt_eq_aux (z : EuclideanSpace ℝ (Fin 3)) :
    (∫ s in Set.Ioi (0 : ℝ), Kt s z)
      = ∫ s in Set.Ioi (0 : ℝ), (4 * Real.pi * s) ^ (-(3 / 2 : ℝ))
          * Real.exp (-(‖z‖ ^ 2 / (4 * s))) := by
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s _
  simp only [Kt, neg_div]

/-- **The `s`-integral of the three-dimensional heat kernel** is the Newtonian kernel: for
`z ≠ 0`, `∫_{s>0} Kt s z ds = 1/(4π‖z‖)`. -/
theorem integral_Kt_eq (z : EuclideanSpace ℝ (Fin 3)) (hz : z ≠ 0) :
    (∫ s in Set.Ioi (0 : ℝ), Work.BoseRowsFS.Kt s z) = 1 / (4 * Real.pi * ‖z‖) := by
  rw [integral_Kt_eq_aux z]
  exact Commons.Analysis.Integral.integral_heat_coulomb_three (a := ‖z‖) (norm_pos_iff.mpr hz)

end Work.BoseRowsFS
