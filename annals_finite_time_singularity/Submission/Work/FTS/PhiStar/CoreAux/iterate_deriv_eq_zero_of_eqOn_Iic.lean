import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Filter Set

namespace Work.FTS.PhiStar.CoreAux

/-- If `f` vanishes on `Iic a`, then its derivative at `a` vanishes.

`f` is constantly `0` on the half-line `Iic a`, so `f` has derivative `0` *within* `Iic a`
at `a`; since `Iic a` is a set of unique differentiability at `a`, the two-sided derivative
`deriv f a` is also `0`. -/
theorem deriv_eq_zero_of_eqOn_Iic {f : ℝ → ℝ} {a : ℝ} (h : ∀ x ≤ a, f x = 0) :
    deriv f a = 0 := by
  have hd : HasDerivWithinAt f 0 (Iic a) a :=
    HasDerivWithinAt.congr (hasDerivWithinAt_const a (Iic a) (0 : ℝ))
      (fun y hy => h y hy) (h a le_rfl)
  exact hd.deriv_eq_zero (uniqueDiffWithinAt_Iic a)

/-- If `f` vanishes on `Iic a`, then `deriv f` vanishes on all of `Iic a`.

For `x < a` the function `f` vanishes on the open neighbourhood `Iio a` of `x`, hence
`deriv f x = 0` by eventual equality with the zero function; for `x = a` this is
`deriv_eq_zero_of_eqOn_Iic`. -/
theorem deriv_eq_zero_of_eqOn_Iic' {f : ℝ → ℝ} {a : ℝ} (h : ∀ y ≤ a, f y = 0) :
    ∀ x ≤ a, deriv f x = 0 := by
  intro x hx
  rcases lt_or_eq_of_le hx with hlt | rfl
  · have hfe : f =ᶠ[nhds x] fun _ : ℝ => (0 : ℝ) := by
      filter_upwards [isOpen_Iio.mem_nhds hlt] with y hy
      exact h y (le_of_lt hy)
    simpa using Filter.EventuallyEq.deriv_eq hfe
  · exact deriv_eq_zero_of_eqOn_Iic h

theorem iterate_deriv_eq_zero_of_eqOn_Iic {g : ℝ → ℝ} {a : ℝ} (h : ∀ x ≤ a, g x = 0) (k : ℕ) :
    (deriv^[k] g) a = 0 := by
  have key : ∀ k, ∀ x ≤ a, (deriv^[k] g) x = 0 := by
    intro k
    induction k with
    | zero => intro x hx; simpa using h x hx
    | succ k ih =>
      intro x hx
      rw [Function.iterate_succ_apply']
      exact deriv_eq_zero_of_eqOn_Iic' (f := deriv^[k] g) ih x hx
  exact key k a le_rfl

end Work.FTS.PhiStar.CoreAux
