import Mathlib
import Submission.Work.RPA3.follow_family_defs

namespace Work.RPA3

/-- The three slice derivatives `∂_xℓ`, `∂_tℓ`, `∂_τℓ` are `2π`-periodic in the angle `t`.

`Tk 1` is the translation by the constant `c = ((0,2π),(0,0))` in `PS`, so by `LagFamilyAll.per`
the family satisfies `ℓ τ y (s+2π) = ℓ τ y s + c`.  Shifting the *values* by a constant does not
change a derivative, which handles `dX` and `dTau` directly; for `dT` the shift is also the point
at which the derivative is taken, so one first changes variables
(`deriv_comp_add_const`) and then again applies `deriv_add_const`. -/
theorem sliceDeriv_periodic (L : Work.RPA3.LagFamilyAll) (τ x t : ℝ) :
    Work.RPA3.dX L τ x (t + 2 * Real.pi) = Work.RPA3.dX L τ x t ∧
    Work.RPA3.dT L τ x (t + 2 * Real.pi) = Work.RPA3.dT L τ x t ∧
    Work.RPA3.dTau L τ x (t + 2 * Real.pi) = Work.RPA3.dTau L τ x t := by
  -- `Tk 1` is the translation by `c = ((0,2π),(0,0))`.
  have hper : ∀ σ y s : ℝ,
      L.ℓ σ (y, s + 2 * Real.pi) = L.ℓ σ (y, s) + ((0, 2 * Real.pi), (0, 0)) := by
    intro σ y s
    rw [L.per σ y s]
    ext <;> simp [Tk]
  refine ⟨?_, ?_, ?_⟩
  · -- the `x`-slice: the shifted curve is the original one translated by the constant `c`.
    simp only [dX]
    rw [show (fun y => L.ℓ τ (y, t + 2 * Real.pi))
          = (fun y => L.ℓ τ (y, t) + ((0, 2 * Real.pi), (0, 0))) from
            funext (fun y => hper τ y t),
        deriv_add_const]
  · -- the `t`-slice: shift the point of differentiation, then translate the values.
    simp only [dT]
    rw [← deriv_comp_add_const (fun s => L.ℓ τ (x, s)) (2 * Real.pi) t]
    rw [show (fun y => L.ℓ τ (x, y + 2 * Real.pi))
          = (fun y => L.ℓ τ (x, y) + ((0, 2 * Real.pi), (0, 0))) from
            funext (fun y => hper τ x y),
        deriv_add_const]
  · -- the `τ`-slice: again only the values are translated.
    simp only [dTau]
    rw [show (fun σ => L.ℓ σ (x, t + 2 * Real.pi))
          = (fun σ => L.ℓ σ (x, t) + ((0, 2 * Real.pi), (0, 0))) from
            funext (fun σ => hper σ x t),
        deriv_add_const]

end Work.RPA3
