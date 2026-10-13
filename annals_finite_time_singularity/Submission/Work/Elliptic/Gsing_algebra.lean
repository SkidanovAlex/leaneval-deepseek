import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Elliptic.GsingFuncs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic

/-- The algebraic identity solved by the singular term `G = Gstar + Gbar`:
`α²z²(Gstar + Gbar)'' + α(5+α)z(Gstar + Gbar)' = (15/4) F_*`.

Written out, `DDGstar`, `DDGbar` are the explicit second derivatives and `DGstar`,
`DGbar` the explicit first derivatives of `Gstar`, `Gbar` (`Work.Elliptic.GsingFuncs`).
The `Gstar`-part contributes `(3αz/4)·(F_*)'(z) + (15/4) F_*(z)` and the `Gbar`-part
contributes `-(3αz/4)·(F_*)'(z)`; the cancellation of the `(F_*)'`-terms and of the
homogeneous `J`-terms is exactly the content of the identity. -/
theorem Gsing_algebra (α : ℝ) (F : ℝ → ℝ → ℝ) (z : ℝ) (hα : 0 < α) (hz : 0 < z) :
    α ^ 2 * z ^ 2 * (DDGstar α F z + DDGbar α F z)
      + α * (5 + α) * z * (DGstar α F z + DGbar α F z)
      = (15 / 4) * Fstar F z := by
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hα0 : α ≠ 0 := ne_of_gt hα
  -- `A := z ^ (-(5/α))` is the homogeneous factor of `Gbar`; it is nonzero.
  have hApos : 0 < z ^ (-(5 / α)) := Real.rpow_pos_of_pos hz _
  have hAne : z ^ (-(5 / α)) ≠ 0 := ne_of_gt hApos
  -- Reduction of all the `z`-powers occurring in the definitions to `A` and `z⁻¹`.
  have hp1 : z ^ (-(5 / α) - 1) = z ^ (-(5 / α)) * z⁻¹ := by
    rw [show -(5 / α) - 1 = -(5 / α) + (-1) by ring, Real.rpow_add hz, Real.rpow_neg_one]
  have hp2 : z ^ (-(5 / α) - 1 - 1) = z ^ (-(5 / α)) * z⁻¹ * z⁻¹ := by
    rw [show -(5 / α) - 1 - 1 = -(5 / α) + (-1) + (-1) by ring,
      Real.rpow_add hz, Real.rpow_add hz, Real.rpow_neg_one]
  have hpt : z ^ ((5 - α) / α) = z⁻¹ / z ^ (-(5 / α)) := by
    rw [eq_div_iff hAne, ← Real.rpow_add hz,
      show (5 - α) / α + -(5 / α) = -1 by field_simp; ring, Real.rpow_neg_one]
  have hpu : z ^ ((5 - α) / α - 1) = (z⁻¹ / z ^ (-(5 / α))) * z⁻¹ := by
    rw [show (5 - α) / α - 1 = (5 - α) / α + (-1) by ring, Real.rpow_add hz, hpt,
      Real.rpow_neg_one]
  unfold DDGstar DDGbar DGstar DGbar Abar DAbar DDAbar
  rw [hp1, hp2, hpt, hpu]
  field_simp
  ring

end Work.Elliptic
