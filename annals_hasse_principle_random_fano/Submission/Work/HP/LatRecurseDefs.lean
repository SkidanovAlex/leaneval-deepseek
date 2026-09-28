import Mathlib

/-!
# Auxiliary definitions for `Work.HP.lat_recurse`

The orthogonal projection onto the orthogonal complement of the line spanned by a vector `x`.
It is used to peel off a shortest lattice vector from a coefficient lattice.
-/

set_option autoImplicit false

noncomputable section

namespace Work.HP

/-- The orthogonal projection of `E` onto the orthogonal complement of `ℝ x`, written in closed
form:  `projPerp x y = y - (‖x‖ ^ 2)⁻¹ • (⟪x, y⟫_ℝ • x)`. -/
def projPerp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x : E) : E →ₗ[ℝ] E :=
  (ContinuousLinearMap.id ℝ E -
    (‖x‖ ^ 2)⁻¹ • ContinuousLinearMap.smulRight (innerSL ℝ x) x : E →L[ℝ] E)

end Work.HP

namespace Work.HP

/-- The second coordinate of the `ℤ`-basis decomposition attached to a bijective decomposition map
`(a, w) ↦ a • u + ∑ i, w i • v i`.  This is the `ℤ`-linear "quotient coordinate" of `ℤ^R` onto
`ℤ^{R-1}` with kernel `ℤ u`. -/
noncomputable def coord2 {R : ℕ} {u : Fin R → ℤ} {v : Fin (R - 1) → (Fin R → ℤ)}
    (hbij : Function.Bijective (fun c : ℤ × (Fin (R - 1) → ℤ) =>
      c.1 • u + ∑ i, c.2 i • v i)) :
    (Fin R → ℤ) → (Fin (R - 1) → ℤ) :=
  fun y => ((Equiv.ofBijective (fun c : ℤ × (Fin (R - 1) → ℤ) =>
    c.1 • u + ∑ i, c.2 i • v i) hbij).symm y).2

end Work.HP
