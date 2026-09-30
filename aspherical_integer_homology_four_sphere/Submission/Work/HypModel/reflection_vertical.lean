import Mathlib
import Submission.Work.HypModel.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The reflection in a "vertical" geodesic hyperplane, in upper half space coordinates

Let `v ∈ ℝ^{1,4}` be a spacelike vector whose last two coordinates agree, `v 3 = v 4`.  Since
`lorentz v v = v₀²+v₁²+v₂²+v₃²−v₄² = v₀²+v₁²+v₂² > 0`, the linear map

`lorentzReflection v = 1 − 2/⟨v,v⟩ · v ⊗ (Jv)`

is the Lorentz transformation reflecting the hyperboloid in the geodesic hyperplane
`{x : ⟨x,v⟩ = 0}`; because `v` has equal `3` and `4` coordinates, this hyperplane is *vertical*
in the upper half space model, i.e. it meets the geodesic compactification at `∞ = (0,0,0,1,1)`.

This file computes the action of this reflection on the upper half space model.  The key point is
that for a point `P` of the hyperboloid the Lorentz reflection acts by the *linear* formula

`lorentzReflection v *ᵥ P = P − (2/⟨v,v⟩ · ⟨v,P⟩) · v`

(`lorentzReflection_mulVec`), so that the coordinate difference `P₄ − P₃`, which is the reciprocal
of the height in the upper half space model, is preserved: applying the reflection contributes
`2⟨v,P⟩/⟨v,v⟩ · (v₄ − v₃) = 0` to it.  Consequently the height `q 3` is fixed, and the horizontal
coordinates undergo the Euclidean reflection in the hyperplane `{⟨x, v₀₁₂⟩ = v₃}` of `ℝ³`:

`(q₀,q₁,q₂) ↦ (q₀,q₁,q₂) − 2 (v₀q₀+v₁q₁+v₂q₂−v₃)/⟨v,v⟩ · (v₀,v₁,v₂)`.

The computation only uses `⟨v, hypOfUHS q⟩ = (v₀q₀+v₁q₁+v₂q₂−v₃)/q₃` — where the terms
`(‖q‖²±1)/(2q₃)` cancel precisely because `v₃ = v₄` — and the elementary coordinate identities
`hypOfUHS q 4 − hypOfUHS q 3 = (q 3)⁻¹` and `hypOfUHS q i = q i / q 3` for `i ≤ 2`.
-/

namespace Work.HypModel

open scoped Matrix

/-- **The Lorentz reflection is a linear reflection.**  For every vector `P ∈ ℝ^{1,4}`,

`lorentzReflection v *ᵥ P = P − 2/⟨v,v⟩ ⟨v,P⟩ · v`.

Indeed `(v ⊗ Jv) *ᵥ P = (⟨v,P⟩) • v`, because `(Jv) ⬝ P = ⟨v,P⟩` and `J = diag(1,1,1,1,−1)`. -/
private theorem lorentzReflection_mulVec (v P : V5) :
    lorentzReflection v *ᵥ P = P - (2 * (lorentz v v)⁻¹ * lorentz v P) • v := by
  ext i
  fin_cases i <;>
    simp [lorentzReflection, Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, Fin.sum_univ_five,
      J_mulVec, lorentz] <;>
    ring

/-- **The action of a vertical Lorentz reflection on the upper half space model.**
If `v 3 = v 4` and `⟨v,v⟩ > 0`, reflecting the point `q` of the upper half space (at height
`q 3 > 0`) in the geodesic hyperplane `⟨x,v⟩ = 0` keeps its height and reflects its horizontal
coordinates in the affine hyperplane `v₀x₀+v₁x₁+v₂x₂ = v₃`. -/
theorem reflection_vertical {v : V5} (hv : 0 < lorentz v v) (hv34 : v 3 = v 4) {q : E4}
    (hq : 0 < q 3) :
    mobius (lorentzReflection v) q =
      !₂[q 0 - 2 * (v 0 * q 0 + v 1 * q 1 + v 2 * q 2 - v 3) * v 0 / lorentz v v,
         q 1 - 2 * (v 0 * q 0 + v 1 * q 1 + v 2 * q 2 - v 3) * v 1 / lorentz v v,
         q 2 - 2 * (v 0 * q 0 + v 1 * q 1 + v 2 * q 2 - v 3) * v 2 / lorentz v v,
         q 3] := by
  have hLne : lorentz v v ≠ 0 := ne_of_gt hv
  have hq3 : q 3 ≠ 0 := ne_of_gt hq
  have hv43 : v 4 = v 3 := hv34.symm
  -- `⟨v, hypOfUHS q⟩`: the terms `(‖q‖²±1)/(2q₃)` cancel because `v₄ = v₃`
  have hlor : lorentz v (hypOfUHS q) =
      (v 0 * q 0 + v 1 * q 1 + v 2 * q 2 - v 3) / q 3 := by
    simp only [lorentz, hypOfUHS_apply_zero, hypOfUHS_apply_one, hypOfUHS_apply_two,
      hypOfUHS_apply_three, hypOfUHS_apply_four, hv43]
    field_simp
    ring
  -- the reflected point of the hyperboloid
  have hY : lorentzReflection v *ᵥ hypOfUHS q
      = hypOfUHS q - (2 * (lorentz v v)⁻¹ *
          ((v 0 * q 0 + v 1 * q 1 + v 2 * q 2 - v 3) / q 3)) • v := by
    rw [lorentzReflection_mulVec, hlor]
  rw [mobius, hY]
  set Y : V5 := hypOfUHS q - (2 * (lorentz v v)⁻¹ *
      ((v 0 * q 0 + v 1 * q 1 + v 2 * q 2 - v 3) / q 3)) • v with hYdef
  -- the horizontal coordinates of the reflected point
  have hY0 : Y 0 = q 0 / q 3 - 2 * (lorentz v v)⁻¹ *
      ((v 0 * q 0 + v 1 * q 1 + v 2 * q 2 - v 3) / q 3) * v 0 := by
    rw [hYdef]
    simp [Pi.sub_apply, hypOfUHS_apply_zero]
  have hY1 : Y 1 = q 1 / q 3 - 2 * (lorentz v v)⁻¹ *
      ((v 0 * q 0 + v 1 * q 1 + v 2 * q 2 - v 3) / q 3) * v 1 := by
    rw [hYdef]
    simp [Pi.sub_apply, hypOfUHS_apply_one]
  have hY2 : Y 2 = q 2 / q 3 - 2 * (lorentz v v)⁻¹ *
      ((v 0 * q 0 + v 1 * q 1 + v 2 * q 2 - v 3) / q 3) * v 2 := by
    rw [hYdef]
    simp [Pi.sub_apply, hypOfUHS_apply_two]
  -- the height of the reflected point, which is again `q 3`
  have hkey : Y 4 - Y 3 = (q 3)⁻¹ := by
    rw [hYdef]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hypOfUHS_apply_three,
      hypOfUHS_apply_four, hv43]
    field_simp
    ring
  ext i
  fin_cases i
  · simp [uhsOfHyp, hkey, hY0, inv_inv]
    field_simp
  · simp [uhsOfHyp, hkey, hY1, inv_inv]
    field_simp
  · simp [uhsOfHyp, hkey, hY2, inv_inv]
    field_simp
  · simp [uhsOfHyp, hkey, inv_inv]

end Work.HypModel
