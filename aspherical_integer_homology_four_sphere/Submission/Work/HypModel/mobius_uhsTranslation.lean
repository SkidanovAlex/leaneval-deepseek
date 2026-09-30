import Mathlib
import Submission.Work.HypModel.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The horospherical translation `x ↦ x + b` in the upper half space model

The matrix `uhsTranslation b : Matrix (Fin 5) (Fin 5) ℝ` fixes the null vector `infty` and
implements, on the upper half space model, the horospherical translation of the horizontal
coordinates:

```
(x, s) ↦ (x + b, s),      i.e. on `E4`:  q ↦ (q₀ + b₀, q₁ + b₁, q₂ + b₂, q₃).
```

Of the four coordinates of `b` only the first three are used: `uhsTranslation b` is the Lorentz
transformation of `(x,s) ↦ (x + b, s)`, and the hyperbolic metric `(|dx|² + ds²)/s²` clearly
depends only on `b₀, b₁, b₂`.

The computation is elementary.  Writing `P := hypotUHS q` and `A := uhsTranslation b`, the first
three rows of `A` send `P` to
`(qᵢ + bᵢ)/q₃` (`i = 0,1,2`), because only the combination `Aᵢ₃ P₃ + Aᵢ₄ P₄` involves `b`, and there
`P₄ − P₃ = 1/q₃`.  The last two rows give

```
(A P)₃ = (2⟨b, q⟩ + ‖q‖² − 1 + B)/(2q₃),   (A P)₄ = (2⟨b, q⟩ + ‖q‖² + 1 + B)/(2q₃),
```

with `B = b₀² + b₁² + b₂²` and `⟨b, q⟩ = b₀q₀ + b₁q₁ + b₂q₂`, so that their difference is
`(A P)₄ − (A P)₃ = 1/q₃`.  Since `uhsOfHyp` divides the first three coordinates of its argument by
`P₄ − P₃` and returns `(P₄ − P₃)⁻¹` as its fourth coordinate, the result is
`(q₀ + b₀, q₁ + b₁, q₂ + b₂, q₃)`.
-/

noncomputable section

namespace Work.HypModel

open scoped Matrix InnerProductSpace
open Matrix

/-- `EuclideanSpace.norm_sq_eq` expanded in the four coordinates of `E4`. -/
theorem norm_sq_E4_expand (q : E4) : ‖q‖ ^ 2 = q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 + q 3 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_four]
  simp [Real.norm_eq_abs, sq_abs]

/-- First coordinate of `uhsTranslation b *ᵥ hypOfUHS q`. -/
theorem uhsTranslation_mulVec_hypOfUHS_zero (b q : E4) :
    (uhsTranslation b *ᵥ hypOfUHS q) 0 = (q 0 + b 0) / q 3 := by
  have hq' := norm_sq_E4_expand q
  simp [uhsTranslation, Matrix.mulVec, dotProduct, Fin.sum_univ_five, hq']
  ring

/-- Second coordinate of `uhsTranslation b *ᵥ hypOfUHS q`. -/
theorem uhsTranslation_mulVec_hypOfUHS_one (b q : E4) :
    (uhsTranslation b *ᵥ hypOfUHS q) 1 = (q 1 + b 1) / q 3 := by
  have hq' := norm_sq_E4_expand q
  simp [uhsTranslation, Matrix.mulVec, dotProduct, Fin.sum_univ_five, hq']
  ring

/-- Third coordinate of `uhsTranslation b *ᵥ hypOfUHS q`. -/
theorem uhsTranslation_mulVec_hypOfUHS_two (b q : E4) :
    (uhsTranslation b *ᵥ hypOfUHS q) 2 = (q 2 + b 2) / q 3 := by
  have hq' := norm_sq_E4_expand q
  simp [uhsTranslation, Matrix.mulVec, dotProduct, Fin.sum_univ_five, hq']
  ring

/-- The relevant coordinate difference of `uhsTranslation b *ᵥ hypOfUHS q`: it is the reciprocal
height `(q 3)⁻¹`.  This is what makes `uhsOfHyp` return the translated point. -/
theorem uhsTranslation_mulVec_hypOfUHS_sub (b q : E4) :
    (uhsTranslation b *ᵥ hypOfUHS q) 4 - (uhsTranslation b *ᵥ hypOfUHS q) 3 = (q 3)⁻¹ := by
  have hq' := norm_sq_E4_expand q
  simp [uhsTranslation, Matrix.mulVec, dotProduct, Fin.sum_univ_five, hq']
  ring

/-- **The horospherical translation `x ↦ x + b` acts on the upper half space model by adding `b`
to the horizontal coordinates.**  Only the first three coordinates of `b` occur, as in the
definition of `uhsTranslation`; the height `q 3` is fixed. -/
theorem mobius_uhsTranslation (b : E4) {q : E4} (hq : 0 < q 3) :
    mobius (uhsTranslation b) q = !₂[q 0 + b 0, q 1 + b 1, q 2 + b 2, q 3] := by
  have hq3 : q 3 ≠ 0 := ne_of_gt hq
  rw [← (WithLp.ofLp_injective 2).eq_iff]
  funext i
  fin_cases i
  · simp [mobius, uhsOfHyp_apply_zero, uhsTranslation_mulVec_hypOfUHS_zero,
      uhsTranslation_mulVec_hypOfUHS_sub, hq3]
  · simp [mobius, uhsOfHyp_apply_one, uhsTranslation_mulVec_hypOfUHS_one,
      uhsTranslation_mulVec_hypOfUHS_sub, hq3]
  · simp [mobius, uhsOfHyp_apply_two, uhsTranslation_mulVec_hypOfUHS_two,
      uhsTranslation_mulVec_hypOfUHS_sub, hq3]
  · simp [mobius, uhsOfHyp_apply_three, uhsTranslation_mulVec_hypOfUHS_sub]

end Work.HypModel
