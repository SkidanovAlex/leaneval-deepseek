import Mathlib
import Submission.Work.REFL.Basic

/-!
# AREA REFL — the component description of `pre oneMinusShift` on points

This file proves `Work.REFL.pre_app_points`, the statement that the endomorphism
`preShift M = pre oneMinusShift` of `ihomP M` is, on `S`-points, given by precomposition of
the corresponding morphism `P ⊗ ℤ[S] ⟶ M` with `testMap S = (1 - S) ⊗ id_{ℤ[S]}`:

`(preShift M).app S = (ihomPPoints M S).symm ∘ (testMap S ≫ -) ∘ (ihomPPoints M S)`.

The proof is the general (two-variable) statement `ihomPoints_pre`, which is the analogue of
Mathlib's `LightCondensed.ihom_map_val_app` for the *contravariant* variable of the internal
hom: for `f : B ⟶ A`, precomposition of an internal-hom point with `f` on the tensor factor
corresponds to `pre f` on the internal hom.  It follows from
`MonoidalClosed.curry_pre_app` together with the naturality of `GrothendieckTopology.yonedaEquiv`
and of the free-forget adjunction.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed

noncomputable section

namespace Work.REFL

open _root_.LightCondensed _root_.LightCondensed.Solid

/-
**The points description of `pre f` on the internal hom.**

For `f : B ⟶ A` and an `S`-point `x` of the internal hom `A ⟹ M`, the `S`-point
`(pre f).app M x` of `B ⟹ M` is obtained by precomposing the corresponding morphism
`A ⊗ ℤ[S] ⟶ M` with `f ▷ ℤ[S]`.

This is the analogue of `LightCondensed.ihom_map_val_app` (which treats `(ihom A).map`)
for the contravariant variable of `ihom`.  Proof: apply the injectivity of `ihomPoints` on
`B`, unfold `ihomPoints` by `rfl` (`ihomPoints_apply`) to an `uncurry`, move
`MonoidalClosed.uncurry_pre_app` and `MonoidalClosed.curry_pre_app` across the `uncurry`,
use the naturality of the free-forget adjunction bijection and of `yonedaEquiv`, and finally
identify `(forget R).map` with the underlying morphism of presheaves, which is `rfl`
(`LightCondensed.forget_map_hom_app_hom_apply`).
-/
set_option backward.isDefEq.respectTransparency false in
lemma ihomPoints_pre (R : Type) [CommRing R] (A B M : LightCondMod R) (f : B ⟶ A)
    (S : LightProfinite)
    (x : (((ihom A).obj M).obj.obj (Opposite.op S))) :
    (((pre f).app M).hom.app (Opposite.op S)) x =
      (ihomPoints R B M S).symm (f ▷ ((free R).obj S.toCondensed) ≫ ihomPoints R A M S x) := by
  rw [Equiv.eq_symm_apply]
  simp only [ihomPoints_apply]
  rw [← MonoidalClosed.uncurry_pre_app]
  congr 1
  rw [← Adjunction.homEquiv_naturality_right_symm]
  congr 1
  rw [Equiv.symm_apply_eq, GrothendieckTopology.yonedaEquiv_comp, Equiv.apply_symm_apply]
  exact (LightCondensed.forget_map_hom_app_hom_apply R _ (Opposite.op S) x).symm

/-- **The component description of `pre oneMinusShift` on `S`-points.**  Specialisation of
`ihomPoints_pre` to `A = B = P`, `f = oneMinusShift`: since `preShift M` is an endomorphism
of `ihomP M`, the corresponding operation on morphisms `P ⊗ ℤ[S] ⟶ M` is precomposition with
`testMap S = oneMinusShift ▷ ℤ[S]`. -/
theorem pre_app_points : Work.REFL.PrePointsStatement := by
  intro M S x
  exact ihomPoints_pre ℤ P P M oneMinusShift S x

end Work.REFL
