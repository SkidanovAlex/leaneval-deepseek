import Mathlib
import Submission.Work.CurveBasics.BaseChangeFunctionField
import Submission.Work.CurveBasics.BaseChange.krullDim_le_one
import Submission.Work.CurveBasics.BaseChange.isAffineOpen_bcOpens

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.CurveBasics.BaseChange

/-!
# The affine local description of a base change square

Let `C` be a curve over a field `k`, `F/k` a field extension and `f = C_F ⟶ C` the projection
of the base change.  For an affine open `W ⊆ C` the preimage `f ⁻¹ᵁ W` is affine in `C_F`
(`Work.CurveBasics.BaseChange.isAffineOpen_bcOpens`), and the square

```
Spec Γ(C_F, f⁻¹W) --Spec (f.app W)--> Spec Γ(C, W)
        |                                    |
        |                                    |
        v                                    v
      Spec F --------Spec (algebraMap k F)--> Spec k
```

is a pullback: its corners are the spectra of the rings appearing in the tensor product
description `Γ(C_F, f⁻¹W) = Γ(C,W) ⊗[k] F` of the base change.

The proof proceeds by comparing the two projections with the maps of the pullback square of
`Work.CurveBasics.BaseChange.isPullback_spec`, using that for an affine open `U` of a scheme
`X` the structure morphism `U ⟶ Spec Γ(X,U)` is `Spec` of the algebra structure map
(`Work.CurveBasics.BaseChange.fromSpec_comp_hom`) and `IsAffineOpen.SpecMap_appLE_fromSpec`.
-/

/-- For the projection `f = C_F ⟶ C` of the base change and an affine open `W ⊆ C`, the
morphism `Spec Γ(C_F, f⁻¹W) ⟶ Spec Γ(C,W)` induced by `f.app W` is, under the canonical
isomorphisms `Spec Γ(X,U) ≅ U`, the restriction `f ∣_ W` of `f` to `W`. -/
theorem isoSpec_hom_specMap_baseChangeFst {k : Type u} [Field k] {C : Work.CurveBasics.Curve k}
    (F : Type u) [Field F] [Algebra k F] (W : C.left.Opens) (hW : IsAffineOpen W) :
    (isAffineOpen_bcOpens F W hW).isoSpec.hom ≫ Spec.map ((C.baseChangeFst F).app W)
      = (C.baseChangeFst F ∣_ W) ≫ hW.isoSpec.hom := by
  have hU' : IsAffineOpen ((C.baseChangeFst F) ⁻¹ᵁ W) := isAffineOpen_bcOpens F W hW
  show hU'.isoSpec.hom ≫ Spec.map ((C.baseChangeFst F).app W)
      = (C.baseChangeFst F ∣_ W) ≫ hW.isoSpec.hom
  have h := IsAffineOpen.SpecMap_appLE_fromSpec (f := C.baseChangeFst F)
    (V := (C.baseChangeFst F) ⁻¹ᵁ W) (U := W) hW hU' le_rfl
  rw [Scheme.Hom.appLE_eq_app (f := C.baseChangeFst F) (U := W)] at h
  simp only [IsAffineOpen.fromSpec] at h
  rw [Category.assoc] at h
  rw [← morphismRestrict_ι (C.baseChangeFst F) W] at h
  have h2 : Spec.map ((C.baseChangeFst F).app W) ≫ hW.isoSpec.inv
      = hU'.isoSpec.inv ≫ (C.baseChangeFst F ∣_ W) := by
    refine (cancel_mono W.ι).mp ?_
    simpa only [Category.assoc] using h
  have h4 : Spec.map ((C.baseChangeFst F).app W)
      = (hU'.isoSpec.inv ≫ (C.baseChangeFst F ∣_ W)) ≫ hW.isoSpec.hom :=
    (Iso.comp_inv_eq _).mp h2
  rw [h4]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- For the projection `f = C_F ⟶ C` of the base change and an affine open `W ⊆ C`, the
structure morphism `Spec Γ(C_F, f⁻¹W) ⟶ Spec F` is `Spec` of the `F`-algebra structure map on
the sections `Γ(C_F, f⁻¹W)`. -/
theorem isoSpec_hom_algebraMap_baseChange {k : Type u} [Field k] {C : Work.CurveBasics.Curve k}
    (F : Type u) [Field F] [Algebra k F] (W : C.left.Opens) (hW : IsAffineOpen W) :
    (isAffineOpen_bcOpens F W hW).isoSpec.hom ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap F ((C.baseChange F).left.presheaf.obj (Opposite.op (C.bcOpens F W)))))
      = (C.bcOpens F W).ι ≫ pullback.snd C.hom (Work.CurveBasics.Curve.specMap k F) := by
  have h := fromSpec_comp_hom (C.baseChange F) (C.bcOpens F W) (isAffineOpen_bcOpens F W hW)
  rw [← h, ← Category.assoc, IsAffineOpen.isoSpec_hom_fromSpec]
  congr 1

theorem isPullback_spec_affine {k : Type u} [Field k] {C : Work.CurveBasics.Curve k} (F : Type u) [Field F]
    [Algebra k F] (W : C.left.Opens) (hW : AlgebraicGeometry.IsAffineOpen W) :
    CategoryTheory.IsPullback (AlgebraicGeometry.Spec.map ((C.baseChangeFst F).app W))
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap F ((C.baseChange F).left.presheaf.obj (Opposite.op (C.bcOpens F W))))))
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k (C.left.presheaf.obj (Opposite.op W)))))
      (Work.CurveBasics.Curve.specMap k F) := by
  refine (isPullback_spec C F W hW).of_iso' (isAffineOpen_bcOpens F W hW).isoSpec.symm
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · exact (Iso.inv_comp_eq _).mpr (isoSpec_hom_specMap_baseChangeFst (C := C) F W hW).symm
  · exact (Iso.inv_comp_eq _).mpr (isoSpec_hom_algebraMap_baseChange (C := C) F W hW).symm
  · simp
  · simp

end Work.CurveBasics.BaseChange
