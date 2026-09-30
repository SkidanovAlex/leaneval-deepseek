import Mathlib
import Submission.Work.Pi6.MSS.Defs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Essential dimension of a pullback of a simplex

For a morphism `φ : ⦋n⦌ ⟶ ⦋t⦌` in the simplex category and a `t`-simplex `y` of a simplicial set
`X`, the pullback `X.map φ.op y` has essential dimension at most the number of vertices in the
image of `φ`, minus one.

The proof uses the epi–mono factorisation of `φ` (the epimorphism `factorThruImage φ` and the
monomorphism `image.ι φ`): the pullback along `φ` is a degeneracy of the pullback along the
monomorphism `image.ι φ`, whose degree is `card (range φ) - 1`, so the essential dimension (the
dimension of the nondegenerate core) is bounded by that degree.
-/

set_option autoImplicit false

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open scoped Simplicial

noncomputable section

theorem essMapLeCardImage {X : SSet.{0}} {n t : ℕ} (φ : SimplexCategory.mk n ⟶ SimplexCategory.mk t)
    (y : X.obj (Opposite.op (SimplexCategory.mk t))) :
    Work.Pi6.MSS.ess (X.map φ.op y) ≤
      (Finset.univ.image (SimplexCategory.Hom.toOrderHom φ)).card - 1 := by
  set e : ⦋n⦌ ⟶ image φ := factorThruImage φ
  set i : image φ ⟶ ⦋t⦌ := image.ι φ
  have hfac : e ≫ i = φ := image.fac φ
  -- `X.map φ.op y` is the degeneracy `X.map e.op` of the simplex `X.map i.op y`.
  have hmap : X.map φ.op y = X.map e.op (X.map i.op y) := by
    have h : X.map (e ≫ i).op y = X.map e.op (X.map i.op y) := by
      rw [op_comp, Functor.map_comp]; rfl
    rwa [hfac] at h
  -- the nondegenerate core of a degeneracy is dominated by the simplex itself
  have hle : (SSet.S.mk (X.map e.op (X.map i.op y))).toN ≤
      (SSet.S.mk (X.map i.op y)).toN := by
    rw [SSet.N.le_iff, SSet.S.subcomplex_toN, SSet.S.subcomplex_toN]
    exact SSet.S.le_def.mp (SSet.S.mk_map_le (X.map i.op y) e)
  have hdim : (SSet.S.mk (X.map e.op (X.map i.op y))).toN.dim ≤ (image φ).len :=
    le_trans (SSet.N.dim_le_of_le hle) (SSet.S.dim_toN_le _)
  -- the number of vertices in the image of `φ` is the number of vertices of `image φ`
  have hcard : (Finset.univ.image (SimplexCategory.Hom.toOrderHom φ)).card =
      (image φ).len + 1 := by
    have hcoh : SimplexCategory.Hom.toOrderHom φ =
        (SimplexCategory.Hom.toOrderHom i).comp (SimplexCategory.Hom.toOrderHom e) := by
      have h := SimplexCategory.comp_toOrderHom e i
      rwa [hfac] at h
    have he_surj : Function.Surjective (⇑(SimplexCategory.Hom.toOrderHom e)) := by
      rw [← SimplexCategory.epi_iff_surjective]; infer_instance
    have hsurj : Finset.image (⇑(SimplexCategory.Hom.toOrderHom e))
        (Finset.univ : Finset (Fin (n + 1))) = Finset.univ :=
      Finset.eq_univ_iff_forall.mpr (fun x => by
        obtain ⟨a, ha⟩ := he_surj x
        exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, ha⟩)
    have himg : (Finset.univ.image (SimplexCategory.Hom.toOrderHom φ)) =
        Finset.univ.image (SimplexCategory.Hom.toOrderHom i) := by
      rw [hcoh, OrderHom.comp_coe, Finset.image_comp, hsurj]
    rw [himg, Finset.card_image_of_injective _ (by
      rw [← SimplexCategory.mono_iff_injective]; infer_instance), Finset.card_univ,
      Fintype.card_fin]
  have hk : (Finset.univ.image (SimplexCategory.Hom.toOrderHom φ)).card - 1 = (image φ).len := by
    rw [hcard, Nat.add_sub_cancel]
  rw [ess, hmap, hk]
  exact hdim

end

end Work.Pi6.MSS
