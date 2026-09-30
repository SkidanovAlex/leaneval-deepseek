import Mathlib
import Submission.Work.SSS.serreE1PieceDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The second isomorphism theorem for the singular chains of a simplicial set

For subcomplexes `A`, `M` of a simplicial set `Z` the quotient of the chains on `M` by the chains on
`A ⊓ M` is isomorphic to the quotient of the chains on `A ⊔ M` by the chains on `A`.

The proof goes through the pushout square

```
A ⊓ M → M
  ↓      ↓
  A  → A ⊔ M
```

of subcomplexes.  Applying the singular chain functor degreewise (which is the free-module functor
on the set `Z _⦋n⦌`, hence preserves colimits) gives a pushout square of chain complexes, whose
horizontal cokernels are therefore isomorphic.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

noncomputable section

/-! ## A colimit is transported along an isomorphism of diagrams -/

/-- If `c` is a colimit cocone for a diagram `F` and `e : F ≅ G`, then the cocone over `G` obtained
by precomposing with `e.inv` is a colimit. -/
noncomputable def isColimit_of_diagramIso {J : Type*} [Category J] {C : Type*} [Category C]
    {F G : J ⥤ C} (e : F ≅ G) {c : Cocone F} (hc : IsColimit c) :
    IsColimit (Cocone.mk c.pt (e.inv ≫ c.ι)) := by
  refine IsColimit.mk (fun t => hc.desc (Cocone.mk t.pt (e.hom ≫ t.ι))) ?_ ?_
  · intro t j
    dsimp only
    rw [NatTrans.comp_app, Category.assoc, IsColimit.fac hc (Cocone.mk t.pt (e.hom ≫ t.ι)) j,
      NatTrans.comp_app, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  · intro t m hm
    refine hc.uniq (Cocone.mk t.pt (e.hom ≫ t.ι)) m ?_
    intro j
    have h := congrArg (fun x => e.hom.app j ≫ x) (hm j)
    simp only [NatTrans.comp_app, Category.assoc] at h ⊢
    rw [Iso.hom_inv_id_app_assoc] at h
    exact h

/-! ## The pushout square, degreewise -/

/-- The square of `n`-chains induced by the lattice square `A ⊓ M → M`, `A → A ⊔ M` is a pushout:
degreewise it is the free module on the bicartesian square of sets
`Z_n ∩ A_n ∩ M_n → A_n`, `M_n → A_n ∪ M_n`. -/
lemma isPushout_level (Z : SSet.{0}) (A M : Z.Subcomplex) (n : ℕ) :
    IsPushout ((sCCMap (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ M ≤ M))).f n)
      ((sCCMap (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ M ≤ A))).f n)
      ((sCCMap (SSet.Subcomplex.homOfLE (le_sup_right : M ≤ A ⊔ M))).f n)
      ((sCCMap (SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ M))).f n) := by
  have hb : Lattice.BicartSq ((A ⊓ M).obj (op ⦋n⦌)) (M.obj (op ⦋n⦌)) (A.obj (op ⦋n⦌))
      ((A ⊔ M).obj (op ⦋n⦌)) :=
    Lattice.BicartSq.mk (by simp [Set.union_comm]) (by simp [Set.inter_comm])
  exact CategoryTheory.Functor.map_isPushout
    (CategoryTheory.Limits.sigmaConst.obj (ModuleCat.of ℤ ℤ))
    (CategoryTheory.Limits.Types.isPushout_of_bicartSq hb)

/-- The lattice square of subcomplexes is a pushout square of chain complexes. -/
lemma isPushout_sCC (Z : SSet.{0}) (A M : Z.Subcomplex) :
    IsPushout (sCCMap (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ M ≤ M)))
      (sCCMap (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ M ≤ A)))
      (sCCMap (SSet.Subcomplex.homOfLE (le_sup_right : M ≤ A ⊔ M)))
      (sCCMap (SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ M))) := by
  have w : sCCMap (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ M ≤ M)) ≫
        sCCMap (SSet.Subcomplex.homOfLE (le_sup_right : M ≤ A ⊔ M)) =
      sCCMap (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ M ≤ A)) ≫
        sCCMap (SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ M)) := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      SSet.Subcomplex.homOfLE_comp, SSet.Subcomplex.homOfLE_comp]
  refine CategoryTheory.IsPushout.of_isColimit (c := PushoutCocone.mk _ _ w) ?_
  apply HomologicalComplex.isColimitOfEval
  intro n
  refine IsColimit.ofIsoColimit
    (isColimit_of_diagramIso
      (CategoryTheory.Limits.spanCompIso
        (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n) _ _).symm
      (isPushout_level Z A M n).isColimit)
    (Cocone.ext (Iso.refl _) ?_)
  intro j
  cases j with
  | none => rfl
  | some v =>
    cases v with
    | left =>
      have h1 : ((isPushout_level Z A M n).cocone).ι.app WalkingSpan.left =
          (sCCMap (SSet.Subcomplex.homOfLE (le_sup_right : M ≤ A ⊔ M))).f n := by
        rw [CategoryTheory.Limits.PushoutCocone.ι_app_left]
        rfl
      simp only [Category.comp_id, NatTrans.comp_app, Iso.symm_inv,
        CategoryTheory.Limits.spanCompIso_hom_app_left, Category.id_comp,
        CategoryTheory.Functor.mapCocone_ι_app, HomologicalComplex.eval_map,
        CategoryTheory.Limits.PushoutCocone.ι_app_left, Iso.refl_hom,
        CategoryTheory.Limits.PushoutCocone.mk_inl, CategoryTheory.IsPushout.cocone]
      exact h1
    | right =>
      have h1 : ((isPushout_level Z A M n).cocone).ι.app WalkingSpan.right =
          (sCCMap (SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ M))).f n := by
        rw [CategoryTheory.Limits.PushoutCocone.ι_app_right]
        rfl
      simp only [Category.comp_id, NatTrans.comp_app, Iso.symm_inv,
        CategoryTheory.Limits.spanCompIso_hom_app_right, Category.id_comp,
        CategoryTheory.Functor.mapCocone_ι_app, HomologicalComplex.eval_map,
        CategoryTheory.Limits.PushoutCocone.ι_app_right, Iso.refl_hom,
        CategoryTheory.Limits.PushoutCocone.mk_inr, CategoryTheory.IsPushout.cocone]
      exact h1

/-- **Second isomorphism theorem for the singular chains of a simplicial set.**  For subcomplexes
`A`, `M` of a simplicial set `Z`, the quotient `C(M)/C(A ⊓ M)` of the chains on `M` by those on the
intersection is naturally isomorphic to the quotient `C(A ⊔ M)/C(A)`.  (Both are canonically
`(C(A) + C(M))/C(A)`.) -/
theorem coker_inf_sup_iso_chain (Z : SSet.{0}) (A M : Z.Subcomplex) :
    Nonempty (CategoryTheory.Limits.cokernel
        (sCCMap (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ M ≤ M))) ≅
      CategoryTheory.Limits.cokernel
        (sCCMap (SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ M)))) := by
  letI : IsIso (CategoryTheory.Limits.cokernel.map
      (sCCMap (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ M ≤ M)))
      (sCCMap (SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ M)))
      (sCCMap (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ M ≤ A)))
      (sCCMap (SSet.Subcomplex.homOfLE (le_sup_right : M ≤ A ⊔ M)))
      (isPushout_sCC Z A M).w) :=
    CategoryTheory.Limits.isIso_cokernel_map_of_isPushout (isPushout_sCC Z A M)
  refine ⟨asIso (CategoryTheory.Limits.cokernel.map
      (sCCMap (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ M ≤ M)))
      (sCCMap (SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ M)))
      (sCCMap (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ M ≤ A)))
      (sCCMap (SSet.Subcomplex.homOfLE (le_sup_right : M ≤ A ⊔ M)))
      (isPushout_sCC Z A M).w)⟩

end

end Work.SSS
