import Submission.Work.Cohomology.Endgame.relMVUVQuasiIso
import Submission.Work.Cohomology.Crux.CapSub
import Submission.Work.Cohomology.exists_relComplexMap
import Submission.Work.Cohomology.Endgame.capCompare

/-!
# The cap product on the overlap, transported to the subspace `U ∩ V`

`capUvCanon` (`shiftCap.lean`) is the cap product with a relative `4`-cocycle on the *small*
chains lying in the overlap.  This file identifies it, along the isomorphism
`smallInLift U V (U ∩ V) : smallInSSet U V (U ∩ V) ≅ Sing(↥(U ∩ V))`
(`isIso_smallInLift_inter`), with the genuine cap product on the singular chains of the subspace
`U ∩ V`: the cochain is the pullback `ovlCochain X U V α` of `α` along the inclusion, and the
identity is

`capSub S 4 m α ≫ (chainComplexMap (smallInLift U V (U∩V))).f m
   = (chainComplexMap (smallInLift U V (U∩V))).f (4+m) ≫ capHom ℤ (↥(U∩V)) (ovlCochain X U V α) m`.

This is the overlap analogue of `Crux.CapSub.capSub_comp_incl`, with `S.ι` replaced by the
factorisation `S.ι = smallInLift ≫ Sing(subtypeIncl X (U∩V))` (`smallInLift_comp`); the two
scalars agree by `app_frontFace` + `genEval_dualMap`.  It is the first ingredient of the overlap
cap-map comparison (`Endgame/NOTES.md` §23).
-/

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

namespace Work.Cohomology

noncomputable section

/-- The pullback of a cochain on `X` to the overlap. -/
noncomputable def ovlCochain (X : TopCat) (U V : Set X)
    (α : Cochain ℤ (TopCat.toSSet.obj X) 4) :
    Cochain ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∩ V))) 4 :=
  α.comp (((SSet.chainComplexMap (TopCat.toSSet.map (subtypeIncl X (U ∩ V)))
      (ModuleCat.of ℤ ℤ)).f 4).hom)

/-- **The cap product on the overlap, transported by `smallInLift`.** -/
theorem capSub_smallInLift (X : TopCat) (U V : Set X)
    (α : Cochain ℤ (TopCat.toSSet.obj X) 4) (m : ℕ) :
    capSub (Y := TopCat.toSSet.obj X) (smallInSubcomplex U V (U ∩ V)) 4 m α
      ≫ (SSet.chainComplexMap (smallInLift U V (U ∩ V)) (ModuleCat.of ℤ ℤ)).f m
    = (SSet.chainComplexMap (smallInLift U V (U ∩ V)) (ModuleCat.of ℤ ℤ)).f (4 + m)
      ≫ capHom ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∩ V))) (ovlCochain X U V α) m := by
  set Y' := TopCat.toSSet.obj (TopCat.of ↥(U ∩ V)) with hY'
  set g := smallInLift U V (U ∩ V) with hg
  set S : (TopCat.toSSet.obj X).Subcomplex := smallInSubcomplex U V (U ∩ V) with hS
  have hmem : ∀ σ : (S : SSet) _⦋4 + m⦌,
      S.ι.app (Opposite.op ⦋4 + m⦌) σ
        = (TopCat.toSSet.map (subtypeIncl X (U ∩ V))).app (Opposite.op ⦋4 + m⦌)
            (g.app (Opposite.op ⦋4 + m⦌) σ) := by
    intro σ
    have h := congrArg (fun (φ : (S : SSet) ⟶ TopCat.toSSet.obj X) =>
      φ.app (Opposite.op ⦋4 + m⦌) σ) (smallInLift_comp U V (U ∩ V))
    simpa [NatTrans.comp_app, hg] using h.symm
  have hscalar : ∀ σ : (S : SSet) _⦋4 + m⦌,
      genEval ℤ (TopCat.toSSet.obj X) α
          (frontFace (TopCat.toSSet.obj X) 4 (4 + m) (Nat.le_add_right 4 m) (S.ι.app _ σ))
        = genEval ℤ Y' (ovlCochain X U V α)
          (frontFace Y' 4 (4 + m) (Nat.le_add_right 4 m) (g.app _ σ)) := by
    intro σ
    rw [hmem σ]
    rw [← app_frontFace (TopCat.toSSet.map (subtypeIncl X (U ∩ V))) (4 + m) 4
      (Nat.le_add_right 4 m) (g.app (Opposite.op ⦋4 + m⦌) σ)]
    rw [← genEval_dualMap ℤ (TopCat.toSSet.map (subtypeIncl X (U ∩ V))) α]
    rfl
  apply SSet.chainComplex_hom_ext (C := ModuleCat ℤ)
  intro σ
  have hL : (S : SSet).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ
      ≫ (capSub S 4 m α ≫ (SSet.chainComplexMap g (ModuleCat.of ℤ ℤ)).f m)
      = ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ ℤ
          (genEval ℤ (TopCat.toSSet.obj X) α
            (frontFace (TopCat.toSSet.obj X) 4 (4 + m) (Nat.le_add_right 4 m)
              (S.ι.app (Opposite.op ⦋4 + m⦌) σ))))
        ≫ Y'.ιChainComplex (R := ModuleCat.of ℤ ℤ)
            (backFace Y' 4 m (g.app (Opposite.op ⦋4 + m⦌) σ)) := by
    rw [← Category.assoc, ιChainComplex_capSub, Category.assoc]
    rw [show (S : SSet).ιChainComplex (R := ModuleCat.of ℤ ℤ)
          (backFace (S : SSet) 4 m σ)
          ≫ (SSet.chainComplexMap g (ModuleCat.of ℤ ℤ)).f m
        = Y'.ιChainComplex (R := ModuleCat.of ℤ ℤ)
            (g.app (Opposite.op ⦋m⦌) (backFace (S : SSet) 4 m σ)) from
      SSet.ι_chainComplexMap_f (X := (S : SSet)) (Y := Y') g (ModuleCat.of ℤ ℤ) _]
    rw [app_backFace]
  have hR : (S : SSet).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ
      ≫ ((SSet.chainComplexMap g (ModuleCat.of ℤ ℤ)).f (4 + m)
          ≫ capHom ℤ Y' (ovlCochain X U V α) m)
      = ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ ℤ
          (genEval ℤ Y' (ovlCochain X U V α)
            (frontFace Y' 4 (4 + m) (Nat.le_add_right 4 m)
              (g.app (Opposite.op ⦋4 + m⦌) σ))))
        ≫ Y'.ιChainComplex (R := ModuleCat.of ℤ ℤ)
            (backFace Y' 4 m (g.app (Opposite.op ⦋4 + m⦌) σ)) := by
    rw [← Category.assoc]
    rw [show (S : SSet).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ
          ≫ (SSet.chainComplexMap g (ModuleCat.of ℤ ℤ)).f (4 + m)
        = Y'.ιChainComplex (R := ModuleCat.of ℤ ℤ)
            (g.app (Opposite.op ⦋4 + m⦌) σ) from
      SSet.ι_chainComplexMap_f (X := (S : SSet)) (Y := Y') g (ModuleCat.of ℤ ℤ) _]
    rw [ιChainComplex_capHom]
  rw [hL, hR, hscalar σ]


/-- The trace of `A` on the overlap, as a subset of the subspace `U ∩ V`. -/
abbrev ovlA (X : TopCat) (A U V : Set X) : Set ↥(U ∩ V) :=
  (Subtype.val : ↥(U ∩ V) → X) ⁻¹' A

/-- **The relative cocycle of the subspace `U ∩ V` obtained by restricting `α`.**  It is the
image of `α` under the pullback `relComplexMap` of the inclusion of pairs
`(↥(U∩V), ovlA) → (X, A)`, so its underlying cochain is the pullback `ovlCochain X U V α.1`. -/
noncomputable def ovl (X : TopCat) (A U V : Set X) (α : relKern ℤ X A 4) :
    relKern ℤ (TopCat.of ↥(U ∩ V)) (ovlA X A U V) 4 :=
  relMapLM ℤ (ovlA X A U V) A (subtypeIncl X (U ∩ V)) (fun _ hx => hx) 4 α

/-- The underlying cochain of `ovl X A U V α` is the pullback `ovlCochain X U V α.1`. -/
theorem ovl_coe (X : TopCat) (A U V : Set X) (α : relKern ℤ X A 4) :
    (ovl X A U V α).1 = ovlCochain X U V α.1 := by
  rw [ovl, relMapLM_coe, dualChainMap_f_hom, chainMap_f_eq]
  rfl

/-- Element form of `capUvCanon_spec`. -/
theorem capUvCanon_spec_apply (X : TopCat) (A U V : Set X) (α : relKern ℤ X A 4) (m : ℕ)
    (y : ↑((smallInChains U V (U ∩ V)).X (4 + m))) :
    ModuleCat.Hom.hom (capUvCanon A U V α m)
        (ModuleCat.Hom.hom ((cokernel.π (subInclChain U V
          (Set.inter_subset_left : U ∩ V ∩ A ⊆ U ∩ V))).f (4 + m)) y)
      = ModuleCat.Hom.hom
          (capSub (Y := TopCat.toSSet.obj X) (smallInSubcomplex U V (U ∩ V)) 4 m α.1) y := by
  have h := congrArg (fun (g : (smallInChains U V (U ∩ V)).X (4 + m)
      ⟶ (smallInChains U V (U ∩ V)).X m) => ModuleCat.Hom.hom g y)
    (capUvCanon_spec A U V α m)
  rw [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h

/-- Element form of `capSub_smallInLift`. -/
theorem capSub_smallInLift_apply (X : TopCat) (U V : Set X)
    (α : Cochain ℤ (TopCat.toSSet.obj X) 4) (m : ℕ)
    (y : ↑((smallInChains U V (U ∩ V)).X (4 + m))) :
    ModuleCat.Hom.hom ((SSet.chainComplexMap (smallInLift U V (U ∩ V))
        (ModuleCat.of ℤ ℤ)).f m)
        (ModuleCat.Hom.hom
          (capSub (Y := TopCat.toSSet.obj X) (smallInSubcomplex U V (U ∩ V)) 4 m α) y)
      = ModuleCat.Hom.hom (capHom ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∩ V)))
          (ovlCochain X U V α) m)
          (ModuleCat.Hom.hom ((SSet.chainComplexMap (smallInLift U V (U ∩ V))
            (ModuleCat.of ℤ ℤ)).f (4 + m)) y) := by
  have h := congrArg (fun (g : (smallInChains U V (U ∩ V)).X (4 + m)
      ⟶ singChains ℤ (TopCat.of ↥(U ∩ V)) m) => ModuleCat.Hom.hom g y)
    (capSub_smallInLift X U V α m)
  rw [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h

/-- **The cap-map comparison on the overlap.**  Along the quasi-isomorphism `relMVUVPhi` of the
relative small chains of the overlap with the relative chains of the subspace `U ∩ V`, the
chain-level cap map `capUvCanon` agrees with the abstract relative cap product `relCapHalf` of
the subspace (restricting the class as `ovl`). -/
theorem exists_capUvCanon_relCapHalf (X : TopCat) (A U V : Set X) (α : relKern ℤ X A 4)
    (m : ℕ) :
    (relMVUVPhi X A U V).f (4 + m)
        ≫ (cokernelComponentIso (inclChains (TopCat.of ↥(U ∩ V)) (ovlA X A U V)) (4 + m)).hom
        ≫ relCapHalf ℤ (TopCat.of ↥(U ∩ V)) (ovlA X A U V) (ovl X A U V α) m
      = capUvCanon A U V α m
        ≫ (SSet.chainComplexMap (smallInLift U V (U ∩ V)) (ModuleCat.of ℤ ℤ)).f m := by
  haveI : Epi ((cokernel.π (subInclChain U V
      (Set.inter_subset_left : U ∩ V ∩ A ⊆ U ∩ V))).f (4 + m)) := epi_cokernel_π_f _ (4 + m)
  have hlevel : (cokernel.π (subInclChain U V
        (Set.inter_subset_left : U ∩ V ∩ A ⊆ U ∩ V))).f (4 + m) ≫ (relMVUVPhi X A U V).f (4 + m)
      = (SSet.chainComplexMap (smallInLift U V (U ∩ V)) (ModuleCat.of ℤ ℤ)).f (4 + m)
        ≫ (cokernel.π (inclChains (TopCat.of ↥(U ∩ V)) (ovlA X A U V))).f (4 + m) := by
    rw [← HomologicalComplex.comp_f, relMVUVPhi_comp, HomologicalComplex.comp_f]
  rw [← cancel_epi ((cokernel.π (subInclChain U V
    (Set.inter_subset_left : U ∩ V ∩ A ⊆ U ∩ V))).f (4 + m))]
  simp only [← Category.assoc]
  rw [hlevel]
  ext y
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  set z : ↑((singularChains ℤ (TopCat.of ↥(U ∩ V))).X (4 + m)) :=
    ModuleCat.Hom.hom ((SSet.chainComplexMap (smallInLift U V (U ∩ V)) (ModuleCat.of ℤ ℤ)).f (4 + m)) y
    with hz
  have hCIS : ModuleCat.Hom.hom (cokernelComponentIso (inclChains (TopCat.of ↥(U ∩ V))
        (ovlA X A U V)) (4 + m)).hom
        (ModuleCat.Hom.hom ((cokernel.π (inclChains (TopCat.of ↥(U ∩ V))
          (ovlA X A U V))).f (4 + m)) z)
      = ModuleCat.Hom.hom (cokernel.π ((inclChains (TopCat.of ↥(U ∩ V))
          (ovlA X A U V)).f (4 + m))) z :=
    cokernelComponentIso_canon_apply (TopCat.of ↥(U ∩ V)) (ovlA X A U V) m z
  have hCV : ModuleCat.Hom.hom (capUvCanon A U V α m)
        (ModuleCat.Hom.hom ((cokernel.π (subInclChain U V
          (Set.inter_subset_left : U ∩ V ∩ A ⊆ U ∩ V))).f (4 + m)) y)
      = ModuleCat.Hom.hom
          (capSub (Y := TopCat.toSSet.obj X) (smallInSubcomplex U V (U ∩ V)) 4 m α.1) y :=
    capUvCanon_spec_apply X A U V α m y
  have hCS : ModuleCat.Hom.hom ((SSet.chainComplexMap (smallInLift U V (U ∩ V))
        (ModuleCat.of ℤ ℤ)).f m)
        (ModuleCat.Hom.hom
          (capSub (Y := TopCat.toSSet.obj X) (smallInSubcomplex U V (U ∩ V)) 4 m α.1) y)
      = ModuleCat.Hom.hom (capHom ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∩ V)))
          (ovlCochain X U V α.1) m) z :=
    capSub_smallInLift_apply X U V α.1 m y
  have hRH : ModuleCat.Hom.hom (relCapHalf ℤ (TopCat.of ↥(U ∩ V)) (ovlA X A U V)
        (ovl X A U V α) m)
        (ModuleCat.Hom.hom ((cokernel.π ((inclChains (TopCat.of ↥(U ∩ V))
          (ovlA X A U V)).f (4 + m)))) z)
      = ModuleCat.Hom.hom (capHom ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∩ V)))
          (ovlCochain X U V α.1) m) z := by
    rw [relCapHalf_apply' (TopCat.of ↥(U ∩ V)) (ovlA X A U V) (ovl X A U V α) m z,
      ovl_coe]
  have key1 : ModuleCat.Hom.hom (relCapHalf ℤ (TopCat.of ↥(U ∩ V)) (ovlA X A U V)
        (ovl X A U V α) m)
        (ModuleCat.Hom.hom (cokernelComponentIso (inclChains (TopCat.of ↥(U ∩ V))
          (ovlA X A U V)) (4 + m)).hom
          (ModuleCat.Hom.hom ((cokernel.π (inclChains (TopCat.of ↥(U ∩ V))
            (ovlA X A U V))).f (4 + m)) z))
      = ModuleCat.Hom.hom (capHom ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∩ V)))
          (ovlCochain X U V α.1) m) z := by
    conv_lhs => rw [hCIS, hRH]
  have key2 : ModuleCat.Hom.hom ((SSet.chainComplexMap (smallInLift U V (U ∩ V))
        (ModuleCat.of ℤ ℤ)).f m)
        (ModuleCat.Hom.hom (capUvCanon A U V α m)
          (ModuleCat.Hom.hom ((cokernel.π (subInclChain U V
            (Set.inter_subset_left : U ∩ V ∩ A ⊆ U ∩ V))).f (4 + m)) y))
      = ModuleCat.Hom.hom (capHom ℤ (TopCat.toSSet.obj (TopCat.of ↥(U ∩ V)))
          (ovlCochain X U V α.1) m) z := by
    conv_lhs => rw [hCV, hCS]
  exact key1.trans key2.symm

end

end Work.Cohomology
