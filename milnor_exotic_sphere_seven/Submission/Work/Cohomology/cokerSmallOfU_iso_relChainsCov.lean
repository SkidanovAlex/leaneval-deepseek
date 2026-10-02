import Mathlib
import Submission.Work.Cohomology.MVSequence
import Submission.Work.Cohomology.mvCochainDefs
import Submission.Work.Cohomology.SmallSES
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.cokerSmallAux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The cokernel of `smallOfU` is the relative chain complex of the second cover element

For a topological space `X` and subsets `A, V ⊆ X`, the cokernel of the Mayer–Vietoris map
`smallOfU A V : C_*(A) ⟶ C^{A,V}_*(X)` (chains of `A` into the small chains of the cover
`{A, V}`) is the relative chain complex

`C_*(V) / C_*(A ∩ V) = C_*(V, A ∩ V)`,

the singular chains of the pair `(V, A ∩ V)`.

The proof is categorical and does not use any hypothesis on `A, V`:

* the legs of the Mayer–Vietoris square
  `C_*(A ∩ V) ⟶ C_*(A)`, `C_*(A ∩ V) ⟶ C_*(V)`, `C_*(A) ⟶ C^{A,V}_*(X)`,
  `C_*(V) ⟶ C^{A,V}_*(X)` make it a **pushout** (this is exactly the short exactness of the
  Mayer–Vietoris sequence, `Work.Cohomology.mv_shortExact`), and
* for a pushout square `B ⟶ C`, `B ⟶ D`, `C ⟶ E`, `D ⟶ E` in an abelian category,
  `coker (C ⟶ E) ≅ coker (B ⟶ D)`

(`cokernel_iso_of_isPushout`).  Finally `C_*(A ∩ V) ≅ C_*(V ∩ A)` — the two descriptions of the
overlap as a subset of `X` and as a subset of `V` — intertwines the two inclusions into `C_*(V)`.

## Main results

* `cokernel_iso_of_isPushout` — the cokernel of one leg of a pushout square;
* `mv_isPushout` — the small-chains (Mayer–Vietoris) square is a pushout;
* `overlapTopIso`, `overlapChainsIso` — the identification of the two models of the overlap;
* `cokerSmallOfU_iso_relChainsCov` — the statement of the problem.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

/-! ## Cokernels of the legs of a pushout square -/

/-- **The cokernel of a leg of a pushout square.**  In an abelian category, if

```
B --f--> C
|        |
g        h
v        v
D --k--> E
```

is a pushout square, then `coker h ≅ coker g`.  More precisely there is an isomorphism
`coker g ≅ coker h` which is compatible with the cokernel projections:
`cokernel.π g ≫ e.hom = k ≫ cokernel.π h`. -/
theorem cokernel_iso_of_isPushout {C : Type*} [Category C] [Abelian C]
    {W X Y Z : C} (f : W ⟶ X) (g : W ⟶ Y) (h : X ⟶ Z) (k : Y ⟶ Z)
    (H : IsPushout f g h k) :
    ∃ e : cokernel g ≅ cokernel h, cokernel.π g ≫ e.hom = k ≫ cokernel.π h := by
  have hker : g ≫ (k ≫ cokernel.π h) = 0 := by
    rw [← Category.assoc, ← H.w, Category.assoc, cokernel.condition, comp_zero]
  let φ : cokernel g ⟶ cokernel h := cokernel.desc g (k ≫ cokernel.π h) hker
  have hφ : cokernel.π g ≫ φ = k ≫ cokernel.π h := cokernel.π_desc _ _ hker
  have hzero : f ≫ (0 : X ⟶ cokernel g) = g ≫ cokernel.π g := by
    rw [comp_zero, cokernel.condition]
  let ρ : Z ⟶ cokernel g := H.desc (0 : X ⟶ cokernel g) (cokernel.π g) hzero
  have hρh : h ≫ ρ = 0 := H.inl_desc _ _ hzero
  have hρk : k ≫ ρ = cokernel.π g := H.inr_desc _ _ hzero
  let ψ : cokernel h ⟶ cokernel g := cokernel.desc h ρ hρh
  have hψ : cokernel.π h ≫ ψ = ρ := cokernel.π_desc h ρ hρh
  refine ⟨Iso.mk φ ψ ?_ ?_, hφ⟩
  · apply (cancel_epi (cokernel.π g)).1
    rw [← Category.assoc, hφ, Category.assoc, hψ, hρk]
    simp
  · apply (cancel_epi (cokernel.π h)).1
    rw [← Category.assoc, hψ]
    apply H.hom_ext
    · rw [← Category.assoc, hρh, zero_comp, ← Category.assoc, cokernel.condition, zero_comp]
    · rw [← Category.assoc, hρk, hφ, ← Category.assoc, Category.comp_id]

/-! ## The Mayer–Vietoris square is a pushout -/

/-- **The Mayer–Vietoris square is a pushout.**  With the (positive) middle maps
`chainInclU`, `chainInclV` and the (positive) structure maps `smallOfU`, `smallOfV`, the square

```
C_*(A ∩ V) --chainInclU--> C_*(A)
    |                          |
chainInclV                 smallOfU
    v                          v
C_*(V) ----smallOfV--> C^{A,V}_*(X)
```

is a pushout.  This is a reformulation of the short exactness of the Mayer–Vietoris sequence
`C_*(A ∩ V) ⟶ C_*(A) ⊞ C_*(V) ⟶ C^{A,V}_*(X)` (with the second map `smallOfU - smallOfV`). -/
theorem mv_isPushout (X : TopCat) (A V : Set X) :
    IsPushout (chainInclU A V) (chainInclV A V) (smallOfU A V) (smallOfV A V) := by
  have hw : chainInclU A V ≫ smallOfU A V = chainInclV A V ≫ smallOfV A V :=
    chainInclU_comp_smallOfU A V
  let σ : (singularChains ℤ (TopCat.of A)) ⊞ (singularChains ℤ (TopCat.of V)) ⟶
      (singularChains ℤ (TopCat.of A)) ⊞ (singularChains ℤ (TopCat.of V)) :=
    biprod.lift (biprod.fst : _ ⊞ _ ⟶ _) (-(biprod.snd : _ ⊞ _ ⟶ _))
  have hfst : σ ≫ (biprod.fst : _ ⊞ _ ⟶ _) = biprod.fst := biprod.lift_fst _ _
  have hsnd : σ ≫ (biprod.snd : _ ⊞ _ ⟶ _) = -(biprod.snd) := biprod.lift_snd _ _
  have h1 : (biprod.inl : _ ⟶ _ ⊞ _) ≫ σ = biprod.inl := by
    apply biprod.hom_ext
    · simp only [σ, Category.assoc, biprod.lift_fst]
    · simp only [σ, Category.assoc, biprod.lift_snd, Preadditive.comp_neg, biprod.inl_snd, neg_zero]
  have h2 : (biprod.inr : _ ⟶ _ ⊞ _) ≫ σ = -(biprod.inr) := by
    apply biprod.hom_ext
    · rw [Category.assoc, hfst, biprod.inr_fst, Preadditive.neg_comp, biprod.inr_fst, neg_zero]
    · simp only [σ, Category.assoc, biprod.lift_snd, Preadditive.comp_neg, Preadditive.neg_comp,
        biprod.inr_snd]
  have hσ2 : σ ≫ σ = 𝟙 _ := by
    apply biprod.hom_ext
    · simp only [σ, Category.assoc, biprod.lift_fst, Category.id_comp]
    · simp only [σ, Category.assoc, biprod.lift_snd, Preadditive.comp_neg, neg_neg, Category.id_comp]
  have hdesc : ∀ {Z : _} (a : singularChains ℤ (TopCat.of A) ⟶ Z)
      (b : singularChains ℤ (TopCat.of V) ⟶ Z), σ ≫ biprod.desc a b = biprod.desc a (-b) := by
    intro Z a b
    apply biprod.hom_ext'
    · rw [← Category.assoc, h1, biprod.inl_desc, biprod.inl_desc]
    · rw [← Category.assoc, h2, Preadditive.neg_comp, biprod.inr_desc, biprod.inr_desc]
  have hσdesc : σ ≫ mvRight A V = biprod.desc (smallOfU A V) (smallOfV A V) := by
    rw [show mvRight A V = biprod.desc (smallOfU A V) (-(smallOfV A V)) from rfl, hdesc, neg_neg]
  have hσdesc' : σ ≫ biprod.desc (smallOfU A V) (smallOfV A V) = mvRight A V := by
    rw [hdesc]
    rfl
  have hσlift : mvLeft A V ≫ σ = biprod.lift (chainInclU A V) (-(chainInclV A V)) := by
    rw [show mvLeft A V = biprod.lift (chainInclU A V) (chainInclV A V) from rfl]
    apply biprod.hom_ext
    · rw [Category.assoc, hfst, biprod.lift_fst, biprod.lift_fst]
    · rw [Category.assoc, hsnd, Preadditive.comp_neg, biprod.lift_snd, biprod.lift_snd]
  have hvanish : (biprod.lift (chainInclU A V) (-(chainInclV A V)))
      ≫ (biprod.desc (smallOfU A V) (smallOfV A V)) = 0 := by
    rw [← hσlift, Category.assoc, hσdesc', mvComp]
  let σiso : ((singularChains ℤ (TopCat.of A)) ⊞ (singularChains ℤ (TopCat.of V))) ≅
      ((singularChains ℤ (TopCat.of A)) ⊞ (singularChains ℤ (TopCat.of V))) := Iso.mk σ σ hσ2 hσ2
  have hepi : Epi (biprod.desc (smallOfU A V) (smallOfV A V)) := by
    rw [← hσdesc]
    have hσe : Epi σ := by
      have h : IsIso σ := σiso.isIso_hom
      exact inferInstance
    haveI : Epi (mvRight A V) := (mv_shortExact (X := X) A V).epi_g
    exact epi_comp σ (mvRight A V)
  have hc : IsColimit (CokernelCofork.ofπ (mvRight A V) (mvComp A V)) :=
    (mv_shortExact (X := X) A V).gIsCokernel
  have hcolim : IsColimit (CokernelCofork.ofπ (biprod.desc (smallOfU A V) (smallOfV A V))
      hvanish) := by
    refine CokernelCofork.IsColimit.ofπ' (biprod.desc (smallOfU A V) (smallOfV A V)) hvanish ?_
    intro W k hk
    have hk' : mvLeft A V ≫ (σ ≫ k) = 0 := by rw [← Category.assoc, hσlift, hk]
    obtain ⟨l, hl⟩ := CokernelCofork.IsColimit.desc' hc (σ ≫ k) hk'
    have hl' : mvRight A V ≫ l = σ ≫ k := hl
    refine ⟨l, ?_⟩
    rw [← hσdesc, Category.assoc, hl', ← Category.assoc, hσ2, Category.id_comp]
  refine IsPushout.mk ⟨hw⟩ ⟨(CommSq.isColimitEquivIsColimitCokernelCofork ⟨hw⟩).symm ?_⟩
  exact IsColimit.ofIsoColimit hcolim (Cofork.ext (Iso.refl _) (by simp))

/-! ## The two models of the overlap -/

/-- The canonical homeomorphism `A ∩ V ≅ V ∩ A`: the set `A ∩ V ⊆ X` and the set
`{x : V | (x : X) ∈ A} ⊆ V` describe the same subset, and the map is the identity on the
underlying points of `X`. -/
def overlapTopIso (X : TopCat) (A V : Set X) :
    TopCat.of ↥(A ∩ V) ≅ TopCat.of (relSubset A V) where
  hom := TopCat.ofHom ⟨fun x => ⟨⟨(x : X), x.2.2⟩, x.2.1⟩, by fun_prop⟩
  inv := TopCat.ofHom ⟨fun y => ⟨((y : ↥V) : X), y.2, y.1.2⟩, by fun_prop⟩
  hom_inv_id := by ext x; rfl
  inv_hom_id := by ext y; rfl

/-- The homeomorphism `A ∩ V ≅ V ∩ A` intertwines the two inclusions into `V`. -/
lemma overlapTopIso_hom_comp (X : TopCat) (A V : Set X) :
    (overlapTopIso X A V).hom ≫ subtypeIncl (TopCat.of V) (relSubset A V) = inclUVV A V := by
  ext x
  rfl

/-- The induced isomorphism of singular chain complexes `C_*(A ∩ V) ≅ C_*(V ∩ A)`. -/
def overlapChainsIso (X : TopCat) (A V : Set X) :
    singularChains ℤ (TopCat.of ↥(A ∩ V)) ≅ singularChains ℤ (TopCat.of (relSubset A V)) :=
  ((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).mapIso (overlapTopIso X A V)

/-- Functoriality of `chainMap` on singular chains. -/
lemma chainMap_comp (X Y Z : TopCat) (f : X ⟶ Y) (g : Y ⟶ Z) :
    chainMap ℤ X Y f ≫ chainMap ℤ Y Z g = chainMap ℤ X Z (f ≫ g) := by
  show (((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map f)
      ≫ (((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map g)
    = (((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map (f ≫ g))
  rw [Functor.map_comp]

/-! ## The main statement -/

/-- **Call-by-name statement.** For arbitrary subsets `A, V ⊆ X` the cokernel of
`smallOfU A V : C_*(A) ⟶ C^{A,V}_*(X)` is the relative chain complex of the pair `(V, A ∩ V)`. -/
theorem cokerSmallOfU_iso_relChainsCov (X : TopCat) (A V : Set X) :
    Nonempty (CategoryTheory.Limits.cokernel (Work.Cohomology.smallOfU A V) ≅
      Work.Cohomology.relChains (TopCat.of ↥V) {x : ↥V | (x : X) ∈ A}) := by
  obtain ⟨e, _he⟩ := cokernel_iso_of_isPushout (chainInclU A V) (chainInclV A V)
    (smallOfU A V) (smallOfV A V) (mv_isPushout X A V)
  have hcompat : chainInclV A V ≫ 𝟙 (singularChains ℤ (TopCat.of V))
      = (overlapChainsIso X A V).hom ≫ inclChains (TopCat.of V) (relSubset A V) := by
    rw [Category.comp_id]
    show chainMap ℤ (TopCat.of ↥(A ∩ V)) (TopCat.of V) (inclUVV A V)
      = chainMap ℤ (TopCat.of ↥(A ∩ V)) (TopCat.of (relSubset A V)) (overlapTopIso X A V).hom
        ≫ chainMap ℤ (TopCat.of (relSubset A V)) (TopCat.of V)
            (subtypeIncl (TopCat.of V) (relSubset A V))
    rw [chainMap_comp, overlapTopIso_hom_comp]
  exact ⟨e.symm ≪≫ cokernel.mapIso (chainInclV A V) (inclChains (TopCat.of V) (relSubset A V))
    (overlapChainsIso X A V) (Iso.refl _) hcompat⟩

end

end Work.Cohomology
