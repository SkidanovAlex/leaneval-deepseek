import Mathlib
import Submission.Work.Cohomology.SmallChains
import Submission.Work.Cohomology.SmallSES
import Submission.Work.Cohomology.mv_shortExact
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.relCochain_shortExact
import Submission.Work.Cohomology.smallLift_cov

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The relative small chains are the relative chains of `(U, A ∩ U)`

For a space `X` and subsets `A, U ⊆ X`, the cokernel of the map

`smallOfU A U : C_*(A) ⟶ C^{A,U}_*(X)`

induced by the inclusion `A ↪ X` into the *small* chains of the cover `{A, U}`, is canonically
isomorphic to the relative chain complex `C_*(U, A ∩ U) = C_*(U)/C_*(A ∩ U)` of the pair
`(U, A ∩ U)`.  The isomorphism is the one through which the second map of the Mayer–Vietoris
sequence `smallOfV A U : C_*(U) ⟶ C^{A,U}_*(X)` factors, i.e. it satisfies

`π_{C_*(U) → C_*(U,A∩U)} ≫ e = smallOfV A U ≫ π_{C^{A,U}_*(X) → coker(smallOfU A U)}`.

This is the two-cover/`second isomorphism theorem` input of the excision argument
(`Work.Cohomology.excision_iso_rel_of_iso`, `Work.Cohomology.relChainsMap_quasiIso`): the
compatibility is exactly what identifies the natual map `C_*(U) → C^{A,U}_*(X)/C_*(A)` with the
projection onto the relative chains of `(U, A ∩ U)`.

## Proof

Write `g : C_*(A ∩ U) ⟶ C_*(U)` for the inclusion.  The Mayer–Vietoris short exact sequence
`0 ⟶ C_*(A ∩ U) ⟶ C_*(A) ⊞ C_*(U) ⟶ C^{A,U}_*(X) ⟶ 0` exhibits `C^{A,U}_*(X)` as the cokernel of
its left-hand map, so the map `w = (0, -π_g) : C_*(A) ⊞ C_*(U) ⟶ coker g` — which kills the image of
the left-hand map because `smallOfV A U ≫ π_g = 0` — descends to a chain map
`s : C^{A,U}_*(X) ⟶ coker g`.  The universal property of `coker (smallOfU A U)` turns `s` into the
inverse of the canonical map `coker g ⟶ coker (smallOfU A U)` induced by `smallOfV A U`; the two
composites are identities by cancellation with the epimorphisms `π_g` and `π_{smallOfU}`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

variable {X : TopCat}

/-- The homeomorphism `A ∩ U ≅ {x : U | x ∈ A}` between the two incarnations of the overlap of `A`
and `U`. -/
def interIso (A U : Set X) :
    TopCat.of ↥(A ∩ U) ≅ TopCat.of {x : ↥U | (x : X) ∈ A} where
  hom := TopCat.ofHom ⟨fun x => ⟨⟨x.1, x.2.2⟩, x.2.1⟩, by fun_prop⟩
  inv := TopCat.ofHom ⟨fun x => ⟨x.1.1, ⟨x.2, x.1.2⟩⟩, by fun_prop⟩
  hom_inv_id := by ext x; rfl
  inv_hom_id := by ext x; rfl

@[reassoc (attr := simp)]
lemma interIso_hom_comp_subtypeIncl (A U : Set X) :
    (interIso A U).hom ≫ subtypeIncl (TopCat.of U) {x : ↥U | (x : X) ∈ A}
      = inclUVV A U := by
  ext x; rfl

/-- Naturality of `biprod.desc` under postcomposition. -/
lemma biprod_desc_comp {C : Type*} [Category C] [Preadditive C] {Y₁ Y₂ W V : C}
    [HasBinaryBiproduct Y₁ Y₂] (p : Y₁ ⟶ W) (q : Y₂ ⟶ W) (k : W ⟶ V) :
    biprod.desc p q ≫ k = biprod.desc (p ≫ k) (q ≫ k) := by
  rw [biprod.desc_eq, biprod.desc_eq, Preadditive.add_comp, Category.assoc, Category.assoc]

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Work.Cohomology in
theorem cokerSmallOfU_iso_relChains_compat (X : TopCat) (A U : Set X) :
    ∃ (e : relChains (TopCat.of U) {x : U | (x : X) ∈ A} ≅ cokernel (smallOfU A U)),
      cokernel.π (inclChains (TopCat.of U) {x : U | (x : X) ∈ A}) ≫ e.hom
        = smallOfV A U ≫ cokernel.π (smallOfU A U) := by
  let A' : Set ↥U := {x : ↥U | (x : X) ∈ A}
  let f : singularChains ℤ (TopCat.of A) ⟶ smallChains A U := smallOfU A U
  let h : singularChains ℤ (TopCat.of U) ⟶ smallChains A U := smallOfV A U
  let g : singularChains ℤ (TopCat.of A') ⟶ singularChains ℤ (TopCat.of U) :=
    inclChains (TopCat.of U) A'
  let G : ChainComplex (ModuleCat ℤ) ℕ := cokernel g
  let F : ChainComplex (ModuleCat ℤ) ℕ := cokernel f
  let i1 : singularChains ℤ (TopCat.of ↥(A ∩ U)) ⟶ singularChains ℤ (TopCat.of A) :=
    chainMap ℤ (TopCat.of ↥(A ∩ U)) (TopCat.of A) (inclUVU A U)
  let i2 : singularChains ℤ (TopCat.of ↥(A ∩ U)) ⟶ singularChains ℤ (TopCat.of U) :=
    chainMap ℤ (TopCat.of ↥(A ∩ U)) (TopCat.of U) (inclUVV A U)
  let κ : singularChains ℤ (TopCat.of ↥(A ∩ U)) ⟶ singularChains ℤ (TopCat.of A') :=
    chainMap ℤ (TopCat.of ↥(A ∩ U)) (TopCat.of A') (interIso A U).hom
  haveI hκiso : IsIso κ := by
    dsimp only [κ, chainMap]
    infer_instance
  -- The map `C_*(A ∩ U) ⟶ C_*(U)` agrees with the inclusion of `A'` followed by `g`.
  have hkg : κ ≫ g = i2 := by
    dsimp only [κ, g, i2, inclChains, chainMap]
    rw [← Functor.map_comp, interIso_hom_comp_subtypeIncl]
  -- The two inclusions `A ∩ U ⊆ A ⊆ X` and `A ∩ U ⊆ U ⊆ X` agree.
  have hlift_eq : i1 ≫ f = i2 ≫ h := by
    have hcomp := mvComp A U
    rw [show mvLeft A U = biprod.lift i1 i2 from rfl,
        show mvRight A U = biprod.desc f (-h) from rfl,
        biprod.lift_desc] at hcomp
    have h2 : i1 ≫ f - i2 ≫ h = 0 := by
      simpa [Preadditive.comp_neg, sub_eq_add_neg] using hcomp
    exact sub_eq_zero.mp h2
  -- The canonical map `coker g ⟶ coker f` induced by `h`.
  have hzero : g ≫ (h ≫ cokernel.π f) = 0 := by
    have h1 : κ ≫ (g ≫ (h ≫ cokernel.π f)) = 0 := by
      rw [← Category.assoc, hkg]
      rw [← Category.assoc, ← hlift_eq]
      rw [Category.assoc, cokernel.condition, comp_zero]
    exact (cancel_epi κ).1 (by rw [h1, comp_zero])
  let e' : G ⟶ F := cokernel.desc g (h ≫ cokernel.π f) hzero
  have he' : cokernel.π g ≫ e' = h ≫ cokernel.π f :=
    cokernel.π_desc g (h ≫ cokernel.π f) hzero
  -- The Mayer–Vietoris short exact sequence for the cover `{A, U}`.
  let S : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
    ShortComplex.mk (mvLeft A U) (mvRight A U) (mvComp A U)
  have hS : S.ShortExact := mv_shortExact A U
  haveI hSepi : Epi (mvRight A U) := by
    have := hS.epi_g
    rwa [show S.g = mvRight A U from rfl] at this
  -- The map `w = (0, -π_g)` kills the left-hand map of the Mayer–Vietoris sequence.
  have hw : mvLeft A U ≫ biprod.desc (0 : singularChains ℤ (TopCat.of A) ⟶ G)
      (-(cokernel.π g)) = 0 := by
    rw [show mvLeft A U = biprod.lift i1 i2 from rfl, biprod.lift_desc]
    rw [comp_zero, zero_add, Preadditive.comp_neg]
    have hi2 : i2 ≫ cokernel.π g = 0 := by
      rw [← hkg, Category.assoc, cokernel.condition, comp_zero]
    rw [hi2, neg_zero]
  -- Descent of `w` through `mvRight`, using that `C^{A,U}_*(X)` is its cokernel.
  let s : smallChains A U ⟶ G :=
    (CokernelCofork.IsColimit.desc' hS.gIsCokernel
      (biprod.desc (0 : singularChains ℤ (TopCat.of A) ⟶ G) (-(cokernel.π g))) hw).1
  have hs : mvRight A U ≫ s = biprod.desc (0 : singularChains ℤ (TopCat.of A) ⟶ G)
      (-(cokernel.π g)) := by
    have := (CokernelCofork.IsColimit.desc' hS.gIsCokernel
      (biprod.desc (0 : singularChains ℤ (TopCat.of A) ⟶ G) (-(cokernel.π g))) hw).2
    simpa using this
  have hfs : f ≫ s = 0 := by
    have hinl : (biprod.inl : singularChains ℤ (TopCat.of A) ⟶
        singularChains ℤ (TopCat.of A) ⊞ singularChains ℤ (TopCat.of U)) ≫ mvRight A U = f :=
      biprod.inl_desc _ _
    rw [show f = (biprod.inl : singularChains ℤ (TopCat.of A) ⟶
        singularChains ℤ (TopCat.of A) ⊞ singularChains ℤ (TopCat.of U)) ≫ mvRight A U
        from hinl.symm]
    rw [Category.assoc, hs, biprod.inl_desc]
  have hhs : h ≫ s = cokernel.π g := by
    have hinr : (biprod.inr : singularChains ℤ (TopCat.of U) ⟶
        singularChains ℤ (TopCat.of A) ⊞ singularChains ℤ (TopCat.of U)) ≫ mvRight A U = -h :=
      biprod.inr_desc _ _
    rw [show h = -((biprod.inr : singularChains ℤ (TopCat.of U) ⟶
        singularChains ℤ (TopCat.of A) ⊞ singularChains ℤ (TopCat.of U)) ≫ mvRight A U) from by
      rw [hinr, neg_neg]]
    rw [Preadditive.neg_comp, Category.assoc, hs, biprod.inr_desc, neg_neg]
  -- The inverse of `e'`.
  let e'' : F ⟶ G := cokernel.desc f s hfs
  have he'' : cokernel.π f ≫ e'' = s := cokernel.π_desc f s hfs
  have hse' : s ≫ e' = cokernel.π f := by
    apply (cancel_epi (mvRight A U)).1
    calc mvRight A U ≫ (s ≫ e')
        = (mvRight A U ≫ s) ≫ e' := (Category.assoc _ _ _).symm
      _ = biprod.desc (0 : singularChains ℤ (TopCat.of A) ⟶ G) (-(cokernel.π g)) ≫ e' := by
            rw [hs]
      _ = biprod.desc ((0 : singularChains ℤ (TopCat.of A) ⟶ G) ≫ e')
              ((-(cokernel.π g)) ≫ e') := biprod_desc_comp _ _ _
      _ = biprod.desc 0 (-(h ≫ cokernel.π f)) := by
            rw [zero_comp, Preadditive.neg_comp, he']
      _ = biprod.desc (f ≫ cokernel.π f) ((-h) ≫ cokernel.π f) := by
            rw [cokernel.condition f, Preadditive.neg_comp]
      _ = (biprod.desc f (-h)) ≫ cokernel.π f := (biprod_desc_comp f (-h) (cokernel.π f)).symm
      _ = mvRight A U ≫ cokernel.π f := rfl
  have h1 : e' ≫ e'' = 𝟙 G := by
    apply (cancel_epi (cokernel.π g)).1
    rw [Category.comp_id]
    calc cokernel.π g ≫ (e' ≫ e'')
        = (cokernel.π g ≫ e') ≫ e'' := (Category.assoc _ _ _).symm
      _ = (h ≫ cokernel.π f) ≫ e'' := by rw [he']
      _ = h ≫ (cokernel.π f ≫ e'') := Category.assoc _ _ _
      _ = h ≫ s := by rw [he'']
      _ = cokernel.π g := hhs
  have h2 : e'' ≫ e' = 𝟙 F := by
    apply (cancel_epi (cokernel.π f)).1
    rw [Category.comp_id]
    calc cokernel.π f ≫ (e'' ≫ e')
        = (cokernel.π f ≫ e'') ≫ e' := (Category.assoc _ _ _).symm
      _ = s ≫ e' := by rw [he'']
      _ = cokernel.π f := hse'
  exact ⟨{ hom := e', inv := e'', hom_inv_id := h1, inv_hom_id := h2 }, he'⟩

end

end Work.Cohomology
