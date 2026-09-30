import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.Pi6.EMZ.BocksteinCore
import Submission.Work.SSS.ExpTensLES
import Submission.Work.StemsB.sphRatHomology
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

/-!
# AREA BOCK — the vocabulary of the natural Bockstein long exact sequence

This file fixes the objects used by `Work.Pi6.BOCK.bocksteinLES`:

* the coefficient short complex `0 → ℤ --·p--> ℤ --red--> ℤ/p → 0`
  (`Work.Pi6.EMZ.coeffSES`, proved short exact in the sibling file `coeffSESShortExact`);
* the Bockstein short complex of singular chains
  `0 → C_*(X;ℤ) --·p--> C_*(X;ℤ) --red--> C_*(X;ℤ/p) → 0`
  (`Work.Pi6.EMZ.bockSES`, short exact by `Work.Pi6.EMZ.bockSES_shortExact`);
* `Work.Pi6.BOCK.expTensMapHom`: the image of a chain map under the coefficient extension `- ⊗ M`;
* `Work.Pi6.BOCK.baseChangeNatIso`: the base-change isomorphism
  `F(C_*(X;M)) ≅ C_*(X;F M)` for a functor `F` preserving coproducts, **as an isomorphism of
  functors of the simplicial set `X`** — this is the naturality input of the whole argument.

The remaining files of the area prove the pieces of the long exact sequence and its naturality.
-/

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory

namespace Work.Pi6.BOCK

noncomputable section

/-! ## Coefficient modules -/

/-- `ℤ` as a `ℤ`-module. -/
abbrev zZ : ModuleCat ℤ := Work.Pi6.EMZ.zZ

/-- `ℤ/p` as a `ℤ`-module. -/
abbrev Mp (p : ℕ) : ModuleCat ℤ := Work.Pi6.EMZ.Mp p

/-! ## The coefficient extension of a chain map -/

/-- The image of a chain map `φ : K ⟶ K'` under the coefficient extension `- ⊗ M`:
the chain map `expTens K M ⟶ expTens K' M` with components `φ.f n ▷ M`. -/
def expTensMapHom (K K' : ChainComplex (ModuleCat ℤ) ℕ) (φ : K ⟶ K') (M : ModuleCat ℤ) :
    Work.SSS.expTens K M ⟶ Work.SSS.expTens K' M where
  f n := φ.f n ▷ M
  comm' i j hij := by
    obtain rfl : j + 1 = i := (ComplexShape.down_Rel ℕ i j).mp hij
    rw [Work.SSS.expTens_d, Work.SSS.expTens_d, ← MonoidalCategory.comp_whiskerRight,
      ← MonoidalCategory.comp_whiskerRight]
    exact congrArg (fun t => MonoidalCategory.whiskerRight t M) (φ.comm (j + 1) j)

@[simp]
theorem expTensMapHom_f (K K' : ChainComplex (ModuleCat ℤ) ℕ) (φ : K ⟶ K') (M : ModuleCat ℤ)
    (n : ℕ) : (expTensMapHom K K' φ M).f n = φ.f n ▷ M := rfl

/-- `expTensMapHom` of an identity is an identity. -/
theorem expTensMapHom_id (K : ChainComplex (ModuleCat ℤ) ℕ) (M : ModuleCat ℤ) :
    expTensMapHom K K (𝟙 K) M = 𝟙 (Work.SSS.expTens K M) := by
  apply HomologicalComplex.hom_ext
  intro n
  simp [expTensMapHom]

/-- `expTensMapHom` is compatible with composition. -/
theorem expTensMapHom_comp (K K' K'' : ChainComplex (ModuleCat ℤ) ℕ) (φ : K ⟶ K')
    (ψ : K' ⟶ K'') (M : ModuleCat ℤ) :
    expTensMapHom K K' φ M ≫ expTensMapHom K' K'' ψ M = expTensMapHom K K'' (φ ≫ ψ) M := by
  apply HomologicalComplex.hom_ext
  intro n
  simp only [HomologicalComplex.comp_f, expTensMapHom_f]
  rw [← MonoidalCategory.comp_whiskerRight]

/-- `expTensMapHom` commutes with the coefficient change `expTensHom`. -/
theorem expTensMapHom_expTensHom (K K' : ChainComplex (ModuleCat ℤ) ℕ) (φ : K ⟶ K')
    {M N : ModuleCat ℤ} (ρ : M ⟶ N) :
    expTensMapHom K K' φ M ≫ Work.SSS.expTensHom K' ρ =
      Work.SSS.expTensHom K ρ ≫ expTensMapHom K K' φ N := by
  apply HomologicalComplex.hom_ext
  intro n
  simp only [HomologicalComplex.comp_f, expTensMapHom_f, Work.SSS.expTensHom_f]
  rw [MonoidalCategory.whisker_exchange]

/-! ## The base-change isomorphism, as an isomorphism of functors -/

/-- **The chain complex functor unfolded.**  The `n`-simplices of `X` span a free module of
rank one, so the singular chain complex of `X` with coefficients in `R` is the alternating face
map complex of the simplicial object `X ⋙ sigmaConst.obj R`. -/
theorem chainFunctor_obj_eq (C : Type*) [Category* C] [HasCoproducts C] [Preadditive C] (R : C) :
    (SSet.chainComplexFunctor C).obj R =
      ((Functor.whiskeringRight SimplexCategoryᵒᵖ Type C).obj (Limits.sigmaConst.obj R)) ⋙
        (AlgebraicTopology.alternatingFaceMapComplex C) := rfl

/-- The two ways of describing the functor `X ↦ (X ⋙ sigmaConst.obj R) ⋙ F`. -/
theorem bock_whisker_eq {C D : Type*} [Category* C] [Category* D] [HasCoproducts C]
    [HasCoproducts D] (F : C ⥤ D) (R : C) :
    ((Functor.whiskeringRight SimplexCategoryᵒᵖ Type C).obj (Limits.sigmaConst.obj R) ⋙
      (Functor.whiskeringRight SimplexCategoryᵒᵖ C D).obj F)
    = ((Functor.whiskeringRight SimplexCategoryᵒᵖ Type D).obj
        (Limits.sigmaConst.obj R ⋙ F)) := rfl

/-- The two descriptions of the base-changed chain complex functor. -/
theorem base_eq {C D : Type*} [Category* C] [Category* D] [HasCoproducts C] [HasCoproducts D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive]
    [∀ (S : Type), PreservesColimitsOfShape (Discrete S) F] (R : C) :
    ((SSet.chainComplexFunctor C).obj R ⋙ F.mapHomologicalComplex (ComplexShape.down ℕ)) =
      (((Functor.whiskeringRight SimplexCategoryᵒᵖ Type D).obj (Limits.sigmaConst.obj R ⋙ F)) ⋙
        (AlgebraicTopology.alternatingFaceMapComplex D)) := by
  rw [chainFunctor_obj_eq, Functor.assoc, AlgebraicTopology.map_alternatingFaceMapComplex,
    ← Functor.assoc, bock_whisker_eq]

/-- **Base change for the singular chain complex, as an isomorphism of functors of the simplicial
set.**  For an additive functor `F` preserving coproducts, the base change of the singular chain
complex of a simplicial set `X` with coefficients in `R` is the singular chain complex with
coefficients in `F.obj R`.  Being an isomorphism of functors, this isomorphism is *natural in `X`*
by construction. -/
noncomputable def baseChangeNatIso {C D : Type*} [Category* C] [Category* D] [HasCoproducts C]
    [HasCoproducts D] [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive]
    [∀ (S : Type), PreservesColimitsOfShape (Discrete S) F] (R : C) :
    (SSet.chainComplexFunctor C).obj R ⋙ F.mapHomologicalComplex (ComplexShape.down ℕ) ≅
      (SSet.chainComplexFunctor D).obj (F.obj R) :=
  eqToIso (base_eq F R) ≪≫
    ((Functor.whiskeringRight SSet (SimplicialObject D) (ChainComplex D ℕ)).obj
      (AlgebraicTopology.alternatingFaceMapComplex D)).mapIso
      ((Functor.whiskeringRight SimplexCategoryᵒᵖ Type D).mapIso
        (Work.StemsB.SphRat.sigmaConstObjCompIso F R)) ≪≫
    eqToIso (chainFunctor_obj_eq D (F.obj R)).symm

/-- The `X`-component of the base-change isomorphism is an isomorphism
`F(C_*(X;R)) ≅ C_*(X;F R)`. -/
def baseChangeNatIso_app {C D : Type*} [Category* C] [Category* D] [HasCoproducts C]
    [HasCoproducts D] [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive]
    [∀ (S : Type), PreservesColimitsOfShape (Discrete S) F] (R : C) (X : SSet) :
    (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj (X.chainComplex R) ≅
      X.chainComplex (F.obj R) :=
  (baseChangeNatIso F R).app X

/-! ## Restriction of scalars and homology -/

/-- **A functor preserving homology commutes with the passage to homology**, in the form of the
canonical isomorphism `H_n(F(K)) ≅ F(H_n(K))`. -/
noncomputable def fcHomologyIso {𝕜 : Type*} [CommRing 𝕜]
    (F : ModuleCat 𝕜 ⥤ ModuleCat ℤ) [F.Additive] [F.PreservesHomology]
    (K : ChainComplex (ModuleCat 𝕜) ℕ) (n : ℕ) :
    (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K).homology n) ≅ F.obj (K.homology n) :=
  ShortComplex.mapHomologyIso (K.sc n) F ≪≫ Iso.refl _

section CompSix

variable {C : Type*} [Category* C]

/-- **Composition of six commuting squares of isomorphisms.**  If `m_i ≫ T_i.hom = S_i.hom ≫ m_{i+1}`
for `i = 1, …, 6`, then the composite of the `m_i` intertwines the composites of the `S_i` and the
`T_i`.  This is the bookkeeping lemma underlying the naturality of the Bockstein sequence. -/
theorem comp_six_aux {A1 A2 A3 A4 A5 A6 A7 B1 B2 B3 B4 B5 B6 B7 : C}
    (S1 : A1 ≅ A2) (S2 : A2 ≅ A3) (S3 : A3 ≅ A4) (S4 : A4 ≅ A5) (S5 : A5 ≅ A6) (S6 : A6 ≅ A7)
    (T1 : B1 ≅ B2) (T2 : B2 ≅ B3) (T3 : B3 ≅ B4) (T4 : B4 ≅ B5) (T5 : B5 ≅ B6) (T6 : B6 ≅ B7)
    (m1 : A1 ⟶ B1) (m2 : A2 ⟶ B2) (m3 : A3 ⟶ B3) (m4 : A4 ⟶ B4) (m5 : A5 ⟶ B5)
    (m6 : A6 ⟶ B6) (m7 : A7 ⟶ B7)
    (h1 : m1 ≫ T1.hom = S1.hom ≫ m2) (h2 : m2 ≫ T2.hom = S2.hom ≫ m3)
    (h3 : m3 ≫ T3.hom = S3.hom ≫ m4) (h4 : m4 ≫ T4.hom = S4.hom ≫ m5)
    (h5 : m5 ≫ T5.hom = S5.hom ≫ m6) (h6 : m6 ≫ T6.hom = S6.hom ≫ m7) :
    m1 ≫ (T1 ≪≫ T2 ≪≫ T3 ≪≫ T4 ≪≫ T5 ≪≫ T6).hom =
      (S1 ≪≫ S2 ≪≫ S3 ≪≫ S4 ≪≫ S5 ≪≫ S6).hom ≫ m7 := by
  have e1 : m1 ≫ (T1.hom ≫ (T2.hom ≫ (T3.hom ≫ (T4.hom ≫ (T5.hom ≫ T6.hom)))))
      = S1.hom ≫ (m2 ≫ (T2.hom ≫ (T3.hom ≫ (T4.hom ≫ (T5.hom ≫ T6.hom))))) := by
    rw [← Category.assoc, h1, Category.assoc]
  have e2 : m2 ≫ (T2.hom ≫ (T3.hom ≫ (T4.hom ≫ (T5.hom ≫ T6.hom))))
      = S2.hom ≫ (m3 ≫ (T3.hom ≫ (T4.hom ≫ (T5.hom ≫ T6.hom)))) := by
    rw [← Category.assoc, h2, Category.assoc]
  have e3 : m3 ≫ (T3.hom ≫ (T4.hom ≫ (T5.hom ≫ T6.hom)))
      = S3.hom ≫ (m4 ≫ (T4.hom ≫ (T5.hom ≫ T6.hom))) := by
    rw [← Category.assoc, h3, Category.assoc]
  have e4 : m4 ≫ (T4.hom ≫ (T5.hom ≫ T6.hom))
      = S4.hom ≫ (m5 ≫ (T5.hom ≫ T6.hom)) := by
    rw [← Category.assoc, h4, Category.assoc]
  have e5 : m5 ≫ (T5.hom ≫ T6.hom) = S5.hom ≫ (m6 ≫ T6.hom) := by
    rw [← Category.assoc, h5, Category.assoc]
  simp only [Iso.trans_hom]
  rw [e1, e2, e3, e4, e5, h6]
  simp only [Category.assoc]

/-- **The inverse naturality of a commuting square of isomorphisms.** -/
theorem inv_naturality_of_square {P Q P' Q' : C} (e1 : P ≅ Q) (e2 : P' ≅ Q')
    (m1 : P ⟶ P') (m2 : Q ⟶ Q') (h : m1 ≫ e2.hom = e1.hom ≫ m2) :
    m2 ≫ e2.inv = e1.inv ≫ m1 := by
  rw [← cancel_epi e1.hom]
  rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

end CompSix

end

end Work.Pi6.BOCK
