import Mathlib
import Submission.Work.SSS.ExpTens
import Submission.Work.StemsB.sphRatHomology

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 (see the port commit message)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000


namespace Work.SSS

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory DoldKan
open Simplicial AlgebraicTopology

noncomputable section

/-! ## Auxiliaries: `Splitting.map` commutes with the differentials

For a simplicial object `X` in a preadditive category `C`, a splitting `s` of `X`, and a functor
`F : C ⥤ D` which is additive and preserves finite coproducts, `s.map F` is a splitting of
`X ⋙ F` whose normalized chain complex is obtained from that of `s` by applying `F` degreewise.
The lemma `normCoeff_map_d` below is the key step: `(s.map F).d i j = F.map (s.d i j)`. -/

open SimplicialObject.Splitting in
/-- The coproduct inclusions of the mapped splitting are the `F`-images of the original ones. -/
lemma normCoeff_map_cofan_inj {C : Type*} [Category* C] [Preadditive C]
    {D : Type*} [Category* D] [Preadditive D]
    {Xc : SimplicialObject C} (sc : Xc.Splitting) (F : C ⥤ D) [PreservesFiniteCoproducts F]
    {Δ : SimplexCategoryᵒᵖ} (A : IndexSet Δ) :
    ((sc.map F).cofan Δ).inj A = F.map ((sc.cofan Δ).inj A) := by
  show (sc.map F).ι (Opposite.unop A.fst).len ≫ F.map (Xc.map A.e.op) =
    F.map (sc.ι (Opposite.unop A.fst).len ≫ Xc.map A.e.op)
  rw [F.map_comp, SimplicialObject.Splitting.map_ι]
  try rfl

open SimplicialObject.Splitting in
/-- The projections of the mapped splitting are the `F`-images of the original ones. -/
lemma normCoeff_map_πSummand {C : Type*} [Category* C] [Preadditive C]
    {D : Type*} [Category* D] [Preadditive D]
    {Xc : SimplicialObject C} (sc : Xc.Splitting) (F : C ⥤ D) [F.Additive]
    [PreservesFiniteCoproducts F] {Δ : SimplexCategoryᵒᵖ} (A₀ : IndexSet Δ) :
    (sc.map F).πSummand A₀ = F.map (sc.πSummand A₀) := by
  set_option backward.isDefEq.respectTransparency false in
  apply (sc.map F).hom_ext'
  intro B
  rw [normCoeff_map_cofan_inj sc F B]
  conv_rhs => rw [← F.map_comp]
  rw [← normCoeff_map_cofan_inj sc F B]
  by_cases hB : B = A₀
  · subst hB
    rw [cofan_inj_πSummand_eq_id, cofan_inj_πSummand_eq_id, F.map_id]
    rfl
  · rw [cofan_inj_πSummand_eq_zero (s := sc.map F) B A₀ (Ne.symm hB),
      cofan_inj_πSummand_eq_zero (s := sc) B A₀ (Ne.symm hB), F.map_zero]

/-- Applying an additive functor to the alternating face map complex of a simplicial object. -/
lemma normCoeff_map_alternatingFaceMapComplex_d {C : Type*} [Category* C] [Preadditive C]
    {D : Type*} [Category* D] [Preadditive D]
    (F : C ⥤ D) [F.Additive] (Y : SimplicialObject C) (i j : ℕ) :
    (AlgebraicTopology.AlternatingFaceMapComplex.obj (Y ⋙ F)).d i j =
      F.map ((AlgebraicTopology.AlternatingFaceMapComplex.obj Y).d i j) := by
  by_cases hij : j + 1 = i
  · subst hij
    rw [AlternatingFaceMapComplex.obj_d_eq, AlternatingFaceMapComplex.obj_d_eq, Functor.map_sum]
    simp only [Functor.map_zsmul]
    rfl
  · rw [HomologicalComplex.shape _ _ _ hij, HomologicalComplex.shape _ _ _ hij, F.map_zero]

open SimplicialObject.Splitting in
/-- `Splitting.map` commutes with the differentials of the normalized chain complexes. -/
lemma normCoeff_map_d {C : Type*} [Category* C] [Preadditive C]
    {D : Type*} [Category* D] [Preadditive D]
    {Xc : SimplicialObject C} (sc : Xc.Splitting) (F : C ⥤ D) [F.Additive]
    [PreservesFiniteCoproducts F] (i j : ℕ) :
    (sc.map F).d i j = F.map (sc.d i j) := by
  set_option backward.isDefEq.respectTransparency false in
  have hd := normCoeff_map_alternatingFaceMapComplex_d F Xc i j
  rw [SimplicialObject.Splitting.d, SimplicialObject.Splitting.d, hd,
    normCoeff_map_cofan_inj sc F _, normCoeff_map_πSummand sc F _]
  rw [← F.map_comp, ← F.map_comp]

/-! ## The normalized chain complex of the coefficient extension -/

/-- **The normalized chain complex of `s.map (tensorRight M)` is `expTens` of that of `s`.**
Both complexes have `n`-th term `s.N n ⊗ M` and differential `s.d i j ▷ M`. -/
def normCoeff_map_tensorRight_iso (Y : SimplicialObject (ModuleCat ℤ)) (s : Y.Splitting)
    (M : ModuleCat ℤ) :
    (s.map (MonoidalCategory.tensorRight M)).nondegComplex ≅ expTens s.nondegComplex M := by
  set_option backward.isDefEq.respectTransparency false in
  refine Hom.isoOfComponents (fun n => Iso.refl _) (fun i j hij => ?_)
  have hij' : j + 1 = i := (ComplexShape.down_Rel ℕ i j).mp hij
  subst hij'
  simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  rw [SimplicialObject.Splitting.nondegComplex_d,
    normCoeff_map_d s (MonoidalCategory.tensorRight M), ChainComplex.of_d,
    SimplicialObject.Splitting.nondegComplex_d]
  rfl

/-- **The coefficient comparison as a morphism of split simplicial objects.**  A natural
transformation `γ : sigmaConst.obj ℤ ⋙ tensorRight M ⟶ sigmaConst.obj M` induces a morphism from
the splitting `(X.splitting.map (sigmaConst.obj ℤ)).map (tensorRight M)` to the splitting
`X.splitting.map (sigmaConst.obj M)`; the compatibility with the `ι`'s is exactly the naturality
of `γ` at the inclusions `X.splitting.ι n` of the nondegenerate simplices. -/
def normCoeff_splitHom (X' : SSet) (M : ModuleCat ℤ)
    (γ : (Limits.sigmaConst.obj (ModuleCat.of ℤ ℤ) ⋙ MonoidalCategory.tensorRight M) ⟶
      Limits.sigmaConst.obj M) :
    SimplicialObject.Split.Hom
      ⟨(X' ⋙ (Limits.sigmaConst.obj (ModuleCat.of ℤ ℤ) ⋙ MonoidalCategory.tensorRight M)),
        (X'.splitting.map (Limits.sigmaConst.obj (ModuleCat.of ℤ ℤ))).map
          (MonoidalCategory.tensorRight M)⟩
      ⟨X' ⋙ Limits.sigmaConst.obj M, X'.splitting.map (Limits.sigmaConst.obj M)⟩ where
  F := { app := fun n => γ.app (X'.obj n), naturality := fun {n m} f => γ.naturality (X'.map f) }
  f := fun n => γ.app (X'.splitting.N n)
  comm := fun n => by
    have h := γ.naturality (X'.splitting.ι n)
    simp only [SimplicialObject.Splitting.map_ι, Functor.comp_map] at h ⊢
    exact h

/-- **Coefficient extension of the normalized chain complex of a split simplicial set.**
For an isomorphism of functors `γ : sigmaConst.obj ℤ ⋙ tensorRight M ≅ sigmaConst.obj M` the
normalized chain complex with coefficients in `M` is the coefficient extension of the integral
one. -/
def normCoeff_coeffIso (X' : SSet) (M : ModuleCat ℤ)
    (γ : (Limits.sigmaConst.obj (ModuleCat.of ℤ ℤ) ⋙ MonoidalCategory.tensorRight M) ≅
      Limits.sigmaConst.obj M) :
    X'.normalizedChainComplex M ≅
      expTens (X'.normalizedChainComplex (ModuleCat.of ℤ ℤ)) M := by
  set_option backward.isDefEq.respectTransparency false in
  let Φ := normCoeff_splitHom X' M γ.hom
  have e₂ : ((X'.splitting.map (Limits.sigmaConst.obj (ModuleCat.of ℤ ℤ))).map
        (MonoidalCategory.tensorRight M)).nondegComplex ≅
      (X'.splitting.map (Limits.sigmaConst.obj M)).nondegComplex :=
    Hom.isoOfComponents (fun n => γ.app (X'.splitting.N n))
      (fun i j hij => (SimplicialObject.Split.nondegComplexFunctor.map Φ).comm' i j hij)
  have e₁ := normCoeff_map_tensorRight_iso
    (X' ⋙ Limits.sigmaConst.obj (ModuleCat.of ℤ ℤ))
    (X'.splitting.map (Limits.sigmaConst.obj (ModuleCat.of ℤ ℤ))) M
  exact e₂.symm ≪≫ e₁

/-- The functor `S ↦ (∐_S ℤ) ⊗ M` is naturally isomorphic to `S ↦ ∐_S M`: tensoring the free
`ℤ`-module on a type `S` with an abelian group `M` gives the coproduct of copies of `M` indexed
by `S`. -/
theorem sigmaConstTensorIso (M : ModuleCat ℤ) :
    Nonempty ((Limits.sigmaConst.obj (ModuleCat.of ℤ ℤ) ⋙ MonoidalCategory.tensorRight M :
        Type ⥤ ModuleCat ℤ) ≅ (Limits.sigmaConst.obj M : Type ⥤ ModuleCat ℤ)) := by
  refine ⟨?_⟩
  haveI : ∀ (S : Type), PreservesColimitsOfShape (Discrete S) (MonoidalCategory.tensorRight M) :=
    fun _ => inferInstance
  exact Work.StemsB.SphRat.sigmaConstObjCompIso (MonoidalCategory.tensorRight M)
      (ModuleCat.of ℤ ℤ) ≪≫ Limits.sigmaConst.mapIso (λ_ M)

/-- **Coefficient extension of the normalized chain complex.**  For a simplicial set `X` and a
`ℤ`-module `M`, the normalized chain complex `X.normalizedChainComplex M` (the coproduct, in
degree `n`, of one copy of `M` for each nondegenerate `n`-simplex of `X`, with the alternating face
differential) is the coefficient extension of the normalized chain complex with `ℤ`-coefficients:
`X.normalizedChainComplex M ≅ expTens (X.normalizedChainComplex ℤ) M`. -/
theorem normalizedCoeffIso (X : SSet) (M : ModuleCat ℤ) :
    Nonempty (X.normalizedChainComplex M ≅
      Work.SSS.expTens (X.normalizedChainComplex (ModuleCat.of ℤ ℤ)) M) := by
  obtain ⟨γ⟩ := sigmaConstTensorIso M
  exact ⟨normCoeff_coeffIso X M γ⟩

end

end Work.SSS
