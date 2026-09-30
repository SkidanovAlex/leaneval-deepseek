import Mathlib
import Submission.Work.SSSR.ExpTens
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

set_option autoImplicit false

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory
open MonoidalCategory
noncomputable section

/-- The chain complex concentrated in degree `0` at `M`: the complex `single₀ M` used in the
definition of `Work.SSSR.tensorComplex`. -/
abbrev singleCoeff (M : ModuleCat R) : ChainComplex (ModuleCat R) ℕ :=
  (single (ModuleCat R) (ComplexShape.down ℕ) 0).obj M

/-- `Work.SSSR.tensorComplex K M` written as the total complex `mapBifunctor K (single₀ M) ⊗`, on
which the API of `HomologicalComplex.mapBifunctor` applies directly.  It is *definitionally*
equal to `Work.SSSR.tensorComplex K M`. -/
abbrev tensorSingle (K : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) :
    ChainComplex (ModuleCat R) ℕ :=
  mapBifunctor K (singleCoeff M) (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ)

/-- The component of the collapse morphism `(K ⊗ S).X n ⟶ K.X n ⊗ M` on the summand indexed by
`(i,j)` with `i + j = n`: the canonical map on the summand with `j = 0`, and zero otherwise
(the other summands are zero objects). -/
def collapseComp (K : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) (n : ℕ) (i j : ℕ)
    (h : ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ) (i, j) = n) :
    K.X i ⊗ (singleCoeff M).X j ⟶ K.X n ⊗ M :=
  if hj : j = 0 then
    (K.X i ◁ (singleObjXIsoOfEq (ComplexShape.down ℕ) 0 M j hj).hom) ≫
      eqToHom (congrArg (fun k => K.X k ⊗ M) (by have h' : i + j = n := h; omega))
  else 0

/-- The collapse morphism in degree `n`: `(K ⊗ single₀ M).X n ⟶ K.X n ⊗ M`. -/
def collapseX (K : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) (n : ℕ) :
    (tensorSingle K M).X n ⟶ K.X n ⊗ M :=
  mapBifunctorDesc (fun i j h => collapseComp K M n i j h)

/-- The inclusion of the `(n,0)` summand: `K.X n ⊗ M ⟶ (K ⊗ single₀ M).X n`. -/
def splitX (K : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) (n : ℕ) :
    K.X n ⊗ M ⟶ (tensorSingle K M).X n :=
  (K.X n ◁ (singleObjXSelf (ComplexShape.down ℕ) 0 M).inv) ≫
    ιMapBifunctor K (singleCoeff M) (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ) n 0 n rfl

/-- The second differential of `K ⊗ single₀ M` vanishes, because the differential of `single₀ M`
is identically zero. -/
lemma d₂_zero (K : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) (i₁ i₂ j : ℕ) :
    mapBifunctor.d₂ K (singleCoeff M) (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ) i₁ i₂ j = 0 := by
  by_cases h : (ComplexShape.down ℕ).Rel i₂ ((ComplexShape.down ℕ).next i₂)
  · rw [mapBifunctor.d₂_eq' K (singleCoeff M) (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ) i₁ h j,
      single_obj_d, Functor.map_zero, zero_comp, smul_zero]
  · rw [mapBifunctor.d₂_eq_zero K (singleCoeff M) (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ)
      i₁ i₂ j h]

/-- The first differential of `K ⊗ single₀ M` on the summand `(j+1, 0)`: it is `d ⊗ id` (there is
no sign, `ε₁ = 1`). -/
lemma d₁_val (K : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) (j : ℕ) :
    mapBifunctor.d₁ K (singleCoeff M) (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ) (j + 1) 0 j =
      (K.d (j + 1) j ▷ (singleCoeff M).X 0) ≫
        ιMapBifunctor K (singleCoeff M) (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ) j 0 j
          (show (ComplexShape.down ℕ).π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (j, 0) = j from rfl) := by
  rw [mapBifunctor.d₁_eq K (singleCoeff M) (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ)
    (show (ComplexShape.down ℕ).Rel (j + 1) j from rfl) 0 j
    (show (ComplexShape.down ℕ).π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (j, 0) = j from rfl)]
  rw [show (ComplexShape.down ℕ).ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (j + 1, 0) = 1 from rfl,
    one_smul]
  rfl

/-- `collapseX` is a retraction of `splitX`.  All the dependent casts simplify here because the
only summand which contributes is `(n,0)`, where the index equation is a definitional identity. -/
lemma collapseX_splitX (K : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) (n : ℕ) :
    collapseX K M n ≫ splitX K M n = 𝟙 _ := by
  apply mapBifunctor.hom_ext
  intro i j h
  rw [← Category.assoc, collapseX, ι_mapBifunctorDesc]
  by_cases hj : j = 0
  · subst hj
    have hi : i = n := by have h' : i + 0 = n := h; omega
    subst hi
    rw [collapseComp, dif_pos rfl]
    simp only [eqToHom_refl, Category.comp_id]
    rw [splitX]
    simp only [singleObjXIsoOfEq, singleObjXSelf, eqToIso.hom, eqToIso.inv]
    rw [← Category.assoc, ← whiskerLeft_comp, eqToHom_trans, whiskerLeft_eqToHom, eqToHom_refl]
    erw [Category.id_comp]
  · rw [collapseComp, dif_neg hj, zero_comp]
    exact (IsZero.eq_of_src (Functor.map_isZero ((curriedTensor (ModuleCat R)).obj (K.X i))
      (isZero_single_obj_X (ComplexShape.down ℕ) 0 M j hj)) _ _)

/-- `splitX` is a section of `collapseX`. -/
lemma splitX_collapseX (K : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) (n : ℕ) :
    splitX K M n ≫ collapseX K M n = 𝟙 _ := by
  rw [splitX, collapseX, Category.assoc, ι_mapBifunctorDesc]
  rw [collapseComp, dif_pos rfl]
  simp only [eqToHom_refl]
  rw [Category.comp_id]
  simp only [singleObjXIsoOfEq, singleObjXSelf, eqToIso.hom, eqToIso.inv]
  rw [← whiskerLeft_comp, eqToHom_trans, whiskerLeft_eqToHom, eqToHom_refl]

/-- Compatibility of `splitX` with the differentials: the naturality of the tensor product. -/
lemma splitX_comm (K : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) (i j : ℕ)
    (hij : (ComplexShape.down ℕ).Rel i j) :
    splitX K M i ≫ (tensorSingle K M).d i j = (expTens K M).d i j ≫ splitX K M j := by
  obtain rfl : j + 1 = i := (ComplexShape.down_Rel ℕ i j).mp hij
  rw [splitX, expTens_d]
  rw [Category.assoc]
  rw [mapBifunctor.d_eq]
  rw [Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂]
  rw [Preadditive.comp_add, d₂_zero K M, comp_zero, add_zero, d₁_val K M]
  rw [splitX]
  rw [← Category.assoc, whiskerLeft_d K (singleObjXSelf (ComplexShape.down ℕ) 0 M).inv j, Category.assoc]

/-- The morphism of complexes `expTens K M ⟶ K ⊗ single₀ M` which is the inclusion of the `(n,0)`
summand in each degree. -/
def split (K : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) :
    expTens K M ⟶ tensorSingle K M where
  f n := splitX K M n
  comm' i j hij := splitX_comm K M i j hij

end

end Work.SSSR
