import Mathlib
import Submission.Work.SSS.ExpTens

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The tensor complex `K ⊗ M` is the naive coefficient extension `expTens K M`

Let `K` be a chain complex of `ℤ`-modules and `M` a `ℤ`-module.  The complex
`Work.SSS.tensorComplex K M = K ⊗ (single₀ M)` is the total complex of the bicomplex with
`(i,j)`-term `K.X i ⊗ S.X j`, where `S = single₀ M` is concentrated in degree `0` at `M`.
Since `S` is concentrated in one degree, the coproduct describing degree `n` collapses onto the
single summand `(n,0)`, giving an isomorphism with the naive coefficient extension
`Work.SSS.expTens K M`, whose `n`-th term is `K.X n ⊗ M` with differential `K.d (n+1) n ▷ M`.

We build the isomorphism as follows.

* `collapseComp`/`collapseX`: the collapse morphism `(K ⊗ S).X n ⟶ K.X n ⊗ M`, which is the
  identity on the summand `(n,0)` and zero on the others (they are zero objects).
* `splitX`: the inverse `K.X n ⊗ M ⟶ (K ⊗ S).X n`, the inclusion of the `(n,0)` summand.
* `collapseX_splitX` : `collapseX n ≫ splitX n = 𝟙` and `splitX_collapseX` : the other
  composite is `𝟙` as well (this second one is where the dependent-index bookkeeping happens).
* `split` : the morphism of complexes `expTens K M ⟶ K ⊗ S` with components `splitX`, whose
  compatibility with the differentials is the naturality of the tensor product.
* Since all its components are isomorphisms, `split` is an isomorphism.
-/

set_option autoImplicit false

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory
open MonoidalCategory

noncomputable section

/-- The chain complex concentrated in degree `0` at `M`: the complex `single₀ M` used in the
definition of `Work.SSS.tensorComplex`. -/
abbrev singleCoeff (M : ModuleCat ℤ) : ChainComplex (ModuleCat ℤ) ℕ :=
  (single (ModuleCat ℤ) (ComplexShape.down ℕ) 0).obj M

/-- `Work.SSS.tensorComplex K M` written as the total complex `mapBifunctor K (single₀ M) ⊗`, on
which the API of `HomologicalComplex.mapBifunctor` applies directly.  It is *definitionally*
equal to `Work.SSS.tensorComplex K M`. -/
abbrev tensorSingle (K : ChainComplex (ModuleCat ℤ) ℕ) (M : ModuleCat ℤ) :
    ChainComplex (ModuleCat ℤ) ℕ :=
  mapBifunctor K (singleCoeff M) (curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ)

/-- The component of the collapse morphism `(K ⊗ S).X n ⟶ K.X n ⊗ M` on the summand indexed by
`(i,j)` with `i + j = n`: the canonical map on the summand with `j = 0`, and zero otherwise
(the other summands are zero objects). -/
def collapseComp (K : ChainComplex (ModuleCat ℤ) ℕ) (M : ModuleCat ℤ) (n : ℕ) (i j : ℕ)
    (h : ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ) (i, j) = n) :
    K.X i ⊗ (singleCoeff M).X j ⟶ K.X n ⊗ M :=
  if hj : j = 0 then
    (K.X i ◁ (singleObjXIsoOfEq (ComplexShape.down ℕ) 0 M j hj).hom) ≫
      eqToHom (congrArg (fun k => K.X k ⊗ M) (by have h' : i + j = n := h; omega))
  else 0

/-- The collapse morphism in degree `n`: `(K ⊗ single₀ M).X n ⟶ K.X n ⊗ M`. -/
def collapseX (K : ChainComplex (ModuleCat ℤ) ℕ) (M : ModuleCat ℤ) (n : ℕ) :
    (tensorSingle K M).X n ⟶ K.X n ⊗ M :=
  mapBifunctorDesc (fun i j h => collapseComp K M n i j h)

/-- The inclusion of the `(n,0)` summand: `K.X n ⊗ M ⟶ (K ⊗ single₀ M).X n`. -/
def splitX (K : ChainComplex (ModuleCat ℤ) ℕ) (M : ModuleCat ℤ) (n : ℕ) :
    K.X n ⊗ M ⟶ (tensorSingle K M).X n :=
  (K.X n ◁ (singleObjXSelf (ComplexShape.down ℕ) 0 M).inv) ≫
    ιMapBifunctor K (singleCoeff M) (curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ) n 0 n rfl

/-- Computation of the components of the collapse morphism. -/
lemma ι_collapseX (K : ChainComplex (ModuleCat ℤ) ℕ) (M : ModuleCat ℤ) (n i j : ℕ)
    (h : ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ) (i, j) = n) :
    ιMapBifunctor K (singleCoeff M) (curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ) i j n h ≫
      collapseX K M n = collapseComp K M n i j h := by
  rw [collapseX, ι_mapBifunctorDesc]

/-- The second differential of `K ⊗ single₀ M` vanishes, because the differential of `single₀ M`
is identically zero. -/
lemma d₂_zero (K : ChainComplex (ModuleCat ℤ) ℕ) (M : ModuleCat ℤ) (i₁ i₂ j : ℕ) :
    mapBifunctor.d₂ K (singleCoeff M) (curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ) i₁ i₂ j = 0 := by
  by_cases h : (ComplexShape.down ℕ).Rel i₂ ((ComplexShape.down ℕ).next i₂)
  · rw [mapBifunctor.d₂_eq' K (singleCoeff M) (curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ) i₁ h j,
      single_obj_d, Functor.map_zero, zero_comp, smul_zero]
  · rw [mapBifunctor.d₂_eq_zero K (singleCoeff M) (curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ)
      i₁ i₂ j h]

/-- The first differential of `K ⊗ single₀ M` on the summand `(j+1, 0)`: it is `d ⊗ id` (there is
no sign, `ε₁ = 1`). -/
lemma d₁_val (K : ChainComplex (ModuleCat ℤ) ℕ) (M : ModuleCat ℤ) (j : ℕ) :
    mapBifunctor.d₁ K (singleCoeff M) (curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ) (j + 1) 0 j =
      (K.d (j + 1) j ▷ (singleCoeff M).X 0) ≫
        ιMapBifunctor K (singleCoeff M) (curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ) j 0 j
          (show (ComplexShape.down ℕ).π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (j, 0) = j from rfl) := by
  rw [mapBifunctor.d₁_eq K (singleCoeff M) (curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ)
    (show (ComplexShape.down ℕ).Rel (j + 1) j from rfl) 0 j
    (show (ComplexShape.down ℕ).π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (j, 0) = j from rfl)]
  rw [show (ComplexShape.down ℕ).ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (j + 1, 0) = 1 from rfl,
    one_smul]
  rfl

/-- `collapseX` is a retraction of `splitX`.  All the dependent casts simplify here because the
only summand which contributes is `(n,0)`, where the index equation is a definitional identity. -/
lemma collapseX_splitX (K : ChainComplex (ModuleCat ℤ) ℕ) (M : ModuleCat ℤ) (n : ℕ) :
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
    exact (IsZero.eq_of_src (Functor.map_isZero ((curriedTensor (ModuleCat ℤ)).obj (K.X i))
      (isZero_single_obj_X (ComplexShape.down ℕ) 0 M j hj)) _ _)

/-- `splitX` is a section of `collapseX`. -/
lemma splitX_collapseX (K : ChainComplex (ModuleCat ℤ) ℕ) (M : ModuleCat ℤ) (n : ℕ) :
    splitX K M n ≫ collapseX K M n = 𝟙 _ := by
  rw [splitX, collapseX, Category.assoc, ι_mapBifunctorDesc]
  rw [collapseComp, dif_pos rfl]
  simp only [eqToHom_refl]
  rw [Category.comp_id]
  simp only [singleObjXIsoOfEq, singleObjXSelf, eqToIso.hom, eqToIso.inv]
  rw [← whiskerLeft_comp, eqToHom_trans, whiskerLeft_eqToHom, eqToHom_refl]

/-- Compatibility of `splitX` with the differentials: the naturality of the tensor product. -/
lemma splitX_comm (K : ChainComplex (ModuleCat ℤ) ℕ) (M : ModuleCat ℤ) (i j : ℕ)
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
def split (K : ChainComplex (ModuleCat ℤ) ℕ) (M : ModuleCat ℤ) :
    expTens K M ⟶ tensorSingle K M where
  f n := splitX K M n
  comm' i j hij := splitX_comm K M i j hij

@[simp]
lemma split_f (K : ChainComplex (ModuleCat ℤ) ℕ) (M : ModuleCat ℤ) (n : ℕ) :
    (split K M).f n = splitX K M n := rfl

/-- The tensor complex `K ⊗ M` of a chain complex `K` with the complex concentrated in degree `0`
at a module `M` is isomorphic to the "naive" coefficient extension `expTens K M` (whose `n`-th term
is `K.X n ⊗ M` with differential `K.d (n+1) n ⊗ 𝟙 M`). -/
theorem tensorComplexIsoExpTens (K : ChainComplex (ModuleCat ℤ) ℕ) (M : ModuleCat ℤ) :
    Nonempty (Work.SSS.tensorComplex K M ≅ Work.SSS.expTens K M) := by
  haveI : ∀ n, IsIso ((split K M).f n) := fun n =>
    ⟨collapseX K M n, splitX_collapseX K M n, collapseX_splitX K M n⟩
  haveI : IsIso (split K M) := HomologicalComplex.Hom.isIso_of_components _
  exact ⟨(asIso (split K M)).symm⟩

end

end Work.SSS
