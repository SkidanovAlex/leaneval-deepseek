import Mathlib


/-!
# The unit of the right derived functor at a complex of acyclic objects

Let `F : C ⥤ D` be an additive, left exact functor between abelian categories, `C` having
enough injectives, and let `K` be a bounded below cochain complex of `C` all of whose terms
are `F`-acyclic.  Then the unit `F.rightDerivedFunctorPlusUnit.app K` of the right derived
functor of `F` is an isomorphism.

The proof proceeds by the classical induction on naive truncations:

* the unit is an isomorphism at the one-term complex `A[n]` whenever `A` is `F`-acyclic
  (`unit_isIso_of_isZero_rightDerived`, transported along the shift);
* the naive truncation short exact sequence `σ_{≥n}K → K → σ_{≤n-1}K` is degreewise split,
  hence yields a distinguished triangle in the bounded below homotopy category
  (`Work.DSEQ0.sesTriangle`), and the five lemma together with the long exact sequence of
  the triangle finishes the induction.
-/

namespace Work.DSEQ0

universe u v w x

open CategoryTheory CategoryTheory.Limits

namespace TA

open scoped Classical

variable {C : Type*} [Category* C] [Abelian C]

/-! ## Auxiliary lemmas about the embeddings `up ℕ → up ℤ` -/

lemma embeddingUpIntGE_f (n : ℤ) (a : ℕ) :
    (ComplexShape.embeddingUpIntGE n).f a = n + a := rfl

lemma embeddingUpIntLE_f (n : ℤ) (a : ℕ) :
    (ComplexShape.embeddingUpIntLE (n - 1)).f a = (n - 1) - a := rfl

lemma embeddingUpIntGE_arith (n i : ℤ) (h : n ≤ i) :
    (ComplexShape.embeddingUpIntGE n).f (i - n).toNat = i := by
  rw [embeddingUpIntGE_f, Int.toNat_of_nonneg (by omega)]
  omega

lemma embeddingUpIntLE_arith (n i : ℤ) (h : i ≤ n - 1) :
    (ComplexShape.embeddingUpIntLE (n - 1)).f (n - 1 - i).toNat = i := by
  rw [embeddingUpIntLE_f, Int.toNat_of_nonneg (by omega)]
  omega

/-- The complex `σ_{≤ n-1} K` is zero in degrees `≥ n`. -/
lemma isZero_stupidTrunc_LE (K : CochainComplex C ℤ) {n i : ℤ} (h : n ≤ i) :
    IsZero ((K.stupidTrunc (ComplexShape.embeddingUpIntLE (n - 1))).X i) :=
  K.isZero_stupidTrunc_X _ i (by
    rw [ComplexShape.notMem_range_embeddingUpIntLE_iff]
    omega)

/-- The complex `σ_{≥ n} K` is zero in degrees `< n`. -/
lemma isZero_stupidTrunc_GE (K : CochainComplex C ℤ) {n i : ℤ} (h : i < n) :
    IsZero ((K.stupidTrunc (ComplexShape.embeddingUpIntGE n)).X i) :=
  K.isZero_stupidTrunc_X _ i (by
    rw [ComplexShape.notMem_range_embeddingUpIntGE_iff]
    omega)

/-- `σ_{≤ n-1} K` is bounded below as soon as `K` is bounded below in degree `m ≤ n`. -/
lemma isStrictlyGE_stupidTrunc_LE' (K : CochainComplex C ℤ) (n m : ℤ) [K.IsStrictlyGE m] :
    CochainComplex.IsStrictlyGE (K.stupidTrunc (ComplexShape.embeddingUpIntLE (n - 1)))
      (min m n) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  have hi1 : i < m := lt_of_lt_of_le hi (min_le_left _ _)
  have hi2 : i ≤ n - 1 := by
    have : i < n := lt_of_lt_of_le hi (min_le_right _ _)
    omega
  exact IsZero.of_iso (K.isZero_of_isStrictlyGE m i hi1)
    (K.stupidTruncXIso (ComplexShape.embeddingUpIntLE (n - 1))
      (embeddingUpIntLE_arith n i hi2))

/-! ## The inclusion `σ_{≥ n} K ⟶ K` and the projection `K ⟶ σ_{≤ n-1} K` -/

/-- The degree-`i` component of the projection `K ⟶ σ_{≤ n-1} K`. -/
noncomputable def truncProjF (K : CochainComplex C ℤ) (n : ℤ) (i : ℤ) :
    K.X i ⟶ (K.stupidTrunc (ComplexShape.embeddingUpIntLE (n - 1))).X i :=
  if h : i ≤ n - 1 then
    (K.restrictionXIso (ComplexShape.embeddingUpIntLE (n - 1))
        (embeddingUpIntLE_arith n i h)).inv ≫
      ((K.restriction (ComplexShape.embeddingUpIntLE (n - 1))).extendXIso
        (ComplexShape.embeddingUpIntLE (n - 1)) (embeddingUpIntLE_arith n i h)).inv
    else 0

/-- The degree-`i` component of the inclusion `σ_{≥ n} K ⟶ K`. -/
noncomputable def truncInclF (K : CochainComplex C ℤ) (n : ℤ) (i : ℤ) :
    (K.stupidTrunc (ComplexShape.embeddingUpIntGE n)).X i ⟶ K.X i :=
  if h : n ≤ i then
    ((K.restriction (ComplexShape.embeddingUpIntGE n)).extendXIso
        (ComplexShape.embeddingUpIntGE n) (embeddingUpIntGE_arith n i h)).hom ≫
      (K.restrictionXIso (ComplexShape.embeddingUpIntGE n)
        (embeddingUpIntGE_arith n i h)).hom
    else 0

/-- The canonical projection `K ⟶ σ_{≤ n-1} K`. -/
noncomputable def truncProj (K : CochainComplex C ℤ) (n : ℤ) :
    K ⟶ K.stupidTrunc (ComplexShape.embeddingUpIntLE (n - 1)) :=
  HomologicalComplex.Hom.mk (truncProjF K n) (by
    intro i j hij
    dsimp only [truncProjF]
    by_cases hi : i ≤ n - 1
    · rw [dite_eq_left hi]
      by_cases hj : j ≤ n - 1
      · rw [dite_eq_left hj]
        dsimp only [HomologicalComplex.stupidTrunc]
        rw [HomologicalComplex.extend_d_eq (K.restriction (ComplexShape.embeddingUpIntLE (n - 1)))
              (ComplexShape.embeddingUpIntLE (n - 1))
              (i := (n - 1 - i).toNat) (j := (n - 1 - j).toNat)
              (embeddingUpIntLE_arith n i hi) (embeddingUpIntLE_arith n j hj)]
        rw [HomologicalComplex.restriction_d_eq K (ComplexShape.embeddingUpIntLE (n - 1))
              (i := (n - 1 - i).toNat) (j := (n - 1 - j).toNat)
              (embeddingUpIntLE_arith n i hi) (embeddingUpIntLE_arith n j hj)]
        simp only [Category.assoc, Iso.inv_hom_id, Iso.hom_inv_id,
          Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc, Category.comp_id, Category.id_comp]
      · rw [dite_eq_right hj, comp_zero]
        have hj' : n ≤ j := by
          simp only [ComplexShape.up, ComplexShape.up'] at hij
          omega
        exact (isZero_stupidTrunc_LE K hj').eq_of_tgt _ 0
    · rw [dite_eq_right hi]
      have hj : ¬ j ≤ n - 1 := by
        simp only [ComplexShape.up, ComplexShape.up'] at hij
        omega
      rw [dite_eq_right hj, zero_comp, comp_zero])

/-- The canonical inclusion `σ_{≥ n} K ⟶ K`. -/
noncomputable def truncIncl (K : CochainComplex C ℤ) (n : ℤ) :
    K.stupidTrunc (ComplexShape.embeddingUpIntGE n) ⟶ K :=
  HomologicalComplex.Hom.mk (truncInclF K n) (by
    intro i j hij
    dsimp only [truncInclF]
    by_cases hi : n ≤ i
    · rw [dite_eq_left hi]
      have hj : n ≤ j := by
        simp only [ComplexShape.up, ComplexShape.up'] at hij
        omega
      rw [dite_eq_left hj]
      dsimp only [HomologicalComplex.stupidTrunc]
      rw [HomologicalComplex.extend_d_eq (K.restriction (ComplexShape.embeddingUpIntGE n))
            (ComplexShape.embeddingUpIntGE n) (i := (i - n).toNat) (j := (j - n).toNat)
            (embeddingUpIntGE_arith n i hi) (embeddingUpIntGE_arith n j hj)]
      rw [HomologicalComplex.restriction_d_eq K (ComplexShape.embeddingUpIntGE n)
            (i := (i - n).toNat) (j := (j - n).toNat)
            (embeddingUpIntGE_arith n i hi) (embeddingUpIntGE_arith n j hj)]
      simp only [Category.assoc, Iso.inv_hom_id, Iso.hom_inv_id,
        Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc, Category.comp_id, Category.id_comp]
    · rw [dite_eq_right hi, zero_comp]
      have hz : IsZero ((K.stupidTrunc (ComplexShape.embeddingUpIntGE n)).X i) :=
        isZero_stupidTrunc_GE K (by omega)
      exact (hz.eq_of_src _ 0).symm)

lemma truncProj_f (K : CochainComplex C ℤ) (n : ℤ) (i : ℤ) :
    (truncProj K n).f i = truncProjF K n i := rfl

lemma truncIncl_f (K : CochainComplex C ℤ) (n : ℤ) (i : ℤ) :
    (truncIncl K n).f i = truncInclF K n i := rfl

lemma truncProjF_eq (K : CochainComplex C ℤ) (n : ℤ) {i : ℤ} (h : i ≤ n - 1) :
    truncProjF K n i =
      (K.restrictionXIso (ComplexShape.embeddingUpIntLE (n - 1))
          (embeddingUpIntLE_arith n i h)).inv ≫
        ((K.restriction (ComplexShape.embeddingUpIntLE (n - 1))).extendXIso
          (ComplexShape.embeddingUpIntLE (n - 1)) (embeddingUpIntLE_arith n i h)).inv :=
  dite_eq_left h

lemma truncInclF_eq (K : CochainComplex C ℤ) (n : ℤ) {i : ℤ} (h : n ≤ i) :
    truncInclF K n i =
      ((K.restriction (ComplexShape.embeddingUpIntGE n)).extendXIso
          (ComplexShape.embeddingUpIntGE n) (embeddingUpIntGE_arith n i h)).hom ≫
        (K.restrictionXIso (ComplexShape.embeddingUpIntGE n)
          (embeddingUpIntGE_arith n i h)).hom :=
  dite_eq_left h

lemma isIso_truncIncl_f (K : CochainComplex C ℤ) (n : ℤ) {i : ℤ} (h : n ≤ i) :
    IsIso ((truncIncl K n).f i) := by
  rw [truncIncl_f K n i, truncInclF_eq K n h]
  exact Iso.isIso_hom (((K.restriction (ComplexShape.embeddingUpIntGE n)).extendXIso
      (ComplexShape.embeddingUpIntGE n) (embeddingUpIntGE_arith n i h)) ≪≫
    (K.restrictionXIso (ComplexShape.embeddingUpIntGE n) (embeddingUpIntGE_arith n i h)))

lemma isIso_truncProj_f (K : CochainComplex C ℤ) (n : ℤ) {i : ℤ} (h : i ≤ n - 1) :
    IsIso ((truncProj K n).f i) := by
  rw [truncProj_f K n i, truncProjF_eq K n h]
  exact Iso.isIso_hom (((K.restrictionXIso (ComplexShape.embeddingUpIntLE (n - 1))
      (embeddingUpIntLE_arith n i h)).symm) ≪≫
    (((K.restriction (ComplexShape.embeddingUpIntLE (n - 1))).extendXIso
      (ComplexShape.embeddingUpIntLE (n - 1)) (embeddingUpIntLE_arith n i h)).symm))

lemma truncIncl_comp_truncProj (K : CochainComplex C ℤ) (n : ℤ) :
    truncIncl K n ≫ truncProj K n = 0 := by
  ext i
  by_cases h : n ≤ i
  · exact (isZero_stupidTrunc_LE K h).eq_of_tgt _ 0
  · exact (isZero_stupidTrunc_GE K (by omega)).eq_of_src _ 0

/-! ## The naive truncation short exact sequence -/

/-- The naive truncation short exact sequence `σ_{≥ n} K ⟶ K ⟶ σ_{≤ n-1} K` of a bounded
below complex, degreewise split. -/
theorem truncSES (K : CochainComplex.Plus C) (n : ℤ) :
    ∃ (S : ShortComplex (CochainComplex.Plus C))
      (σ : ∀ i : ℤ, ((S.map (CochainComplex.Plus.ι C)).map
        (HomologicalComplex.eval C (ComplexShape.up ℤ) i)).Splitting),
      S.X₂ = K ∧
      (∀ i : ℤ, i < n → IsZero ((S.X₁).obj.X i)) ∧
      (∀ i : ℤ, n ≤ i → Nonempty ((S.X₁).obj.X i ≅ K.obj.X i)) ∧
      (∀ i : ℤ, n ≤ i → IsZero ((S.X₃).obj.X i)) ∧
      (∀ i : ℤ, i ≤ n - 1 → Nonempty ((S.X₃).obj.X i ≅ K.obj.X i)) ∧
      (∀ i : ℤ, i ≤ n - 1 → IsIso ((S.g).hom.f i)) := by
  classical
  obtain ⟨m₀, hm₀⟩ := K.2
  let A : CochainComplex.Plus C :=
    ⟨K.obj.stupidTrunc (ComplexShape.embeddingUpIntGE n), ⟨n, by
      rw [CochainComplex.isStrictlyGE_iff]
      intro i hi
      exact isZero_stupidTrunc_GE K.obj hi⟩⟩
  let B : CochainComplex.Plus C :=
    ⟨K.obj.stupidTrunc (ComplexShape.embeddingUpIntLE (n - 1)),
      ⟨min m₀ n, by
        haveI := hm₀
        exact isStrictlyGE_stupidTrunc_LE' K.obj n m₀⟩⟩
  let f : A ⟶ K := ObjectProperty.homMk (truncIncl K.obj n)
  let g : K ⟶ B := ObjectProperty.homMk (truncProj K.obj n)
  have hfg : f ≫ g = 0 :=
    ObjectProperty.hom_ext (CochainComplex.plus C) (by
      rw [ObjectProperty.FullSubcategory.comp_hom]
      exact truncIncl_comp_truncProj K.obj n)
  let S : ShortComplex (CochainComplex.Plus C) := ShortComplex.mk f g hfg
  let σ : ∀ i : ℤ, ((S.map (CochainComplex.Plus.ι C)).map
      (HomologicalComplex.eval C (ComplexShape.up ℤ) i)).Splitting := by
    intro i
    by_cases h : n ≤ i
    · haveI hf : IsIso (((S.map (CochainComplex.Plus.ι C)).map
          (HomologicalComplex.eval C (ComplexShape.up ℤ) i)).f) :=
        isIso_truncIncl_f K.obj n h
      haveI hz : IsZero (((S.map (CochainComplex.Plus.ι C)).map
          (HomologicalComplex.eval C (ComplexShape.up ℤ) i)).X₃) :=
        isZero_stupidTrunc_LE K.obj h
      exact
        { r := inv (((S.map (CochainComplex.Plus.ι C)).map
              (HomologicalComplex.eval C (ComplexShape.up ℤ) i)).f)
          s := 0
          f_r := IsIso.hom_inv_id _
          s_g := hz.eq_of_tgt _ _
          id := by rw [comp_zero, add_zero, IsIso.inv_hom_id] }
    · have hi : i ≤ n - 1 := by omega
      haveI hg : IsIso (((S.map (CochainComplex.Plus.ι C)).map
          (HomologicalComplex.eval C (ComplexShape.up ℤ) i)).g) :=
        isIso_truncProj_f K.obj n hi
      haveI hz : IsZero (((S.map (CochainComplex.Plus.ι C)).map
          (HomologicalComplex.eval C (ComplexShape.up ℤ) i)).X₁) :=
        isZero_stupidTrunc_GE K.obj (by omega)
      exact
        { r := 0
          s := inv (((S.map (CochainComplex.Plus.ι C)).map
              (HomologicalComplex.eval C (ComplexShape.up ℤ) i)).g)
          f_r := hz.eq_of_tgt _ _
          s_g := IsIso.inv_hom_id _
          id := by rw [zero_comp, zero_add, IsIso.hom_inv_id] }
  refine ⟨S, σ, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact isZero_stupidTrunc_GE K.obj hi
  · intro i hi
    exact ⟨K.obj.stupidTruncXIso (ComplexShape.embeddingUpIntGE n)
      (embeddingUpIntGE_arith n i hi)⟩
  · intro i hi
    exact isZero_stupidTrunc_LE K.obj hi
  · intro i hi
    exact ⟨K.obj.stupidTruncXIso (ComplexShape.embeddingUpIntLE (n - 1))
      (embeddingUpIntLE_arith n i hi)⟩
  · intro i hi
    exact isIso_truncProj_f K.obj n hi

open CategoryTheory Limits Pretriangulated

/-- A degreewise split short complex of bounded below cochain complexes gives a distinguished
triangle in the bounded below homotopy category. -/
theorem sesTriangle {C : Type*} [Category* C] [Preadditive C]
    [Limits.HasZeroObject C] [Limits.HasBinaryBiproducts C]
    (S : ShortComplex (CochainComplex.Plus C))
    (σ : ∀ n : ℤ, ((S.map (CochainComplex.Plus.ι C)).map
      (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).Splitting) :
    ∃ δ : (HomotopyCategory.Plus.quotient C).obj S.X₃ ⟶
        (CategoryTheory.shiftFunctor (HomotopyCategory.Plus C) (1 : ℤ)).obj
          ((HomotopyCategory.Plus.quotient C).obj S.X₁),
      Triangle.mk ((HomotopyCategory.Plus.quotient C).map S.f)
        ((HomotopyCategory.Plus.quotient C).map S.g) δ ∈ distTriang _ := by
  let S' := S.map (CochainComplex.Plus.ι C)
  let σ' : ∀ n : ℤ, (S'.map (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).Splitting := σ
  let Q := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  let T' : Triangle (HomotopyCategory C (ComplexShape.up ℤ)) :=
    Triangle.mk (Q.map S'.f) (Q.map S'.g)
      (Q.map (CochainComplex.homOfDegreewiseSplit S' σ') ≫
        (Functor.commShiftIso Q (1 : ℤ)).hom.app S'.X₁)
  have hT' : T' ∈ distTriang (HomotopyCategory C (ComplexShape.up ℤ)) :=
    CochainComplex.trianglehOfDegreewiseSplit_distinguished S' σ'
  let δ : (HomotopyCategory.Plus.quotient C).obj S.X₃ ⟶
      (CategoryTheory.shiftFunctor (HomotopyCategory.Plus C) (1 : ℤ)).obj
        ((HomotopyCategory.Plus.quotient C).obj S.X₁) :=
    (HomotopyCategory.Plus.ι C).preimage
      (T'.mor₃ ≫ ((HomotopyCategory.Plus.ι C).commShiftIso (1 : ℤ)).inv.app
        ((HomotopyCategory.Plus.quotient C).obj S.X₁))
  have hδ : (HomotopyCategory.Plus.ι C).map δ =
      T'.mor₃ ≫ ((HomotopyCategory.Plus.ι C).commShiftIso (1 : ℤ)).inv.app
        ((HomotopyCategory.Plus.quotient C).obj S.X₁) := by
    dsimp only [δ]
    rw [Functor.map_preimage]
  refine ⟨δ, ?_⟩
  rw [← (HomotopyCategory.Plus.ι C).map_distinguished_iff]
  let T₂ : Triangle (HomotopyCategory C (ComplexShape.up ℤ)) :=
    Triangle.mk (Q.map S'.f) (Q.map S'.g)
      ((HomotopyCategory.Plus.ι C).map δ ≫
        (Functor.commShiftIso (HomotopyCategory.Plus.ι C) (1 : ℤ)).hom.app
          ((HomotopyCategory.Plus.quotient C).obj S.X₁))
  refine isomorphic_distinguished T' hT' T₂ ?_
  refine Triangle.isoMk T₂ T' (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · rw [show (Iso.refl T₂.obj₂).hom = 𝟙 T₂.obj₂ from rfl,
        show (Iso.refl T₂.obj₁).hom = 𝟙 T₂.obj₁ from rfl,
        Category.comp_id, Category.id_comp]
    rfl
  · rw [show (Iso.refl T₂.obj₃).hom = 𝟙 T₂.obj₃ from rfl,
        show (Iso.refl T₂.obj₂).hom = 𝟙 T₂.obj₂ from rfl,
        Category.comp_id, Category.id_comp]
    rfl
  · rw [show (Iso.refl T₂.obj₁).hom = 𝟙 T₂.obj₁ from rfl,
        CategoryTheory.Functor.map_id,
        show (Iso.refl T₂.obj₃).hom = 𝟙 T₂.obj₃ from rfl,
        Category.comp_id, Category.id_comp]
    show (HomotopyCategory.Plus.ι C).map δ ≫
      (Functor.commShiftIso (HomotopyCategory.Plus.ι C) (1 : ℤ)).hom.app
        ((HomotopyCategory.Plus.quotient C).obj S.X₁) = T'.mor₃
    rw [hδ, Category.assoc, Iso.inv_hom_id_app]
    exact Category.comp_id T'.mor₃


end TA

end Work.DSEQ0
