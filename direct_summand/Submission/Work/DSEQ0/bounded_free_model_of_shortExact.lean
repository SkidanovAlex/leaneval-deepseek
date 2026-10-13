import Mathlib
import Submission.Work.DSEQ0.Model
import Submission.Work.DSEQ0.exists_lift_of_quasiIso

namespace Work.DSEQ0

universe u

open CategoryTheory Limits Pretriangulated

set_option linter.style.haveILetI false

section TriangleAux

variable {C : Type*} [Category* C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- In a pretriangulated category, the first object of a distinguished triangle is determined
up to isomorphism by the triangle: two distinguished triangles whose second and third objects
are identified in a way compatible with `mor₂` have isomorphic first objects.

This is the "uniqueness of the fibre" statement: `mor₁` is the fibre of `mor₂`.  It is proved
with the five lemma for morphisms of triangles (`isIso₁_of_isIso₂₃`), the morphism of triangles
being produced by `complete_distinguished_triangle_morphism₁`. -/
noncomputable def iso_obj₁_of_distinguished {T₁ T₂ : Triangle C}
    (h₁ : T₁ ∈ distTriang C) (h₂ : T₂ ∈ distTriang C)
    (e₂ : T₁.obj₂ ≅ T₂.obj₂) (e₃ : T₁.obj₃ ≅ T₂.obj₃)
    (comm : T₁.mor₂ ≫ e₃.hom = e₂.hom ≫ T₂.mor₂) :
    T₁.obj₁ ≅ T₂.obj₁ := by
  classical
  let h := complete_distinguished_triangle_morphism₁ T₁ T₂ h₁ h₂ e₂.hom e₃.hom comm
  let φ : T₁ ⟶ T₂ :=
    { hom₁ := Classical.choose h
      hom₂ := e₂.hom
      hom₃ := e₃.hom
      comm₁ := (Classical.choose_spec h).1
      comm₂ := comm
      comm₃ := (Classical.choose_spec h).2 }
  haveI hφ₂ : IsIso φ.hom₂ := by change IsIso e₂.hom; infer_instance
  haveI hφ₃ : IsIso φ.hom₃ := by change IsIso e₃.hom; infer_instance
  haveI hφ₁ : IsIso φ.hom₁ := isIso₁_of_isIso₂₃ φ h₁ h₂ hφ₂ hφ₃
  exact asIso φ.hom₁

end TriangleAux

section Terms

variable {A : Type u} [CommRing A]

/-- The `i`-th term of the mapping cocone of `ψ : K ⟶ L⟦1⟧` is (up to isomorphism) the product
of the corresponding terms of `K` and `L`.  Since `(mappingCocone ψ).X i` is
`(mappingCone ψ).X (i - 1)` and the terms of the mapping cone are biproducts, this is the
biproduct `K.X ((i-1)+1) ⊞ L.X ((i-1)+1)`, rewritten as a product of modules. -/
noncomputable def mappingCocone_X_iso (K L : CochainComplex (ModuleCat.{u} A) ℤ)
    (ψ : K ⟶ L⟦(1 : ℤ)⟧) (i : ℤ) :
    (CochainComplex.mappingCocone ψ).X i ≅
      ModuleCat.of A (K.X ((i + (-1)) + 1) × L.X ((i + (-1)) + 1)) :=
  (HomologicalComplex.homotopyCofiber.XIsoBiprod ψ (i + (-1)) ((i + (-1)) + 1)
      (ComplexShape.up_mk _ _ (by ring))).trans
    (ModuleCat.biprodIsoProd (K.X ((i + (-1)) + 1)) ((L⟦(1 : ℤ)⟧).X (i + (-1))))

end Terms

/-- **The crux of the model construction (area `EQ0`).**  Given a short exact sequence
`0 → S.X₁ → S.X₂ → S.X₃ → 0` of cochain complexes of `A`-modules, together with bounded models
of finite free modules `Q → S.X₁` and `F → S.X₃` (quasi-isomorphisms), the middle term `S.X₂`
also has a bounded model of finite free modules.  The model is the (co)cone of a lift of the
connecting map `S.X₃ ⟶ S.X₁⟦1⟧`, which exists because `F` is K-projective: bounded-above with
free terms.  This is the induction step of "a complex whose cohomology has finite free
resolutions has a bounded finite free model" — the input that `DSMap.area_COH` plus finite
projective dimension over a regular local ring provide. -/
theorem bounded_free_model_of_shortExact {A : Type u} [CommRing A]
    (S : CategoryTheory.ShortComplex (CochainComplex (ModuleCat.{u} A) ℤ))
    (hS : CategoryTheory.ShortComplex.ShortExact S)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ) (q : Q ⟶ S.X₁) (hq : QuasiIso q)
    (hQfin : ∀ j, Module.Finite A (Q.X j)) (hQfree : ∀ j, Module.Free A (Q.X j))
    (hQbdd : ∃ a b : ℤ, ∀ j, j < a ∨ b < j → CategoryTheory.Limits.IsZero (Q.X j))
    (F : CochainComplex (ModuleCat.{u} A) ℤ) (f : F ⟶ S.X₃) (hf : QuasiIso f)
    (hFfin : ∀ j, Module.Finite A (F.X j)) (hFfree : ∀ j, Module.Free A (F.X j))
    (hFbdd : ∃ a b : ℤ, ∀ j, j < a ∨ b < j → CategoryTheory.Limits.IsZero (F.X j)) :
    ∃ (P : CochainComplex (ModuleCat.{u} A) ℤ),
      (∀ j, Module.Finite A (P.X j)) ∧ (∀ j, Module.Free A (P.X j)) ∧
      (∃ a b : ℤ, ∀ j, j < a ∨ b < j → CategoryTheory.Limits.IsZero (P.X j)) ∧
      ∃ q' : P ⟶ S.X₂, QuasiIso q' := by
  -- We work in the derived category of `A`-modules (any instance will do).
  letI : HasDerivedCategory (ModuleCat.{u} A) := HasDerivedCategory.standard _
  haveI : QuasiIso q := hq
  haveI : QuasiIso f := hf
  obtain ⟨aF, bF, hFbdd'⟩ := hFbdd
  obtain ⟨aQ, bQ, hQbdd'⟩ := hQbdd
  -- `F` is bounded above with free (hence projective) terms, so it is K-projective.
  haveI hFle : F.IsStrictlyLE bF :=
    (CochainComplex.isStrictlyLE_iff F bF).mpr (fun i hi => hFbdd' i (Or.inr hi))
  haveI hFproj : CochainComplex.IsKProjective F :=
    CochainComplex.isKProjective_of_projective F bF
  -- The isomorphisms of the derived category identifying the models with the terms of `S`.
  let e₂ : DerivedCategory.Q.obj S.X₃ ≅ DerivedCategory.Q.obj F :=
    (asIso (DerivedCategory.Q.map f)).symm
  let e₃ : (DerivedCategory.Q.obj S.X₁)⟦(1 : ℤ)⟧ ≅ DerivedCategory.Q.obj (Q⟦(1 : ℤ)⟧) :=
    ((shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (1 : ℤ)).mapIso
        (asIso (DerivedCategory.Q.map q))).symm ≪≫
      ((DerivedCategory.Q.commShiftIso (1 : ℤ)).app Q).symm
  -- The connecting map `S.X₃ ⟶ S.X₁⟦1⟧` of the short exact sequence, transported to the
  -- models.  Since `F` is K-projective, this morphism of the derived category is represented
  -- by an honest chain map `ψ : F ⟶ Q⟦1⟧`.
  obtain ⟨ψ, hψ⟩ :=
    Q_map_surjective_of_isKProjective (A := A) (K := F) (Q⟦(1 : ℤ)⟧)
      (e₂.inv ≫ DerivedCategory.triangleOfSESδ hS ≫ e₃.hom)
  -- The rotated triangle of the short exact sequence and the mapping cocone triangle of `ψ`
  -- have the same `mor₂`; this identifies their first objects.
  have hT₁ : (DerivedCategory.triangleOfSES hS).rotate ∈
      distTriang (DerivedCategory (ModuleCat.{u} A)) :=
    rot_of_distTriang _ (DerivedCategory.triangleOfSES_distinguished hS)
  have hT₂ : DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCocone.triangle ψ) ∈
      distTriang (DerivedCategory (ModuleCat.{u} A)) :=
    DerivedCategory.mappingCocone_triangle_distinguished ψ
  have comm : DerivedCategory.triangleOfSESδ hS ≫ e₃.hom =
      e₂.hom ≫ DerivedCategory.Q.map ψ := by
    rw [hψ]
    calc DerivedCategory.triangleOfSESδ hS ≫ e₃.hom
        = (e₂.hom ≫ e₂.inv) ≫ (DerivedCategory.triangleOfSESδ hS ≫ e₃.hom) := by
          rw [e₂.hom_inv_id, Category.id_comp]
      _ = e₂.hom ≫ (e₂.inv ≫ DerivedCategory.triangleOfSESδ hS ≫ e₃.hom) := by
          simp only [Category.assoc]
  have e : DerivedCategory.Q.obj S.X₂ ≅
      DerivedCategory.Q.obj (CochainComplex.mappingCocone ψ) :=
    iso_obj₁_of_distinguished hT₁ hT₂ e₂ e₃ comm
  -- The model of `S.X₂` is the mapping cocone of `ψ`.
  let P : CochainComplex (ModuleCat.{u} A) ℤ := CochainComplex.mappingCocone ψ
  -- Its terms are the products `F.X j × Q.X j`, hence finite free, and it is bounded.
  have hzP : ∀ j, (j < aF ∨ bF < j) → (j < aQ ∨ bQ < j) → IsZero (P.X j) := by
    intro j hjF hjQ
    have hidx : (j + (-1)) + 1 = j := by ring
    have h₁ : IsZero (F.X ((j + (-1)) + 1)) := by
      rw [hidx]; exact hFbdd' j hjF
    have h₂ : IsZero (Q.X ((j + (-1)) + 1)) := by
      rw [hidx]; exact hQbdd' j hjQ
    have hbp : IsZero (F.X ((j + (-1)) + 1) ⊞ (Q⟦(1 : ℤ)⟧).X (j + (-1))) :=
      (biprod_isZero_iff _ _).mpr ⟨h₁, h₂⟩
    have hprod : IsZero (ModuleCat.of A
        (F.X ((j + (-1)) + 1) × Q.X ((j + (-1)) + 1))) :=
      IsZero.of_iso hbp
        (ModuleCat.biprodIsoProd (F.X ((j + (-1)) + 1)) ((Q⟦(1 : ℤ)⟧).X (j + (-1)))).symm
    exact IsZero.of_iso hprod (mappingCocone_X_iso F Q ψ j)
  have hzPbdd : ∃ a b : ℤ, ∀ j, j < a ∨ b < j → IsZero (P.X j) := by
    refine ⟨min aF aQ, max bF bQ, fun j hj => ?_⟩
    rcases hj with h | h
    · exact hzP j (Or.inl (lt_of_lt_of_le h (min_le_left aF aQ)))
        (Or.inl (lt_of_lt_of_le h (min_le_right aF aQ)))
    · exact hzP j (Or.inr (lt_of_le_of_lt (le_max_left bF bQ) h))
        (Or.inr (lt_of_le_of_lt (le_max_right bF bQ) h))
  have hPfin : ∀ j, Module.Finite A (P.X j) := fun j => by
    haveI := hFfin ((j + (-1)) + 1)
    haveI := hQfin ((j + (-1)) + 1)
    exact Module.Finite.equiv (mappingCocone_X_iso F Q ψ j).toLinearEquiv.symm
  have hPfree : ∀ j, Module.Free A (P.X j) := fun j => by
    haveI := hFfree ((j + (-1)) + 1)
    haveI := hQfree ((j + (-1)) + 1)
    exact Module.Free.of_equiv' inferInstance (mappingCocone_X_iso F Q ψ j).toLinearEquiv.symm
  -- Hence `P` is again K-projective, and the isomorphism of the derived category is
  -- represented by an honest morphism, which is a quasi-isomorphism.
  haveI : P.IsStrictlyLE (max bF bQ) := by
    rw [CochainComplex.isStrictlyLE_iff P (max bF bQ)]
    intro j hj
    exact hzP j (Or.inr (lt_of_le_of_lt (le_max_left bF bQ) hj))
      (Or.inr (lt_of_le_of_lt (le_max_right bF bQ) hj))
  haveI : ∀ j, Projective (P.X j) := fun j => by
    haveI := hPfree j
    infer_instance
  haveI : CochainComplex.IsKProjective P :=
    CochainComplex.isKProjective_of_projective P (max bF bQ)
  obtain ⟨g, hg⟩ := Q_map_surjective_of_isKProjective (A := A) (K := P) S.X₂ e.symm.hom
  haveI : IsIso (DerivedCategory.Q.map g) := by rw [hg]; infer_instance
  have hgqi : QuasiIso g :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{u} A) g).mp inferInstance
  exact ⟨P, hPfin, hPfree, hzPbdd, g, hgqi⟩

end Work.DSEQ0
