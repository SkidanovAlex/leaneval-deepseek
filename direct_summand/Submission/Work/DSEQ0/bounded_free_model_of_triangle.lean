import Mathlib
import Submission.Work.DSEQ0.Model

open CategoryTheory Limits Pretriangulated

namespace Work.DSEQ0

universe u

set_option linter.style.haveILetI false

section Helpers

variable {A : Type u} [CommRing A]

/-- A binary biproduct of finite modules is finite (transfer along the canonical
isomorphism `M ⊞ N ≅ M × N` of `ModuleCat`). -/
lemma tri_moduleCat_finite_biprod {M N : ModuleCat.{u} A} [Module.Finite A M]
    [Module.Finite A N] : Module.Finite A ↥(M ⊞ N) :=
  Module.Finite.equiv (ModuleCat.biprodIsoProd M N).symm.toLinearEquiv

/-- A binary biproduct of free modules is free. -/
lemma tri_moduleCat_free_biprod {M N : ModuleCat.{u} A} [Module.Free A M] [Module.Free A N] :
    Module.Free A ↥(M ⊞ N) :=
  Module.Free.of_equiv (ModuleCat.biprodIsoProd M N).symm.toLinearEquiv

end Helpers

/-- For a K-projective complex `K`, the localization functor `Q` is surjective on morphisms out
of `K`: every morphism `Q K ⟶ Q L` in the derived category is the image of an honest chain map
`K ⟶ L`.  This is `CochainComplex.IsKProjective.Qh_map_bijective`, the homotopy category
and the derived category being identified along `DerivedCategory.quotientCompQhIso`. -/
lemma tri_Q_map_surjective_of_isKProjective {A : Type u} [CommRing A]
    [HasDerivedCategory (ModuleCat.{u} A)]
    {K : CochainComplex (ModuleCat.{u} A) ℤ} [K.IsKProjective]
    (L : CochainComplex (ModuleCat.{u} A) ℤ) :
    Function.Surjective
      (DerivedCategory.Q.map : (K ⟶ L) →
        (DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L)) := by
  intro T
  obtain ⟨y, hy⟩ := (CochainComplex.IsKProjective.Qh_map_bijective K _).surjective
    ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).hom.app K ≫ T ≫
      (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).inv.app L)
  obtain ⟨f, rfl⟩ :=
    (HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).map_surjective y
  refine ⟨f, ?_⟩
  rw [← cancel_epi ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).hom.app K),
    ← DerivedCategory.quotientCompQhIso_hom_naturality f, hy]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

/-- **Bounded finite free models are stable under the middle of a distinguished triangle.**
Given a distinguished triangle `X₁ → X₂ → X₃ →⁺¹` in `D(A)` and bounded models of finite free
`A`-modules of two of its vertices, the third vertex has one too.  The proof is the (co)cone
construction: `X₂` is the homotopy fibre of `X₃ → X₁⟦1⟧`, whose lift to a chain map
`Q₃ ⟶ Q₁⟦1⟧` exists because `Q₃` is K-projective (bounded, free terms).  Useful helper facts:
`CochainComplex.isKProjective_of_projective` (bounded-above + projective terms), and the
mapping cone `CochainComplex.mappingCone` / `HomologicalComplex.HomotopyCofiber`.

This is the general form of `Work.DSEQ0.bounded_free_model_of_shortExact` (a short exact sequence
of complexes gives a distinguished triangle), and it is the statement needed by the induction of
"a complex whose cohomology has finite free resolutions has a bounded finite free model": the
induction uses the t-structure triangle
`H^N(C)⟦-N⟧ ⟶ C ⟶ C.truncLE (N-1) ⟶⁺¹`, which is *not* a short exact sequence of complexes. -/
theorem bounded_free_model_of_triangle {A : Type u} [CommRing A]
    [HasDerivedCategory (ModuleCat.{u} A)]
    (T : CategoryTheory.Pretriangulated.Triangle (DerivedCategory (ModuleCat.{u} A)))
    (hT : T ∈ CategoryTheory.Pretriangulated.distinguishedTriangles)
    (Q₁ Q₃ : CochainComplex (ModuleCat.{u} A) ℤ)
    (hQ₁fin : ∀ j, Module.Finite A (Q₁.X j)) (hQ₁free : ∀ j, Module.Free A (Q₁.X j))
    (hQ₁bdd : ∃ a b : ℤ, ∀ j, j < a ∨ b < j → CategoryTheory.Limits.IsZero (Q₁.X j))
    (hQ₃fin : ∀ j, Module.Finite A (Q₃.X j)) (hQ₃free : ∀ j, Module.Free A (Q₃.X j))
    (hQ₃bdd : ∃ a b : ℤ, ∀ j, j < a ∨ b < j → CategoryTheory.Limits.IsZero (Q₃.X j))
    (e₁ : DerivedCategory.Q.obj Q₁ ≅ T.obj₁) (e₃ : DerivedCategory.Q.obj Q₃ ≅ T.obj₃) :
    ∃ (P : CochainComplex (ModuleCat.{u} A) ℤ),
      (∀ j, Module.Finite A (P.X j)) ∧ (∀ j, Module.Free A (P.X j)) ∧
      (∃ a b : ℤ, ∀ j, j < a ∨ b < j → CategoryTheory.Limits.IsZero (P.X j)) ∧
      Nonempty (DerivedCategory.Q.obj P ≅ T.obj₂) := by
  -- `Q₃` is K-projective: it is bounded above and all its terms are free, hence projective.
  have hproj₃ : ∀ n, Projective (Q₃.X n) := by
    intro n
    haveI : Module.Free A (Q₃.X n) := hQ₃free n
    infer_instance
  have hK₃ : Q₃.IsKProjective := by
    obtain ⟨a, b, hb⟩ := hQ₃bdd
    haveI : Q₃.IsStrictlyLE b := by
      rw [CochainComplex.isStrictlyLE_iff]
      exact fun i hi => hb i (Or.inr hi)
    haveI := hproj₃
    exact CochainComplex.isKProjective_of_projective Q₃ b
  haveI : Q₃.IsKProjective := hK₃
  -- Rotating the triangle, the middle vertex `T.obj₂` becomes the third vertex of the
  -- distinguished triangle `T.obj₃⟦-1⟧ ⟶ T.obj₁ ⟶ T.obj₂ ⟶⁺¹`.
  have hT' : T.invRotate ∈ distTriang (DerivedCategory (ModuleCat.{u} A)) :=
    inv_rot_of_distTriang T hT
  -- The identification of the two first vertices of `T.invRotate` with the model complexes.
  let α : DerivedCategory.Q.obj (Q₃⟦(-1 : ℤ)⟧) ≅ T.invRotate.obj₁ :=
    (DerivedCategory.Q.commShiftIso (-1 : ℤ)).app Q₃ ≪≫
      (shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (-1 : ℤ)).mapIso e₃
  let β : DerivedCategory.Q.obj Q₁ ≅ T.invRotate.obj₂ := e₁
  -- The connecting map `Q₃⟦-1⟧ ⟶ Q₁`, transported to the models.
  let ψ : DerivedCategory.Q.obj (Q₃⟦(-1 : ℤ)⟧) ⟶ DerivedCategory.Q.obj Q₁ :=
    α.hom ≫ T.invRotate.mor₁ ≫ β.inv
  -- It lifts to a chain map because `Q₃⟦-1⟧` is K-projective.
  obtain ⟨φ, hφ⟩ := tri_Q_map_surjective_of_isKProjective (A := A) (K := Q₃⟦(-1 : ℤ)⟧) Q₁ ψ
  -- The mapping cone of that lift is a distinguished triangle isomorphic to `T.invRotate`,
  -- hence its third vertex is `T.obj₂`.
  let V : Triangle (DerivedCategory (ModuleCat.{u} A)) :=
    DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle φ)
  have hV : V ∈ distTriang (DerivedCategory (ModuleCat.{u} A)) :=
    DerivedCategory.mappingCone_triangle_distinguished φ
  have hcomm₀ : DerivedCategory.Q.map φ ≫ β.hom = α.hom ≫ T.invRotate.mor₁ := by
    rw [hφ]
    simp only [ψ]
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hcomm : V.mor₁ ≫ β.hom = α.hom ≫ T.invRotate.mor₁ := hcomm₀
  obtain ⟨c, hc₁, hc₂⟩ :=
    complete_distinguished_triangle_morphism V T.invRotate hV hT' α.hom β.hom hcomm
  haveI : IsIso c := isIso₃_of_isIso₁₂
    (Triangle.homMk V T.invRotate α.hom β.hom c hcomm hc₁ hc₂) hV hT'
    (inferInstance : IsIso α.hom) (inferInstance : IsIso β.hom)
  have hIso : Nonempty (V.obj₃ ≅ T.invRotate.obj₃) := ⟨asIso c⟩
  refine ⟨CochainComplex.mappingCone φ, ?_, ?_, ?_, ?_⟩
  · -- finiteness
    intro i
    haveI : Module.Finite A ((Q₃⟦(-1 : ℤ)⟧).X (i + 1)) := hQ₃fin ((i + 1) + (-1))
    haveI : Module.Finite A (Q₁.X i) := hQ₁fin i
    haveI : Module.Finite A ↥((Q₃⟦(-1 : ℤ)⟧).X (i + 1) ⊞ Q₁.X i) := tri_moduleCat_finite_biprod
    exact Module.Finite.equiv
      (HomologicalComplex.homotopyCofiber.XIsoBiprod φ i (i + 1) rfl).symm.toLinearEquiv
  · -- freeness
    intro i
    haveI : Module.Free A ((Q₃⟦(-1 : ℤ)⟧).X (i + 1)) := hQ₃free ((i + 1) + (-1))
    haveI : Module.Free A (Q₁.X i) := hQ₁free i
    haveI : Module.Free A ↥((Q₃⟦(-1 : ℤ)⟧).X (i + 1) ⊞ Q₁.X i) := tri_moduleCat_free_biprod
    exact Module.Free.of_equiv
      (HomologicalComplex.homotopyCofiber.XIsoBiprod φ i (i + 1) rfl).symm.toLinearEquiv
  · -- boundedness: the cone in degree `j` is `Q₃.X j ⊞ Q₁.X j`
    obtain ⟨a₁, b₁, h₁⟩ := hQ₁bdd
    obtain ⟨a₃, b₃, h₃⟩ := hQ₃bdd
    refine ⟨min a₁ a₃, max b₁ b₃, fun j hj => ?_⟩
    rcases hj with hj | hj
    · have h1 : j < a₁ := lt_of_lt_of_le hj (min_le_left _ _)
      have h3 : j < a₃ := lt_of_lt_of_le hj (min_le_right _ _)
      exact (CochainComplex.mappingCone.isZero_X_iff φ j).mpr
        ⟨h₃ _ (Or.inl (by simpa using h3)), h₁ _ (Or.inl h1)⟩
    · have h1 : b₁ < j := lt_of_le_of_lt (le_max_left _ _) hj
      have h3 : b₃ < j := lt_of_le_of_lt (le_max_right _ _) hj
      exact (CochainComplex.mappingCone.isZero_X_iff φ j).mpr
        ⟨h₃ _ (Or.inr (by simpa using h3)), h₁ _ (Or.inr h1)⟩
  · exact hIso

end Work.DSEQ0
