import Mathlib
import Submission.Work.DSEQ0.bounded_free_model_of_shortExact
import Submission.Work.DSEQ0.exists_lift_of_quasiIso

namespace Work.DSG4a

open CategoryTheory AlgebraicGeometry Limits Opposite Pretriangulated

universe u

set_option linter.style.haveILetI false

/-- **The bounded-above model construction (area `DSG4a`).**  This is the one-sided refinement
of `Work.DSEQ0.bounded_free_model_of_shortExact`: instead of asking that the finite free models
`Q → S.X₁` and `F → S.X₃` be bounded on both sides, we ask only that they be *bounded above*
(`IsStrictlyLE d₁`, `IsStrictlyLE d₃`), and the resulting model `P → S.X₂` is then bounded above
in degree `max d₁ d₃`.

The construction is identical to the two-sided case: `F` is K-projective (bounded above with
free, hence projective, terms), so the connecting map of the short exact sequence can be lifted
to an honest chain map `ψ : F ⟶ Q⟦1⟧`; the middle model is the mapping cocone of `ψ`, whose
terms are the products `F.X j × Q.X j`.  Since `F` is zero above `d₃` and `Q` is zero above `d₁`,
the product is zero whenever `j > max d₁ d₃`. -/
theorem boundedAbove_free_model_of_shortExact {A : Type u} [CommRing A]
    (S : CategoryTheory.ShortComplex (CochainComplex (ModuleCat.{u} A) ℤ))
    (hS : CategoryTheory.ShortComplex.ShortExact S) {d₁ : ℤ}
    (Q : CochainComplex (ModuleCat.{u} A) ℤ) (q : Q ⟶ S.X₁) (hq : QuasiIso q)
    (hQfin : ∀ j, Module.Finite A (Q.X j)) (hQfree : ∀ j, Module.Free A (Q.X j))
    (hQbd : Q.IsStrictlyLE d₁) {d₃ : ℤ}
    (F : CochainComplex (ModuleCat.{u} A) ℤ) (f : F ⟶ S.X₃) (hf : QuasiIso f)
    (hFfin : ∀ j, Module.Finite A (F.X j)) (hFfree : ∀ j, Module.Free A (F.X j))
    (hFbd : F.IsStrictlyLE d₃) :
    ∃ (P : CochainComplex (ModuleCat.{u} A) ℤ) (q₂ : P ⟶ S.X₂),
      (∀ j, Module.Finite A (P.X j)) ∧ (∀ j, Module.Free A (P.X j)) ∧
      P.IsStrictlyLE (max d₁ d₃) ∧ QuasiIso q₂ := by
  -- We work in the derived category of `A`-modules (any instance will do).
  letI : HasDerivedCategory (ModuleCat.{u} A) := HasDerivedCategory.standard _
  haveI : QuasiIso q := hq
  haveI : QuasiIso f := hf
  -- `F` is bounded above with free (hence projective) terms, so it is K-projective.
  haveI hFle : F.IsStrictlyLE d₃ := hFbd
  haveI hFproj : CochainComplex.IsKProjective F :=
    CochainComplex.isKProjective_of_projective F d₃
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
    Work.DSEQ0.Q_map_surjective_of_isKProjective (A := A) (K := F) (Q⟦(1 : ℤ)⟧)
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
    Work.DSEQ0.iso_obj₁_of_distinguished hT₁ hT₂ e₂ e₃ comm
  -- The model of `S.X₂` is the mapping cocone of `ψ`.
  let P : CochainComplex (ModuleCat.{u} A) ℤ := CochainComplex.mappingCocone ψ
  -- Its terms are the products `F.X j × Q.X j`, hence finite free, and it is bounded above
  -- in degree `max d₁ d₃`.
  have hzP : ∀ j, d₃ < j → d₁ < j → IsZero (P.X j) := by
    intro j hjF hjQ
    have hidx : (j + (-1)) + 1 = j := by ring
    have h₁ : IsZero (F.X ((j + (-1)) + 1)) := by
      rw [hidx]; exact F.isZero_of_isStrictlyLE d₃ j hjF
    have h₂ : IsZero (Q.X ((j + (-1)) + 1)) := by
      rw [hidx]; exact Q.isZero_of_isStrictlyLE d₁ j hjQ
    have hbp : IsZero (F.X ((j + (-1)) + 1) ⊞ (Q⟦(1 : ℤ)⟧).X (j + (-1))) :=
      (biprod_isZero_iff _ _).mpr ⟨h₁, h₂⟩
    have hprod : IsZero (ModuleCat.of A
        (F.X ((j + (-1)) + 1) × Q.X ((j + (-1)) + 1))) :=
      IsZero.of_iso hbp
        (ModuleCat.biprodIsoProd (F.X ((j + (-1)) + 1)) ((Q⟦(1 : ℤ)⟧).X (j + (-1)))).symm
    exact IsZero.of_iso hprod (Work.DSEQ0.mappingCocone_X_iso F Q ψ j)
  haveI hPbdd : P.IsStrictlyLE (max d₁ d₃) := by
    rw [CochainComplex.isStrictlyLE_iff P (max d₁ d₃)]
    intro j hj
    exact hzP j (lt_of_le_of_lt (le_max_right d₁ d₃) hj)
      (lt_of_le_of_lt (le_max_left d₁ d₃) hj)
  have hPfin : ∀ j, Module.Finite A (P.X j) := fun j => by
    haveI := hFfin ((j + (-1)) + 1)
    haveI := hQfin ((j + (-1)) + 1)
    exact Module.Finite.equiv (Work.DSEQ0.mappingCocone_X_iso F Q ψ j).toLinearEquiv.symm
  have hPfree : ∀ j, Module.Free A (P.X j) := fun j => by
    haveI := hFfree ((j + (-1)) + 1)
    haveI := hQfree ((j + (-1)) + 1)
    exact Module.Free.of_equiv' inferInstance
      (Work.DSEQ0.mappingCocone_X_iso F Q ψ j).toLinearEquiv.symm
  -- Hence `P` is again K-projective, and the isomorphism of the derived category is
  -- represented by an honest morphism, which is a quasi-isomorphism.
  haveI : ∀ j, Projective (P.X j) := fun j => by
    haveI := hPfree j
    infer_instance
  haveI : CochainComplex.IsKProjective P :=
    CochainComplex.isKProjective_of_projective P (max d₁ d₃)
  obtain ⟨g, hg⟩ := Work.DSEQ0.Q_map_surjective_of_isKProjective (A := A) (K := P) S.X₂ e.symm.hom
  haveI : IsIso (DerivedCategory.Q.map g) := by rw [hg]; infer_instance
  have hgqi : QuasiIso g :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{u} A) g).mp inferInstance
  exact ⟨P, g, hPfin, hPfree, hPbdd, hgqi⟩

end Work.DSG4a
