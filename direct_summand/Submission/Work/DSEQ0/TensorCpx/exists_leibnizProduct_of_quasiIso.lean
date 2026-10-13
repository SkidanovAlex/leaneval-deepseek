import Mathlib
import Submission.Work.DSEQ0.exists_lift_of_quasiIso
import Submission.Work.DSEQ0.TensorCpx.Basic
import Submission.Work.DSEQ0.TensorCpx.T_isKProjective
import Submission.Work.DSEQ0.TensorCpx.Main
import Submission.Work.DSEQ0.TensorCpx.tPsi_exists

namespace Work.DSEQ0.TensorCpx

universe a

open CategoryTheory Limits

theorem exists_leibnizProduct_of_quasiIso (A : Type a) [CommRing A]
    (F C : CochainComplex (ModuleCat.{a} A) ℤ)
    [∀ i : ℤ, Module.Free A (F.X i)] [∀ i : ℤ, Module.Finite A (F.X i)]
    (hFb : ∃ N : ℤ, ∀ i : ℤ, N < i → CategoryTheory.Limits.IsZero (F.X i))
    (φ : F ⟶ C) (hφ : QuasiIso φ)
    (ψ : ∀ i j : ℤ, ↥(F.X i) →ₗ[A] ↥(F.X j) →ₗ[A] ↥(C.X (i + j)))
    (hψ : ∀ (i j : ℤ) (x : ↥(F.X i)) (y : ↥(F.X j)),
      (C.d (i + j) (i + j + 1)).hom ((ψ i j x) y) =
        (C.XIsoOfEq (by omega : i + 1 + j = i + j + 1)).hom
            (((ψ (i + 1) j) ((F.d i (i + 1)).hom x)) y)
        + (-1 : A) ^ i.natAbs •
            ((C.XIsoOfEq (by omega : i + (j + 1) = i + j + 1)).hom
              ((ψ i (j + 1) x) ((F.d j (j + 1)).hom y))))
    (e : ↥(F.X 0)) (he : ∀ k : ℤ, (F.d 0 k).hom e = 0)
    (hunit : ∀ (j : ℤ) (y : ↥(F.X j)),
        (C.XIsoOfEq (by omega : 0 + j = j)).hom ((ψ 0 j e) y) = (φ.f j) y) :
    ∃ (μ : ∀ i j : ℤ, ↥(F.X i) →ₗ[A] ↥(F.X j) →ₗ[A] ↥(F.X (i + j)))
      (H : ∀ j : ℤ, ↥(F.X (j + 1)) →ₗ[A] ↥(F.X j)),
      (∀ (i j : ℤ) (x : ↥(F.X i)) (y : ↥(F.X j)),
        (F.d (i + j) (i + j + 1)).hom ((μ i j x) y) =
          (F.XIsoOfEq (by omega : i + 1 + j = i + j + 1)).hom
              (((μ (i + 1) j) ((F.d i (i + 1)).hom x)) y)
          + (-1 : A) ^ i.natAbs •
              ((F.XIsoOfEq (by omega : i + (j + 1) = i + j + 1)).hom
                ((μ i (j + 1) x) ((F.d j (j + 1)).hom y)))) ∧
      (∀ (j : ℤ) (y : ↥(F.X (j + 1))),
        (F.XIsoOfEq (by omega : 0 + (j + 1) = j + 1)).hom ((μ 0 (j + 1) e) y) - y =
          (F.d j (j + 1)).hom (H j y) + H (j + 1) ((F.d (j + 1) ((j + 1) + 1)).hom y)) := by
  -- The tensor square `F ⊗ F` is K-projective, and so is `F` itself (bounded above, free).
  haveI hTproj : (T F).IsKProjective :=
    T_isKProjective A F hFb
  obtain ⟨N, hN⟩ := hFb
  haveI hFle : F.IsStrictlyLE N := (CochainComplex.isStrictlyLE_iff F N).mpr hN
  haveI hFproj : F.IsKProjective := by
    haveI : ∀ n : ℤ, Projective (F.X n) := fun n => by
      haveI := (inferInstance : Module.Free A (F.X n))
      infer_instance
    exact CochainComplex.isKProjective_of_projective F N
  -- The unit `x ↦ e ⊗ x` and the transferred product `Φ : F ⊗ F ⟶ C`.
  have he1 : (F.d 0 1).hom e = 0 := he 1
  let ι : F ⟶ T F := tU F e he1
  obtain ⟨Φ, hΦ⟩ := tPsi_exists A ψ hψ
  -- `Φ` on a summand, with the degree bookkeeping.
  have hΦ' : ∀ (i j p : ℤ) (hp : i + j = p) (x : ↥(F.X i)) (y : ↥(F.X j)),
      (Φ.f p).hom ((TIncl F i j hp) (x ⊗ₜ[A] y)) = (C.XIsoOfEq hp).hom ((ψ i j x) y) := by
    intro i j p hp x y
    rw [← XIsoOfEq_f_TIncl F Φ i j hp rfl hp (x ⊗ₜ[A] y), hΦ]
  -- The unit and `Φ` compose to `φ`.
  have hUPhi : ι ≫ Φ = φ := by
    ext n x
    simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [tU_apply, hΦ' 0 n n (by omega)]
    exact hunit n x
  -- Derived-category argument: the class `φ⁻¹ ∘ Φ` is realized by a chain map `μT`.
  letI : HasDerivedCategory (ModuleCat.{a} A) := HasDerivedCategory.standard _
  haveI : QuasiIso φ := hφ
  obtain ⟨μT, hμT⟩ := Work.DSEQ0.Q_map_surjective_of_isKProjective (A := A) (K := T F) F
    (DerivedCategory.Q.map Φ ≫ inv (DerivedCategory.Q.map φ))
  -- `μT` restricted along the unit is homotopic to the identity.
  have hQid : DerivedCategory.Q.map (𝟙 F) = 𝟙 (DerivedCategory.Q.obj F) :=
    DerivedCategory.Q.map_id F
  have hQ : DerivedCategory.Q.map (ι ≫ μT) = 𝟙 (DerivedCategory.Q.obj F) := by
    rw [Functor.map_comp, hμT, ← Category.assoc, ← Functor.map_comp, hUPhi]
    exact IsIso.hom_inv_id _
  have hQh : DerivedCategory.Qh.map
        ((HomotopyCategory.quotient (ModuleCat.{a} A) (ComplexShape.up ℤ)).map (ι ≫ μT)) =
      DerivedCategory.Qh.map
        ((HomotopyCategory.quotient (ModuleCat.{a} A) (ComplexShape.up ℤ)).map (𝟙 F)) := by
    have h1 := DerivedCategory.quotientCompQhIso_hom_naturality (C := ModuleCat.{a} A) (ι ≫ μT)
    have h2 := DerivedCategory.quotientCompQhIso_hom_naturality (C := ModuleCat.{a} A) (𝟙 F)
    rw [hQ, Category.comp_id] at h1
    rw [hQid, Category.comp_id] at h2
    exact (cancel_mono _).mp (h1.trans h2.symm)
  have hquot : (HomotopyCategory.quotient (ModuleCat.{a} A) (ComplexShape.up ℤ)).map (ι ≫ μT) =
      (HomotopyCategory.quotient (ModuleCat.{a} A) (ComplexShape.up ℤ)).map (𝟙 F) :=
    (CochainComplex.IsKProjective.Qh_map_bijective (C := ModuleCat.{a} A) F
      ((HomotopyCategory.quotient (ModuleCat.{a} A) (ComplexShape.up ℤ)).obj F)).1 hQh
  have hhom : Homotopy (ι ≫ μT) (𝟙 F) := HomotopyCategory.homotopyOfEq _ _ hquot
  exact exists_leibniz_of_homotopy A F e ι
    (fun n x => tU_apply F e he1 n x) μT hhom

end Work.DSEQ0.TensorCpx
