import Mathlib
import Submission.Work.DSEQ0.TensorCpx.Basic

namespace Work.DSEQ0.TensorCpx

universe a

open CategoryTheory Limits

variable {A : Type a} [CommRing A]

noncomputable def tPsiComp {F C : CochainComplex (ModuleCat.{a} A) ℤ}
    (ψ : ∀ i j : ℤ, ↥(F.X i) →ₗ[A] ↥(F.X j) →ₗ[A] ↥(C.X (i + j)))
    (n : ℤ) : TX F n →ₗ[A] C.X n :=
  DirectSum.toModule A (TIdx n) (C.X n)
    (fun p => (C.XIsoOfEq p.2).hom.hom ∘ₗ TensorProduct.lift (ψ p.1.1 p.1.2))

/-- The reindexing isomorphism `XIsoOfEq` of a self-equality is the identity. -/
lemma XIsoOfEq_self_hom {K : CochainComplex (ModuleCat.{a} A) ℤ} {p : ℤ} (h : p = p) :
    (K.XIsoOfEq h).hom = 𝟙 (K.X p) := by
  rw [Subsingleton.elim h rfl, HomologicalComplex.XIsoOfEq_rfl]
  rfl

/-- `XIsoOfEq`, as a morphism, depends on the reindexing equality only through proof
irrelevance. -/
lemma XIsoOfEq_hom_congr {K : CochainComplex (ModuleCat.{a} A) ℤ} {p q : ℤ}
    {h1 h2 : p = q} (h : h1 = h2) : (K.XIsoOfEq h1).hom = (K.XIsoOfEq h2).hom := by
  rw [h]

lemma tPsiComp_lof {F C : CochainComplex (ModuleCat.{a} A) ℤ}
    (ψ : ∀ i j : ℤ, ↥(F.X i) →ₗ[A] ↥(F.X j) →ₗ[A] ↥(C.X (i + j)))
    {n : ℤ} (p : TIdx n) (z : TFam F p.1.1 p.1.2) :
    tPsiComp ψ n (DirectSum.lof A (TIdx n) (fun p => TFam F p.1.1 p.1.2) p z)
      = (C.XIsoOfEq p.2).hom (TensorProduct.lift (ψ p.1.1 p.1.2) z) := by
  unfold tPsiComp
  rw [DirectSum.toModule_lof]
  rfl

lemma tPsiComp_apply {F C : CochainComplex (ModuleCat.{a} A) ℤ}
    (ψ : ∀ i j : ℤ, ↥(F.X i) →ₗ[A] ↥(F.X j) →ₗ[A] ↥(C.X (i + j)))
    {n : ℤ} (i j : ℤ) (h : i + j = n) (z : TFam F i j) :
    tPsiComp ψ n (TIncl F i j h z) = (C.XIsoOfEq h).hom (TensorProduct.lift (ψ i j) z) := by
  unfold tPsiComp TIncl
  rw [DirectSum.toModule_lof]
  rfl

lemma tPsiComp_tmul {F C : CochainComplex (ModuleCat.{a} A) ℤ}
    (ψ : ∀ i j : ℤ, ↥(F.X i) →ₗ[A] ↥(F.X j) →ₗ[A] ↥(C.X (i + j)))
    {n : ℤ} (i j : ℤ) (h : i + j = n) (x : ↥(F.X i)) (y : ↥(F.X j)) :
    tPsiComp ψ n (TIncl F i j h (x ⊗ₜ[A] y)) = (C.XIsoOfEq h).hom ((ψ i j x) y) := by
  rw [tPsiComp_apply, TensorProduct.lift.tmul]

lemma Td_lof_apply {F : CochainComplex (ModuleCat.{a} A) ℤ} {n : ℤ}
    (p : TIdx n) (z : TFam F p.1.1 p.1.2) :
    Td F n (DirectSum.lof A (TIdx n) (fun p => TFam F p.1.1 p.1.2) p z)
      = TdComp F p.1.1 p.1.2 p.2 z :=
  Td_apply_incl F p.1.1 p.1.2 p.2 z

lemma tPsiComp_chain {F C : CochainComplex (ModuleCat.{a} A) ℤ}
    (ψ : ∀ i j : ℤ, ↥(F.X i) →ₗ[A] ↥(F.X j) →ₗ[A] ↥(C.X (i + j)))
    (hψ : ∀ (i j : ℤ) (x : ↥(F.X i)) (y : ↥(F.X j)),
      (C.d (i + j) (i + j + 1)).hom ((ψ i j x) y) =
        (C.XIsoOfEq (by omega : i + 1 + j = i + j + 1)).hom
            (((ψ (i + 1) j) ((F.d i (i + 1)).hom x)) y)
        + (-1 : A) ^ i.natAbs •
            ((C.XIsoOfEq (by omega : i + (j + 1) = i + j + 1)).hom
              ((ψ i (j + 1) x) ((F.d j (j + 1)).hom y))))
    (n : ℤ) :
    (C.d n (n+1)).hom ∘ₗ tPsiComp ψ n = tPsiComp ψ (n+1) ∘ₗ Td F n := by
  apply DirectSum.linearMap_ext A
  intro p
  obtain ⟨⟨i, j⟩, h⟩ := p
  cases h
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    simp only [LinearMap.comp_apply]
    rw [tPsiComp_lof, Td_lof_apply, TdComp_tmul]
    simp only [map_add, map_smul]
    simp only [tPsiComp_tmul, TensorProduct.lift.tmul]
    rw [negOnePow_eq_pow_natAbs]
    rw [XIsoOfEq_self_hom, ModuleCat.id_apply]
    rw [hψ i j x y]
  | add a b ha hb =>
    simp only [LinearMap.comp_apply, map_add] at ha hb ⊢
    rw [ha, hb]

theorem tPsi_exists (A : Type a) [CommRing A] {F C : CochainComplex (ModuleCat.{a} A) ℤ}
    (ψ : ∀ i j : ℤ, ↥(F.X i) →ₗ[A] ↥(F.X j) →ₗ[A] ↥(C.X (i + j)))
    (hψ : ∀ (i j : ℤ) (x : ↥(F.X i)) (y : ↥(F.X j)),
      (C.d (i + j) (i + j + 1)).hom ((ψ i j x) y) =
        (C.XIsoOfEq (by omega : i + 1 + j = i + j + 1)).hom
            (((ψ (i + 1) j) ((F.d i (i + 1)).hom x)) y)
        + (-1 : A) ^ i.natAbs •
            ((C.XIsoOfEq (by omega : i + (j + 1) = i + j + 1)).hom
              ((ψ i (j + 1) x) ((F.d j (j + 1)).hom y)))) :
    ∃ Φ : Work.DSEQ0.TensorCpx.T F ⟶ C, ∀ (i j : ℤ) (x : ↥(F.X i)) (y : ↥(F.X j)),
      (Φ.f (i + j)).hom ((Work.DSEQ0.TensorCpx.TIncl F i j rfl) (x ⊗ₜ[A] y)) = (ψ i j x) y := by
  refine ⟨HomologicalComplex.Hom.mk (fun n => ModuleCat.ofHom (tPsiComp ψ n)) ?_, ?_⟩
  · intro n m hrel
    rw [ComplexShape.up_Rel] at hrel
    subst hrel
    rw [T_d]
    apply ModuleCat.hom_ext
    change (C.d n (n+1)).hom ∘ₗ tPsiComp ψ n = tPsiComp ψ (n+1) ∘ₗ Td F n
    exact tPsiComp_chain ψ hψ n
  · intro i j x y
    change tPsiComp ψ (i + j) (TIncl F i j rfl (x ⊗ₜ[A] y)) = (ψ i j x) y
    rw [tPsiComp_apply, TensorProduct.lift.tmul, XIsoOfEq_self_hom, ModuleCat.id_apply]

end Work.DSEQ0.TensorCpx
