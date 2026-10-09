import Mathlib
import Submission.Commons.RingTheory.Valuation.mem_stabilizer_valuationSubring_iff
import Submission.Commons.FieldTheory.Galois.isClosed_stabilizer_valuationSubring
import Submission.Commons.FieldTheory.Galois.exists_restrictScalars_smul_eq_of_comap_eq
import Submission.Commons.NumberTheory.NumberField.Valuation.atMostOne_indecomposable_prime
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Pointwise

set_option autoImplicit false

namespace Commons.NumberTheory.NumberField.Valuation

variable {K K' : Type*} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']

omit [NumberField K] [IsSepClosure K K'] in
private lemma comap_eq_self_of_mem_stabilizer (A : ValuationSubring K') (g : K' ≃ₐ[K] K')
    (hg : g ∈ MulAction.stabilizer (K' ≃ₐ[K] K') A) : A.comap (g : K' →+* K') = A := by
  rw [Commons.RingTheory.Valuation.mem_stabilizer_valuationSubring_iff] at hg
  ext x; rw [ValuationSubring.mem_comap]; exact (hg x).symm

omit [NumberField K] [IsSepClosure K K'] in
private lemma mem_stabilizer_of_comap_eq (A : ValuationSubring K') (g : K' ≃ₐ[K] K')
    (hg : A.comap (g : K' →+* K') = A) : g ∈ MulAction.stabilizer (K' ≃ₐ[K] K') A := by
  rw [Commons.RingTheory.Valuation.mem_stabilizer_valuationSubring_iff]
  intro x
  have h := SetLike.ext_iff.mp hg x
  rw [ValuationSubring.mem_comap] at h
  exact h.symm

theorem eq_one_of_comap_eq_of_comap_eq {K K' : Type*} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K'] {A₁ A₂ : ValuationSubring K'} (hne : A₁ ≠ A₂) (h₁ : A₁.comap (algebraMap K K') ≠ ⊤) (h₂ : A₂.comap (algebraMap K K') ≠ ⊤) (σ : K' ≃ₐ[K] K') (hσ₁ : A₁.comap (σ : K' →+* K') = A₁) (hσ₂ : A₂.comap (σ : K' →+* K') = A₂) : σ = 1 := by
  by_contra hσne
  let H : Subgroup (K' ≃ₐ[K] K') :=
    MulAction.stabilizer (K' ≃ₐ[K] K') A₁ ⊓ MulAction.stabilizer (K' ≃ₐ[K] K') A₂
  have hσH : σ ∈ H :=
    ⟨mem_stabilizer_of_comap_eq A₁ σ hσ₁, mem_stabilizer_of_comap_eq A₂ σ hσ₂⟩
  have hHcl : IsClosed (H : Set (K' ≃ₐ[K] K')) :=
    ((Commons.FieldTheory.Galois.isClosed_stabilizer_valuationSubring A₁).inter
      (Commons.FieldTheory.Galois.isClosed_stabilizer_valuationSubring A₂))
  let L : IntermediateField K K' := IntermediateField.fixedField H
  have hfix : IntermediateField.fixingSubgroup L = H :=
    InfiniteGalois.fixingSubgroup_fixedField (k := K) (K := K') ⟨H, hHcl⟩
  have hLne : L ≠ ⊤ := by
    intro hLtop
    apply hσne
    ext x
    have hx : x ∈ L := by rw [hLtop]; trivial
    rw [IntermediateField.mem_fixedField_iff] at hx
    exact hx σ hσH
  have hfix₁ : ∀ g : K' ≃ₐ[K] K', (∀ x : L, g x = x) → A₁.comap (g : K' →+* K') = A₁ := by
    intro g hg
    have hgmem : g ∈ IntermediateField.fixingSubgroup L := by
      rw [IntermediateField.mem_fixingSubgroup_iff]; intro x hx; exact hg ⟨x, hx⟩
    rw [hfix] at hgmem
    exact comap_eq_self_of_mem_stabilizer A₁ g (Subgroup.mem_inf.mp hgmem).1
  have hfix₂ : ∀ g : K' ≃ₐ[K] K', (∀ x : L, g x = x) → A₂.comap (g : K' →+* K') = A₂ := by
    intro g hg
    have hgmem : g ∈ IntermediateField.fixingSubgroup L := by
      rw [IntermediateField.mem_fixingSubgroup_iff]; intro x hx; exact hg ⟨x, hx⟩
    rw [hfix] at hgmem
    exact comap_eq_self_of_mem_stabilizer A₂ g (Subgroup.mem_inf.mp hgmem).2
  have h₁L : A₁.comap (algebraMap ↥L K') ≠ ⊤ := by
    intro htop
    apply h₁
    have hcc : (A₁.comap (algebraMap ↥L K')).comap (algebraMap K ↥L) = A₁.comap (algebraMap K K') := by
      rw [ValuationSubring.comap_comap, IsScalarTower.algebraMap_eq K ↥L K']
    rw [htop] at hcc
    have htop2 : (⊤ : ValuationSubring ↥L).comap (algebraMap K ↥L) = ⊤ := by
      ext x; simp [ValuationSubring.mem_comap]
    rw [htop2] at hcc
    exact hcc.symm
  have h₂L : A₂.comap (algebraMap ↥L K') ≠ ⊤ := by
    intro htop
    apply h₂
    have hcc : (A₂.comap (algebraMap ↥L K')).comap (algebraMap K ↥L) = A₂.comap (algebraMap K K') := by
      rw [ValuationSubring.comap_comap, IsScalarTower.algebraMap_eq K ↥L K']
    rw [htop] at hcc
    have htop2 : (⊤ : ValuationSubring ↥L).comap (algebraMap K ↥L) = ⊤ := by
      ext x; simp [ValuationSubring.mem_comap]
    rw [htop2] at hcc
    exact hcc.symm
  have hA₁ : ∀ B : ValuationSubring K', B.comap (algebraMap ↥L K') = A₁.comap (algebraMap ↥L K') → B = A₁ := by
    intro B hB
    have hBne : B.comap (algebraMap ↥L K') ≠ ⊤ := by rw [hB]; exact h₁L
    obtain ⟨τ, hτL, hτ⟩ :=
      Commons.FieldTheory.Galois.exists_restrictScalars_smul_eq_of_comap_eq L B A₁ hBne (by rw [hB])
    have hτA₁ : A₁.comap (τ : K' →+* K') = A₁ := hfix₁ τ hτL
    have hcomp : (B.comap (τ.symm : K' →+* K')).comap (τ : K' →+* K') = B := by
      ext x; simp [ValuationSubring.mem_comap]
    rw [← hcomp, hτ, hτA₁]
  have hA₂ : ∀ B : ValuationSubring K', B.comap (algebraMap ↥L K') = A₂.comap (algebraMap ↥L K') → B = A₂ := by
    intro B hB
    have hBne : B.comap (algebraMap ↥L K') ≠ ⊤ := by rw [hB]; exact h₂L
    obtain ⟨τ, hτL, hτ⟩ :=
      Commons.FieldTheory.Galois.exists_restrictScalars_smul_eq_of_comap_eq L B A₂ hBne (by rw [hB])
    have hτA₂ : A₂.comap (τ : K' →+* K') = A₂ := hfix₂ τ hτL
    have hcomp : (B.comap (τ.symm : K' →+* K')).comap (τ : K' →+* K') = B := by
      ext x; simp [ValuationSubring.mem_comap]
    rw [← hcomp, hτ, hτA₂]
  exact Commons.NumberTheory.NumberField.Valuation.atMostOne_indecomposable_prime L hLne A₁ A₂ hne h₁L h₂L hA₁ hA₂

end Commons.NumberTheory.NumberField.Valuation
