import Mathlib
import Submission.Work.SSGRoute.ZConstruction.AuxInterface
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZConstruction

open _root_.SSGRoute
open scoped Pointwise

set_option linter.unusedVariables false

section KConjBasic

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]

/-- Level-`K` conjugacy is reflexive. -/
theorem kConj_refl (K : IntermediateField k Ω) (A : ValuationSubring Ω) :
    Work.SSGRoute.KConj K A A :=
  ⟨1, K.fixingSubgroup.one_mem, one_smul _ _⟩

/-- Level-`K` conjugacy is symmetric. -/
theorem kConj_symm {K : IntermediateField k Ω} {A B : ValuationSubring Ω}
    (h : Work.SSGRoute.KConj K A B) : Work.SSGRoute.KConj K B A := by
  obtain ⟨τ, hτ, hτA⟩ := h
  exact ⟨τ⁻¹, K.fixingSubgroup.inv_mem hτ, by rw [← hτA, inv_smul_smul]⟩

/-- Level-`K` conjugacy is transitive. -/
theorem kConj_trans {K : IntermediateField k Ω} {A B C : ValuationSubring Ω}
    (h₁ : Work.SSGRoute.KConj K A B) (h₂ : Work.SSGRoute.KConj K B C) :
    Work.SSGRoute.KConj K A C := by
  obtain ⟨τ, hτ, hτA⟩ := h₁
  obtain ⟨υ, hυ, hυB⟩ := h₂
  exact ⟨υ * τ, K.fixingSubgroup.mul_mem hυ hτ, by rw [mul_smul, hτA, hυB]⟩

/-- Level-`K` conjugacy implies `G_k`-conjugacy. -/
theorem kConj_isConjPlace {K : IntermediateField k Ω} {A B : ValuationSubring Ω}
    (h : Work.SSGRoute.KConj K A B) : SSGRoute.IsConjPlace k A B := by
  obtain ⟨τ, -, hτA⟩ := h
  exact ⟨τ, hτA⟩

/-- The setoid of level-`K` conjugacy of finite places. -/
def kConjSetoid (K : IntermediateField k Ω) : Setoid (ValuationSubring Ω) where
  r := Work.SSGRoute.KConj K
  iseqv := ⟨kConj_refl K, fun h => kConj_symm h, fun h₁ h₂ => kConj_trans h₁ h₂⟩

end KConjBasic

/-- **Upgrading a `G_k`-conjugacy cover of a finite place set to a level-`K` conjugacy cover.**
Given a finite set `T` of pairwise *level-`K`*-non-conjugate finite places and a finite set `S'` of
pairwise `G_k`-non-conjugate finite places, there is a finite set `T''` which
* contains `T` as a subset,
* is a set of pairwise level-`K`-non-conjugate finite places,
* meets every level-`K` class of every element of `S'` (i.e. every place `G_k`-conjugate to an
  element of `S'` is level-`K`-conjugate to an element of `T''`).

This is the technical passage recorded in `ZConstruction/AuxInterface.lean` (notes 1 and 2): the
product formula `Work.SSGRoute.ZDataMup.IsProductFormula` is stated in terms of level-`K`
conjugacy, whereas the finiteness statement of the workspace
(`Work.SSGRoute.ZConstruction.exists_finset_ramifiedPlaces`) produces a cover up to `G_k`-conjugacy;
the two agree because a `G_k`-class is the union of at most `[K : k]` level-`K` classes (the
quotient `G_k/(G_K · D_A)` is finite because `[G_k : G_K] = [K : k]` is finite).  Pure place/Galois
bookkeeping: no arithmetic enters. -/
theorem exists_finset_KConj_cover (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (T S' : Finset (ValuationSubring Ω))
    (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T, Work.SSGRoute.KConj K A B → A = B)
    (hS'fin : ∀ A ∈ S', SSGRoute.IsFinPlace k A)
    (hS'disj : ∀ A ∈ S', ∀ B ∈ S', SSGRoute.IsConjPlace k A B → A = B) :
    ∃ T'' : Finset (ValuationSubring Ω),
      (∀ A ∈ T'', SSGRoute.IsFinPlace k A) ∧
      (∀ A ∈ T'', ∀ B ∈ T'', Work.SSGRoute.KConj K A B → A = B) ∧
      (∀ A ∈ T, A ∈ T'') ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∃ A ∈ S', SSGRoute.IsConjPlace k A B) → ∃ A' ∈ T'', Work.SSGRoute.KConj K A' B) := by
  classical
  -- A chosen lift of an element of `Gal(K/k)` to `G_k`.
  let lift : (K ≃ₐ[k] K) → (Ω ≃ₐ[k] Ω) := fun φ => φ.liftNormal Ω
  have lift_spec : ∀ φ : K ≃ₐ[k] K, AlgEquiv.restrictNormalHom (↥K) (lift φ) = φ := by
    intro φ
    rw [show AlgEquiv.restrictNormalHom (↥K) (lift φ) = (lift φ).restrictNormal (↥K) from rfl]
    exact AlgEquiv.restrict_liftNormal Ω φ
  -- A finite set meeting every level-`K` class inside the `G_k`-closure of `S'`.
  set W : Finset (ValuationSubring Ω) :=
    S'.biUnion (fun A => (Finset.univ : Finset (K ≃ₐ[k] K)).image (fun φ => lift φ • A))
      with hW
  have hWfin : ∀ w ∈ W, SSGRoute.IsFinPlace k w := by
    intro w hw
    rw [hW, Finset.mem_biUnion] at hw
    obtain ⟨A, hAS', hwA⟩ := hw
    rw [Finset.mem_image] at hwA
    obtain ⟨φ, -, rfl⟩ := hwA
    exact (isFinPlace_smul_iff A (lift φ)).mpr (hS'fin A hAS')
  -- The level-`K` classes met by `W`, and those already met by `T`.
  set C : Finset (Quotient (kConjSetoid K)) :=
    W.image (fun w => Quotient.mk (kConjSetoid K) w) with hC
  set CT : Finset (Quotient (kConjSetoid K)) :=
    T.image (fun t => Quotient.mk (kConjSetoid K) t) with hCT
  -- Add to `T` one place from each new level-`K` class.
  set T'' : Finset (ValuationSubring Ω) :=
    T ∪ (C \ CT).image (fun q => Quotient.out q) with hT''
  refine ⟨T'', ?_, ?_, ?_, ?_⟩
  · -- finiteness of the places of `T''`
    intro A hA
    rw [hT'', Finset.mem_union] at hA
    rcases hA with hA | hA
    · exact hTfin A hA
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hA
      rw [Finset.mem_sdiff] at hq
      obtain ⟨hqC, -⟩ := hq
      rw [hC] at hqC
      obtain ⟨w, hwW, hwq⟩ := Finset.mem_image.mp hqC
      have hout : Work.SSGRoute.KConj K (Quotient.out q) w := by
        rw [← hwq]
        exact Quotient.exact (Quotient.out_eq (Quotient.mk (kConjSetoid K) w))
      exact isFinPlace_of_isConjPlace (hWfin w hwW)
        (SSGRoute.isConjPlace_symm (kConj_isConjPlace hout))
  · -- pairwise non-`K`-conjugacy of the places of `T''`
    intro A hA B hB hAB
    rw [hT'', Finset.mem_union] at hA hB
    rcases hA with hA | hA <;> rcases hB with hB | hB
    · exact hTdisj A hA B hB hAB
    · exfalso
      obtain ⟨qB, hqB, rfl⟩ := Finset.mem_image.mp hB
      rw [Finset.mem_sdiff] at hqB
      obtain ⟨-, hqBnot⟩ := hqB
      have hmem : Quotient.mk (kConjSetoid K) A ∈ CT := by
        rw [hCT]
        exact Finset.mem_image.mpr ⟨A, hA, rfl⟩
      have hqeq : Quotient.mk (kConjSetoid K) A = qB :=
        (Quotient.sound hAB).trans (Quotient.out_eq qB)
      rw [hqeq] at hmem
      exact hqBnot hmem
    · exfalso
      obtain ⟨qA, hqA, rfl⟩ := Finset.mem_image.mp hA
      rw [Finset.mem_sdiff] at hqA
      obtain ⟨-, hqAnot⟩ := hqA
      have hmem : Quotient.mk (kConjSetoid K) B ∈ CT := by
        rw [hCT]
        exact Finset.mem_image.mpr ⟨B, hB, rfl⟩
      have hqeq : Quotient.mk (kConjSetoid K) B = qA :=
        (Quotient.sound (kConj_symm hAB)).trans (Quotient.out_eq qA)
      rw [hqeq] at hmem
      exact hqAnot hmem
    · obtain ⟨qA, hqA, rfl⟩ := Finset.mem_image.mp hA
      obtain ⟨qB, hqB, rfl⟩ := Finset.mem_image.mp hB
      have hqq : Quotient.mk (kConjSetoid K) (Quotient.out qA) =
          Quotient.mk (kConjSetoid K) (Quotient.out qB) := Quotient.sound hAB
      have hq : qA = qB := by
        rw [Quotient.out_eq qA, Quotient.out_eq qB] at hqq
        exact hqq
      rw [hq]
  · -- `T` is contained in `T''`
    intro A hA
    rw [hT'']
    exact Finset.mem_union_left _ hA
  · -- every place `G_k`-conjugate into `S'` is level-`K`-conjugate into `T''`
    intro B _hBfin ⟨A0, hA0S', hA0B⟩
    obtain ⟨σ, hσ⟩ := hA0B
    set φ : K ≃ₐ[k] K := AlgEquiv.restrictNormalHom (↥K) σ with hφdef
    have hker : (AlgEquiv.restrictNormalHom (↥K)) (σ * (lift φ)⁻¹) = 1 := by
      rw [map_mul, map_inv, ← hφdef, lift_spec φ, mul_inv_cancel]
    have hmem : σ * (lift φ)⁻¹ ∈ K.fixingSubgroup := by
      rw [← IntermediateField.restrictNormalHom_ker K]
      exact MonoidHom.mem_ker.mpr hker
    have hKconj : Work.SSGRoute.KConj K (lift φ • A0) B := by
      refine ⟨σ * (lift φ)⁻¹, hmem, ?_⟩
      rw [← mul_smul, mul_assoc, inv_mul_cancel, mul_one]
      exact hσ
    have hwW : lift φ • A0 ∈ W := by
      rw [hW, Finset.mem_biUnion]
      exact ⟨A0, hA0S', Finset.mem_image.mpr ⟨φ, Finset.mem_univ φ, rfl⟩⟩
    have hclassB : Quotient.mk (kConjSetoid K) B ∈ C := by
      rw [hC]
      have hmem2 : Quotient.mk (kConjSetoid K) (lift φ • A0) ∈
          W.image (fun w => Quotient.mk (kConjSetoid K) w) :=
        Finset.mem_image.mpr ⟨lift φ • A0, hwW, rfl⟩
      rwa [Quotient.sound hKconj] at hmem2
    by_cases hmemCT : Quotient.mk (kConjSetoid K) B ∈ CT
    · rw [hCT] at hmemCT
      obtain ⟨t, htT, htq⟩ := Finset.mem_image.mp hmemCT
      refine ⟨t, ?_, Quotient.exact htq⟩
      rw [hT'']
      exact Finset.mem_union_left _ htT
    · refine ⟨Quotient.out (Quotient.mk (kConjSetoid K) B), ?_, ?_⟩
      · rw [hT'']
        refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, ?_, rfl⟩)
        rw [Finset.mem_sdiff]
        exact ⟨hclassB, hmemCT⟩
      · exact Quotient.exact (Quotient.out_eq (Quotient.mk (kConjSetoid K) B))

end Work.SSGRoute.ZConstruction
