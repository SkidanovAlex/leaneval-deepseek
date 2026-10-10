import Mathlib.Order.CompletePartialOrder
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Commons.FieldTheory.Galois.comap_smul_eq_restrictNormalHom_smul
import Submission.Commons.FieldTheory.Galois.eq_of_comap_eq_forall_finite_normal
import Submission.Commons.RingTheory.Valuation.comap_inclusion_comap_eq
import Submission.Commons.RingTheory.Valuation.exists_smul_eq_of_comap_eq_of_finite
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.RingTheory.Valuation

open scoped Pointwise

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-- **Transitivity of the Galois action on the extensions of a valuation.**
Let `E/F` be a Galois extension and `A`, `B` valuation subrings of `E` whose traces on `F`
agree and are proper.  Then `A` and `B` are conjugate by an element of `Gal(E/F)`. -/
theorem exists_smul_eq_of_comap_eq_isGalois {F E : Type*} [Field F] [Field E] [Algebra F E]
    [IsGalois F E] [Algebra.IsAlgebraic F E] (A B : ValuationSubring E)
    (hAB : A.comap (algebraMap F E) = B.comap (algebraMap F E))
    (hC : A.comap (algebraMap F E) ≠ ⊤) :
    ∃ σ : E ≃ₐ[F] E, σ • A = B := by
  -- Index the compactness argument by the finite normal intermediate fields of `E/F`.
  let ι := {L : IntermediateField F E // FiniteDimensional F L ∧ Normal F L}
  let t : ι → Set (E ≃ₐ[F] E) := fun L =>
    {σ | (σ • A).comap (algebraMap ↥L.1 E) = B.comap (algebraMap ↥L.1 E)}
  -- **Nonemptiness**: on a finite normal intermediate field the problem is finite, and the
  -- finite case is `exists_smul_eq_of_comap_eq_of_finite`.
  have htne : ∀ L : ι, (t L).Nonempty := by
    intro L
    haveI hfin : FiniteDimensional F L.1 := L.2.1
    haveI hnorm : Normal F L.1 := L.2.2
    haveI : IsGalois F ↥L.1 := isGalois_iff.mpr ⟨inferInstance, hnorm⟩
    have hPQ : (A.comap (algebraMap ↥L.1 E)).comap (algebraMap F ↥L.1) =
        (B.comap (algebraMap ↥L.1 E)).comap (algebraMap F ↥L.1) := by
      rw [ValuationSubring.comap_comap, ValuationSubring.comap_comap,
        ← IsScalarTower.algebraMap_eq F ↥L.1 E]
      exact hAB
    obtain ⟨σL, hσL⟩ :=
      exists_smul_eq_of_comap_eq_of_finite (F := F) (L := ↥L.1)
        (A.comap (algebraMap ↥L.1 E)) (B.comap (algebraMap ↥L.1 E)) hPQ
    obtain ⟨σ, hσ⟩ :=
      AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := ↥L.1) (E := E) σL
    refine ⟨σ, ?_⟩
    show (σ • A).comap (algebraMap ↥L.1 E) = B.comap (algebraMap ↥L.1 E)
    rw [Commons.FieldTheory.Galois.comap_smul_eq_restrictNormalHom_smul, hσ, hσL]
  -- **Directedness**: restricting the trace along an inclusion of intermediate fields.
  have htd : Directed (· ⊇ ·) t := by
    intro L₁ L₂
    haveI : FiniteDimensional F L₁.1 := L₁.2.1
    haveI : FiniteDimensional F L₂.1 := L₂.2.1
    haveI : Normal F L₁.1 := L₁.2.2
    haveI : Normal F L₂.1 := L₂.2.2
    refine ⟨⟨L₁.1 ⊔ L₂.1, IntermediateField.finiteDimensional_sup L₁.1 L₂.1,
      IntermediateField.normal_sup F E L₁.1 L₂.1⟩, ?_, ?_⟩
    · intro σ hσ
      simp only [t, Set.mem_ofPred_eq] at hσ ⊢
      rw [← Commons.RingTheory.Valuation.comap_inclusion_comap_eq
            (le_sup_left : L₁.1 ≤ L₁.1 ⊔ L₂.1) (σ • A),
          hσ,
          Commons.RingTheory.Valuation.comap_inclusion_comap_eq
            (le_sup_left : L₁.1 ≤ L₁.1 ⊔ L₂.1) B]
    · intro σ hσ
      simp only [t, Set.mem_ofPred_eq] at hσ ⊢
      rw [← Commons.RingTheory.Valuation.comap_inclusion_comap_eq
            (le_sup_right : L₂.1 ≤ L₁.1 ⊔ L₂.1) (σ • A),
          hσ,
          Commons.RingTheory.Valuation.comap_inclusion_comap_eq
            (le_sup_right : L₂.1 ≤ L₁.1 ⊔ L₂.1) B]
  -- **Closedness**: via continuity of `restrictNormalHom` into the discrete finite group
  -- `Gal(L/F)`.
  have htcl : ∀ L : ι, IsClosed (t L) := by
    intro L
    haveI hfin : FiniteDimensional F L.1 := L.2.1
    haveI hnorm : Normal F L.1 := L.2.2
    have heq : t L = (AlgEquiv.restrictNormalHom (F := F) (K₁ := E) L.1) ⁻¹'
        {g : ↥L.1 ≃ₐ[F] ↥L.1 |
          g • (A.comap (algebraMap ↥L.1 E)) = B.comap (algebraMap ↥L.1 E)} := by
      ext σ
      simp only [t, Set.mem_ofPred_eq, Set.mem_preimage]
      rw [Commons.FieldTheory.Galois.comap_smul_eq_restrictNormalHom_smul]
    rw [heq]
    exact IsClosed.preimage (InfiniteGalois.restrictNormalHom_continuous L.1) (isClosed_discrete _)
  have htc : ∀ L : ι, IsCompact (t L) := fun L => (htcl L).isCompact
  haveI : Nonempty ι := ⟨⟨⊥, inferInstance, inferInstance⟩⟩
  -- The compactness (Cantor intersection) argument.
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    t htd htne htc htcl
  refine ⟨σ, ?_⟩
  -- `σ • A` and `B` have the same trace on every finite normal intermediate field, hence agree.
  refine Commons.FieldTheory.Galois.eq_of_comap_eq_forall_finite_normal
    (K := F) (K' := E) (A := σ • A) (B := B) ?_
  intro L hfin hnorm
  exact Set.mem_iInter.mp hσ ⟨L, hfin, hnorm⟩

end Commons.RingTheory.Valuation
