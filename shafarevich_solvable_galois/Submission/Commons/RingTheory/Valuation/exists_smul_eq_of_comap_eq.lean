import Mathlib
import Submission.Commons.FieldTheory.Galois.comap_smul_eq_restrictNormalHom_smul
import Submission.Commons.FieldTheory.Galois.eq_of_comap_eq_forall_finite_normal
import Submission.Commons.RingTheory.Valuation.comap_inclusion_comap_eq
import Submission.Commons.RingTheory.Valuation.ValuationSubring.eq_top_of_comap_algebraMap_eq_top
import Submission.Commons.RingTheory.Valuation.exists_smul_eq_of_comap_eq_of_finite
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.RingTheory.Valuation

open scoped Pointwise

set_option linter.style.haveILetI false

/-- **Transitivity of the Galois action on the extensions of a valuation.**

Let `E / F` be a Galois extension of fields and let `A`, `B` be valuation subrings of `E` whose
traces on `F` (along `algebraMap F E`) agree.  Then `A` and `B` are conjugate under
`Gal(E/F)`: there is `σ : E ≃ₐ[F] E` with `σ • A = B`.

The proof reduces to the finite Galois case (the lemma
`Commons.RingTheory.Valuation.exists_smul_eq_of_comap_eq_of_finite`) by the usual compactness
argument on the directed system of finite normal intermediate fields: for each such `L` the set
of `σ` whose induced action on `L` carries `A ∩ L` to `B ∩ L` is a nonempty closed subset of the
compact group `E ≃ₐ[F] E`, the family is directed under `L₁ ⊔ L₂`, and an element of the
intersection restricts to the correct thing on every finite normal intermediate field, whence
`σ • A = B` by `Commons.FieldTheory.Galois.eq_of_comap_eq_forall_finite_normal`.  The degenerate
case where the common trace is `⊤` is handled by
`Commons.RingTheory.Valuation.ValuationSubring.eq_top_of_comap_algebraMap_eq_top`. -/
theorem exists_smul_eq_of_comap_eq {F E : Type*} [Field F] [Field E] [Algebra F E] [IsGalois F E]
    (A B : ValuationSubring E) (hAB : A.comap (algebraMap F E) = B.comap (algebraMap F E)) :
    ∃ σ : E ≃ₐ[F] E, σ • A = B := by
  have halg : Algebra.IsAlgebraic F E := by
    have : Algebra.IsIntegral F E := ⟨fun x => IsGalois.integral F x⟩
    exact Algebra.IsIntegral.isAlgebraic
  by_cases hC : A.comap (algebraMap F E) = ⊤
  · have hA : A = ⊤ :=
      Commons.RingTheory.Valuation.ValuationSubring.eq_top_of_comap_algebraMap_eq_top A halg hC
    have hB : B = ⊤ :=
      Commons.RingTheory.Valuation.ValuationSubring.eq_top_of_comap_algebraMap_eq_top B halg
        (hAB ▸ hC)
    exact ⟨1, by rw [hA, hB, one_smul]⟩
  · let ι := {L : IntermediateField F E // FiniteDimensional F L ∧ Normal F L}
    let t : ι → Set (E ≃ₐ[F] E) := fun L =>
      {σ | (σ • A).comap (algebraMap ↥L.1 E) = B.comap (algebraMap ↥L.1 E)}
    have htne : ∀ L : ι, (t L).Nonempty := by
      intro L
      haveI hfin' : FiniteDimensional F L.1 := L.2.1
      haveI hnorm' : Normal F L.1 := L.2.2
      haveI hisgal : IsGalois F ↥L.1 := isGalois_iff.mpr ⟨inferInstance, hnorm'⟩
      have hPQ : (A.comap (algebraMap ↥L.1 E)).comap (algebraMap F ↥L.1) =
          (B.comap (algebraMap ↥L.1 E)).comap (algebraMap F ↥L.1) := by
        rw [ValuationSubring.comap_comap, ValuationSubring.comap_comap,
          ← IsScalarTower.algebraMap_eq F ↥L.1 E]
        exact hAB
      obtain ⟨σL, hσL⟩ :=
        Commons.RingTheory.Valuation.exists_smul_eq_of_comap_eq_of_finite
          (F := F) (L := ↥L.1) (A.comap (algebraMap ↥L.1 E)) (B.comap (algebraMap ↥L.1 E)) hPQ
      obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := ↥L.1) (E := E) σL
      refine ⟨σ, ?_⟩
      show (σ • A).comap (algebraMap ↥L.1 E) = B.comap (algebraMap ↥L.1 E)
      rw [Commons.FieldTheory.Galois.comap_smul_eq_restrictNormalHom_smul, hσ, hσL]
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
        rw [← Commons.RingTheory.Valuation.comap_inclusion_comap_eq (le_sup_left : L₁.1 ≤ _) (σ • A),
          hσ, Commons.RingTheory.Valuation.comap_inclusion_comap_eq (le_sup_left : L₁.1 ≤ _) B]
      · intro σ hσ
        simp only [t, Set.mem_ofPred_eq] at hσ ⊢
        rw [← Commons.RingTheory.Valuation.comap_inclusion_comap_eq (le_sup_right : L₂.1 ≤ _) (σ • A),
          hσ, Commons.RingTheory.Valuation.comap_inclusion_comap_eq (le_sup_right : L₂.1 ≤ _) B]
    have htcl : ∀ L : ι, IsClosed (t L) := by
      intro L
      haveI hfin' : FiniteDimensional F L.1 := L.2.1
      haveI hnorm' : Normal F L.1 := L.2.2
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
    obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      t htd htne htc htcl
    refine ⟨σ, ?_⟩
    refine Commons.FieldTheory.Galois.eq_of_comap_eq_forall_finite_normal
      (K := F) (K' := E) (A := σ • A) (B := B) ?_
    intro L hfinL hnormL
    exact Set.mem_iInter.mp hσ ⟨L, hfinL, hnormL⟩

end Commons.RingTheory.Valuation
