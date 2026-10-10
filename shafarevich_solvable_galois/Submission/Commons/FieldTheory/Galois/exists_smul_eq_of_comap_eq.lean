import Mathlib.Order.CompletePartialOrder
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Commons.FieldTheory.Galois.comap_smul_eq_restrictNormalHom_smul
import Submission.Commons.FieldTheory.Galois.eq_of_comap_eq_forall_finite_normal
import Submission.Commons.NumberTheory.RamificationInertia.exists_smul_eq_of_comap_eq_of_finite
import Submission.Commons.RingTheory.Valuation.comap_inclusion_comap_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.FieldTheory.Galois

open scoped Pointwise

set_option linter.style.haveILetI false

/-- **Transitivity of the Galois action on the places of a Galois extension over a fixed place
of the base field.**  Let `F` be a number field and `K'` a Galois extension of `F`.  If `A` and
`B` are valuation subrings of `K'` with equal traces on `F`, and the common trace is not
everything (i.e. `A` and `B` are places of `K'` over the same place of `F`), then some
`σ : K' ≃ₐ[F] K'` carries `A` onto `B`.

Suggested route (compactness).  For each finite normal intermediate field `L`, the set
`T L := {σ | (A.comap σ.symm).comap (algebraMap L K') = B.comap (algebraMap L K')}` is a
nonempty closed subset of the compact group `K' ≃ₐ[F] K'` (`IsClosed.preimage` of the continuous
`AlgEquiv.restrictNormalHom` into the discrete finite group `Gal(L/F)`, using
`Commons.FieldTheory.Galois.comap_smul_eq_restrictNormalHom_smul` or its preimage form); the
family is directed under `L₁ ⊔ L₂` (`IntermediateField.finiteDimensional_sup`,
`IntermediateField.normal_sup` and `Commons.RingTheory.Valuation.comap_inclusion_comap_eq`);
nonemptiness of `T L` is
`Commons.NumberTheory.RamificationInertia.exists_smul_eq_of_comap_eq_of_finite`.  Then
`IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed` produces `σ` in the
intersection, and `Commons.FieldTheory.Galois.eq_of_comap_eq_forall_finite_normal` finishes. -/
theorem exists_smul_eq_of_comap_eq {F K' : Type*} [Field F] [NumberField F] [Field K']
    [Algebra F K'] [IsGalois F K'] (A B : ValuationSubring K')
    (hC : A.comap (algebraMap F K') ≠ ⊤)
    (hAB : A.comap (algebraMap F K') = B.comap (algebraMap F K')) :
    ∃ σ : K' ≃ₐ[F] K', σ • A = B := by
  -- Index the compactness argument by the finite normal intermediate fields of `K'/F`, and
  -- consider the family of closed sets `t L` of automorphisms whose induced action on the trace
  -- of `A` and `B` on `L` agrees.
  let ι := {L : IntermediateField F K' // FiniteDimensional F L ∧ Normal F L}
  let t : ι → Set (K' ≃ₐ[F] K') := fun L =>
    {σ | (σ • A).comap (algebraMap ↥L.1 K') = B.comap (algebraMap ↥L.1 K')}
  -- **Nonemptiness.**  On a finite normal intermediate field the problem is finite, and the
  -- finite case is `exists_smul_eq_of_comap_eq_of_finite`.
  have htne : ∀ L : ι, (t L).Nonempty := by
    intro L
    haveI hfin : FiniteDimensional F L.1 := L.2.1
    haveI hnorm : Normal F L.1 := L.2.2
    haveI : NumberField ↥L.1 := NumberField.of_module_finite F ↥L.1
    haveI : IsGalois F ↥L.1 := ⟨⟩
    -- The traces of `A` and `B` on `L` have equal traces on `F`, namely the trace of `A` on `F`.
    have hPQ : (A.comap (algebraMap ↥L.1 K')).comap (algebraMap F ↥L.1) =
        (B.comap (algebraMap ↥L.1 K')).comap (algebraMap F ↥L.1) := by
      rw [ValuationSubring.comap_comap, ValuationSubring.comap_comap,
        ← IsScalarTower.algebraMap_eq F ↥L.1 K']
      exact hAB
    have hPC : (A.comap (algebraMap ↥L.1 K')).comap (algebraMap F ↥L.1) ≠ ⊤ := by
      rw [ValuationSubring.comap_comap, ← IsScalarTower.algebraMap_eq F ↥L.1 K']
      exact hC
    -- The traces on `L` are proper valuation subrings of `L`.
    have hP : A.comap (algebraMap ↥L.1 K') ≠ ⊤ := by
      intro h; apply hPC; rw [h]; ext x; simp [ValuationSubring.mem_comap]
    have hQ : B.comap (algebraMap ↥L.1 K') ≠ ⊤ := by
      intro h
      apply (hPQ ▸ hPC)
      rw [h]; ext x; simp [ValuationSubring.mem_comap]
    obtain ⟨σL, hσL⟩ :=
      Commons.NumberTheory.RamificationInertia.exists_smul_eq_of_comap_eq_of_finite
        (F := F) (L := ↥L.1) (A.comap (algebraMap ↥L.1 K'))
        (B.comap (algebraMap ↥L.1 K')) hP hQ hPQ
    -- Lift `σL` to an automorphism of `K'`, which is possible since `restrictNormalHom` is
    -- surjective.
    obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := ↥L.1) (E := K') σL
    refine ⟨σ, ?_⟩
    show (σ • A).comap (algebraMap ↥L.1 K') = B.comap (algebraMap ↥L.1 K')
    rw [Commons.FieldTheory.Galois.comap_smul_eq_restrictNormalHom_smul, hσ, hσL]
  -- **Directedness.**  Restricting the trace along an inclusion of intermediate fields.
  have htd : Directed (· ⊇ ·) t := by
    intro L₁ L₂
    haveI : FiniteDimensional F L₁.1 := L₁.2.1
    haveI : FiniteDimensional F L₂.1 := L₂.2.1
    haveI : Normal F L₁.1 := L₁.2.2
    haveI : Normal F L₂.1 := L₂.2.2
    refine ⟨⟨L₁.1 ⊔ L₂.1, IntermediateField.finiteDimensional_sup L₁.1 L₂.1,
      IntermediateField.normal_sup F K' L₁.1 L₂.1⟩, ?_, ?_⟩
    · intro σ hσ
      simp only [t, Set.mem_ofPred_eq] at hσ ⊢
      rw [← Commons.RingTheory.Valuation.comap_inclusion_comap_eq (le_sup_left : L₁.1 ≤ _) (σ • A),
        hσ, Commons.RingTheory.Valuation.comap_inclusion_comap_eq (le_sup_left : L₁.1 ≤ _) B]
    · intro σ hσ
      simp only [t, Set.mem_ofPred_eq] at hσ ⊢
      rw [← Commons.RingTheory.Valuation.comap_inclusion_comap_eq (le_sup_right : L₂.1 ≤ _) (σ • A),
        hσ, Commons.RingTheory.Valuation.comap_inclusion_comap_eq (le_sup_right : L₂.1 ≤ _) B]
  -- **Closedness.**  Via continuity of `restrictNormalHom` into the discrete finite group
  -- `Gal(L/F)`.
  have htcl : ∀ L : ι, IsClosed (t L) := by
    intro L
    haveI hfin : FiniteDimensional F L.1 := L.2.1
    haveI hnorm : Normal F L.1 := L.2.2
    have heq : t L = (AlgEquiv.restrictNormalHom (F := F) (K₁ := K') L.1) ⁻¹'
        {g : ↥L.1 ≃ₐ[F] ↥L.1 |
          g • (A.comap (algebraMap ↥L.1 K')) = B.comap (algebraMap ↥L.1 K')} := by
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
  -- `σ • A` and `B` have the same trace on every finite normal intermediate field, hence are
  -- equal.
  refine Commons.FieldTheory.Galois.eq_of_comap_eq_forall_finite_normal
    (K := F) (K' := K') (A := σ • A) (B := B) ?_
  intro L hfin hnorm
  exact Set.mem_iInter.mp hσ ⟨L, hfin, hnorm⟩

end Commons.FieldTheory.Galois
