import Mathlib
import Submission.NK.LocalInputs.Defs
import Submission.NK.Reconstruct.exists_isFrobElementAt_split_of_restrict
import Submission.NK.Reconstruct.exists_split_frobAt_unramified
import Submission.NK.Reconstruct.frobElementAt
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.Reconstruct

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

theorem exists_isFrobElementAt_split_awayFromL {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    [IsGalois ℚ Ω] (L : NK.Reconstruct.FrobLevel ℚ Ω) [IsSepClosure ↥L.L Ω] (ℓ : ℕ) [Fact ℓ.Prime]
    (hC : ∀ (N : IntermediateField ↥L.L Ω) [FiniteDimensional ↥L.L N] [Normal ↥L.L N]
      [NumberField ↥N] (τ : Gal(↥N/↥L.L)),
      ∃ (𝔭 : NK.Chebotarev.PrimeIdeal ↥L.L) (P : NK.Chebotarev.PrimeIdeal ↥N),
        P.asIdeal.LiesOver 𝔭.asIdeal ∧ NK.Reconstruct.SplitsCompletelyOverRat 𝔭 ∧
        P.asIdeal.ramificationIdx (NumberField.RingOfIntegers ↥L.L) = 1 ∧
        NK.Chebotarev.IsFrobAt (K := ↥L.L) (L := ↥N) P τ ∧
        NK.LocalInputs.primeBelowNat ↥L.L 𝔭 ≠ ℓ)
    (T : IntermediateField ↥L.L Ω) [FiniteDimensional ↥L.L T] [Normal ↥L.L T] [NumberField ↥T]
    (τ : Gal(↥T/↥L.L)) :
    ∃ (𝔭 : NK.Chebotarev.PrimeIdeal ↥L.L) (σ : Gal(Ω/↥L.L)),
      NK.Reconstruct.SplitsCompletelyOverRat 𝔭 ∧ NK.Reconstruct.IsFrobElementAt 𝔭 σ ∧
      NK.LocalInputs.primeBelowNat ↥L.L 𝔭 ≠ ℓ ∧
      AlgEquiv.restrictNormalHom (F := ↥L.L) (K₁ := Ω) T σ = τ := by
  classical
  haveI : IsGalois ↥L.L Ω := inferInstance
  -- The split Čebotarev input at `(T, τ)` fixes the prime `𝔭` (away from `ℓ`) and the Frobenius
  -- datum on `T`.
  obtain ⟨𝔭, P₀, hP₀, hsplit, he₀, hτ₀, hℓ⟩ := hC T τ
  -- The index set: the finite normal number-field levels of `Ω/L` containing `T`.
  let ι := {M : IntermediateField ↥L.L Ω // T ≤ M ∧ FiniteDimensional ↥L.L M ∧ Normal ↥L.L M ∧
    NumberField ↥M}
  -- The family of conditions: `σ` restricts to `τ` on `T` and is a Frobenius element at a prime
  -- above `𝔭` on `M`.
  let t : ι → Set Gal(Ω/↥L.L) := fun M => by
    letI : FiniteDimensional ↥L.L M.1 := M.2.2.1
    letI : Normal ↥L.L M.1 := M.2.2.2.1
    letI : NumberField ↥M.1 := M.2.2.2.2
    exact {σ : Gal(Ω/↥L.L) |
      AlgEquiv.restrictNormalHom (F := ↥L.L) (K₁ := Ω) T σ = τ ∧
        ∃ Q : NK.Chebotarev.PrimeIdeal ↥M.1, Q.asIdeal.LiesOver 𝔭.asIdeal ∧
          NK.Chebotarev.IsFrobAt (K := ↥L.L) (L := ↥M.1) Q
            (AlgEquiv.restrictNormalHom (F := ↥L.L) (K₁ := Ω) M.1 σ)}
  haveI hιne : Nonempty ι :=
    ⟨⟨T, le_rfl, inferInstance, inferInstance, inferInstance⟩⟩
  -- The family is directed: the condition at a compositum implies the conditions at the factors.
  have hdir : Directed (· ⊇ ·) t := by
    intro M₁ M₂
    haveI : FiniteDimensional ↥L.L M₁.1 := M₁.2.2.1
    haveI : Normal ↥L.L M₁.1 := M₁.2.2.2.1
    haveI : NumberField ↥M₁.1 := M₁.2.2.2.2
    haveI : FiniteDimensional ↥L.L M₂.1 := M₂.2.2.1
    haveI : Normal ↥L.L M₂.1 := M₂.2.2.2.1
    haveI : NumberField ↥M₂.1 := M₂.2.2.2.2
    haveI : FiniteDimensional ↥L.L ↥(M₁.1 ⊔ M₂.1) := inferInstance
    haveI : Normal ↥L.L ↥(M₁.1 ⊔ M₂.1) := inferInstance
    haveI : NumberField ↥(M₁.1 ⊔ M₂.1) :=
      Commons.NumberTheory.NumberField.numberField_of_intermediateField (K := ↥L.L) (K' := Ω)
        (M₁.1 ⊔ M₂.1)
    refine ⟨⟨M₁.1 ⊔ M₂.1, M₁.2.1.trans le_sup_left, inferInstance, inferInstance,
      inferInstance⟩, ?_, ?_⟩
    · intro σ hσ
      exact ⟨hσ.1, NK.Chebotarev.exists_isFrobAtPrime_of_le M₁.1 (M₁.1 ⊔ M₂.1) le_sup_left
        hσ.2⟩
    · intro σ hσ
      exact ⟨hσ.1, NK.Chebotarev.exists_isFrobAtPrime_of_le M₂.1 (M₁.1 ⊔ M₂.1) le_sup_right
        hσ.2⟩
  -- Each condition is satisfied.
  have hne : ∀ M : ι, (t M).Nonempty := by
    intro M
    haveI : FiniteDimensional ↥L.L M.1 := M.2.2.1
    haveI : Normal ↥L.L M.1 := M.2.2.2.1
    haveI : NumberField ↥M.1 := M.2.2.2.2
    obtain ⟨σ, hσ₁, hσ₂⟩ :=
      NK.Chebotarev.exists_sigma_restrict_eq_and_isFrobAtPrime (K := ↥L.L) (K' := Ω)
        T M.1 M.2.1 𝔭 P₀ τ hP₀ he₀ hτ₀
    exact ⟨σ, hσ₁, hσ₂⟩
  -- Each condition is closed: it is the preimage of a subset of the finite group `Gal(↥M/L)`.
  have hcl : ∀ M : ι, IsClosed (t M) := by
    intro M
    haveI : FiniteDimensional ↥L.L M.1 := M.2.2.1
    haveI : Normal ↥L.L M.1 := M.2.2.2.1
    haveI : NumberField ↥M.1 := M.2.2.2.2
    have hτ' : IsClosed ((AlgEquiv.restrictNormalHom (F := ↥L.L) (K₁ := Ω) T) ⁻¹' {τ}) :=
      IsClosed.preimage (InfiniteGalois.restrictNormalHom_continuous T) (isClosed_discrete _)
    have hfr : IsClosed ((AlgEquiv.restrictNormalHom (F := ↥L.L) (K₁ := Ω) M.1) ⁻¹'
        {ρ : Gal(↥M.1/↥L.L) | ∃ Q : NK.Chebotarev.PrimeIdeal ↥M.1,
          Q.asIdeal.LiesOver 𝔭.asIdeal ∧
            NK.Chebotarev.IsFrobAt (K := ↥L.L) (L := ↥M.1) Q ρ}) :=
      IsClosed.preimage (InfiniteGalois.restrictNormalHom_continuous M.1) (isClosed_discrete _)
    rw [show t M = ((AlgEquiv.restrictNormalHom (F := ↥L.L) (K₁ := Ω) T) ⁻¹' {τ}) ∩
        ((AlgEquiv.restrictNormalHom (F := ↥L.L) (K₁ := Ω) M.1) ⁻¹'
          {ρ : Gal(↥M.1/↥L.L) | ∃ Q : NK.Chebotarev.PrimeIdeal ↥M.1,
            Q.asIdeal.LiesOver 𝔭.asIdeal ∧
              NK.Chebotarev.IsFrobAt (K := ↥L.L) (L := ↥M.1) Q ρ}) from by
      ext σ
      exact Iff.rfl]
    exact hτ'.inter hfr
  -- Compactness: the intersection of the family is nonempty.
  obtain ⟨σ, hσ⟩ :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t hdir hne
      (fun M => (hcl M).isCompact) hcl
  have hT : AlgEquiv.restrictNormalHom (F := ↥L.L) (K₁ := Ω) T σ = τ :=
    (Set.mem_iInter.mp hσ ⟨T, le_rfl, inferInstance, inferInstance, inferInstance⟩).1
  refine ⟨𝔭, σ, hsplit, ?_, hℓ, hT⟩
  -- On an arbitrary finite normal level `N/L` of `Ω`, apply the condition at `N ⊔ T`.
  intro N FinN NormN NFN
  haveI : FiniteDimensional ↥L.L N := FinN
  haveI : Normal ↥L.L N := NormN
  haveI : NumberField ↥N := NFN
  haveI : FiniteDimensional ↥L.L ↥(N ⊔ T) := inferInstance
  haveI : Normal ↥L.L ↥(N ⊔ T) := inferInstance
  haveI : NumberField ↥(N ⊔ T) :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField (K := ↥L.L) (K' := Ω)
      (N ⊔ T)
  exact NK.Chebotarev.exists_isFrobAtPrime_of_le N (N ⊔ T) le_sup_left
    (Set.mem_iInter.mp hσ ⟨N ⊔ T, le_sup_right, inferInstance, inferInstance,
      inferInstance⟩).2

end NK.Reconstruct
