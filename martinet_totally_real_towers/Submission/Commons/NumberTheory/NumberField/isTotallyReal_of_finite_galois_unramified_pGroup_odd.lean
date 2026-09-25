import Mathlib
import Submission.Commons.NumberTheory.NumberField.isTotallyReal_of_isUnramifiedAtInfinitePlaces

namespace Commons.NumberTheory.NumberField

theorem isTotallyReal_of_finite_galois_unramified_pGroup_odd
    {F K : Type*} [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    [Field K] [NumberField K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    (hG : IsPGroup 3 (K ≃ₐ[F] K))
    (hdiff : differentIdeal (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers K) = ⊤) :
    NumberField.IsTotallyReal K := by
  have hodd : Odd (Nat.card (K ≃ₐ[F] K)) := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    haveI : Finite (K ≃ₐ[F] K) := inferInstance
    obtain ⟨n, hn⟩ := IsPGroup.exists_card_eq (G := K ≃ₐ[F] K) hG
    rw [hn]
    exact Odd.pow (show Odd (3 : ℕ) by norm_num)
  have hunram : IsUnramifiedAtInfinitePlaces F K :=
    IsUnramifiedAtInfinitePlaces_of_odd_card_aut (k := F) (K := K) hodd
  exact isTotallyReal_of_isUnramifiedAtInfinitePlaces F K

end Commons.NumberTheory.NumberField
