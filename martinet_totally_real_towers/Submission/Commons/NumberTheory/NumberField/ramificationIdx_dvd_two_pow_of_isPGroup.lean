import Mathlib
import Submission.Commons.NumberTheory.NumberField.ramificationIdx_dvd_finrank_of_isGalois

namespace Commons.NumberTheory.NumberField

/-- If `L/F` is Galois with Galois group a `2`-group, then every ramification index
`e(P | P ∩ F)` is a power of `2`.

Indeed `e` divides `[L : F] = |Gal(L/F)|`, which is a power of `2`. -/
theorem ramificationIdx_dvd_two_pow_of_isPGroup {F L : Type*} [Field F] [NumberField F] [Field L]
    [NumberField L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    (hG : IsPGroup 2 (L ≃ₐ[F] L)) (P : Ideal (NumberField.RingOfIntegers L)) [P.IsPrime] :
    ∃ k : ℕ, P.ramificationIdx (NumberField.RingOfIntegers F) = 2 ^ k := by
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := L ≃ₐ[F] L)).mp hG
  have hdvd : P.ramificationIdx (NumberField.RingOfIntegers F) ∣ 2 ^ n := by
    rw [← hn, IsGalois.card_aut_eq_finrank F L]
    exact ramificationIdx_dvd_finrank_of_isGalois (K := F) (L := L) P
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  exact ⟨k, hk⟩

end Commons.NumberTheory.NumberField
