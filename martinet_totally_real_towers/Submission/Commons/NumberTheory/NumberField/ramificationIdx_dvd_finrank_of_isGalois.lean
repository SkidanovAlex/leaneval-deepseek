import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.Algebra.CharZero.Infinite

set_option linter.style.haveILetI false

namespace Commons.NumberTheory.NumberField

theorem ramificationIdx_dvd_finrank_of_isGalois {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (P : Ideal (NumberField.RingOfIntegers L)) [P.IsPrime] :
    P.ramificationIdx (NumberField.RingOfIntegers K) ∣ Module.finrank K L := by
  letI : MulSemiringAction Gal(L/K) (NumberField.RingOfIntegers L) :=
    IsIntegralClosure.MulSemiringAction (NumberField.RingOfIntegers K) K L
      (NumberField.RingOfIntegers L)
  haveI hGal : IsGaloisGroup Gal(L/K) (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L) :=
    IsGaloisGroup.of_isFractionRing Gal(L/K) (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L) K L
  -- the fundamental identity in the Galois case
  have hfund := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (P.under (NumberField.RingOfIntegers K)) (NumberField.RingOfIntegers L) Gal(L/K)
  -- all ramification indices over a fixed prime agree
  have he : Ideal.ramificationIdxIn (P.under (NumberField.RingOfIntegers K))
        (NumberField.RingOfIntegers L)
      = P.ramificationIdx (NumberField.RingOfIntegers K) :=
    Ideal.ramificationIdxIn_eq_ramificationIdx (P.under (NumberField.RingOfIntegers K)) P Gal(L/K)
  have hcard : Nat.card Gal(L/K) = Module.finrank K L := IsGalois.card_aut_eq_finrank K L
  refine ⟨((P.under (NumberField.RingOfIntegers K)).primesOver
        (NumberField.RingOfIntegers L)).ncard
      * Ideal.inertiaDegIn (P.under (NumberField.RingOfIntegers K))
        (NumberField.RingOfIntegers L), ?_⟩
  rw [← hcard, ← hfund, he, mul_left_comm]

end Commons.NumberTheory.NumberField