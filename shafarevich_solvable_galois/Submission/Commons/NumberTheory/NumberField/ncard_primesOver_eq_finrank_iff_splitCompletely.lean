import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.NumberTheory.NumberField

open Module

theorem ncard_primesOver_eq_finrank_iff_splitCompletely {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    (p.asIdeal.primesOver (NumberField.RingOfIntegers L)).ncard = Module.finrank K L ↔
      (p.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers L) = 1 ∧
        p.asIdeal.inertiaDegIn (NumberField.RingOfIntegers L) = 1) := by
  classical
  have hfund :
      (p.asIdeal.primesOver (NumberField.RingOfIntegers L)).ncard *
        (p.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers L) *
          p.asIdeal.inertiaDegIn (NumberField.RingOfIntegers L)) = Module.finrank K L := by
    rw [← IsGalois.card_aut_eq_finrank K L]
    exact Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
      (A := NumberField.RingOfIntegers K) (B := NumberField.RingOfIntegers L)
      (G := Gal(L/K)) p.asIdeal
  have hnpos : 0 < Module.finrank K L := Module.finrank_pos
  constructor
  · intro h
    have h2 :
        Module.finrank K L *
          (p.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers L) *
            p.asIdeal.inertiaDegIn (NumberField.RingOfIntegers L)) = Module.finrank K L := by
      calc Module.finrank K L *
            (p.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers L) *
              p.asIdeal.inertiaDegIn (NumberField.RingOfIntegers L))
          = (p.asIdeal.primesOver (NumberField.RingOfIntegers L)).ncard *
              (p.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers L) *
                p.asIdeal.inertiaDegIn (NumberField.RingOfIntegers L)) := by rw [h]
        _ = Module.finrank K L := hfund
    have hmul :
        p.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers L) *
          p.asIdeal.inertiaDegIn (NumberField.RingOfIntegers L) = 1 :=
      Nat.mul_left_cancel hnpos (by rw [mul_one]; exact h2)
    constructor
    · exact Nat.dvd_one.mp ⟨_, hmul.symm⟩
    · exact Nat.dvd_one.mp ⟨_, by rw [mul_comm]; exact hmul.symm⟩
  · rintro ⟨he, hf⟩
    rw [he, hf, mul_one, mul_one] at hfund
    exact hfund

end Commons.NumberTheory.NumberField