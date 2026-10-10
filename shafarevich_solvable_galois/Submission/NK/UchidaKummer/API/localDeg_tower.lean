import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Submission.NK.UchidaKummer.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Multiplicativity of the local degree in a tower of number fields

For a tower `K ⊆ L ⊆ M` of number fields and non-zero primes
`p ⊆ 𝒪 K`, `P ⊆ 𝒪 L`, `Q ⊆ 𝒪 M` with `P` over `p` and `Q` over `P`, the local degree
`[M_Q : K_p] = e(Q|p) * f(Q|p)` is the product of the local degrees of the two steps:

`[M_Q : K_p] = [M_Q : L_P] * [L_P : K_p]`.

This is the multiplicativity of the ramification index and of the inertia degree in towers
(`Ideal.ramificationIdx_tower`, `Ideal.inertiaDeg_tower`).
-/

namespace NK.UchidaKummer.API

open IsDedekindDomain

theorem localDeg_tower {K L M : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Field M] [NumberField M] [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M] (p : NK.Chebotarev.PrimeIdeal K) (P : NK.Chebotarev.PrimeIdeal L)
    (Q : NK.Chebotarev.PrimeIdeal M) (hP : P.asIdeal.LiesOver p.asIdeal)
    (hQ : Q.asIdeal.LiesOver P.asIdeal) :
    NK.UchidaKummer.localDeg Q p =
      NK.UchidaKummer.localDeg Q P * NK.UchidaKummer.localDeg P p := by
  let hP' : P.asIdeal.LiesOver p.asIdeal := hP
  let hQ' : Q.asIdeal.LiesOver P.asIdeal := hQ
  have he := Ideal.ramificationIdx_tower (R := NumberField.RingOfIntegers K)
    (S := NumberField.RingOfIntegers L) (T := NumberField.RingOfIntegers M) P.asIdeal Q.asIdeal
  have hf := Ideal.inertiaDeg_tower (R := NumberField.RingOfIntegers K)
    (S := NumberField.RingOfIntegers L) (T := NumberField.RingOfIntegers M) P.asIdeal Q.asIdeal
  simp only [NK.UchidaKummer.localDeg]
  rw [he, hf]
  ring

end NK.UchidaKummer.API
