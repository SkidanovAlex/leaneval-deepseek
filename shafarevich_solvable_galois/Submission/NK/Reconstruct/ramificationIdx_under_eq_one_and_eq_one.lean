import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RamificationInertia.Ramification
import Submission.NK.Chebotarev.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.Reconstruct

/-- **Unramifiedness transfers down a tower of number fields.**  If `P` is a prime of `𝓞 M`
unramified over the base number field `K`, then its contraction to an intermediate number field
`L` is unramified over `K` and `P` is unramified over `L`: both statements are the two factors of
the tower formula `e(P/K) = e(P ∩ 𝓞 L / K) · e(P / P ∩ 𝓞 L)`. -/
theorem ramificationIdx_under_eq_one_and_eq_one
    {K L M : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Field M] [NumberField M] [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M]
    (P : NK.Chebotarev.PrimeIdeal M)
    (h : P.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) :
    (P.under (NumberField.RingOfIntegers L)).asIdeal.ramificationIdx
        (NumberField.RingOfIntegers K) = 1 ∧
      P.asIdeal.ramificationIdx (NumberField.RingOfIntegers L) = 1 := by
  have hte := Ideal.ramificationIdx_tower (R := NumberField.RingOfIntegers K)
    (S := NumberField.RingOfIntegers L) (T := NumberField.RingOfIntegers M)
    (P.asIdeal.under (NumberField.RingOfIntegers L)) P.asIdeal
  rw [h] at hte
  exact ⟨(mul_eq_one.mp hte.symm).1, (mul_eq_one.mp hte.symm).2⟩

end NK.Reconstruct
