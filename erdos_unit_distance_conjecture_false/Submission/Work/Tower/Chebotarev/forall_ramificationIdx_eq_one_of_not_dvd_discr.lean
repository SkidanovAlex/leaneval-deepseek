import Mathlib
import Submission.Work.Tower.Chebotarev.Defs

namespace Work.Tower.Chebotarev

open NumberField
open scoped Classical nonZeroDivisors NumberField

/-- If the prime `q` does not divide the discriminant of the number field `K`, then `q` is
unramified in `K`: every prime of `𝓞 K` above `q` has ramification index one. -/
theorem forall_ramificationIdx_eq_one_of_not_dvd_discr {K : Type} [Field K] [NumberField K]
    (q : ℕ) [Fact (Nat.Prime q)] (h : ¬ (q : ℤ) ∣ NumberField.discr K) :
    ∀ P : (Ideal.span {(q : ℤ)}).primesOver (𝓞 K), P.1.ramificationIdx ℤ = 1 := by
  intro P
  have hp : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  have hunr : Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(q : ℤ)}) :=
    (NumberField.not_dvd_discr_iff_isUnramifiedIn K (𝓞 K) hp).mp h
  exact hunr.ramificationIdx_eq_one P.2.2

end Work.Tower.Chebotarev
