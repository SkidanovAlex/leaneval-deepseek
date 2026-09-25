import Mathlib
import Submission.Work.QuadraticFields.Ramification
import Submission.Commons.NumberTheory.NumberField.differentIdeal_eq_top_of_ramificationIdx

/-!
# Unramified at all finite primes ⟹ trivial relative different

If `M/F` is an extension of number fields in which every prime ideal `𝔓` of `𝓞 M` lying over a
nonzero prime `𝔭` of `𝓞 F` has ramification index one (`Work.QuadraticFields.
IsUnramifiedAtFinitePrimes F M`), then the relative different `differentIdeal (𝓞 F) (𝓞 M)` is
the unit ideal.

The argument is the standard one:

* every prime `Q ≠ ⊥` of `𝓞 M` contracts to a nonzero prime `Q.under (𝓞 F)` of `𝓞 F` (integrality),
  and `Q ∈ (Q.under (𝓞 F)).primesOver (𝓞 M)`; so the hypothesis gives
  `Q.ramificationIdx (𝓞 F) = 1`, which is equivalent to `¬ Q ∣ differentIdeal (𝓞 F) (𝓞 M)`
  (`Commons.NumberTheory.NumberField.ramificationIdx_one_iff_not_dvd_differentIdeal`);
* the zero prime is harmless: `⊥ ∣ 𝔡` would force `𝔡 = ⊥`, contradicting `differentIdeal_ne_bot`;
* finally, a nonzero ideal of a Dedekind domain that is divisible by no prime is the unit ideal
  (`Commons.NumberTheory.NumberField.differentIdeal_eq_top_of_forall_not_dvd`).
-/

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ClassFieldTower

theorem differentIdeal_eq_top_of_isUnramifiedAtFinitePrimes {F M : Type*} [Field F] [NumberField F]
    [Field M] [NumberField M] [Algebra F M]
    (h : Work.QuadraticFields.IsUnramifiedAtFinitePrimes F M) :
    differentIdeal (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers M) = ⊤ := by
  classical
  refine Commons.NumberTheory.NumberField.differentIdeal_eq_top_of_forall_not_dvd
    (E := F) (K := M) ?_
  intro Q hQ
  by_cases hQbot : Q = ⊥
  · -- the zero ideal cannot divide a nonzero ideal
    subst hQbot
    intro hdvd
    obtain ⟨c, hc⟩ := hdvd
    have hbot : differentIdeal (𝓞 F) (𝓞 M) = ⊥ := by rw [hc]; simp
    exact differentIdeal_ne_bot hbot
  · -- a nonzero prime `Q` contracts to a nonzero prime of `𝓞 F`, over which it is unramified
    rw [Commons.NumberTheory.NumberField.ramificationIdx_one_iff_not_dvd_differentIdeal
      (E := F) (K := M) Q hQ]
    exact h (Q.under (𝓞 F)) Q (Ideal.IsPrime.under (𝓞 F) Q)
      (Ideal.under_ne_bot (𝓞 F) hQbot) ⟨hQ, Ideal.over_under Q⟩

end Work.ClassFieldTower
