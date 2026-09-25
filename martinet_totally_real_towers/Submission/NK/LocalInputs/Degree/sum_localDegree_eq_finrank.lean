import Mathlib
import Submission.NK.Mine.CommonsAdicSumAPI
import Submission.NK.LocalInputs.Defs
import Submission.NK.LocalInputs.Degree.localDegree_eq_ramificationIdx_mul_inertiaDeg

open scoped NumberField
open IsDedekindDomain.HeightOneSpectrum

set_option linter.style.haveILetI false

namespace NK.LocalInputs.Degree

/-- **The sum of the absolute local degrees equals the global degree.**

Let `K` be a number field and `P` a finite prime of `ℚ`.  Summing the absolute local degrees
`[K_𝔮 : ℚ_p]` (`NK.LocalInputs.localDegree K 𝔮`) over all finite primes `𝔮` of `K` lying over
`P` gives the degree `[K : ℚ]`.

The proof rewrites each local degree as the product `e(𝔮/p) · f(𝔮/p)` of the ramification index
and the inertia degree of `𝔮` over `ℤ` (`localDegree_eq_ramificationIdx_mul_inertiaDeg`), moves
these invariants from `ℤ` to `𝓞 ℚ`, and then applies the global fundamental identity
`∑_{𝔮 | P} e(𝔮/P) · f(𝔮/P) = [K : ℚ]` (`Ideal.sum_ramification_inertia_eq_finrank`) together
with `IsFractionRing.finrank_eq`. -/
theorem sum_localDegree_eq_finrank (K : Type*) [Field K] [NumberField K]
    (P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    (∑ qq : P.asIdeal.primesOver (NumberField.RingOfIntegers K),
      NK.LocalInputs.localDegree K
        (Commons.NumberTheory.NumberField.Completion.sumFinrank_eQ (K := ℚ) (L := K) P qq))
      = Module.finrank ℚ K := by
  classical
  have hterm : ∀ qq : P.asIdeal.primesOver (NumberField.RingOfIntegers K),
      NK.LocalInputs.localDegree K
        (Commons.NumberTheory.NumberField.Completion.sumFinrank_eQ (K := ℚ) (L := K) P qq)
      = qq.1.ramificationIdx (NumberField.RingOfIntegers ℚ)
          * qq.1.inertiaDeg (NumberField.RingOfIntegers ℚ) := by
    intro qq
    have hne : qq.1 ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver P.ne_bot qq.2
    haveI : qq.1.IsPrime := qq.2.1
    rw [NK.LocalInputs.Degree.localDegree_eq_ramificationIdx_mul_inertiaDeg]
    simp only [Commons.NumberTheory.NumberField.Completion.sumFinrank_eQ]
    rw [← NK.LocalInputs.Degree.ramificationIdx_rat_eq qq.1 hne,
      ← NK.LocalInputs.Degree.inertiaDeg_rat_eq qq.1 hne]
  rw [Finset.sum_congr rfl (fun qq _ => hterm qq)]
  rw [Ideal.sum_ramification_inertia_eq_finrank (R := NumberField.RingOfIntegers ℚ)
    (S := NumberField.RingOfIntegers K) (p := P.asIdeal)]
  exact (IsFractionRing.finrank_eq (NumberField.RingOfIntegers ℚ) ℚ
    (NumberField.RingOfIntegers K) K).symm

end NK.LocalInputs.Degree
