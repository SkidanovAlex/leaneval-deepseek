import Mathlib
import Submission.Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.Completion.sumFinrank_adicCompletion_le_finrank

open scoped NumberField
namespace Commons.NumberTheory.NumberField.Completion

open IsDedekindDomain.HeightOneSpectrum

theorem finrank_adicCompletion_le_finrank {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    @Module.finrank (Q.adicCompletion K) (q.adicCompletion L) _ _
        (RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)).toModule
      ≤ Module.finrank K L := by
  classical
  let f : Q.asIdeal.primesOver (𝓞 L) → ℕ := fun qq =>
    @Module.finrank (Q.adicCompletion K) ((sumFinrank_eQ Q qq).adicCompletion L) _ _
      (RingHom.toAlgebra
        (Commons.RingTheory.Henselian.adicCompletionMap Q (sumFinrank_eQ Q qq) qq.2.2)).toModule
  have hb := sumFinrank_adicCompletion_le_finrank (K := K) (L := L) Q
  change (∑ qq : Q.asIdeal.primesOver (𝓞 L), f qq) ≤ Module.finrank K L at hb
  let qq₀ : Q.asIdeal.primesOver (𝓞 L) := ⟨q.asIdeal, q.isPrime, hq⟩
  have hle : f qq₀ ≤ ∑ qq, f qq :=
    Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ qq₀)
  exact hle.trans hb

end Commons.NumberTheory.NumberField.Completion
