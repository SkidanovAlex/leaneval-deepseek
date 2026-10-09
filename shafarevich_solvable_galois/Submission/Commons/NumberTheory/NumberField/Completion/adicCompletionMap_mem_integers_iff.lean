import Mathlib
import Submission.Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_mem_integers_of_integers
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Integrality of an element and of its image under the adic-completion map

Let `L / K` be a finite extension of number fields, `Q` a height-one prime of `𝓞 K` and `q` a
height-one prime of `𝓞 L` lying over `Q`.  The induced ring homomorphism of adic completions

`Commons.RingTheory.Henselian.adicCompletionMap Q q hq : Q.adicCompletion K →+* q.adicCompletion L`

satisfies, for every `x : Q.adicCompletion K`,

`adicCompletionMap Q q hq x ∈ q.adicCompletionIntegers L ↔ x ∈ Q.adicCompletionIntegers K`,

i.e. it reflects as well as preserves integrality.

The forward implication is `Commons.RingTheory.Henselian.adicCompletionMap_mem_integers`.
For the converse, by `Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow`
the valuation of the image is the `e`-th power of the valuation of `x`, where
`e = q.asIdeal.ramificationIdx (𝓞 K) ≥ 1` is the ramification index of `q` over `Q`; thus
`v (map x) ≤ 1` forces `v x ≤ 1`, which is exactly integrality of `x`.
-/

open scoped NumberField

namespace Commons.NumberTheory.NumberField.Completion

open IsDedekindDomain.HeightOneSpectrum

theorem adicCompletionMap_mem_integers_iff {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) (x : Q.adicCompletion K) :
    Commons.RingTheory.Henselian.adicCompletionMap Q q hq x ∈
        (q.adicCompletionIntegers L : Set (q.adicCompletion L)) ↔
      x ∈ (Q.adicCompletionIntegers K : Set (Q.adicCompletion K)) := by
  constructor
  · -- `v (map x) ≤ 1` forces `v x ≤ 1`, because `v (map x) = (v x) ^ e` with `e ≥ 1`
    intro h
    have h' : Valued.v (Commons.RingTheory.Henselian.adicCompletionMap Q q hq x) ≤ 1 :=
      (mem_adicCompletionIntegers (R := 𝓞 L) L q).mp h
    rw [val_adicCompletionMap_eq_pow Q q hq x] at h'
    apply (mem_adicCompletionIntegers (R := 𝓞 K) K Q).mpr
    by_contra hx
    rw [not_le] at hx
    have he : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) ≠ 0 :=
      (Ideal.ramificationIdx_pos (NumberField.RingOfIntegers K) q.asIdeal).ne'
    have : 1 < (Valued.v x) ^ q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) :=
      one_lt_pow₀ hx he
    exact absurd h' (not_le.mpr this)
  · -- integrality is preserved by the map of adic completions
    intro h
    exact Commons.RingTheory.Henselian.adicCompletionMap_mem_integers_of_integers Q q hq h

end Commons.NumberTheory.NumberField.Completion
