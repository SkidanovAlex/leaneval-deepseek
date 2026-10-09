import Mathlib
import Submission.NK.LocalInputs.Inputs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The absolute local degree of `ℚ` at a finite prime is `1`

`NK.LocalInputs.localDegree ℚ 𝔭` is by definition the dimension of the completion
`ℚ_𝔭 = 𝔭.adicCompletion ℚ` over `ℚ_p`, where `p` is the rational prime below `𝔭` and the algebra
structure on `𝔭.adicCompletion ℚ` over `p.adicCompletion ℚ` is the one induced by the transition
map `Commons.RingTheory.Henselian.adicCompletionMap`.

For `K = ℚ` the prime below `𝔭` is `𝔭` itself (the `LiesOver` relation on finite primes of `ℚ` is
equality), and the transition map from a finite prime of `ℚ` to itself is the identity of the
completion.  Hence `localDegree ℚ 𝔭 = Module.finrank ℚ_𝔭 ℚ_𝔭 = 1`.

The two ingredients are isolated below.

* `NK.LocalInputs.Degree.adicCompletionMap_self` — for *any* number field `K` and any finite
  prime `Q`, the transition map `adicCompletionMap Q Q` is the identity of `Q.adicCompletion K`.
  (The proof does not use `NumberField K`; it only records that source and target of the map
  coincide.)
* `NK.LocalInputs.Degree.eq_of_liesOver` — for `K = ℚ` the `LiesOver` relation on finite
  primes is equality, so the map featuring in `localDegree` is of the form `adicCompletionMap Q Q`.

Note the auxiliary definition `localDegreeOf`, which is *definitionally* `localDegree` for
`K = ℚ` (see `NK.LocalInputs.Degree.localDegree_eq_localDegreeOf`), but which presents the
algebra structure as a named `letI` binder so that the prime below `𝔭` can be replaced by `𝔭`
inside the statement.
-/

open scoped Classical NumberField
open IsDedekindDomain.HeightOneSpectrum

namespace NK.LocalInputs.Degree

/-- **The transition map from a finite prime to itself is the identity.**

For any number field `K` and any finite prime `Q`, the ring homomorphism
`adicCompletionMap Q Q : Q.adicCompletion K →+* Q.adicCompletion K` — the universal extension of
the identity of `K` to the `Q`-adic completion — is the identity. -/
lemma adicCompletionMap_self {K : Type*} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (h : Q.asIdeal.LiesOver Q.asIdeal) :
    Commons.RingTheory.Henselian.adicCompletionMap Q Q h = RingHom.id (Q.adicCompletion K) := by
  -- The underlying map of `WithVal`-spaces is `algebraMap (WithVal v) (WithVal v) = id`.
  have halg : algebraMap (WithVal (Q.valuation K)) (WithVal (Q.valuation K)) =
      RingHom.id (WithVal (Q.valuation K)) := rfl
  unfold Commons.RingTheory.Henselian.adicCompletionMap
  ext x
  simp only [RingHom.coe_comp, RingEquiv.toRingHom_eq_coe, Function.comp_apply, RingHom.id_apply,
    halg, UniformSpace.Completion.mapRingHom_id]
  cases x
  rfl

/-- **The `LiesOver` relation on finite primes of `ℚ` is equality.**

If the height-one prime `q` of `𝓞 ℚ = ℤ` lies over the height-one prime `Q`, then `Q = q`: the
contraction `q.asIdeal.under (𝓞 ℚ)` is `q.asIdeal` itself (the algebra map `𝓞 ℚ → 𝓞 ℚ` is the
identity), and equal ideals give equal height-one primes. -/
lemma eq_of_liesOver (Q q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (h : q.asIdeal.LiesOver Q.asIdeal) : Q = q :=
  IsDedekindDomain.HeightOneSpectrum.ext (by
    have h1 := h.over
    rw [h1]
    show Ideal.comap (algebraMap (NumberField.RingOfIntegers ℚ) (NumberField.RingOfIntegers ℚ))
      q.asIdeal = q.asIdeal
    rw [show (algebraMap (NumberField.RingOfIntegers ℚ) (NumberField.RingOfIntegers ℚ)) =
      RingHom.id (NumberField.RingOfIntegers ℚ) from rfl]
    simp)

/-- The absolute local degree `[ℚ_𝔮 : ℚ_Q]` attached to a pair of finite primes `Q`, `q` of `ℚ`
with `q` lying over `Q`, with the algebra structure induced by `adicCompletionMap Q q`.  It is
definitionally `NK.LocalInputs.localDegree ℚ 𝔭` for `Q = primeBelow ℚ 𝔭`, `q = 𝔭`. -/
noncomputable def localDegreeOf (Q q : IsDedekindDomain.HeightOneSpectrum
    (NumberField.RingOfIntegers ℚ)) (h : q.asIdeal.LiesOver Q.asIdeal) : ℕ := by
  letI := RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q h)
  exact Module.finrank (Q.adicCompletion ℚ) (q.adicCompletion ℚ)

/-- `localDegreeOf` computes `localDegree` for `K = ℚ` (the prime below is `primeBelow`). -/
theorem localDegree_eq_localDegreeOf
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    NK.LocalInputs.localDegree ℚ 𝔭 = localDegreeOf (NK.LocalInputs.primeBelow ℚ 𝔭) 𝔭
      (NK.LocalInputs.primeBelow_liesOver ℚ 𝔭) := rfl

/-- For `K = ℚ` the two primes are equal, so the transition map is the identity and the local
degree is `Module.finrank ℚ_𝔭 ℚ_𝔭 = 1`. -/
lemma localDegreeOf_eq_one (Q q : IsDedekindDomain.HeightOneSpectrum
    (NumberField.RingOfIntegers ℚ)) (h : q.asIdeal.LiesOver Q.asIdeal) :
    localDegreeOf Q q h = 1 := by
  have hQ : Q = q := eq_of_liesOver Q q h
  subst hQ
  unfold localDegreeOf
  rw [adicCompletionMap_self]
  exact Module.finrank_self _

/-- **The absolute local degree of `ℚ` at a finite prime is `1`.** -/
theorem localDegree_rat (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    NK.LocalInputs.localDegree ℚ 𝔭 = 1 := by
  rw [localDegree_eq_localDegreeOf]
  exact localDegreeOf_eq_one _ _ _

end NK.LocalInputs.Degree
