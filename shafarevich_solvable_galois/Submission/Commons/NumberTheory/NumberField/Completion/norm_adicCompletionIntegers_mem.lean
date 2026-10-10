import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.Commons.NumberTheory.NumberField.Completion.adicCompletionMap_mem_integers_iff
import Submission.Commons.NumberTheory.NumberField.Completion.val_norm_adicCompletion_eq_pow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Integrality of the norm on the ring of integers of an adic completion

Let `L / K` be a finite Galois extension of number fields, `Q` a height-one prime of `𝓞 K`
and `q` a height-one prime of `𝓞 L` lying over `Q`.  Via the ring homomorphism
`Commons.RingTheory.Henselian.adicCompletionMap Q q hq : Q.adicCompletion K →+* q.adicCompletion L`,
view the local field `L_q = q.adicCompletion L` as an extension of `K_Q = Q.adicCompletion K`.

Then the norm `N_{L_q / K_Q}` maps the ring of integers `q.adicCompletionIntegers L` into the
ring of integers `Q.adicCompletionIntegers K`.

The argument is the classical one.  For `x ∈ L_q` integral at `q`, the norm identity
`Commons.NumberTheory.NumberField.Completion.val_norm_adicCompletion_eq_pow` gives

`v_q (algebraMap (norm x)) = (v_q x) ^ [L_q : K_Q]`,

which is `≤ 1` because `v_q x ≤ 1`.  Equivalently the image of the norm under the map of
completions is integral at `q`.  Since `Commons.NumberTheory.NumberField.Completion.adicCompletionMap_mem_integers_iff`
says that this map preserves and reflects integrality, the norm is integral at `Q`.
-/

open scoped NumberField
open IsDedekindDomain.HeightOneSpectrum

set_option linter.style.haveILetI false

namespace Commons.NumberTheory.NumberField.Completion

theorem norm_adicCompletionIntegers_mem {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    ∀ x : q.adicCompletionIntegers L,
      Algebra.norm (Q.adicCompletion K) (x : q.adicCompletion L) ∈
        Q.adicCompletionIntegers K := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  intro x
  -- integrality of `x` at `q`
  have hx : Valued.v (x : q.adicCompletion L) ≤ 1 :=
    (mem_adicCompletionIntegers (R := 𝓞 L) L q).mp x.2
  -- the image of the norm under the map of completions is integral at `q`
  have hmap : Commons.RingTheory.Henselian.adicCompletionMap Q q hq
      (Algebra.norm (Q.adicCompletion K) (x : q.adicCompletion L)) ∈
        (q.adicCompletionIntegers L : Set (q.adicCompletion L)) := by
    apply (mem_adicCompletionIntegers (R := 𝓞 L) L q).mpr
    have hnorm := val_norm_adicCompletion_eq_pow Q q hq (x : q.adicCompletion L)
    rw [RingHom.algebraMap_toAlgebra] at hnorm
    rw [hnorm]
    exact pow_le_one₀ zero_le hx
  -- integrality is reflected by the map of completions
  exact (adicCompletionMap_mem_integers_iff Q q hq
    (Algebra.norm (Q.adicCompletion K) (x : q.adicCompletion L))).mp hmap

end Commons.NumberTheory.NumberField.Completion
