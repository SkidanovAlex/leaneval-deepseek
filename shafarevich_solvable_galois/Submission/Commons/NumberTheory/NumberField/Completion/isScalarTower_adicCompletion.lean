import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_mem_integers
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The algebra tower `K → K_Q → L_q`

Let `L / K` be an extension of number fields, let `Q` be a height-one prime ideal of the ring of
integers of `K` and let `q` be a height-one prime of the ring of integers of `L` lying over `Q`.
The inclusion `K → L` induces a ring homomorphism
`Commons.RingTheory.Henselian.adicCompletionMap Q q hq : Q.adicCompletion K →+* q.adicCompletion L`
between the corresponding adic completions, which extends the map `algebraMap K L` on the dense
subfields.  Equipping `q.adicCompletion L` with the `Q.adicCompletion K`-algebra structure given
by this ring homomorphism, the diagram

```
K  --→  K_Q
|        |
↓        ↓
L  --→  L_q
```

is a tower: the statement below records that `K → Q.adicCompletion K → q.adicCompletion L` is a
scalar tower, which is what makes `q.adicCompletion L` available as a `K`-algebra both through `K`
and through `Q.adicCompletion K`, consistently with the structure map `adicCompletionMap`.
-/

set_option linter.style.haveILetI false

open IsDedekindDomain.HeightOneSpectrum

namespace Commons.NumberTheory.NumberField.Completion

/-- The `Q.adicCompletion K`-algebra structure on `q.adicCompletion L` induced by
`adicCompletionMap Q q hq` turns `K → Q.adicCompletion K → q.adicCompletion L` into a tower of
algebras.  Equivalently, `adicCompletionMap Q q hq` intertwines the structure maps from `K`: it
sends the image of `x : K` in `Q.adicCompletion K` to the image of `algebraMap K L x` in
`q.adicCompletion L`. -/
theorem isScalarTower_adicCompletion {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    IsScalarTower K (Q.adicCompletion K) (q.adicCompletion L) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
  -- `adicCompletionMap` is `algebraMap (Q.adicCompletion K) (q.adicCompletion L)` by definition,
  -- the coercion `K → Q.adicCompletion K` is `algebraMap K (Q.adicCompletion K)`, and the
  -- coercion `K → q.adicCompletion L` is `algebraMap K (q.adicCompletion L)`; so the claim is
  -- exactly `adicCompletionMap_apply`.
  have h1 : algebraMap K (Q.adicCompletion K) x = (x : Q.adicCompletion K) :=
    congrFun (algebraMap_adicCompletion (v := Q) (S := K) (K := K)) x
  have h2 : algebraMap K (q.adicCompletion L) x = (algebraMap K L x : q.adicCompletion L) :=
    congrFun (algebraMap_adicCompletion (v := q) (S := K) (K := L)) x
  rw [RingHom.algebraMap_toAlgebra, h1, h2,
    Commons.RingTheory.Henselian.adicCompletionMap_apply Q q hq x]

end Commons.NumberTheory.NumberField.Completion
