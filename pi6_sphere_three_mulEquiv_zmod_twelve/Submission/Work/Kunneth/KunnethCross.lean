import Mathlib
import Submission.Work.Kunneth.CrossGen
import Submission.Work.Kunneth.kunneth_homology

/-!
# The Künneth isomorphism in its cross-product form

`Work.Kunneth.kunneth_homology` produces *an* isomorphism

`Hₙ(C ⊗ D) ≅ ⨁_{p+q=n} H_p(C) ⊗ H_q(D)`

for chain complexes `D` with projective terms and projective homology.  This module fixes that
isomorphism once and for all (`kunnethHomIso`), and defines **the assembled cross-product map**

`Work.Kunneth.crossSumMap : ⨁_{p+q=n} H_p(C) ⊗ H_q(D) → Hₙ(C ⊗ D)`

as its inverse.  The mathematical content of the Künneth theorem in this form is the *computation
rule* `Work.Kunneth.crossSumMap_lof_shuffle`: on the class of `u ⊗ v`, with `u` and `v` cycles, the
map is the class of the Eilenberg–Zilber shuffle chain `u ⊗ v` of `crossCycTens` — i.e. the map *is*
the cross product.  Once that rule is known, `crossSumMap` is (by construction) an isomorphism and
the two descriptions agree.

## Main results

* `Work.Kunneth.kunnethHomIso` — the Künneth isomorphism, as a named isomorphism;
* `Work.Kunneth.crossSumMap` — the assembled cross-product map `⊕_{p+q=n} H_p ⊗ H_q → Hₙ`;
* `Work.Kunneth.crossSumMap_lof_shuffle` — its computation rule (the cross-product form of Künneth).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-- **The Künneth isomorphism** of `Work.Kunneth.kunneth_homology`, as a named isomorphism
`Hₙ(C ⊗ D) ≅ ⨁_{p+q=n} H_p(C) ⊗ H_q(D)`. -/
noncomputable def kunnethHomIso (C D : ChainComplex (ModuleCat ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) (n : ℕ) :
    (tpC C D).homology n ≅ (tpC (homSum C) (homSum D)).X n :=
  Classical.choice (kunneth_homology C D hD hH n)

/-- **The assembled cross-product map** `⨁_{p+q=n} H_p(C) ⊗ H_q(D) → Hₙ(C ⊗ D)`: the inverse of the
Künneth isomorphism. -/
noncomputable def crossSumMap (C D : ChainComplex (ModuleCat ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) (n : ℕ) :
    ↥((tpC (homSum C) (homSum D)).X n) →ₗ[ℤ] ↥((tpC C D).homology n) :=
  (kunnethHomIso C D hD hH n).inv.hom

/-- The structure map of the direct sum `⨁_{p+q=n} H_p(C) ⊗ H_q(D)`, at the bidegree `(p,q)`. -/
abbrev crossSummandLof (C D : ChainComplex (ModuleCat ℤ) ℕ) (n p q : ℕ) (hpq : p + q = n) :
    ↥(C.homology p ⊗ D.homology q) →ₗ[ℤ] ↥((tpC (homSum C) (homSum D)).X n) :=
  DirectSum.lof ℤ (tpIdx n)
    (fun pq : tpIdx n => ↥((homSum C).X pq.1.1 ⊗ (homSum D).X pq.1.2)) ⟨(p, q), hpq⟩

/-! ## The cross-product form of the Künneth theorem

The mathematical content of the Künneth theorem in this form is the *computation rule*

```
Work.Kunneth.crossSumMap C D hD hH n
    (crossSummandLof C D n p q hpq ((C.homologyπ p).hom u ⊗ₜ[ℤ] (D.homologyπ q).hom v))
  = ((tpC C D).homologyπ n).hom (crossCycTens C D n p q hpq (u ⊗ₜ[ℤ] v))
```

for all cycles `u`, `v`: on the class of `u ⊗ v` the Künneth isomorphism is the cross product, i.e.
the class of the Eilenberg–Zilber shuffle chain `u ⊗ v`.  It is stated (and proved) separately in
`Submission/Work/Kunneth/kunnethCrossExistence.lean` (see README §8). -/

end

end Work.Kunneth
