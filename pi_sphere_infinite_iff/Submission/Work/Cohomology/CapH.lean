import Mathlib
import Submission.Work.Cohomology.exists_capH
import Submission.Work.Cohomology.CupRing

/-!
# The cap product pairing, packaged

`Submission/Work/Cohomology/exists_capH.lean` proves the existence of the cap product pairing
`H^n(X;R) × H_{n+m}(X;R) ⟶ H_m(X;R)` (as an unexplicit `∃`).  This file fixes the pairing once and
for all (`capPair`, with its cycle-level partner `capPairZ`) and records its computation rules:

* `capPair_apply` — on the classes of a cocycle `z` and a cycle `c` the value is the class of
  `capZ z c`;
* `capPairZ_iCycles` — the cycle-level value is the cap product of the underlying (co)chains,
  `iCycles (capZ z c) = cap (iCycles z) m (iCycles c)`.

With the Alexander–Whitney conventions of this repository the cap/cup identity
(`Work.Cohomology.kronecker_cap_cup`) reads `⟨β, c ⌢ α⟩ = ⟨α ⌣ β, c⟩`; its form on homology — the
engine of any intersection-form computation — is `Work.Cohomology.capPair_cup_kronecker`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

variable (R : Type) [CommRing R] (X : SSet)

/-- **The cap product on cycles**: a choice of the pairing `capZ` whose existence is
`Work.Cohomology.exists_capH`. -/
noncomputable def capPairZ (n m : ℕ) :
    ↑((cochainC R X).cycles n) →ₗ[R]
      ((chainC R X).cycles (n + m) →ₗ[R] (chainC R X).cycles m) :=
  Classical.choose (exists_capH R X) n m

/-- **The cap product pairing** `H^n(X;R) →ₗ (H_{n+m}(X;R) →ₗ H_m(X;R))`, a choice of the
pairing whose existence is `Work.Cohomology.exists_capH`. -/
noncomputable def capPair (n m : ℕ) :
    ↑((cochainC R X).homology n) →ₗ[R]
      ((chainC R X).homology (n + m) →ₗ[R] (chainC R X).homology m) :=
  Classical.choose (Classical.choose_spec (exists_capH R X)) n m

/-- **The computation rule for `capPairZ`**: on a cocycle `z` and a cycle `c` the cycle-level cap
product is the cap product of the underlying (co)chains. -/
theorem capPairZ_iCycles (n m : ℕ) (z : ↑((cochainC R X).cycles n))
    (c : ↑((chainC R X).cycles (n + m))) :
    (chainC R X).iCycles m (capPairZ R X n m z c)
      = cap R X ((cochainC R X).iCycles n z) m ((chainC R X).iCycles (n + m) c) :=
  (Classical.choose_spec (Classical.choose_spec (exists_capH R X))).1 n m z c

/-- **The computation rule for `capPair`**: on the classes of a cocycle `z` and a cycle `c` the value
is the homology class of `capPairZ z c`. -/
theorem capPair_apply (n m : ℕ) (z : ↑((cochainC R X).cycles n))
    (c : ↑((chainC R X).cycles (n + m))) :
    capPair R X n m ((cochainC R X).homologyπ n z)
        ((chainC R X).homologyπ (n + m) c)
      = (chainC R X).homologyπ m (capPairZ R X n m z c) :=
  (Classical.choose_spec (Classical.choose_spec (exists_capH R X))).2 n m z c

end

end Work.Cohomology
