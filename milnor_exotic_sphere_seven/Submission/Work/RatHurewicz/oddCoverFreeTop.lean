import Mathlib
import Submission.Work.RatHurewicz.Basic
import Submission.Work.RatHurewicz.RelHomotopy
import Submission.Work.Serre.Models

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The free-top ℤ-spike Eilenberg–MacLane input of the sphere-specific route

This module records the definition `Work.RatHurewicz.OddCoverAcyclicUpTo`, the **free-top** form of
the odd step `C2` of the Serre blueprint, in the sphere-specific shape consumed by the sphere route
to the stable stems (`Work.RatHurewicz.sphere_stem_torsion`).

For odd `n`, a *range model* of `K(ℤ,n)` up to degree `N` (`Work.Serre.IsEMSpaceUpTo ℤ n N X pt`),
and a map `f : Sⁿ → X` inducing an isomorphism on `πₙ` (the "bottom cell"), the homotopy fibre
`E := hofib f` is the `n`-connected cover of `X`; the statement says that `E` is rationally acyclic
in every degree `0 < j ≤ M`, as soon as the range model is known through `M + 1`.

The range `M` is **free** (it is not capped by `2n-3`, the bound that the range-form `C2` statements
of `Submission/Work/Stems/Engine/C2Range.lean` carry).  This is the correction designed in
`Submission/Work/Stems/Engine/C2FreeTop.lean` (blueprint ADDENDUM 3 (B), (C)): with a free top the
range deficit that blocks the range-form mutual induction disappears, the loss being absorbed by
choosing the range-model bound `N` large enough at the start of the induction.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.RatHurewicz

noncomputable section

/-- **The free-top form of the odd step of `C2`.**  For `n` odd, `≥ 3`, a range model `X` of
`K(ℤ,n)` through degree `N` with `N ≥ M + n` (the bound that the free-top mutual induction of the
blueprint's ADDENDUM 3 (C) delivers: the `n`-step loss is absorbed by choosing `N` large), and a
`πₙ`-bijective map `f : Sⁿ → X`, the homotopy fibre of `f` is rationally acyclic in degrees
`0 < j ≤ M`. -/
def OddCoverAcyclicUpTo : Prop :=
  ∀ (n M N : ℕ) (hn : 3 ≤ n), Odd n → M + n ≤ N →
    ∀ (X : Type) [TopologicalSpace X] (pt : X),
      Work.Serre.IsEMSpaceUpTo ℤ n (by omega) N X pt →
        ∀ (s₀ : Work.Serre.Sph n) (f : C(Work.Serre.Sph n, X)),
          Function.Bijective (Work.Serre.piMapN f n s₀) →
            ∀ j : ℕ, 0 < j → j ≤ M →
              CategoryTheory.Limits.IsZero
                (Work.Serre.ratH
                  (TopCat.of (Work.RatHurewicz.homotopyFibre f s₀)) j)

end

end Work.RatHurewicz
