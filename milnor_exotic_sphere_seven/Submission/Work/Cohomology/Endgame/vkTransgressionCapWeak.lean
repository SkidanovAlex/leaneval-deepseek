import Submission.Work.Cohomology.Endgame.transgressionIso
import Submission.Work.Cohomology.Endgame.dshDelta
import Submission.Work.Cohomology.cohomologyPairVk
import Submission.Work.Cohomology.sphere3DiscPairDefs
import Submission.Work.Cohomology.RelCapHTransfer

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The weak Mayer–Vietoris transgression identity for the two-chart cover of `Vk (-2)`

This file is the endpoint of the transgression route (`Endgame/NOTES.md` §27–§30): it states, and
will prove, the identity

`U (a ⌢ c) = ± (r a) ⌢ (T c)`  for all `a`, `c`,

with `r`, `T`, `U` the restriction and the two Mayer–Vietoris connecting maps, mapping into the
*model* pair `(PairXT, PairAT) = (S³×D⁴, S³×S³)`.  It is the statement of a colleague's
`Work.Cohomology.Crux.vk_transgression_cap_weak` (`Crux/vk_transgression_cap_weak.lean:66`, whose
own proof is the one `sorry` there); I restate it here so that the proof can be assembled in my own
files from the pieces I have built, without touching a colleague's file.

## What is already proved and importable (all sorry-free)

* **§31 below** — `transgression_cruxδ`: the chain-level identity `transgression_capUvCanon`
  (in `Endgame/shiftCap.lean`) rewritten with `dshShort_cruxShort_delta`
  (in `Endgame/dshDelta.lean`) so that the connecting map appears as `cruxδ X A U V (4 + m)`.
  This is the first connection of the assembly.
* `exists_capTopCanon_relCapHalf` (`Endgame/capCompare.lean`, §16–§19) — `capTopCanon`'s chain map
  is the abstract relative cap product of `(X,A)` along the quasi-isomorphism `relMV_quasiIso`.
* `exists_capUvCanon_relCapHalf` and `ovl X A U V α` (`Endgame/overlapCap.lean`, §24–§25) — the same
  for the overlap, along the quasi-isomorphism `relMVUV_quasiIso` (§21) and the iso
  `smallInLift U V (U ∩ V)`; `ovl` is the image of `α` under the pullback `relComplexMap` of the
  inclusion of pairs, so `r` is the induced map on cohomology.
* `ovlT`, `ovlU` (`Endgame/transgressionIso.lean`, §26) — the two connecting maps as isomorphisms
  (`ovlT` = conjugate of `cruxδ` by the two quasi-isomorphisms, `ovlU` = conjugate of the
  small-chains connecting map), together with `ovlT_eq`/`ovlU_eq`.
* Input B: the overlap pair is the model pair up to an isomorphism preserving the cap product
  (`Work.Cohomology.Crux.overlapPairModel`), so the right-hand side can be moved to
  `(PairXT, PairAT)`.  **Caveat (measured, §31): that module does not currently compile** — it dies
  with heartbeat timeouts at `Crux/overlapPairModel.lean:290,308,310,321` and an "unknown constant
  `ovlRelComplexMap_isIso`" at 336, so it must *not* be imported yet (the `.olean` artifacts the
  referees saw are stale).

## How the proof will go (for whoever continues)

Choose representatives: `α` with `relClassOf α = a` (`exists_relClassOf`), `c'` with
`(homologyMap φtop 8) c' = c` and a preimage of the `c`-class under the `dsh` reindexing — using
*`Function.Surjective` of the isomorphisms*, never `asIso.inv` applied to an element (NOTES §27).
Then apply `transgression_cruxδ` at `c'` and rewrite the two sides with the two cap comparisons and
`relCapPair_apply`/`relCapPairZ_iCycles`; `r`, `T`, `U` are the induced maps of `ovl`,
`ovlT`, `ovlU` (their `Surjective`/`Injective` consequences come from `IsIso`), and the transport to
the model is `Crux.overlapPairModel`.  The only geometric input left is `ρ ≠ 0`
(`Endgame/vk_ovlRestr_ne_zero`, NOTES §28).
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Simplicial

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

namespace Work.Cohomology

noncomputable section

variable {X : TopCat}

/-- **The transgression identity in the `cruxδ` form** (the first connection of the assembly):
`transgression_capUvCanon` with the reindexed connecting map replaced by `cruxδ X A U V (4 + m)`
via `dshShort_cruxShort_delta`. -/
theorem transgression_cruxδ (A U V : Set X) (α : relKern ℤ X A 4)
    (hα : relDiffLM ℤ X A 4 α = 0) (m : ℕ) (hm : 1 ≤ m) :
    CategoryTheory.CategoryStruct.comp
        (dshHomologyIso_mulFour (relMVTopC X A U V) (m + 1) (by omega)).hom
        (CategoryTheory.CategoryStruct.comp (cruxδ X A U V (4 + m))
          (dshHomologyIso_mulFour (relMVUV X A U V) m hm).inv)
      ≫ HomologicalComplex.homologyMap (capUvChain A U V α hα) m
    = HomologicalComplex.homologyMap (capTopChain A U V α hα) (m + 1)
      ≫ (mvSmall_shortExact U V).δ (m + 1) m (by simp only [ComplexShape.down_Rel]) := by
  rw [← dshShort_cruxShort_delta X A U V m hm]
  exact transgression_capUvCanon A U V α hα m

/-- **WIP — the weak Mayer–Vietoris transgression identity for `(Vk(-2), Mk(-2))`.**

This is the statement of the colleague's `Work.Cohomology.Crux.vk_transgression_cap_weak`
(`Crux/vk_transgression_cap_weak.lean:66`), restated here so that it can be proved in my own files
from the pieces above.  **It is not proved yet** (the `sorry` is deliberate and this file is *not*
claimed); the first connection of its proof, `transgression_cruxδ`, is proved above, and the plan
is in the module docstring. -/
theorem vk_transgression_cap_weak :
    ∃ (r : (Work.Cohomology.relCohomology ℤ Work.Cohomology.vkPairX Work.Cohomology.vkPairA 4)
            →ₗ[ℤ]
            (Work.Cohomology.relCohomology ℤ Work.Cohomology.PairXT Work.Cohomology.PairAT 4))
      (T : (Work.Cohomology.relChains Work.Cohomology.vkPairX Work.Cohomology.vkPairA).homology 8
            →ₗ[ℤ]
            (Work.Cohomology.relChains Work.Cohomology.PairXT Work.Cohomology.PairAT).homology 7)
      (U : (Work.Cohomology.singularChains ℤ Work.Cohomology.vkPairX).homology 4
            →ₗ[ℤ] (Work.Cohomology.singularChains ℤ Work.Cohomology.PairXT).homology 3),
      Function.Surjective r ∧ Function.Surjective T ∧ Function.Injective U ∧
      ∀ (a : Work.Cohomology.relCohomology ℤ Work.Cohomology.vkPairX Work.Cohomology.vkPairA 4)
        (c : (Work.Cohomology.relChains Work.Cohomology.vkPairX Work.Cohomology.vkPairA).homology 8),
        U (Work.Cohomology.relCapPair Work.Cohomology.vkPairX Work.Cohomology.vkPairA 4 4 a c)
            = Work.Cohomology.relCapPair Work.Cohomology.PairXT Work.Cohomology.PairAT 4 3 (r a) (T c) ∨
        U (Work.Cohomology.relCapPair Work.Cohomology.vkPairX Work.Cohomology.vkPairA 4 4 a c)
            = - Work.Cohomology.relCapPair Work.Cohomology.PairXT Work.Cohomology.PairAT 4 3 (r a) (T c) := by
  sorry

end

end Work.Cohomology
