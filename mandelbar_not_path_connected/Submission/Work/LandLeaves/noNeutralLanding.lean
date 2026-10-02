/-
Copyright: subproject `Submission/Work/LandLeaves/` of `mandelbar_not_path_connected`.

# Ledger item 5 assembled: the Snail lemma gives `NoNeutralLanding` and `SnailDichotomy`

The chain proved in this area is

```
SnailLemmaMilnor                          -- Milnor, Lemma 16.5 (germ form, delegated)
  → (c ∈ Mandelbar, periodic ray landing) multiplier2 c k z = 1     -- delegated
  → NoNeutralLanding                                                 -- this file
  → SnailDichotomy                                                   -- snailDichotomy_of_noNeutral
```

The `c ∈ Mandelbar` hypothesis of the instantiation is discharged with
`Work.LandLeaves.mem_mandelbar_of_landsAt` (a consequence of ledger item 2, proved in this area),
so the ray-level statement is exactly `Work.LandLeaves.NoNeutralLanding`.
-/
import Submission.Work.LandLeaves.noNeutralLanding_of_snailMilnor
import Submission.Work.LandLeaves.snailDichotomy_of_noNeutral
import Submission.Work.LandLeaves.dynBottcherOnlyOnMandelbar

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **Ledger item 5, the Snail lemma**: Milnor's Lemma 16.5 implies that a dynamic ray does not
land at a neutral non-parabolic periodic point (`Work.LandLeaves.NoNeutralLanding`).

The mandelbar hypothesis of the instantiation `noNeutralLanding_of_snailMilnor` is supplied by
`Work.LandLeaves.mem_mandelbar_of_landsAt` (ledger item 2), so no hypothesis is lost: for
`c ∉ Mandelbar` there is no landing at all. -/
theorem noNeutralLanding_of_snailLemmaMilnor (h : SnailLemmaMilnor) : NoNeutralLanding := by
  intro c θ k z hk hper hland hnorm
  exact noNeutralLanding_of_snailMilnor h c (mem_mandelbar_of_landsAt hland)
    hk hper hland hnorm

/-- **Ledger item 5, concluded**: the Snail lemma (Milnor 16.5) gives
`Work.LANDCL.SnailDichotomy`, i.e. a periodic ray whose landing point is not attracting lands at a
repelling or parabolic point, for **every** period (the even-period clause being exactly
`NoNeutralLanding`). -/
theorem snailDichotomy_of_snailLemmaMilnor (h : SnailLemmaMilnor) :
    Work.LANDCL.SnailDichotomy :=
  snailDichotomy_of_noNeutralLanding (noNeutralLanding_of_snailLemmaMilnor h)

end Work.LandLeaves
