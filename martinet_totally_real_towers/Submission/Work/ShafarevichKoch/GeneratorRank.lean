import Mathlib
import Submission.Work.ClassFieldTower.ProTwoDefs
import Submission.Work.ClassFieldTower.Objects
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Profinite

/-!
# `Work.ShafarevichKoch.GeneratorRank` -- the generator rank of `G_∅`

This module is the definition layer of **item (1)** of the deliverable of this chapter, the
arithmetic identification

```
d(G_∅) = rank₂ Cl(F),        G_∅ = Gal(F_∅/F),
```

for an imaginary quadratic field `F` (the workspace's benchmark field is
`Kc = ℚ(√-30030)`, where both sides are `5`).

The two objects are

* `QuadraticLevel F M` -- an **unramified quadratic level**, i.e. an intermediate field
  `Kc ⊆ L ⊆ F_∅` with `[L : F] = 2`.  These are Kummer-theoretically the "unramified `Z/2`
  extensions of `F`", and the classical statement of item (1) is that every one of them comes
  from a class of order `2`;
* `ProTwoChar F M` -- the **continuous character group** `H¹(G_∅, 𝔽₂)`, i.e. the continuous
  homomorphisms `G_∅ → 𝔽₂` (written multiplicatively).  By the Burnside basis theorem for
  pro-`2` groups, `#ProTwoChar = 2 ^ d(G_∅)`, so the arithmetic identification is the statement
  `#ProTwoChar = 2 ^ rank₂ Cl(F)`.

The bridge between the two is the fundamental theorem of infinite Galois theory (in Mathlib as
`InfiniteGalois.IntermediateFieldEquivClosedSubgroup` and friends, imported below): continuous
characters correspond to *open* index-`2` subgroups of `G_∅`, which correspond bijectively to
the quadratic levels, with the trivial character corresponding to `F` itself.  Hence

```
#ProTwoChar F M = #(QuadraticLevel F M) + 1.
```

The upper bound `#QuadraticLevel F M ≤ 2 ^ rank₂ Cl(F) - 1` (every unramified quadratic
extension comes from a class of order `2`, with the unit classes excluded) is the Kummer two
descent of `Work.ShafarevichKoch.card_unramifiedQuadraticLevels_le_classGroupTwoRank`; the
matching lower bound comes from the genus level of `Kc`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ShafarevichKoch

open Work.ClassFieldTower

variable {F : Type*} [Field F] [NumberField F]

/-- **A quadratic level of `F_∅/F`**: an unramified quadratic extension of `F` inside the maximal
unramified pro-`2` extension `F_∅ = M.K`, i.e. an intermediate field of `F`-dimension `2`.

By `Work.ClassFieldTower.MaximalUnramifiedProP.unramified`, every such level is unramified over
`F`; by `M.universal` every unramified quadratic extension of `F` occurs as one. -/
abbrev QuadraticLevel (F : Type*) [Field F] [NumberField F]
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} F 2) : Type _ :=
  {L : IntermediateField F M.K // Module.finrank F L = 2}

/-- **The continuous character group of `G_∅` over `𝔽₂`**, the group `H¹(G_∅, 𝔽₂)`:
the continuous group homomorphisms `G_∅ = Gal(F_∅/F) → Multiplicative (ZMod 2)`.

Its cardinality is `2 ^ d(G_∅)` (the `𝔽₂`-dimension of `H¹(G_∅,𝔽₂)` is the minimal number of
topological generators of the pro-`2` group `G_∅`), and by infinite Galois theory its non-trivial
elements correspond bijectively to the quadratic levels of `F_∅/F`. -/
abbrev ProTwoChar (F : Type*) [Field F] [NumberField F]
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} F 2) : Type _ :=
  {χ : Work.ClassFieldTower.galoisGroup M →* Multiplicative (ZMod 2) // Continuous χ}

variable (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} F 2)

/-- A quadratic level has `F`-dimension `2` (definitional). -/
theorem quadraticLevel_finrank (L : QuadraticLevel F M) : Module.finrank F (L : IntermediateField F M.K) = 2 :=
  L.2

/-- The field `F` itself is not a quadratic level. -/
theorem quadraticLevel_ne_bot (L : QuadraticLevel F M) :
    (L : IntermediateField F M.K) ≠ ⊥ := by
  intro h
  have h2 := L.2
  rw [h] at h2
  simp at h2

end Work.ShafarevichKoch
