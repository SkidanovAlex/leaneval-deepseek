import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseKinLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Sector.sectorEnergy_le_ratioB`

The defining property of the per-sector box energy `EΛn`: it is the infimum of the
box-restricted Rayleigh quotients

  `Φ ↦ boxFormB m v g ℓ μ d s εT b Φ / sqNormB m ℓ Φ`

over the states `Φ : BoxState m ℓ` *of that same sector* `m`, so it is a lower
bound for the quotient at any single admissible state, provided the set of
quotients is bounded below.  The hypothesis `hEi` records exactly that boundedness;
it is also what makes `⨅` in `ℝ` a genuine infimum rather than the junk value `0`
of `Real.iInf_of_not_bddBelow`.

This is the elementary "the infimum is a lower bound" step: `ciInf_le` applied to
`EΛn`'s definition `⨅ Φ : BoxState m ℓ, …`.

It is the `boxFormB` counterpart of `Sector/sectorEnergy_le_ratio` (which is
stated for the whole-space `boxForm … 0 ·`): here both numerator and denominator
see only the restriction of `Φ` to the box `abox m ℓ`, so no support condition on
`Φ` is needed — `BoxState` is the relaxed class of smooth, symmetric, nonzero
states.

Note also what this statement does *not* claim (the traps recorded in
`Sector/_refute_boxForm_ge.lean`): it is the *per-sector* bound — `EΛn m` with the
same particle number `m` as the state — not a bound by the free-particle-number
infimum `EΛ = ⨅ m, EΛn m` (which for an attractive kernel is a junk value `0`
because `{EΛn m}` is unbounded below).
-/

namespace Work.BoseKinLoc.Sector

open Submission.BoseGases

set_option autoImplicit false

/-- **The per-sector box energy is a lower bound for every box Rayleigh quotient.**
`EΛn m v g ℓ μ d s εT b = ⨅ Φ, boxFormB m v g ℓ μ d s εT b Φ / sqNormB m ℓ Φ` is
by definition the infimum of the quotients over all states `Φ : BoxState m ℓ`,
hence at most the quotient of any one such state, once the family of quotients is
bounded below. -/
theorem sectorEnergy_le_ratioB {v g : ℝ³ → ℝ} {ℓ μ d s εT b : ℝ} {m : ℕ}
    (hEi : BddBelow (Set.range (fun Φ : Work.BoseKinLoc.BoxState m ℓ =>
      Work.BoseKinLoc.boxFormB m v g ℓ μ d s εT b Φ / Work.BoseKinLoc.sqNormB m ℓ Φ)))
    (Φ : Work.BoseKinLoc.BoxState m ℓ) :
    Work.BoseKinLoc.EΛn m v g ℓ μ d s εT b
      ≤ Work.BoseKinLoc.boxFormB m v g ℓ μ d s εT b Φ / Work.BoseKinLoc.sqNormB m ℓ Φ := by
  rw [Work.BoseKinLoc.EΛn]
  exact ciInf_le hEi Φ

end Work.BoseKinLoc.Sector
