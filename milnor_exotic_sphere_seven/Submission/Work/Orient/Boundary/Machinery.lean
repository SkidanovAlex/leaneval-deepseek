import Submission.Work.Orient.Boundary
import Submission.Work.Orient.Boundary.HalfVanishing
import Submission.Work.Orient.Boundary.HalfCover

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The half-space port of Hatcher 3.27: what is proved

`Submission/Work/Orient/Boundary/Machinery.lean` records, as theorems, the components of the
"missing chapter" `Work.Orient.HalfSpaceHatcher` that are **proved**, so that a consumer can use the
`Prop`-shaped interface of `Submission/Work/Orient/Boundary.lean` without knowing which file proves
which component.

Proved:

* `Work.Orient.halfVanishingProp` — `H_i(W, W∖A) = 0` for `i > n+1` and `A` compact
  (`Submission/Work/Orient/Boundary/HalfVanishing.lean`, which reduces the half-space model to the
  Euclidean one through the fold map `x ↦ |x₀|` and the retraction principle for pairs);
* `Work.Orient.halfCoverProp` — a compact set is covered by finitely many coordinate half-balls
  centred at its points and avoiding a disjoint closed set
  (`Submission/Work/Orient/Boundary/HalfCover.lean`);
* `Work.Orient.halfLocalHomologyProp` — `H_{n+1}(W, W∖{x}) ≅ ℤ` at an interior point and `0` at a
  boundary point (`Submission/Work/Orient/Boundary/localHomology_corner.lean`);
* `Work.Orient.Boundary.halfRestrictIsoProp` — the localisation isomorphism out of a coordinate
  half-ball lying in the interior — and the assembled `Work.Orient.Boundary.halfSpaceHatcher :
  HalfSpaceHatcher n`; both live in `Submission/Work/Orient/Boundary/HalfRestrictIso.lean`, which
  *imports this file* (so a consumer that wants all four should import
  `Submission.Work.Orient.Boundary.HalfRestrictIso`).

So the whole half-space port `Work.Orient.HalfSpaceHatcher` is **proved**.  What remains for item 2
is the *gluing* layer (`Work.Orient.HalfCompactZeroProp`, `Work.Orient.HalfCoverGlueProp`, the
half-space analogue of `Work.Orient.Port.compactZero` / `Port.coverGlue`) and then the assembly of
`Work.Orient.RelativeFundamentalClassExists` (the transfer of the class over a compact core to
`H_{n+1}(W, ∂W)`, for which the workspace's collar input in `Submission/Work/Surgery/` supplies the
homotopy equivalence `∂W ↪ W∖C`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Manifold

namespace Work.Orient

noncomputable section

/-- **Hatcher 3.27(a) for the half-space model** — proved in
`Submission/Work/Orient/Boundary/HalfVanishing.lean`. -/
theorem halfVanishingProp (n : ℕ) : HalfVanishingProp n :=
  fun W _ _ A hA i hi => Boundary.HalfVanishing n W A hA i hi

/-- **The cover by coordinate half-balls** — proved in
`Submission/Work/Orient/Boundary/HalfCover.lean`. -/
theorem halfCoverProp (n : ℕ) : HalfCoverProp n :=
  fun W _ _ A S hA hAS hS => Boundary.HalfCover n W hA hAS hS

/-- The two proved components of the missing chapter (the third, `HalfLocalHomologyProp`, is
`Work.Orient.halfLocalHomologyProp`). -/
theorem halfVanishing_and_halfCover (n : ℕ) : HalfVanishingProp n ∧ HalfCoverProp n :=
  ⟨halfVanishingProp n, halfCoverProp n⟩

end

end Work.Orient
