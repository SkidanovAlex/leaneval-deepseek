/-
# `ELAssembly` — the inputs of the two certified pull-backs `pbQ`, `pbD`

`Work.ELNest.NestData` asks for the pull-backs of the two nests as `Set.BijOn` statements
(`pbQ`, `pbD`): the level-`(n+1)` region is mapped bijectively onto the level-`n` region by
`F c = (Tantibar c)^[10]` (resp. `f_c^6 = (Tantibar c)^[6]`).

Proving those directly in the `Work.EL` vocabulary (the design of
`NOTES_LEAD_mandelbar_gaps2.md` §3a) replaces simple connectivity, which the workspace does not
have, by the covering-plus-one-fibre criterion
`Work.ELAssembly.bijOn_of_isCoveringMapOn_of_fibre`.  The inputs it needs are exactly the fields
of the two structures below:

* `hcv` — the critical values of the iterate avoid the *base* region (`k = 1 … 10`, resp.
  `1 … 6`).  This is the same `c`-side (wake/certificate) residual as `ChainInputs.hcv`
  (`Work.ELAssembly.chainInputs_of`); class **C**.
* `arc` — the angle map `Work.EL.T^[10]` (resp. `T^[6]`) carries the *(open) near arcs* of the
  level-`(n+1)` polygon into the near arcs of the level-`n` polygon; stated in the pair-list form
  (`¬ InClosedArc`, i.e. "in the near arcs", the boundary points being excluded by the same
  hypothesis).  This is the rational certificate `ELPull.nearArcsCover_Q` / `nearArcsCover_Delta`
  transported to the `Work.EL` vocabulary; **provable** by `InArc_T10_bAngQ` /
  `InArc_T6_armD` (exact rational arithmetic).
* `pair` — the same on the boundary angles: the ray of the image angle is a ray of the target
  polygon (used to show that the image of the boundary curve avoids the target region).
* `one` — at most one preimage angle per fibre: the only angles in the near arcs of the
  level-`(n+1)` polygon whose image is the middle angle `midNear` of the level-`n` polygon agree
  mod `1`.  Again exact rational arithmetic.
-/
import Mathlib
import Submission.Work.ELAssembly.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false

noncomputable section

namespace Work.ELAssembly

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## The `z₁`-nest -/

/-- **The inputs of the pull-back `pbQ` of the `z₁`-nest.**  `P0` is the `α`-pair and `N` the
seven pair sequences; the level-`n` polygon is `[P0, N.Qp n]`. -/
structure QPullInputs (c : ℂ) (d : Work.EL.RootParabolic c) (L : ℝ)
    (P0 : Work.EL.CoPair d.hN) (N : NestPairs d) : Prop where
  /-- the reference level is above `1` (so that both regions are nondegenerate). -/
  hL : 1 < L
  /-- the critical values `(Tantibar c)^[k] 0`, `k = 1 … 10`, avoid every level-`n` region. -/
  hcv : ∀ n : ℕ, ∀ k ∈ Set.Icc 1 10,
    (Tantibar c)^[k] 0 ∉ Work.EL.polyRegion [P0, N.Qp n] (Work.ELNest.Qlev L n)
  /-- the angle map `Work.EL.T^[10]` carries the near arcs of the level-`(n+1)` polygon into
  the near arcs of the level-`n` polygon. -/
  arc : ∀ n : ℕ, ∀ x : ℝ,
    (∀ P ∈ [P0, N.Qp (n + 1)], ¬ Work.EL.InClosedArc x P.a P.b) →
    ∀ P ∈ [P0, N.Qp n], ¬ Work.EL.InClosedArc (Work.EL.T^[10] x) P.a P.b
  /-- the boundary angles of the level-`(n+1)` polygon map to boundary angles of the level-`n`
  polygon. -/
  pair : ∀ n : ℕ, ∀ P' ∈ [P0, N.Qp (n + 1)], ∃ P ∈ [P0, N.Qp n],
    Work.EL.paramRay d.hN (Work.EL.T^[10] P'.a) = Work.EL.paramRay d.hN P.a ∨
    Work.EL.paramRay d.hN (Work.EL.T^[10] P'.a) = Work.EL.paramRay d.hN P.b
  /-- at most one angle in the near arcs of the level-`(n+1)` polygon is carried, mod `1`, to
  the middle angle of the level-`n` polygon. -/
  one : ∀ n : ℕ, ∀ x y : ℝ,
    (∀ P ∈ [P0, N.Qp (n + 1)], ¬ Work.EL.InClosedArc x P.a P.b) →
    (∀ P ∈ [P0, N.Qp (n + 1)], ¬ Work.EL.InClosedArc y P.a P.b) →
    (∃ k : ℤ, (Work.EL.T^[10]) x = Work.EL.midNear [P0, N.Qp n] + k) →
    (∃ k : ℤ, (Work.EL.T^[10]) y = Work.EL.midNear [P0, N.Qp n] + k) →
    ∃ k : ℤ, x = y + k

/-! ## The `b₂`-nest -/

/-- **The inputs of the pull-back `pbD` of the `b₂`-nest.**  The level-`n` polygon is the
three-pair list `[N.Za n, N.Zb n, N.Zc n]`. -/
structure DPullInputs (c : ℂ) (d : Work.EL.RootParabolic c) (L : ℝ) (N : NestPairs d) : Prop where
  /-- the reference level is above `1` (so that both regions are nondegenerate). -/
  hL : 1 < L
  /-- the critical values `(Tantibar c)^[k] 0`, `k = 1 … 6`, avoid every level-`n` region. -/
  hcv : ∀ n : ℕ, ∀ k ∈ Set.Icc 1 6,
    (Tantibar c)^[k] 0 ∉
      Work.EL.polyRegion [N.Za n, N.Zb n, N.Zc n] (Work.ELNest.Dlev L n)
  /-- the angle map `Work.EL.T^[6]` carries the near arcs of the level-`(n+1)` polygon into the
  near arcs of the level-`n` polygon. -/
  arc : ∀ n : ℕ, ∀ x : ℝ,
    (∀ P ∈ [N.Za (n + 1), N.Zb (n + 1), N.Zc (n + 1)], ¬ Work.EL.InClosedArc x P.a P.b) →
    ∀ P ∈ [N.Za n, N.Zb n, N.Zc n], ¬ Work.EL.InClosedArc (Work.EL.T^[6] x) P.a P.b
  /-- the boundary angles of the level-`(n+1)` polygon map to boundary angles of the level-`n`
  polygon. -/
  pair : ∀ n : ℕ, ∀ P' ∈ [N.Za (n + 1), N.Zb (n + 1), N.Zc (n + 1)],
    ∃ P ∈ [N.Za n, N.Zb n, N.Zc n],
      Work.EL.paramRay d.hN (Work.EL.T^[6] P'.a) = Work.EL.paramRay d.hN P.a ∨
      Work.EL.paramRay d.hN (Work.EL.T^[6] P'.a) = Work.EL.paramRay d.hN P.b
  /-- at most one angle in the near arcs of the level-`(n+1)` polygon is carried, mod `1`, to the
  middle angle of the level-`n` polygon. -/
  one : ∀ n : ℕ, ∀ x y : ℝ,
    (∀ P ∈ [N.Za (n + 1), N.Zb (n + 1), N.Zc (n + 1)], ¬ Work.EL.InClosedArc x P.a P.b) →
    (∀ P ∈ [N.Za (n + 1), N.Zb (n + 1), N.Zc (n + 1)], ¬ Work.EL.InClosedArc y P.a P.b) →
    (∃ k : ℤ, (Work.EL.T^[6]) x = Work.EL.midNear [N.Za n, N.Zb n, N.Zc n] + k) →
    (∃ k : ℤ, (Work.EL.T^[6]) y = Work.EL.midNear [N.Za n, N.Zb n, N.Zc n] + k) →
    ∃ k : ℤ, x = y + k

end Work.ELAssembly
