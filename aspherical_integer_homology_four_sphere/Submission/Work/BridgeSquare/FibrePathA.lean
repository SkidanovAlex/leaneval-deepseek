/-
# `BridgeSquare/FibrePathA.lean` — the vocabulary of the `κ_{v,2}` fibre-loop assembly

The `A`-case fibre identity compares the *centre line* of the fibre loop (`singA v`, the image of
the `a`-generator of `H_1(T²)` under the section `Fn v`, cf. `singA_eq_cChain`) with the *corner
line*: the `κ_{v,2}`-loop of the cusp cube structure is a chain of `n = fibreLen v 0` unit cube
edges, each of which is the affine chart segment with vertices

  `cuspCorner v k`  and  `cuspCorner1 v k = cuspCorner v k + axVec v`

(`FibreGeomDataA.lean`; `cuspCorner v k` is the cube corner of `edgeCube v 0 k` shifted by
`-(1/2,1/2,1/2)`, `axVec v` the unit vector in the axis `dirKappa v 1`).  The loop is *closed modulo
the lattice*: going around the cycle increases the axis coordinate by `n`, i.e. by `-λ₂`.

For `v ≤ 3` the two cells have corners `(0,0,0)` and `(0,0,-1)` (axis `2`), and for `v = 4` the four
cells have corners `(0,0,0)`, `(0,1,0)`, `(0,-2,0)`, `(0,-1,0)` (axis `1`); the cyclic order of the
cells (each followed by the next *with* larger axis coordinate) is therefore

  `v ≤ 3`: `1 → 0 → (corner 0 + axVec)`;   `v = 4`: `2 → 3 → 0 → 1 → (corner 1 + axVec)`.

So the corner line is the affine path from `DA v` to `BA v`, where

  `DA v = cuspCorner v 1`, `BA v = cuspCorner1 v 0` for `v ≤ 3`  and
  `DA v = cuspCorner v 2`, `BA v = cuspCorner1 v 1` for `v = 4`,

with `BA v - DA v = -λ₂ = fibreLen v 0 • axVec v`.  The two facts on which the assembly rests are
(`CornerSumA.lean`, `PrismA.lean`):

* `∑_{k<n} [cuspCorner v k, cuspCorner1 v k] = [DA v, BA v] + ∂(2-chain)`
  (the subdivision of the corner line into its unit cube edges, `ChartAlgA.c1_subdiv`);
* `[0, λ₂] + [DA v, BA v] ∈ ∂(2-chains)`
  (the prism translation `cuspH → 0`, `ChartAlgA.c1_prism` + the `Λ_v`-periodicity of `mbarPtC`).

-/
import Mathlib
import Submission.Work.BridgeSquare.FibreGeomDataA
import Submission.Work.BridgeSquare.ChartAlgA

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open Convexity

attribute [local instance] Convexity.ConvexSpace.ofModule

namespace Work.BridgeSquare

noncomputable section

/-- **The starting point of the corner line**: `cuspCorner v k_lo` with `k_lo = 1` for `v ≤ 3` and
`k_lo = 2` for `v = 4`. -/
def DA (v : Fin 5) : cE3 := if (v : ℕ) = 4 then cuspCorner v 2 else cuspCorner v 1

/-- **The end point of the corner line**: `cuspCorner1 v k_hi` with `k_hi = 0` for `v ≤ 3` and
`k_hi = 1` for `v = 4`.  One has `BA v = DA v - lam2V v` (the loop closes modulo `Λ_v`). -/
def BA (v : Fin 5) : cE3 := if (v : ℕ) = 4 then cuspCorner1 v 1 else cuspCorner1 v 0

/-- The `k`-th unit cube edge of the `κ_{v,2}`-loop, as a chart `1`-chain. -/
abbrev EcA (v : Fin 5) (k : Fin 4) : ↥((singCxFun.obj cMtop).X 1) :=
  cChain (v := v) ![cuspCorner v k, cuspCorner1 v k]

/-- The chart `1`-chain `[cuspCorner v k, cuspMid v k]` (the first half of the `k`-th unit edge). -/
abbrev E0A (v : Fin 5) (k : Fin 4) : ↥((singCxFun.obj cMtop).X 1) :=
  cChain (v := v) ![cuspCorner v k, cuspMid v k]

/-- The chart `1`-chain `[cuspCorner1 v k, cuspMid v k]`. -/
abbrev E1A (v : Fin 5) (k : Fin 4) : ↥((singCxFun.obj cMtop).X 1) :=
  cChain (v := v) ![cuspCorner1 v k, cuspMid v k]

/-- The sum of the `fibreLen v 0` unit cube edges of the `κ_{v,2}`-loop, over the positional
indexing `Fin 4` (the dummy indices `k ≥ fibreLen v 0` contribute `0`). -/
def EcSumA (v : Fin 5) : ↥((singCxFun.obj cMtop).X 1) :=
  ∑ k : Fin 4, if (k : ℕ) < fibreLen v 0 then EcA v k else 0

/-- The basis vector of the `k`-th unit edge cell of the fibre loop, as an element of the
cellular chain group `C_1 = ↑(Gen.mbarCx.toChainComplex.X 1)`.

This is `Pi.single (edgeCell v 0 k) 1`, but with the type of `C_1` fixed once and for all: the
`mbarDim`-indexed type of the chain complex is only definitionally equal to `Fin 168 → ℤ`, which
makes the bare `Pi.single` term unusable inside tactics. -/
def evecA (v : Fin 5) (k : Fin 4) : ↥((Work.HomologyIso.Gen.mbarCx.toChainComplex).X 1) :=
  Pi.single (edgeCell v 0 k) (1 : ℤ)

end

end Work.BridgeSquare
