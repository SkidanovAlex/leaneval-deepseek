import Mathlib
import Submission.Work.BridgeSquare.FibrePathA
import Submission.Work.BridgeSquare.ChartAlgA
import Submission.Work.BridgeSquare.FibreGeomDataA

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped Topology
open Convexity

attribute [local instance] Convexity.ConvexSpace.ofModule

namespace Work.BridgeSquare

noncomputable section

/-!
# `BridgeSquare/cornerSumA.lean`

The subdivision of the `κ_{v,2}`-fibre loop into the corner line `[DA v, BA v]` up to a
boundary.  For every cusp `v` the sum `EcSumA v` of the unit cube edges of the loop is the
corner line `[DA v, BA v]` plus the boundary `∂W` of an explicit chart 2-chain `W`.

Two cases are distinguished by the lattice length `fibreLen v 0`:

* `fibreLen v 0 = 2` (`v ≠ 4`): the loop consists of the two unit edges `[cc 0, cc 0 + e]`
  and `[cc 1, cc 1 + e]`, with `cc 1 = cc 0 - e`.  Hence the corner line is `[cc 1, cc 0 + e]`
  and the subdivision is the elementary collinear subdivision `c1_sub`.

* `fibreLen v 0 = 4` (`v = 4`): the four edges run around the corner line `[cc 2, cc 1 + e]`
  in the cyclic order `2 → 3 → 0 → 1`; the subdivision glues the four unit edges with three
  applications of `c1_sub`.
-/

/-- The `v ≠ 4` case of `cornerSumA`: here `fibreLen v 0 = 2`.

The two unit edges `[cc 0, cc 0 + e]`, `[cc 1, cc 1 + e]` of the loop are the two halves of the
corner line `[cc 1, cc 0 + e]`; adding the boundary of the triangle `[cc 1, cc 0, cc 0 + e]`
turns the sum of the halves into their concatenation. -/
theorem cornerSumA_ne_four (v : Fin 5) (hv : (v : ℕ) ≠ 4) :
    ∃ (W : ↥((singCxFun.obj cMtop).X 2)),
      EcSumA v = cChain (v := v) ![DA v, BA v] + (singCxFun.obj cMtop).d 2 1 W := by
  have hlen : fibreLen v 0 = 2 := by
    fin_cases v <;> simp_all [fibreLen, fibreDir, dirKappa, Work.Cusp.latMod]
  refine ⟨c2 v (cuspCorner v 1) (cuspCorner v 0) (cuspCorner1 v 0), ?_⟩
  change EcSumA v = c1 v (DA v) (BA v)
      + (singCxFun.obj cMtop).d 2 1 (c2 v (cuspCorner v 1) (cuspCorner v 0) (cuspCorner1 v 0))
  rw [show DA v = cuspCorner v 1 from by simp [DA, hv],
      show BA v = cuspCorner1 v 0 from by simp [BA, hv]]
  have hsum : EcSumA v = c1 v (cuspCorner v 0) (cuspCorner1 v 0)
      + c1 v (cuspCorner v 1) (cuspCorner1 v 1) := by
    rw [EcSumA, Fin.sum_univ_four]
    rw [hlen]
    norm_num
  have hrel : cuspCorner1 v 1 = cuspCorner v 0 := by
    fin_cases v <;>
      first
      | (exfalso; revert hv; decide)
      | (apply PiLp.ext; intro i; fin_cases i <;>
          simp only [cuspCorner, cuspCorner1, axVec, PiLp.toLp_apply, PiLp.add_apply, Fin.isValue,
            Work.BridgeSquare.dirKappa, Fin.reduceFinMk] <;>
          norm_num [edgeCube, Work.Cusp.cubeCorner])
  rw [hsum, hrel]
  have h := c1_sub v (cuspCorner v 1) (cuspCorner v 0) (cuspCorner1 v 0)
  rw [add_comm (c1 v (cuspCorner v 0) (cuspCorner1 v 0)) (c1 v (cuspCorner v 1) (cuspCorner v 0))]
  exact h

/-- The `v = 4` case of `cornerSumA`: here `fibreLen 4 0 = 4`.

The four unit edges run in the cyclic order `2 → 3 → 0 → 1` along the corner line `[cc 2, cc 1+e]`.
The three vertices `cc 0 + e = cuspCorner1 4 0`, `cuspCorner1 4 2`, `cuspCorner1 4 3` coincide
with the corners `cc 1`, `cc 3`, `cc 0`, so the sum glues in three `c1_sub` steps. -/
theorem cornerSumA_four :
    ∃ (W : ↥((singCxFun.obj cMtop).X 2)),
      EcSumA 4 = cChain (v := 4) ![DA 4, BA 4] + (singCxFun.obj cMtop).d 2 1 W := by
  refine ⟨c2 4 (cuspCorner 4 0) (cuspCorner 4 1) (cuspCorner1 4 1)
        + c2 4 (cuspCorner 4 2) (cuspCorner 4 3) (cuspCorner 4 0)
        + c2 4 (cuspCorner 4 2) (cuspCorner 4 0) (cuspCorner1 4 1), ?_⟩
  change EcSumA 4 = c1 4 (cuspCorner 4 2) (cuspCorner1 4 1)
      + (singCxFun.obj cMtop).d 2 1
        (c2 4 (cuspCorner 4 0) (cuspCorner 4 1) (cuspCorner1 4 1)
          + c2 4 (cuspCorner 4 2) (cuspCorner 4 3) (cuspCorner 4 0)
          + c2 4 (cuspCorner 4 2) (cuspCorner 4 0) (cuspCorner1 4 1))
  have R1 : cuspCorner1 4 0 = cuspCorner 4 1 := by
    apply PiLp.ext; intro i; fin_cases i <;>
      simp only [cuspCorner, cuspCorner1, axVec, PiLp.toLp_apply, PiLp.add_apply, Fin.isValue,
        Work.BridgeSquare.dirKappa, Fin.reduceFinMk] <;>
      norm_num [edgeCube, Work.Cusp.cubeCorner]
  have R2 : cuspCorner1 4 2 = cuspCorner 4 3 := by
    apply PiLp.ext; intro i; fin_cases i <;>
      simp only [cuspCorner, cuspCorner1, axVec, PiLp.toLp_apply, PiLp.add_apply, Fin.isValue,
        Work.BridgeSquare.dirKappa, Fin.reduceFinMk] <;>
      norm_num [edgeCube, Work.Cusp.cubeCorner]
  have R3 : cuspCorner1 4 3 = cuspCorner 4 0 := by
    apply PiLp.ext; intro i; fin_cases i <;>
      simp only [cuspCorner, cuspCorner1, axVec, PiLp.toLp_apply, PiLp.add_apply, Fin.isValue,
        Work.BridgeSquare.dirKappa, Fin.reduceFinMk] <;>
      norm_num [edgeCube, Work.Cusp.cubeCorner]
  have hsum : EcSumA 4 = c1 4 (cuspCorner 4 0) (cuspCorner 4 1)
      + c1 4 (cuspCorner 4 1) (cuspCorner1 4 1)
      + c1 4 (cuspCorner 4 2) (cuspCorner 4 3) + c1 4 (cuspCorner 4 3) (cuspCorner 4 0) := by
    rw [show EcSumA 4 = c1 4 (cuspCorner 4 0) (cuspCorner1 4 0) + c1 4 (cuspCorner 4 1) (cuspCorner1 4 1)
        + c1 4 (cuspCorner 4 2) (cuspCorner1 4 2) + c1 4 (cuspCorner 4 3) (cuspCorner1 4 3) from by
      rw [EcSumA, Fin.sum_univ_four]; norm_num [fibreLen, fibreDir, dirKappa, Work.Cusp.latMod]]
    rw [R1, R2, R3]
  have h1 := c1_sub 4 (cuspCorner 4 0) (cuspCorner 4 1) (cuspCorner1 4 1)
  have h2 := c1_sub 4 (cuspCorner 4 2) (cuspCorner 4 3) (cuspCorner 4 0)
  have h3 := c1_sub 4 (cuspCorner 4 2) (cuspCorner 4 0) (cuspCorner1 4 1)
  rw [hsum]
  calc c1 4 (cuspCorner 4 0) (cuspCorner 4 1) + c1 4 (cuspCorner 4 1) (cuspCorner1 4 1)
        + c1 4 (cuspCorner 4 2) (cuspCorner 4 3) + c1 4 (cuspCorner 4 3) (cuspCorner 4 0)
      = (c1 4 (cuspCorner 4 0) (cuspCorner 4 1) + c1 4 (cuspCorner 4 1) (cuspCorner1 4 1))
        + (c1 4 (cuspCorner 4 2) (cuspCorner 4 3) + c1 4 (cuspCorner 4 3) (cuspCorner 4 0)) := by
        abel
    _ = (c1 4 (cuspCorner 4 0) (cuspCorner1 4 1)
          + (singCxFun.obj cMtop).d 2 1 (c2 4 (cuspCorner 4 0) (cuspCorner 4 1) (cuspCorner1 4 1)))
        + (c1 4 (cuspCorner 4 2) (cuspCorner 4 0)
          + (singCxFun.obj cMtop).d 2 1 (c2 4 (cuspCorner 4 2) (cuspCorner 4 3) (cuspCorner 4 0))) := by
        rw [h1, h2]
    _ = (c1 4 (cuspCorner 4 2) (cuspCorner 4 0) + c1 4 (cuspCorner 4 0) (cuspCorner1 4 1))
        + ((singCxFun.obj cMtop).d 2 1 (c2 4 (cuspCorner 4 0) (cuspCorner 4 1) (cuspCorner1 4 1))
          + (singCxFun.obj cMtop).d 2 1 (c2 4 (cuspCorner 4 2) (cuspCorner 4 3) (cuspCorner 4 0))) := by
        abel
    _ = (c1 4 (cuspCorner 4 2) (cuspCorner1 4 1)
          + (singCxFun.obj cMtop).d 2 1 (c2 4 (cuspCorner 4 2) (cuspCorner 4 0) (cuspCorner1 4 1)))
        + ((singCxFun.obj cMtop).d 2 1 (c2 4 (cuspCorner 4 0) (cuspCorner 4 1) (cuspCorner1 4 1))
          + (singCxFun.obj cMtop).d 2 1 (c2 4 (cuspCorner 4 2) (cuspCorner 4 3) (cuspCorner 4 0))) := by
        rw [h3]
    _ = c1 4 (cuspCorner 4 2) (cuspCorner1 4 1)
        + ((singCxFun.obj cMtop).d 2 1 (c2 4 (cuspCorner 4 0) (cuspCorner 4 1) (cuspCorner1 4 1))
          + (singCxFun.obj cMtop).d 2 1 (c2 4 (cuspCorner 4 2) (cuspCorner 4 3) (cuspCorner 4 0))
          + (singCxFun.obj cMtop).d 2 1 (c2 4 (cuspCorner 4 2) (cuspCorner 4 0) (cuspCorner1 4 1))) := by
        abel
    _ = c1 4 (cuspCorner 4 2) (cuspCorner1 4 1)
        + (singCxFun.obj cMtop).d 2 1 (c2 4 (cuspCorner 4 0) (cuspCorner 4 1) (cuspCorner1 4 1)
          + c2 4 (cuspCorner 4 2) (cuspCorner 4 3) (cuspCorner 4 0)
          + c2 4 (cuspCorner 4 2) (cuspCorner 4 0) (cuspCorner1 4 1)) := by
        rw [map_add, map_add]

/-- **The corner-sum identity for the `κ_{v,2}` fibre loop.**  The sum of the unit cube edges of
the loop is the corner line `[DA v, BA v]` plus the boundary of a chart `2`-chain. -/
theorem cornerSumA (v : Fin 5) :
    ∃ (W : ↑((Work.BridgeSquare.singCxFun.obj (TopCat.of Work.FoldInst.Mbar)).X 2)),
      Work.BridgeSquare.EcSumA v
        = Work.BridgeSquare.cChain (v := v) ![Work.BridgeSquare.DA v, Work.BridgeSquare.BA v]
          + (Work.BridgeSquare.singCxFun.obj (TopCat.of Work.FoldInst.Mbar)).d 2 1 W := by
  fin_cases v
  · exact cornerSumA_ne_four 0 (by decide)
  · exact cornerSumA_ne_four 1 (by decide)
  · exact cornerSumA_ne_four 2 (by decide)
  · exact cornerSumA_ne_four 3 (by decide)
  · exact cornerSumA_four

end

end Work.BridgeSquare
