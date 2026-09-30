import Mathlib
import Submission.Work.BridgeSquare.FibrePathA
import Submission.Work.BridgeSquare.ChartAlgA
import Submission.Work.BridgeSquare.FibreGeomDataA
import Submission.Work.BridgeSquare.FibreAsmA
import Submission.Work.BridgeSquare.prism_c1

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxHeartbeats 4000000

namespace Work.BridgeSquare

/-!
# `BridgeSquare/prismA.lean` — the prism translation `[0, κ_{v,2}] + [D_A, B_A] ∈ ∂(2-chains)`

The corner line `[D_A v, B_A v]` is the *translate* of the centre line `[0, λ₂]`
(`λ₂ = κ_{v,2} = lam2V v`) by the base point `B_A v`: indeed the loop closes modulo the cusp lattice,
`D_A v = B_A v + λ₂`, so by `Λ_v`-periodicity of the ceiling map (`c1_add_lattice`) the two
segments `[λ₂, D_A]` and `[0, B_A]` coincide as chart `1`-chains.

The two triangles `[0, λ₂, D_A]` and `[0, D_A, B_A]` then give

  `∂(c₂(0,λ₂,D_A) + c₂(0,D_A,B_A)) = [λ₂,D_A] + [0,λ₂] + [D_A,B_A] - [0,B_A]`

and the periodicity kills the two remaining terms, leaving exactly `[0,λ₂] + [D_A,B_A]` as a
boundary — the statement of the prism translation used by the `A`-case fibre identity.
-/

/-- **The corner line closes modulo the cusp lattice.**  The starting point of the corner line is
the translate of the end point by `λ₂ = κ_{v,2}`: `D_A v = B_A v + lam2V v`. -/
theorem DA_eq_BA_add (v : Fin 5) : DA v = BA v + lam2V v := by
  fin_cases v <;>
  · apply PiLp.ext; intro i; fin_cases i <;>
    simp only [DA, BA, cuspCorner, cuspCorner1, axVec, lam2V, dirKappa, Work.Cusp.kappa,
      edgeCube, Work.Cusp.cubeCorner, PiLp.add_apply, PiLp.toLp_apply,
      Fin.isValue, Fin.reduceFinMk, ↓reduceIte] <;>
    norm_num

theorem prismA (v : Fin 5) :
    ∃ (W : ↑((Work.BridgeSquare.singCxFun.obj (TopCat.of Work.FoldInst.Mbar)).X 2)),
      Work.BridgeSquare.cChain (v := v) ![(0 : Work.Cusp.E3), Work.BridgeSquare.lam2V v]
        + Work.BridgeSquare.cChain (v := v) ![Work.BridgeSquare.DA v, Work.BridgeSquare.BA v]
        = (Work.BridgeSquare.singCxFun.obj (TopCat.of Work.FoldInst.Mbar)).d 2 1 W := by
  have hDA : DA v = BA v + lam2V v := DA_eq_BA_add v
  refine ⟨c2 v 0 (lam2V v) (DA v) + c2 v 0 (DA v) (BA v), ?_⟩
  have hper : c1 v (lam2V v) (DA v) = c1 v 0 (BA v) := by
    have h := c1_add_lattice v 0 (BA v) (lam2V v) (lam2V_mem_lattice v)
    rw [zero_add, ← hDA] at h
    exact h
  rw [map_add, c2_d, c2_d, hper]
  abel

end Work.BridgeSquare
