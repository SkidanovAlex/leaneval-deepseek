import Mathlib
import Submission.Work.BridgeSquare.ChartAlgA
import Submission.Work.BridgeSquare.affineChain

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Convexity

namespace Work.BridgeSquare

/-- **Translation invariance of the chart `1`-chain under the cusp lattice.**  If `l` lies in the
cusp lattice `Λ_v`, then translating both endpoints by `l` does not change the chart edge `[a,b]`,
because the ceiling map `mbarPtC v` is `Λ_v`-periodic. -/
theorem c1_add_lattice (v : Fin 5) (a b l : Work.BridgeSquare.cE3)
    (hl : l ∈ Work.Cusp.lattice v) :
    Work.BridgeSquare.c1 v (a + l) (b + l) = Work.BridgeSquare.c1 v a b := by
  have hpt : ∀ z : Convexity.StdSimplex ℝ (Fin 2),
      Work.BridgeSquare.cPt ![a + l, b + l] z = Work.BridgeSquare.cPt ![a, b] z + l := by
    intro z
    rw [Work.BridgeSquare.cPt_eq_sum, Work.BridgeSquare.cPt_eq_sum]
    rw [Fin.sum_univ_two, Fin.sum_univ_two]
    change z.weights 0 • (a + l) + z.weights 1 • (b + l)
      = z.weights 0 • a + z.weights 1 • b + l
    rw [show z.weights 0 • (a + l) + z.weights 1 • (b + l)
        = z.weights 0 • a + z.weights 1 • b + (z.weights 0 + z.weights 1) • l from by
      rw [smul_add, smul_add, add_smul]; abel]
    rw [StdSimplex.total_fin_two z, one_smul]
  have h : Work.BridgeSquare.cSimp v ![a + l, b + l] = Work.BridgeSquare.cSimp v ![a, b] := by
    ext z
    rw [Work.BridgeSquare.cSimp_apply, Work.BridgeSquare.cSimp_apply, hpt z]
    exact Work.RTOwed.mbarPtC_periodic v (by rw [add_sub_cancel_left]; exact hl)
  simp only [Work.BridgeSquare.c1, Work.BridgeSquare.cChain]
  rw [h]

theorem prism_c1 (v : Fin 5) :
    Work.BridgeSquare.c1 v 0 (Work.Cusp.lam3 v)
      = Work.BridgeSquare.c1 v (-Work.RTOwed.cuspH) (Work.Cusp.lam3 v - Work.RTOwed.cuspH)
        + (Work.BridgeSquare.singCxFun.obj Work.BridgeSquare.cMtop).d 2 1
            (Work.BridgeSquare.c2 v 0 (Work.Cusp.lam3 v - Work.RTOwed.cuspH) (-Work.RTOwed.cuspH)
             + Work.BridgeSquare.c2 v 0 (Work.Cusp.lam3 v) (Work.Cusp.lam3 v - Work.RTOwed.cuspH)
             - Work.BridgeSquare.c2 v (-Work.RTOwed.cuspH) (Work.Cusp.lam3 v - Work.RTOwed.cuspH) (-Work.RTOwed.cuspH)
             - Work.BridgeSquare.c2 v (-Work.RTOwed.cuspH) (-Work.RTOwed.cuspH) (-Work.RTOwed.cuspH)) := by
  have hl : Work.Cusp.lam3 v ∈ Work.Cusp.lattice v := Work.Cusp.kv_mem_lattice v 2
  have hper : Work.BridgeSquare.c1 v (Work.Cusp.lam3 v) (Work.Cusp.lam3 v - Work.RTOwed.cuspH)
      = Work.BridgeSquare.c1 v 0 (-Work.RTOwed.cuspH) := by
    have h := c1_add_lattice v 0 (-Work.RTOwed.cuspH) (Work.Cusp.lam3 v) hl
    rw [zero_add] at h
    rwa [show (-Work.RTOwed.cuspH) + Work.Cusp.lam3 v = Work.Cusp.lam3 v - Work.RTOwed.cuspH by abel] at h
  have hD : (Work.BridgeSquare.singCxFun.obj Work.BridgeSquare.cMtop).d 2 1
        (Work.BridgeSquare.c2 v 0 (Work.Cusp.lam3 v - Work.RTOwed.cuspH) (-Work.RTOwed.cuspH)
         + Work.BridgeSquare.c2 v 0 (Work.Cusp.lam3 v) (Work.Cusp.lam3 v - Work.RTOwed.cuspH)
         - Work.BridgeSquare.c2 v (-Work.RTOwed.cuspH) (Work.Cusp.lam3 v - Work.RTOwed.cuspH) (-Work.RTOwed.cuspH)
         - Work.BridgeSquare.c2 v (-Work.RTOwed.cuspH) (-Work.RTOwed.cuspH) (-Work.RTOwed.cuspH))
      = Work.BridgeSquare.c1 v 0 (Work.Cusp.lam3 v)
        + Work.BridgeSquare.c1 v (Work.Cusp.lam3 v) (Work.Cusp.lam3 v - Work.RTOwed.cuspH)
        - Work.BridgeSquare.c1 v 0 (-Work.RTOwed.cuspH)
        - Work.BridgeSquare.c1 v (-Work.RTOwed.cuspH) (Work.Cusp.lam3 v - Work.RTOwed.cuspH) := by
    rw [map_sub, map_sub, map_add, Work.BridgeSquare.c2_d, Work.BridgeSquare.c2_d,
        Work.BridgeSquare.c2_d, Work.BridgeSquare.c2_d]
    abel
  rw [hD, hper]
  abel

end Work.BridgeSquare
