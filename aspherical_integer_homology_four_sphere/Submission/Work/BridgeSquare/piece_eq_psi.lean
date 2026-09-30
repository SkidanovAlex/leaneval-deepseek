/-
# `BridgeSquare/piece_eq_psi.lean` — the per-piece identity of the `κ_{v,3}` fibre

For every cusp `v` and every unit edge `i` of the `κ_{v,3}`-corner line, the chart chain
`c1 v (Xv v i) (Xv v (i+1))` agrees, up to a boundary, with `± edgeSign · Ψ_M` of the matching
cellular `1`-cell:

* the matching is the *reversal* `τ = Fin.revPerm` of the edge indices (the interior of the `i`-th
  chart edge lies in the cube `edgeCube v 1 (τ i)`);
* the global sign is `cpsi v = (-1)^{v+1}`;
* the boundary correction is the explicit `c2`-chain built out of the corner edge
  `Yv v k 0 → Yv v k 1/2 → Yv v k 1` of the cube.

The geometric input is the identification `Ψ_M(edgeCell v 1 k) = ± edgeSign · (upper - lower)` of
`BridgeSquare/PsiM_edgeCell_eq.lean`; the chart identification `c1 (Xv i)(Xv i+1) = c1 (Yv 1)(Yv 0)`
is `BridgeSquare.pieceDefs.chart_eq_Yv`.  The rest is the `c1`/`c2` calculus of
`BridgeSquare/ChartAlgA.lean`.
-/
import Mathlib
import Submission.Work.BridgeSquare.fibreSteps
import Submission.Work.BridgeSquare.pieceDefs
import Submission.Work.BridgeSquare.PsiM_edgeCell_eq

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option maxHeartbeats 1000000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped Topology Simplicial
open Convexity

namespace Work.BridgeSquare

theorem piece_eq_psi (v : Fin 5) :
    ∃ (τ : Fin (Work.BridgeSquare.fibreLen v 1) ≃ Fin (Work.BridgeSquare.fibreLen v 1)) (s : ℤ),
      (s = 1 ∨ s = -1) ∧
      (∀ i : Fin (Work.BridgeSquare.fibreLen v 1), ∃ Z : (Work.BridgeSquare.singCxFun.obj
          Work.BridgeSquare.cMtop).X 2,
        Work.BridgeSquare.c1 v (Work.BridgeSquare.Xv v (i : ℕ))
            (Work.BridgeSquare.Xv v ((i : ℕ) + 1))
          = s • (Work.BridgeSquare.edgeSign v 1 (Work.BridgeSquare.eIdx v (τ i))) •
              (Work.BridgeSquare.PsiM.f 1)
                (Pi.single (Work.BridgeSquare.edgeCell v 1 (Work.BridgeSquare.eIdx v (τ i)))
                  (1 : ℤ))
            + (Work.BridgeSquare.singCxFun.obj Work.BridgeSquare.cMtop).d 2 1 Z) := by
  refine ⟨Fin.revPerm, cpsi v, cpsi_spec v, fun i => ?_⟩
  set k : Fin 4 := eIdx v (Fin.revPerm i) with hkdef
  have hk : (k : ℕ) < fibreLen v 1 := eIdx_rev_lt v i
  set Z : (singCxFun.obj cMtop).X 2 :=
      c2 v (Yv v k 0) (Yv v k 1) (Yv v k 0)
    + c2 v (Yv v k 0) (Yv v k 0) (Yv v k 0)
    + c2 v (Yv v k 0) (Yv v k (1 / 2)) (Yv v k 1)
    - c2 v (Yv v k 1) (Yv v k (1 / 2)) (Yv v k 1)
    - c2 v (Yv v k 1) (Yv v k 1) (Yv v k 1) with hZdef
  refine ⟨Z, ?_⟩
  have hZ : (singCxFun.obj cMtop).d 2 1 Z
      = c1 v (Yv v k 1) (Yv v k 0)
        - (c1 v (Yv v k 1) (Yv v k (1 / 2)) - c1 v (Yv v k 0) (Yv v k (1 / 2))) := by
    rw [hZdef]
    simp only [map_add, map_sub]
    rw [c2_d, c2_d, c2_d, c2_d, c2_d]
    abel
  rw [hkdef, chart_eq_Yv v i, PsiM_edgeCell_eq v k hk, hZ]
  simp only [smul_smul]
  have hcoef : cpsi v * (edgeSign v 1 k * (edgeSign v 1 k * cpsi v)) = 1 := by
    rcases cpsi_spec v with h | h <;> rcases edgeSign_pm v k hk with h' | h' <;>
      rw [h, h'] <;> norm_num
  rw [hcoef, one_smul]
  abel

end Work.BridgeSquare
