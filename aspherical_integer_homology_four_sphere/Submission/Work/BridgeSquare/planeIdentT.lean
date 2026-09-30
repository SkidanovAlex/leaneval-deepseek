/-
# `BridgeSquare/planeIdentT.lean` — the degree-`2` fibre identity of the `v`-th cusp torus

**Target** (`Work.BridgeSquare.planeIdentT`, the statement below, unchanged):

  `∃ s ∈ {±1}, ∃ y ∈ C_3(M̄), ∂y = singT v - s • Ψ_M(planeCycleVec v 0)`.

## What the statement says, and why it is true

`singT v = Sing(Fn v)(χ_{T₀} - χ_{T₁})` is the image of the fundamental `2`-cycle of the
`Δ`-model of `T²_v` under the section `Fn v = secT v ≫ secMap0 ≫ cuspMap`
(`CuspSection.lean`).  `planeCycleVec v 0` is the *cellular* `κ_{v,2} ∧ κ_{v,3}` cycle of the
cusp cube structure, which is a boundary of `Gen.mbarCx` (`Gen.planeCycle_bd`), hence
`Ψ_M(planeCycleVec v 0) = ∂(Ψ_M(planeWitVec v 0))` is a boundary
(`PsiM_d_planeWit`).  Because the statement has the sign `s ∈ {±1}` free and the second
term is a boundary, the statement is *equivalent* to

  **`[singT v] = 0` in `H_2(M̄; ℤ)`**,

i.e. to the degree-`2` half of `Work.BridgeSquare.SubtorusNull` (statement **(a)** of
`NOTES_LEAD_aspherical_bridge.md` §2.6): the `κ_{v,2}κ_{v,3}` subtorus of the `v`-th cusp is
null-homologous in `M̄`.

## The geometric proof (design; see `NOTES_SESSION3.md` §3/§6)

Write `z = cuspY v y + cuspH` for the *cube coordinate* of the section
(`Fn_apply`: `Fn v (mk y) = mbarPt v (cuspY v (y) + cuspH)`, `cuspH = (1/2,1/2,1/2)`), and let
`m` be the coordinate axis of the meridian `κ_{v,1}` (the cusps' `κ`'s are axis parallel).  Then

* the section's plane is `z_m = 1/2` (the *middle* of the cube layer) with
  `(z_i,z_j)` ranging over a `2×2` (resp. `4×4`) fundamental square of the fibre lattice;
* `planeCycleVec v 0` is the chain of the *bottom faces* (`u_m = 0`) of the cubes
  (`unit_sq_cell` in `scripts/gen_cusp_loops.py`), i.e. the wall `z_m = 0` (identified with
  `z_m = 1`) over the *unit-square* grid of the cube structure.

The two cycles are homologous through the **sheared slab**

  `Ψ(y,t) := mbarPt v (cuspY v y + cuspH + t • (1,1,1))`,  `y ∈ [0,1]²`, `t ∈ [0,1]`,

which for `t = 0` is the section (hence the plane chain), for `t = 1` is the *wall*
(its fine `1/2`-grid is exactly the cube structure's unit squares), and whose four side faces
cancel because `cuspY v (y + e_i) - cuspY v y = κ_{v,i+1} ∈ Λ_v` and `mbarPt v` is
`Λ_v`-periodic.

Concretely, the proof is assembled from

1. **the affine framework** (below): vertex families `v : Fin (k+1) → E`, their affine simplices
   `affVN v`, the singular chains `singAff G v`, the boundary formula `singAff_d`, the
   face lemma `affVN_faceVN`, and the periodicity lemma `singAff_translate`;
2. **the plane subdivision**: a `3`-chain `W` of the `(y,t)`-box `[0,1]² × [0,1]`, subordinate to
   the sheared cube regions, with `∂(toSing Ψ W) = singT v - (wall chain)` (the `t=0` faces give
   the *fine* plane chain, which differs from `singT v` by the boundary of a further `3`-chain
   obtained by coning the two triangulations of the plane square — `singT v` is the coarse
   two-triangle chain by `singT_eq`);
3. **the wall = the cellular cycle**: at `t = 1` the fine grid's unit squares are the cube
   structure's `2`-cells, and the barycentric subdivision of each such square matches
   `Ψ_M(1_e)` (`PsiM_f_piSingle_eq_sum`): for every vertex of the subdivision the chart value
   `kleinPt a u` of the cube `a` is the polytope position `posR F` of the corresponding face of
   `Q̄` (finite table), and both sides are affine in `w`, so they agree on the whole simplex;
4. **the cellular algebra**: the wall chain is `Ψ_M (planeCycleVec v 0)` up to the explicit
   cellular boundary `Gen.planeCycle_bd`.


## Status of this file (session 3, L854)

Proved here (sorry-free): the affine-chain framework (`faceVN`, `affVN`, `affVN_apply`,
`wts_succAbove`, `wts_zero`, `affVN_faceVN`, `singAff`, `singAff_d`, `transVN`, `affVN_transVN`,
`singAff_transVN`), and the cusp-lattice periodicity of the ceiling map
(`mbarPt_add_kv`, `cuspY_add_zero/one/single`, the latter two via
`Work.RTOwed.cuspCert.mbarPt_latVec` / `kv_latVec` of `cuspCert/lattice_bridge.lean`).

Remaining (the target `planeIdentT` is still open), in the order of the plan above:

1. `singT_eq_aff` (delegated): `singT v` is the two singular `2`-simplices of the plane triangles
   `(0,0),(1,0),(1,1)` and `(0,0),(0,1),(1,1)` under `y ↦ mbarPtC v (cuspX v 0 y)`, i.e. the
   *coarse* plane chain;
2. the *fine* plane chain (the subdivision at the cube walls, in the sheared coordinates), its
   comparison with the coarse one by the cone identity in the plane, and the sheared slab
   `(y,t) ↦ mbarPt v (cuspY v y + cuspH + t • (1,1,1))` with `singAff_d` + `singAff_transVN`
   (`cuspY_add_single` + `mbarPt_add_kv` give the four side cancellations);
3. the wall end (`t = 1`): the fine unit squares are the cube structure's `2`-cells
   (`gen_cusp_loops.py`: `unit_sq_cell`), and the barycentric subdivision of each such square
   matches `Ψ_M(1_e)` (`PsiM_f_piSingle_eq_sum`): per subdivision vertex, the chart value
   `kleinPt a u` of the cube `a` equals the polytope position `posR F` of the corresponding face
   of `Q̄` (a finite table, generated), and both sides are affine in `w`;
4. the cellular algebra (`Gen.planeCycle_bd`, `PsiM_d_planeWit`) to replace the wall chain by
   `Ψ_M(planeCycleVec v 0)`, with the sign `s` fixed by the orientations.

-/
import Mathlib
import Submission.Work.BridgeSquare.FibreData
import Submission.Work.BridgeSquare.subtorusBoundaries_of_fibreIdent
import Submission.Work.BridgeSquare.PsiM_truncCell_mem_range
import Submission.Work.BridgeSquare.Fn_apply
import Submission.Work.RTOwed.cuspCert.lattice_bridge
import Submission.Work.BridgeSquare.PlaneSlabBot
import Submission.Work.BridgeSquare.slabWall_exists

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex Convexity


namespace Work.BridgeSquare

noncomputable section

/-! ## §3  The target statement (unchanged) -/

theorem planeIdentT (v : Fin 5) :
    ∃ (s : ℤ) (y : ↑((Work.BridgeSquare.singCxFun.obj
        (TopCat.of Work.FoldInst.Mbar)).X 3)),
      (s = 1 ∨ s = -1) ∧
      ((Work.BridgeSquare.singCxFun.obj (TopCat.of Work.FoldInst.Mbar)).d 3 2) y
        = Work.BridgeSquare.singT v
          - s • (Work.BridgeSquare.PsiM.f 2) (Work.BridgeSquare.planeCycleVec v 0) :=
  Work.BridgeSquare.planeIdentT_of_slabWall_exists
    (fun v => Work.BridgeSquare.slabWall_exists v) v

end

end Work.BridgeSquare
