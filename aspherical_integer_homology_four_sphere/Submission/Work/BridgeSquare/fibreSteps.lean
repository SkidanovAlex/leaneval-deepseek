/-
# `BridgeSquare/fibreSteps.lean` — the chain-level steps of the `κ_{v,3}` fibre identity

All of this is `sorry`-free and can be imported freely (unlike `fibreLoopIdentB.lean`, whose target
theorem is still open).  Contents:

* **Step 1** — `singB v = singGen (mbarPtC v ∘ loopPt v)`: the section loop in cusp coordinates
  (`Fn_apply` + `chiChain`/`singGen` naturality);
* **Step 2, chart form** — `singB_eq_c1 : singB v = c1 v 0 κ_{v,3}`, the prism `prism_c1` (imported
  from `BridgeSquare/prism_c1.lean`, with the explicit chain `prismWit v`), and the subdivision of
  the corner line `cornerC_subdiv_c1` into the `fibreLen v 1` unit cube edges `c1 v (Xv v i) (Xv v (i+1))`;
* **Assembly** — `singB_eq_pieces`: `singB v` differs from the sum of the unit cube edges by a
  boundary.  What remains for the target is the per-cell comparison of `c1 v (Xv v i) (Xv v (i+1))`
  with `± Ψ(1_{edgeCell v 1 k})`.
-/
import Mathlib
import Submission.Work.BridgeSquare.FibreData
import Submission.Work.BridgeSquare.subtorusBoundaries_of_fibreIdent
import Submission.Work.BridgeSquare.PsiM_truncCell_mem_range
import Submission.Work.Cusp.Data
import Submission.Work.FoldInst.Basic
import Submission.Work.RTOwed.cuspDev
import Submission.Work.BridgeSquare.Fn_apply
import Submission.Work.BridgeSquare.affineChain
import Submission.Work.BridgeSquare.ChartAlgA
import Submission.Work.BridgeSquare.prism_c1

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option maxHeartbeats 4000000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped Topology Simplicial
open Convexity

namespace Work.BridgeSquare

noncomputable section


/-! ## Step 1: the `κ_{v,3}`-loop in cusp coordinates -/

/-- The cusp-coordinate parametrisation of the `κ_{v,3}`-loop:
`w ↦ w₁ • κ_{v,3}` (with `κ_{v,3} = lam3 v`). -/
def loopPt (v : Fin 5) : C(StdSimplex ℝ (Fin 2), CuspE3) where
  toFun w := w.weights 1 • Work.Cusp.lam3 v
  continuous_toFun :=
    ((by fun_prop : Continuous fun w : StdSimplex ℝ (Fin 2) => w.weights 1)).smul continuous_const

@[simp] theorem loopPt_apply (v : Fin 5) (w : StdSimplex ℝ (Fin 2)) :
    loopPt v w = w.weights 1 • Work.Cusp.lam3 v := rfl

/-- The ceiling map `mbarPtC v` as a continuous map. -/
def mbarPtCM (v : Fin 5) : C(CuspE3, Work.FoldInst.Mbar) :=
  ⟨Work.RTOwed.mbarPtC v, Work.RTOwed.mbarPtC_continuous v⟩

@[simp] theorem mbarPtCM_apply (v : Fin 5) (x : CuspE3) :
    mbarPtCM v x = Work.RTOwed.mbarPtC v x := rfl

/-- `cuspX v 0 y = y₁ • κ_{v,3}` for `y = (0, t)`. -/
theorem cuspX_zero_apply (v : Fin 5) (t : ℝ) :
    Work.Cusp.cuspX v 0 !₂[0, t] = t • Work.Cusp.lam3 v := by
  simp only [Work.Cusp.cuspX, Work.Cusp.cuspY, zero_smul, zero_add]
  congr 1
  simp

/-- The value of `chiB`: `chiB w = ![(0 : AddCircle 1), ↑(w.weights 1)]`. -/
theorem chiB_apply (w : StdSimplex ℝ (Fin 2)) :
    Work.PieceHomology.chiB w
      = ![(0 : AddCircle (1 : ℝ)), ((w.weights 1 : ℝ) : AddCircle (1 : ℝ))] := by
  funext i
  fin_cases i <;> rfl

/-- `chiChain 1 (torus2Edge 1)` is `singGen` of the characteristic map of the `b`-loop. -/
theorem chiChain_one_torus2Edge_one :
    chiChain 1 (Work.PieceHomology.torus2Edge 1) = singGen (Work.PieceHomology.chiB) := by
  rw [show chiChain 1 (Work.PieceHomology.torus2Edge 1)
      = singGen (Work.PieceHomology.torus2ChiCls 1
          (Fin.cast (Work.PieceHomology.torus2DeltaCx_card 1).symm
            (Work.PieceHomology.torus2Edge 1))) from rfl]
  congr 1

/-- The `b`-loop of the `T²` `Δ`-model, as an element of `E2`. -/
theorem chiB_apply_eq (w : StdSimplex ℝ (Fin 2)) :
    Work.PieceHomology.chiB w
      = (fun i => (((!₂[0, w.weights 1] : Work.Cusp.E2) i : ℝ) : AddCircle (1 : ℝ))) := by
  rw [chiB_apply]
  funext i
  fin_cases i <;> simp

/-- **Step 1 of the fibre identity.**  The singular `1`-chain `singB v` is `singGen` of the cusp
line `t ↦ t • κ_{v,3}` composed with the ceiling map `mbarPtC v`. -/
theorem singB_eq_singGen (v : Fin 5) :
    singB v = singGen ((mbarPtCM v).comp (loopPt v)) := by
  have hnat : (singCxFun.map (Fn (rt := Work.RTOwed.rtData) v)).f 1
        (singGen (Work.PieceHomology.chiB))
      = singGen (⟨fun w => Fn (rt := Work.RTOwed.rtData) v (Work.PieceHomology.chiB w),
          (TopCat.Hom.hom (Fn (rt := Work.RTOwed.rtData) v)).continuous.comp
            (Work.PieceHomology.chiB).continuous⟩ : C(StdSimplex ℝ (Fin 2), Work.FoldInst.Mbar)) :=
    singGen_natural (Fn (rt := Work.RTOwed.rtData) v) (Work.PieceHomology.chiB)
  have hstep : (singCxFun.map (Fn (rt := Work.RTOwed.rtData) v)).f 1
        (singGen (Work.PieceHomology.chiB))
      = singGen ((mbarPtCM v).comp (loopPt v)) := by
    rw [hnat]
    congr 1
    apply ContinuousMap.ext
    intro w
    show Fn (rt := Work.RTOwed.rtData) v (Work.PieceHomology.chiB w) = mbarPtCM v (loopPt v w)
    rw [chiB_apply_eq, Work.BridgeSquare.Fn_apply, cuspX_zero_apply, mbarPtCM_apply, loopPt_apply]
  have h1 : singB v = (singCxFun.map (Fn (rt := Work.RTOwed.rtData) v)).f 1
      (chiChain 1 (Work.PieceHomology.torus2Edge 1)) := rfl
  rw [h1, chiChain_one_torus2Edge_one]
  exact hstep

/-! ## Step 2: the prism between the centre line and the corner line -/

/-! ## Step 2 (chart form): the loop and its corner line as chart chains

Following `Submission/Work/BridgeSquare/ChartAlgA.lean` (a colleague's module), a *chart chain*
`c1 v a b = singGen (cSimp v ![a,b])` is the image in `C_*(M̄)` of the affine segment with chart
vertices `a`, `b`; no pushing by `Sing (mbarPt)` is needed, since the chart simplices are already
singular simplices of `M̄`. -/

/-- **The loop as a chart chain**: `singB v = c1 v 0 (κ_{v,3})`. -/
theorem singB_eq_c1 (v : Fin 5) : singB v = c1 v 0 (Work.Cusp.lam3 v) := by
  rw [singB_eq_singGen]
  congr 1
  apply ContinuousMap.ext
  intro w
  show Work.RTOwed.mbarPtC v (w.weights 1 • Work.Cusp.lam3 v)
      = Work.RTOwed.mbarPtC v (cPt (![0, Work.Cusp.lam3 v] : Fin 2 → CuspE3) w)
  rw [cPt_eq_sum]
  congr 1
  rw [Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, smul_zero, zero_add]

/-- The `i`-th lattice point of the corner line, in chart coordinates. -/
def Xv (v : Fin 5) (i : ℕ) : CuspE3 := (i : ℝ) • unitStep v - Work.RTOwed.cuspH

/-- **The subdivision of the corner line** into its `fibreLen v 1` unit cube edges. -/
theorem cornerC_subdiv_c1 (v : Fin 5) :
    ∃ Z : (singCxFun.obj cMtop).X 2,
      c1 v (-Work.RTOwed.cuspH) (Work.Cusp.lam3 v - Work.RTOwed.cuspH)
        = (∑ i ∈ Finset.range (Work.BridgeSquare.fibreLen v 1), c1 v (Xv v i) (Xv v (i + 1)))
          + (singCxFun.obj cMtop).d 2 1 Z := by
  have h := c1_subdiv v (Xv v) (Work.BridgeSquare.fibreLen v 1)
  have h0 : Xv v 0 = -Work.RTOwed.cuspH := by simp [Xv]
  have hN : Xv v (Work.BridgeSquare.fibreLen v 1)
      = Work.Cusp.lam3 v - Work.RTOwed.cuspH := by
    simp only [Xv, lam3_eq_smul_unitStep]
  have key : (∑ i ∈ Finset.range (Work.BridgeSquare.fibreLen v 1),
        c1 v (Xv v i) (Xv v (i + 1)))
      = c1 v (-Work.RTOwed.cuspH) (Work.Cusp.lam3 v - Work.RTOwed.cuspH)
        + (singCxFun.obj cMtop).d 2 1 (∑ i ∈ Finset.range (Work.BridgeSquare.fibreLen v 1),
            c2 v (-Work.RTOwed.cuspH) (Xv v i) (Xv v (i + 1)))
        - c1 v (-Work.RTOwed.cuspH) (-Work.RTOwed.cuspH) := by
    simpa only [h0, hN] using h
  refine ⟨-(∑ i ∈ Finset.range (Work.BridgeSquare.fibreLen v 1),
      c2 v (-Work.RTOwed.cuspH) (Xv v i) (Xv v (i + 1)))
      + c2 v (-Work.RTOwed.cuspH) (-Work.RTOwed.cuspH) (-Work.RTOwed.cuspH), ?_⟩
  rw [map_add, map_neg, key, c1_deg]
  abel

/-- The explicit prism `2`-chain of `prism_c1`. -/
def prismWit (v : Fin 5) : (singCxFun.obj cMtop).X 2 :=
  c2 v 0 (Work.Cusp.lam3 v - Work.RTOwed.cuspH) (-Work.RTOwed.cuspH)
  + c2 v 0 (Work.Cusp.lam3 v) (Work.Cusp.lam3 v - Work.RTOwed.cuspH)
  - c2 v (-Work.RTOwed.cuspH) (Work.Cusp.lam3 v - Work.RTOwed.cuspH) (-Work.RTOwed.cuspH)
  - c2 v (-Work.RTOwed.cuspH) (-Work.RTOwed.cuspH) (-Work.RTOwed.cuspH)


/-- The `κ_{v,3}`-loop has at most `4` unit cube edges. -/
theorem fibreLen_le_four (v : Fin 5) : Work.BridgeSquare.fibreLen v 1 ≤ 4 := by
  fin_cases v <;> decide

/-- The index of a unit cube edge in the degree-`4` data tables (`edgeCube`, `edgeW0Face`, …). -/
def eIdx (v : Fin 5) (k : Fin (Work.BridgeSquare.fibreLen v 1)) : Fin 4 :=
  Fin.castLE (fibreLen_le_four v) k

/-- **The loop as the sum of its unit cube edges, up to a boundary.**  Assembly of `singB_eq_c1`,
`prism_c1` and `cornerC_subdiv_c1`: the witness is the prism `prismWit v` plus the subdivision
cone of the corner line. -/
theorem singB_eq_pieces (v : Fin 5) :
    ∃ Z : (singCxFun.obj cMtop).X 2,
      singB v = (∑ i ∈ Finset.range (Work.BridgeSquare.fibreLen v 1),
          c1 v (Xv v i) (Xv v (i + 1))) + (singCxFun.obj cMtop).d 2 1 Z := by
  set Z₂ : (singCxFun.obj cMtop).X 2 := Classical.choose (cornerC_subdiv_c1 v) with hZ₂
  have h₂ : c1 v (-Work.RTOwed.cuspH) (Work.Cusp.lam3 v - Work.RTOwed.cuspH)
      = (∑ i ∈ Finset.range (Work.BridgeSquare.fibreLen v 1), c1 v (Xv v i) (Xv v (i + 1)))
        + (singCxFun.obj cMtop).d 2 1 Z₂ := by
    simpa only [hZ₂] using Classical.choose_spec (cornerC_subdiv_c1 v)
  refine ⟨prismWit v + Z₂, ?_⟩
  calc singB v = c1 v 0 (Work.Cusp.lam3 v) := singB_eq_c1 v
    _ = c1 v (-Work.RTOwed.cuspH) (Work.Cusp.lam3 v - Work.RTOwed.cuspH)
          + (singCxFun.obj cMtop).d 2 1 (prismWit v) := prism_c1 v
    _ = ((∑ i ∈ Finset.range (Work.BridgeSquare.fibreLen v 1),
            c1 v (Xv v i) (Xv v (i + 1))) + (singCxFun.obj cMtop).d 2 1 Z₂)
          + (singCxFun.obj cMtop).d 2 1 (prismWit v) := by rw [h₂]
    _ = (∑ i ∈ Finset.range (Work.BridgeSquare.fibreLen v 1),
          c1 v (Xv v i) (Xv v (i + 1)))
          + (singCxFun.obj cMtop).d 2 1 (prismWit v + Z₂) := by
        rw [map_add]; abel

end

end Work.BridgeSquare
