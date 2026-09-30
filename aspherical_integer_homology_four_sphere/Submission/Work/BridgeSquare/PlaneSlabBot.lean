/-
# `BridgeSquare/PlaneSlabBot.lean` — the *bottom* face of the sheared slab

The bottom (`t = 0`) face of the slab `Φ(y₀,y₁,t) = mbarPtC v (cuspY v (y₀,y₁) - t • cuspHm v)` is
the section `Fn v`, and the coarse two-triangle chain of the fundamental square maps to `singT v`:

  `slabChain v 2 (single botV0 1 - single botV1 1) = singT v`.

Here `botV0 = [(0,0,0), (1,0,0), (1,1,0)]` and `botV1 = [(0,0,0), (0,1,0), (1,1,0)]` are the two
standard triangles of the unit square in the slab coordinates; their `slabL`-images are the vertex
families `[0, λ₂, λ₂+λ₃]` and `[0, λ₃, λ₂+λ₃]` of the chart chains.

To keep this file importable from `planeIdentT.lean`, the chart presentation of `singT`
(`singT_eq_cChain.lean`) is re-derived here from `Fn_apply` and `ChartAlgA` rather than imported
(the original file imports `planeIdentT` itself).
-/
import Mathlib
import Submission.Work.BridgeSquare.PlaneSlab
import Submission.Work.BridgeSquare.Fn_apply

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped Topology Simplicial
open Convexity

namespace Work.BridgeSquare

noncomputable section

/-! ## §1  `singT v` on the two triangles of the `Δ`-model of `T²` -/

/-- `Fn v` on the characteristic map of the triangle `T₀ = (w₀,w₁,w₂) ↦ (w₁+w₂, w₂)`. -/
private theorem Fn_chiT0' (v : Fin 5) (w : StdSimplex ℝ (Fin 3)) :
    Work.BridgeSquare.Fn (rt := Work.RTOwed.rtData) v (Work.PieceHomology.chiT0 w)
      = Work.RTOwed.mbarPtC v (Work.Cusp.cuspX v 0 !₂[w.weights 1 + w.weights 2, w.weights 2]) := by
  rw [← Work.BridgeSquare.Fn_apply v (!₂[w.weights 1 + w.weights 2, w.weights 2])]
  congr 1
  change (Work.PieceHomology.chiT0 w : Fin 2 → AddCircle (1 : ℝ))
    = fun i => (((!₂[w.weights 1 + w.weights 2, w.weights 2]).ofLp i : ℝ) : AddCircle (1 : ℝ))
  funext i
  fin_cases i <;> rfl

/-- `Fn v` on the characteristic map of the triangle `T₁ = (w₀,w₁,w₂) ↦ (w₂, w₁+w₂)`. -/
private theorem Fn_chiT1' (v : Fin 5) (w : StdSimplex ℝ (Fin 3)) :
    Work.BridgeSquare.Fn (rt := Work.RTOwed.rtData) v (Work.PieceHomology.chiT1 w)
      = Work.RTOwed.mbarPtC v (Work.Cusp.cuspX v 0 !₂[w.weights 2, w.weights 1 + w.weights 2]) := by
  rw [← Work.BridgeSquare.Fn_apply v (!₂[w.weights 2, w.weights 1 + w.weights 2])]
  congr 1
  change (Work.PieceHomology.chiT1 w : Fin 2 → AddCircle (1 : ℝ))
    = fun i => (((!₂[w.weights 2, w.weights 1 + w.weights 2]).ofLp i : ℝ) : AddCircle (1 : ℝ))
  funext i
  fin_cases i <;> rfl

/-- The affine point of the vertex family `[0, λ₂, λ₂+λ₃]` at the barycentric weights `z` is the
cusp coordinate `cuspX v 0 (z₁+z₂, z₂)`. -/
private lemma cPt_lam2' (v : Fin 5) (z : StdSimplex ℝ (Fin 3)) :
    Work.BridgeSquare.cPt ![0, Work.Cusp.lam2 v, Work.Cusp.lam2 v + Work.Cusp.lam3 v] z
      = Work.Cusp.cuspX v 0 !₂[z.weights 1 + z.weights 2, z.weights 2] := by
  rw [Work.BridgeSquare.cPt_eq_sum, Fin.sum_univ_three, Work.Cusp.cuspX, Work.Cusp.cuspY]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, zero_smul, smul_zero, smul_add, add_smul]
  abel

/-- The affine point of the vertex family `[0, λ₃, λ₂+λ₃]` at the barycentric weights `z` is the
cusp coordinate `cuspX v 0 (z₂, z₁+z₂)`. -/
private lemma cPt_lam3' (v : Fin 5) (z : StdSimplex ℝ (Fin 3)) :
    Work.BridgeSquare.cPt ![0, Work.Cusp.lam3 v, Work.Cusp.lam2 v + Work.Cusp.lam3 v] z
      = Work.Cusp.cuspX v 0 !₂[z.weights 2, z.weights 1 + z.weights 2] := by
  rw [Work.BridgeSquare.cPt_eq_sum, Fin.sum_univ_three, Work.Cusp.cuspX, Work.Cusp.cuspY]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, zero_smul, smul_zero, smul_add, add_smul]
  abel

/-- **`singT v` is the difference of the two chart `2`-chains** of the vertex families
`[0, λ₂, λ₂+λ₃]` and `[0, λ₃, λ₂+λ₃]`. -/
theorem singT_eq_cChainB (v : Fin 5) :
    Work.BridgeSquare.singT v
      = Work.BridgeSquare.cChain v ![0, Work.Cusp.lam2 v, Work.Cusp.lam2 v + Work.Cusp.lam3 v]
        - Work.BridgeSquare.cChain v ![0, Work.Cusp.lam3 v, Work.Cusp.lam2 v + Work.Cusp.lam3 v] := by
  have h0 : (fun w : StdSimplex ℝ (Fin 3) =>
        Work.BridgeSquare.Fn (rt := Work.RTOwed.rtData) v (Work.PieceHomology.chiT0 w))
      = fun w => Work.RTOwed.mbarPtC v
          (Work.Cusp.cuspX v 0 !₂[w.weights 1 + w.weights 2, w.weights 2]) :=
    funext fun w => Fn_chiT0' v w
  have h1 : (fun w : StdSimplex ℝ (Fin 3) =>
        Work.BridgeSquare.Fn (rt := Work.RTOwed.rtData) v (Work.PieceHomology.chiT1 w))
      = fun w => Work.RTOwed.mbarPtC v
          (Work.Cusp.cuspX v 0 !₂[w.weights 2, w.weights 1 + w.weights 2]) :=
    funext fun w => Fn_chiT1' v w
  have hD0 : ((Work.BridgeSquare.singCxFun.map
        (Work.BridgeSquare.Fn (rt := Work.RTOwed.rtData) v)).f 2)
        (Work.BridgeSquare.singGen (Work.PieceHomology.chiT0))
      = Work.BridgeSquare.singGen (⟨fun w => Work.BridgeSquare.Fn (rt := Work.RTOwed.rtData) v
            (Work.PieceHomology.chiT0 w), _⟩ :
          C(StdSimplex ℝ (Fin 3), Work.BridgeSquare.Mop)) :=
    Work.BridgeSquare.singGen_natural _ _
  have hD1 : ((Work.BridgeSquare.singCxFun.map
        (Work.BridgeSquare.Fn (rt := Work.RTOwed.rtData) v)).f 2)
        (Work.BridgeSquare.singGen (Work.PieceHomology.chiT1))
      = Work.BridgeSquare.singGen (⟨fun w => Work.BridgeSquare.Fn (rt := Work.RTOwed.rtData) v
            (Work.PieceHomology.chiT1 w), _⟩ :
          C(StdSimplex ℝ (Fin 3), Work.BridgeSquare.Mop)) :=
    Work.BridgeSquare.singGen_natural _ _
  unfold Work.BridgeSquare.singT
  rw [show Work.BridgeSquare.chiChain 2 (Work.PieceHomology.torus2Tri 0)
        = Work.BridgeSquare.singGen (Work.PieceHomology.chiT0) from rfl,
      show Work.BridgeSquare.chiChain 2 (Work.PieceHomology.torus2Tri 1)
        = Work.BridgeSquare.singGen (Work.PieceHomology.chiT1) from rfl]
  rw [hD0, hD1]
  congr 1
  · rw [Work.BridgeSquare.cChain]
    congr 1
    refine ContinuousMap.ext fun z => ?_
    simp only [ContinuousMap.coe_mk]
    rw [congrFun h0 z]
    exact congrArg (fun x => Work.RTOwed.mbarPtC v x) (cPt_lam2' v z).symm
  · rw [Work.BridgeSquare.cChain]
    congr 1
    refine ContinuousMap.ext fun z => ?_
    simp only [ContinuousMap.coe_mk]
    rw [congrFun h1 z]
    exact congrArg (fun x => Work.RTOwed.mbarPtC v x) (cPt_lam3' v z).symm

/-! ## §2  The bottom triangles of the slab -/

/-- The first corner of the unit square in the slab coordinates. -/
def botV00 : CuspE3 := slabPt 0 0 0
/-- The second corner of the unit square in the slab coordinates. -/
def botV10 : CuspE3 := slabPt 1 0 0
/-- The third corner of the unit square in the slab coordinates. -/
def botV01 : CuspE3 := slabPt 0 1 0
/-- The fourth corner of the unit square in the slab coordinates. -/
def botV11 : CuspE3 := slabPt 1 1 0

/-- The first coarse triangle of the fundamental square. -/
def botV0 : Fin 3 → CuspE3 := ![botV00, botV10, botV11]

/-- The second coarse triangle of the fundamental square. -/
def botV1 : Fin 3 → CuspE3 := ![botV00, botV01, botV11]

/-- **The coarse two-triangle chain of the fundamental square** (the bottom face of the slab). -/
def slabBot : AffC 2 := Finsupp.single botV0 1 - Finsupp.single botV1 1

theorem slabV_botV0 (v : Fin 5) : slabV v botV0 = ![0, Work.Cusp.lam2 v, Work.Cusp.lam2 v + Work.Cusp.lam3 v] := by
  funext i
  fin_cases i <;>
    simp [slabV, botV0, botV00, botV10, botV11, slabL, slabPt]

theorem slabV_botV1 (v : Fin 5) : slabV v botV1 = ![0, Work.Cusp.lam3 v, Work.Cusp.lam2 v + Work.Cusp.lam3 v] := by
  funext i
  fin_cases i <;>
    simp [slabV, botV1, botV00, botV01, botV11, slabL, slabPt]

/-- **The bottom face of the slab is the section cycle `singT v`.** -/
theorem slabChain_bot (v : Fin 5) : slabChain v 2 slabBot = Work.BridgeSquare.singT v := by
  rw [slabBot, map_sub, slabChain_single_one, slabChain_single_one, slabV_botV0, slabV_botV1,
    ← singT_eq_cChainB]

/-! ## §3  The target, modulo the slab sandwich -/

/-- **`planeIdentT` follows from the slab sandwich `slabWall_exists`.**  This is the last step of the
assembly: coning the sandwich `2`-cycle over any point of the slab space. -/
theorem planeIdentT_of_slabWall_exists
    (h : ∀ v : Fin 5, ∃ (s : ℤ) (c : AffC 2),
      (s = 1 ∨ s = -1) ∧ dLC 1 c = 0 ∧
      slabChain v 2 c = Work.BridgeSquare.singT v
        - s • ((Work.BridgeSquare.PsiM.f 2) (Work.BridgeSquare.planeCycleVec v 0)))
    (v : Fin 5) :
    ∃ (s : ℤ) (y : ↑((Work.BridgeSquare.singCxFun.obj
        (TopCat.of Work.FoldInst.Mbar)).X 3)),
      (s = 1 ∨ s = -1) ∧
      ((Work.BridgeSquare.singCxFun.obj (TopCat.of Work.FoldInst.Mbar)).d 3 2) y
        = Work.BridgeSquare.singT v
          - s • (Work.BridgeSquare.PsiM.f 2) (Work.BridgeSquare.planeCycleVec v 0) := by
  obtain ⟨s, c, hs, hc, himg⟩ := h v
  exact exists_of_slabCycle v s hs c (slabPt 0 0 0) hc himg


end

end Work.BridgeSquare
