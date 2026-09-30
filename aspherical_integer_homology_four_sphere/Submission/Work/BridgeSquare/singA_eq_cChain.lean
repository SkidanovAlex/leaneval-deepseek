import Mathlib
import Submission.Work.BridgeSquare.ChartAlgA
import Submission.Work.BridgeSquare.FibreGeomA
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
set_option maxHeartbeats 2000000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped Topology
open Convexity

attribute [local instance] Convexity.ConvexSpace.ofModule

namespace Work.BridgeSquare

noncomputable section

/-!
# `BridgeSquare/singA_eq_cChain.lean` — `singA v` as the chart chain `[0, λ₂]`

The `A`-gem of the ceiling identity: the image in `M̄` of the `Δ`-generator `a` of `H_1(T²)` is the
chart `1`-chain of the affine segment from `0` to `λ₂ = κ_{v,2}`.

This mirrors `fibreSteps.singB_eq_c1` (the `κ_{v,3}` case).  The `a`-loop is the characteristic map
`chiA : Δ¹ → T²`, `z ↦ (z₁, 0)`; applying `Fn v` and using `Fn_apply` (`Fn v y =
mbarPtC v (cuspX v 0 y)`) together with `cuspX v 0 (t,0) = t • λ₂` presents it as the ceiling map of
the line `t ↦ t • λ₂`, which is exactly the chart simplex `cSimp v ![0, λ₂]`.
-/

/-! ## §1  The `a`-loop of the `Δ`-model of `T²` -/

/-- `lam2V v` is the cusp lattice vector `κ_{v,2} = λ₂`. -/
theorem lam2V_eq_lam2 (v : Fin 5) : lam2V v = Work.Cusp.lam2 v := by
  rw [lam2V, Work.Cusp.lam2, Work.Cusp.kv]
  apply PiLp.ext
  intro i
  fin_cases i <;> rfl

/-- `chiChain 1 (torus2Edge 0)` is `singGen` of the characteristic map of the `a`-loop. -/
theorem chiChain_one_torus2Edge_zero :
    chiChain 1 (Work.PieceHomology.torus2Edge 0) = singGen (Work.PieceHomology.chiA) := by
  rw [show chiChain 1 (Work.PieceHomology.torus2Edge 0)
      = singGen (Work.PieceHomology.torus2ChiCls 1
          (Fin.cast (Work.PieceHomology.torus2DeltaCx_card 1).symm
            (Work.PieceHomology.torus2Edge 0))) from rfl]
  congr 1

/-- The value of `chiA`: `chiA w = ![↑(w.weights 1), 0]`. -/
theorem chiA_apply (w : StdSimplex ℝ (Fin 2)) :
    Work.PieceHomology.chiA w
      = ![((w.weights 1 : ℝ) : AddCircle (1 : ℝ)), (0 : AddCircle (1 : ℝ))] := by
  funext i
  fin_cases i <;> rfl

/-- The `a`-loop written in the underlying real pair of `E2`. -/
theorem chiA_apply_eq (w : StdSimplex ℝ (Fin 2)) :
    Work.PieceHomology.chiA w
      = (fun i => (((!₂[w.weights 1, (0 : ℝ)] : Work.Cusp.E2) i : ℝ) : AddCircle (1 : ℝ))) := by
  funext i
  fin_cases i <;> rfl

/-- `cuspX v 0 y = y₁ • λ₂` for `y = (t, 0)`. -/
theorem cuspX_zero_apply_left (v : Fin 5) (t : ℝ) :
    Work.Cusp.cuspX v 0 !₂[t, (0 : ℝ)] = t • Work.Cusp.lam2 v := by
  rw [Work.Cusp.cuspX, Work.Cusp.cuspY, Work.Cusp.lam2, Work.Cusp.kv]
  simp

/-- The `a`-loop of the `T²` `Δ`-model, as a continuous map into the cusp coordinate space. -/
def loopPtA (v : Fin 5) : C(StdSimplex ℝ (Fin 2), Work.Cusp.E3) where
  toFun w := w.weights 1 • Work.Cusp.lam2 v
  continuous_toFun :=
    ((by fun_prop : Continuous fun w : StdSimplex ℝ (Fin 2) => w.weights 1)).smul continuous_const

@[simp] theorem loopPtA_apply (v : Fin 5) (w : StdSimplex ℝ (Fin 2)) :
    loopPtA v w = w.weights 1 • Work.Cusp.lam2 v := rfl

/-- The ceiling map `mbarPtC v`, as a continuous map. -/
def ceilMap (v : Fin 5) : C(Work.Cusp.E3, Work.FoldInst.Mbar) :=
  ⟨Work.RTOwed.mbarPtC v, Work.RTOwed.mbarPtC_continuous v⟩

@[simp] theorem ceilMap_apply (v : Fin 5) (x : Work.Cusp.E3) :
    ceilMap v x = Work.RTOwed.mbarPtC v x := rfl

/-! ## §2  `singA` as a `singGen` -/

/-- **The `a`-loop in cusp coordinates.**  `singA v` is `singGen` of the cusp line `t ↦ t • λ₂`
composed with the ceiling map `mbarPtC v` (the `Δ`-analogue of `fibreSteps.singB_eq_singGen`). -/
theorem singA_eq_singGen (v : Fin 5) :
    singA v = singGen ((ceilMap v).comp (loopPtA v)) := by
  have h1 : singA v = (singCxFun.map (Fn (rt := Work.RTOwed.rtData) v)).f 1
      (chiChain 1 (Work.PieceHomology.torus2Edge 0)) := rfl
  rw [h1, chiChain_one_torus2Edge_zero]
  have hnat : (singCxFun.map (Fn (rt := Work.RTOwed.rtData) v)).f 1
        (singGen (Work.PieceHomology.chiA))
      = singGen (⟨fun w => Fn (rt := Work.RTOwed.rtData) v (Work.PieceHomology.chiA w),
          (TopCat.Hom.hom (Fn (rt := Work.RTOwed.rtData) v)).continuous.comp
            (Work.PieceHomology.chiA).continuous⟩ : C(StdSimplex ℝ (Fin 2), Work.FoldInst.Mbar)) :=
    singGen_natural (Fn (rt := Work.RTOwed.rtData) v) (Work.PieceHomology.chiA)
  refine hnat.trans ?_
  congr 1
  apply ContinuousMap.ext
  intro w
  show Fn (rt := Work.RTOwed.rtData) v (Work.PieceHomology.chiA w) = ceilMap v (loopPtA v w)
  rw [chiA_apply_eq, Work.BridgeSquare.Fn_apply, cuspX_zero_apply_left, ceilMap, loopPtA_apply]
  rfl

/-! ## §3  The target -/

/-- **`singA v` is the chart `1`-chain `[0, λ₂]`.** -/
theorem singA_eq_cChain (v : Fin 5) :
    Work.BridgeSquare.singA v
      = Work.BridgeSquare.cChain (v := v) ![0, Work.BridgeSquare.lam2V v] := by
  rw [singA_eq_singGen]
  show singGen ((ceilMap v).comp (loopPtA v)) = singGen (cSimp v ![0, lam2V v])
  congr 1
  apply ContinuousMap.ext
  intro w
  show ceilMap v (loopPtA v w) = Work.RTOwed.mbarPtC v (cPt ![0, lam2V v] w)
  rw [ceilMap_apply, loopPtA_apply, cPt_eq_sum, Fin.sum_univ_two]
  have h : w.weights 1 • Work.Cusp.lam2 v
      = w.weights 0 • (![0, lam2V v] : Fin 2 → cE3) 0 + w.weights 1 • (![0, lam2V v]) 1 := by
    rw [lam2V_eq_lam2]; simp
  rw [h]

end

end Work.BridgeSquare
