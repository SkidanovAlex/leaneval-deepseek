/-
# `Work.FTS.EllSol.EllPkgAux.uopSlotLe4` — the `U/sin 2θ`-slot at level `4` over `EllClassOk 7`

The target is the `U`-component of the level-`4` package `EllPkgGo` on the linear class
`Work.FTS.EllSol.ClassC` and the level-`7` solution class `Work.FTS.EllExist.EllClassOk`:

```
∃ C > 0, ∀ α g Ψ, 0 < α → α ≤ 1/4 → ClassC α g → EllClassOk 7 α g Ψ →
  HQo α 4 (Uop α (PhiTil α g Ψ) / sin 2θ) ∧
  HkNorm α 4 (Uop α (PhiTil α g Ψ) / sin 2θ) ≤ C · HkNorm α 4 g
```

The whole estimate is assembled in `Submission/Work/FTS/EllSol/EllPkgAux/uopSlotCore.lean`
(the lemma `uopSlot_core`, with the right-hand side still in the *wall* form
`α²‖z²∂²_zX‖₄ + ‖∂²_θX‖₄ + ‖g‖₄`, `X = ellShift α g Ψ`); this module performs the final
elliptic closure

  `α²‖z²∂²_zX‖₄ + ‖∂²_θX‖₄ + ‖g‖₄ ≤ (Ce·Cos + 1)·‖g‖₄`

from the hypothesis `EllEstUnif 4` (applied to the descended weak class
`EllWeakPos α 4 (orthSource g) X`, which `EllClassOk 7` provides via
`ClassC.ellWeakPos_descend` and `TT.HkMem_descend_open`) and the source comparison
`orthSourceHkNormClassC` (`‖orthSource g‖₄ ≤ C‖g‖₄`).

The traces of `X`, the wall `PkgK5.wall_of_interp 4` (fed by `interpFamOfTrace_exists` from the
trace-class interpolation hypothesis `hI`), `PkgK5.divSinK5`, `PkgK5.uopDzIter2Bound`,
`thetaPoincareOpenTrace`, `HkNorm_Dz_le_open`, `Gbar_Hk_le_open`, `Fstar_Hk_le_open` and
`PkgK5.radialHkNorm_le_sinMul` are all consumed inside `uopSlot_core`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllSol.EllPkgAux.Slots
import Submission.Work.FTS.EllSol.EllPkgAux.TraceStmt
import Submission.Work.FTS.EllSol.EllPkgAux.interpFamOfTrace
import Submission.Work.FTS.EllSol.EllPkgAux.uopSlotCore
import Submission.Work.FTS.EllSol.EllPkgAux.orthSourceHkNormClassC
import Submission.Work.FTS.EllSol.PkgK5.wall_of_interp
import Submission.Work.FTS.EllipticEst.TT.HkMem_descend_open
import Submission.Work.FTS.ClassC.removingL12_classC_aux
import Submission.Work.FTS.EllExist.ClassCInputs
import Submission.Work.FTS.EllExist.LevelK
import Submission.Work.FTS.EllipticEst.Fstar_Hk_le_open
import Submission.Work.FTS.EllipticEst.Cert.HkMem_Fstar_sin
import Submission.Work.FTS.EllipticEst.HkNorm_add_le
import Submission.Work.FTS.EllipticEst.HkNorm_const_mul
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.FTS.LocData.HkMem_const_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

-- The U/sin 2θ-slot at level 4 over EllClassOk 7, from the level-4 elliptic estimate and the
-- trace-class interpolation.  Route: the wall `Work.FTS.EllSol.PkgK5.wall_of_interp 4` applied to
-- the straightened unknown `EllSol.ellShift α g Ψ` (via `interpFamOfTrace_exists`), the layer
-- transfer `α‖D_z∂_θΞ‖ ≤ C(α‖D_z∂_θ(ellShift)‖ + ‖g‖)`, `divSinK5`, `thetaPoincareOpenTrace`,
-- `HkNorm_Dz_le_open` and `EllEstUnif 4` (with `orthSource_HkNorm_le`-type bounds).
theorem uopSlotLe4
    (hEst : ∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllEstUnif 4 C)
    (hI : ∃ C : ℝ, 0 < C ∧ Work.FTS.EllSol.EllPkgAux.InterpOpenTraceStmt C) :
    ∃ C : ℝ, 0 < C ∧ Work.FTS.EllSol.EllPkgAux.UopSlotLe4 C := by
  obtain ⟨Ce, hCepos, hEst'⟩ := hEst
  obtain ⟨K, hKpos, hcore⟩ := uopSlot_core
    (Work.FTS.EllSol.PkgK5.wall_of_interp 4 (by norm_num)
      (Work.FTS.EllSol.EllPkgAux.interpFamOfTrace_exists hI 4))
  obtain ⟨Cos, hCosp, hos⟩ := Work.FTS.EllSol.EllPkgAux.orthSourceHkNormClassC 4 (by norm_num)
  refine ⟨K * (Ce * Cos + 1), by positivity, ?_⟩
  intro α g Ψ hα hα4 hC hOk
  obtain ⟨hQ, hcore'⟩ := hcore α g Ψ hα hα4 hC hOk
  refine ⟨hQ, ?_⟩
  have hα1 : α ≤ 1 := by linarith
  -- the descended weak class of the straightened unknown, and the elliptic closure
  have hweak7 : Work.FTS.EllipticEst.TT.EllWeakPos α 7 (Work.Elliptic.orthSource g)
      (Work.FTS.EllSol.ellShift α g Ψ) := by
    have hshift : Work.FTS.EllExist.shiftSing α g Ψ = Work.FTS.EllSol.ellShift α g Ψ := rfl
    rw [← hshift]
    exact hOk.2.2
  have hOsSm : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.orthSource g) :=
    Work.FTS.EllExist.smoothOpen_orthSource_of_Fstar_smooth hC.reg hC.fsm
  have hXsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.EllSol.ellShift α g Ψ) :=
    Work.FTS.EllipticEst.smoothOpen_of_forall (by
      intro n
      have h := hweak7.smooth n
      simpa only [Work.FTS.EllipticEst.Q0] using h)
  have hweak : Work.FTS.EllipticEst.TT.EllWeakPos α 4 (Work.Elliptic.orthSource g)
      (Work.FTS.EllSol.ellShift α g Ψ) :=
    Work.FTS.ClassC.ellWeakPos_descend (α := α) (k := 4) (l := 7)
      (F := Work.Elliptic.orthSource g) (Ψ := Work.FTS.EllSol.ellShift α g Ψ)
      (by norm_num) hOsSm hXsm hweak7
  have hgnn : (0 : ℝ) ≤ Work.Spaces.HkNorm α 4 g := Work.Spaces.HkNorm_nonneg α 4 g
  have hle : α ^ 2 * Work.Spaces.HkNorm α 4
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.FTS.EllSol.ellShift α g Ψ) z θ)
        + Work.Spaces.HkNorm α 4 (Work.Spaces.pthIter 2 (Work.FTS.EllSol.ellShift α g Ψ))
        + Work.Spaces.HkNorm α 4 g
      ≤ (Ce * Cos + 1) * Work.Spaces.HkNorm α 4 g := by
    have h1 := hEst' α (Work.Elliptic.orthSource g) (Work.FTS.EllSol.ellShift α g Ψ)
      hα hα4 hweak
    have h2 := hos α g hα hα1 hC
    have h3 : Ce * Work.Spaces.HkNorm α 4 (Work.Elliptic.orthSource g)
        ≤ Ce * (Cos * Work.Spaces.HkNorm α 4 g) :=
      mul_le_mul_of_nonneg_left h2 hCepos.le
    nlinarith [h1, h3, hgnn, mul_nonneg hCepos.le hCosp.le]
  calc Work.Spaces.HkNorm α 4 (fun z θ =>
        Work.Construction.Uop α (Work.Construction.PhiTil α g Ψ) z θ / Work.Construction.s2 θ)
      ≤ K * (α ^ 2 * Work.Spaces.HkNorm α 4
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.FTS.EllSol.ellShift α g Ψ) z θ)
          + Work.Spaces.HkNorm α 4 (Work.Spaces.pthIter 2 (Work.FTS.EllSol.ellShift α g Ψ))
          + Work.Spaces.HkNorm α 4 g) := hcore'
    _ ≤ K * ((Ce * Cos + 1) * Work.Spaces.HkNorm α 4 g) :=
        mul_le_mul_of_nonneg_left hle hKpos.le
    _ = K * (Ce * Cos + 1) * Work.Spaces.HkNorm α 4 g := by ring

end Work.FTS.EllSol.EllPkgAux
