import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.EllSol.ClassC
import Submission.Work.FTS.EllExist.LevelK
import Submission.Work.FTS.EllSol.EllPkgAux.Slots
import Submission.Work.FTS.EllSol.EllPkgAux.VRSlots
import Submission.Work.FTS.EllSol.EllPkgAux.uopSlotLe4
import Submission.Work.FTS.ClassC.vthQuarter
import Submission.Work.FTS.EllSol.VthAuxC.certC
import Submission.Work.FTS.ClassC.RopGen.interpOpenTrace
import Submission.Work.FTS.ClassC.AlphaDzGen.ProviderBridge
import Submission.Work.FTS.EllSol.ellPkgK6_of_classC

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-
# `Work.FTS.EllSol.ellPkgConj_of_classOk` — the two elliptic packages at one constant

The statement conjoins the level-`4` package `VocabO.EllPkgGo` (the `ℋ⁴`-package consumed by the
transport/coercivity chapter) and the level-`6` package `EllPkgK 6` (consumed by the level-six
persistence rows), at a *single* constant `Ce` and a *single* range `α ≤ α₀`.

## The assembly

* The level-`4` package over `EllClassOk 7` has exactly the content of
  `Work.FTS.EllSol.ellPkgGo_of_classOk`, namely
  `EllPkgAux.ellPkgGoOfClassOk_of` applied to the four level-`4` slots
  (`ropSlotLe4_cl`, `uopSlotLe4`, `vopSlotLe4_cl`, `vthSlotLe4`).
  It is re-assembled here because the workspace carries several *mutually exclusive* copies of
  shared theory (Lean refuses to import two modules declaring the same name, e.g.
  `Work.EllipticEst.Core.i0Aux.rho` or `Work.FTS.EllipticEst.AngAWeak.Yslice`), and the natural
  providers of the level-`4` and level-`6` packages happen to sit on opposite sides of those
  splits.  Every input is therefore taken from the same side as the level-`6` package
  `ellPkgK6_of_classC`:
  - the interpolation input `EllPkgAux.InterpOpenTraceStmt` (consumed by `uopSlotLe4`) is supplied
    through the verbatim bridge `ClassC.AlphaDzGen.openTraceStmt_of_openTrace` applied to
    `ClassC.RopGen.interpOpenTrace` (the `PkgK5.K5c` copy of the same paper-§7 estimate);
  - the `V^{th}` slot is proved here directly from
    `EllSol.ellVth_transferC_of_pieces_quarter` (in `ClassC/vthQuarter`, together with
    `VthAuxC.certC` and `EllSol.poinC_quarter`), *without* the sibling module
    `ClassC.vthTransfer_classC`, which would pull in the other copy of the level-`4` elliptic
    estimate.
* The level-`6` package is `ellPkgK6_of_classC` verbatim.
* Finally `EllClassOk` is monotone in the level (`8 → 7`, needed by the level-`4` slots) and both
  packages are monotone in their constant, so `Ce := max Ce₄ Ce₆` and `α₀ := min α₄ α₆` serve
  both.
-/

namespace Work.FTS.EllSol

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## Monotonicity of the two packages in the constant

Both packages bound each slot norm by `Ce` times a *nonnegative* datum norm, so raising `Ce`
preserves them.  These are the only two structural facts the assembly needs. -/

/-- `EllPkgK` is monotone in the constant. -/
theorem EllPkgK_mono {α : ℝ} {k : ℕ} {Ce Ce' : ℝ} {g Φg : Fn}
    (h : EllPkgK α k Ce g Φg) (hle : Ce ≤ Ce') : EllPkgK α k Ce' g Φg := by
  obtain ⟨h1, h2, ⟨hRm, hRb⟩, ⟨hUm, hUb⟩, ⟨hVm, hVb⟩⟩ := h
  have hgnn : 0 ≤ Work.Spaces.HkNorm α k g := Work.Spaces.HkNorm_nonneg α k g
  have hmon : ∀ X : ℝ, X ≤ Ce * Work.Spaces.HkNorm α k g →
      X ≤ Ce' * Work.Spaces.HkNorm α k g :=
    fun X hX => le_trans hX (mul_le_mul_of_nonneg_right hle hgnn)
  exact ⟨h1, h2, ⟨hRm, hmon _ hRb⟩, ⟨hUm, hmon _ hUb⟩, ⟨hVm, hmon _ hVb⟩⟩

/-- `VocabO.EllPkgGo` is monotone in the constant (only `0 < α` is needed, to keep the
`α^{-1/2}`-factor nonnegative). -/
theorem EllPkgGo_mono {α Ce Ce' : ℝ} {g Φg : Fn} (hα : 0 < α)
    (h : Work.FTS.VocabO.EllPkgGo α Ce g Φg) (hle : Ce ≤ Ce') :
    Work.FTS.VocabO.EllPkgGo α Ce' g Φg := by
  obtain ⟨h1, h2, ⟨hRm, hRb⟩, ⟨hUm, hUb⟩, ⟨hVm, hVb⟩, hv, ⟨hTm, hTb⟩⟩ := h
  have hgnn : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hαp : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  refine ⟨h1, h2, ⟨hRm, ?_⟩, ⟨hUm, ?_⟩, ⟨hVm, ?_⟩, hv, ⟨hTm, ?_⟩⟩
  · exact le_trans hRb (mul_le_mul_of_nonneg_right hle hgnn)
  · exact le_trans hUb (mul_le_mul_of_nonneg_right hle hgnn)
  · exact le_trans hVb (mul_le_mul_of_nonneg_right hle hgnn)
  · refine le_trans hTb ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle hαp) hgnn

/-- **`EllClassOk` is monotone in the level** (the instance `l = 7`, `K = 8` of
`PkgK5.EllWeakPos_descend`), stated here to keep the assembly self-contained. -/
theorem ellClassOk_eight_seven {α : ℝ} {g Ψ : Fn}
    (h : Work.FTS.EllExist.EllClassOk 8 α g Ψ) :
    Work.FTS.EllExist.EllClassOk 7 α g Ψ :=
  ⟨h.1, h.2.1,
    Work.FTS.EllSol.PkgK5.EllWeakPos_descend (l := 7) (by norm_num) h.2.2⟩

/-! ## The `V^{th}`-slot, on the side of the level-`6` package -/

/-- **The `V^{th}`-slot at level `4` over `EllClassOk 7`**, proved directly from
`ellVth_transferC_of_pieces_quarter` (`ClassC/vthQuarter`) with the two certificate inputs
`VthAuxC.certC` and `EllSol.poinC_quarter`.

This is the content of `EllPkgAux.vthSlotLe4`, but without the sibling import
`ClassC.vthTransfer_classC` (which pulls in the second copy of the level-`4` elliptic estimate,
incompatible with the level-`6` package of this file). -/
theorem vthSlotLe4_clashFree
    (hEst : ∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllEstUnif 4 C) :
    ∃ C : ℝ, 0 < C ∧ EllPkgAux.VthSlotLe4 C := by
  obtain ⟨Ce, hCe, h⟩ :=
    Work.FTS.EllSol.ellVth_transferC_of_pieces_quarter hEst
      Work.FTS.EllSol.VthAuxC.certC Work.FTS.EllSol.poinC_quarter
  refine ⟨Ce, hCe, ?_⟩
  intro α g Ψ hα hα4 hC hO
  exact h α g Ψ hα hα4 hC (Work.FTS.StrongGlobal.IsBslSol.toPos hO.1) hO.2.1
    (Work.FTS.EllSol.PkgK5.EllWeakPos_descend (K := 7) (l := 4) (by norm_num) hO.2.2)

/-! ## The level-`4` package -/

/-- **`ellPkgGo_of_classOk`, re-assembled on the side of the level-`6` package.**  Same content
as `Work.FTS.EllSol.ellPkgGo_of_classOk`, with the interpolation input taken through the verbatim
bridge `EllPkgAux.InterpOpenTraceStmt ↦ PkgK5.K5c.InterpOpenTrace`. -/
theorem ellPkgGo_of_classOk_clashFree
    (hEst4 : ∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllEstUnif 4 C) :
    ∃ Ce α₀ : ℝ, 0 < Ce ∧ 0 < α₀ ∧
    ∀ (α : ℝ) (g Ψ : Fn), 0 < α → α ≤ α₀ →
      ClassC α g →
      Work.FTS.EllExist.EllClassOk 7 α g Ψ →
      Work.FTS.VocabO.EllPkgGo α Ce g Ψ := by
  have hI : ∃ C : ℝ, 0 < C ∧ Work.FTS.EllSol.EllPkgAux.InterpOpenTraceStmt C :=
    Work.FTS.ClassC.AlphaDzGen.openTraceStmt_of_openTrace
      Work.FTS.ClassC.RopGen.interpOpenTrace
  exact EllPkgAux.ellPkgGoOfClassOk_of
    (EllPkgAux.ropSlotLe4_cl (EllPkgAux.uopSlotLe4 hEst4 hI) (EllPkgAux.vopSlotLe4_cl hEst4))
    (EllPkgAux.uopSlotLe4 hEst4 hI)
    (EllPkgAux.vopSlotLe4_cl hEst4)
    (vthSlotLe4_clashFree hEst4)

/-! ## The conjunction -/

theorem ellPkgConj_of_classOk (hEst4 : ∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllEstUnif 4 C) (hEst6 : ∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllEstUnif 6 C) :
    ∃ Ce α₀ : ℝ, 0 < Ce ∧ 0 < α₀ ∧
    ∀ (α : ℝ) (g Ψ : Work.FTS.Galerkin.Fn), 0 < α → α ≤ α₀ →
      Work.FTS.EllSol.ClassC α g →
      Work.FTS.EllExist.EllClassOk 8 α g Ψ →
      Work.FTS.VocabO.EllPkgGo α Ce g Ψ ∧ Work.FTS.EllSol.EllPkgK α 6 Ce g Ψ := by
  obtain ⟨CeG, αG, hCeG, hαG, hG⟩ := ellPkgGo_of_classOk_clashFree hEst4
  obtain ⟨CeK, αK, hCeK, hαK, hK⟩ := ellPkgK6_of_classC hEst6
  refine ⟨max CeG CeK, min αG αK, lt_max_of_lt_left hCeG, lt_min hαG hαK, ?_⟩
  intro α g Ψ hα hαm hC hOK8
  have hαG' : α ≤ αG := le_trans hαm (min_le_left _ _)
  have hαK' : α ≤ αK := le_trans hαm (min_le_right _ _)
  exact ⟨EllPkgGo_mono hα (hG α g Ψ hα hαG' hC (ellClassOk_eight_seven hOK8))
      (le_max_left _ _),
    EllPkgK_mono (hK α g Ψ hα hαK' hC hOK8) (le_max_right _ _)⟩

end Work.FTS.EllSol
