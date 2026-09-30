import Mathlib
import Submission.Work.BridgeSquare.CellChiADefs
import Submission.Work.BridgeSquare.ChartAlgA
import Submission.Work.BridgeSquare.PsiM_truncCell_mem_range
import Submission.Work.BridgeSquare.eChi0_chart
import Submission.Work.BridgeSquare.eChi1_chart_v2
import Submission.Work.BridgeSquare.PsiM_edgeCell_expand

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

open Work.MbarHomology

namespace Work.BridgeSquare

noncomputable section

/-- The constant sign of the `A`-case, in the form in which the tables prove it. -/
def sA (v : Fin 5) : ℤ := if (v : ℕ) = 0 ∨ (v : ℕ) = 2 then 1 else -1

theorem sA_spec : ∀ v : Fin 5, sA v = 1 ∨ sA v = -1 := by
  decide

/-- The coefficient of the identity: `eBeta` on the genuine edges and `0` on the dummy ones. -/
def betaA (v : Fin 5) : Fin 4 → ℤ :=
  fun k => if (k : ℕ) < fibreLen v 0 then eBeta v k else 0

/-- The lower characteristic half of the unit edge is the chart `1`-chain of
`[cuspCorner v k, cuspMid v k]`. -/
theorem eChi0_eq_cChain (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 0) :
    eChi0 v k hk = cChain (v := v) ![cuspCorner v k, cuspMid v k] :=
  congrArg singGen (eChi0_chart v k hk)

/-- The upper characteristic half of the unit edge is the chart `1`-chain of
`[cuspCorner1 v k, cuspMid v k]`. -/
theorem eChi1_eq_cChain (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 0) :
    eChi1 v k hk = cChain (v := v) ![cuspCorner1 v k, cuspMid v k] :=
  congrArg singGen (eChi1_chart_v2 v k hk)

/-- **The assembly of `cellChiA` from the three per-cell lemmas.** -/
theorem cellChiA_of (v : Fin 5)
    (hexp : ∀ (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 0),
      (PsiM.f 1) (Pi.single (edgeCell v 0 k) (1 : ℤ))
        = - eBeta v k • eChi0 v k hk
          - (qInc (eRootI v k) (eU1 v k).idx) • eChi1 v k hk)
    (hchi0 : ∀ (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 0),
      eChi0 v k hk = cChain (v := v) ![cuspCorner v k, cuspMid v k])
    (hchi1 : ∀ (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 0),
      eChi1 v k hk = cChain (v := v) ![cuspCorner1 v k, cuspMid v k]) :
    ∃ (s : ℤ) (β : Fin 4 → ℤ) (Z : Fin 4 → ↑((Work.BridgeSquare.singCxFun.obj
        (TopCat.of Work.FoldInst.Mbar)).X 2)),
      (s = 1 ∨ s = -1) ∧
      (∀ k : Fin 4, β k * Work.BridgeSquare.edgeSign v 0 k
          = if (k : ℕ) < Work.BridgeSquare.fibreLen v 0 then s else 0) ∧
      (∀ (k : Fin 4) (hk : (k : ℕ) < Work.BridgeSquare.fibreLen v 0),
        (Work.BridgeSquare.PsiM.f 1) (Pi.single (Work.BridgeSquare.edgeCell v 0 k) (1 : ℤ))
          = β k • Work.BridgeSquare.cChain (v := v)
                ![Work.BridgeSquare.cuspCorner1 v k, Work.BridgeSquare.cuspMid v k]
            - β k • Work.BridgeSquare.cChain (v := v)
                ![Work.BridgeSquare.cuspCorner v k, Work.BridgeSquare.cuspMid v k]
            + (Work.BridgeSquare.singCxFun.obj (TopCat.of Work.FoldInst.Mbar)).d 2 1 (Z k)) := by
  refine ⟨sA v, betaA v, fun _ => 0, sA_spec v, ?_, ?_⟩
  · -- condition 1: the coefficient times the fibre-loop sign is the constant `sA v`
    intro k
    simp only [betaA]
    by_cases hk : (k : ℕ) < fibreLen v 0
    · rw [if_pos hk, if_pos hk, eBeta_edgeSign v k hk]
      by_cases h : (v : ℕ) = 0 ∨ (v : ℕ) = 2 <;> simp [sA, h]
    · rw [if_neg hk, if_neg hk, zero_mul]
  · -- condition 2: the per-cell identity, with `Z = 0`
    intro k hk
    have hcast : qInc (eRootI v k) (eU1 v k).idx = -eBeta v k := qInc_eU1 v k hk
    rw [hexp v k hk, hchi0 v k hk, hchi1 v k hk, hcast]
    simp only [betaA, if_pos hk, map_zero]
    simp only [neg_zsmul]
    abel

theorem cellChiA (v : Fin 5) :
    ∃ (s : ℤ) (β : Fin 4 → ℤ) (Z : Fin 4 → ↑((Work.BridgeSquare.singCxFun.obj
        (TopCat.of Work.FoldInst.Mbar)).X 2)),
      (s = 1 ∨ s = -1) ∧
      (∀ k : Fin 4, β k * Work.BridgeSquare.edgeSign v 0 k
          = if (k : ℕ) < Work.BridgeSquare.fibreLen v 0 then s else 0) ∧
      (∀ (k : Fin 4) (hk : (k : ℕ) < Work.BridgeSquare.fibreLen v 0),
        (Work.BridgeSquare.PsiM.f 1) (Pi.single (Work.BridgeSquare.edgeCell v 0 k) (1 : ℤ))
          = β k • Work.BridgeSquare.cChain (v := v)
                ![Work.BridgeSquare.cuspCorner1 v k, Work.BridgeSquare.cuspMid v k]
            - β k • Work.BridgeSquare.cChain (v := v)
                ![Work.BridgeSquare.cuspCorner v k, Work.BridgeSquare.cuspMid v k]
            + (Work.BridgeSquare.singCxFun.obj (TopCat.of Work.FoldInst.Mbar)).d 2 1 (Z k)) :=
  cellChiA_of v PsiM_edgeCell_expand eChi0_eq_cChain eChi1_eq_cChain

end

end Work.BridgeSquare
