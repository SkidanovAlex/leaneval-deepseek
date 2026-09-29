import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Resample.pb2CostDefs
import Submission.Work.Resample.pbCostArithKit
import Submission.Work.Resample.paCostD
import Submission.Work.Resample.pb2DGroupCm
import Submission.Work.Resample.pb2DXLe
import Submission.Work.Resample.pb2DRestLe

/-! Guidance from the project lead (the requester):

LEAD (endgame: Resample's B half is the LAST open piece of the whole problem — speed matters). This statement is the
MIRROR of the already PROVED `Work.Resample.paCostD` (Submission/Work/Resample/). Start by COPYING that file's proof and
adapting it; do not design anything new. Mirror dictionary (definitions in Submission/Work/Resample/pb2Defs.lean):
PAVec/PAInv/PAMid/PABr/PAIterBrF ↦ PB2Vec/PB2Inv/PB2Mid/PB2Br/PB2IterBrF; the array flows from shape ts (input,
ts.prod entries) to shape ss (output); list iteration is `axisIter ts ss Φ` with Φ j : (Fin t_j → ℤ×ℤ) → (Fin s_j → ℤ×ℤ);
applyAlong arguments per axis j are A = (ss.take j).prod, m = t_j, n = s_j, B = (ts.drop (j+1)).prod; stack 2 holds the
remaining INPUT dims (ts.drop j), stack 3 the remaining OUTPUT dims (ss.drop j), stack 6 (ss.take j).prod, stack 7 s_j;
SliceSpecAtA Kb p α s t prep q Φ P ↦ SliceSpecAt prep q Kb p α s t Φ P (argument order differs; its q cost has the extra
Kb(t+1)(p+1)² term, already in PB2Br); resAop/rA ↦ resBop/rB. Size bounds keep ts.prod (sᵢ < tᵢ, so every intermediate
array has ≤ ts.prod entries: (ss.take j).prod ≤ (ts.take j).prod). NEVER import pbSetupF, pbRoundF, pbIterGo*, pbIterF*
(obsolete route; pbSetupF needs 17 GB). Split into children only where the A-side proof was split.
-/

namespace Work.Resample

open HvdH

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-! ## The `p^2` group of the `B̃` cost arithmetic

`PB2Br` splits into the three groups of `Work.Resample.pb2DBr_eq3`:

* `64 * paDZ Kb p ts j` — the `prep` table of the axis, handled by the *reused* `paDGroupZ`
  (`Work.Resample.paCostD`), since the `prep` term of `PB2Br` is literally `64 * paDZ`;
* `64 * pb2DCm Kb Cm p α ss ts j` — the `applyAlong` passes calling `self`, handled by
  `pb2DGroupCm`;
* `pb2DY Kb p ss ts j = 64 * pb2DX Kb p ss ts j + pb2DRest Kb p ss ts j` — the extra
  `Kb (t_j+1) (p+1)^2` term of the `B`-slice word together with the layout, `isz` and constant
  terms; these are handled here, from the per-axis bounds `pb2DXLe` and `pb2DRestLe`. -/

/-- **The `p^2` group of the cost arithmetic of the `B̃` half.**  The prologue, the epilogue and
everything in the per-axis budgets except the `prep` tables and the `Cm`-carrying passes are
absorbed by the `ts.prod * p^2` term of `resCost` (mirror of `paDGroupA`). -/
theorem pb2DGroupRest {Kb Kc1 Kc2 Kc3 p α : ℕ} {ss ts : List ℕ}
    (h : HvdH.ResParams p α ss ts) {K : ℕ}
    (hreq : 4096 * (Kc1 + Kc3) + Kc2 * (HvdH.D * pb2DCR Kb + 1) ≤ K)
    (hrest : ∀ j : ℕ, j < HvdH.D → pb2DY Kb p ss ts j ≤ pb2DCR Kb * (ts.prod * p ^ 2)) :
    Kc1 * PASetupBr p ss ts
      + Kc2 * ((∑ j ∈ Finset.range HvdH.D, pb2DY Kb p ss ts j) + 1)
      + Kc3 * PAFinalBr p ss ts ≤ K * (ts.prod * p ^ 2) := by
  have hA1 : 1 ≤ ts.prod := (pbcaParamFacts p α ss ts h).1
  have hp1 : 1 ≤ p := by have := h.2.2.1; omega
  have hB1 : 1 ≤ ts.prod * p ^ 2 := by
    calc (1 : ℕ) = 1 * 1 := by ring
      _ ≤ ts.prod * p ^ 2 := Nat.mul_le_mul hA1 (by nlinarith)
  have hSR : (∑ j ∈ Finset.range HvdH.D, pb2DY Kb p ss ts j)
      ≤ HvdH.D * (pb2DCR Kb * (ts.prod * p ^ 2)) := by
    calc (∑ j ∈ Finset.range HvdH.D, pb2DY Kb p ss ts j)
        ≤ ∑ _j ∈ Finset.range HvdH.D, (pb2DCR Kb * (ts.prod * p ^ 2)) :=
          Finset.sum_le_sum (fun j hj => hrest j (Finset.mem_range.mp hj))
      _ = HvdH.D * (pb2DCR Kb * (ts.prod * p ^ 2)) := by
          rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have h1 : Kc1 * PASetupBr p ss ts + Kc3 * PAFinalBr p ss ts
      ≤ (4096 * (Kc1 + Kc3)) * (ts.prod * p ^ 2) := by
    have hsetup := paDSetupBr (p := p) (α := α) (ss := ss) (ts := ts) h
    have ha : Kc1 * PASetupBr p ss ts ≤ Kc1 * (4096 * (ts.prod * p ^ 2)) :=
      le_trans (Nat.mul_le_mul_left _ (Nat.le_add_right _ _)) (Nat.mul_le_mul_left _ hsetup)
    have hb : Kc3 * PAFinalBr p ss ts ≤ Kc3 * (4096 * (ts.prod * p ^ 2)) :=
      le_trans (Nat.mul_le_mul_left _ (Nat.le_add_left _ _)) (Nat.mul_le_mul_left _ hsetup)
    calc Kc1 * PASetupBr p ss ts + Kc3 * PAFinalBr p ss ts
        ≤ Kc1 * (4096 * (ts.prod * p ^ 2)) + Kc3 * (4096 * (ts.prod * p ^ 2)) :=
          add_le_add ha hb
      _ = (4096 * (Kc1 + Kc3)) * (ts.prod * p ^ 2) := by ring
  have h2 : Kc2 * ((∑ j ∈ Finset.range HvdH.D, pb2DY Kb p ss ts j) + 1)
      ≤ (Kc2 * (HvdH.D * pb2DCR Kb + 1)) * (ts.prod * p ^ 2) := by
    have hSR1 : (∑ j ∈ Finset.range HvdH.D, pb2DY Kb p ss ts j) + 1
        ≤ (HvdH.D * pb2DCR Kb + 1) * (ts.prod * p ^ 2) := by
      have h0 := hSR
      calc (∑ j ∈ Finset.range HvdH.D, pb2DY Kb p ss ts j) + 1
          ≤ HvdH.D * (pb2DCR Kb * (ts.prod * p ^ 2)) + (ts.prod * p ^ 2) := by omega
        _ = (HvdH.D * pb2DCR Kb + 1) * (ts.prod * p ^ 2) := by ring
    calc Kc2 * ((∑ j ∈ Finset.range HvdH.D, pb2DY Kb p ss ts j) + 1)
        ≤ Kc2 * ((HvdH.D * pb2DCR Kb + 1) * (ts.prod * p ^ 2)) := Nat.mul_le_mul_left _ hSR1
      _ = (Kc2 * (HvdH.D * pb2DCR Kb + 1)) * (ts.prod * p ^ 2) := by ring
  calc Kc1 * PASetupBr p ss ts
        + Kc2 * ((∑ j ∈ Finset.range HvdH.D, pb2DY Kb p ss ts j) + 1)
        + Kc3 * PAFinalBr p ss ts
      = (Kc1 * PASetupBr p ss ts + Kc3 * PAFinalBr p ss ts)
        + Kc2 * ((∑ j ∈ Finset.range HvdH.D, pb2DY Kb p ss ts j) + 1) := by ring
    _ ≤ (4096 * (Kc1 + Kc3)) * (ts.prod * p ^ 2)
        + (Kc2 * (HvdH.D * pb2DCR Kb + 1)) * (ts.prod * p ^ 2) := add_le_add h1 h2
    _ = (4096 * (Kc1 + Kc3) + Kc2 * (HvdH.D * pb2DCR Kb + 1)) * (ts.prod * p ^ 2) := by ring
    _ ≤ K * (ts.prod * p ^ 2) := Nat.mul_le_mul_right _ hreq

/-- Mirror of paCostD for the B half: the three budgets fit into resCost. -/
theorem pb2CostD (Kb Kc1 Kc2 Kc3 : ℕ) :
    ∃ K : ℕ, Kc1 ≤ K ∧ Kc2 ≤ K ∧ Kc3 ≤ K ∧ Kb ≤ K ∧
      ∀ (Cm : ℕ → ℕ) (p α : ℕ) (ss ts : List ℕ),
      HvdH.ResParams p α ss ts → Monotone Cm →
      Kc1 * Work.Resample.PASetupBr p ss ts + Kc2 * Work.Resample.PB2IterBrF Kb Cm p α ss ts +
        Kc3 * Work.Resample.PAFinalBr p ss ts ≤ HvdH.resCost K Cm p α ts := by
  obtain ⟨hKc1, hKc2, hKc3, hKKb, hKz, hKcm, hKA⟩ := pb2DK_facts Kb Kc1 Kc2 Kc3
  refine ⟨pb2DK Kb Kc1 Kc2 Kc3, hKc1, hKc2, hKc3, hKKb, ?_⟩
  intro Cm p α ss ts hRes hmon
  have hSplit : (∑ j ∈ Finset.range HvdH.D, PB2Br Kb Cm p α ss ts j)
      = 64 * (∑ j ∈ Finset.range HvdH.D, paDZ Kb p ts j)
        + 64 * (∑ j ∈ Finset.range HvdH.D, pb2DCm Kb Cm p α ss ts j)
        + (∑ j ∈ Finset.range HvdH.D, pb2DY Kb p ss ts j) := by
    rw [Finset.sum_congr rfl (fun j _ => pb2DBr_eq3 Kb Cm p α ss ts j)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hIter : PB2IterBrF Kb Cm p α ss ts
      = 64 * (∑ j ∈ Finset.range HvdH.D, paDZ Kb p ts j)
        + 64 * (∑ j ∈ Finset.range HvdH.D, pb2DCm Kb Cm p α ss ts j)
        + (∑ j ∈ Finset.range HvdH.D, pb2DY Kb p ss ts j) + 1 := by
    unfold PB2IterBrF
    rw [hSplit]
  have hZ := paDGroupZ (Kb := Kb) (Kc2 := Kc2) hRes hKKb hKz
  have hGCm := pb2DGroupCm hRes Cm hmon hKKb hKcm
  have hRest := pb2DGroupRest (Kb := Kb) (Kc1 := Kc1) (Kc2 := Kc2) (Kc3 := Kc3)
    (K := pb2DK Kb Kc1 Kc2 Kc3) hRes hKA (fun j hj =>
      calc pb2DY Kb p ss ts j
          = 64 * pb2DX Kb p ss ts j + pb2DRest Kb p ss ts j := rfl
        _ ≤ 1024 * Kb * (ts.prod * p ^ 2)
            + (2 ^ 24 * HvdH.D ^ 3 * (HvdH.D + 5)) * (ts.prod * p ^ 2) :=
            add_le_add (pb2DXLe hRes Kb j hj) (pb2DRestLe hRes Kb j hj)
        _ = pb2DCR Kb * (ts.prod * p ^ 2) := by unfold pb2DCR; ring)
  calc Kc1 * PASetupBr p ss ts + Kc2 * PB2IterBrF Kb Cm p α ss ts + Kc3 * PAFinalBr p ss ts
      = (Kc1 * PASetupBr p ss ts
          + Kc2 * ((∑ j ∈ Finset.range HvdH.D, pb2DY Kb p ss ts j) + 1)
          + Kc3 * PAFinalBr p ss ts)
        + Kc2 * (64 * (∑ j ∈ Finset.range HvdH.D, paDZ Kb p ts j))
        + Kc2 * (64 * (∑ j ∈ Finset.range HvdH.D, pb2DCm Kb Cm p α ss ts j)) := by
        rw [hIter]; ring
    _ ≤ pb2DK Kb Kc1 Kc2 Kc3 * (ts.prod * p ^ 2)
        + pb2DK Kb Kc1 Kc2 Kc3 * ts.sum * (p + 1) ^ (pb2DK Kb Kc1 Kc2 Kc3)
        + pb2DK Kb Kc1 Kc2 Kc3 * ts.prod * (Nat.sqrt p + 1) * α
            * (Cm (pb2DK Kb Kc1 Kc2 Kc3 * p) + p) :=
        add_le_add (add_le_add hRest hZ) hGCm
    _ = HvdH.resCost (pb2DK Kb Kc1 Kc2 Kc3) Cm p α ts := by
        unfold HvdH.resCost
        ring

end Work.Resample
