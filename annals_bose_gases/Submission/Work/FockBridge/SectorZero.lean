import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.FockBridge.qLHSwordB_eq_zero_of_forall_notMem
import Submission.Work.FockBridge.tBwordInd_eq_zero_of_forall_notMem
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.FockBridge.SectorZero` — the `k = 0` occupancy sector carries no word

FS's remark after `thm:smallbox` — *"we may of course assume that `n > 0` as the inequality we want
to prove is obviously satisfied if `n = 0` as the operator is 0 whereas the lower bound is negative
in this case"* (l. 3993) — made formal: on the configuration set where **no** particle lies in the
box, both the localised kinetic word `tBwordBInd` and the localised potential word `qLHSwordB`
vanish *identically* (the box projections `P_{B,i}, Q_{B,i}` and the localised kernels
`wSmallPair`, `wSmall1Pair` all carry the box indicator/`χ_B` factor).  So the `k = 0` instance of
the termwise residual `Work.FockBridge.PerSectorBound` is reduced to the single numeric condition
`dlThreshold … 0 ≤ 0`, i.e. to the error budget of `Work.FockBridge.DLRegime`. -/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.FockBridge

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases
open BoseGases
open Work.UBBInputs8
open Classical

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

variable {N : ℕ}

/-- The zero-occupancy sector piece vanishes where some particle lies in the box. -/
theorem sectorPiece_zero_eq_zero_of_exists_mem {B : Set ℝ³} {Φ : X N → ℝ} {x : X N}
    (hx : ∃ i : Fin N, x i ∈ B) : sectorPiece B 0 Φ x = 0 := by
  rw [sectorPiece, Set.indicator_of_notMem]
  intro hmem
  obtain ⟨i, hi⟩ := hx
  have hpos : 0 < boxOccupancy B x :=
    Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  rw [mem_sectorSet_iff] at hmem
  omega

/-- **The `k = 0` localised kinetic word vanishes** (FS l. 3993). -/
theorem tBwordBInd_sectorPiece_zero (N : ℕ) (L d ε c : ℝ) (u : ℝ³) (Φ : X N → ℝ) :
    tBwordBInd N L d ε c u (sectorPiece (dlBox L d u) 0 Φ) = 0 := by
  have h := tBwordInd_eq_zero_of_forall_notMem (A := dlBox L d u)
    (volA := SmallBoxSliding.boxMass L d u) (χ := chiB L d u)
    (a := L) (s := L * d) (ε := ε) (c := c)
    (Ψ := sectorPiece (dlBox L d u) 0 Φ)
    (fun x hx => sectorPiece_zero_eq_zero_of_exists_mem hx)
  simpa [tBwordBInd] using h

/-- **The `k = 0` localised potential word vanishes** (FS l. 3993): the localised kernels
`wSmallPair`, `wSmall1Pair` all carry the `χ_B`-factor. -/
theorem qLHSwordB_sectorPiece_zero {N : ℕ} {v : ℝ³ → ℝ} (h : Work.UBB.ScatSol v) (M : ℕ) (L d μ : ℝ)
    (hL : 0 < L) (hd : 0 < d) (u : ℝ³) (Φ : X N → ℝ) :
    SmallBoxSliding.qLHSwordB h M L d μ u (sectorPiece (dlBox L d u) 0 Φ) = 0 :=
  qLHSwordB_eq_zero_of_forall_notMem (N := N) (v := v) h (M := M) (L := L) (d := d) (μ := μ)
    hL hd (u := u) (Ψ := sectorPiece (dlBox L d u) 0 Φ)
    (fun x hx => sectorPiece_zero_eq_zero_of_exists_mem hx)

/-- **The whole localised per-box word vanishes on the `k = 0` occupancy sector** — FS's `n = 0`
remark (l. 3993).  Consequently the `k = 0` instance of `Work.FockBridge.PerSectorBound` reduces to
the single numeric condition `sectorMass L (dlBox L d u) Φ 0 · dlThreshold c C ρ (a v) (chiMass M L d u) Γ 0 ≤ 0`,
i.e. to the error budget of `Work.FockBridge.DLRegime`. -/
theorem sectorPiece_zero_word_eq_zero {N : ℕ} {v : ℝ³ → ℝ} (h : Work.UBB.ScatSol v) (M : ℕ)
    (L d μ ε c : ℝ) (hL : 0 < L) (hd : 0 < d) (u : ℝ³) (Φ : X N → ℝ) :
    tBwordBInd N L d ε c u (sectorPiece (dlBox L d u) 0 Φ)
      + SmallBoxSliding.qLHSwordB h M L d μ u (sectorPiece (dlBox L d u) 0 Φ) = 0 := by
  rw [tBwordBInd_sectorPiece_zero N L d ε c u Φ,
    qLHSwordB_sectorPiece_zero (N := N) h M L d μ hL hd u Φ, add_zero]

end Work.FockBridge
