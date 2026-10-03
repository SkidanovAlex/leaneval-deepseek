/-
# The `g`-side (lin-2) estimate of the mixed range, via the assembled `A7G` low-pass route

This module re-derives the `g`-side factor estimate `Work.KMTAreas.A7.MixedGSideEstimate P p₂`
of the mixed range (Area A7, KMT §8) through the **proved** assembly

  `A7Hi.LinVarG`  ⟸  `A7Hi.lacunaryBumpVarEstimate_assemblyG`  ⟸  `A7Hi.lowpassVarG`

instead of the `A7MixedG` three-dyadic-piece route (`SupPiece` / `ChainPiece` / `SqPiece`).

## Why this route

`A7Hi.LinVarG` is *proved* in the tree, and its single unproved input is `A7Hi.lowpassVarG`
(the `j₂ = 0`, `s₂ = -u` case of `(lin-2)`).  That statement is *character-identical* to the
**proved** `A7G.lowpassVarG` (`Submission/Work/KMTAreas/A7G/lowpassVarG.lean`, complete), which
in turn is the composition `A7G.plainBumpVarG` (proved) ∘ `A7G.lowpassAlphaTransferG` (proved) with
the Ionescu–Wainger transference.  So the `A7Hi.lowpassVarG` stub is pure missing wiring, which
this file supplies under the name `lowpassVarG_lo`.

Consequently the entire `g`-side gap of the mixed range is *not* the JSW maximal/chain/square
theory of the `A7MixedG` chapter, but the two inputs that the `A7G` route leaves open:

* `Work.KMTAreas.A7G.chainPartLowpass` / `Work.KMTAreas.A7HiRep.chainPartSqFun` — the
  Lépingle / Jones–Seeger–Wright step for the low-pass Ionescu–Wainger family;
* `Work.KMTAreas.A7MixedG.fiberLargeResidue` — the paper's §8 fibre/Shannon transfer (used by
  `Work.KMTAreas.A7MixedG.FiberGuard`, which is otherwise proved).

## What is proved here

* `lowpassVarG_lo` — the statement of `A7Hi.lowpassVarG` from `A7G.lowpassVarG`;
* `LinVarG_lo` — the statement of `A7Hi.LinVarG` (the `g`-side linear lacunary variational estimate
  at arbitrary arithmetic height `l₁`, with the loss `lossWeight A ρ l₁ l₂ k₁ k₂`) from
  `lowpassVarG_lo`;
* `LinVarGuard_lo` — its `l₁ = 0` instance `Work.KMTAreas.A7.LinVarGuard`;
* `MixedGSideEstimate_lo` — the target `MixedGSideEstimate P p₂`, by the proved assembly
  `Work.KMTAreas.A7.MixedGSideHolds_of_pieces` applied to `LinVarGuard_lo` and the proved
  `Work.KMTAreas.A7MixedG.FiberGuard`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7MixedG.LinVarGuard
import Submission.Work.KMTAreas.A7MixedG.FiberGuard
import Submission.Work.A7MixedG.FiberLargeResidueHolds
import Submission.Work.KMTAreas.A7.MixedGSideHolds
import Submission.Work.KMTAreas.A7LoPoly.lowpassVarGDirect
import Submission.Work.KMTAreas.A7.FibrePlumbing

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.Analysis.EndVar

/-- **The `g`-side low-pass variational estimate** (`A7Hi.lowpassVarG`).  Proved directly from the
`(1+l₂)²`-loss dyadic core `Work.KMTAreas.A7LoPoly.lpfVarPolyLoss`
(`Work.KMTAreas.A7LoPoly.lowpassVarGDirect`), i.e. **without** passing through the `l`-free stubs
`Work.KMTAreas.A7G.chainPartLowpass` and `Work.KMTAreas.A7Hi2.lacunaryMaxPiece`. -/
theorem lowpassVarG_lo (P : Polynomial ℤ) (hdeg : 2 ≤ P.natDegree) :
    ∀ (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (r : NNReal) (hr : 2 < r)
      (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) (Λ : NNReal) (hΛ : 1 < Λ),
      ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧
        ∀ (k : ℤ) (l₂ : ℕ) (a : ℕ → NNReal) (ha : PointwiseErgodicTheorems.Lacunary Λ a)
          (ha1 : ∀ n, 1 ≤ a n) (f : ℤ → ℂ),
          Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₂ k →
          (∀ n : ℕ, -((P.natDegree : ℤ) *
            Work.Analysis.EndVar.logN (Nat.floor (a n))) ≤ k) →
          MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Work.KMTAreas.A7.Tle ρ l₂
              (Work.KMTAreas.A7.varphitildeN P.natDegree (Nat.floor (a n)) 0) f x))
            p MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (C * (1 + (l₂ : ℝ)) ^ 2) *
              MeasureTheory.eLpNorm f p MeasureTheory.Measure.count :=
  fun ρ hρ hρ1 r hr p hp hptop Λ hΛ =>
    Work.KMTAreas.A7LoPoly.lowpassVarGDirect P hdeg ρ hρ hρ1 r hr p hp hptop Λ hΛ

/-- **The `g`-side linear lacunary variational estimate** (`A7Hi.LinVarG`, with the low-pass input
`lowpassVarG_lo`). -/
theorem LinVarG_lo (P : Polynomial ℤ) (hdeg : 2 ≤ P.natDegree) (C₀ : ℕ) (hC₀ : 1 ≤ C₀)
    (r : NNReal) (hr : 2 < r) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∀ (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤),
      ∃ C : NNReal → NNReal,
        ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (g : ℤ → ℂ),
          1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
          t ∈ Set.Icc (1/2 : ℝ) 1 →
          MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => Work.KMTAreas.A7.Gcl ρ P C₀ a l₁ l₂ k₁ k₂ t g n x)) p
              MeasureTheory.Measure.count
            ≤ (C Λ : ENNReal) * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ k₁ k₂) *
                MeasureTheory.eLpNorm g p MeasureTheory.Measure.count := by
  refine Work.KMTAreas.A7Hi.lacunaryBumpVarEstimate_assemblyG P hdeg ?_ ?_ ?_ C₀ hC₀ r hr
  · -- the low-pass piece (paper (lin-2), `s₂ = -u`, `j₂ = 0`)
    exact lowpassVarG_lo P hdeg
  · -- the clipped low-pass piece, derived from the low-pass piece
    intro ρ hρ hρ1 C₀ Cρc Cρ hCρpos hCρc Λ hΛ r hr p hp hptop C hCpos hLow
    exact Work.KMTAreas.A7Hi.lacunaryBumpLowpassClipBoundG (P.natDegree) (by omega) ρ hρ hρ1 C₀ Cρc Cρ
      hCρpos hCρc Λ hΛ r hr p hp hptop C hCpos hLow
  · -- the poor (non-narrow) scales
    intro ρ hρ hρ1 C₀ hC₀ hρC Cρc hCρc Λ hΛ r hr p hp hptop
    exact Work.KMTAreas.A7Hi.lacunaryBumpBadPartBoundG P P.natDegree hdeg le_rfl ρ hρ hρ1 C₀ hC₀ hρC
      Cρc hCρc Λ hΛ r hr p hp hptop

/-- **The `g`-side (lin-2) estimate of the mixed range** (`Work.KMTAreas.A7.LinVarGuard`), from the
proved `A7G` route. -/
theorem LinVarGuard_lo (P : Polynomial ℤ) (p₂ : ENNReal) (hdeg : 2 ≤ P.natDegree)
    (hp₂ : 1 < p₂) (htp₂ : p₂ < ⊤) : Work.KMTAreas.A7.LinVarGuard P p₂ hdeg hp₂ htp₂ := by
  intro C₀ r hC₀ hr
  obtain ⟨A, hA, ρ₀, hρ₀, hrec⟩ := LinVarG_lo P hdeg C₀ hC₀ r hr
  refine ⟨A, hA, ρ₀, hρ₀, ?_⟩
  intro ρ hρ hρle
  obtain ⟨C, hC⟩ := hrec ρ hρ hρle p₂ hp₂ htp₂
  refine ⟨C, ?_⟩
  intro a Λ l₂ k₁ k₂ t g hΛ ha ha1 hl₂ ht hgb
  have hl₂ne : l₂ ≠ 0 := by omega
  have hfam := Work.KMTAreas.A7MixedG.GmixedFam_eq_Gcl ρ P C₀ a l₂ k₁ k₂ t g hl₂ne
  have hV : Work.KMTAreas.A7.GmixedVar r ρ P C₀ a l₂ k₁ k₂ t g
      = fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7.Gcl ρ P C₀ a 0 l₂ k₁ k₂ t g n x) := by
    funext x
    simp only [Work.KMTAreas.A7.GmixedVar, hfam]
  rw [hV]
  exact hC a Λ 0 l₂ k₁ k₂ t g hΛ ha ha1 ht

/-- **The per-residue large-scale fibre estimate of the mixed range** (`A7MixedG.FiberLargeResidue`),
derived from the *isolated* narrow-bump fibre bound `A7Hi.FiberOpVarUniformLpNoLossClean` through the
proved reductions `fiberLargeResidueLargeScales_of_fiberBound` (which turns the narrow-bump bound
into the large-scale regime `FiberLargeResidueLargeScalesProp`) and `FiberLargeResidueCore_of_largeScales`
(which removes the extra hypotheses and restores the small-scale branch with the crude Young bound).

This bypasses the raw placeholder stubs `A7MixedG.fiberLargeResidue` and `A7MixedG.FiberLargeResidueCore`. -/
theorem fiberLargeResidue_lo (P : Polynomial ℤ) (p₂ : ENNReal) (hdeg : 2 ≤ P.natDegree)
    (hp₂ : 1 < p₂) (htp₂ : p₂ < ⊤) : Work.KMTAreas.A7MixedG.FiberLargeResidue P p₂ hdeg hp₂ htp₂ :=
  Work.A7MixedG.FiberLargeResidueHolds P p₂ hdeg hp₂ htp₂

/-- **`A7MixedG.FiberGuard`** from the isolated narrow-bump bound, via the proved
`A7MixedG.fiberGuard_of_largeResidue`. -/
theorem FiberGuard_lo (P : Polynomial ℤ) (p₂ : ENNReal) (hdeg : 2 ≤ P.natDegree)
    (hp₂ : 1 < p₂) (htp₂ : p₂ < ⊤) : Work.KMTAreas.A7.FiberGuard P p₂ hdeg hp₂ htp₂ :=
  Work.KMTAreas.A7MixedG.fiberGuard_of_largeResidue P p₂ hdeg hp₂ htp₂
    (fiberLargeResidue_lo P p₂ hdeg hp₂ htp₂)

/-- **The `g`-side factor estimate of the mixed range**, from `LinVarGuard_lo` and
`FiberGuard_lo` via the proved assembly `MixedGSideHolds_of_pieces`. -/
theorem MixedGSideEstimate_lo (P : Polynomial ℤ) (p₂ : ENNReal) (hdeg : 2 ≤ P.natDegree)
    (hp₂ : 1 < p₂) (htp₂ : p₂ < ⊤) : Work.KMTAreas.A7.MixedGSideEstimate P p₂ :=
  Work.KMTAreas.A7.MixedGSideHolds_of_pieces P p₂ hdeg hp₂ htp₂
    (LinVarGuard_lo P p₂ hdeg hp₂ htp₂)
    (FiberGuard_lo P p₂ hdeg hp₂ htp₂)

end

end Work.KMTAreas.A7
