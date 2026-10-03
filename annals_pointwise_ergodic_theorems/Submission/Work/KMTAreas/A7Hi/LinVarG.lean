import Mathlib
import Submission.Work.KMTAreas.A7Hi.Gassembly
import Submission.Work.KMTAreas.A7Hi.lowpassVarG

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTAreas.A7Hi

/-- **`LinVarG` with the three dyadic pieces of the low-pass estimate as hypotheses.**  This is the
complete wiring of the `g`-side linear lacunary variational estimate: the assembly
`lacunaryBumpVarEstimate_assemblyG` (proved, axiom-clean) consumes the low-pass estimate, the
clipped low-pass estimate (derived from the low-pass one by `lacunaryBumpLowpassClipBoundG`) and the
poor-scales estimate (`lacunaryBumpBadPartBoundG`); the low-pass estimate is supplied by
`Work.KMTAreas.A7Hi2.lowpassVarG_of_pieces` from the three dyadic pieces `SupPiece`, `ChainPiece`,
`SqPiece`. -/
theorem linVarG_of_pieces (hSup : Work.KMTAreas.A7Hi2.SupPiece)
    (hChain : Work.KMTAreas.A7Hi2.ChainPiece) (hSq : Work.KMTAreas.A7Hi2.SqPiece)
    (P : Polynomial ℤ) (hdeg : 2 ≤ P.natDegree) (C₀ : ℕ) (hC₀ : 1 ≤ C₀)
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
  refine lacunaryBumpVarEstimate_assemblyG P hdeg ?_ ?_ ?_ C₀ hC₀ r hr
  · -- the low-pass piece (paper (lin-2), `s₂ = -u`, `j₂ = 0`), from the three dyadic pieces
    exact Work.KMTAreas.A7Hi2.lowpassVarG_of_pieces hSup hChain hSq P.natDegree (by omega)
  · -- the clipped low-pass piece, derived from the low-pass piece
    intro ρ hρ hρ1 C₀ Cρc Cρ hCρpos hCρc Λ hΛ r hr p hp hptop C hCpos hLow
    exact lacunaryBumpLowpassClipBoundG (P.natDegree) (by omega) ρ hρ hρ1 C₀ Cρc Cρ
      hCρpos hCρc Λ hΛ r hr p hp hptop C hCpos hLow
  · -- the poor (non-narrow) scales
    intro ρ hρ hρ1 C₀ hC₀ hρC Cρc hCρc Λ hΛ r hr p hp hptop
    exact Work.KMTAreas.A7Hi.lacunaryBumpBadPartBoundG P P.natDegree hdeg le_rfl ρ hρ hρ1 C₀ hC₀ hρC
      Cρc hCρc Λ hΛ r hr p hp hptop

/-- The `g`-side linear lacunary variational estimate (paper (lin-1)/(lin-2), §8) for the exact-height Ionescu--Wainger projections of the modulated `g`-bumps `φ̃_{N,t}` (with the polynomial twist `P`).  Import `Submission.Work.KMTAreas.A7.LargeInterface` for `Gcl`, `lossWeight`, `core`.  The existing stub `Submission/Work/KMTAreas/A7/lacunaryBumpVarEstimateG.lean` is the same statement (its right-hand side has an auto-bound extra exponent, so it is stated here with `p` explicitly); the `f`-side analogue is `Work.KMTAreas.A7.lacunaryBumpVarEstimate` and the route is documented in `NOTES_lacunaryBumpVarEstimate_SESSION.md`. -/
theorem LinVarG (P : Polynomial ℤ) (hdeg : 2 ≤ P.natDegree) (C₀ : ℕ) (hC₀ : 1 ≤ C₀)
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
  refine lacunaryBumpVarEstimate_assemblyG P hdeg ?_ ?_ ?_ C₀ hC₀ r hr
  · -- the low-pass piece (paper (lin-2), `s₂ = -u`, `j₂ = 0`)
    exact lowpassVarG P hdeg
  · -- the clipped low-pass piece, derived from the low-pass piece
    intro ρ hρ hρ1 C₀ Cρc Cρ hCρpos hCρc Λ hΛ r hr p hp hptop C hCpos hLow
    exact lacunaryBumpLowpassClipBoundG (P.natDegree) (by omega) ρ hρ hρ1 C₀ Cρc Cρ
      hCρpos hCρc Λ hΛ r hr p hp hptop C hCpos hLow
  · -- the poor (non-narrow) scales
    intro ρ hρ hρ1 C₀ hC₀ hρC Cρc hCρc Λ hΛ r hr p hp hptop
    exact Work.KMTAreas.A7Hi.lacunaryBumpBadPartBoundG P P.natDegree hdeg le_rfl ρ hρ hρ1 C₀ hC₀ hρC
      Cρc hCρc Λ hΛ r hr p hp hptop

end Work.KMTAreas.A7Hi
