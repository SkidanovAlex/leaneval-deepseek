import Mathlib
import Submission.Work.Drive.collapseT5

/-!
# The diameter side of `T5` in the form the transport consumes (`ht5`)

The transport `T6` (`Work.Drive.odd_topBdryMeet_zero_iff_coreSideCount_mul_of_design_intrinsic_nf`,
`transportT6Sharp.lean`) consumes the diameter parity

> `Odd (diamMeet Q q.1 W).ncard ↔ Odd (coreSideCount Q c₂ P₂)`

at the finitely many parameters `q.1` of the core meets (`ht5`; the *uniform* form `∀ t` is false in
general — see `NOTES_LEAD_hblock_uniformity.md` §4.2 — but it is *derivable* from the family regularity
data of the two interpolation families).

`Work.Drive.odd_ncard_diamMeet_iff_arcMeet` and `Work.Drive.odd_ncard_arcMeet_iff_core`
(`collapseT5.lean`, both proved) supply the two halves; this file composes them into the single
implication the transport wants, so that a consumer supplies the family data once and gets `ht5`
directly.  (The hypothesis lists are those of the two lemmas, with `W` specialised to
`clampedSweep c (fun s => 1 - s) P` and the hypothesis names distinguished.)

Everything is sorry-free and axiom-clean.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-- **`ht5`: the diameter parity at the parameter `t`, from the family regularity data.** -/
theorem odd_ncard_diamMeet_iff_coreSideCount (Q : ℂ → CappingSpace) (t c : ℝ)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z)
    (hLd : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (diamFam Q t))
    (hLa : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (arcFam Q t))
    (hN : ContMDiff (𝓡 3) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (clampedSweep c (fun s => 1 - s) P))
    (hseam : ∀ x : EuclideanSpace ℝ (Fin 3), onSeam x →
      clampedSweep c (fun s => 1 - s) P (seamInv x) = clampedSweep c (fun s => 1 - s) P x)
    (havoidD : ∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)),
      diamFam Q t u = clampedSweep c (fun s => 1 - s) P x → x ∈ Submission.Drive.unitBox 2 →
      (x 2 = 0 ∨ x 2 = 1) → False)
    (htransD : ∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)),
      diamFam Q t u = clampedSweep c (fun s => 1 - s) P x →
      LinearMap.range (mfderiv (𝓡 2) (𝓡 4) (diamFam Q t) u).toLinearMap ⊔
        LinearMap.range
          (mfderiv (𝓡 3) (𝓡 4) (clampedSweep c (fun s => 1 - s) P) x).toLinearMap = ⊤)
    (hfaceD : ∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)),
      diamFam Q t u = clampedSweep c (fun s => 1 - s) P x →
      u ∈ Submission.Drive.unitBox 1 → x ∈ Submission.Drive.unitBox 2 →
      (u ∈ Submission.Drive.unitBoxBdry 1 ∨ x ∈ Submission.Drive.unitBoxBdry 2) →
      (∃ i : Fin 2, (u i = 0 ∨ u i = 1) ∧ (∀ j : Fin 2, j ≠ i → u j ∈ Set.Ioo (0 : ℝ) 1) ∧
          (∀ j : Fin 3, x j ∈ Set.Ioo (0 : ℝ) 1) ∧
          ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
            mfderiv (𝓡 2) (𝓡 4) (diamFam Q t) u σ
              = mfderiv (𝓡 3) (𝓡 4) (clampedSweep c (fun s => 1 - s) P) x τ ∧ σ i ≠ 0)
        ∨ (∃ j : Fin 3, (x j = 0 ∨ x j = 1) ∧ (∀ k : Fin 3, k ≠ j → x k ∈ Set.Ioo (0 : ℝ) 1) ∧
            (∀ i : Fin 2, u i ∈ Set.Ioo (0 : ℝ) 1) ∧
            ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
              mfderiv (𝓡 2) (𝓡 4) (diamFam Q t) u σ
                = mfderiv (𝓡 3) (𝓡 4) (clampedSweep c (fun s => 1 - s) P) x τ ∧ τ j ≠ 0))
    (havoidA : ∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)),
      arcFam Q t u = clampedSweep c (fun s => 1 - s) P x → x ∈ Submission.Drive.unitBox 2 →
      (x 2 = 0 ∨ x 2 = 1) → False)
    (htransA : ∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)),
      arcFam Q t u = clampedSweep c (fun s => 1 - s) P x →
      LinearMap.range (mfderiv (𝓡 2) (𝓡 4) (arcFam Q t) u).toLinearMap ⊔
        LinearMap.range
          (mfderiv (𝓡 3) (𝓡 4) (clampedSweep c (fun s => 1 - s) P) x).toLinearMap = ⊤)
    (hfaceA : ∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)),
      arcFam Q t u = clampedSweep c (fun s => 1 - s) P x →
      u ∈ Submission.Drive.unitBox 1 → x ∈ Submission.Drive.unitBox 2 →
      (u ∈ Submission.Drive.unitBoxBdry 1 ∨ x ∈ Submission.Drive.unitBoxBdry 2) →
      (∃ i : Fin 2, (u i = 0 ∨ u i = 1) ∧ (∀ j : Fin 2, j ≠ i → u j ∈ Set.Ioo (0 : ℝ) 1) ∧
          (∀ j : Fin 3, x j ∈ Set.Ioo (0 : ℝ) 1) ∧
          ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
            mfderiv (𝓡 2) (𝓡 4) (arcFam Q t) u σ
              = mfderiv (𝓡 3) (𝓡 4) (clampedSweep c (fun s => 1 - s) P) x τ ∧ σ i ≠ 0)
        ∨ (∃ j : Fin 3, (x j = 0 ∨ x j = 1) ∧ (∀ k : Fin 3, k ≠ j → x k ∈ Set.Ioo (0 : ℝ) 1) ∧
            (∀ i : Fin 2, u i ∈ Set.Ioo (0 : ℝ) 1) ∧
            ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
              mfderiv (𝓡 2) (𝓡 4) (arcFam Q t) u σ
                = mfderiv (𝓡 3) (𝓡 4) (clampedSweep c (fun s => 1 - s) P) x τ ∧ τ j ≠ 0)) :
    Odd (diamMeet Q t (clampedSweep c (fun s => 1 - s) P)).ncard ↔
      Odd (coreSideCount Q c P) :=
  (odd_ncard_diamMeet_iff_arcMeet Q t (clampedSweep c (fun s => 1 - s) P) hQseam hLd hN hseam
    havoidD htransD hfaceD).trans
    (odd_ncard_arcMeet_iff_core Q t c P hQseam hLa hN hseam havoidA htransA hfaceA)

end

end Work.Drive
