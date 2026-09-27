import Mathlib
import Submission.Work.Drive.coreMeet_ncard_eq_famMeet_gen
import Submission.Work.Drive.odd_ncard_famMeet_iff
import Submission.Work.Drive.designCount

/-!
# The moving-chart L6-family lemma, and the perturbation-independence of the design's count

`Work.Drive.odd_coreSideCount_iff_of_famRegular` (`Drive/designCountLocality.lean`) is the
`hn4`-shaped lemma for a **fixed** chart: the parity of `coreSideCount Q c (P t)` is the same at the
two ends of a family `t ↦ P t` of plane presentations, provided the loop-vs-sweep family satisfies the
L6 regularity hypotheses.

For the *full* design's count
`designCount Q A A' c ψ u = Odd (coreSideCount (linCapping A ∘ Q) c (linCapping A' ∘ rotPresentation Q u))`
the chart `linCapping A ∘ Q` **also** moves with the perturbation, so the fixed-chart lemma does not
apply as it stands.  This file is the verbatim generalisation obtained by replacing the bridge
`Work.Drive.coreMeet_ncard_eq_famMeet` with its moving-chart form
`Work.Drive.coreMeet_ncard_eq_famMeet_gen` (whose loop side is `chartLoopFam Q`):

* `Work.Drive.odd_coreSideCount_iff_of_famRegular_gen` — the family lemma for a family
  `t ↦ (Q t, P t)` of chart/plane pairs;
* `Work.Drive.designCount_perturb_indep` — the design-facing consequence: for a family
  `t ↦ (A t, A' t)` of *class perturbations* the value of `designCount` is the same at the two ends
  (the count is insensitive to the perturbation, whenever the family is regular).

This is the lead's item "expose `designCount` parity is independent of small `(A, A′)` as an L6-family
lemma" (message of 11:00), in the form that covers the full `designCount` (both the chart and the
sweep perturbed).
-/

namespace Work.Drive

open Manifold Filter
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-- **The L6-family lemma with a *moving chart*.**  If the loop-vs-sweep family of the family of charts
`t ↦ Q t` against the family of plane presentations `t ↦ P t` satisfies the regularity hypotheses of
the L6 engine, then the parities of the two end counts agree.  (`Q : ℝ → ℂ → CappingSpace` is a family
of charts; the loop side is `chartLoopFam Q`, i.e. `p ↦ coreLoop (Q (p 0)) (p 1)`.) -/
theorem odd_coreSideCount_iff_of_famRegular_gen (Q : ℝ → ℂ → CappingSpace) (c : ℝ)
    (P : ℝ → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hL : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (chartLoopFam Q))
    (hN : ContMDiff (𝓡 4) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (sweepFam c (fun s => 1 - s) P))
    (hloop : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      chartLoopFam Q (mk2 t 0) = chartLoopFam Q (mk2 t 1))
    (hseam : ∀ (t : ℝ) (x : EuclideanSpace ℝ (Fin 3)), onSeam x →
      sweepFam c (fun s => 1 - s) P (famPt t (seamInv x))
        = sweepFam c (fun s => 1 - s) P (famPt t x))
    (havoid : ∀ p : EuclideanSpace ℝ (Fin 5), p ∈ Submission.Drive.unitBox 4 →
      famLoop (chartLoopFam Q) p = famChain (sweepFam c (fun s => 1 - s) P) p →
      (p 4 = 0 ∨ p 4 = 1) → False)
    (htrans : ∀ p : EuclideanSpace ℝ (Fin 5), p ∈ Submission.Drive.unitBox 4 →
      famLoop (chartLoopFam Q) p = famChain (sweepFam c (fun s => 1 - s) P) p →
      Function.Surjective (fun v : EuclideanSpace ℝ (Fin 5) =>
        (show EuclideanSpace ℝ (Fin 4) from
            mfderiv (𝓡 5) (𝓡 4) (famLoop (chartLoopFam Q)) p v)
          - (show EuclideanSpace ℝ (Fin 4) from
              mfderiv (𝓡 5) (𝓡 4) (famChain (sweepFam c (fun s => 1 - s) P)) p v)))
    (hface : ∀ p : EuclideanSpace ℝ (Fin 5), p ∈ Submission.Drive.unitBox 4 →
      famLoop (chartLoopFam Q) p = famChain (sweepFam c (fun s => 1 - s) P) p →
      p ∈ Submission.Drive.unitBoxBdry 4 →
      ∃ i : Fin 5, (p i = 0 ∨ p i = 1) ∧ (∀ j : Fin 5, j ≠ i → p j ∈ Set.Ioo (0 : ℝ) 1) ∧
        ∃ σ : EuclideanSpace ℝ (Fin 5),
          mfderiv (𝓡 5) (𝓡 4) (famLoop (chartLoopFam Q)) p σ
            = mfderiv (𝓡 5) (𝓡 4) (famChain (sweepFam c (fun s => 1 - s) P)) p σ ∧ σ i ≠ 0) :
    Odd (coreSideCount (Q 0) c (P 0)) ↔ Odd (coreSideCount (Q 1) c (P 1)) := by
  rw [coreSideCount, coreSideCount,
    coreMeet_ncard_eq_famMeet_gen Q c P 0 (by norm_num),
    coreMeet_ncard_eq_famMeet_gen Q c P 1 (by norm_num)]
  exact odd_ncard_famMeet_iff CappingSpace (chartLoopFam Q) (sweepFam c (fun s => 1 - s) P)
    hL hN hloop hseam havoid htrans hface

/-- **The perturbation-independence of the design's count.**  For a family `t ↦ (A t, A' t)` of class
perturbations, if the loop-vs-sweep family of the perturbed chart `linCapping (A t) ∘ Q` against the
perturbed rotated plane `linCapping (A' t) ∘ rotPresentation Q u` is regular in the L6 sense, then the
design's count has the same parity at the two ends.  In particular the count does not see a small
change of the perturbation, so the perturbation may be chosen per angle (which is what the design's
`hdense`/`hn2` arguments need). -/
theorem designCount_perturb_indep {γ : Circle → ℝ × ℝ} (Q : ℂ → CappingSpace)
    (A A' : ℝ → Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (ψ : ℝ → ℝ) (u : UnitAddCircle)
    (hL : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (chartLoopFam (fun t z => linCapping (A t) (Q z))))
    (hN : ContMDiff (𝓡 4) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (sweepFam c (fun s => 1 - s)
        (fun t y => linCapping (A' t) (rotPresentation Q u y))))
    (hloop : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      chartLoopFam (fun t z => linCapping (A t) (Q z)) (mk2 t 0)
        = chartLoopFam (fun t z => linCapping (A t) (Q z)) (mk2 t 1))
    (hseam : ∀ (t : ℝ) (x : EuclideanSpace ℝ (Fin 3)), onSeam x →
      sweepFam c (fun s => 1 - s) (fun t y => linCapping (A' t) (rotPresentation Q u y))
          (famPt t (seamInv x))
        = sweepFam c (fun s => 1 - s) (fun t y => linCapping (A' t) (rotPresentation Q u y))
          (famPt t x))
    (havoid : ∀ p : EuclideanSpace ℝ (Fin 5), p ∈ Submission.Drive.unitBox 4 →
      famLoop (chartLoopFam (fun t z => linCapping (A t) (Q z))) p
        = famChain (sweepFam c (fun s => 1 - s)
            (fun t y => linCapping (A' t) (rotPresentation Q u y))) p →
      (p 4 = 0 ∨ p 4 = 1) → False)
    (htrans : ∀ p : EuclideanSpace ℝ (Fin 5), p ∈ Submission.Drive.unitBox 4 →
      famLoop (chartLoopFam (fun t z => linCapping (A t) (Q z))) p
        = famChain (sweepFam c (fun s => 1 - s)
            (fun t y => linCapping (A' t) (rotPresentation Q u y))) p →
      Function.Surjective (fun v : EuclideanSpace ℝ (Fin 5) =>
        (show EuclideanSpace ℝ (Fin 4) from
            mfderiv (𝓡 5) (𝓡 4)
              (famLoop (chartLoopFam (fun t z => linCapping (A t) (Q z)))) p v)
          - (show EuclideanSpace ℝ (Fin 4) from
              mfderiv (𝓡 5) (𝓡 4)
                (famChain (sweepFam c (fun s => 1 - s)
                  (fun t y => linCapping (A' t) (rotPresentation Q u y)))) p v)))
    (hface : ∀ p : EuclideanSpace ℝ (Fin 5), p ∈ Submission.Drive.unitBox 4 →
      famLoop (chartLoopFam (fun t z => linCapping (A t) (Q z))) p
        = famChain (sweepFam c (fun s => 1 - s)
            (fun t y => linCapping (A' t) (rotPresentation Q u y))) p →
      p ∈ Submission.Drive.unitBoxBdry 4 →
      ∃ i : Fin 5, (p i = 0 ∨ p i = 1) ∧ (∀ j : Fin 5, j ≠ i → p j ∈ Set.Ioo (0 : ℝ) 1) ∧
        ∃ σ : EuclideanSpace ℝ (Fin 5),
          mfderiv (𝓡 5) (𝓡 4)
              (famLoop (chartLoopFam (fun t z => linCapping (A t) (Q z)))) p σ
            = mfderiv (𝓡 5) (𝓡 4)
                (famChain (sweepFam c (fun s => 1 - s)
                  (fun t y => linCapping (A' t) (rotPresentation Q u y)))) p σ ∧ σ i ≠ 0) :
    designCount Q (A 0) (A' 0) c ψ u = designCount Q (A 1) (A' 1) c ψ u := by
  have hiff := odd_coreSideCount_iff_of_famRegular_gen
    (fun t z => linCapping (A t) (Q z)) c
    (fun t y => linCapping (A' t) (rotPresentation Q u y))
    hL hN hloop hseam havoid htrans hface
  rw [designCount, designCount]
  by_cases h0 : Odd (coreSideCount (fun z => linCapping (A 0) (Q z)) c
    (fun y => linCapping (A' 0) (rotPresentation Q u y)))
  · rw [if_pos h0, if_pos (hiff.mp h0)]
  · rw [if_neg h0, if_neg (fun h1 => h0 (hiff.mpr h1))]

end

end Work.Drive
