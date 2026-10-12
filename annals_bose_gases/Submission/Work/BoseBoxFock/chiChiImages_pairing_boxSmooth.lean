import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.L1Tails.chiChiImages_pairing_coul
import Submission.Work.BoseBoxFock.pairRowDirDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.chiChiImages_pairing_boxSmooth` — the images row `T7` at the `BoxSmooth`
test-function class

The proved tail `Work.BoseBoxFock.L1Tails.chiChiImages_pairing_coul` bounds the box pairing of the
`χχ`-images kernel for a test function `G` that is **globally** `C^∞`.  The honest fibres of the
(S2) row are not globally smooth — they only agree, on the box squared, with a smooth function
(this is exactly the predicate `Work.BoseBoxFock.BoxSmooth` of `pairRowDirDefs.lean`).

This module upgrades the tail to that class.  The reduction is the pair of transport lemmas of
`pairRowDirDefs.lean`:

* `setIntegral_pairing_congr_box` — the box-squared pairing of any kernel only depends on the
  restriction of the test function to `boxL ℓ × boxL ℓ`, so the pairing may be evaluated at the
  smooth representative `G'` of `BoxSmooth ℓ G`;
* `pairEnergy_congr_box` — the Dirichlet energy `pairEnergy` is likewise blind to the values off
  the box squared, so `pairEnergy ℓ G' = pairEnergy ℓ G`.

The constant `C` produced is the one of the `C^∞` tail, hence independent of `ℓ`, `R`, `W`, `G`.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem chiChiImages_pairing_boxSmooth (K : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ {ℓ R : ℝ}, 0 < ℓ → 0 < R → R ≤ ℓ / 4 →
    ∀ {W : EuclideanSpace ℝ (Fin 3) → ℝ}, MeasureTheory.Integrable W → (∀ᵐ x, 0 ≤ W x) →
      (∀ x : EuclideanSpace ℝ (Fin 3), R ≤ ‖x‖ → W x = 0) →
      MeasureTheory.Integrable (Work.BoseBoxFock.coulInt W) →
    ∀ {G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ},
      Work.BoseBoxFock.BoxSmooth ℓ G →
      ‖∫ w in Work.BoseK15.corpusBox.boxL ℓ, ∫ y in Work.BoseK15.corpusBox.boxL ℓ,
          Work.BoseBoxFock.chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y * G w y‖
        ≤ C * (R / ℓ) ^ K * Real.sqrt (∫ p, Work.BoseBoxFock.coulInt W p)
          * Real.sqrt (ℓ ^ 3 * Work.BoseBoxFock.L1Tails.pairEnergy ℓ G) := by
  obtain ⟨C, hCnn, hC⟩ := Work.BoseBoxFock.L1Tails.chiChiImages_pairing_coul K
  refine ⟨C, hCnn, ?_⟩
  intro ℓ R hℓ hR hRℓ W hWi hW0 hWs hJ G hG
  obtain ⟨G', hG'sm, hG'eq⟩ := hG
  -- the pairing only sees the restriction to the box squared
  have hpair : (∫ w in Work.BoseK15.corpusBox.boxL ℓ, ∫ y in Work.BoseK15.corpusBox.boxL ℓ,
        Work.BoseBoxFock.chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y * G' w y)
      = ∫ w in Work.BoseK15.corpusBox.boxL ℓ, ∫ y in Work.BoseK15.corpusBox.boxL ℓ,
        Work.BoseBoxFock.chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y * G w y :=
    setIntegral_pairing_congr_box
      (K := Work.BoseBoxFock.chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)))
      (fun w y hw hy => hG'eq w y hw hy)
  -- and so does the Dirichlet energy
  have hE : Work.BoseBoxFock.L1Tails.pairEnergy ℓ G' = Work.BoseBoxFock.L1Tails.pairEnergy ℓ G :=
    pairEnergy_congr_box hℓ (fun w y hw hy => hG'eq w y hw hy)
  have hb := hC hℓ hR hRℓ hWi hW0 hWs hJ hG'sm
  calc ‖∫ w in Work.BoseK15.corpusBox.boxL ℓ, ∫ y in Work.BoseK15.corpusBox.boxL ℓ,
        Work.BoseBoxFock.chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y * G w y‖
      = ‖∫ w in Work.BoseK15.corpusBox.boxL ℓ, ∫ y in Work.BoseK15.corpusBox.boxL ℓ,
        Work.BoseBoxFock.chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y * G' w y‖ := by rw [hpair]
    _ ≤ C * (R / ℓ) ^ K * Real.sqrt (∫ p, Work.BoseBoxFock.coulInt W p)
          * Real.sqrt (ℓ ^ 3 * Work.BoseBoxFock.L1Tails.pairEnergy ℓ G) := by
        rw [← hE]
        exact hb

end Work.BoseBoxFock
