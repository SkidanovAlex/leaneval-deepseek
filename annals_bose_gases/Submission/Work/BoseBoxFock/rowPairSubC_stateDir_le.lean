import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.rowSum_roots_le_chi
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

/-- **The state-level (S2) substitution bound for the `Q₂` row, with the Dirichlet/mass budget
evaluated on the state.**

This is the assembly of the two independent halves:

* `Work.BoseBoxFock.rowPairSubC_stateDir` — the (S2) substitution of `KI → K1lim ℓ W₁'`,
  `KII → K1lim ℓ W₂'` at the row level, giving the sum of the six per-pair square roots
  (`pairEnergy`/`massBox` of the three fibres `pairG13`, `pairG21`, `pairG23`) with the prefactor
  `2·(ℓ³)⁻¹·max ε₁ ε₂`;
* `Work.BoseBoxFock.rowSum_roots_le_chi` — the evaluation of that sum on the state `Θ`, `A`:
  each fibre's Dirichlet energy is bounded by `C·cA²cA²·pinL2·(pinDirChi + pinL2)` (χ-weighted
  content!) and each fibre's mass by `(∫‖A‖²)²·(∫‖Θ‖²)²`, and there are at most `n·n` pairs.

Composing the two with `mul_le_mul_of_nonneg_left` yields the stated bound with the *same*
constant function `Cf` produced by `rowSum_roots_le_chi`. -/
theorem rowPairSubC_stateDir_le :
    ∃ Cf : ℝ → ℝ, (∀ l, 0 ≤ Cf l) ∧
      ∀ {n : ℕ} {ℓ ε₁ ε₂ : ℝ}, 0 < ℓ →
        ∀ {Θ Θ₀ : Work.BoseDict.Xn n → ℂ} {A : EuclideanSpace ℝ (Fin 3) → ℂ}
          {KI KII : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ}
          {W₁' W₂' : EuclideanSpace ℝ (Fin 3) → ℝ} {cA : ℝ},
        Measurable Θ → (∃ K : ℝ, ∀ x, ‖Θ x‖ ≤ K) →
        Function.support Θ ⊆ Work.MB.boxPow n ℓ →
        ContDiff ℝ (⊤ : ℕ∞) Θ₀ →
        (∀ x, Θ x = Set.indicator (Submission.BoseGases.abox n ℓ) Θ₀ x) →
        Measurable A → (∃ K : ℝ, ∀ x, ‖A x‖ ≤ K) → Work.BoseBoxFock.CutSmooth1 ℓ A →
        Measurable (Function.uncurry KI) → (∃ K : ℝ, ∀ w y, ‖KI w y‖ ≤ K) →
        Measurable (Function.uncurry KII) → (∃ K : ℝ, ∀ w y, ‖KII w y‖ ≤ K) →
        MeasureTheory.Integrable W₁' → MeasureTheory.Integrable W₂' →
        0 ≤ ε₁ → 0 ≤ ε₂ → 0 ≤ cA → (∀ x, ‖A x‖ ≤ cA) →
        MeasureTheory.Integrable (fun x : Work.BoseDict.Xn n => ‖Θ x‖ ^ 2) →
        MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin 3) => ‖A x‖ ^ 2) →
        (∀ G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ,
          Work.BoseBoxFock.BoxSmooth ℓ G →
          ‖∫ w in Work.BoseK15.corpusBox.boxL ℓ,
             ∫ y in Work.BoseK15.corpusBox.boxL ℓ,
               (KI w y - Work.BoseBoxFock.K1lim ℓ W₁' w y) * G w y‖
            ≤ ε₁ * (Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy ℓ G)
                + Real.sqrt (Work.BoseBoxFock.massBox ℓ G))) →
        (∀ G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ,
          Work.BoseBoxFock.BoxSmooth ℓ G →
          ‖∫ w in Work.BoseK15.corpusBox.boxL ℓ,
             ∫ y in Work.BoseK15.corpusBox.boxL ℓ,
               (KII w y - Work.BoseBoxFock.K1lim ℓ W₂' w y) * G w y‖
            ≤ ε₂ * (Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy ℓ G)
                + Real.sqrt (Work.BoseBoxFock.massBox ℓ G))) →
        ‖Work.BoseBoxFock.rowPairSubC ((ℓ ^ 3)⁻¹) Θ A KI KII
            - Work.BoseBoxFock.rowPairSubC ((ℓ ^ 3)⁻¹) Θ A
                (Work.BoseBoxFock.K1lim ℓ W₁') (Work.BoseBoxFock.K1lim ℓ W₂')‖
          ≤ 2 * (ℓ ^ 3)⁻¹ * max ε₁ ε₂
              * (Cf ℓ * (n : ℝ) * (n : ℝ)
                  * (cA ^ 2 * (Real.sqrt (Work.BoseBoxFock.pinL2 ℓ Θ₀)
                        * Real.sqrt (Work.BoseBoxFock.pinDirChi ℓ Θ₀
                            + Work.BoseBoxFock.pinL2 ℓ Θ₀))
                    + (∫ x : EuclideanSpace ℝ (Fin 3), ‖A x‖ ^ 2)
                      * (∫ x : Work.BoseDict.Xn n, ‖Θ x‖ ^ 2))) := by
  obtain ⟨Cf, hCf0, hCf⟩ := rowSum_roots_le_chi
  refine ⟨Cf, hCf0, ?_⟩
  intro n ℓ ε₁ ε₂ hℓ Θ Θ₀ A KI KII W₁' W₂' cA
    hΘm hΘb hΘs hΘ₀ hΘind hAm hAb hCutA hKIm hKIb hKIIm hKIIb hWi₁ hWi₂
    hε₁ hε₂ hcA hAc hΘL hAL hPairI hPairII
  -- the (S2) substitution at the row level
  have hmain := rowPairSubC_stateDir (n := n) (ℓ := ℓ) (ε₁ := ε₁) (ε₂ := ε₂) hℓ
    (Θ := Θ) (Θ₀ := Θ₀) (A := A) (KI := KI) (KII := KII) (W₁' := W₁') (W₂' := W₂')
    hΘm hΘb hΘs hΘ₀ hΘind hAm hAb hCutA hKIm hKIb hKIIm hKIIb hWi₁ hWi₂
    hε₁ hε₂ hPairI hPairII
  -- the evaluation of the per-pair square-root sum on the state
  have hsum := hCf hℓ hΘm hΘb hΘs hΘL hΘ₀ hΘind hAm hAb hAL hcA hAc
  -- the prefactor is nonnegative
  have hcoef0 : 0 ≤ 2 * (ℓ ^ 3)⁻¹ * max ε₁ ε₂ := by
    have hmax0 : 0 ≤ max ε₁ ε₂ := le_trans hε₁ (le_max_left ε₁ ε₂)
    positivity
  exact hmain.trans (mul_le_mul_of_nonneg_left hsum hcoef0)

end Work.BoseBoxFock
