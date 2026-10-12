import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.kfBlock2Self
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

theorem potPairRows_kernelForm {m : ℕ} [NeZero m] {n : ℕ} {ℓ : ℝ} {Mode : Type*}
    [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hmeas : ∀ l, Measurable (e l))
    (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : EuclideanSpace ℝ (Fin 3), star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (f : Mode → Fin m → ℝ) (hf0 : ∀ k, f k 0 = 0) (E : Work.BoseB7.Q3Env Mode)
    (Fp : Mode → EuclideanSpace ℝ (Fin 3) → ℂ) (Th : EuclideanSpace ℝ (Fin 3) → ℂ)
    (hF : ∀ k, Work.BoseDict.etaOf e (f k) =ᵐ[MeasureTheory.volume] Fp k)
    (hTh : Work.BoseDict.etaOf e (Work.BoseBoxFock.evec0 m) =ᵐ[MeasureTheory.volume] Th)
    (Theta : Work.BoseDict.Xn n → ℂ) (hΘm : Measurable Theta)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Theta x‖ ≤ C)
    (hΘs : Function.support Theta ⊆ Work.MB.boxPow n ℓ) :
    Work.BoseDict.cIPn n Theta
        (potPairRows (fun T => Work.BoseDict.boxSlotSum e T) f E Theta)
      = (E.ell ^ (-(3 : ℝ))) •
          (∑ p ∈ Submission.BoseGases.pairSet n,
            ∫ x : Work.BoseDict.Xn n, ∫ y : EuclideanSpace ℝ (Fin 3),
              ∫ u : EuclideanSpace ℝ (Fin 3),
              (starRingEnd ℂ) (Theta x) * Th (x p.1)
                * (∑ k : Mode, (E.W1 k + E.W1omega k)
                    * (Fp k (x p.2) * (starRingEnd ℂ) (Fp k y)))
                * (starRingEnd ℂ) (Th u)
                * Theta (Function.update (Function.update x p.1 y) p.2 u))
        + ((1 / 2 : ℝ) * E.ell ^ (-(3 : ℝ))) •
          ((∑ p ∈ Submission.BoseGases.pairSet n,
              ∫ x : Work.BoseDict.Xn n, ∫ y : EuclideanSpace ℝ (Fin 3),
                ∫ u : EuclideanSpace ℝ (Fin 3),
                (starRingEnd ℂ) (Theta x) * Th (x p.1) * Th (x p.2)
                  * (∑ k : Mode, E.W1 k
                      * ((starRingEnd ℂ) (Fp k y) * (starRingEnd ℂ) (Fp (-k) u)))
                  * Theta (Function.update (Function.update x p.1 y) p.2 u))
            + (∑ p ∈ Submission.BoseGases.pairSet n,
              ∫ x : Work.BoseDict.Xn n, ∫ y : EuclideanSpace ℝ (Fin 3),
                ∫ u : EuclideanSpace ℝ (Fin 3),
                (starRingEnd ℂ) (Theta x)
                  * (∑ k : Mode, E.W1 k * (Fp k (x p.1) * Fp (-k) (x p.2)))
                  * (starRingEnd ℂ) (Th y) * (starRingEnd ℂ) (Th u)
                  * Theta (Function.update (Function.update x p.1 y) p.2 u)))
        + (∑ k : Mode,
            ((E.ell ^ (-(3 : ℝ)) * E.W1 0 + E.ell ^ (-(3 : ℝ)) * E.W1omega0) •
                (∑ p ∈ Submission.BoseGases.pairSet n,
                  ∫ x : Work.BoseDict.Xn n, ∫ y : EuclideanSpace ℝ (Fin 3),
                    ∫ u : EuclideanSpace ℝ (Fin 3),
                    (starRingEnd ℂ) (Theta x) * Th (x p.1) * (starRingEnd ℂ) (Th y)
                      * Fp k (x p.2) * (starRingEnd ℂ) (Fp k u)
                      * Theta (Function.update (Function.update x p.1 y) p.2 u))
              - (E.mu * E.W1 0) •
                (∑ j : Fin n,
                  ∫ x : Work.BoseDict.Xn n, ∫ y : EuclideanSpace ℝ (Fin 3),
                    (starRingEnd ℂ) (Theta x) * Fp k (x j) * (starRingEnd ℂ) (Fp k y)
                      * Theta (Function.update x j y)))) := by
  classical
  -- the everywhere-good representatives: the superpositions `η_{f k}` and `η_{evec0}`
  have hηm : ∀ k : Mode, Measurable (Work.BoseDict.etaOf e (f k)) :=
    fun k => Work.MB.etaOf_weak_measurable hmeas (f k)
  have hηb : ∀ k : Mode, ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖Work.BoseDict.etaOf e (f k) z‖ ≤ C :=
    fun k => Work.MB.etaOf_weak_bound hbdd (f k)
  have hθm : Measurable (Work.BoseDict.etaOf e (evec0 m)) :=
    Work.MB.etaOf_weak_measurable hmeas _
  have hθb : ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖Work.BoseDict.etaOf e (evec0 m) z‖ ≤ C :=
    Work.MB.etaOf_weak_bound hbdd _
  have hΘb' : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖Theta x‖ ≤ C := by
    obtain ⟨C, hC⟩ := hΘb
    exact ⟨max C 0, le_max_right _ _, fun x => le_trans (hC x) (le_max_left _ _)⟩
  -- the two block conversions (the third block is common to the two spellings)
  have hb1 := potPairRowsKernelBlock1 (ℓ := ℓ) E Fp (fun k => Work.BoseDict.etaOf e (f k))
    Th (Work.BoseDict.etaOf e (evec0 m)) Theta
    hηm hηb hθm hθb (fun k => (hF k).symm) hTh.symm hΘm hΘb' hΘs
  have hb2 := potPairRowsKernelBlock2Local (ℓ := ℓ) E Fp (fun k => Work.BoseDict.etaOf e (f k))
    Th (Work.BoseDict.etaOf e (evec0 m)) Theta
    hηm hηb hθm hθb (fun k => (hF k).symm) hTh.symm hΘm hΘb' hΘs
  -- the pinned normal form of the `Q₂` row
  have hpin := potPairRows_cIPn_pinned_gen (ℓ := ℓ) hmeas hbdd hsupp horth f hf0 E Fp Th
    hF hTh Theta hΘm hΘb hΘs
  refine hpin.trans ?_
  rw [hb1, hb2]

end Work.BoseBoxFock
