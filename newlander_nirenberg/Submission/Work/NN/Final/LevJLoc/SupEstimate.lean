import Mathlib
import Submission.Work.NN.Core.Lev.moserSource
import Submission.Work.NN.Final.LevJLoc.CaccSource

/-!
# The level-`0` sup estimate with `L²` remainder

`Work.NN.Core.Lev.supEstimateL2` with the smallness hypothesis on the perturbation at Hölder level
`0` instead of level `1`.  The proof is a copy of the original: the smallness is used only in the
level-`0` Caccioppoli source estimate, and `Work.NN.Core.Lev.moserSource` is `A`-free.
-/

namespace Work.NN.Final.LevJLoc

open scoped NNReal ENNReal ContDiff Topology
open Set MeasureTheory Filter
open Work.NN.Core Work.NN.Core.Lev

noncomputable section

variable {n : ℕ}

theorem supEstimateL2_v {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {σ ρ : Fin n → ℝ} (hσ0 : ∀ j, 0 < σ j) (hρ0 : ∀ j, 0 < ρ j) (hσρ : ∀ j, σ j < ρ j) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ {A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n},
        (∀ m : ℕ, ContDiff ℝ m A) → ∀ {ε : ℝ}, ε ≤ ε₀ →
        (∀ i j : Fin n, Work.CR.Flat.holderNorm 0 α
            (fun z => A z (Pi.single i 1) j) (Work.CR.Flat.polydisc 0 ρ)
          ≤ ENNReal.ofReal ε) →
        (∀ z, z ∈ Work.CR.Flat.polydisc 0 ρ → ∀ v : Work.NN.Core.Cn n,
          (Work.NN.Core.JstdCn n + A) z ((Work.NN.Core.JstdCn n + A) z v) = -v) →
        ∀ u : Work.NN.Core.Cn n → ℂ,
          ContDiffOn ℝ 1 u (Work.CR.Flat.polydisc 0 ρ) →
          (⨆ z ∈ Work.CR.Flat.polydisc 0 σ, ENNReal.ofReal ‖u z‖)
            ≤ ENNReal.ofReal C * ((∑ j : Fin n,
                  Work.CR.Flat.holderNorm 0 α
                    (fun z => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) u z (Pi.single j 1))
                    (Work.CR.Flat.polydisc 0 ρ))
                + MeasureTheory.eLpNorm u 2
                    (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 ρ))) := by
  obtain ⟨εc, hεc, Ac, hAc, hcac⟩ := powCaccioppoliSource_v (n := n) hn hα0 hα1 hρ0
  obtain ⟨Cm, hCm, hmos⟩ := moserSource (n := n) hn hσ0 hρ0 hσρ (A₀ := Ac) hAc
  refine ⟨εc, hεc, Cm, hCm, ?_⟩
  intro A hA ε hε hsmall hJ u hu
  set D : ℝ≥0∞ := ∑ j : Fin n, Work.CR.Flat.holderNorm 0 α
      (fun z => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) u z (Pi.single j 1))
      (Work.CR.Flat.polydisc 0 ρ) with hD
  rcases eq_or_ne D ⊤ with hDtop | hDne
  · -- trivial case: the right-hand side is `⊤`
    rw [hDtop, top_add, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr hCm)]
    exact le_top
  · have hDfin : ∀ j : Fin n, Work.CR.Flat.holderNorm 0 α
        (fun z => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) u z (Pi.single j 1))
        (Work.CR.Flat.polydisc 0 ρ) ≠ ⊤ := by
      intro j h
      refine hDne ?_
      rw [hD]
      exact (ENNReal.sum_eq_top).mpr ⟨j, Finset.mem_univ j, h⟩
    have hDtr : D.toReal = ∑ j : Fin n, (Work.CR.Flat.holderNorm 0 α
        (fun z => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) u z (Pi.single j 1))
        (Work.CR.Flat.polydisc 0 ρ)).toReal := by
      rw [hD, ENNReal.toReal_sum (fun j _ => hDfin j)]
    have hdatum : ∀ w ∈ Work.CR.Flat.polydisc 0 ρ,
        ∑ j : Fin n,
          ‖Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) u w (Pi.single j 1)‖^2
          ≤ D.toReal^2 := by
      intro w hw
      have h1 : ∀ j : Fin n, ‖Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) u w
          (Pi.single j 1)‖ ≤ (Work.CR.Flat.holderNorm 0 α
            (fun z => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) u z (Pi.single j 1))
            (Work.CR.Flat.polydisc 0 ρ)).toReal := by
        intro j
        have hb := Work.CR.Flat.norm_apply_le_holderNorm 0 α
          (fun z => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) u z (Pi.single j 1))
          (Work.CR.Flat.polydisc 0 ρ) hw
        rw [← ENNReal.ofReal_toReal (hDfin j)] at hb
        exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp hb
      have h2 : ∑ j : Fin n, ‖Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) u w
          (Pi.single j 1)‖ ≤ D.toReal := by
        rw [hDtr]
        exact Finset.sum_le_sum fun j _ => h1 j
      have h4 : ∀ j : Fin n, 0 ≤ ‖Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) u w
          (Pi.single j 1)‖ := fun j => norm_nonneg _
      have h3 : ∑ j : Fin n, ‖Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) u w
            (Pi.single j 1)‖^2
          ≤ (∑ j : Fin n, ‖Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) u w
            (Pi.single j 1)‖)^2 := by
        have h5 : ∑ j : Fin n, ‖Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) u w
              (Pi.single j 1)‖^2
            ≤ (∑ j : Fin n, ‖Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) u w
              (Pi.single j 1)‖) * (∑ j : Fin n, ‖Work.NN.Core.dbarCn
                (Work.NN.Core.JstdCn n + A) u w (Pi.single j 1)‖) := by
          rw [Finset.sum_mul]
          refine Finset.sum_le_sum fun j _ => ?_
          rw [sq]
          exact mul_le_mul_of_nonneg_left
            (Finset.single_le_sum (fun k _ => h4 k) (Finset.mem_univ j)) (h4 j)
        rw [sq]
        exact h5
      exact h3.trans (pow_le_pow_left₀ (Finset.sum_nonneg fun j _ => h4 j) h2 2)
    have hcac' : (∀ (k : ℕ), 1 ≤ k → ∀ (φ : Work.NN.Core.Cn n → ℝ),
        ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Work.CR.Flat.polydisc 0 ρ → (∀ z, 0 ≤ φ z) →
        ∫ z in Work.CR.Flat.polydisc 0 ρ,
            (k : ℝ)^2 * (φ z)^2 * (‖u z‖^2)^(k-1) *
              (∑ j, (‖Work.CR.Flat.dCoord j u z‖^2
                + ‖Work.CR.Flat.dbarCoord j u z‖^2))
          ≤ Ac * ((∫ z in Work.CR.Flat.polydisc 0 ρ, ‖fderiv ℝ φ z‖^2 * (‖u z‖^2)^k)
                 + (k:ℝ)^2 * ∫ z in Work.CR.Flat.polydisc 0 ρ,
                     (φ z)^2 * (‖u z‖^2)^(k-1) * D.toReal^2)) :=
      fun k hk φ hφ hcs hts hnn => hcac (A' := A) hA hε hsmall hJ k hk u hu
        (Λ := D.toReal) D.toReal_nonneg hdatum φ hφ hcs hts hnn
    refine (iSup₂_le fun z hz => hmos D.toReal_nonneg u hu hcac' z hz).trans ?_
    refine mul_le_mul' le_rfl ?_
    calc MeasureTheory.eLpNorm u 2 (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 ρ))
          + ENNReal.ofReal D.toReal
        ≤ MeasureTheory.eLpNorm u 2 (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 ρ))
          + D := add_le_add le_rfl ENNReal.ofReal_toReal_le
      _ = D + MeasureTheory.eLpNorm u 2
            (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 ρ)) := add_comm _ _


end

end Work.NN.Final.LevJLoc
