/-
# The frozen-`t` single-scale bound of Case B, with the bounded-bump interface

`Work.KMTPlan.A6.lowFrozenBilinBound` with the single-scale estimate in its `Linf` form
(`Work.KMTPlan.A6.SSUBodyAtLinf`), and with the two `L^∞`-membership facts of the *randomised*
symbols `randSymb (lowModSymbF …) ε K`, `randSymb (lowModSymbG …) ε' K` produced from the two
pointwise bounds of the members of the families (the extra hypotheses `hbF`, `hbG`) via
`Work.KMTPlan.A6.Linf.memLp_periodize_randSymb`.

The remaining public declarations used by the proof (`VrFull_TmBtwist_le_rand_uniform`,
`tmSideBumpNtj`, `TmSide_lowModSymbF`, `tmBddLowModSymbF`, …) are taken from the original module.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.lowFrozenBilinBound
import Submission.Work.KMTPlan.A6.lowModRandL2Gh
import Submission.Work.KMTPlan.A6.LinfDefs

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Work.KMTPlan.A6.Linf

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators Interval
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger
open Work.KMTAreas.A7

theorem lowFrozenBilinBound (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) :
    ∃ C_RM : ℝ, 0 < C_RM ∧
      ∀ (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (ρ : ℝ) (hρ : 0 < ρ) (B : ℕ)
        (C : NNReal → NNReal)
        (hRanF : Work.KMTPlan.A6.LowModRandL2FBody P C₀ ρ B C)
        (hRanG : Work.KMTPlan.A6.LowModRandL2GBody P C₀ ρ B C)
        (cS : ℝ) (hcS : 0 < cS) (Cssu : NNReal)
        (hSS : ∀ (m₁ m₂ u : ℕ) (φ ψ : ℝ → ℂ) (f' g' : ℤ → ℂ),
          (max m₁ m₂ : ℝ) ≤ (u : ℝ) →
          (2 : ℝ) ^ (ρ * (max m₁ m₂ : ℝ)) ≤ (u : ℝ) →
          MeasureTheory.MemLp f' 2 MeasureTheory.Measure.count →
          MeasureTheory.MemLp g' 2 MeasureTheory.Measure.count →
          MeasureTheory.MemLp (Work.Analysis.IonescuWainger.periodize φ) ⊤
            Work.Analysis.IonescuWainger.circleMeasure →
          MeasureTheory.MemLp (Work.Analysis.IonescuWainger.periodize ψ) ⊤
            Work.Analysis.IonescuWainger.circleMeasure →
          (∀ ξ : ℝ, φ ξ ≠ 0 → |ξ| ≤ (2 : ℝ) ^ (-(3 * (u : ℤ)))) →
          (∀ ξ : ℝ, ψ ξ ≠ 0 → |ξ| ≤ (2 : ℝ) ^ (-(3 * (P.natDegree : ℤ) * (u : ℤ)))) →
          MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTPlan.A6.BtwistEx ρ P m₁ m₂
              (Work.KMTAreas.A7.mStarF u)
              (Work.KMTAreas.A7.mStargF P.natDegree u)
              (Work.KMTAreas.A7.Tm ρ m₁ φ f') (Work.KMTAreas.A7.Tm ρ m₂ ψ g') x)
            1 MeasureTheory.Measure.count
            ≤ (Cssu : ENNReal) * ENNReal.ofReal ((2 : ℝ) ^ (-(cS * (max (m₁ : ℝ) (m₂ : ℝ)))))
                * MeasureTheory.eLpNorm (Work.KMTAreas.A7.Tm ρ m₁ φ f') 2 MeasureTheory.Measure.count
                * MeasureTheory.eLpNorm (Work.KMTAreas.A7.Tm ρ m₂ ψ g') 2 MeasureTheory.Measure.count)
        (u : ℕ) (Λ : NNReal) (hΛ : 1 < Λ) (a : ℕ → NNReal)
        (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n)
        (l₁ l₂ k₁ k₂ K : ℕ) (hB : B ≤ Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)
        (huL : (max l₁ l₂ : ℝ) ≤ (u : ℝ))
        (hu2 : (2 : ℝ) ^ (ρ * (max l₁ l₂ : ℝ)) ≤ (u : ℝ))
        (j₁ j₂ : ℤ) (hj₁ : j₁ ∈ ({-1, 0, 1} : Finset ℤ)) (hj₂ : j₂ ∈ ({-1, 0, 1} : Finset ℤ))
        (hk₁ : ¬ (k₁ = 0 ∧ j₁ = -1)) (hk₂ : ¬ (k₂ = 0 ∧ j₂ = -1))
        (t : ℝ) (ht : t ∈ Set.Icc (1 / 2 : ℝ) 1) (f g : ℤ → ℂ)
        (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count)
        (hg : MeasureTheory.MemLp g 2 MeasureTheory.Measure.count)
        (hsupF : ∀ n : ℕ, ∀ ξ : ℝ,
          Work.KMTPlan.A6.lowModSymbF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t n ξ ≠ 0 →
            |ξ| ≤ (2 : ℝ) ^ (-(3 * (u : ℤ))))
        (hsupG : ∀ n : ℕ, ∀ ξ : ℝ,
          Work.KMTPlan.A6.lowModSymbG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t n ξ ≠ 0 →
            |ξ| ≤ (2 : ℝ) ^ (-(3 * (P.natDegree : ℤ) * (u : ℤ))))
        (BF BG : ℝ)
        (hbF : ∀ (n : ℕ) (ξ : ℝ),
          ‖Work.KMTPlan.A6.lowModSymbF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t n ξ‖ ≤ BF)
        (hbG : ∀ (n : ℕ) (ξ : ℝ),
          ‖Work.KMTPlan.A6.lowModSymbG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t n ξ‖ ≤ BG),
        MeasureTheory.eLpNorm (fun x : ℤ => Work.Analysis.Variation.VrFull 2 K
            (fun n : ℕ => Work.KMTPlan.A6.BtwistEx ρ P l₁ l₂
              (Work.KMTAreas.A7.mStarF u) (Work.KMTAreas.A7.mStargF P.natDegree u)
              (Work.KMTAreas.A7.Tm ρ l₁ (Work.KMTPlan.A6.lowModSymbF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t n) f)
              (Work.KMTAreas.A7.Tm ρ l₂ (Work.KMTPlan.A6.lowModSymbG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t n) g) x))
          1 MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (C_RM * ((Nat.log2 K : ℝ) + 2) ^ (2 : ℝ)) *
              ((Cssu : ENNReal) * ENNReal.ofReal ((2 : ℝ) ^ (-(cS * (max (l₁ : ℝ) (l₂ : ℝ)))))
                * ((C Λ : ENNReal) * (C Λ : ENNReal))) *
              MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count *
              MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
  obtain ⟨C_RM, hC_RM, hgen⟩ := VrFull_TmBtwist_le_rand_uniform
  refine ⟨C_RM, hC_RM, ?_⟩
  intro C₀ hC₀ ρ hρ B C hRanF hRanG cS hcS Cssu hSS u Λ hΛ a ha ha1
    l₁ l₂ k₁ k₂ K hB huL hu2 j₁ j₂ hj₁ hj₂ hk₁ hk₂ t ht f g hf hg hsupF hsupG
    BF BG hbF hbG
  set Φ : ℕ → ℝ → ℂ := lowModSymbF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t with hΦdef
  set Ψ : ℕ → ℝ → ℂ := lowModSymbG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t with hΨdef
  set Xa : ENNReal :=
    (Cssu : ENNReal) * ENNReal.ofReal ((2 : ℝ) ^ (-(cS * (max (l₁ : ℝ) (l₂ : ℝ))))) with hXadef
  set Yb : ENNReal := (C Λ : ENNReal) * (C Λ) with hYbdef
  set F2 : ENNReal := MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count with hF2def
  set G2 : ENNReal := MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count with hG2def
  have hSSinst : ∀ (ε ε' : ℕ → ℂ), (∀ k, ‖ε k‖ ≤ 1) → (∀ k, ‖ε' k‖ ≤ 1) →
      MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTPlan.A6.BtwistEx ρ P l₁ l₂
        (Work.KMTAreas.A7.mStarF u) (Work.KMTAreas.A7.mStargF P.natDegree u)
        (Work.KMTAreas.A7.Tm ρ l₁ (Work.KMTAreas.A7.randSymb Φ ε K) f)
        (Work.KMTAreas.A7.Tm ρ l₂ (Work.KMTAreas.A7.randSymb Ψ ε' K) g) x)
        1 MeasureTheory.Measure.count ≤ Xa * Yb * F2 * G2 := by
    intro ε ε' hε hε'
    have hsF : ∀ ξ : ℝ, randSymb Φ ε K ξ ≠ 0 → |ξ| ≤ (2 : ℝ) ^ (-(3 * (u : ℤ))) := by
      intro ξ hξ
      obtain ⟨n, _hnK, hn⟩ := exists_ne_zero_of_randSymb_ne_zero hξ
      exact hsupF n ξ hn
    have hsG : ∀ ξ : ℝ, randSymb Ψ ε' K ξ ≠ 0 →
        |ξ| ≤ (2 : ℝ) ^ (-(3 * (P.natDegree : ℤ) * (u : ℤ))) := by
      intro ξ hξ
      obtain ⟨n, _hnK, hn⟩ := exists_ne_zero_of_randSymb_ne_zero hξ
      exact hsupG n ξ hn
    have hk₂' : k₂ ≠ 0 ∨ 0 ≤ j₂ := by
      by_cases hk : k₂ = 0
      · right
        rcases (by simpa using hj₂ : j₂ = -1 ∨ j₂ = 0 ∨ j₂ = 1) with h | h | h
        · exact absurd ⟨hk, h⟩ hk₂
        · omega
        · omega
      · exact Or.inl hk
    have hRc : (0 : ℝ) ≤ (2 : ℝ) ^ (-(3 * (u : ℤ))) := by positivity
    have hRcG : (0 : ℝ) ≤ (2 : ℝ) ^ (-(3 * (P.natDegree : ℤ) * (u : ℤ))) := by positivity
    have hMlpF : MeasureTheory.MemLp
        (Work.Analysis.IonescuWainger.periodize (Work.KMTAreas.A7.randSymb Φ ε K)) ⊤
        Work.Analysis.IonescuWainger.circleMeasure :=
      memLp_periodize_randSymb (R := (2 : ℝ) ^ (-(3 * (u : ℤ)))) (B := BF) hRc
        (fun n => by
          show Measurable (Work.KMTPlan.A6.lowModSymbF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t n)
          exact measurable_lowModSymbF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t n)
        (fun n ξ => by
          show Work.KMTPlan.A6.lowModSymbF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t n ξ ≠ 0 →
            |ξ| ≤ (2 : ℝ) ^ (-(3 * (u : ℤ)))
          exact hsupF n ξ)
        (fun n ξ => by
          show ‖Work.KMTPlan.A6.lowModSymbF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t n ξ‖ ≤ BF
          exact hbF n ξ)
        ε hε K
    have hMlpG : MeasureTheory.MemLp
        (Work.Analysis.IonescuWainger.periodize (Work.KMTAreas.A7.randSymb Ψ ε' K)) ⊤
        Work.Analysis.IonescuWainger.circleMeasure :=
      memLp_periodize_randSymb (R := (2 : ℝ) ^ (-(3 * (P.natDegree : ℤ) * (u : ℤ)))) (B := BG)
        hRcG
        (fun n => by
          show Measurable (Work.KMTPlan.A6.lowModSymbG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t n)
          exact measurable_lowModSymbG P ρ C₀ a l₁ l₂ k₁ k₂ j₂ t hk₂' ht n)
        (fun n ξ => by
          show Work.KMTPlan.A6.lowModSymbG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t n ξ ≠ 0 →
            |ξ| ≤ (2 : ℝ) ^ (-(3 * (P.natDegree : ℤ) * (u : ℤ)))
          exact hsupG n ξ)
        (fun n ξ => by
          show ‖Work.KMTPlan.A6.lowModSymbG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t n ξ‖ ≤ BG
          exact hbG n ξ)
        ε' hε' K
    have h1 := hSS l₁ l₂ u (randSymb Φ ε K) (randSymb Ψ ε' K) f g huL hu2 hf hg
      hMlpF hMlpG hsF hsG
    have h2 : MeasureTheory.eLpNorm (Tm ρ l₁ (randSymb Φ ε K) f) 2 MeasureTheory.Measure.count
        ≤ (C Λ : ENNReal) * F2 := by
      rw [hF2def]
      exact hRanF a Λ l₁ l₂ k₁ k₂ K t j₁ ε f hΛ ha ha1 hε ht hj₁ hk₁ hB hf
    have h3 : MeasureTheory.eLpNorm (Tm ρ l₂ (randSymb Ψ ε' K) g) 2 MeasureTheory.Measure.count
        ≤ (C Λ : ENNReal) * G2 := by
      rw [hG2def]
      exact hRanG a Λ l₁ l₂ k₁ k₂ K t j₂ ε' g hΛ ha ha1 hε' ht hj₂ hk₂ hB hg
    calc MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTPlan.A6.BtwistEx ρ P l₁ l₂
          (Work.KMTAreas.A7.mStarF u) (Work.KMTAreas.A7.mStargF P.natDegree u)
          (Work.KMTAreas.A7.Tm ρ l₁ (Work.KMTAreas.A7.randSymb Φ ε K) f)
          (Work.KMTAreas.A7.Tm ρ l₂ (Work.KMTAreas.A7.randSymb Ψ ε' K) g) x)
          1 MeasureTheory.Measure.count
        ≤ (Cssu : ENNReal) * ENNReal.ofReal ((2 : ℝ) ^ (-(cS * (max (l₁ : ℝ) (l₂ : ℝ)))))
            * MeasureTheory.eLpNorm (Tm ρ l₁ (randSymb Φ ε K) f)
                2 MeasureTheory.Measure.count
            * MeasureTheory.eLpNorm (Tm ρ l₂ (randSymb Ψ ε' K) g)
                2 MeasureTheory.Measure.count := h1
      _ ≤ (Cssu : ENNReal) * ENNReal.ofReal ((2 : ℝ) ^ (-(cS * (max (l₁ : ℝ) (l₂ : ℝ)))))
            * ((C Λ : ENNReal) * F2)
            * MeasureTheory.eLpNorm (Tm ρ l₂ (randSymb Ψ ε' K) g)
                2 MeasureTheory.Measure.count :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 zero_le) zero_le
      _ ≤ (Cssu : ENNReal) * ENNReal.ofReal ((2 : ℝ) ^ (-(cS * (max (l₁ : ℝ) (l₂ : ℝ)))))
            * ((C Λ : ENNReal) * F2) * ((C Λ : ENNReal) * G2) :=
          mul_le_mul_of_nonneg_left h3 zero_le
      _ = Xa * Yb * F2 * G2 := by rw [hXadef, hYbdef]; ac_rfl
  have hmain := hgen ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u) (cw_mStarF_summable u)
    (cw_mStargF_summable P.natDegree u) K Φ Ψ f g (Xa * Yb * F2 * G2)
    (by rw [hΦdef]; exact lowModSymbF_zero ρ C₀ a l₁ l₂ k₁ k₂ j₁ t)
    (by rw [hΨdef]; exact lowModSymbG_zero ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t)
    hf hg
    (by rw [hΦdef]; exact TmSide_lowModSymbF ρ C₀ a l₁ l₂ k₁ k₂ K j₁ t hj₁ hk₁ ht)
    (by rw [hΨdef]; exact TmSide_lowModSymbG ρ P C₀ a l₁ l₂ k₁ k₂ K j₂ t hj₂ hk₂ ht)
    (by rw [hΦdef]; exact tmBddLowModSymbF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t hj₁ hk₁ ht f hf)
    (by rw [hΨdef]; exact tmBddLowModSymbG P ρ C₀ a l₁ l₂ k₁ k₂ j₂ t hj₂ hk₂ ht g hg)
    hSSinst
  refine le_trans hmain ?_
  simp only [hXadef, hYbdef, hF2def, hG2def, mul_assoc, le_refl]

end

end Work.KMTPlan.A6.Linf
