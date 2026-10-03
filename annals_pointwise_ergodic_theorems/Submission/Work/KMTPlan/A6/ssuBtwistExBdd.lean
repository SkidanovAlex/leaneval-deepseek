import Mathlib
import Submission.Work.KMTPlan.A6.ssuMain

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier Work.KMTAreas.A7
open Submission.PointwiseErgodicTheorems

theorem ssuBtwistExBdd (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) (hI : Work.KMTContract.ImprovKMT P) :
    ∃ c : Real, 0 < c ∧ ∃ ρ₀ : Real, 0 < ρ₀ ∧ ∀ ρ : Real, 0 < ρ → ρ ≤ ρ₀ →
      ∃ C : NNReal, 0 < C ∧
      ∀ (l₁ l₂ u : ℕ) (φ ψ : Real → Complex) (f g : ℤ → Complex),
        (max l₁ l₂ : Real) ≤ (u : Real) →
        (2 : Real) ^ (ρ * (max l₁ l₂ : Real)) ≤ (u : Real) →
        MeasureTheory.MemLp f 2 MeasureTheory.Measure.count →
        MeasureTheory.MemLp g 2 MeasureTheory.Measure.count →
        MeasureTheory.MemLp (Work.Analysis.IonescuWainger.periodize φ) ⊤
          Work.Analysis.IonescuWainger.circleMeasure →
        MeasureTheory.MemLp (Work.Analysis.IonescuWainger.periodize ψ) ⊤
          Work.Analysis.IonescuWainger.circleMeasure →
        (∀ ξ : Real, φ ξ ≠ 0 → |ξ| ≤ (2 : Real) ^ (-(3 * (u : ℤ)))) →
        (∀ ξ : Real, ψ ξ ≠ 0 → |ξ| ≤ (2 : Real) ^ (-(3 * (P.natDegree : ℤ) * (u : ℤ)))) →
        MeasureTheory.eLpNorm (fun x : ℤ =>
            Work.KMTPlan.A6.BtwistEx ρ P l₁ l₂
              (Work.KMTAreas.A7.mStarF u)
              (Work.KMTAreas.A7.mStargF P.natDegree u)
              (Work.KMTAreas.A7.Tm ρ l₁ φ f)
              (Work.KMTAreas.A7.Tm ρ l₂ ψ g) x)
          1 MeasureTheory.Measure.count
        ≤ (C : ENNReal) * ENNReal.ofReal ((2 : Real) ^ (-(c * (max (l₁ : Real) (l₂ : Real)))))
            * MeasureTheory.eLpNorm (Work.KMTAreas.A7.Tm ρ l₁ φ f) 2 MeasureTheory.Measure.count
            * MeasureTheory.eLpNorm (Work.KMTAreas.A7.Tm ρ l₂ ψ g) 2 MeasureTheory.Measure.count := by
  obtain ⟨c₀, hc₀, hI'⟩ := hI
  refine ⟨c₀ / 2, ?_, 1, by norm_num, ?_⟩
  · linarith
  intro ρ hρ hρ1
  obtain ⟨CI₀, hCI₀⟩ := hI' ρ hρ hρ1
  have hIρ : ∀ (N l : ℕ) (f g : ℤ → ℂ), 1 ≤ N → MemLp f 2 Measure.count →
      MemLp g 2 Measure.count →
      (Work.KMTContract.kmtProj ρ l (-(Work.Analysis.EndVar.logN N) + (l : ℤ)) f = 0 ∨
        Work.KMTContract.kmtProj ρ l
          ((P.natDegree : ℤ) * (-(Work.Analysis.EndVar.logN N) + (l : ℤ))) g = 0) →
      eLpNorm (fun x : ℤ => AhalfR TZ (N : ℝ≥0) Polynomial.X P f g x) 1 Measure.count
        ≤ ENNReal.ofReal ((CI₀ : ℝ) * ((2 : ℝ) ^ (-(c₀ * (l : ℝ)))
            + (((Work.Analysis.EndVar.logN N : ℤ) : ℝ)) ^ (-(c₀ / ρ))))
          * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count := by
    intro N l f g hN hf hg hdj
    have h := hCI₀ N l f g hN hf hg hdj
    rw [ENNReal.coe_nnreal_eq] at h
    rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (CI₀ : ℝ))] at h
    exact h
  obtain ⟨Cm, hCmpos, L₀, hL₀1, hmain⟩ := ssuMainBound ρ hρ hρ1 P hd c₀ hc₀ (CI₀ : ℝ)
    (by positivity) hIρ
  obtain ⟨Cm', hCm'pos, hcrude⟩ := ssuCrudeUniform ρ P L₀
  have hCv : 0 < max Cm (Cm' * (2 : ℝ) ^ ((c₀ / 2) * (L₀ : ℝ))) := by
    have h : Cm ≤ max Cm (Cm' * (2 : ℝ) ^ ((c₀ / 2) * (L₀ : ℝ))) := le_max_left _ _
    linarith
  let Cv : ℝ := max Cm (Cm' * (2 : ℝ) ^ ((c₀ / 2) * (L₀ : ℝ)))
  have hCvpos : 0 < Cv := hCv
  let C : NNReal := ⟨Cv, hCvpos.le⟩
  have hCeq : (C : ENNReal) = ENNReal.ofReal (max Cm (Cm' * (2 : ℝ) ^ ((c₀ / 2) * (L₀ : ℝ)))) := by
    dsimp only [C, Cv]
    exact ENNReal.coe_nnreal_eq _
  refine ⟨C, ?_, ?_⟩
  · show (0 : NNReal) < C
    rw [← NNReal.coe_lt_coe]
    exact hCvpos
  intro l₁ l₂ u φ ψ f g hLu h2ρL hf hg hΦ hΨ hφ hψ
  by_cases hcase : max l₁ l₂ < L₀
  · have hcr := hcrude l₁ l₂ u (Tm ρ l₁ φ f) (Tm ρ l₂ ψ g) hcase
    refine hcr.trans ?_
    have hCm'le : ENNReal.ofReal Cm' ≤ (C : ENNReal)
        * ENNReal.ofReal ((2 : ℝ) ^ (-((c₀ / 2) * (max l₁ l₂ : ℝ)))) := by
      have hreal : Cm' ≤ (max Cm (Cm' * (2 : ℝ) ^ ((c₀ / 2) * (L₀ : ℝ))))
          * (2 : ℝ) ^ (-((c₀ / 2) * (max l₁ l₂ : ℝ))) := by
        have hLle : (max l₁ l₂ : ℝ) ≤ (L₀ : ℝ) := by exact_mod_cast le_of_lt hcase
        have hA : Cm' * (2 : ℝ) ^ ((c₀ / 2) * (L₀ : ℝ))
            ≤ max Cm (Cm' * (2 : ℝ) ^ ((c₀ / 2) * (L₀ : ℝ))) := le_max_right _ _
        have hB : (0 : ℝ) ≤ (2 : ℝ) ^ (-((c₀ / 2) * (max l₁ l₂ : ℝ))) :=
          Real.rpow_nonneg (by norm_num) _
        have hC1 : (1 : ℝ) ≤ (2 : ℝ) ^ ((c₀ / 2) * ((L₀ : ℝ) - (max l₁ l₂ : ℝ))) :=
          Real.one_le_rpow (by norm_num) (by nlinarith [hLle])
        have hD := mul_le_mul_of_nonneg_right hA hB
        have hE : Cm' * (2 : ℝ) ^ ((c₀ / 2) * (L₀ : ℝ))
              * (2 : ℝ) ^ (-((c₀ / 2) * (max l₁ l₂ : ℝ)))
            = Cm' * (2 : ℝ) ^ ((c₀ / 2) * ((L₀ : ℝ) - (max l₁ l₂ : ℝ))) := by
          rw [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          ring_nf
        nlinarith [hD, hC1, hCm'pos, hE]
      calc ENNReal.ofReal Cm'
          ≤ ENNReal.ofReal ((max Cm (Cm' * (2 : ℝ) ^ ((c₀ / 2) * (L₀ : ℝ))))
              * (2 : ℝ) ^ (-((c₀ / 2) * (max l₁ l₂ : ℝ)))) := ENNReal.ofReal_le_ofReal hreal
        _ = ENNReal.ofReal (max Cm (Cm' * (2 : ℝ) ^ ((c₀ / 2) * (L₀ : ℝ))))
              * ENNReal.ofReal ((2 : ℝ) ^ (-((c₀ / 2) * (max l₁ l₂ : ℝ)))) := by
            rw [ENNReal.ofReal_mul (by positivity)]
        _ = (C : ENNReal) * ENNReal.ofReal ((2 : ℝ) ^ (-((c₀ / 2) * (max l₁ l₂ : ℝ)))) := by
            rw [hCeq]
    gcongr
  · have hL : L₀ ≤ max l₁ l₂ := le_of_not_gt hcase
    have hmn := hmain l₁ l₂ u φ ψ f g hL hLu h2ρL hf hg hΦ hΨ hφ hψ
    refine hmn.trans ?_
    have hCge : ENNReal.ofReal Cm ≤ (C : ENNReal) := by
      rw [hCeq]
      exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
    gcongr
