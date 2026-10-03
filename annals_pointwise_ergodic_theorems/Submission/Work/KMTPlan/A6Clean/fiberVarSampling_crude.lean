import Mathlib
import Submission.Work.KMTAreas.A7.fiberOpVarNonFareyBounded
import Submission.Work.KMTAreas.A7.eLpNorm_residueLp_le

namespace Work.KMTPlan.A6Clean

theorem fiberVarSampling_crude (r : NNReal) (hr : 2 < r) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) (B : ℝ → ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (l₁ l₂ k₁ k₂ : ℕ),
        max (max l₁ l₂) (max k₁ k₂) ≤ B ρ →
        ∀ (u : ℕ → ℤ → ℂ),
          MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7.residueLp p.toReal
              (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
              (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r
                (fun n : ℕ => Work.KMTAreas.A7.fiberOp ρ l₁
                  (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ
                    (max (max l₁ l₂) (max k₁ k₂)))) n₀ (u n) y)) x) p
            MeasureTheory.Measure.count
          ≤ ENNReal.ofReal C *
              MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
                (fun n : ℕ => u n x)) p MeasureTheory.Measure.count := by
  -- The whole content is the *per-residue* (non-Farey) fibre bound `fiberOpVarNonFareyBounded`,
  -- applied uniformly in the residue `n₀`, together with the exact residue aggregation
  -- `A7.eLpNorm_residueLp_le` (the `ℓᵖ`-norm of the residue average is the residue average of the
  -- `ℓᵖ`-norms, with exponent matching, so the passage to the residue average costs nothing).
  obtain ⟨C, hCpos, hC⟩ :=
    Work.KMTAreas.A7.fiberOpVarNonFareyBounded r hr ρ hρ hρ1 p hp hptop B
  refine ⟨C, hCpos, ?_⟩
  intro l₁ l₂ k₁ k₂ hL u
  have hp0 : p ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp)
  have hpt : p ≠ ⊤ := ne_of_lt hptop
  have hpR : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  have hof : ENNReal.ofReal p.toReal = p := ENNReal.ofReal_toReal hpt
  -- Work with the exponent `ENNReal.ofReal p.toReal = p`, which is the form in which the residue
  -- aggregation is stated.
  have main : MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7.residueLp p.toReal
        (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
        (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7.fiberOp ρ l₁
            (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ
              (max (max l₁ l₂) (max k₁ k₂)))) n₀ (u n) y)) x)
      (ENNReal.ofReal p.toReal) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm (fun x : ℤ =>
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => u n x))
          (ENNReal.ofReal p.toReal) MeasureTheory.Measure.count := by
    refine Work.KMTAreas.A7.eLpNorm_residueLp_le (p := p.toReal) hpR
      (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7.fiberOp ρ l₁
            (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ
              (max (max l₁ l₂) (max k₁ k₂)))) n₀ (u n) y))
      (ENNReal.ofReal C * MeasureTheory.eLpNorm (fun x : ℤ =>
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => u n x))
          (ENNReal.ofReal p.toReal) MeasureTheory.Measure.count) ?_
    intro n₀ _hn₀
    simpa only [hof] using hC l₁ l₂ k₁ k₂ hL n₀ u
  simpa only [hof] using main

end Work.KMTPlan.A6Clean
