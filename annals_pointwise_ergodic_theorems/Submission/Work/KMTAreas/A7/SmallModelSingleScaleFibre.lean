/-
# The §7 single-scale estimate `ssu`, assembled

The wrapper of `Work.KMTAreas.A7.smallModelSingleScale_of_fibre_core`: it supplies the two §4
*linear* bounds for the randomised cutoffs (`randSymb_Tm_f_lp` for the `f`-side and
`randSymb_Tm_g_lp` for the `g`-side) to the core assembly, producing the paper's single-scale
model estimate (`ssu`, arXiv:2008.00857 §8) in the gain-free form consumed by
`Work.KMTAreas.A7.SmallModelVar`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.SmallModelSingleScaleFibreCore
import Submission.Work.KMTAreas.A7.randSymb_Tm_f_lp
import Submission.Work.KMTAreas.A7.randSymb_Tm_g_lp

namespace Work.KMTAreas.A7

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators

noncomputable section

/-- **The §7 single-scale estimate (`ssu`), gain-free form**, assembled from the two §4 linear
bounds and the Ionescu--Wainger fibre bounds `fiberOpCum_lp_goodArcs` / `fiberOpD_lp_crude`. -/
theorem smallModelSingleScale_of_fibre (P : Polynomial ℤ) (p₁ p₂ : ENNReal)
    (hdeg : 2 ≤ P.natDegree) (hA1 : Work.KMTContract.AreaA1) (hp₁ : 1 < p₁) (htp₁ : p₁ < ⊤)
    (hp₂ : 1 < p₂) (htp₂ : p₂ < ⊤) (hsum : p₁⁻¹ + p₂⁻¹ ≤ 1) :
    ∀ (C₀ : ℕ), 1 ≤ C₀ → ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ C : NNReal → NNReal,
        ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ K : ℕ) (t : ℝ) (ε ε' : ℕ → ℂ)
          (f g : ℤ → ℂ),
          1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
          (∀ n, ‖ε n‖ ≤ 1) → (∀ n, ‖ε' n‖ ≤ 1) → t ∈ Set.Icc ((1:ℝ)/2) 1 →
          MeasureTheory.eLpNorm (fun x : ℤ =>
              smallBtwist ρ P l₁ l₂
                (mStarF (uScale ρ (smallL l₁ l₂ k₁ k₂)))
                (mStargF P.natDegree (uScale ρ (smallL l₁ l₂ k₁ k₂)))
                (Tm ρ l₁ (randSymb (smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t) ε K) f)
                (Tm ρ l₂ (randSymb (smallSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t) ε' K) g) x)
            (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
          ≤ (C Λ : ENNReal) *
              ENNReal.ofReal ((1 + lmaxR l₁ l₂ k₁ k₂) ^ A *
                (2 : ℝ) ^ (A * ρ * lmaxR l₁ l₂ k₁ k₂)) *
              MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
              MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count :=
  smallModelSingleScale_of_fibre_core P p₁ p₂ hdeg hA1 hp₁ htp₁ hp₂ htp₂ hsum
    (randSymb_Tm_f_lp P p₁ p₂ hdeg hA1 hp₁ htp₁ hp₂ htp₂ hsum)
    (randSymb_Tm_g_lp P p₁ p₂ hdeg hA1 hp₁ htp₁ hp₂ htp₂ hsum)

end

end Work.KMTAreas.A7
