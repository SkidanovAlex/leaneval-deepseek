import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Honesty.VanGridK
import Submission.Work.FTS.ClassC.vanGrid_integrable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

theorem vanGridK_integrable {α : ℝ} {K : ℕ} {Ψ : ℝ → ℝ → ℝ}
    (hσ : ∀ l m : ℕ, l ≤ K + 2 → m ≤ 2 →
      Work.Spaces.HkMem α 0 (Work.Spaces.DzIter l (Work.Spaces.pthIter m Ψ)))
    (hV : ∀ t l : ℕ, 3 ≤ t → t ≤ K + 2 → l ≤ K + 2 →
      (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ =>
          (Work.Spaces.DzIter l (Work.Spaces.pthIter t Ψ) z θ * Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (t : ℝ) - 4 - Work.Spaces.gam α)) Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.DzIter l (Work.Spaces.pthIter t Ψ) z θ * Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (t : ℝ) - 4 - Work.Spaces.gam α)) Work.Spaces.Iz) :
    (∀ z ∈ Work.Spaces.Iz,
        MeasureTheory.IntegrableOn (fun θ => Work.FTS.PhiStar.Honesty.vanGridK α Ψ K z θ)
          Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
          Work.FTS.PhiStar.Honesty.vanGridK α Ψ K z θ) Work.Spaces.Iz := by
  -- The grid majorant is the sum of two finite families of level-`0` honest integrands.
  have hA : Work.FTS.ClassC.Level0Integrable (fun z θ =>
      ∑ l ∈ Finset.range (K + 3), ∑ m ∈ Finset.range 3,
        Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter l (Work.Spaces.pthIter m Ψ)) z θ) := by
    refine Work.FTS.ClassC.Level0Integrable_sum _ fun l hl =>
      Work.FTS.ClassC.Level0Integrable_sum _ fun m hm => ?_
    exact hσ l m (by have := Finset.mem_range.mp hl; omega)
      (by have := Finset.mem_range.mp hm; omega)
  have hB : Work.FTS.ClassC.Level0Integrable (fun z θ =>
      ∑ t ∈ Finset.Icc 3 (K + 2), ∑ l ∈ Finset.range (K + 3),
        Work.FTS.ClassC.hVint α Ψ t l z θ) := by
    refine Work.FTS.ClassC.Level0Integrable_sum _ fun t ht =>
      Work.FTS.ClassC.Level0Integrable_sum _ fun l hl => ?_
    have ht' := Finset.mem_Icc.mp ht
    have hl' : l ≤ K + 2 := by have := Finset.mem_range.mp hl; omega
    exact hV t l ht'.1 ht'.2 hl'
  -- `vanGridK` unfolds definitionally to the sum of the two families.
  exact Work.FTS.ClassC.Level0Integrable_add hA hB

end Work.FTS.PhiStar.Honesty
