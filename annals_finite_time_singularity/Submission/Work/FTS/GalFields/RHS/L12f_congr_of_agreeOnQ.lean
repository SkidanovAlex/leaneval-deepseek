import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Construction.Defs
import Submission.Work.Coercivity.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter

namespace Work.FTS.GalFields.RHS

/-- On the angular interval `Iθ = [0, π/2]` the open interval `(0, π/2)` is of full
measure: the two excluded points are singletons. -/
lemma ae_mem_Ioo_of_mem_Iθ_gal :
    ∀ᵐ θ ∂(volume : Measure ℝ), θ ∈ Work.Spaces.Iθ → 0 < θ ∧ θ < Real.pi / 2 := by
  have hne : (volume : Measure ℝ) ({0, Real.pi / 2} : Set ℝ) = 0 := by
    have hf : ({0, Real.pi / 2} : Set ℝ).Finite :=
      (Set.finite_singleton (Real.pi / 2)).insert 0
    exact hf.measure_zero volume
  have hset : {θ : ℝ | ¬ (θ ∉ ({0, Real.pi / 2} : Set ℝ))} = ({0, Real.pi / 2} : Set ℝ) := by
    ext θ
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, not_not]
  have hmem : ∀ᵐ θ ∂(volume : Measure ℝ), θ ∉ ({0, Real.pi / 2} : Set ℝ) := by
    rw [MeasureTheory.ae_iff, hset]
    exact hne
  filter_upwards [hmem] with θ hθ hθI
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hθ
  simp only [Work.Spaces.Iθ, Set.mem_Icc] at hθI
  exact ⟨lt_of_le_of_ne hθI.1 (fun hh => hθ.1 hh.symm), lt_of_le_of_ne hθI.2 hθ.2⟩

/-- `L₁₂` sees a profile only through its values on the open quadrant `z > 0`,
`0 < θ < π/2`; consequently `L12f` depends only on those values. -/
theorem L12f_congr_of_agreeOnQ {a b : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 ≤ z)
    (h : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → a z θ = b z θ) :
    Work.Coercivity.L12f a z = Work.Coercivity.L12f b z := by
  have hinner : ∀ s ∈ Set.Ioi z,
      Work.FM.L12dens Work.Spaces.K a s = Work.FM.L12dens Work.Spaces.K b s := by
    intro s hs
    have hs0 : 0 < s := lt_of_le_of_lt hz hs
    simp only [Work.FM.L12dens]
    refine MeasureTheory.setIntegral_congr_ae measurableSet_Icc ?_
    filter_upwards [ae_mem_Ioo_of_mem_Iθ_gal] with θ hθ hθI
    obtain ⟨h1, h2⟩ := hθ hθI
    rw [h s θ hs0 h1 h2]
  simp only [Work.Coercivity.L12f, Work.FM.L12]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hinner

end Work.FTS.GalFields.RHS
