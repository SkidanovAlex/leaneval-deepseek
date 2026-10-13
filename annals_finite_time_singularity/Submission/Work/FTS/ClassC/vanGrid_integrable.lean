import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.ClassC.VanishFamilyDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory

namespace Work.FTS.ClassC

/-- **Level-`0` honesty of an integrand.**  The integrand `F` has integrable angular slices on
`Iθ` for every `z ∈ Iz`, and its angular integral `z ↦ ∫_θ F z θ` is integrable on `Iz`.

For `F = fun z θ => Work.Spaces.HkIntegrand α 0 f z θ` this is exactly `Work.Spaces.HkMem α 0 f`,
and the hypothesis `hV` of `vanGrid_integrable` is exactly this statement for
`F = hVint α Ψ t l`.  The point of the abstraction is that this property is stable under finite
sums, which is what the integrability of the grid majorant `vanGrid` reduces to. -/
def Level0Integrable (F : ℝ → ℝ → ℝ) : Prop :=
  (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ => F z θ) Work.Spaces.Iθ) ∧
    MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, F z θ) Work.Spaces.Iz

/-- A finite sum of level-`0` honest integrands is level-`0` honest. -/
theorem Level0Integrable_sum {ι : Type*} (s : Finset ι) {F : ι → ℝ → ℝ → ℝ}
    (h : ∀ i ∈ s, Level0Integrable (F i)) :
    Level0Integrable (fun z θ => ∑ i ∈ s, F i z θ) := by
  refine ⟨fun z hz => ?_, ?_⟩
  · exact MeasureTheory.integrable_finsetSum (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ) s
      (fun i hi => (h i hi).1 z hz)
  · -- `z ↦ ∫_θ ∑_i F i z θ = ∑_i ∫_θ F i z θ` on `Iz`; the right-hand side is a finite sum of
    -- functions that are integrable on `Iz`.
    refine MeasureTheory.IntegrableOn.congr_fun
      (f := fun z => ∑ i ∈ s, ∫ θ in Work.Spaces.Iθ, F i z θ) ?_ ?_ measurableSet_Ici
    · exact MeasureTheory.integrable_finsetSum (μ := MeasureTheory.volume.restrict Work.Spaces.Iz) s
        (fun i hi => (h i hi).2)
    · intro z hz
      exact (MeasureTheory.integral_finsetSum s (fun i hi => (h i hi).1 z hz)).symm

/-- A sum of two level-`0` honest integrands is level-`0` honest. -/
theorem Level0Integrable_add {F G : ℝ → ℝ → ℝ} (hF : Level0Integrable F)
    (hG : Level0Integrable G) : Level0Integrable (fun z θ => F z θ + G z θ) := by
  refine ⟨fun z hz => ?_, ?_⟩
  · exact MeasureTheory.IntegrableOn.add (hF.1 z hz) (hG.1 z hz)
  · refine MeasureTheory.IntegrableOn.congr_fun
      (f := fun z => (∫ θ in Work.Spaces.Iθ, F z θ) + ∫ θ in Work.Spaces.Iθ, G z θ)
      ?_ ?_ measurableSet_Ici
    · exact MeasureTheory.IntegrableOn.add hF.2 hG.2
    · intro z hz
      exact (MeasureTheory.integral_add (hF.1 z hz) (hG.1 z hz)).symm

/-- The grid majorant `vanGrid` of the seven-slot honesty transfer is integrable: each of its
finitely many summands is integrable by hypothesis (`hσ` for the singular-weight family
`HkIntegrand α 0 (D_z^l ∂_θ^m Ψ)`, `l ≤ 9`, `m ≤ 2`, and `hV` for the vanishing-weight family
`hVint α Ψ t l`, `3 ≤ t ≤ 9`, `l ≤ 9`), and the property is stable under finite sums. -/
theorem vanGrid_integrable {α : ℝ} (hα : 0 < α) (hγ : Work.Spaces.gam α ≤ 3 / 2)
    {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (hσ : ∀ l m : ℕ, l ≤ 9 → m ≤ 2 →
      Work.Spaces.HkMem α 0 (Work.Spaces.DzIter l (Work.Spaces.pthIter m Ψ)))
    (hV : ∀ t l : ℕ, 3 ≤ t → t ≤ 9 → l ≤ 9 →
      (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ =>
          (Work.Spaces.DzIter l (Work.Spaces.pthIter t Ψ) z θ * Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (t : ℝ) - 4 - Work.Spaces.gam α)) Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.DzIter l (Work.Spaces.pthIter t Ψ) z θ * Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (t : ℝ) - 4 - Work.Spaces.gam α)) Work.Spaces.Iz)
    : (∀ z ∈ Work.Spaces.Iz,
        MeasureTheory.IntegrableOn (fun θ => Work.FTS.ClassC.vanGrid α Ψ z θ) Work.Spaces.Iθ)
      ∧ MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
          Work.FTS.ClassC.vanGrid α Ψ z θ) Work.Spaces.Iz := by
  -- First conjunct of the grid: the singular-weight family, `l ≤ 9`, `m ≤ 2`.
  have hA : Level0Integrable (fun z θ => ∑ l ∈ Finset.range 10, ∑ m ∈ Finset.range 3,
      Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter l (Work.Spaces.pthIter m Ψ)) z θ) := by
    refine Level0Integrable_sum _ fun l hl => Level0Integrable_sum _ fun m hm => ?_
    exact hσ l m (by have := Finset.mem_range.mp hl; omega)
      (by have := Finset.mem_range.mp hm; omega)
  -- Second conjunct of the grid: the vanishing-weight family, `3 ≤ t ≤ 9`, `l ≤ 9`.
  have hB : Level0Integrable (fun z θ => ∑ t ∈ Finset.Icc 3 9, ∑ l ∈ Finset.range 10,
      hVint α Ψ t l z θ) := by
    refine Level0Integrable_sum _ fun t ht => Level0Integrable_sum _ fun l hl => ?_
    have ht' := Finset.mem_Icc.mp ht
    have hl' : l ≤ 9 := by have := Finset.mem_range.mp hl; omega
    exact hV t l ht'.1 ht'.2 hl'
  -- `vanGrid` unfolds definitionally to the sum of the two families.
  exact Level0Integrable_add hA hB

end Work.FTS.ClassC
