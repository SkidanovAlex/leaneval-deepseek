import Mathlib

namespace Work.EKLC6Core

theorem measurable_birkhoffAverage {X : Type*} [MeasurableSpace X] (T : X → X) (g : X → ℝ)
    (hT : Measurable T) (hg : Measurable g) (n : ℕ) :
    Measurable (birkhoffAverage ℝ T g n) := by
  rw [show birkhoffAverage ℝ T g n = fun x => (n : ℝ)⁻¹ • birkhoffSum T g n x from rfl]
  exact (Finset.measurable_sum _ (fun k _ => hg.comp (hT.iterate k))).const_smul (n : ℝ)⁻¹

end Work.EKLC6Core
