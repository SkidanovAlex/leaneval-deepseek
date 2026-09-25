import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Function.Floor
import Submission.Commons.NumberTheory.Mertens.mertens_lower

namespace Commons.NumberTheory.Mertens

theorem logDiv_measurable : Measurable Commons.NumberTheory.Mertens.logDiv := by
  let f : ℕ → ℝ := fun n => ∑ p ∈ n.primesLE, Real.log (p : ℝ) / (p : ℝ)
  have hf : Measurable f := measurable_of_countable f
  have hc : Measurable (f ∘ (Nat.floor : ℝ → ℕ)) := hf.comp Nat.measurable_floor
  convert hc using 1
  ext x
  rfl

end Commons.NumberTheory.Mertens
