import Mathlib
import Submission.Work.RPB1a.Caratheodory.Brouwer.RetractDefs

namespace Work.RPB1a.Caratheodory.Brouwer

/-- `x ↦ rayT (H x) (x - H x)` is continuous whenever `H` is continuous and has no fixed point
(the latter makes the denominator `‖x - H x‖ ^ 2` of the closed form for `rayT` nonvanishing). -/
lemma continuous_rayT_comp {N : ℕ} (H : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (hH : Continuous H) (hne : ∀ x, H x ≠ x) :
    Continuous (fun x => rayT (H x) (x - H x)) := by
  have hnum : Continuous fun x =>
      -(inner ℝ (H x) (x - H x)) +
        Real.sqrt ((inner ℝ (H x) (x - H x)) ^ 2 + ‖x - H x‖ ^ 2 * (1 - ‖H x‖ ^ 2)) := by
    fun_prop
  have hden : Continuous fun x => ‖x - H x‖ ^ 2 := by fun_prop
  simp only [rayT]
  exact hnum.div hden (fun x => by
    have hx : x - H x ≠ 0 := sub_ne_zero.mpr (Ne.symm (hne x))
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))

end Work.RPB1a.Caratheodory.Brouwer
