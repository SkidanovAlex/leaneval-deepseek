import Mathlib

namespace Work.Pert.pert2v2.HlimRow

theorem floor_rep_window (w : ℂ) :
    ((w - (((Int.floor w.re : ℤ)) : ℂ)).re : ℂ) + (w.im : ℂ) * Complex.I
        = w - (((Int.floor w.re : ℤ)) : ℂ)
    ∧ (w - (((Int.floor w.re : ℤ)) : ℂ)).re ∈ Set.Ico (0 : ℝ) 1
    ∧ (w - (((Int.floor w.re : ℤ)) : ℂ)).im = w.im := by
  refine ⟨?_, ?_, ?_⟩
  · -- `re + im * I = z` applied to `z = w - ⌊w.re⌋`
    have him : (w - (((Int.floor w.re : ℤ)) : ℂ)).im = w.im := by simp
    rw [← him]
    exact Complex.re_add_im _
  · -- the fractional part of the real part lies in `[0, 1)`
    rw [Set.mem_Ico, Complex.sub_re, Complex.intCast_re]
    constructor
    · linarith [Int.floor_le w.re]
    · linarith [Int.lt_floor_add_one w.re]
  · -- subtracting a real does not change the imaginary part
    simp

end Work.Pert.pert2v2.HlimRow
