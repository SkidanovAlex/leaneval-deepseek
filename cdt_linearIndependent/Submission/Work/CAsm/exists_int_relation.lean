import Mathlib

namespace Work.CAsm

/-- Clearing denominators for a rational linear relation among `1, lm, ln, lm * ln` whose
coefficient of `lm * ln` is nonzero: such a relation can be rescaled to an integer relation
with nonzero coefficient on `lm * ln`. -/
theorem exists_int_relation {lm ln : ℝ} (p q r s : ℚ) (hs : s ≠ 0)
    (h : (p : ℝ) + (q : ℝ) * lm + (r : ℝ) * ln + (s : ℝ) * (lm * ln) = 0) :
    ∃ A B C E : ℤ, E ≠ 0 ∧ (A : ℝ) + (B : ℝ) * lm + (C : ℝ) * ln + (E : ℝ) * (lm * ln) = 0 := by
  refine ⟨p.num * q.den * r.den * s.den, q.num * p.den * r.den * s.den,
          r.num * p.den * q.den * s.den, s.num * p.den * q.den * r.den, ?_, ?_⟩
  · have hsnum : s.num ≠ 0 := Rat.num_ne_zero.mpr hs
    have hp : (p.den : ℤ) ≠ 0 := by exact_mod_cast p.den_nz
    have hq : (q.den : ℤ) ≠ 0 := by exact_mod_cast q.den_nz
    have hr : (r.den : ℤ) ≠ 0 := by exact_mod_cast r.den_nz
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hsnum hp) hq) hr
  · have key : (↑(p.num * ↑q.den * ↑r.den * ↑s.den) + ↑(q.num * ↑p.den * ↑r.den * ↑s.den) * lm +
          ↑(r.num * ↑p.den * ↑q.den * ↑s.den) * ln +
        ↑(s.num * ↑p.den * ↑q.den * ↑r.den) * (lm * ln))
        = (p.den:ℝ)*(q.den:ℝ)*(r.den:ℝ)*(s.den:ℝ) * ((p:ℝ) + (q:ℝ)*lm + (r:ℝ)*ln + (s:ℝ)*(lm*ln)) := by
        simp only [Rat.cast_def]; push_cast; field_simp
    rw [key, h, mul_zero]

end Work.CAsm
