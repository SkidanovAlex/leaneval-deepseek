import Mathlib
import Submission.Work.TMC13.fourier_amp

namespace Work.TMC13

/-- `vc t * vc (-2t) = conj (vc t)`, the factorisation behind the `t ↔ -t` Fourier
identity for `smul A (vc t)`. -/
theorem vc_mul_vc_neg_two (t : ℝ) :
    Work.TMComp.RotBasics.vc t * Work.TMComp.RotBasics.vc (-2 * t) =
      (starRingEnd ℂ) (Work.TMComp.RotBasics.vc t) := by
  rw [← Work.TMComp.RotBasics.vc_add t (-2 * t)]
  rw [show t + -2 * t = -t by ring, Work.TMComp.RotBasics.vc_neg]

/-- `c1 A ≠ 0` when `det A = 1` (the leading Fourier coefficient dominates). -/
theorem c1_ne_zero_of_det_one {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.det = 1) :
    c1 A ≠ 0 := by
  intro h
  have hd := fourier_amp_det A
  rw [hA] at hd
  rw [h] at hd
  simp at hd
  nlinarith [sq_nonneg (c2 A).re, sq_nonneg (c2 A).im]

/-- The factored form of the `t ↔ -t` Fourier identity for a real `2×2` matrix of
determinant `1`: the conjugate term `c2 A * conj (vc t)` can be written as
`c1 A * vc t * ((c2 A / c1 A) * vc (-2t))` because `vc t * vc (-2t) = conj (vc t)`
and `c1 A ≠ 0`. -/
theorem ref_fourier_factor {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.det = 1) (t : ℝ) :
    Work.TMComp.RotBasics.smul A (Work.TMComp.RotBasics.vc t) =
      Work.TMC13.c1 A * Work.TMComp.RotBasics.vc t *
        (1 + (Work.TMC13.c2 A / Work.TMC13.c1 A) * Work.TMComp.RotBasics.vc (-2 * t)) := by
  have hc1 : c1 A ≠ 0 := c1_ne_zero_of_det_one hA
  have hw := vc_mul_vc_neg_two t
  have h1 : c1 A * (1 + (c2 A / c1 A) * Work.TMComp.RotBasics.vc (-2 * t)) =
      c1 A + c2 A * Work.TMComp.RotBasics.vc (-2 * t) := by
    rw [mul_add, mul_one, ← mul_assoc, mul_div_cancel₀ (c2 A) hc1]
  rw [fourier_amp_smul A t, ← hw]
  calc c1 A * Work.TMComp.RotBasics.vc t +
        c2 A * (Work.TMComp.RotBasics.vc t * Work.TMComp.RotBasics.vc (-2 * t))
      = (c1 A * (1 + (c2 A / c1 A) * Work.TMComp.RotBasics.vc (-2 * t))) *
          Work.TMComp.RotBasics.vc t := by
        rw [h1]; ring
    _ = c1 A * Work.TMComp.RotBasics.vc t *
          (1 + (c2 A / c1 A) * Work.TMComp.RotBasics.vc (-2 * t)) := by ring

end Work.TMC13
