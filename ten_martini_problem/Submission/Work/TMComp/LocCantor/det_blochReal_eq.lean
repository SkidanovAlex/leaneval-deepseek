import Mathlib
import Submission.Work.TMComp.LocCantor.Defs

/-!
# C17 (`P_LocCantor`) — the determinant of the real Bloch matrix

(AJ §5: the matrix `A = [Re W, Im W]` obtained from a Bloch wave `W` with columns the
Bloch wave and its complex conjugate.)

The complex matrix `blochMat α θ u x = [W, W̄]` and the real matrix
`blochReal α θ u x = [Re W, Im W]` are related by `[W, W̄] = [Re W, Im W] · [[1,1],[i,-i]]`,
so their determinants satisfy

  `det [W, W̄] = -2 i · det [Re W, Im W]`.

Consequently, if `det [W(x), W̄(x)] = c i` for *every* `x` and a nonzero real number `c`
(which is what `Work.TMComp.LocCantor.det_blochMat_const` produces: the determinant of the
Bloch matrix is a purely imaginary constant), then `det [Re W(x), Im W(x)]` is the *constant*
`d = -c/2 ≠ 0`, and `c = -2 d`.
-/

noncomputable section

open scoped ComplexConjugate

namespace Work.TMComp.LocCantor

/-- For complex numbers `z w`, `z * conj w - conj z * w = -2 i (z.re * w.im - z.im * w.re)`.

Indeed the left-hand side is `F - conj F` with `F = z * conj w`, and for any `F`,
`F - conj F = 2 i F.im`. -/
theorem blochDet_complex_aux (z w : ℂ) :
    z * (starRingEnd ℂ) w - (starRingEnd ℂ) z * w
      = -2 * Complex.I * (((z.re * w.im - z.im * w.re : ℝ)) : ℂ) := by
  have h : z * (starRingEnd ℂ) w - (starRingEnd ℂ) z * w
      = (z * (starRingEnd ℂ) w) - (starRingEnd ℂ) (z * (starRingEnd ℂ) w) := by
    rw [map_mul, Complex.conj_conj]
  rw [h, Complex.sub_conj, Complex.mul_im, Complex.conj_im, Complex.conj_re]
  push_cast
  ring

/-- `det [W, W̄] = -2 i · det [Re W, Im W]`. -/
theorem det_blochMat_eq_det_blochReal (α θ : ℝ) (u : ℤ → ℂ) (x : ℝ) :
    (Work.TMComp.blochMat α θ u x).det
      = -2 * Complex.I * (((Work.TMComp.blochReal α θ u x).det : ℝ) : ℂ) := by
  have h1 : (Work.TMComp.blochMat α θ u x).det
      = Work.TMComp.blochVec α θ u x 0 * (starRingEnd ℂ) (Work.TMComp.blochVec α θ u x 1)
        - (starRingEnd ℂ) (Work.TMComp.blochVec α θ u x 0)
            * Work.TMComp.blochVec α θ u x 1 := by
    rw [Matrix.det_fin_two]
    simp [Work.TMComp.blochMat]
  have h2 : (Work.TMComp.blochReal α θ u x).det
      = (Work.TMComp.blochVec α θ u x 0).re * (Work.TMComp.blochVec α θ u x 1).im
        - (Work.TMComp.blochVec α θ u x 0).im * (Work.TMComp.blochVec α θ u x 1).re := by
    rw [Matrix.det_fin_two]
    simp [Work.TMComp.blochReal]
  rw [h1, h2, blochDet_complex_aux]

/-- Cancel the factor `i` in `c i = -2 i d` for real `c`, `d`. -/
theorem ofReal_eq_ofReal_mul_I_cancel {c d : ℝ}
    (h : (c : ℂ) * Complex.I = -2 * Complex.I * (d : ℂ)) : c = -2 * d := by
  have h3 : (c : ℂ) * Complex.I = ((-2 * d : ℝ) : ℂ) * Complex.I := by
    rw [h]; push_cast; ring
  exact Complex.ofReal_injective (mul_right_cancel₀ Complex.I_ne_zero h3)

theorem det_blochReal_eq {α θ : ℝ} {u : ℤ → ℂ} {c : ℝ} (hc : c ≠ 0)
    (hdet : ∀ x, (Work.TMComp.blochMat α θ u x).det = (c : ℂ) * Complex.I) :
    ∃ d : ℝ, d ≠ 0 ∧ c = -2 * d ∧ ∀ x, (Work.TMComp.blochReal α θ u x).det = d := by
  -- `det [Re W, Im W]` is the constant `-c/2`
  have hconst : ∀ x, c = -2 * (Work.TMComp.blochReal α θ u x).det := by
    intro x
    refine ofReal_eq_ofReal_mul_I_cancel ?_
    exact (hdet x).symm.trans (det_blochMat_eq_det_blochReal α θ u x)
  refine ⟨-c / 2, ?_, ?_, fun x => ?_⟩
  · intro hzero
    exact hc (by linarith)
  · ring
  · have := hconst x
    linarith

end Work.TMComp.LocCantor
