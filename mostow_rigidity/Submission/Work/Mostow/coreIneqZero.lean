import Mathlib
import Submission.Work.Mostow.poAux
import Submission.Work.Mostow.StabHoroForm

/-!
# The BCG `coreIneq` at the `n = 0` / zero-shift point

With `s = (√(1-d²))⁻¹` and `q = p + d·w`, bilinearity of the Minkowski form `mform`
turns the left-hand side into `s²·(⟨q, Mq⟩)`, and the hypotheses give
`⟨q, Mq⟩ = -A + d²B`.  Since `s² = (1-d²)⁻¹` and `B ≤ 1 < A`, the claim reduces to
`B < A`, which holds strictly.
-/

namespace Work.Mostow

open Matrix

lemma coreIneqZero {n : ℕ} (M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ)
    (p w : Fin n ⊕ Fin 1 → ℝ) (A B : ℝ)
    (hpw : Work.Mostow.mform p w = 0) (hww : Work.Mostow.mform w w = 1)
    (hwp : Work.Mostow.mform w (M.mulVec p) = 0) (hpwM : Work.Mostow.mform p (M.mulVec w) = 0)
    (hAp : Work.Mostow.mform p (M.mulVec p) = -A) (hBw : Work.Mostow.mform w (M.mulVec w) = B)
    (hB : B ≤ 1) (hA : 1 < A)
    (d : ℝ) (hd : 0 < d) (hd1 : d < 1) :
    Work.Mostow.mform ((Real.sqrt (1 - d^2))⁻¹ • (p + d • w))
        (M.mulVec ((Real.sqrt (1 - d^2))⁻¹ • (p + d • w)))
      < Work.Mostow.mform p (M.mulVec p) := by
  have hd2 : 0 < d ^ 2 := by positivity
  have h1d2 : 0 < 1 - d ^ 2 := by nlinarith [hd, hd1, sq_nonneg (1 - d), sq_nonneg d]
  set s : ℝ := (Real.sqrt (1 - d ^ 2))⁻¹ with hs
  set q : Fin n ⊕ Fin 1 → ℝ := p + d • w with hq
  -- The quadratic value of `q`: `⟨p+d·w, M(p+d·w)⟩ = -A + d²B`.
  have hqval : mform q (M.mulVec q) = -A + d ^ 2 * B := by
    simp only [hq, Matrix.mulVec_add, Matrix.mulVec_smul, mform_add_left,
      mform_add_right, mform_smul_left, mform_smul_right, hAp, hpwM, hwp, hBw]
    ring
  have hsq : s ^ 2 = (1 - d ^ 2)⁻¹ := by
    rw [hs, inv_pow, Real.sq_sqrt (le_of_lt h1d2)]
  have hLHS : mform (s • q) (M.mulVec (s • q)) = s ^ 2 * (-A + d ^ 2 * B) := by
    rw [Matrix.mulVec_smul, mform_smul_left, mform_smul_right, hqval]
    ring
  rw [hLHS, hsq, inv_mul_lt_iff₀ h1d2]
  nlinarith [mul_lt_mul_of_pos_left (lt_of_le_of_lt hB hA) hd2]

end Work.Mostow
