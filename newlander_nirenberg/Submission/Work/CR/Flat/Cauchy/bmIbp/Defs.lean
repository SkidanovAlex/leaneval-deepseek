/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The regularised `(1,0)`-derivative of the Bochner–Martinelli kernel

This small file collects the definitions shared by the proof of
`Work.CR.Flat.Cauchy.bmDzKernel_ibp` (integration by parts for the flat `∂`-operator against
the Bochner–Martinelli kernel).

The singular kernel `bmDzKernel k j = ∂_{z_k}(bmKernel j)` is regularised by smoothing the
denominator: for `ε > 0`,

  `bmDzKerEps j k ε x = -n · \bar x_j · \bar x_k / (‖x‖² + ε²)^{n+1}`,

so that `bmDzKerEps j k ε = ∂_{z_j}(bmKerEps k ε)` (see
`Work.CR.Flat.Cauchy.bmIbp.dCoord_bmKerEps`) and `bmDzKerEps j k ε x → bmDzKernel j k x`
as `ε → 0⁺`.
-/
import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmSetup
import Submission.Work.CR.Flat.Cauchy.bmCZDefs

noncomputable section

open scoped NNReal ENNReal
open MeasureTheory Set

namespace Work.CR.Flat.Cauchy.bmIbp

open Work.CR.Flat.Cauchy

/-- The regularised `(1,0)`-derivative of the Bochner–Martinelli kernel:
`bmDzKerEps j k ε x = -n \bar x_j \bar x_k / (‖x‖² + ε²)^{n+1}`. -/
def bmDzKerEps {n : ℕ} (j k : Fin n) (ε : ℝ) (x : Fin n → ℂ) : ℂ :=
  -((n : ℂ)) * starRingEnd ℂ (x j) * starRingEnd ℂ (x k)
    / (((nrmSq x + ε ^ 2 : ℝ)) : ℂ) ^ (n + 1)

@[simp] lemma bmDzKerEps_apply {n : ℕ} (j k : Fin n) (ε : ℝ) (x : Fin n → ℂ) :
    bmDzKerEps j k ε x
      = -((n : ℂ)) * starRingEnd ℂ (x j) * starRingEnd ℂ (x k)
        / (((nrmSq x + ε ^ 2 : ℝ)) : ℂ) ^ (n + 1) := rfl

/-- `∂_{z_k}(bmKernel j)` in terms of the squared Euclidean norm. -/
lemma bmDzKernel_eq_nrmSq {n : ℕ} (j k : Fin n) (x : Fin n → ℂ) :
    bmDzKernel j k x = -((n : ℂ)) * starRingEnd ℂ (x j) * starRingEnd ℂ (x k)
      / (((nrmSq x : ℝ)) : ℂ) ^ (n + 1) := by
  have h2 : ((eucNorm x : ℂ)) ^ 2 = ((nrmSq x : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, nrmSq_eq_eucNorm_sq]
  have hpow : ((eucNorm x : ℂ)) ^ (2 * n + 2) = (((nrmSq x : ℝ)) : ℂ) ^ (n + 1) := by
    rw [show 2 * n + 2 = 2 * (n + 1) by ring, pow_mul, h2]
  rw [bmDzKernel, hpow]
  ring

@[simp] lemma bmDzKerEps_zero {n : ℕ} (j k : Fin n) (ε : ℝ) :
    bmDzKerEps j k ε (0 : Fin n → ℂ) = 0 := by
  simp [bmDzKerEps, nrmSq]

end Work.CR.Flat.Cauchy.bmIbp
