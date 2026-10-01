import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Work.LinnikAreas.A5.F1_neg_lam

namespace Work.LinnikAreas.A5

/-- `(x S)(1/6 + A/S) = x (S/6 + A)` for `S ≠ 0`. -/
private lemma mul_div_add_sixth (x S A : ℝ) (hS : S ≠ 0) :
    x * S * (1/6 + A/S) = x * (S/6 + A) := by
  field_simp

/-- `e^{-x} sinh x = (1 - e^{-2x})/2`. -/
private lemma exp_neg_mul_sinh (x : ℝ) :
    Real.exp (-x) * Real.sinh x = (1 - Real.exp (-2*x))/2 := by
  rw [Real.sinh_eq]
  rw [show -2*x = -x + -x by ring, Real.exp_add, Real.exp_neg]
  field_simp

/-
Elementary arithmetic of the HB-13.3 test function, with
`c = (λ/2) e^{Kλ} / sinh(Kλ)` and `X = e^{Kλ}(K/2 − (1 − e^{−2Kλ})/(4λ))/sinh(Kλ)`
(note `X` is the value `(Ftil K lam (-λ)).re` computed in `F1_neg_lam`, and `F1_neg_lam` (ii)
gives `(2/λ) e^{−Kλ}(sinh(Kλ)/6 + e^{Kλ}(K/2 − (1−e^{−2Kλ})/(4λ))) = K² B(λ)`):

1. `c > 0`;
2. `c⁻¹ (1/6 + X) = K² B(λ)`   (this is the main term of HB Lemma 13.3);
3. `c⁻¹ ≤ 2K`   (from `1 − e^{−2Kλ} ≤ 2Kλ`, e.g. `Real.add_one_le_exp` at `−2Kλ`; this bounds
   both error terms by `2K · error`).
-/
theorem testfun_arith (K lam : ℝ) (hK : 0 < K) (hlam : 0 < lam) :
    0 < (lam / 2) * Real.exp (lam * K) / Real.sinh (K * lam) ∧
    ((lam / 2) * Real.exp (lam * K) / Real.sinh (K * lam))⁻¹ *
        (1 / 6 + Real.exp (K * lam) * (K / 2 - (1 - Real.exp (-2 * K * lam)) / (4 * lam)) /
          Real.sinh (K * lam))
      = K ^ 2 * Work.LinnikContract.Bfun K lam ∧
    ((lam / 2) * Real.exp (lam * K) / Real.sinh (K * lam))⁻¹ ≤ 2 * K := by
  have hKl : 0 < K * lam := mul_pos hK hlam
  have hsinh : 0 < Real.sinh (K * lam) := Real.sinh_pos_iff.mpr hKl
  have hsinhne : Real.sinh (K * lam) ≠ 0 := ne_of_gt hsinh
  have hEpos : 0 < Real.exp (K * lam) := Real.exp_pos _
  -- the reciprocal of the normalising factor `c`, in the shape `(2/λ) e^{-Kλ} sinh(Kλ)`
  have hcinv : ((lam / 2) * Real.exp (lam * K) / Real.sinh (K * lam))⁻¹
      = (2/lam) * Real.exp (-(K*lam)) * Real.sinh (K*lam) := by
    have hE : Real.exp (lam*K) = Real.exp (K*lam) := by rw [mul_comm]
    rw [hE, Real.exp_neg]
    field_simp
  refine ⟨?_, ?_, ?_⟩
  · -- (1) positivity of `c`
    rw [show Real.exp (lam*K) = Real.exp (K*lam) by rw [mul_comm]]
    exact div_pos (mul_pos (by linarith) hEpos) hsinh
  · -- (2) `c⁻¹ (1/6 + X) = K² B(λ)`, from `F1_neg_lam` (ii)
    rw [← (Work.LinnikAreas.A5.F1_neg_lam K lam hK hlam).2, hcinv]
    exact mul_div_add_sixth ((2/lam) * Real.exp (-(K*lam))) (Real.sinh (K*lam))
      (Real.exp (K*lam) * (K/2 - (1 - Real.exp (-2*K*lam))/(4*lam))) hsinhne
  · -- (3) `c⁻¹ = (1 - e^{-2Kλ})/λ ≤ 2K`
    have h3 : ((lam / 2) * Real.exp (lam * K) / Real.sinh (K * lam))⁻¹
        = (1 - Real.exp (-2*K*lam))/lam := by
      have hassoc : (2/lam) * Real.exp (-(K*lam)) * Real.sinh (K*lam)
          = (2/lam) * (Real.exp (-(K*lam)) * Real.sinh (K*lam)) := by ring
      rw [hcinv, hassoc, exp_neg_mul_sinh]
      rw [show (-2:ℝ) * (K*lam) = -2*K*lam by ring]
      field_simp
    rw [h3, div_le_iff₀ hlam]
    nlinarith [Real.add_one_le_exp (-2*K*lam)]

end Work.LinnikAreas.A5
