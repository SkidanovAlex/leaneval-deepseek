import Mathlib
import Submission.Work.BMF.adi_descent

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Polynomial Finset

/-- Dilation of the polynomial peeled off in one descent step. -/
theorem dil_peel (a : ℝ) (P τ : ℝ[X]) (c μ : ℝ) (j : ℕ) :
    dil a (P - C c * τ - C μ * X ^ j) =
      dil a P - C c * dil a τ - C μ * (C (a ^ j) * X ^ j) := by
  rw [dil_sub, dil_sub, dil_C_mul, dil_C_mul, dil_X_pow]

/-- The top coefficient identity driving one descent step:
`μ_j (a^j - b^j) = coeff_j G`, because `coeff_j (dil a P - dil b P) = (a^j - b^j) coeff_j P`. -/
theorem muval_mul_qj (p : ADIPar) (s : DSt) (hp : ADIHyp p) (hj : 1 ≤ s.j) :
    muval p s * ((p.a : ℝ) ^ s.j - (p.b : ℝ) ^ s.j) = s.G.coeff s.j := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hba, -⟩ := hp
  rw [muval, qj_cast p.a p.b s.j (le_of_lt hba)]
  have hne : ((p.a : ℝ) ^ s.j - (p.b : ℝ) ^ s.j) ≠ 0 := by
    have hpos : 0 < qj p.a p.b s.j := qj_pos p.a p.b s.j hba (by omega)
    have hcast : (0 : ℝ) < ((qj p.a p.b s.j : ℕ) : ℝ) := by exact_mod_cast hpos
    rw [qj_cast p.a p.b s.j (le_of_lt hba)] at hcast
    exact ne_of_gt hcast
  exact div_mul_cancel₀ _ hne

theorem step_relation (p : ADIPar) (s : DSt) (hp : ADIHyp p) (hs : DInv p s) (hj : 1 ≤ s.j) :
    dil (p.a : ℝ) (dstep p s).P - dil (p.b : ℝ) (dstep p s).P =
      (dstep p s).E + (dstep p s).G := by
  obtain ⟨-, -, -, -, hdil, -⟩ := hs
  have hkey := muval_mul_qj p s hp hj
  have hmuX : C (muval p s) *
        (C ((p.a : ℝ) ^ s.j) * X ^ s.j - C ((p.b : ℝ) ^ s.j) * X ^ s.j) =
      C (s.G.coeff s.j) * X ^ s.j := by
    have h2 : (C ((p.a : ℝ) ^ s.j) : ℝ[X]) * X ^ s.j - C ((p.b : ℝ) ^ s.j) * X ^ s.j =
        (C ((p.a : ℝ) ^ s.j) - C ((p.b : ℝ) ^ s.j)) * X ^ s.j := by ring
    have h3 : (C (muval p s) : ℝ[X]) * (C ((p.a : ℝ) ^ s.j) - C ((p.b : ℝ) ^ s.j)) =
        C (s.G.coeff s.j) := by
      rw [← C_sub, ← C_mul, hkey]
    rw [h2, ← mul_assoc, h3]
  have hPa : dil (p.a : ℝ) (dstep p s).P =
      dil (p.a : ℝ) s.P - C (Tval p s / (2 * Real.pi)) * dil (p.a : ℝ) (Tay s.j p.x) -
        C (muval p s) * (C ((p.a : ℝ) ^ s.j) * X ^ s.j) := by
    rw [dstep_P]
    exact dil_peel (p.a : ℝ) s.P (Tay s.j p.x) (Tval p s / (2 * Real.pi)) (muval p s) s.j
  have hPb : dil (p.b : ℝ) (dstep p s).P =
      dil (p.b : ℝ) s.P - C (Tval p s / (2 * Real.pi)) * dil (p.b : ℝ) (Tay s.j p.x) -
        C (muval p s) * (C ((p.b : ℝ) ^ s.j) * X ^ s.j) := by
    rw [dstep_P]
    exact dil_peel (p.b : ℝ) s.P (Tay s.j p.x) (Tval p s / (2 * Real.pi)) (muval p s) s.j
  rw [hPa, hPb, dstep_E, dstep_G]
  linear_combination hdil - hmuX

end Work.BMF
