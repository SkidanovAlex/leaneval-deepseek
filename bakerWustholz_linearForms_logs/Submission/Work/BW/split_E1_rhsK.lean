import Mathlib
import Submission.Work.BW.split_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Pure algebraic core: the `E1` right-hand-side rewrite, with the two Kummer
powers `(2^I)^m` and `(ξ^K)^m` distributed and the inverse power pulled out. -/
private lemma split_E1_rhsK_aux (x a y : ℝ) (d h m I K : ℕ) (hx : x ≠ 0) :
    16*(d:ℝ)*(a*x)^(m+1) * ((2:ℝ)^I)^m * (x^K)^m
        * ((h:ℝ) * y^(m+1) / (((2:ℝ)^I)^m * ((m+1).factorial:ℝ)))
      = 16*(d:ℝ)*(h:ℝ)*(x^K)⁻¹*(a*x^(K+1)*y)^(m+1) / ((m+1).factorial:ℝ) := by
  simp only [mul_pow, ← pow_mul]
  have h2I : (2:ℝ)^(I*m) ≠ 0 := by positivity
  have hf : ((m+1).factorial:ℝ) ≠ 0 := by positivity
  have hxK : x^K ≠ 0 := pow_ne_zero _ hx
  field_simp
  rw [show (K+1)*(m+1) = (m+1) + (K*m + K) by ring, pow_add, pow_add]
  ring

theorem split_E1_rhsK {r d h m : ℕ} (σ : Fin r → ℝ) (hx : (0:ℝ) < pxi r) :
    16*(d:ℝ)*(5.5*(pxi r))^(m+1) * ((2:ℝ)^(pI r d))^m * ((pxi r)^(r*pI r d))^m
        * ((h:ℝ) * (pD r d σ)^(m+1) / (((2:ℝ)^(pI r d))^m * ((m+1).factorial:ℝ)))
      = 16*(d:ℝ)*(h:ℝ)*(pxi r)^(-((r*pI r d:ℕ):ℤ))*(5.5*(pxi r)^(r*pI r d+1)*pD r d σ)^(m+1) / ((m+1).factorial:ℝ) := by
  have hz : (pxi r)^(-((r*pI r d:ℕ):ℤ)) = ((pxi r)^(r*pI r d))⁻¹ := by
    rw [zpow_neg, zpow_natCast]
  rw [hz]
  exact split_E1_rhsK_aux (pxi r) 5.5 (pD r d σ) d h m (pI r d) (r*pI r d) (ne_of_gt hx)

end Work.BW
