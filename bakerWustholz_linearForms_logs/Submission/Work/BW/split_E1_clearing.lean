import Mathlib
import Submission.Work.BW.split_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- One step of the `E1` clearing computation: the two displayed expressions agree because
`(D/(r·2^I))^m = D^m/(r^m·(2^I)^m)` and `r·D·(1/(2 log(2rd)) + 1/(r·D)) = r·D/(2 log(2rd)) + 1`. -/
theorem split_E1_clearing {r d h m : ℕ} (σ : Fin r → ℝ) (hr : (0:ℝ) < (r:ℝ))
    (hD : (0:ℝ) < pD r d σ) (hL : (0:ℝ) < Real.log (2*r*d)) :
    (((r+1).descFactorial (m+1) : ℕ) : ℝ) * ((h:ℝ) * ((r:ℝ)*pD r d σ/(2*Real.log (2*r*d)) + 1))
        * (pD r d σ / ((r:ℝ) * (2:ℝ)^(pI r d)))^m
      = ((((r+1).descFactorial (m+1) : ℕ) : ℝ) * ((m+1).factorial : ℝ) * (r:ℝ) / (r:ℝ)^m
          * (1/(2*Real.log (2*r*d)) + 1/((r:ℝ)*pD r d σ)))
        * ((h:ℝ) * (pD r d σ)^(m+1) / (((2:ℝ)^(pI r d))^m * ((m+1).factorial:ℝ))) := by
  have hpow : (pD r d σ / ((r:ℝ)*(2:ℝ)^(pI r d)))^m
      = (pD r d σ)^m / ((r:ℝ)^m * ((2:ℝ)^(pI r d))^m) := by
    rw [div_pow, mul_pow]
  rw [hpow]
  field_simp
  ring

end Work.BW
