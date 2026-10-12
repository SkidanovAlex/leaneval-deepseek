import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseB7.FSParamsVals
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseK15

theorem ell_mul_KL_sqrt {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Work.BoseB7.Q3Env Mode) (h : Work.BoseB7.FSParamsView E) :
    E.ell * E.KL * Real.sqrt (E.mu * E.aScat) = E.Kl * E.KL := by
  -- `ℓ = K_ℓ(μa)^{-1/2}`, so `ℓ√(μa) = K_ℓ` provided `μa > 0`; multiply by `K_L`.
  have ha : 0 < E.aScat := h.a_pos
  have ha3 : 0 < E.aScat ^ 3 := by positivity
  have hmu : 0 < E.mu := by
    have hmm : E.mu = h.t / E.aScat ^ 3 := by
      rw [eq_div_iff (ne_of_gt ha3)]
      exact h.mu_eq
    rw [hmm]
    exact div_pos h.t_pos ha3
  have hmua : 0 < E.mu * E.aScat := mul_pos hmu ha
  have hsqrt : (E.mu * E.aScat) ^ (-(1 / 2 : ℝ)) * Real.sqrt (E.mu * E.aScat) = 1 := by
    rw [Real.rpow_neg hmua.le, ← Real.sqrt_eq_rpow]
    exact inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr hmua))
  have hell : E.ell * Real.sqrt (E.mu * E.aScat) = E.Kl := by
    rw [h.ell_eq, Work.BoseB7.side, mul_assoc, hsqrt, mul_one]
  calc E.ell * E.KL * Real.sqrt (E.mu * E.aScat)
      = E.KL * (E.ell * Real.sqrt (E.mu * E.aScat)) := by ring
    _ = E.KL * E.Kl := by rw [hell]
    _ = E.Kl * E.KL := by ring

end Work.BoseK15
