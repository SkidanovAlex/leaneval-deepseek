import Mathlib
import Submission.Work.Cert.ACSlit.Shadow

namespace Work.Cert.ACSlit

/-- The upper mantissa `sQpD = qpU + (sQp).r + ⌈ρA2/S⌉ + 1` of `S·sup|Q'|` on the disc of radius
`ρ/S` dominates `‖q'‖ + (ρ/S)·2(1+r)²` whenever `‖q'‖ ≤ (qpU + (sQp).r)/S` and `A2 = S·2(1+r)²`.

Indeed, writing `P = qpU + (sQp).r` (a lower bound of `S·|Q'(c)|` modulo the ball radius) and
`M = ⌈ρA2/S⌉`, we have `mu_ge`: `ρ·2(1+r)² = ρA2/S ≤ M`, so
`(P + M + 1)/S = P/S + (M + 1)/S ≥ ‖q'‖ + (ρ/S)·2(1+r)²`; the `+1` is pure slack, and no sign
hypothesis on `st.rho` is needed. -/
lemma sQpD_bound (A B2 E C1 G8 A2 ror roi : ℤ) (st : Work.Cert.St) (w : Work.Cert.SlitW)
    {r : ℝ} {q' : ℂ}
    (hA2 : (A2 : ℝ) = (Work.Cert.S : ℝ) * (2 * (1 + r) ^ 2))
    (hqp : ‖q'‖ ≤ (((w.qpU + (Work.Cert.ACSlit.sQp A B2 E C1 G8 A2 ror roi st w).r : ℤ)) : ℝ)
        / (Work.Cert.S : ℝ)) :
    ‖q'‖ + ((st.rho : ℝ) / (Work.Cert.S : ℝ)) * (2 * (1 + r) ^ 2)
      ≤ (((Work.Cert.ACSlit.sQpD A B2 E C1 G8 A2 ror roi st w : ℤ)) : ℝ) / (Work.Cert.S : ℝ) := by
  have hSR : (0 : ℝ) < (Work.Cert.S : ℝ) := Work.Cert.ACBall.S_posR
  have hSne : (Work.Cert.S : ℝ) ≠ 0 := ne_of_gt hSR
  -- the `mu` rounding of `ρ·A2/S`
  have hmu : (st.rho : ℝ) * (2 * (1 + r) ^ 2) ≤ ((Work.Cert.mu st.rho A2 : ℤ) : ℝ) := by
    have h1 : (st.rho : ℝ) * (A2 : ℝ) / (Work.Cert.S : ℝ)
        = (st.rho : ℝ) * (2 * (1 + r) ^ 2) := by
      rw [hA2]; field_simp
    linarith [Work.Cert.ACBall.mu_ge st.rho A2]
  -- push the `ℤ → ℝ` cast through the sum in the hypothesis
  have hqp' : ‖q'‖ ≤ ((w.qpU : ℝ)
        + ((Work.Cert.ACSlit.sQp A B2 E C1 G8 A2 ror roi st w).r : ℝ))
      / (Work.Cert.S : ℝ) := by
    push_cast at hqp; exact hqp
  -- unfold `sQpD` and split the quotient
  have hdef : Work.Cert.ACSlit.sQpD A B2 E C1 G8 A2 ror roi st w
      = w.qpU + (Work.Cert.ACSlit.sQp A B2 E C1 G8 A2 ror roi st w).r
        + Work.Cert.mu st.rho A2 + 1 := rfl
  rw [hdef]
  push_cast
  have hkey : ((w.qpU : ℝ) + ((Work.Cert.ACSlit.sQp A B2 E C1 G8 A2 ror roi st w).r : ℝ)
        + ((Work.Cert.mu st.rho A2 : ℤ) : ℝ) + 1) / (Work.Cert.S : ℝ)
      = ((w.qpU : ℝ) + ((Work.Cert.ACSlit.sQp A B2 E C1 G8 A2 ror roi st w).r : ℝ))
          / (Work.Cert.S : ℝ)
        + ((((Work.Cert.mu st.rho A2 : ℤ) : ℝ) + 1) / (Work.Cert.S : ℝ)) := by ring
  rw [hkey]
  have hnum : ((st.rho : ℝ) / (Work.Cert.S : ℝ)) * (2 * (1 + r) ^ 2)
      ≤ ((((Work.Cert.mu st.rho A2 : ℤ) : ℝ) + 1) / (Work.Cert.S : ℝ)) := by
    rw [show ((st.rho : ℝ) / (Work.Cert.S : ℝ)) * (2 * (1 + r) ^ 2)
        = ((st.rho : ℝ) * (2 * (1 + r) ^ 2)) / (Work.Cert.S : ℝ) by ring]
    exact div_le_div_of_nonneg_right (by linarith [hmu]) hSR.le
  linarith [hqp', hnum]

end Work.Cert.ACSlit
