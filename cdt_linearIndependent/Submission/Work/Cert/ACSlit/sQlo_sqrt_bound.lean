import Mathlib
import Submission.Work.Cert.ACSlit.Shadow

namespace Work.Cert.ACSlit

open Work.Cert Work.Cert.ACBall

/-- **Numerical core of the explict (`M2e`) branch, `sqrt`/`sL` form.**

Given the witness inequalities `0 < w.sL`, `w.sL² ≤ sQlo·S` and the lower bound
`(qL − sQ.r)/S ≤ ‖q‖` on the analytic value `q`, the mantissa `sL` is a valid lower
bound for `S·√(|q| − (ρ/S)·(sQpD/S))` up to the scale `S`, i.e.

`sL/S ≤ √(‖q‖ − (ρ/S)·(sQpD/S))`.

The only rounding input is the ceiling property `mu_ge` of `Work.Cert.mu`
(`ρ·q pD/S ≤ mu ρ q pD` as integers), which is exactly the `−mu ρ q pD − 1` slack in
`Work.Cert.ACSlit.sQlo`. -/
lemma sQlo_sqrt_bound (A B2 E C1 G8 A2 ror roi : ℤ) (st : Work.Cert.St) (w : Work.Cert.SlitW)
    {r : ℝ} {q : ℂ}
    (hlo : 0 < Work.Cert.ACSlit.sQlo A B2 E C1 G8 A2 ror roi st w)
    (hsL0 : 0 < w.sL)
    (hsL2 : w.sL * w.sL ≤ Work.Cert.ACSlit.sQlo A B2 E C1 G8 A2 ror roi st w * Work.Cert.S)
    (hq : (((w.qL - (Work.Cert.ACSlit.sQ A B2 E C1 G8 A2 ror roi st w).r : ℤ)) : ℝ)
        / (Work.Cert.S : ℝ) ≤ ‖q‖) :
    (w.sL : ℝ) / (Work.Cert.S : ℝ) ≤ Real.sqrt (‖q‖
      - ((st.rho : ℝ) / (Work.Cert.S : ℝ))
        * ((((Work.Cert.ACSlit.sQpD A B2 E C1 G8 A2 ror roi st w : ℤ)) : ℝ) / (Work.Cert.S : ℝ))) := by
  have hSR : (0:ℝ) < (Work.Cert.S : ℝ) := Work.Cert.ACBall.S_posR
  -- step A : `(sL/S)² ≤ sQlo/S`, from `sL² ≤ sQlo·S`
  have hsL2R : (w.sL : ℝ) * (w.sL : ℝ)
      ≤ ((Work.Cert.ACSlit.sQlo A B2 E C1 G8 A2 ror roi st w : ℤ) : ℝ) * (Work.Cert.S : ℝ) := by
    exact_mod_cast hsL2
  have hA : ((w.sL : ℝ) / (Work.Cert.S : ℝ)) ^ 2
      ≤ ((Work.Cert.ACSlit.sQlo A B2 E C1 G8 A2 ror roi st w : ℤ) : ℝ) / (Work.Cert.S : ℝ) := by
    rw [div_pow]
    simp only [pow_two]
    calc (w.sL : ℝ) * (w.sL : ℝ) / ((Work.Cert.S : ℝ) * (Work.Cert.S : ℝ))
        ≤ (((Work.Cert.ACSlit.sQlo A B2 E C1 G8 A2 ror roi st w : ℤ) : ℝ) * (Work.Cert.S : ℝ))
            / ((Work.Cert.S : ℝ) * (Work.Cert.S : ℝ)) :=
          div_le_div_of_nonneg_right hsL2R (by positivity)
      _ = ((Work.Cert.ACSlit.sQlo A B2 E C1 G8 A2 ror roi st w : ℤ) : ℝ) / (Work.Cert.S : ℝ) := by
          field_simp
  -- step B : `sQlo/S ≤ ‖q‖ − (ρ/S)·(sQpD/S)`
  have hmu := Work.Cert.ACBall.mu_ge st.rho (Work.Cert.ACSlit.sQpD A B2 E C1 G8 A2 ror roi st w)
  have hmu' : ((st.rho : ℝ) / (Work.Cert.S : ℝ))
        * (((Work.Cert.ACSlit.sQpD A B2 E C1 G8 A2 ror roi st w : ℤ) : ℝ) / (Work.Cert.S : ℝ))
      ≤ (((Work.Cert.mu st.rho (Work.Cert.ACSlit.sQpD A B2 E C1 G8 A2 ror roi st w) : ℤ)) : ℝ)
        / (Work.Cert.S : ℝ) := by
    have h2 := div_le_div_of_nonneg_right hmu (le_of_lt hSR)
    have heq : (((st.rho : ℝ) * (((Work.Cert.ACSlit.sQpD A B2 E C1 G8 A2 ror roi st w : ℤ) : ℝ))
          / (Work.Cert.S : ℝ)) / (Work.Cert.S : ℝ))
        = ((st.rho : ℝ) / (Work.Cert.S : ℝ))
          * (((Work.Cert.ACSlit.sQpD A B2 E C1 G8 A2 ror roi st w : ℤ) : ℝ) / (Work.Cert.S : ℝ)) := by
      ring
    rwa [heq] at h2
  have hsQlo_eq : ((Work.Cert.ACSlit.sQlo A B2 E C1 G8 A2 ror roi st w : ℤ) : ℝ) / (Work.Cert.S : ℝ)
      = (((w.qL - (Work.Cert.ACSlit.sQ A B2 E C1 G8 A2 ror roi st w).r : ℤ)) : ℝ) / (Work.Cert.S : ℝ)
        - (((Work.Cert.mu st.rho (Work.Cert.ACSlit.sQpD A B2 E C1 G8 A2 ror roi st w) : ℤ)) : ℝ)
            / (Work.Cert.S : ℝ)
        - 1 / (Work.Cert.S : ℝ) := by
    simp only [Work.Cert.ACSlit.sQlo]
    push_cast
    ring
  have hX : ((w.sL : ℝ) / (Work.Cert.S : ℝ)) ^ 2 ≤ ‖q‖
      - ((st.rho : ℝ) / (Work.Cert.S : ℝ))
        * (((Work.Cert.ACSlit.sQpD A B2 E C1 G8 A2 ror roi st w : ℤ) : ℝ) / (Work.Cert.S : ℝ)) := by
    rw [hsQlo_eq] at hA
    have h1S : (0:ℝ) ≤ 1/(Work.Cert.S:ℝ) := by positivity
    linarith [hA, hq, hmu', h1S]
  exact Real.le_sqrt_of_sq_le hX

end Work.Cert.ACSlit
