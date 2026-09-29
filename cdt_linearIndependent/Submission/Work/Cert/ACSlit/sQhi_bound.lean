import Mathlib
import Submission.Work.Cert.ACSlit.Shadow

namespace Work.Cert.ACSlit

open Work.Cert Work.Cert.ACBall

/-- The mantissa `S·sup|Q|` on the input disc, `sQhi = qU + rad Q + ⌈ρ·sQpD/S⌉ + 1`, dominates
`S‖q‖ + ρ·sQpD/S` whenever `S‖q‖ ≤ qU + rad Q`.  (Pure rounding arithmetic: the only input about
the extrema is `hq`; the factor `ρ·sQpD/S` is absorbed by the `⌈ρ·sQpD/S⌉ + 1` slack of `sQhi`.) -/
lemma sQhi_bound (A B2 E C1 G8 A2 ror roi : ℤ) (st : Work.Cert.St) (w : Work.Cert.SlitW)
    {r : ℝ} {q : ℂ}
    (hq : ‖q‖ ≤ (((w.qU + (Work.Cert.ACSlit.sQ A B2 E C1 G8 A2 ror roi st w).r : ℤ)) : ℝ)
        / (Work.Cert.S : ℝ)) :
    ‖q‖ + ((st.rho : ℝ) / (Work.Cert.S : ℝ))
        * (((Work.Cert.ACSlit.sQpD A B2 E C1 G8 A2 ror roi st w : ℤ)) : ℝ) / (Work.Cert.S : ℝ)
      ≤ (((Work.Cert.ACSlit.sQhi A B2 E C1 G8 A2 ror roi st w : ℤ)) : ℝ) / (Work.Cert.S : ℝ) := by
  have hS : (0 : ℝ) < (S : ℝ) := by exact_mod_cast (S_pos : (0 : ℤ) < S)
  have hmu := mu_ge st.rho (sQpD A B2 E C1 G8 A2 ror roi st w)
  rw [sQhi]
  have hstep : ((st.rho : ℝ) / (S : ℝ))
        * (((sQpD A B2 E C1 G8 A2 ror roi st w : ℤ)) : ℝ) / (S : ℝ)
      ≤ ((mu st.rho (sQpD A B2 E C1 G8 A2 ror roi st w) : ℤ) : ℝ) / (S : ℝ) + 1 / (S : ℝ) := by
    have h1 : ((st.rho : ℝ) / (S : ℝ)) * (((sQpD A B2 E C1 G8 A2 ror roi st w : ℤ)) : ℝ)
        / (S : ℝ)
        = ((st.rho : ℝ) * (((sQpD A B2 E C1 G8 A2 ror roi st w : ℤ)) : ℝ) / (S : ℝ))
          / (S : ℝ) := by
      ring
    rw [h1]
    calc ((st.rho : ℝ) * (((sQpD A B2 E C1 G8 A2 ror roi st w : ℤ)) : ℝ) / (S : ℝ)) / (S : ℝ)
        ≤ (((mu st.rho (sQpD A B2 E C1 G8 A2 ror roi st w) : ℤ) : ℝ) + 1) / (S : ℝ) :=
          div_le_div_of_nonneg_right (by linarith) hS.le
      _ = ((mu st.rho (sQpD A B2 E C1 G8 A2 ror roi st w) : ℤ) : ℝ) / (S : ℝ)
            + 1 / (S : ℝ) := by
          ring
  calc ‖q‖ + ((st.rho : ℝ) / (S : ℝ))
        * (((sQpD A B2 E C1 G8 A2 ror roi st w : ℤ)) : ℝ) / (S : ℝ)
      ≤ (((w.qU + (sQ A B2 E C1 G8 A2 ror roi st w).r : ℤ)) : ℝ) / (S : ℝ)
        + (((mu st.rho (sQpD A B2 E C1 G8 A2 ror roi st w) : ℤ) : ℝ) / (S : ℝ)
            + 1 / (S : ℝ)) :=
        add_le_add hq hstep
    _ = (((w.qU + (sQ A B2 E C1 G8 A2 ror roi st w).r
          + mu st.rho (sQpD A B2 E C1 G8 A2 ror roi st w) + 1 : ℤ)) : ℝ) / (S : ℝ) := by
        push_cast; ring

end Work.Cert.ACSlit
