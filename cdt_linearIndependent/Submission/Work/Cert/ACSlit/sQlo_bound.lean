import Mathlib
import Submission.Work.Cert.ACSlit.Shadow

namespace Work.Cert.ACSlit

/-- Lower bound for `|Q(c)|` on the input disc: `sQlo > 0` says
`qL − sQ.r − ⌈ρ·sQpD/S⌉ − 1 > 0`, i.e. the announced lower bound `(qL − sQ.r)/S` for `‖q‖`
dominates the linear perturbation `(ρ/S)·(‖q'‖ + (ρ/S)·2(1+r)²)` of the slit derivative.

Chain: `(ρ/S)·(sQpD/S) = (ρ·sQpD/S)/S ≤ mu(ρ,sQpD)/S < (qL − sQ.r)/S ≤ ‖q‖`, the middle strict
inequality being `sQlo > 0`. -/
lemma sQlo_bound (A B2 E C1 G8 A2 ror roi : ℤ) (st : Work.Cert.St) (w : Work.Cert.SlitW)
    {r : ℝ} {q q' : ℂ}
    (hrho : 0 ≤ (st.rho : ℝ))
    (hlo : 0 < Work.Cert.ACSlit.sQlo A B2 E C1 G8 A2 ror roi st w)
    (hq : (((w.qL - (Work.Cert.ACSlit.sQ A B2 E C1 G8 A2 ror roi st w).r : ℤ)) : ℝ)
        / (Work.Cert.S : ℝ) ≤ ‖q‖)
    (hqpD : ‖q'‖ + ((st.rho : ℝ) / (Work.Cert.S : ℝ)) * (2 * (1 + r) ^ 2)
        ≤ (((Work.Cert.ACSlit.sQpD A B2 E C1 G8 A2 ror roi st w : ℤ)) : ℝ) / (Work.Cert.S : ℝ)) :
    ((st.rho : ℝ) / (Work.Cert.S : ℝ)) * (‖q'‖ + ((st.rho : ℝ) / (Work.Cert.S : ℝ))
        * (2 * (1 + r) ^ 2)) < ‖q‖ := by
  have hS : (0 : ℝ) < (Work.Cert.S : ℝ) := Work.Cert.ACBall.S_posR
  -- `sQlo > 0`, cast to `ℝ`
  have hloZ : (0 : ℤ) < w.qL - (sQ A B2 E C1 G8 A2 ror roi st w).r
      - mu st.rho (sQpD A B2 E C1 G8 A2 ror roi st w) - 1 := by
    simpa only [sQlo] using hlo
  have hloR : (0 : ℝ) < (w.qL : ℝ) - ((sQ A B2 E C1 G8 A2 ror roi st w).r : ℝ)
      - ((mu st.rho (sQpD A B2 E C1 G8 A2 ror roi st w) : ℤ) : ℝ) - 1 := by
    exact_mod_cast hloZ
  -- the hypothesis on `q`, cast to `ℝ`
  have hqR : ((w.qL : ℝ) - ((sQ A B2 E C1 G8 A2 ror roi st w).r : ℝ))
      / (Work.Cert.S : ℝ) ≤ ‖q‖ := by
    have := hq
    push_cast at this
    linarith
  -- `ρ·sQpD/S ≤ mu(ρ, sQpD)`, divided by `S`
  have hmu := Work.Cert.ACBall.mu_ge st.rho (sQpD A B2 E C1 G8 A2 ror roi st w)
  have h1 : ((st.rho : ℝ) / (Work.Cert.S : ℝ))
        * ((((sQpD A B2 E C1 G8 A2 ror roi st w) : ℤ) : ℝ) / (Work.Cert.S : ℝ))
      ≤ (((mu st.rho (sQpD A B2 E C1 G8 A2 ror roi st w) : ℤ) : ℝ)) / (Work.Cert.S : ℝ) := by
    have h2 := div_le_div_of_nonneg_right hmu hS.le
    rw [show ((st.rho : ℝ) * ((sQpD A B2 E C1 G8 A2 ror roi st w : ℤ) : ℝ)
            / (Work.Cert.S : ℝ)) / (Work.Cert.S : ℝ)
          = ((st.rho : ℝ) / (Work.Cert.S : ℝ))
            * ((((sQpD A B2 E C1 G8 A2 ror roi st w) : ℤ) : ℝ) / (Work.Cert.S : ℝ)) from by ring] at h2
    exact h2
  -- the strict inequality coming from `sQlo > 0`
  have h2 : (((mu st.rho (sQpD A B2 E C1 G8 A2 ror roi st w) : ℤ) : ℝ)) / (Work.Cert.S : ℝ)
      < ((w.qL : ℝ) - ((sQ A B2 E C1 G8 A2 ror roi st w).r : ℝ)) / (Work.Cert.S : ℝ) := by
    rw [div_lt_div_iff_of_pos_right hS]
    linarith
  have hrhoD : 0 ≤ (st.rho : ℝ) / (Work.Cert.S : ℝ) := div_nonneg hrho hS.le
  calc ((st.rho : ℝ) / (Work.Cert.S : ℝ))
        * (‖q'‖ + ((st.rho : ℝ) / (Work.Cert.S : ℝ)) * (2 * (1 + r) ^ 2))
      ≤ ((st.rho : ℝ) / (Work.Cert.S : ℝ))
        * ((((sQpD A B2 E C1 G8 A2 ror roi st w) : ℤ) : ℝ) / (Work.Cert.S : ℝ)) :=
        mul_le_mul_of_nonneg_left hqpD hrhoD
    _ ≤ (((mu st.rho (sQpD A B2 E C1 G8 A2 ror roi st w) : ℤ) : ℝ)) / (Work.Cert.S : ℝ) := h1
    _ < ((w.qL : ℝ) - ((sQ A B2 E C1 G8 A2 ror roi st w).r : ℝ)) / (Work.Cert.S : ℝ) := h2
    _ ≤ ‖q‖ := hqR

end Work.Cert.ACSlit
