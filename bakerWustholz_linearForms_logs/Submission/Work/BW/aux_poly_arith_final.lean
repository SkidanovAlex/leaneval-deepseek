import Mathlib
import Submission.Work.BW.Defs
import Submission.Work.BW.auxpolydefs
import Submission.Work.BW.aux_poly_arith_core
import Submission.Work.BW.aux_poly_arith_ball

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 4000000

/-! # BW (12): the final arithmetic, with room for the discriminant slack

`aux_poly_arith_ball` bounds the Siegel right-hand side by `0.85·S·D`, but its proof only
establishes `13.5·r·d·h·D = 0.84375·S·D` (via `aux_poly_arith_core`, `13.4`, plus
`log_four_mul_Mu_le`, `0.1`).  The `aux_poly` assembly needs a little of that slack: the
discriminant term is bounded by `discr_term_le_tiny` with an *additive* error `0.001·S·D`, so the
arithmetic input must hold with `0.849·S·D` on the right.  Since `13.5 ≤ 0.849·16 = 13.584` this is
free; we re-run `aux_poly_arith_ball`'s final bookkeeping with the tighter constant. -/

namespace Work.BW

theorem aux_poly_arith_final {K : Type*} [Field K] [NumberField K] {r : ℕ} (hr : 2 ≤ r)
    (h : ℕ) (hh : 19 ≤ h) (σ : Fin r → ℝ) (hσ : ∀ j, 1 / (Module.finrank ℚ K : ℝ) ≤ σ j) :
    let d : ℝ := Module.finrank ℚ K
    let D : ℝ := pD r (Module.finrank ℚ K) σ
    let S : ℕ := pS r (Module.finrank ℚ K) h
    let D0 : ℕ := pD0 r (Module.finrank ℚ K) σ
    let Dj : Fin r → ℕ := pDj r (Module.finrank ℚ K) σ
    let Mu : ℕ := h * (D0 + 1) * ∏ j, (Dj j + 1)
    let Me : ℕ := Fintype.card (AuxEqnIdx r S (pT r (Module.finrank ℚ K) σ))
    let rho : ℝ := (Me : ℝ) / ((Mu : ℝ) - Me)
    (1 / 2) * d * rho * Real.log (Mu : ℝ) + d ^ 2 * ((∑ j, σ j) + (1 / 2) * r * Real.log 2)
      + d * rho * (1.7 * (h : ℝ) * (11.75 * r * D)
          + (D / d) * ((S : ℝ) * (S + 1) / (2 * (S : ℝ) + 1)))
      + d * Real.log (4 * d * (Mu : ℝ))
      ≤ 0.849 * (S : ℝ) * D := by
  dsimp only
  have hcore := aux_poly_arith_core (K := K) hr h hh σ hσ
  dsimp only at hcore
  have hT4 := log_four_mul_Mu_le (K := K) hr h hh σ hσ
  dsimp only at hT4
  have hS : (pS r (Module.finrank ℚ K) h : ℝ) = 16 * (r:ℝ) * (Module.finrank ℚ K : ℝ) * (h:ℝ) := by
    simp only [pS]; push_cast; ring
  have hgoal : 0.849 * (pS r (Module.finrank ℚ K) h : ℝ) * pD r (Module.finrank ℚ K) σ
      = 13.584 * (r:ℝ) * (Module.finrank ℚ K : ℝ) * (h:ℝ) * pD r (Module.finrank ℚ K) σ := by
    rw [hS]; ring
  rw [hgoal]
  have hR : (0:ℝ) ≤ (r:ℝ) * (Module.finrank ℚ K : ℝ) * (h:ℝ) * pD r (Module.finrank ℚ K) σ := by
    have hdn : 1 ≤ Module.finrank ℚ K := by
      have := Module.finrank_pos (R := ℚ) (M := K); omega
    have hDpos : 0 < pD r (Module.finrank ℚ K) σ := pD_pos hr hdn σ hσ
    have hr2 : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
    have hh19 : (19:ℝ) ≤ (h:ℝ) := by exact_mod_cast hh
    have hd1 : (1:ℝ) ≤ (Module.finrank ℚ K : ℝ) := by exact_mod_cast hdn
    have h1 : (0:ℝ) ≤ (r:ℝ) * (Module.finrank ℚ K : ℝ) := by positivity
    have h2 : (0:ℝ) ≤ (h:ℝ) := by linarith
    positivity
  linarith [hcore, hT4, hR]

end Work.BW
