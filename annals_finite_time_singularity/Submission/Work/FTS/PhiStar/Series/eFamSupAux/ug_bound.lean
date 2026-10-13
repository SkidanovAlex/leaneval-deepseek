import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Submission.Work.FTS.PhiStar.Series.eFamSupDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Series.eFamSupAux

open Work.FTS.PhiStar.Series (ug Npsi ene ene_le ene_eq Npsi_pos)

/-- `u(1) = 0`, so the endpoint case of `ug_bound` is trivial. -/
lemma ug_one (m : ℕ) : ug m 1 = 0 := by
  show (1 - (1 : ℝ) ^ 2) * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) 1 = 0
  ring

theorem ug_bound (m : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (Work.FTS.PhiStar.Series.ug m x) ^ 2 ≤ Work.FTS.PhiStar.Series.Npsi m * (1 - x ^ 2) := by
  have hx0 : 0 ≤ x := hx.1
  rcases lt_or_eq_of_le hx.2 with hlt | heq
  · have hx2 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx0, hlt]
    have hpos : 0 < 1 - x ^ 2 := by nlinarith [hx0, hlt]
    have hN : 0 < Npsi m := Npsi_pos m
    -- The radial energy `E = (u')^2 + N·u^2/(1-x^2)` is bounded by `E(1) = N^2`.
    have h := ene_le m hx
    rw [ene_eq m hx2] at h
    rw [show ug m x * ug m x = (ug m x) ^ 2 from (sq _).symm] at h
    have hd : 0 ≤ deriv (ug m) x * deriv (ug m) x := mul_self_nonneg _
    have h2 : (Npsi m / (1 - x ^ 2)) * (ug m x) ^ 2 ≤ Npsi m * Npsi m := by linarith
    have h2' : Npsi m * (ug m x) ^ 2 / (1 - x ^ 2) ≤ Npsi m * Npsi m := by
      have hdiv : (Npsi m / (1 - x ^ 2)) * (ug m x) ^ 2
          = Npsi m * (ug m x) ^ 2 / (1 - x ^ 2) := by ring
      rwa [hdiv] at h2
    have h3 : Npsi m * (ug m x) ^ 2 ≤ Npsi m * Npsi m * (1 - x ^ 2) :=
      (div_le_iff₀ hpos).mp h2'
    have h5 : (ug m x) ^ 2 * Npsi m ≤ (Npsi m * (1 - x ^ 2)) * Npsi m := by nlinarith
    exact le_of_mul_le_mul_right h5 hN
  · subst heq
    rw [ug_one m]
    norm_num

end Work.FTS.PhiStar.Series.eFamSupAux
