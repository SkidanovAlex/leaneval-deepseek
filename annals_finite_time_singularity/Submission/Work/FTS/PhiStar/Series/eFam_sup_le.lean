import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.PhiStar.Series.eFamSupAux.ug_bound
import Submission.Work.Spaces.ThetaAgmon.agmon_interval
import Submission.Work.Spaces.sq_mul_div_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Series

set_option autoImplicit false

open Work.FTS.PhiStar.Gegenbauer (eFam gC)

/-- `|ug m (sin θ)| ≤ √(Npsi m)·cos θ` for `θ ∈ [0, π/2]`: the radial bound
`(ug m x)² ≤ Npsi m (1-x²)` at `x = sin θ`, with `1 - sin²θ = cos²θ`. -/
lemma abs_ug_sin_le (m : ℕ) (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    |ug m (Real.sin θ)| ≤ Real.sqrt (Npsi m) * Real.cos θ := by
  have hs0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [Real.pi_pos, hθ.2]⟩
  have hs1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have hcos : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Real.pi_pos, hθ.1]) hθ.2
  have hb := eFamSupAux.ug_bound m ⟨hs0, hs1⟩
  have hsq : 1 - (Real.sin θ) ^ 2 = (Real.cos θ) ^ 2 := by
    have h := Real.sin_sq_add_cos_sq θ
    linarith
  rw [hsq] at hb
  have h1 : |ug m (Real.sin θ)| ≤ Real.sqrt (Npsi m * (Real.cos θ) ^ 2) :=
    abs_le_sqrt_of_sq_le hb
  rwa [Real.sqrt_mul (le_of_lt (Npsi_pos m)), Real.sqrt_sq hcos] at h1

/-- **Uniform sup bound for the family `eFam`.**  For every `m` and every `θ ∈ Iθ`,

  `|eFam m θ| ≤ √(Npsi m)`,   `Npsi m = (2m+2)(2m+3)`.

This is the sharp `O(m)` shape: `√(Npsi m) ≤ 3(m+1)`, and it holds on the *closed* interval
`Iθ` (`eFam m θ = ug m (sin θ)/cos θ` and `|ug m (sin θ)| ≤ √N·cos θ`). -/
lemma abs_eFam_le_sqrt_Npsi (m : ℕ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |eFam m θ| ≤ Real.sqrt (Npsi m) := by
  have hI := hθ
  rw [Work.Spaces.Iθ] at hI
  obtain ⟨h0, h1⟩ := hI
  rcases eq_or_lt_of_le h1 with h1' | h1'
  · subst h1'
    have hz : eFam m (Real.pi / 2) = 0 := by
      rw [eFam, Real.cos_pi_div_two, zero_mul]
    rw [hz, abs_zero]
    exact Real.sqrt_nonneg _
  · have hcos : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, h0], h1'⟩
    have hcne : Real.cos θ ≠ 0 := ne_of_gt hcos
    have hb := abs_ug_sin_le m θ ⟨h0, le_of_lt h1'⟩
    have hsq : 1 - (Real.sin θ) ^ 2 = (Real.cos θ) ^ 2 := by
      have h := Real.sin_sq_add_cos_sq θ
      linarith
    have he : eFam m θ = ug m (Real.sin θ) / Real.cos θ := by
      show Real.cos θ * gC (2 * m + 1) (Real.sin θ) = ug m (Real.sin θ) / Real.cos θ
      rw [show ug m (Real.sin θ)
          = (1 - (Real.sin θ) ^ 2) * gC (2 * m + 1) (Real.sin θ) from rfl, hsq]
      field_simp
    rw [he, abs_div, abs_of_pos hcos, div_le_iff₀ hcos]
    exact hb

/-- `√(Npsi m) ≤ 3(m+1)`. -/
lemma sqrt_Npsi_le_three (m : ℕ) : Real.sqrt (Npsi m) ≤ 3 * ((m : ℝ) + 1) := by
  have h3 : Npsi m ≤ (3 * ((m : ℝ) + 1)) ^ 2 := by
    rw [Npsi]
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    nlinarith
  calc Real.sqrt (Npsi m) ≤ Real.sqrt ((3 * ((m : ℝ) + 1)) ^ 2) := Real.sqrt_le_sqrt h3
    _ = 3 * ((m : ℝ) + 1) := Real.sqrt_sq (by positivity)

theorem eFam_sup_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ C * ((m : ℝ) + 1) := by
  refine ⟨3, by norm_num, fun m θ hθ => ?_⟩
  exact le_trans (abs_eFam_le_sqrt_Npsi m hθ) (sqrt_Npsi_le_three m)

end Work.FTS.PhiStar.Series
