import Mathlib
import Submission.Work.Mostow.BCGDefs
import Submission.Work.Mostow.BaryBase

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

/-- On the sphere the Poisson kernel `pfun n x ξ = (tpart x - ⟪x,ξ⟫)^{-(n-1)}` is bounded
uniformly in `ξ ∈ Sph n` and in `x` in a ball: for each radius `R` there is `C ≥ 0` with
`|pfun n x ξ| ≤ C` whenever `‖x‖ ≤ R`.  (Indeed `tpart x - ⟪x,ξ⟫` lies in the compact
interval `[1/M, M]`, `M = √(1+R²) + R`, for `‖x‖ ≤ R` and `ξ` on the unit sphere.) -/
theorem PfunBoundSph (n : ℕ) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Submission.Mostow.E n, ‖x‖ ≤ R →
      ∀ ξ : Submission.Mostow.E n, ξ ∈ Submission.Mostow.Sph n →
        |Work.Mostow.pfun n x ξ| ≤ C := by
  by_cases hR : R < 0
  · -- vacuous: the ball of radius `R < 0` is empty
    refine ⟨0, le_refl 0, ?_⟩
    intro x hx ξ hξ
    exfalso
    have h1 : ‖x‖ < 0 := lt_of_le_of_lt hx hR
    have h2 : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
    linarith
  · have hR0 : 0 ≤ R := not_lt.mp hR
    refine ⟨(Real.sqrt (1 + R ^ 2) + R) ^ |1 - (n : ℝ)|,
      Real.rpow_nonneg (add_nonneg (Real.sqrt_nonneg _) hR0) _, ?_⟩
    -- name the constant `M = √(1+R²) + R`
    set M : ℝ := Real.sqrt (1 + R ^ 2) + R with hMdef
    have hM1 : 1 ≤ M := by
      have hsq : (1 : ℝ) ≤ 1 + R ^ 2 := by nlinarith [sq_nonneg R]
      have h1 : (1 : ℝ) ≤ Real.sqrt (1 + R ^ 2) := by
        have := Real.sqrt_le_sqrt hsq
        rwa [Real.sqrt_one] at this
      simp only [hMdef]
      linarith
    have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM1
    intro x hx ξ hξ
    have hξ1 : ‖ξ‖ = 1 := (mem_Sph_iff ξ).mp hξ
    have hs0 : 0 ≤ ‖x‖ := norm_nonneg x
    have hb_pos : 0 < tpart x - inner ℝ x ξ := busemann_arg_pos ξ hξ x
    -- Cauchy–Schwarz, both sides
    have hinner_ge : -‖x‖ ≤ inner ℝ x ξ := by
      have h := abs_real_inner_le_norm x ξ
      rw [hξ1, mul_one] at h
      exact (abs_le.mp h).1
    have hinner_le : inner ℝ x ξ ≤ ‖x‖ := by
      have h := abs_real_inner_le_norm x ξ
      rw [hξ1, mul_one] at h
      exact (abs_le.mp h).2
    -- the two bounds on `tpart x ± ‖x‖`
    have htx_le : tpart x ≤ Real.sqrt (1 + R ^ 2) := by
      rw [tpart]
      apply Real.sqrt_le_sqrt
      have hsq : ‖x‖ ^ 2 ≤ R ^ 2 := by
        simpa [pow_two] using mul_self_le_mul_self hs0 hx
      linarith
    have hb_le : tpart x - inner ℝ x ξ ≤ M := by
      rw [hMdef]
      linarith
    have hb_ge : M⁻¹ ≤ tpart x - inner ℝ x ξ := by
      have hden_pos : 0 < tpart x + ‖x‖ := tpart_add_norm_pos x
      have h1 : tpart x + ‖x‖ ≤ M := by
        rw [hMdef]
        linarith
      have h2 : M⁻¹ ≤ (tpart x + ‖x‖)⁻¹ := inv_anti₀ hden_pos h1
      have h3 : (tpart x + ‖x‖)⁻¹ = tpart x - ‖x‖ :=
        (eq_inv_of_mul_eq_one_right (tpart_add_norm_mul_tpart_sub_norm x)).symm
      rw [h3] at h2
      linarith
    -- rewrite the kernel without the absolute value
    have habs : |Work.Mostow.pfun n x ξ|
        = (tpart x - inner ℝ x ξ) ^ (1 - (n : ℝ)) := by
      have hp : Work.Mostow.pfun n x ξ
          = (tpart x - inner ℝ x ξ) ^ (-((n : ℝ) - 1)) := rfl
      rw [hp, abs_of_pos (Real.rpow_pos_of_pos hb_pos _),
        show -((n : ℝ) - 1) = 1 - (n : ℝ) by ring]
    by_cases he : 1 - (n : ℝ) ≤ 0
    · -- exponent `1 - n ≤ 0`: the lower bound `M⁻¹ ≤ b` is the relevant one
      calc |Work.Mostow.pfun n x ξ|
          = (tpart x - inner ℝ x ξ) ^ (1 - (n : ℝ)) := habs
        _ ≤ M⁻¹ ^ (1 - (n : ℝ)) :=
              Real.rpow_le_rpow_of_nonpos (inv_pos.mpr hMpos) hb_ge he
        _ = M ^ |1 - (n : ℝ)| := by
              rw [Real.inv_rpow (le_of_lt hMpos), ← Real.rpow_neg (le_of_lt hMpos),
                abs_of_nonpos he]
    · -- exponent `1 - n > 0`: the upper bound `b ≤ M` is the relevant one
      have he' : 0 < 1 - (n : ℝ) := not_le.mp he
      calc |Work.Mostow.pfun n x ξ|
          = (tpart x - inner ℝ x ξ) ^ (1 - (n : ℝ)) := habs
        _ ≤ M ^ (1 - (n : ℝ)) := Real.rpow_le_rpow (le_of_lt hb_pos) hb_le (le_of_lt he')
        _ ≤ M ^ |1 - (n : ℝ)| :=
              Real.rpow_le_rpow_of_exponent_le hM1 (le_abs_self (1 - (n : ℝ)))

end Work.Mostow
