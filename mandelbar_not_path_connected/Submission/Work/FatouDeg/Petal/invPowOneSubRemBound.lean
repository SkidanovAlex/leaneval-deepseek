import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Truncated expansion of `(1 - w)^{-n}` up to order two

For every `n : ℕ` the function `w ↦ ((1 - w) ^ n)⁻¹` agrees with its Taylor polynomial

`1 + n * w + (n * (n + 1) / 2) * w ^ 2`

up to an error of the order `‖w‖ ^ 3` on the disc `‖w‖ ≤ 1 / 2`.

The proof is by induction on `n`, using the exact relation `f = 1 + w + w² * f` for
`f = (1 - w)⁻¹`: writing `Pₙ` for the truncation, `Dₙ = (1 - w)^{-n} - Pₙ` and
`cₙ = n (n + 1) / 2`, one has

* `f^{n+1} - P_{n+1} = (Pₙ * f - P_{n+1}) + Dₙ * f`,
* `Pₙ * f - P_{n+1} = w² * (Pₙ * f - 1) + cₙ * w³`,
* `Pₙ * f - 1 = w * (n + 1 + cₙ * w) * f`,

and `‖Pₙ * f - 1‖ ≤ 2 (n + 1 + cₙ / 2) ‖w‖` on `‖w‖ ≤ 1 / 2`, giving the recursion
`C_{n+1} ≤ 2 Cₙ + (n + 1)(n + 2)` for the constants.
-/

namespace Work.FatouDeg.Petal

/-- The quadratic coefficient `n (n + 1) / 2` of the Taylor polynomial of `(1 - w)^{-n}`. -/
noncomputable def invPowCoeff (n : ℕ) : ℂ := (n : ℂ) * (n + 1) / 2

/-- The Taylor truncation of `(1 - w)^{-n}` at the origin, up to order two. -/
noncomputable def invPowTaylor (n : ℕ) (w : ℂ) : ℂ :=
  1 + (n : ℂ) * w + invPowCoeff n * w ^ 2

/-- The truncation `invPowTaylor n w` is definitionally the expression appearing in the
statement of `invPowOneSubRemBound`. -/
lemma invPowTaylor_eq (n : ℕ) (w : ℂ) :
    invPowTaylor n w = 1 + (n : ℂ) * w + ((n : ℂ) * (n + 1) / 2) * w ^ 2 := rfl

/-- Norm of the quadratic coefficient. -/
lemma invPowCoeff_norm (n : ℕ) : ‖invPowCoeff n‖ = (n : ℝ) * (n + 1) / 2 := by
  unfold invPowCoeff
  rw [show (n : ℂ) * (n + 1) = ((n * (n + 1) : ℕ) : ℂ) by push_cast; ring]
  rw [show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num]
  rw [norm_div, Complex.norm_natCast, Complex.norm_natCast]
  push_cast
  ring

/-- Norm of `n + 1` viewed in `ℂ`. -/
lemma norm_natCast_add_one (n : ℕ) : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
  have h : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
  rw [h, Complex.norm_natCast]
  push_cast
  ring

theorem invPowOneSubRemBound (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, ‖w‖ ≤ 1 / 2 →
    ‖((1 - w) ^ n)⁻¹ - (1 + (n : ℂ) * w + ((n : ℂ) * (n + 1) / 2) * w ^ 2)‖
      ≤ C * ‖w‖ ^ 3 := by
  have main : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, ‖w‖ ≤ 1 / 2 →
      ‖((1 - w) ^ n)⁻¹ - invPowTaylor n w‖ ≤ C * ‖w‖ ^ 3 := by
    intro n
    induction n with
    | zero =>
      refine ⟨0, le_refl 0, ?_⟩
      intro w hw
      simp [invPowTaylor, invPowCoeff]
    | succ n ih =>
      obtain ⟨C₀, hC₀, hih⟩ := ih
      refine ⟨2 * C₀ + ((n : ℝ) + 1) * ((n : ℝ) + 2), ?_, ?_⟩
      · positivity
      · intro w hw
        have hw1 : (1 : ℂ) - w ≠ 0 := by
          intro h
          have hwe : w = 1 := (sub_eq_zero.mp h).symm
          rw [hwe] at hw
          norm_num at hw
        set f : ℂ := (1 - w)⁻¹ with hf
        have hf_norm : ‖f‖ ≤ 2 := by
          rw [hf, norm_inv]
          have h1 : (1 : ℝ) / 2 ≤ ‖(1 : ℂ) - w‖ := by
            have := norm_sub_norm_le (1 : ℂ) w
            simp only [norm_one] at this
            linarith
          have hpos : (0 : ℝ) < ‖(1 : ℂ) - w‖ := by linarith
          rw [inv_le_comm₀ hpos (by norm_num : (0 : ℝ) < 2)]
          norm_num
          exact h1
        have hDn : ‖((1 - w) ^ n)⁻¹ - invPowTaylor n w‖ ≤ C₀ * ‖w‖ ^ 3 := hih w hw
        have hdecomp : ((1 - w) ^ (n + 1))⁻¹ - invPowTaylor (n + 1) w
            = (invPowTaylor n w * f - invPowTaylor (n + 1) w)
              + (((1 - w) ^ n)⁻¹ - invPowTaylor n w) * f := by
          have hpow : ((1 - w) ^ (n + 1))⁻¹ = ((1 - w) ^ n)⁻¹ * f := by
            rw [hf]; rw [pow_succ, mul_inv_rev, mul_comm]
          rw [hpow]; ring
        have hkey : invPowTaylor n w * f - 1
            = w * ((n : ℂ) + 1 + invPowCoeff n * w) * f := by
          rw [hf]; unfold invPowTaylor invPowCoeff; field_simp; ring
        have hsub : invPowTaylor n w * f - invPowTaylor (n + 1) w
            = w ^ 2 * (invPowTaylor n w * f - 1) + invPowCoeff n * w ^ 3 := by
          rw [hf]; unfold invPowTaylor invPowCoeff; field_simp; push_cast; ring
        have hkey_norm :
            ‖invPowTaylor n w * f - 1‖ ≤ ‖w‖ * (2 * ((n : ℝ) + 1) + (n : ℝ) * (n + 1) / 2) := by
          rw [hkey]
          have hA_bound : ‖(n : ℂ) + 1 + invPowCoeff n * w‖
              ≤ (n : ℝ) + 1 + (n : ℝ) * (n + 1) / 2 * ‖w‖ := by
            calc ‖(n : ℂ) + 1 + invPowCoeff n * w‖
                ≤ ‖(n : ℂ) + 1‖ + ‖invPowCoeff n * w‖ := norm_add_le _ _
              _ = (n : ℝ) + 1 + (n : ℝ) * (n + 1) / 2 * ‖w‖ := by
                    rw [norm_natCast_add_one n, norm_mul, invPowCoeff_norm n]
          have hstep1 : ‖w * ((n : ℂ) + 1 + invPowCoeff n * w) * f‖
              ≤ ‖w‖ * ((n : ℝ) + 1 + (n : ℝ) * (n + 1) / 2 * ‖w‖) * 2 := by
            rw [norm_mul, norm_mul]
            calc ‖w‖ * ‖(n : ℂ) + 1 + invPowCoeff n * w‖ * ‖f‖
                ≤ ‖w‖ * ((n : ℝ) + 1 + (n : ℝ) * (n + 1) / 2 * ‖w‖) * ‖f‖ :=
                  mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left hA_bound (norm_nonneg w)) (norm_nonneg f)
              _ ≤ ‖w‖ * ((n : ℝ) + 1 + (n : ℝ) * (n + 1) / 2 * ‖w‖) * 2 :=
                  mul_le_mul_of_nonneg_left hf_norm (by positivity)
          have hstep2 : ‖w‖ * ((n : ℝ) + 1 + (n : ℝ) * (n + 1) / 2 * ‖w‖) * 2
              ≤ ‖w‖ * (2 * ((n : ℝ) + 1) + (n : ℝ) * (n + 1) / 2) := by
            have hc : 0 ≤ (n : ℝ) * (n + 1) / 2 := by positivity
            have hw0 : 0 ≤ ‖w‖ := norm_nonneg w
            have hcc : ((n : ℝ) * (n + 1) / 2) * ‖w‖ * 2 ≤ (n : ℝ) * (n + 1) / 2 := by
              nlinarith [hc, hw, hw0]
            nlinarith [hcc, hw0]
          linarith [hstep1, hstep2]
        have hsub_norm :
            ‖invPowTaylor n w * f - invPowTaylor (n + 1) w‖
              ≤ ((n : ℝ) + 1) * ((n : ℝ) + 2) * ‖w‖ ^ 3 := by
          rw [hsub]
          calc ‖w ^ 2 * (invPowTaylor n w * f - 1) + invPowCoeff n * w ^ 3‖
              ≤ ‖w ^ 2 * (invPowTaylor n w * f - 1)‖ + ‖invPowCoeff n * w ^ 3‖ :=
                norm_add_le _ _
            _ = ‖w‖ ^ 2 * ‖invPowTaylor n w * f - 1‖ + ‖invPowCoeff n‖ * ‖w‖ ^ 3 := by
                  simp only [norm_mul, norm_pow]
            _ ≤ ‖w‖ ^ 2 * (‖w‖ * (2 * ((n : ℝ) + 1) + (n : ℝ) * (n + 1) / 2))
                  + ((n : ℝ) * (n + 1) / 2) * ‖w‖ ^ 3 := by
                  rw [invPowCoeff_norm n]
                  exact add_le_add (mul_le_mul_of_nonneg_left hkey_norm (by positivity)) le_rfl
            _ = ((n : ℝ) + 1) * ((n : ℝ) + 2) * ‖w‖ ^ 3 := by ring
        calc ‖((1 - w) ^ (n + 1))⁻¹ - invPowTaylor (n + 1) w‖
            = ‖(invPowTaylor n w * f - invPowTaylor (n + 1) w)
                + (((1 - w) ^ n)⁻¹ - invPowTaylor n w) * f‖ := by rw [hdecomp]
          _ ≤ ‖invPowTaylor n w * f - invPowTaylor (n + 1) w‖
                + ‖(((1 - w) ^ n)⁻¹ - invPowTaylor n w) * f‖ := norm_add_le _ _
          _ ≤ ((n : ℝ) + 1) * ((n : ℝ) + 2) * ‖w‖ ^ 3 + (C₀ * ‖w‖ ^ 3) * 2 :=
              add_le_add hsub_norm
                (by rw [norm_mul]
                    exact mul_le_mul hDn hf_norm (norm_nonneg f) (by positivity))
          _ = (2 * C₀ + ((n : ℝ) + 1) * ((n : ℝ) + 2)) * ‖w‖ ^ 3 := by ring
  obtain ⟨C, hC, h⟩ := main n
  exact ⟨C, hC, h⟩

end Work.FatouDeg.Petal
