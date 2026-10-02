import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Koebe

/-- **Growth bound for the Taylor coefficients of a function holomorphic on the unit disk.**

If `h : ℂ → ℂ` is complex differentiable on the open unit ball around `0`, then its Taylor
coefficients `a n = (n!)⁻¹ * iteratedDeriv n h 0` grow at most geometrically with any ratio
`s⁻¹ > 1`, `s ∈ (0,1)`: there is a constant `C` with `‖a n‖ ≤ C * s⁻¹ ^ n` for all `n`.

The point is that the radius of convergence of the Taylor series at `0` is at least `1`, so
`a n * ρ ^ n → 0` for every `ρ < 1`; picking `ρ = (1+s)/2 ∈ (s,1)` and using that the terms of
a summable nonnegative series are bounded by the total sum yields the claim, since then
`ρ⁻¹ ≤ s⁻¹`. -/
theorem signedArea_coeff_bound (h : ℂ → ℂ) (hd : DifferentiableOn ℂ h (Metric.ball 0 1))
    (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ, ∀ n : ℕ, ‖(n.factorial : ℂ)⁻¹ * iteratedDeriv n h 0‖ ≤ C * s⁻¹ ^ n := by
  -- Work at the intermediate radius `ρ = (1+s)/2`, which satisfies `s < ρ < 1`.
  set ρ : ℝ := (1 + s) / 2 with hρdef
  have hsρ : s < ρ := by rw [hρdef]; linarith
  have hρ1 : ρ < 1 := by rw [hρdef]; linarith
  have hρ0 : 0 < ρ := lt_trans hs0 hsρ
  have hnormρ : ‖(ρ : ℂ)‖ = ρ := by
    rw [show ‖(ρ : ℂ)‖ = |ρ| from RCLike.norm_ofReal ρ, abs_of_pos hρ0]
  -- The Taylor series of `h` at `0` converges at the real point `ρ ∈ (0,1)`.
  have hzmem : (ρ : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero, hnormρ]
    exact hρ1
  have hHas := Complex.hasSum_taylorSeries_on_ball (f := h) (c := 0) (r := 1) hd hzmem
  -- Name the Taylor coefficients.
  set a : ℕ → ℂ := fun n => (n.factorial : ℂ)⁻¹ * iteratedDeriv n h 0 with hadef
  have hfe : (fun n : ℕ => (n.factorial : ℂ)⁻¹ • ((ρ : ℂ) - 0) ^ n • iteratedDeriv n h 0)
      = (fun n : ℕ => a n * (ρ : ℂ) ^ n) := by
    funext n
    rw [hadef]
    simp only [sub_zero, smul_eq_mul]
    ring
  have hHas' : HasSum (fun n : ℕ => a n * (ρ : ℂ) ^ n) (h ρ) := by
    rw [hfe] at hHas
    exact hHas
  have hSum : Summable (fun n : ℕ => a n * (ρ : ℂ) ^ n) := hHas'.summable
  have hSumNorm : Summable (fun n : ℕ => ‖a n‖ * ρ ^ n) := by
    refine (hSum.norm).congr ?_
    intro n
    rw [norm_mul, norm_pow, hnormρ]
  -- The total mass of the nonnegative series bounds each of its terms.
  set M : ℝ := ∑' n : ℕ, ‖a n‖ * ρ ^ n with hMdef
  have hMnonneg : 0 ≤ M := by
    rw [hMdef]
    exact tsum_nonneg (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg hρ0.le n))
  refine ⟨M, ?_⟩
  intro n
  have hle : ‖a n‖ * ρ ^ n ≤ M := by
    rw [hMdef]
    exact hSumNorm.le_tsum n (fun j hj => mul_nonneg (norm_nonneg _) (pow_nonneg hρ0.le j))
  have hρn_pos : 0 < ρ ^ n := pow_pos hρ0 n
  have h1 : ‖a n‖ ≤ M * (ρ⁻¹) ^ n := by
    have h2 : ‖a n‖ ≤ M / ρ ^ n := (le_div_iff₀ hρn_pos).mpr hle
    rwa [div_eq_mul_inv, ← inv_pow] at h2
  have hρinv_le : ρ⁻¹ ≤ s⁻¹ := (inv_le_inv₀ hρ0 hs0).mpr hsρ.le
  have hpow : M * (ρ⁻¹) ^ n ≤ M * (s⁻¹) ^ n :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.mpr hρ0.le) hρinv_le n) hMnonneg
  calc ‖(n.factorial : ℂ)⁻¹ * iteratedDeriv n h 0‖
      = ‖a n‖ := by rw [hadef]
    _ ≤ M * (ρ⁻¹) ^ n := h1
    _ ≤ M * (s⁻¹) ^ n := hpow

end Work.Koebe
