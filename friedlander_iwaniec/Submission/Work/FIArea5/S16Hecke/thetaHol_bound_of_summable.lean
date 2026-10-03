import Mathlib
import Submission.Work.FIArea5.S16Hecke.heckeFE_defs

namespace Work.FIArea5.S16Hecke

open scoped BigOperators
open Work.FIPlan

noncomputable section

/-- A primary Gaussian integer is nonzero (its real part is odd). -/
lemma isPrimary_ne_zero (z : GaussianInt) (hz : IsPrimary z) : z ≠ 0 := by
  rintro rfl
  obtain ⟨h1, _⟩ := hz
  simp only [Zsqrtd.re_zero] at h1
  exact Int.not_odd_zero h1

/-- For a primary Gaussian integer `z` one has `|z|² = gnorm z ≥ 1`. -/
lemma one_le_gnorm_of_isPrimary (z : GaussianInt) (hz : IsPrimary z) : 1 ≤ gnorm z := by
  rw [Nat.one_le_iff_ne_zero]
  intro h0
  have hnorm : ‖z.toComplex‖ = 0 := by
    rw [norm_toComplex, h0]; simp
  have hz0 : z.toComplex = 0 := norm_eq_zero.mp hnorm
  exact isPrimary_ne_zero z hz
    (GaussianInt.toComplex_injective (by rw [hz0, GaussianInt.toComplex_zero]))

/-- `‖exp(-πug)‖ = e^{-πug}` for real `u`, `g`. -/
lemma norm_exp_neg_mul (u g : ℝ) :
    ‖Complex.exp (-Real.pi * u * g)‖ = Real.exp (-Real.pi * u * g) := by
  have h : (-(Real.pi : ℂ) * u * g) = (((-(Real.pi * u * g)) : ℝ) : ℂ) := by push_cast; ring
  rw [h, Complex.norm_exp_ofReal, show -(Real.pi * u * g) = -Real.pi * u * g by ring]

/-- Splitting the Gaussian factor: for `u ≥ u₀` and `g ≥ 1`, `e^{-πug} ≤ e^{-π(u-u₀)}·e^{-πu₀g}`. -/
lemma exp_neg_mul_le (u u₀ g : ℝ) (hu : u₀ ≤ u) (hg : 1 ≤ g) :
    Real.exp (-Real.pi * u * g) ≤ Real.exp (-Real.pi * (u - u₀)) * Real.exp (-Real.pi * u₀ * g) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h : 0 ≤ (u - u₀) * (g - 1) := mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hg)
  nlinarith [Real.pi_pos, h]

/-- The summability hypothesis at `u₀` makes every summand of `thetaHol` at level `u ≥ u₀`
dominated by the level-`u₀` summand, up to the global factor `e^{-π(u-u₀)}`. -/
lemma norm_thetaSummand_le (chi : GaussianInt → ℂ) (m : ℕ) {u₀ u : ℝ} (hu : u₀ ≤ u) (z : GaussianInt) :
    ‖thetaSummand chi m u z‖ ≤ Real.exp (-Real.pi * (u - u₀)) * ‖thetaSummand chi m u₀ z‖ := by
  classical
  by_cases hz : IsPrimary z
  · simp only [thetaSummand, if_pos hz]
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_exp_neg_mul, norm_exp_neg_mul]
    have hg1 : (1 : ℝ) ≤ (gnorm z : ℝ) := by
      exact_mod_cast one_le_gnorm_of_isPrimary z hz
    have hexp : Real.exp (-Real.pi * u * (gnorm z : ℝ))
        ≤ Real.exp (-Real.pi * (u - u₀)) * Real.exp (-Real.pi * u₀ * (gnorm z : ℝ)) :=
      exp_neg_mul_le u u₀ (gnorm z : ℝ) hu hg1
    calc ‖chi z‖ * ‖(z.toComplex) ^ m‖ * Real.exp (-Real.pi * u * (gnorm z : ℝ))
        ≤ ‖chi z‖ * ‖(z.toComplex) ^ m‖ *
            (Real.exp (-Real.pi * (u - u₀)) * Real.exp (-Real.pi * u₀ * (gnorm z : ℝ))) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = Real.exp (-Real.pi * (u - u₀)) *
            (‖chi z‖ * ‖(z.toComplex) ^ m‖ * Real.exp (-Real.pi * u₀ * (gnorm z : ℝ))) := by
          ring
  · simp only [thetaSummand, if_neg hz, norm_zero, mul_zero, le_refl]

theorem thetaHol_bound_of_summable (chi : GaussianInt → ℂ) (m : ℕ) {u₀ : ℝ} (hu₀ : 0 < u₀)
    (hsum : Summable (fun z : GaussianInt => thetaSummand chi m u₀ z)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, u₀ ≤ u →
      ‖thetaHol chi m u‖ ≤ C * Real.exp (-Real.pi * (u - u₀)) := by
  classical
  have _ := hu₀
  refine ⟨∑' z : GaussianInt, ‖thetaSummand chi m u₀ z‖,
    tsum_nonneg (fun z => norm_nonneg _), ?_⟩
  intro u hu
  have hnormsum₀ : Summable (fun z : GaussianInt => ‖thetaSummand chi m u₀ z‖) := hsum.norm
  have hterm := fun z => norm_thetaSummand_le chi m hu z
  have hsumu : Summable (fun z : GaussianInt => thetaSummand chi m u z) := by
    apply Summable.of_norm_bounded (g := fun z =>
      Real.exp (-Real.pi * (u - u₀)) * ‖thetaSummand chi m u₀ z‖)
    · exact Summable.mul_left _ hnormsum₀
    · exact hterm
  have hnormsumu : Summable (fun z : GaussianInt => ‖thetaSummand chi m u z‖) := hsumu.norm
  calc ‖thetaHol chi m u‖
      = ‖∑' z : GaussianInt, thetaSummand chi m u z‖ := by rw [thetaHol_eq_tsum]
    _ ≤ ∑' z : GaussianInt, ‖thetaSummand chi m u z‖ :=
        norm_tsum_le_tsum_norm hnormsumu
    _ ≤ ∑' z : GaussianInt, Real.exp (-Real.pi * (u - u₀)) * ‖thetaSummand chi m u₀ z‖ :=
        Summable.tsum_le_tsum hterm hnormsumu (Summable.mul_left _ hnormsum₀)
    _ = Real.exp (-Real.pi * (u - u₀)) * ∑' z : GaussianInt, ‖thetaSummand chi m u₀ z‖ :=
        tsum_mul_left
    _ = (∑' z : GaussianInt, ‖thetaSummand chi m u₀ z‖) * Real.exp (-Real.pi * (u - u₀)) := by
        ring

end

end Work.FIArea5.S16Hecke
