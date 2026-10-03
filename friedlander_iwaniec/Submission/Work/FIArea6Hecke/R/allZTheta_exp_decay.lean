import Mathlib
import Submission.Work.FIArea6Hecke.R.AllZThetaDefs

namespace Work.FIArea6Hecke.R

open scoped BigOperators
open Work.FIPlan

noncomputable section

/-- The Gaussian kernel of `allZSummand` is a real exponential, hence
`‖e^{-πu n}‖ = e^{-πu n}` for real `u`, `n`. -/
lemma norm_exp_allZ (u n : ℝ) :
    ‖Complex.exp (-(Real.pi * u * n))‖ = Real.exp (-(Real.pi * u * n)) := by
  rw [Complex.norm_exp]; simp

/-- **Shifting the Gaussian parameter.**  For `u₀ ≤ u` every summand of `allZTheta` at level `u`
is dominated by its level-`u₀` value up to the global factor `e^{-π(u-u₀)}`.  The `z = 0` summand
vanishes identically (we use `χ₀ 0 = 0`), and for `z ≠ 0` we have `|z|² = gnorm z ≥ 1`, so that
`e^{-πu|z|²} ≤ e^{-π(u-u₀)}·e^{-πu₀|z|²}`. -/
lemma allZSummand_norm_shift {chi₀ : GaussianInt → ℂ} {m : ℕ} (hchi0 : chi₀ 0 = 0)
    {u₀ u : ℝ} (hu : u₀ ≤ u) (z : GaussianInt) :
    ‖allZSummand chi₀ m u z‖ ≤
      Real.exp (-Real.pi * (u - u₀)) * ‖allZSummand chi₀ m u₀ z‖ := by
  by_cases hz : z = 0
  · subst hz
    simp [allZSummand, hchi0]
  · have hg1 : (1 : ℝ) ≤ (gnorm z : ℝ) := by
      have hpos : 0 < gnorm z := Nat.pos_of_ne_zero (fun h => hz (eq_zero_of_gnorm_eq_zero h))
      exact_mod_cast hpos
    have hcore : -(Real.pi * u * (gnorm z : ℝ))
        ≤ -Real.pi * (u - u₀) + -(Real.pi * u₀ * (gnorm z : ℝ)) := by
      have h : 0 ≤ (u - u₀) * ((gnorm z : ℝ) - 1) :=
        mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hg1)
      nlinarith [Real.pi_pos, h]
    have hexp : Real.exp (-(Real.pi * u * (gnorm z : ℝ)))
        ≤ Real.exp (-Real.pi * (u - u₀)) * Real.exp (-(Real.pi * u₀ * (gnorm z : ℝ))) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr hcore
    rw [allZSummand, allZSummand, norm_mul, norm_mul, norm_mul, norm_mul,
      norm_exp_allZ, norm_exp_allZ]
    calc ‖chi₀ z‖ * ‖(z.toComplex) ^ m‖ * Real.exp (-(Real.pi * u * ↑(gnorm z)))
        ≤ ‖chi₀ z‖ * ‖(z.toComplex) ^ m‖ *
            (Real.exp (-Real.pi * (u - u₀)) * Real.exp (-(Real.pi * u₀ * ↑(gnorm z)))) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = Real.exp (-Real.pi * (u - u₀)) *
            (‖chi₀ z‖ * ‖(z.toComplex) ^ m‖ * Real.exp (-(Real.pi * u₀ * ↑(gnorm z)))) := by
          ring_nf

/-- **Exponential decay of the all-`z` theta series.**  For a weight `χ₀` bounded by `1` and
vanishing at `0`, the theta series `Θ(u) = Σ_z χ₀(z) z^m e^{-πu|z|²}` decays at least like
`e^{-πu}`: beyond `u₀ = 1` one has `‖Θ(u)‖ ≤ C·e^{-πu}`.

The `z = 0` summand contributes `χ₀(0)·0^m` and is killed by `χ₀ 0 = 0`; every remaining summand
carries the factor `e^{-πu|z|²} ≤ e^{-πu}·e^{-πu₀(|z|²-1)}` with `|z|² ≥ 1`, and the resulting
majorant is summable by `summable_allZSummand` / `summable_gnorm_weight`. -/
theorem allZTheta_exp_decay (chi₀ : GaussianInt → ℂ) (m : ℕ)
    (hchi : ∀ z : GaussianInt, ‖chi₀ z‖ ≤ 1) (hchi0 : chi₀ 0 = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ u₀ : ℝ, 0 < u₀ ∧ ∀ u : ℝ, u₀ ≤ u →
      ‖Work.FIArea6Hecke.R.allZTheta chi₀ m u‖ ≤ C * Real.exp (-Real.pi * u) := by
  classical
  set u₀ : ℝ := 1 with hu₀def
  have hu₀pos : 0 < u₀ := by rw [hu₀def]; norm_num
  have hsum₀ : Summable (fun z : GaussianInt => allZSummand chi₀ m u₀ z) :=
    summable_allZSummand hu₀pos hchi
  have hnorm₀ : Summable (fun z : GaussianInt => ‖allZSummand chi₀ m u₀ z‖) := hsum₀.norm
  refine ⟨Real.exp (Real.pi * u₀) * ∑' z : GaussianInt, ‖allZSummand chi₀ m u₀ z‖,
    mul_nonneg (Real.exp_nonneg _) (tsum_nonneg (fun z => norm_nonneg _)), u₀, hu₀pos, ?_⟩
  intro u hu
  have hsumu : Summable (fun z : GaussianInt => allZSummand chi₀ m u z) :=
    summable_allZSummand (lt_of_lt_of_le hu₀pos hu) hchi
  have hnormu : Summable (fun z : GaussianInt => ‖allZSummand chi₀ m u z‖) := hsumu.norm
  have hterm : ∀ z : GaussianInt, ‖allZSummand chi₀ m u z‖ ≤
      Real.exp (-Real.pi * (u - u₀)) * ‖allZSummand chi₀ m u₀ z‖ :=
    fun z => allZSummand_norm_shift hchi0 hu z
  calc ‖Work.FIArea6Hecke.R.allZTheta chi₀ m u‖
      = ‖∑' z : GaussianInt, allZSummand chi₀ m u z‖ := by rw [allZTheta_eq_tsum_summand]
    _ ≤ ∑' z : GaussianInt, ‖allZSummand chi₀ m u z‖ := norm_tsum_le_tsum_norm hnormu
    _ ≤ ∑' z : GaussianInt, Real.exp (-Real.pi * (u - u₀)) * ‖allZSummand chi₀ m u₀ z‖ :=
        Summable.tsum_le_tsum hterm hnormu (hnorm₀.mul_left _)
    _ = Real.exp (-Real.pi * (u - u₀)) * ∑' z : GaussianInt, ‖allZSummand chi₀ m u₀ z‖ :=
        tsum_mul_left
    _ = (Real.exp (Real.pi * u₀) * ∑' z : GaussianInt, ‖allZSummand chi₀ m u₀ z‖)
          * Real.exp (-Real.pi * u) := by
        rw [show Real.exp (-Real.pi * (u - u₀))
              = Real.exp (Real.pi * u₀) * Real.exp (-Real.pi * u) by
            rw [← Real.exp_add]; congr 1; ring]
        ring

end

end Work.FIArea6Hecke.R
