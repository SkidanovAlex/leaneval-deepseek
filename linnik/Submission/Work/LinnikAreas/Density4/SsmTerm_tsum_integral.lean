import Mathlib
import Submission.Work.LinnikAreas.Density4.SsmTermDefs

open DirichletCharacter Complex MeasureTheory
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas.Density4

/-- Pointwise domination of the summands by a summable-times-integrable majorant.

For every `n` (including `n = 0`, where both sides vanish because `Ψ(0) = 0` and `X/0 = 0`),
`‖SsmTerm n t‖ ≤ (X · ‖mollCoeff n‖ · n^{-(Re ρ + 1)}) · ‖Γ(1 + it)‖`.

The first factor is summable in `n` by hypothesis and `t ↦ ‖Γ(1 + it)‖` is integrable, so the right
hand side is a product majorant; this is what makes Tonelli/Fubini applicable. -/
lemma norm_SsmTerm_le_rpow (q : ℕ) [NeZero q] (U V W X : ℝ) (χ : DirichletCharacter ℂ q)
    (ρ : ℂ) (hX : 0 < X) (n : ℕ) (t : ℝ) :
    ‖SsmTerm q U V W X χ ρ n t‖
      ≤ (X * (‖mollCoeff q U V W χ n‖ * (n : ℝ) ^ (-(ρ.re + 1))))
          * ‖Complex.Gamma ((1 : ℂ) + (t : ℂ) * Complex.I)‖ := by
  refine (norm_SsmTerm_le q U V W X χ ρ hX n t).trans (le_of_eq ?_)
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [mollCoeff_zero]
    norm_num
  · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hsplit : (n : ℝ) ^ (-ρ.re) * (n : ℝ) ^ (-(1 : ℝ)) = (n : ℝ) ^ (-(ρ.re + 1)) := by
      rw [← Real.rpow_add hn0]
      congr 1
      ring
    have hXdiv : (‖mollCoeff q U V W χ n‖ * (n : ℝ) ^ (-ρ.re) * (X / (n : ℝ)))
        = X * (‖mollCoeff q U V W χ n‖ * ((n : ℝ) ^ (-ρ.re) * (n : ℝ) ^ (-(1 : ℝ)))) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one (n : ℝ)]
      ring
    rw [hXdiv, hsplit]

/-- `t ↦ SsmTerm q U V W X χ ρ n t` is ae-strongly measurable (w.r.t. Lebesgue measure on `ℝ`):
it is continuous for `n ≥ 1` and identically `0` for `n = 0`. -/
lemma aestronglyMeasurable_SsmTerm (q : ℕ) [NeZero q] (U V W X : ℝ) (χ : DirichletCharacter ℂ q)
    (ρ : ℂ) (hX : 0 < X) (n : ℕ) :
    AEStronglyMeasurable (fun t : ℝ => SsmTerm q U V W X χ ρ n t) volume := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp only [SsmTerm_zero]
    exact (continuous_const : Continuous fun _ : ℝ => (0 : ℂ)).aestronglyMeasurable
  · have hb : (((n : ℝ) / X : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]
      exact ne_of_gt (div_pos (by exact_mod_cast hn) hX)
    have hXc : Continuous
        (fun t : ℝ => (((n : ℝ) / X : ℝ) : ℂ) ^ (-(1 + (t : ℂ) * Complex.I))) := by
      have harg : Continuous (fun t : ℝ => -(1 + (t : ℂ) * Complex.I)) := by fun_prop
      exact harg.const_cpow (Or.inl hb)
    have hΓc : Continuous (fun t : ℝ => Complex.Gamma ((1 : ℂ) + (t : ℂ) * Complex.I)) := by
      rw [continuous_iff_continuousAt]
      intro t
      have hinner : ContinuousAt (fun t : ℝ => (1 : ℂ) + (t : ℂ) * Complex.I) t := by fun_prop
      refine ContinuousAt.comp (f := fun t : ℝ => (1 : ℂ) + (t : ℂ) * Complex.I)
        (g := Complex.Gamma) (x := t) ?_ hinner
      exact Complex.continuousAt_Gamma ((1 : ℂ) + (t : ℂ) * Complex.I) (fun m hm => by
        have hre : (1 : ℝ) = -(m : ℝ) := by
          have := congrArg Complex.re hm
          simpa using this
        have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        linarith)
    have hmain : Continuous fun t : ℝ => mollCoeff q U V W χ n * (n : ℂ) ^ (-ρ) *
        ((((n : ℝ) / X : ℝ) : ℂ) ^ (-(1 + (t : ℂ) * Complex.I)) *
          Complex.Gamma ((1 : ℂ) + (t : ℂ) * Complex.I)) :=
      (continuous_const.mul continuous_const).mul (hXc.mul hΓc)
    simpa only [SsmTerm] using hmain.aestronglyMeasurable

theorem SsmTerm_tsum_integral (q : ℕ) [NeZero q] (U V W X : ℝ) (χ : DirichletCharacter ℂ q) (ρ : ℂ)
    (hX : 0 < X) (hβ : 0 < ρ.re)
    (hsum : Summable (fun n : ℕ => ‖Work.LinnikAreas.Density4.mollCoeff q U V W χ n‖ * (n : ℝ) ^ (-(ρ.re + 1)))) :
    (∑' n : ℕ, ∫ t : ℝ, Work.LinnikAreas.Density4.SsmTerm q U V W X χ ρ n t)
      = ∫ t : ℝ, ∑' n : ℕ, Work.LinnikAreas.Density4.SsmTerm q U V W X χ ρ n t := by
  have hΓ : Integrable (fun t : ℝ => ‖Complex.Gamma ((1 : ℂ) + (t : ℂ) * Complex.I)‖) :=
    integrable_norm_gamma_vertical_one
  have hgsum : Summable
      (fun n : ℕ => X * (‖mollCoeff q U V W χ n‖ * (n : ℝ) ^ (-(ρ.re + 1)))) :=
    hsum.mul_left X
  have hFint : ∀ n : ℕ, Integrable (fun t : ℝ => SsmTerm q U V W X χ ρ n t) := by
    intro n
    refine (hΓ.const_mul (X * (‖mollCoeff q U V W χ n‖ * (n : ℝ) ^ (-(ρ.re + 1))))).mono'
      (aestronglyMeasurable_SsmTerm q U V W X χ ρ hX n) ?_
    filter_upwards with t
    exact norm_SsmTerm_le_rpow q U V W X χ ρ hX n t
  have hsumint : Summable (fun n : ℕ => ∫ t : ℝ, ‖SsmTerm q U V W X χ ρ n t‖) := by
    have hbd : Summable (fun n : ℕ =>
        ∫ t : ℝ, (X * (‖mollCoeff q U V W χ n‖ * (n : ℝ) ^ (-(ρ.re + 1)))) *
          ‖Complex.Gamma ((1 : ℂ) + (t : ℂ) * Complex.I)‖) := by
      have h2 : ∀ n : ℕ,
          (∫ t : ℝ, (X * (‖mollCoeff q U V W χ n‖ * (n : ℝ) ^ (-(ρ.re + 1)))) *
            ‖Complex.Gamma ((1 : ℂ) + (t : ℂ) * Complex.I)‖)
          = (X * (‖mollCoeff q U V W χ n‖ * (n : ℝ) ^ (-(ρ.re + 1)))) *
              ∫ t : ℝ, ‖Complex.Gamma ((1 : ℂ) + (t : ℂ) * Complex.I)‖ :=
        fun n => integral_const_mul _ _
      simpa only [h2] using hgsum.mul_right
        (∫ t : ℝ, ‖Complex.Gamma ((1 : ℂ) + (t : ℂ) * Complex.I)‖)
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg (fun t => norm_nonneg _))
      (fun n => ?_) hbd
    refine integral_mono (hFint n).norm
      (hΓ.const_mul (X * (‖mollCoeff q U V W χ n‖ * (n : ℝ) ^ (-(ρ.re + 1))))) (fun t => ?_)
    exact norm_SsmTerm_le_rpow q U V W X χ ρ hX n t
  exact MeasureTheory.integral_tsum_of_summable_integral_norm hFint hsumint

end Work.LinnikAreas.Density4
