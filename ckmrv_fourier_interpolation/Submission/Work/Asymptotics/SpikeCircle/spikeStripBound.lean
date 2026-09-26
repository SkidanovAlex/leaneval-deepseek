import Mathlib
import Submission.Work.Asymptotics.SpikeCircle.divisorLowerDisc
import Submission.Work.Asymptotics.SpikeCircle.divisorLower
import Submission.Work.Asymptotics.continuous_AfunFun
import Submission.Work.Asymptotics.KfunAuxDefs

/-!
# Uniform bound for the kernel on the spike circle in the strip `2 ≤ Im τ ≤ H`

On the compact "spike region"

  `{(τ,ζ) : τ ∈ 𝒟, 2 ≤ Im τ ≤ H, ‖ζ - τ‖ = 29/20}`

the cleared kernel `AfunFun` is bounded by a constant `A` (`continuous_AfunFun` on the compact
`spikeSet H`).  The divisor lower bound `divisorLowerDisc` controls `‖j τ - j ζ‖` from below by
`c · exp (2π Im τ) · ‖(ζ-τ)(ζ-τ-1)(ζ-τ+1)‖`, and on the circle `‖ζ-τ‖ = 29/20` each of the
last two factors has norm at least `9/20`; since `Im τ ≥ 2` this is bounded below by a positive
constant.  Hence `Kfun = AfunFun/(j τ - j ζ)` is bounded.
-/
namespace Work.Asymptotics.SpikeCircle

open UpperHalfPlane

noncomputable section

open Work.Kernels

/-- Reverse-triangle lower bound: for `‖a‖ = 29/20` the product `a (a+1) (a-1)` has norm at
least `(29/20)·(9/20)²`. -/
lemma norm_mul_succ_pred_lower {a : ℂ} (ha : ‖a‖ = 29 / 20) :
    (29 / 20) * (9 / 20) * (9 / 20) ≤ ‖a * (a + 1) * (a - 1)‖ := by
  have h1 : (9 / 20 : ℝ) ≤ ‖a + 1‖ := by
    have h := abs_norm_sub_norm_le a (-1)
    rw [norm_neg, norm_one, ha] at h
    rw [sub_neg_eq_add] at h
    have h2 : |(29 : ℝ) / 20 - 1| = 9 / 20 := by norm_num
    linarith [h, le_of_eq h2]
  have h2 : (9 / 20 : ℝ) ≤ ‖a - 1‖ := by
    have h := abs_norm_sub_norm_le a 1
    rw [norm_one, ha] at h
    have h3 : |(29 : ℝ) / 20 - 1| = 9 / 20 := by norm_num
    linarith [h, le_of_eq h3]
  have hp1 : (0 : ℝ) ≤ ‖a + 1‖ := norm_nonneg _
  have hm1 : (0 : ℝ) ≤ ‖a - 1‖ := norm_nonneg _
  rw [norm_mul, norm_mul, ha]
  nlinarith

theorem spikeStripBound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (H : ℝ) (hH : 3 ≤ H) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ ζ : UpperHalfPlane, Work.Asymptotics.Funnel τ →
      ‖(ζ : ℂ) - (τ : ℂ)‖ = 29 / 20 → τ.im ≤ H →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun ζ →
      ‖Work.Kernels.Kfun ℓ d τ ζ‖ ≤ C := by
  -- Step 1: a uniform bound for `AfunFun` on the compact spike region.
  obtain ⟨A₀, hA₀⟩ : ∃ A : ℝ, ∀ p : UpperHalfPlane × UpperHalfPlane,
      p ∈ spikeSet H → ‖AfunFun ℓ d p.1 p.2‖ ≤ A := by
    have hcomp : IsCompact (spikeSet H) := isCompact_spikeSet H hH
    have hcont : Continuous
        (fun p : UpperHalfPlane × UpperHalfPlane => ‖AfunFun ℓ d p.1 p.2‖) :=
      (continuous_AfunFun ℓ d).norm
    have himg : IsCompact ((fun p : UpperHalfPlane × UpperHalfPlane =>
        ‖AfunFun ℓ d p.1 p.2‖) '' spikeSet H) := hcomp.image hcont
    obtain ⟨A, hA⟩ := himg.bddAbove
    refine ⟨A, fun p hp => ?_⟩
    exact hA (Set.mem_image_of_mem _ hp)
  -- Step 2: the divisor lower bound, uniformly over the strip.
  obtain ⟨c, hc, hdiv⟩ := divisorLowerDisc
  have hprod_pos : (0 : ℝ) < (29 / 20) * (9 / 20) * (9 / 20) := by norm_num
  set Cd : ℝ := c * Real.exp (4 * Real.pi) * ((29 / 20) * (9 / 20) * (9 / 20)) with hCd
  have hCdpos : 0 < Cd := by rw [hCd]; positivity
  refine ⟨max A₀ 0 / Cd + 1, ?_, ?_⟩
  · have : 0 ≤ max A₀ 0 / Cd := div_nonneg (le_max_right _ _) hCdpos.le
    linarith
  · intro τ ζ hτ hdist him hne
    have hmem : (τ, ζ) ∈ spikeSet H := by
      rw [mem_spikeSet]
      exact ⟨le_of_lt (Funnel.re_abs_lt_one hτ), Funnel.im_two hτ, him, hdist⟩
    have hAfun : ‖AfunFun ℓ d τ ζ‖ ≤ max A₀ 0 :=
      le_trans (hA₀ (τ, ζ) hmem) (le_max_left _ _)
    -- lower bound for `‖j τ - j ζ‖`
    set a : ℂ := (ζ : ℂ) - (τ : ℂ) with ha
    have hanorm : ‖a‖ = 29 / 20 := by rw [ha]; exact hdist
    have hP : ((ζ : ℂ) - (τ : ℂ)) * ((ζ : ℂ) - ((τ : ℂ) - 1)) * ((ζ : ℂ) - ((τ : ℂ) + 1))
        = a * (a + 1) * (a - 1) := by
      rw [ha]; ring
    have hprod : (29 / 20) * (9 / 20) * (9 / 20) ≤
        ‖((ζ : ℂ) - (τ : ℂ)) * ((ζ : ℂ) - ((τ : ℂ) - 1)) *
          ((ζ : ℂ) - ((τ : ℂ) + 1))‖ := by
      rw [hP]; exact norm_mul_succ_pred_lower hanorm
    have hexp : Real.exp (4 * Real.pi) ≤ Real.exp (2 * Real.pi * τ.im) := by
      apply Real.exp_le_exp.mpr
      have h2 := Funnel.im_two hτ
      nlinarith [Real.pi_pos]
    have hdiv' := hdiv τ ζ hτ (le_of_eq hdist)
    have hJlower : Cd ≤ ‖jInvariantFun τ - jInvariantFun ζ‖ := by
      rw [hCd]
      calc c * Real.exp (4 * Real.pi) * ((29 / 20) * (9 / 20) * (9 / 20))
          ≤ c * Real.exp (2 * Real.pi * τ.im) *
              ‖((ζ : ℂ) - (τ : ℂ)) * ((ζ : ℂ) - ((τ : ℂ) - 1)) *
                ((ζ : ℂ) - ((τ : ℂ) + 1))‖ := by
            apply mul_le_mul
            · exact mul_le_mul_of_nonneg_left hexp hc.le
            · exact hprod
            · norm_num
            · positivity
        _ ≤ ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun ζ‖ := hdiv'
    have hJpos : 0 < ‖jInvariantFun τ - jInvariantFun ζ‖ := lt_of_lt_of_le hCdpos hJlower
    -- rewrite the kernel and bound
    have hjd : jInvariantFun τ - jInvariantFun ζ ≠ 0 := sub_ne_zero.mpr hne
    have hKrule := Kfun_mul_slope_eq_AfunFun ℓ d hd τ ζ hne
    have hKfun : Kfun ℓ d τ ζ = AfunFun ℓ d τ ζ / (jInvariantFun τ - jInvariantFun ζ) := by
      rw [eq_div_iff hjd]
      exact hKrule
    rw [hKfun, norm_div]
    calc ‖AfunFun ℓ d τ ζ‖ / ‖jInvariantFun τ - jInvariantFun ζ‖
        ≤ max A₀ 0 / ‖jInvariantFun τ - jInvariantFun ζ‖ :=
          div_le_div_of_nonneg_right hAfun (norm_nonneg _)
      _ ≤ max A₀ 0 / Cd :=
          div_le_div_of_nonneg_left (le_max_right _ _) hCdpos hJlower
      _ ≤ max A₀ 0 / Cd + 1 := by linarith

end

end Work.Asymptotics.SpikeCircle
