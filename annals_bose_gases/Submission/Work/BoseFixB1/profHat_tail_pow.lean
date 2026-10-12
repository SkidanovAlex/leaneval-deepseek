import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Algebra.Order.Star.Real
import Submission.Commons.Analysis.Integral.radial_integral_three_Ioi
import Submission.Work.OneBodyKin.ProfHatDecay
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.profHat_tail_pow`

The origin value of the (scale-`1`) unprojected family symbol at the FS cut-off `σ` decays like
`σ^{-7}`:

    `∃ K ≥ 1, ∀ σ ≥ 1, symA 1 (fsKinCoeff σ) 0 ≤ K σ^{-7}`.

At scale `1` and momentum `0` the symbol is the plain `(2π)^{-3}`-multiple of the integral

    `symA 1 F 0 = (2π)^{-3} ∫_p F(‖p‖) · profHat(p)² dp`

(`Work.OneBodyKin.symA` with `ℓ = 1`, `q = 0`), and for `F = fsKinCoeff σ = [· − σ]₊²` the
integrand `(‖p‖ − σ)₊² profHat(p)²` is supported on the exterior of the ball of radius `σ`.  The
decay of `profHat` from `ProfHatDecay` (`|profHat p| ≤ C₀ (1+‖p‖)^{-6}`) turns this into

    `symA 1 (fsKinCoeff σ) 0 ≤ (2π)^{-3} C₀² ∫_{‖p‖ > σ} (1 + ‖p‖)^{-10} dp`,

and the **radial tail estimate** `∫_{‖p‖ > σ} (1+‖p‖)^{-10} dp ≲ σ^{-7}` (the exponent is
`10 − 3`; it is supplied here by spherical coordinates,
`Commons.Analysis.Integral.radial_integral_three_Ioi`, together with the one-dimensional bound
`oneD_tail_ten`) gives the claim.

The reduction `tail bound ⟹ target` is `profHat_tail_pow_of_tail`; the tail estimate itself is a
statement about Lebesgue measure on `ℝ³` alone.
-/

noncomputable section

open MeasureTheory Filter
open scoped Real Topology

namespace Work.BoseFixB1

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000

/-! ## 1. The pointwise domination of the cut-off integrand -/

/-- **The FS cut-off integrand is dominated by the integrable radial weight `(1+‖p‖)^{-10}`.**
Given the decay `|profHat p| ≤ C₀ (1+‖p‖)^{-6}` and `σ ≥ 0`,

    `[‖p‖ − σ]₊² · profHat(p)² ≤ C₀² (1 + ‖p‖)^{-10}`  for every `p`.

Inside the ball (`‖p‖ ≤ σ`) the left side vanishes; outside it, `(‖p‖−σ)² ≤ (1+‖p‖)²` and
`profHat(p)² ≤ C₀²(1+‖p‖)^{-12}`, so the product is at most `C₀²(1+‖p‖)^{-10}`. -/
private lemma fsKinCoeff_mul_profHat_sq_le {C₀ σ : ℝ} (hσ : 0 ≤ σ)
    (hdec : ∀ p : ℝ³, |Work.OneBodyKin.profHat p| ≤ C₀ / (1 + ‖p‖) ^ 6) (p : ℝ³) :
    Submission.BoseGases.fsKinCoeff σ ‖p‖ * (Work.OneBodyKin.profHat p) ^ 2
      ≤ C₀ ^ 2 * (1 + ‖p‖) ^ (-(10 : ℝ)) := by
  have h10 : ((1 + ‖p‖) ^ 10)⁻¹ = (1 + ‖p‖) ^ (-(10 : ℝ)) := by
    rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + ‖p‖)]
    congr 1
    exact (Real.rpow_natCast (1 + ‖p‖) 10).symm
  rw [← h10]
  by_cases hle : ‖p‖ ≤ σ
  · rw [Submission.BoseGases.fsKinCoeff_of_le hle, zero_mul]
    positivity
  · have hlt : σ < ‖p‖ := not_le.mp hle
    rw [Submission.BoseGases.fsKinCoeff_of_lt hσ hlt]
    have hp2 : (Work.OneBodyKin.profHat p) ^ 2 ≤ C₀ ^ 2 * ((1 + ‖p‖) ^ 12)⁻¹ := by
      have hh := pow_le_pow_left₀ (abs_nonneg (Work.OneBodyKin.profHat p)) (hdec p) 2
      rw [sq_abs, div_pow, ← pow_mul] at hh
      norm_num at hh
      rwa [div_eq_mul_inv] at hh
    have hr2 : (‖p‖ - σ) ^ 2 ≤ (1 + ‖p‖) ^ 2 := by
      have h3 : 0 ≤ ‖p‖ - σ := by linarith
      have h4 : ‖p‖ - σ ≤ 1 + ‖p‖ := by linarith [norm_nonneg p]
      exact pow_le_pow_left₀ h3 h4 2
    calc (‖p‖ - σ) ^ 2 * (Work.OneBodyKin.profHat p) ^ 2
        ≤ (1 + ‖p‖) ^ 2 * (C₀ ^ 2 * ((1 + ‖p‖) ^ 12)⁻¹) :=
          mul_le_mul hr2 hp2 (sq_nonneg _) (by positivity)
      _ = C₀ ^ 2 * ((1 + ‖p‖) ^ 2 * ((1 + ‖p‖) ^ 12)⁻¹) := by ring
      _ = C₀ ^ 2 * ((1 + ‖p‖) ^ 10)⁻¹ := by
          congr 1
          field_simp

/-! ## 2. The reduction: the radial tail estimate implies the symbol decay -/

/-- **The tail estimate implies the symbol bound.**  If the radial weight `(1+‖p‖)^{-10}` has a
`σ^{-7}`-decaying tail, then the origin value of the unprojected symbol at the FS cut-off `σ`
does too.  Concretely, with `Kt` the tail constant,

    `symA 1 (fsKinCoeff σ) 0 ≤ max 1 ((2π)^{-3} C₀² Kt) · σ^{-7}`.

The proof: unroll `symA`, replace the integral by the one over `{σ < ‖p‖}` (the integrand
vanishes inside the ball), bound pointwise by `C₀²(1+‖p‖)^{-10}`, and apply the tail estimate. -/
private lemma profHat_tail_pow_of_tail
    (htail : ∃ K : ℝ, 0 ≤ K ∧ ∀ σ : ℝ, 1 ≤ σ →
      (∫ p in {p : ℝ³ | σ < ‖p‖}, (1 + ‖p‖) ^ (-(10 : ℝ))) ≤ K * σ ^ (-(7 : ℝ))) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ σ : ℝ, 1 ≤ σ →
      Work.OneBodyKin.symA 1 (Submission.BoseGases.fsKinCoeff σ) 0 ≤ K * σ ^ (-(7 : ℝ)) := by
  obtain ⟨C₀, _hC₀, hdec⟩ := Work.OneBodyKin.ProfHatDecay
  obtain ⟨Kt, _hKt, htailb⟩ := htail
  refine ⟨max 1 (((2 * Real.pi) ^ 3)⁻¹ * C₀ ^ 2 * Kt), le_max_left _ _, fun σ hσ => ?_⟩
  have hσ0 : 0 < σ := by linarith
  -- the dominating weight is integrable on `ℝ³`
  have hfin : (Module.finrank ℝ ℝ³ : ℝ) < 10 := by
    rw [finrank_euclideanSpace_fin]; norm_num
  have hInt : Integrable (fun p : ℝ³ => C₀ ^ 2 * (1 + ‖p‖) ^ (-(10 : ℝ))) volume :=
    (integrable_one_add_norm (E := ℝ³) (μ := volume) (r := 10) hfin).const_mul (C₀ ^ 2)
  -- unroll `symA` at `ℓ = 1`, `q = 0`
  have hsymA : Work.OneBodyKin.symA 1 (Submission.BoseGases.fsKinCoeff σ) 0
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³,
          Submission.BoseGases.fsKinCoeff σ ‖p‖ * (Work.OneBodyKin.profHat p) ^ 2 := by
    simp only [Work.OneBodyKin.symA, zero_add, inv_one, one_smul]
  rw [hsymA]
  -- the integrand vanishes off `{σ < ‖p‖}`
  have hF0 : ∀ p ∉ {p : ℝ³ | σ < ‖p‖},
      Submission.BoseGases.fsKinCoeff σ ‖p‖ * (Work.OneBodyKin.profHat p) ^ 2 = 0 := by
    intro p hp
    have hle : ‖p‖ ≤ σ := not_lt.mp (fun h => hp h)
    rw [Submission.BoseGases.fsKinCoeff_of_le hle, zero_mul]
  have hstep1 : (∫ p : ℝ³,
        Submission.BoseGases.fsKinCoeff σ ‖p‖ * (Work.OneBodyKin.profHat p) ^ 2)
      = ∫ p in {p : ℝ³ | σ < ‖p‖},
        Submission.BoseGases.fsKinCoeff σ ‖p‖ * (Work.OneBodyKin.profHat p) ^ 2 :=
    (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hF0).symm
  -- monotone comparison with the radial weight
  have hstep2 : (∫ p in {p : ℝ³ | σ < ‖p‖},
        Submission.BoseGases.fsKinCoeff σ ‖p‖ * (Work.OneBodyKin.profHat p) ^ 2)
      ≤ ∫ p in {p : ℝ³ | σ < ‖p‖}, C₀ ^ 2 * (1 + ‖p‖) ^ (-(10 : ℝ)) := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ (hInt.integrableOn) ?_
    · filter_upwards with p
      exact mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg σ ‖p‖) (sq_nonneg _)
    · filter_upwards with p
      exact fsKinCoeff_mul_profHat_sq_le hσ0.le hdec p
  -- the radial tail estimate
  have hstep3 : (∫ p in {p : ℝ³ | σ < ‖p‖}, C₀ ^ 2 * (1 + ‖p‖) ^ (-(10 : ℝ)))
      ≤ C₀ ^ 2 * (Kt * σ ^ (-(7 : ℝ))) := by
    rw [MeasureTheory.integral_const_mul]
    exact mul_le_mul_of_nonneg_left (htailb σ hσ) (sq_nonneg C₀)
  calc ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³,
        Submission.BoseGases.fsKinCoeff σ ‖p‖ * (Work.OneBodyKin.profHat p) ^ 2
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p in {p : ℝ³ | σ < ‖p‖},
          Submission.BoseGases.fsKinCoeff σ ‖p‖ * (Work.OneBodyKin.profHat p) ^ 2 := by
        rw [hstep1]
    _ ≤ ((2 * Real.pi) ^ 3)⁻¹ * ∫ p in {p : ℝ³ | σ < ‖p‖},
          C₀ ^ 2 * (1 + ‖p‖) ^ (-(10 : ℝ)) :=
        mul_le_mul_of_nonneg_left hstep2 (by positivity)
    _ ≤ ((2 * Real.pi) ^ 3)⁻¹ * (C₀ ^ 2 * (Kt * σ ^ (-(7 : ℝ)))) :=
        mul_le_mul_of_nonneg_left hstep3 (by positivity)
    _ = ((2 * Real.pi) ^ 3)⁻¹ * C₀ ^ 2 * Kt * σ ^ (-(7 : ℝ)) := by ring
    _ ≤ max 1 (((2 * Real.pi) ^ 3)⁻¹ * C₀ ^ 2 * Kt) * σ ^ (-(7 : ℝ)) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hσ0.le _)

/-! ## 3. The one-dimensional tail and the assembled tail estimate -/

/-- **The one-dimensional tail integral.**  For `σ ≥ 1`,

    `∫_{σ}^{∞} r² (1+r)^{-10} dr ≤ σ^{-7}/7`.

Indeed `r²(1+r)^{-10} ≤ r^{-8}` for `r > 0` (`1 + r ≥ r` and the exponent `-10` is negative),
and `∫_σ^∞ r^{-8} dr = σ^{-7}/7` (`integral_Ioi_rpow_of_lt`). -/
private lemma oneD_tail_ten : ∃ K : ℝ, 0 ≤ K ∧ ∀ σ : ℝ, 1 ≤ σ →
    (∫ r in Set.Ioi σ, r ^ 2 * (1 + r) ^ (-(10 : ℝ))) ≤ K * σ ^ (-(7 : ℝ)) := by
  refine ⟨1 / 7, by norm_num, fun σ hσ => ?_⟩
  have hσ0 : 0 < σ := by linarith
  have hint : IntegrableOn (fun r : ℝ => r ^ (-(8 : ℝ))) (Set.Ioi σ) :=
    integrableOn_Ioi_rpow_of_lt (show (-(8 : ℝ)) < -1 by norm_num) hσ0
  have hmono : (∫ r in Set.Ioi σ, r ^ 2 * (1 + r) ^ (-(10 : ℝ)))
      ≤ ∫ r in Set.Ioi σ, r ^ (-(8 : ℝ)) := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ hint ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      have hr0 : 0 < r := lt_trans hσ0 hr
      positivity
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      have hr0 : 0 < r := lt_trans hσ0 hr
      have h1 : (1 + r) ^ (-(10 : ℝ)) ≤ r ^ (-(10 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hr0 (by linarith) (by norm_num)
      calc r ^ 2 * (1 + r) ^ (-(10 : ℝ))
          ≤ r ^ 2 * r ^ (-(10 : ℝ)) := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = r ^ (-(8 : ℝ)) := by
            rw [← Real.rpow_natCast r 2, ← Real.rpow_add hr0]
            norm_num
  have hval : (∫ r in Set.Ioi σ, r ^ (-(8 : ℝ))) = (1 / 7) * σ ^ (-(7 : ℝ)) := by
    rw [integral_Ioi_rpow_of_lt (show (-(8 : ℝ)) < -1 by norm_num) hσ0]
    rw [show (-(8 : ℝ)) + 1 = -(7 : ℝ) by norm_num]
    ring
  calc (∫ r in Set.Ioi σ, r ^ 2 * (1 + r) ^ (-(10 : ℝ)))
      ≤ ∫ r in Set.Ioi σ, r ^ (-(8 : ℝ)) := hmono
    _ = (1 / 7) * σ ^ (-(7 : ℝ)) := hval

/-- **The radial tail estimate, from a radial-transfer identity.**  Given the identity expressing
a radial set integral over the exterior of the ball of radius `σ` as `4π` times the corresponding
one-dimensional integral, the weight `(1+‖p‖)^{-10}` has the `σ^{-7}` tail. -/
private lemma radial_tail_ten_of_transfer
    (htr : ∀ {σ : ℝ}, 0 < σ → ∀ f : ℝ → ℝ,
      (∫ p in {p : ℝ³ | σ < ‖p‖}, f ‖p‖)
        = 4 * Real.pi * (∫ r in Set.Ioi σ, r ^ 2 * f r)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ σ : ℝ, 1 ≤ σ →
      (∫ p in {p : ℝ³ | σ < ‖p‖}, (1 + ‖p‖) ^ (-(10 : ℝ))) ≤ K * σ ^ (-(7 : ℝ)) := by
  obtain ⟨K₁, hK₁, h1⟩ := oneD_tail_ten
  refine ⟨4 * Real.pi * K₁, by positivity, fun σ hσ => ?_⟩
  rw [htr (by linarith : (0 : ℝ) < σ) (fun r : ℝ => (1 + r) ^ (-(10 : ℝ)))]
  calc 4 * Real.pi * (∫ r in Set.Ioi σ, r ^ 2 * (1 + r) ^ (-(10 : ℝ)))
      ≤ 4 * Real.pi * (K₁ * σ ^ (-(7 : ℝ))) :=
        mul_le_mul_of_nonneg_left (h1 σ hσ) (by positivity)
    _ = (4 * Real.pi * K₁) * σ ^ (-(7 : ℝ)) := by ring

/-! ## 4. The tail estimate and the target -/

/-- The radial tail estimate for the weight `(1+‖p‖)^{-10}`, obtained from
`Commons.Analysis.Integral.radial_integral_three_Ioi` (spherical coordinates) and the
one-dimensional bound `oneD_tail_ten`. -/
private lemma radial_tail_ten_local : ∃ K : ℝ, 0 ≤ K ∧ ∀ σ : ℝ, 1 ≤ σ →
    (∫ p in {p : ℝ³ | σ < ‖p‖}, (1 + ‖p‖) ^ (-(10 : ℝ))) ≤ K * σ ^ (-(7 : ℝ)) :=
  radial_tail_ten_of_transfer
    (fun hσ f => Commons.Analysis.Integral.radial_integral_three_Ioi f hσ.le)

theorem profHat_tail_pow : ∃ K : ℝ, 1 ≤ K ∧ ∀ σ : ℝ, 1 ≤ σ →
    Work.OneBodyKin.symA 1 (Submission.BoseGases.fsKinCoeff σ) 0 ≤ K * σ ^ (-(7 : ℝ)) :=
  profHat_tail_pow_of_tail radial_tail_ten_local

end Work.BoseFixB1
