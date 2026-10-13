import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.cs_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Weighted Cauchy–Schwarz for the angular moment `∫_θ |u|·sinθcos²θ`

The angular profile of the elliptic problem is `sinCos2 θ = sinθ·cos²θ` and the `i = 0`
angular weight is `sEta θ = sin(2θ)^{-η}` with `η = 99/100` (`Work.Spaces.Iθ = [0,π/2]`).

This file proves `sinCos2_cs_sEta`: for `u` whose weighted square `u²·sEta` is integrable on
`Iθ` and which is a.e. strongly measurable,

* `sinCos2²/sEta` is integrable on `Iθ` with nonnegative integral (it is bounded by `1`: on
  `(0,π/2)` it equals `sinCos2²·sin(2θ)^η ≤ 1`, and the two endpoints are null);
* `|u|·sinCos2` is integrable on `Iθ`;
* `(∫_θ |u|·sinCos2)² ≤ (∫_θ sinCos2²/sEta)·(∫_θ u²·sEta)`,

the last being the sharp weighted Cauchy–Schwarz inequality with the two `L²` factors
`√(u²·sEta)` and `√(sinCos2²/sEta)` (their product is `|u|·sinCos2`, since `sinCos2 ≥ 0` on
`Iθ` and `sEta > 0` on the open interval, which is co-null in `Iθ`).

Everything reduces to the open interval `(0,π/2)` through the equality of the restrictions
of Lebesgue measure, because there `sEta` is strictly positive.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Mine

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Elementary facts on the open interval and on `Iθ` -/

/-- `sin(2θ) > 0` on the open angular interval. -/
private theorem sin_two_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `sEta θ ≥ 0` on `Iθ`. -/
private theorem sEta_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.sEta θ := by
  rw [Work.FTS.EllipticEst.sEta]
  exact Real.rpow_nonneg
    (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])) _

/-- `sEta θ > 0` on the open interval. -/
private theorem sEta_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Work.FTS.EllipticEst.sEta θ := by
  rw [Work.FTS.EllipticEst.sEta]
  exact Real.rpow_pos_of_pos (sin_two_pos_of_mem_Ioo hθ) _

/-- On the open interval, the reciprocal of `sEta θ` is `sin(2θ)^η`. -/
private theorem inv_sEta_eq_rpow_of_mem_Ioo {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (Work.FTS.EllipticEst.sEta θ)⁻¹ = (Real.sin (2 * θ)) ^ Work.Spaces.eta := by
  rw [Work.FTS.EllipticEst.sEta, Real.rpow_neg (le_of_lt (sin_two_pos_of_mem_Ioo hθ)), inv_inv]

/-- `sinθcos²θ ≥ 0` on `Iθ`. -/
private theorem sinCos2_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.Elliptic.sinCos2 θ := by
  rw [Work.Elliptic.sinCos2]
  exact mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos]))
    (sq_nonneg _)

/-- On the open interval, `sinCos2²/sEta = sinCos2²·sin(2θ)^η`. -/
private theorem sinCos2_sq_div_sEta_eq_mul_rpow {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (Work.Elliptic.sinCos2 θ) ^ 2 / Work.FTS.EllipticEst.sEta θ
      = (Work.Elliptic.sinCos2 θ) ^ 2 * (Real.sin (2 * θ)) ^ Work.Spaces.eta := by
  rw [div_eq_mul_inv, inv_sEta_eq_rpow_of_mem_Ioo hθ]

/-- The open interval `(0,π/2)` and `Iθ = [0,π/2]` carry the same restriction of Lebesgue
measure: they differ by the two null points `0` and `π/2`. -/
private theorem restrict_Ioo_eq_restrict_Iθ :
    volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) = volume.restrict Work.Spaces.Iθ :=
  MeasureTheory.Measure.restrict_congr_set
    (by rw [Work.Spaces.Iθ]; exact MeasureTheory.Ioo_ae_eq_Icc)

/-- `θ ↦ sinθcos²θ` is continuous. -/
private theorem continuous_sinCos2_fts : Continuous (fun θ : ℝ => Work.Elliptic.sinCos2 θ) := by
  rw [show (fun θ : ℝ => Work.Elliptic.sinCos2 θ)
      = fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2 from rfl]
  fun_prop

/-- `θ ↦ sinCos2 θ²·sin(2θ)^η` is continuous on `Iθ` (where `η ≥ 0`). -/
private theorem continuousOn_sinCos2_sq_mul_rpow_Iθ :
    ContinuousOn (fun θ : ℝ => (Work.Elliptic.sinCos2 θ) ^ 2
      * (Real.sin (2 * θ)) ^ Work.Spaces.eta) Work.Spaces.Iθ := by
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) Work.Spaces.Iθ :=
    Real.continuous_sin.comp_continuousOn ((continuous_const.mul continuous_id).continuousOn)
  have hrpow : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ Work.Spaces.eta)
      Work.Spaces.Iθ :=
    hsin.rpow_const (fun _ _ => Or.inr (by norm_num [Work.Spaces.eta]))
  exact ((continuous_sinCos2_fts.pow 2).continuousOn).mul hrpow

/-- `|sinCos2 θ²·sin(2θ)^η| ≤ 1` on the open interval. -/
private theorem abs_sinCos2_sq_mul_rpow_le_one {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    ‖(Work.Elliptic.sinCos2 θ) ^ 2 * (Real.sin (2 * θ)) ^ Work.Spaces.eta‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_mul]
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hrpow_le : (Real.sin (2 * θ)) ^ Work.Spaces.eta ≤ 1 :=
    Real.rpow_le_one (le_of_lt (sin_two_pos_of_mem_Ioo hθ)) hs1 (by norm_num [Work.Spaces.eta])
  have hcabs : |Work.Elliptic.sinCos2 θ| ≤ 1 := by
    rw [Work.Elliptic.sinCos2, abs_mul, abs_of_nonneg (sq_nonneg (Real.cos θ))]
    have ha : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
    have hb : Real.cos θ ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one _).mpr (Real.abs_cos_le_one θ)
    calc |Real.sin θ| * Real.cos θ ^ 2 ≤ 1 * 1 := mul_le_mul ha hb (sq_nonneg _) zero_le_one
      _ = 1 := by ring
  have hcsq : |(Work.Elliptic.sinCos2 θ) ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact (sq_le_one_iff_abs_le_one _).mpr hcabs
  have hrpow_abs : |(Real.sin (2 * θ)) ^ Work.Spaces.eta| ≤ 1 := by
    rw [abs_of_nonneg (Real.rpow_nonneg (le_of_lt (sin_two_pos_of_mem_Ioo hθ)) _)]
    exact hrpow_le
  calc |(Work.Elliptic.sinCos2 θ) ^ 2| * |(Real.sin (2 * θ)) ^ Work.Spaces.eta| ≤ 1 * 1 :=
        mul_le_mul hcsq hrpow_abs (abs_nonneg _) zero_le_one
    _ = 1 := by ring

/-! ## Integrability of the `sinCos2²/sEta` factor -/

/-- `sinCos2²/sEta` is integrable on `Iθ`. -/
private theorem integrableOn_sinCos2_sq_div_sEta :
    IntegrableOn
      (fun θ : ℝ => (Work.Elliptic.sinCos2 θ) ^ 2 / Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
  have hIθ_meas : MeasurableSet Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  have hFin : IsFiniteMeasure (volume.restrict Work.Spaces.Iθ) :=
    ⟨by rw [Measure.restrict_apply_univ, Work.Spaces.Iθ, Real.volume_Icc]
        exact ENNReal.ofReal_lt_top⟩
  -- the auxiliary continuous function `sinCos2²·sin(2θ)^η`
  have haesm : AEStronglyMeasurable (fun θ : ℝ => (Work.Elliptic.sinCos2 θ) ^ 2
      * (Real.sin (2 * θ)) ^ Work.Spaces.eta) (volume.restrict Work.Spaces.Iθ) :=
    continuousOn_sinCos2_sq_mul_rpow_Iθ.aestronglyMeasurable hIθ_meas
  have hint : Integrable (fun θ : ℝ => (Work.Elliptic.sinCos2 θ) ^ 2
      * (Real.sin (2 * θ)) ^ Work.Spaces.eta) (volume.restrict Work.Spaces.Iθ) := by
    refine MeasureTheory.Integrable.of_bound haesm 1 ?_
    filter_upwards [ae_restrict_mem hIθ_meas] with θ hθ
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · subst h0
      rw [show (Work.Elliptic.sinCos2 0) = 0 from by
        rw [Work.Elliptic.sinCos2, Real.sin_zero]; ring]
      simp
    rcases eq_or_lt_of_le hθ.2 with h1 | h1
    · subst h1
      rw [show (Work.Elliptic.sinCos2 (Real.pi / 2)) = 0 from by
        rw [Work.Elliptic.sinCos2, Real.cos_pi_div_two]; ring]
      simp
    · exact abs_sinCos2_sq_mul_rpow_le_one ⟨h0, h1⟩
  -- transfer to `sinCos2²/sEta`, equal a.e. (and everywhere on the open interval)
  refine hint.congr ?_
  filter_upwards [ae_restrict_mem hIθ_meas] with θ hθ
  rcases eq_or_lt_of_le hθ.1 with h0 | h0
  · subst h0
    rw [show (Work.Elliptic.sinCos2 0) = 0 from by
        rw [Work.Elliptic.sinCos2, Real.sin_zero]; ring,
      show Work.FTS.EllipticEst.sEta 0 = 0 from by
        rw [Work.FTS.EllipticEst.sEta, show (2 : ℝ) * 0 = 0 from by ring, Real.sin_zero,
          Real.zero_rpow (by norm_num [Work.Spaces.eta])]]
    simp
  rcases eq_or_lt_of_le hθ.2 with h1 | h1
  · subst h1
    rw [show (Work.Elliptic.sinCos2 (Real.pi / 2)) = 0 from by
      rw [Work.Elliptic.sinCos2, Real.cos_pi_div_two]; ring]
    simp
  · exact (sinCos2_sq_div_sEta_eq_mul_rpow ⟨h0, h1⟩).symm

/-! ## The a.e. factorisation of the integrand -/

/-- The product of the two `L²` factors `√(u²·sEta)` and `√(sinCos2²/sEta)` is `|u|·sinCos2`
a.e. on `Iθ` (on the open interval `sEta > 0` and `sinCos2 ≥ 0`). -/
private theorem ae_sqrt_prod_eq_abs_mul {u : ℝ → ℝ} :
    (fun θ : ℝ => Real.sqrt ((u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        * Real.sqrt ((Work.Elliptic.sinCos2 θ) ^ 2 / Work.FTS.EllipticEst.sEta θ))
      =ᵐ[volume.restrict Work.Spaces.Iθ] (fun θ : ℝ => |u θ| * Work.Elliptic.sinCos2 θ) := by
  rw [← restrict_Ioo_eq_restrict_Iθ]
  refine ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
  beta_reduce
  have hs : 0 < Work.FTS.EllipticEst.sEta θ := sEta_pos_of_mem_Ioo hθ
  have hu2 : 0 ≤ (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := mul_nonneg (sq_nonneg _) hs.le
  have hc : 0 ≤ Work.Elliptic.sinCos2 θ :=
    sinCos2_nonneg_of_mem_Iθ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  rw [← Real.sqrt_mul hu2]
  have hmul : (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
      * ((Work.Elliptic.sinCos2 θ) ^ 2 / Work.FTS.EllipticEst.sEta θ)
      = (u θ * Work.Elliptic.sinCos2 θ) ^ 2 := by
    field_simp
  rw [hmul, Real.sqrt_sq_eq_abs, abs_mul, abs_of_nonneg hc]

/-! ## The main estimate -/

theorem sinCos2_cs_sEta {u : ℝ → ℝ}
    (hu : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ)
    (hmeasu : MeasureTheory.AEStronglyMeasurable u (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Work.Elliptic.sinCos2 θ) ^ 2 / Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ
      ∧ 0 ≤ ∫ θ in Work.Spaces.Iθ, (Work.Elliptic.sinCos2 θ) ^ 2 / Work.FTS.EllipticEst.sEta θ
      ∧ MeasureTheory.IntegrableOn (fun θ : ℝ => |u θ| * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ
      ∧ (∫ θ in Work.Spaces.Iθ, |u θ| * Work.Elliptic.sinCos2 θ) ^ 2
          ≤ (∫ θ in Work.Spaces.Iθ, (Work.Elliptic.sinCos2 θ) ^ 2 / Work.FTS.EllipticEst.sEta θ)
            * ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
  have hIθ_meas : MeasurableSet Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  -- a.e. nonnegativity of the two `L²` squares
  have hnn : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      0 ≤ (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
    (ae_restrict_mem hIθ_meas).mono
      (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg_of_mem_Iθ hθ))
  have hnnC : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      0 ≤ (Work.Elliptic.sinCos2 θ) ^ 2 / Work.FTS.EllipticEst.sEta θ :=
    (ae_restrict_mem hIθ_meas).mono
      (fun θ hθ => div_nonneg (sq_nonneg _) (sEta_nonneg_of_mem_Iθ hθ))
  -- ## the first `L²` factor `√(u²·sEta)`
  have hA_mem : MemLp (fun θ : ℝ => Real.sqrt ((u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) 2
      (volume.restrict Work.Spaces.Iθ) := by
    refine (memLp_two_iff_integrable_sq ?_).mpr ?_
    · exact Real.continuous_sqrt.comp_aestronglyMeasurable hu.aestronglyMeasurable
    · exact hu.congr (hnn.mono (fun θ hθ => (Real.sq_sqrt hθ).symm))
  -- ## the second `L²` factor `√(sinCos2²/sEta)`
  have hDiv_aesm : AEStronglyMeasurable
      (fun θ : ℝ => (Work.Elliptic.sinCos2 θ) ^ 2 / Work.FTS.EllipticEst.sEta θ)
      (volume.restrict Work.Spaces.Iθ) := by
    rw [← restrict_Ioo_eq_restrict_Iθ]
    refine ((continuousOn_sinCos2_sq_mul_rpow_Iθ.mono
      (fun θ hθ => ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)).aestronglyMeasurable
        measurableSet_Ioo).congr ?_
    exact ae_restrict_of_forall_mem measurableSet_Ioo
      (fun θ hθ => (sinCos2_sq_div_sEta_eq_mul_rpow hθ).symm)
  have hB_mem : MemLp
      (fun θ : ℝ => Real.sqrt ((Work.Elliptic.sinCos2 θ) ^ 2 / Work.FTS.EllipticEst.sEta θ)) 2
      (volume.restrict Work.Spaces.Iθ) := by
    refine (memLp_two_iff_integrable_sq ?_).mpr ?_
    · exact Real.continuous_sqrt.comp_aestronglyMeasurable hDiv_aesm
    · exact (integrableOn_sinCos2_sq_div_sEta).congr
        (hnnC.mono (fun θ hθ => (Real.sq_sqrt hθ).symm))
  -- ## Cauchy–Schwarz
  have hcs := Work.Spaces.cs_integral hA_mem hB_mem
  have e1 : (∫ θ in Work.Spaces.Iθ, Real.sqrt ((u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        * Real.sqrt ((Work.Elliptic.sinCos2 θ) ^ 2 / Work.FTS.EllipticEst.sEta θ))
      = ∫ θ in Work.Spaces.Iθ, |u θ| * Work.Elliptic.sinCos2 θ :=
    integral_congr_ae ae_sqrt_prod_eq_abs_mul
  have e2 : (∫ θ in Work.Spaces.Iθ,
        (Real.sqrt ((u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) ^ 2)
      = ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
    integral_congr_ae (hnn.mono (fun θ hθ => Real.sq_sqrt hθ))
  have e3 : (∫ θ in Work.Spaces.Iθ,
        (Real.sqrt ((Work.Elliptic.sinCos2 θ) ^ 2 / Work.FTS.EllipticEst.sEta θ)) ^ 2)
      = ∫ θ in Work.Spaces.Iθ,
          (Work.Elliptic.sinCos2 θ) ^ 2 / Work.FTS.EllipticEst.sEta θ :=
    integral_congr_ae (hnnC.mono (fun θ hθ => Real.sq_sqrt hθ))
  have hmain : (∫ θ in Work.Spaces.Iθ, |u θ| * Work.Elliptic.sinCos2 θ) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, (Work.Elliptic.sinCos2 θ) ^ 2 / Work.FTS.EllipticEst.sEta θ)
        * ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
    rw [e1, e2, e3] at hcs
    rw [mul_comm (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)] at hcs
    exact hcs
  -- ## integrability of the moment integrand
  have hProd : Integrable (fun θ : ℝ => Real.sqrt ((u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      * Real.sqrt ((Work.Elliptic.sinCos2 θ) ^ 2 / Work.FTS.EllipticEst.sEta θ))
      (volume.restrict Work.Spaces.Iθ) := hA_mem.integrable_mul hB_mem
  have hAbsInt : IntegrableOn (fun θ : ℝ => |u θ| * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ := hProd.congr ae_sqrt_prod_eq_abs_mul
  have hCnonneg : 0 ≤ ∫ θ in Work.Spaces.Iθ,
      (Work.Elliptic.sinCos2 θ) ^ 2 / Work.FTS.EllipticEst.sEta θ :=
    integral_nonneg_of_ae hnnC
  exact ⟨integrableOn_sinCos2_sq_div_sEta, hCnonneg, hAbsInt, hmain⟩

end Work.FTS.EllipticEst.Mine
