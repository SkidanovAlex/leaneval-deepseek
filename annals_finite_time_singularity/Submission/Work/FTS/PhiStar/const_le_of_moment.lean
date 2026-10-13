/-
# The constant in a decomposition orthogonal to `sin 2θ · sin θ cos²θ`

If `v = w + c` on the open interval `(0, π/2)`, if `|w| ≤ M` on `[0, π/2]` and if the
`sin 2θ·sinθcos²θ`-moment of `v` vanishes, then the constant `c` is bounded by `M`.

The point is that the weight `g(θ) = sin 2θ · sinθcos²θ` is nonnegative on `Iθ` and has
strictly positive integral `4/15` there (`Work.Elliptic.integral_sin_two_mul_sinCos2`), so

`0 = ∫ g·v = ∫ g·w + c·∫ g = ∫ g·w + c·(4/15)`,

hence `c = -(15/4)·∫ g·w` and `|c| ≤ (15/4)·M·(4/15) = M`.

The function `v` is only related to `w + c` on the *open* interval; this is harmless because
`g` vanishes at both endpoints, so the two integrands agree a.e. on `Iθ`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.PhiStar.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- `sin θ ≥ 0` on `Iθ = [0, π/2]`. -/
private lemma sin_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin θ := by
  rw [Work.Spaces.Iθ] at hθ
  exact Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩

/-- `sin (2θ) ≥ 0` on `Iθ = [0, π/2]`. -/
private lemma sin_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) := by
  rw [Work.Spaces.Iθ] at hθ
  exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- `sinθ cos²θ ≥ 0` on `Iθ = [0, π/2]`. -/
private lemma sinCos2_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.Elliptic.sinCos2 θ := by
  rw [Work.Elliptic.sinCos2]
  exact mul_nonneg (sin_nonneg_of_mem_Iθ hθ) (sq_nonneg _)

theorem const_le_of_moment {v w : ℝ → ℝ} {c M : ℝ}
    (hvw : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), v θ = w θ + c)
    (hw : ∀ θ ∈ Work.Spaces.Iθ, |w θ| ≤ M)
    (hwmeas : MeasureTheory.AEStronglyMeasurable w (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hmom : ∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) * v θ * Work.Elliptic.sinCos2 θ = 0) :
    |c| ≤ M := by
  have hIθ_meas : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  -- `M` is nonnegative: apply the bound to any point of `Iθ`.
  have hMnn : 0 ≤ M := le_trans (abs_nonneg (w 0)) (hw 0 Work.Spaces.zero_mem_Iθ)
  -- The weight `g θ = sin 2θ · sinθcos²θ` is nonnegative and bounded by `1` on `Iθ`.
  have hg_nonneg : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ :=
    fun θ hθ => mul_nonneg (sin_two_nonneg_of_mem_Iθ hθ) (sinCos2_nonneg_of_mem_Iθ hθ)
  have hg_abs_le_one : ∀ θ ∈ Work.Spaces.Iθ, |Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ| ≤ 1 := by
    intro θ hθ
    have hsc_le : Work.Elliptic.sinCos2 θ ≤ 1 := by
      rw [Work.Elliptic.sinCos2]
      nlinarith [Real.sin_le_one θ, Real.cos_sq_le_one θ, sin_nonneg_of_mem_Iθ hθ,
        sq_nonneg (Real.cos θ)]
    have hmul : Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ ≤ 1 := by
      have := mul_le_mul (Real.sin_le_one (2 * θ)) hsc_le (sinCos2_nonneg_of_mem_Iθ hθ)
        zero_le_one
      simpa using this
    rw [abs_le]
    exact ⟨by linarith [hg_nonneg θ hθ], hmul⟩
  have hg_cont : Continuous (fun θ : ℝ => Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ) := by
    rw [show (fun θ : ℝ => Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ)
        = (fun θ : ℝ => Real.sin (2 * θ) * (Real.sin θ * Real.cos θ ^ 2)) from rfl]
    fun_prop
  -- Integrability of the two pieces of the split.
  have hgw_int : Integrable (fun θ : ℝ => Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ * w θ)
      (volume.restrict Work.Spaces.Iθ) := by
    refine Integrable.of_bound (hg_cont.aestronglyMeasurable.mul hwmeas) M ?_
    filter_upwards [ae_restrict_mem hIθ_meas] with θ hθ
    rw [Real.norm_eq_abs, abs_mul]
    calc |Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ| * |w θ|
        ≤ 1 * M := mul_le_mul (hg_abs_le_one θ hθ) (hw θ hθ) (abs_nonneg _) zero_le_one
      _ = M := one_mul M
  have hcg_int : Integrable (fun θ : ℝ => c * (Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ))
      (volume.restrict Work.Spaces.Iθ) :=
    ((continuous_const.mul hg_cont).continuousOn).integrableOn_compact isCompact_Icc
  -- The moment splits as `∫ g·w + c·∫ g`.
  have hkey : ∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ * v θ
      = (∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ * w θ)
        + c * (∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ) := by
    have h1 : (fun θ : ℝ => Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ * v θ)
        =ᵐ[volume.restrict (Set.Ioo (0:ℝ) (π / 2))]
        (fun θ : ℝ => Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ * w θ
          + c * (Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      rw [hvw θ hθ]; ring
    have h2 : (fun θ : ℝ => Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ * v θ)
        =ᵐ[volume.restrict Work.Spaces.Iθ]
        (fun θ : ℝ => Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ * w θ
          + c * (Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ)) :=
      (MeasureTheory.ae_restrict_congr_set
        (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0:ℝ)) (b := π / 2))).mp h1
    rw [integral_congr_ae h2, integral_add hgw_int hcg_int, integral_const_mul]
  have h0 : ∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ * v θ = 0 := by
    rw [← hmom]
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    ring
  have hkey2 : (∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ * w θ)
      + c * (4 / 15) = 0 := by
    have h := hkey
    rw [h0, Work.Elliptic.integral_sin_two_mul_sinCos2] at h
    exact h.symm
  have hc_eq : c
      = -(15 / 4) * (∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ * w θ) := by
    linarith [hkey2]
  -- Bound the remaining moment by `M · ∫ g`.
  have hA : |(∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ * w θ)|
      ≤ M * (4 / 15) := by
    have hgwabs_int : Integrable (fun θ : ℝ => Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ * |w θ|)
        (volume.restrict Work.Spaces.Iθ) := by
      refine Integrable.of_bound (hg_cont.aestronglyMeasurable.mul hwmeas.norm) M ?_
      filter_upwards [ae_restrict_mem hIθ_meas] with θ hθ
      rw [Real.norm_eq_abs, abs_mul, abs_abs]
      calc |Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ| * |w θ|
          ≤ 1 * M := mul_le_mul (hg_abs_le_one θ hθ) (hw θ hθ) (abs_nonneg _) zero_le_one
        _ = M := one_mul M
    have hbound : ∫ θ in Work.Spaces.Iθ, ‖Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ * w θ‖
        = ∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ * |w θ| := by
      refine setIntegral_congr_fun hIθ_meas (fun θ hθ => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hg_nonneg θ hθ)]
    have hmono : ∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ * |w θ|
        ≤ ∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ * M := by
      refine setIntegral_mono_on hgwabs_int ?_ hIθ_meas (fun θ hθ => ?_)
      · exact ((hg_cont.mul continuous_const).continuousOn).integrableOn_compact isCompact_Icc
      · exact mul_le_mul_of_nonneg_left (hw θ hθ) (hg_nonneg θ hθ)
    have hstep : |(∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ * w θ)|
        ≤ ∫ θ in Work.Spaces.Iθ, ‖Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ * w θ‖ := by
      rw [← Real.norm_eq_abs]
      exact norm_integral_le_integral_norm _
    calc |(∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ * w θ)|
        ≤ ∫ θ in Work.Spaces.Iθ, ‖Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ * w θ‖ := hstep
      _ = ∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ * |w θ| := hbound
      _ ≤ ∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ * M := hmono
      _ = M * (4 / 15) := by
          rw [integral_mul_const, Work.Elliptic.integral_sin_two_mul_sinCos2]
          ring
  have hfin : |c| ≤ 15 / 4 * (M * (4 / 15)) := by
    rw [hc_eq, abs_mul, abs_neg, abs_of_pos (by norm_num : (0:ℝ) < 15 / 4)]
    exact mul_le_mul_of_nonneg_left hA (by norm_num)
  linarith [hfin]

end Work.FTS.PhiStar
