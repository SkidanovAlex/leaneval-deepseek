import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.row15_defs
import Submission.Work.Spaces.sin_rpow_le_majorant_pi
import Submission.Work.Spaces.integrableOn_majorant_rpow
import Submission.Work.Spaces.integral_majorant_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The angular bookkeeping weight `Gwt` of row 15 is integrable, with `∫_θ Gwt ≤ 2000/α`

`Gwt α θ = Γ(θ)² · (5 sin(2θ)^{-η} + 30 sin(2θ)^{-γ})` with
`Γ(θ) = (sin θ cos²θ)^{α/3}`, `η = 99/100` and `γ = 1 + α/10`.  Both singular
factors are *not* integrable on their own (`sin(2θ)^{-γ}` blows up like `θ^{-1-α/10}`
at `θ = 0`), but the vanishing of `Γ(θ)² ~ θ^{2α/3}` supplies exactly the missing
power.

The route is the already proved `Gam_sq_mul_sin_rpow_le`, which turns `Γ(θ)² sin(2θ)^{-q}`
into the single `rpow` weight `sin(2θ)^{2α/5 - q}` as soon as `q ≥ 2α/5`:

* `q = η`: `Γ² sin^{-η} ≤ sin^{2α/5-η}`, exponent `> -η > -1`, integrable with a
  *constant* integral;
* `q = γ`: `Γ² sin^{-γ} ≤ sin^{2α/5-γ} = sin^{3α/10-1}`, integrable with integral
  `≲ 1/α`.

For the quantitative form we need the sharp constant `π` in the elementary estimate
`∫_θ sin(2θ)^p ≤ π/(p+1)` (`p ∈ (-1,0]`), not the lossy `100` of
`Work.Spaces.sin_two_rpow`: with it the total is
`5π/(2α/5+1/100) + 30π/(3α/10) ≤ 225π/(2α) ≤ 2000/α`.

Everything here is aimed at the row-15 bound `HkSq α 4 f ≤ 10¹² K² (Cs+1)² α⁴`
described in `row15_defs.lean`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP.row15aux

set_option autoImplicit false

/-- The sharp form of `Work.Spaces.sin_two_rpow`: for `-1 < p ≤ 0` the function
`θ ↦ sin(2θ)^p` is integrable on `Iθ` and its integral is at most `π/(p+1)`.

(The sibling `Work.Spaces.sin_two_rpow` proves `≤ 100/(p+1)` by forgetting the
factor `π ≤ 4` in the majorant `π (1/2)^{-p}/(1+p)`; the row-15 bookkeeping needs
the `1/α`-rate, so here the sharper constant is kept.) -/
theorem sin_two_rpow_le_pi_div (p : ℝ) (hp : -1 < p) (hp0 : p ≤ 0) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ p) Work.Spaces.Iθ ∧
      ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ p ≤ Real.pi / (p + 1) := by
  rcases eq_or_lt_of_le hp0 with hp_eq | hp_lt
  · -- The exponent vanishes: the integrand is the constant `1`.
    subst hp_eq
    constructor
    · simpa only [Real.rpow_zero] using
        (MeasureTheory.integrableOn_const (μ := volume) (s := Work.Spaces.Iθ) (C := (1:ℝ))
          (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
    · have hvol : volume.real Work.Spaces.Iθ = Real.pi / 2 := by
        rw [MeasureTheory.measureReal_def, Work.Spaces.Iθ, Real.volume_Icc,
            ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
        ring
      have hconst : ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (0:ℝ)
          = volume.real Work.Spaces.Iθ := by
        simp only [Real.rpow_zero]
        rw [MeasureTheory.setIntegral_const]
        simp
      rw [hconst, hvol, zero_add, div_one]
      linarith [Real.pi_pos]
  · -- The exponent is negative: dominate by the integrable Jordan majorant.
    set q : ℝ := -p with hq
    have hq0 : 0 < q := by rw [hq]; linarith
    have hq1 : q < 1 := by rw [hq]; linarith
    have hpq : p = -q := by rw [hq]; ring
    -- The majorant, its integrability and its integral.
    have hGint : Integrable (fun θ : ℝ => (Real.pi/4)^q * (θ^(-q) + (Real.pi/2 - θ)^(-q)))
        (volume.restrict Work.Spaces.Iθ) := by
      rw [Work.Spaces.Iθ]; exact Work.Spaces.integrableOn_majorant_rpow q hq0 hq1
    have hGval : ∫ θ in Work.Spaces.Iθ, ((Real.pi/4)^q * (θ^(-q) + (Real.pi/2 - θ)^(-q)))
        = Real.pi * (1/2)^q / (1 - q) := by
      rw [Work.Spaces.Iθ]; exact Work.Spaces.integral_majorant_rpow q hq0 hq1
    -- Nonnegativity of the integrand on `Iθ`.
    have hnonneg : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ] (fun θ : ℝ => (Real.sin (2*θ))^p) := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      exact Real.rpow_nonneg
        (Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) p
    -- The pointwise majorant.
    have hpoint : (fun θ : ℝ => (Real.sin (2*θ))^p) ≤ᵐ[volume.restrict Work.Spaces.Iθ]
        (fun θ : ℝ => (Real.pi/4)^q * (θ^(-q) + (Real.pi/2 - θ)^(-q))) := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      rw [hpq]
      exact Work.Spaces.sin_rpow_le_majorant_pi q θ hq0 hθ
    -- Measurability of the integrand.
    have hmeas : AEStronglyMeasurable (fun θ : ℝ => (Real.sin (2*θ))^p)
        (volume.restrict Work.Spaces.Iθ) :=
      (Measurable.pow_const (Real.measurable_sin.comp (measurable_const.mul measurable_id)) p)
        |>.aestronglyMeasurable
    -- Domination of the norms, as required by `Integrable.mono'`.
    have hnorm : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        ‖(Real.sin (2*θ))^p‖ ≤ (Real.pi/4)^q * (θ^(-q) + (Real.pi/2 - θ)^(-q)) := by
      filter_upwards [hpoint, hnonneg] with θ h1 h2
      rw [Real.norm_of_nonneg h2]
      exact h1
    constructor
    · exact hGint.mono' hmeas hnorm
    · calc ∫ θ in Work.Spaces.Iθ, (Real.sin (2*θ))^p
          ≤ ∫ θ in Work.Spaces.Iθ, ((Real.pi/4)^q * (θ^(-q) + (Real.pi/2 - θ)^(-q))) :=
            integral_mono_of_nonneg hnonneg hGint hpoint
        _ = Real.pi * (1/2)^q / (1 - q) := hGval
        _ ≤ Real.pi / (p + 1) := by
            rw [hpq]
            rw [show -q + 1 = 1 - q by ring]
            have h1 : (1/2:ℝ)^q ≤ 1 :=
              Real.rpow_le_one (by norm_num) (by norm_num) (le_of_lt hq0)
            have h2 : Real.pi * (1/2:ℝ)^q ≤ Real.pi := by
              simpa using mul_le_mul_of_nonneg_left h1 (le_of_lt Real.pi_pos)
            exact div_le_div_of_nonneg_right h2 (by linarith)

/-- `Gwt α` is measurable (it is a product of `rpow`s of measurable functions). -/
theorem measurable_Gwt (α : ℝ) : Measurable (fun θ : ℝ => Gwt α θ) := by
  have hGam : Measurable (fun θ : ℝ => Work.Spaces.Gam α θ) := by
    simp only [Work.Spaces.Gam]
    exact (Real.measurable_sin.mul (Real.measurable_cos.pow_const 2)).pow_const (α / 3)
  simp only [Gwt]
  refine (hGam.pow_const 2).mul ?_
  refine Measurable.add ?_ ?_
  · exact ((Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const
      (-Work.Spaces.eta)).const_mul 5
  · exact ((Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const
      (-Work.Spaces.gam α)).const_mul 30

/-- The pointwise (a.e.) domination of `Gwt` by the two single `rpow` weights coming
from `Gam_sq_mul_sin_rpow_le`. -/
theorem Gwt_le_rpow_sum {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      Gwt α θ ≤ 5 * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.eta)
        + 30 * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α) := by
  have hIoo : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0:ℝ) (π/2) := by
    rw [Work.Spaces.Iθ, ← Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [hIoo] with θ hθ
  have h1 : (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
      ≤ (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.eta) := by
    apply Gam_sq_mul_sin_rpow_le hα hθ
    rw [Work.Spaces.eta]; linarith
  have h2 : (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.gam α)
      ≤ (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α) := by
    apply Gam_sq_mul_sin_rpow_le hα hθ
    rw [Work.Spaces.gam]; linarith
  calc Gwt α θ
      = 5 * ((Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
        + 30 * ((Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.gam α)) := by
        rw [Gwt]; ring
    _ ≤ 5 * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.eta)
        + 30 * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num))
          (mul_le_mul_of_nonneg_left h2 (by norm_num))

theorem Gwt_integrableOn_and_integral_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    MeasureTheory.IntegrableOn
        (fun θ : ℝ => Work.FTS.Nonlinear.Pieces.RNP.row15aux.Gwt α θ) Work.Spaces.Iθ ∧
      ∫ θ in Work.Spaces.Iθ, Work.FTS.Nonlinear.Pieces.RNP.row15aux.Gwt α θ ≤ 2000 / α := by
  -- The admissible exponents of the two `rpow` majorants.
  have hp1 : (-1 : ℝ) < 2 * α / 5 - Work.Spaces.eta := by rw [Work.Spaces.eta]; linarith
  have hp1' : 2 * α / 5 - Work.Spaces.eta ≤ 0 := by rw [Work.Spaces.eta]; linarith
  have hp2 : (-1 : ℝ) < 2 * α / 5 - Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have hp2' : 2 * α / 5 - Work.Spaces.gam α ≤ 0 := by rw [Work.Spaces.gam]; linarith
  obtain ⟨hI1, hI1'⟩ :=
    sin_two_rpow_le_pi_div (2 * α / 5 - Work.Spaces.eta) hp1 hp1'
  obtain ⟨hI2, hI2'⟩ :=
    sin_two_rpow_le_pi_div (2 * α / 5 - Work.Spaces.gam α) hp2 hp2'
  -- Integrability of the majorant.
  have hIntmaj : Integrable (fun θ : ℝ =>
      5 * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.eta)
        + 30 * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))
      (volume.restrict Work.Spaces.Iθ) :=
    (Integrable.const_mul hI1 5).add (Integrable.const_mul hI2 30)
  -- Nonnegativity on `Iθ`.
  have hnn : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ] (fun θ : ℝ => Gwt α θ) := by
    rw [Work.Spaces.Iθ] at *
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    exact Gwt_nonneg hα hθ
  have hpt := Gwt_le_rpow_sum hα hα1
  have hnorm : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      ‖Gwt α θ‖ ≤ 5 * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.eta)
        + 30 * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α) := by
    filter_upwards [hnn, hpt] with θ hn hp
    rwa [Real.norm_of_nonneg hn]
  refine ⟨?_, ?_⟩
  · exact hIntmaj.mono' (measurable_Gwt α).aestronglyMeasurable hnorm
  · calc ∫ θ in Work.Spaces.Iθ, Gwt α θ
        ≤ ∫ θ in Work.Spaces.Iθ, (5 * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.eta)
            + 30 * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)) :=
          integral_mono_of_nonneg hnn hIntmaj hpt
      _ = 5 * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.eta))
            + 30 * (∫ θ in Work.Spaces.Iθ,
                (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)) := by
          rw [integral_add (Integrable.const_mul hI1 5) (Integrable.const_mul hI2 30),
            integral_const_mul, integral_const_mul]
      _ ≤ 5 * (Real.pi / ((2 * α / 5 - Work.Spaces.eta) + 1))
            + 30 * (Real.pi / ((2 * α / 5 - Work.Spaces.gam α) + 1)) :=
          add_le_add (mul_le_mul_of_nonneg_left hI1' (by norm_num))
            (mul_le_mul_of_nonneg_left hI2' (by norm_num))
      _ ≤ 2000 / α := by
          have hA : (2 * α / 5 - Work.Spaces.eta) + 1 = 2 * α / 5 + 1 / 100 := by
            rw [Work.Spaces.eta]; ring
          have hB : (2 * α / 5 - Work.Spaces.gam α) + 1 = 3 * α / 10 := by
            rw [Work.Spaces.gam]; ring
          rw [hA, hB]
          have hpos1 : (0:ℝ) < 2 * α / 5 := by linarith
          have hle1 : 2 * α / 5 ≤ 2 * α / 5 + 1 / 100 := by norm_num
          have hstep1 : Real.pi / (2 * α / 5 + 1 / 100) ≤ Real.pi / (2 * α / 5) :=
            div_le_div_of_nonneg_left (le_of_lt Real.pi_pos) hpos1 hle1
          have h1 : 5 * (Real.pi / (2 * α / 5 + 1 / 100)) ≤ 25 * Real.pi / (2 * α) := by
            calc 5 * (Real.pi / (2 * α / 5 + 1 / 100))
                ≤ 5 * (Real.pi / (2 * α / 5)) :=
                  mul_le_mul_of_nonneg_left hstep1 (by norm_num)
              _ = 25 * Real.pi / (2 * α) := by field_simp; ring
          have h2 : 30 * (Real.pi / (3 * α / 10)) = 100 * Real.pi / α := by
            field_simp; ring
          have h3 : 25 * Real.pi / (2 * α) + 100 * Real.pi / α ≤ 2000 / α := by
            have h22 : 25 * Real.pi / (2 * α) + 100 * Real.pi / α = (225 * Real.pi / 2) / α := by
              field_simp; ring
            rw [h22]
            apply div_le_div_of_nonneg_right _ (le_of_lt hα)
            nlinarith [Real.pi_le_four]
          linarith [h1, h2, h3]

end Work.FTS.Nonlinear.Pieces.RNP.row15aux
