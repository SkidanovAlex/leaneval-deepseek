/-
# `FaStep` — the `r`-step with an explicit `r`-dependent profile

The three primed `gs`-rows (`N₁^{gs}, N₂^{gs}, N₃^{gs}`) have slot the *explicit* profile
`F_*` (resp. `∂_θF_*`, `D_zF_*`), so their `θ`-dependence is entirely under control: for
`r > 0` and `θ ∈ (0,π/2)`,

  `|K θ · N_i r θ| ≤ c_i r · M_i r`

with an explicit `c_i` (the profile bound, e.g. `120·α·r/(1+r)²` for `N₁^{gs}`) and `M_i`
the *`r`-dependent* majorant of the `HQo`-coefficient, `M_i r = √(C_A/(γ-1) · Ψ_i r)`,
where `Ψ_i r = ∫_θ HkIntegrand α 4 A_i r θ` is the angular energy of the coefficient `A_i`
of `EllPkgGo` (bound `angSup_le`).

This file performs the generic step from such a pointwise bound to the `L₁₂`-functional

  `Fa N = ∫⁻ r in (0,∞), r⁻¹ · ∫⁻ θ in Iθ, |K θ · N r θ|`

by Cauchy–Schwarz: the profile part `c_i` is squared and integrated (it is an explicit
function of `r`), while the coefficient part `M_i` is paired with its own energy `Ψ_i`
through `Work.FTS.NonlinRows.Rl1.outer_gen`.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.NonlinRows.Rl1.tools

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.NonlinRows.Rl1

set_option autoImplicit false

/-- The angular integral of a pointwise bound that is constant in `θ`:
`∫⁻_θ ∈ Iθ, ofReal d ≤ ofReal d · volume Iθ`. -/
theorem lintegral_const_le_ofReal {d : ℝ} (_hd : 0 ≤ d) :
    (∫⁻ _θ in Work.Spaces.Iθ, ENNReal.ofReal d)
      = ENNReal.ofReal d * ENNReal.ofReal (π / 2) := by
  rw [MeasureTheory.setLIntegral_const, Work.Spaces.Iθ, Real.volume_Icc, sub_zero]

/-- **The `r`-step with an explicit profile.**  If `|K θ · N r θ| ≤ c r · M r` pointwise on
the open quadrant, `(M r)² ≤ C · Ψ r` on `r > 0`, `c` is nonnegative, `r ↦ r⁻¹c r` is
square-integrable and `Ψ` is integrable (and nonnegative), then

  `Fa N ≤ ofReal ((π/2) · √C · (∫Ψ)^{1/2} · (∫(r⁻¹c)²)^{1/2})`.

The factor `π/2` is the angular volume; it is kept explicit so that the caller can choose
its own (harmless) numerical over-estimate. -/
theorem Fa_le_of_profile {N : ℝ → ℝ → ℝ} {c M Ψ : ℝ → ℝ} {C : ℝ}
    (hC : 0 ≤ C)
    (hc : ∀ r, 0 < r → 0 ≤ c r)
    (hMnn : ∀ r, 0 ≤ M r) (hΨnn : ∀ r, 0 ≤ Ψ r)
    (hΨmeas : AEMeasurable Ψ (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (hΨint : MeasureTheory.IntegrableOn Ψ (Set.Ioi (0 : ℝ)))
    (hcmeas : AEMeasurable (fun r => r⁻¹ * c r)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (hcint : MeasureTheory.IntegrableOn (fun r => (r⁻¹ * c r) ^ 2) (Set.Ioi (0 : ℝ)))
    (hMle : ∀ r, 0 < r → (M r) ^ 2 ≤ C * Ψ r)
    (hpt : ∀ r, 0 < r → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Spaces.K θ * N r θ| ≤ c r * M r) :
    Work.FTS.Nonlinear.Pieces.Fa N
      ≤ ENNReal.ofReal (Real.pi / 2 * (Real.sqrt C
          * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), Ψ r)
          * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * c r) ^ 2))) := by
  -- ### the θ-step: the pointwise bound is constant in θ
  have hinner : ∀ r ∈ Set.Ioi (0 : ℝ),
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * N r θ|)
        ≤ ENNReal.ofReal (c r * M r) * ENNReal.ofReal (π / 2) := by
    intro r hr
    have hr0 : 0 < r := hr
    have hcm : 0 ≤ c r * M r := mul_nonneg (hc r hr0) (hMnn r)
    have hae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        ENNReal.ofReal |Work.Spaces.K θ * N r θ| ≤ ENNReal.ofReal (c r * M r) :=
      Work.FTS.Nonlinear.Pieces.rl1Pieces.ae_Iθ_of_forall_Ioo
        (fun θ hθ => ENNReal.ofReal_le_ofReal (hpt r hr0 θ hθ))
    calc (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * N r θ|)
        ≤ ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (c r * M r) :=
          MeasureTheory.lintegral_mono_ae hae
      _ = ENNReal.ofReal (c r * M r) * ENNReal.ofReal (π / 2) :=
          lintegral_const_le_ofReal hcm
  -- ### the extension of `r ↦ r⁻¹c r` to all of `ℝ`, used by `outer_gen`
  set θw : ℝ → ℝ := (Set.Ioi (0 : ℝ)).indicator (fun r => r⁻¹ * c r) with hθwdef
  have hθwmem : ∀ r ∈ Set.Ioi (0 : ℝ), θw r = r⁻¹ * c r := by
    intro r hr
    rw [hθwdef, Set.indicator_of_mem hr]
  have hwnn : ∀ r, 0 ≤ θw r := by
    intro r
    by_cases hr : r ∈ Set.Ioi (0 : ℝ)
    · rw [hθwmem r hr]
      exact mul_nonneg (inv_nonneg.mpr (le_of_lt hr)) (hc r hr)
    · rw [hθwdef, Set.indicator_of_notMem hr]
  have hwmeas : AEMeasurable θw (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    hcmeas.congr (by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
      exact (hθwmem r hr).symm)
  have hwint : MeasureTheory.IntegrableOn (fun r => (θw r) ^ 2) (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.IntegrableOn.congr_fun hcint
      (fun r hr => by rw [hθwmem r hr]) measurableSet_Ioi
  have hMle' : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      (M r) ^ 2 ≤ C * Ψ r := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    exact hMle r hr
  have houter := outer_gen hC hwnn hMnn hΨnn hwmeas hΨmeas hwint hΨint hMle'
  rw [Work.FTS.Nonlinear.Pieces.Fa]
  -- ### the chain
  have h1 : (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * N r θ|))
      ≤ ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹
          * (ENNReal.ofReal (c r * M r) * ENNReal.ofReal (π / 2)) := by
    refine MeasureTheory.lintegral_mono_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    exact mul_le_mul_right (hinner r hr) _
  have h2 : (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹
        * (ENNReal.ofReal (c r * M r) * ENNReal.ofReal (π / 2)))
      = ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (π / 2)
          * (ENNReal.ofReal (r⁻¹ * c r) * ENNReal.ofReal (M r)) := by
    refine MeasureTheory.lintegral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 < r := hr
    have hcr : 0 ≤ c r := hc r hr0
    have hinv : 0 ≤ r⁻¹ := inv_nonneg.mpr hr0.le
    rw [ENNReal.ofReal_mul hcr]
    calc ENNReal.ofReal r⁻¹
          * (ENNReal.ofReal (c r) * ENNReal.ofReal (M r) * ENNReal.ofReal (π / 2))
        = (ENNReal.ofReal r⁻¹ * ENNReal.ofReal (c r))
            * (ENNReal.ofReal (M r) * ENNReal.ofReal (π / 2)) := by ring
      _ = ENNReal.ofReal (r⁻¹ * c r)
            * (ENNReal.ofReal (M r) * ENNReal.ofReal (π / 2)) := by
            rw [ENNReal.ofReal_mul hinv]
      _ = ENNReal.ofReal (π / 2)
            * (ENNReal.ofReal (r⁻¹ * c r) * ENNReal.ofReal (M r)) := by ring
  have h3 : (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (π / 2)
        * (ENNReal.ofReal (r⁻¹ * c r) * ENNReal.ofReal (M r)))
      = ENNReal.ofReal (π / 2) * ∫⁻ r in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (r⁻¹ * c r) * ENNReal.ofReal (M r) :=
    MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have h4 : (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (r⁻¹ * c r) * ENNReal.ofReal (M r))
      ≤ ENNReal.ofReal (Real.sqrt C * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), Ψ r)
          * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * c r) ^ 2)) := by
    have hcong : (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (θw r) * ENNReal.ofReal (M r))
        = ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (r⁻¹ * c r) * ENNReal.ofReal (M r) := by
      refine MeasureTheory.lintegral_congr_ae ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
      rw [hθwmem r hr]
    have hsq : (∫ r in Set.Ioi (0 : ℝ), (θw r) ^ 2)
        = ∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * c r) ^ 2 := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
      intro r hr
      exact congrArg (fun x => x ^ 2) (hθwmem r hr)
    rw [← hcong, ← hsq]
    exact houter
  calc (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * N r θ|))
      ≤ ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹
          * (ENNReal.ofReal (c r * M r) * ENNReal.ofReal (π / 2)) := h1
    _ = ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (π / 2)
          * (ENNReal.ofReal (r⁻¹ * c r) * ENNReal.ofReal (M r)) := h2
    _ = ENNReal.ofReal (π / 2) * ∫⁻ r in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (r⁻¹ * c r) * ENNReal.ofReal (M r) := h3
    _ ≤ ENNReal.ofReal (π / 2) * ENNReal.ofReal (Real.sqrt C
          * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), Ψ r)
          * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * c r) ^ 2)) :=
        mul_le_mul_right h4 _
    _ = ENNReal.ofReal (Real.pi / 2 * (Real.sqrt C
          * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), Ψ r)
          * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * c r) ^ 2))) := by
        rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ Real.pi / 2)]

end Work.FTS.NonlinRows.Rl1
