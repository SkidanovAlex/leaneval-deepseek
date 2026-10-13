import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_RegExport.RXT.Sys.EPCDefs
import Submission.Work.FTS_RegExport.RXA2w.lim_mixed_weighted_proved
import Submission.Work.FTS_RegExport.RXT.Ftau_bounds
import Submission.Work.FTS_RegExport.RXT.L12Iter.Basic
import Submission.Work.FTS_RegExport.RXT.L12Iter.Tower
import Submission.Work.FTS_RegExport.RXT.C2Radial
import Submission.Work.FTS_RegExport.RXT.Sys.Ftau_jets_bounded_of_LimApprox
import Submission.Work.FTS_RegExport.RXT.Sys.majorant_Ioi_integrable
import Submission.Work.FTS_RegExport.RXT.Sys.abs_L12dens_Fstar_add_le
import Submission.Work.FTS_RegExport.RXT.Sys.continuousAt_Qang_of_bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Sys.Ftau_datum_of_LimApprox`

The profile `F(τ) = Ftau (pExp α) (GR α g) τ = F_* + g(τ)` of the strong route is an admissible
*datum* for the radial `L₁₂`/`𝔽K` jet calculus: on every horizon `[0,S]` the four clauses of
`DatumHyp F C` (open-quadrant `C²`-regularity, the three pointwise jet bounds `DatumBnd`, the
`L¹`-integrability of the `L₁₂`-density, and its integral bound) hold with a single constant `C`
independent of `τ`.

Everything comes from the `LimApprox` clause of `DynOK'` (the approximating class-`C` families)
and the standing `C²`-regularity hypothesis `hc2` on the slices:

* `Work.FTS_RegExport.RXA2w.lim_mixed_weighted_proved` bounds every slot `D_z^bD_θ^a` (`a+b ≤ 2`)
  of `slice g τ` by `Cw · z^{3/2}/(1+z)²` — the decay that makes the `L₁₂`-density integrable at
  `z = 0`;
* `Work.FTS_RegExport.RXT.Sys.Ftau_jets_bounded_of_LimApprox` (same argument as the proved
  `Ftau_bounds`, with `DynOK'` weakened to `LimApprox`) gives `DatumBnd F C_db`;
* `Work.FTS_RegExport.RXT.Sys.abs_L12dens_Fstar_add_le` bounds the density pointwise by the
  elementary majorant `3(π/2)(20/(1+s)² + Cw·s^{1/2}/(1+s)²)`, whose integral is controlled by
  `Work.FTS_RegExport.RXT.Sys.majorant_Ioi_integrable`;
* `Work.FTS_RegExport.RXT.Sys.continuousAt_Qang_of_bounds` makes the density continuous on
  `(0,∞)`, which supplies the a.e. strong measurability needed for `Integrable.mono'`.

The final constant is `max 1 C_db + 120 + 18·Cw`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.Sys

set_option autoImplicit false

/-! ## §1 Elementary bounds on the profile `F_*` -/

/-- The coefficient `α·Γ(θ)/c(α)` of `F_*` is bounded by `10` on `θ ∈ Iθ`: `0 ≤ Γ ≤ 1` and
`c(α) ≥ 1/10`. -/
theorem abs_Fstar_coeff_le_ten {α θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |α| * |Work.Spaces.Gam α θ / Work.Spaces.c α| ≤ 10 := by
  have hGam := Work.Spaces.Gam_bounds α θ hα hθ
  have hc := Work.Spaces.c_bounds α hα hα1
  have hcpos : 0 < Work.Spaces.c α := by linarith [hc.1]
  rw [abs_of_nonneg hα.le, abs_of_nonneg (div_nonneg hGam.1 hcpos.le)]
  rw [← mul_div_assoc, div_le_iff₀ hcpos]
  nlinarith [hα, hα1, hGam.1, hGam.2, hc.1]

/-- **Pointwise bound of the reference profile**: `|F_*(z,θ)| ≤ 10·|F_{*,rad}(z)|` on
`θ ∈ Iθ`. -/
theorem abs_Fstar_le_ten {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Construction.Fstar α z θ| ≤ 10 * |Work.FM.Fstar z| := by
  have hcoef := abs_Fstar_coeff_le_ten hα hα1 hθ
  rw [Work.Construction.Fstar, abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)

/-- The radial factor `2z/(1+z)²` of the reference profile is bounded by `2` on `z ≥ 0`. -/
theorem abs_FM_Fstar_le_two {z : ℝ} (hz : 0 ≤ z) : |Work.FM.Fstar z| ≤ 2 := by
  rw [Work.FM.Fstar, abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg (1 + z), sq_nonneg z]

/-- The radial weight `z^{3/2}/(1+z)²` is bounded by `Z^{3/2}` for `z ∈ (0,Z]`. -/
theorem weight_le_rpow {z Z : ℝ} (hz : 0 < z) (h : z ≤ Z) :
    z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2 ≤ Z ^ ((3 : ℝ) / 2) := by
  have h1 : z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2 ≤ z ^ ((3 : ℝ) / 2) := by
    rw [div_le_iff₀ (by positivity)]
    have hz2 : (1 : ℝ) ≤ (1 + z) ^ 2 := by nlinarith [sq_nonneg z]
    nlinarith [Real.rpow_nonneg hz.le ((3 : ℝ) / 2)]
  have h2 : z ^ ((3 : ℝ) / 2) ≤ Z ^ ((3 : ℝ) / 2) :=
    Real.rpow_le_rpow hz.le h (by norm_num)
  linarith

/-- The `L₁₂`-density is the angular moment `Q_0` divided by `z`. -/
theorem L12dens_eq_thetaIntegral (f : ℝ → ℝ → ℝ) (s : ℝ) :
    Work.Construction.L12dens f s
      = (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ * f s θ) / s := by
  rw [Work.Construction.L12dens, Work.FTS_RegExport.RXT.L12Iter.L12dens_eq_Qang_zero]
  simp only [Work.Elliptic.Qang, Work.Spaces.DzIter_zero]

/-! ## §2 The target -/

/-- **The profile `F(τ)` is a datum on `[0,S]`.** -/
theorem Ftau_datum_of_LimApprox {α C₀ : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hA : Work.FTS.FinalV2.LimApprox (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (S : ℝ) (hS : 0 < S)
    (hc2 : ∀ τ ∈ Set.Icc (0 : ℝ) S,
      ContDiffOn ℝ 2 (Function.uncurry (Work.FTS.Galerkin.slice g τ))
        Work.FTS.EllipticEst.Q0) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ τ ∈ Set.Icc (0 : ℝ) S,
      Work.FTS_RegExport.RXT.Sys.DatumHyp
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ) C := by
  have hp0 : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hp1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  have hα1 : α ≤ 1 := le_trans hα13 (by norm_num)
  -- §2.1 the standing bounds: weighted slots of the approximants, and the jet bounds of `F(τ)`
  have hT : 0 < max S 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨Cw, hCw0, hCw⟩ :=
    Work.FTS_RegExport.RXA2w.lim_mixed_weighted_proved (αG := Work.FTS.Regularity.pExp α)
      (C₀ := C₀) (Φs := Φs) (E := E) (g := g) hp0 hp1 hA (max S 1) hT
  obtain ⟨Cdb, -, hCdb⟩ := Ftau_jets_bounded_of_LimApprox hα hα13 hA S hS hc2
  obtain ⟨hmaj_int, hmaj_val⟩ := majorant_Ioi_integrable hCw0
  refine ⟨max 1 Cdb + 120 + 18 * Cw, ?_, ?_⟩
  · have h1 : (1 : ℝ) ≤ max 1 Cdb := le_max_left _ _
    have h2 : (0 : ℝ) ≤ 120 + 18 * Cw := by linarith
    linarith
  · intro τ hτ
    have hτT : τ ∈ Set.Icc (0 : ℝ) (max S 1) := ⟨hτ.1, le_trans hτ.2 (le_max_left _ _)⟩
    have hτnn : 0 ≤ τ := hτ.1
    -- §2.2 `GR` agrees with `g` on the closed quadrant
    have hGR : ∀ z θ : ℝ, 0 < z → 0 ≤ θ → θ ≤ Real.pi / 2 →
        Work.FTS.Galerkin.slice (Work.FTS.RegExportIface.RXT.GR α g) τ z θ
          = Work.FTS.Galerkin.slice g τ z θ :=
      fun z θ hz h0 h1 => Work.FTS_RegExport.RXT.ftau_slice_GR_eq hτnn hz h0 h1
    -- the weighted bound for the `GR`-slice
    have hub : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.FTS.Galerkin.slice (Work.FTS.RegExportIface.RXT.GR α g) τ z θ|
          ≤ Cw * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := by
      intro z θ hz h1 h2
      rw [hGR z θ hz h1.le h2.le]
      have h := hCw τ hτT 0 0 (by norm_num) z θ hz h1 h2
      simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero] using h
    -- §2.3 `C²`-regularity of the `GR`-slice, and of `F(τ)`, on the open quadrant
    have hGRc : ContDiffOn ℝ 2
        (Function.uncurry (Work.FTS.Galerkin.slice (Work.FTS.RegExportIface.RXT.GR α g) τ))
        Work.FTS.EllipticEst.Q0 :=
      (hc2 τ hτ).congr (fun p hp => hGR p.1 p.2 hp.1 hp.2.1.le hp.2.2.le)
    have hFc : ContDiffOn ℝ 2
        (Function.uncurry (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ)) Work.FTS.EllipticEst.Q0 := by
      have h1 : ContDiffOn ℝ 2
          (Function.uncurry (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)))
          Work.FTS.EllipticEst.Q0 := Work.FTS_RegExport.RXT.ftau_contDiffOn_Fstar_Q0 hp0 hp1
      have h2 := h1.add hGRc
      refine h2.congr (fun p _ => ?_)
      simp only [Function.uncurry, Work.Construction.Ftau, Work.FTS.Galerkin.slice]
    -- §2.4 the pointwise bound of the `L₁₂`-density of `F(τ)`
    have hpt : ∀ s : ℝ, 0 < s →
        |Work.Construction.L12dens (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) τ) s|
          ≤ 3 * (Real.pi / 2)
              * (20 / (1 + s) ^ 2 + Cw * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2)) := by
      intro s hs
      have h := abs_L12dens_Fstar_add_le (α := Work.FTS.Regularity.pExp α) hp0 hp1 hCw0
        (u := Work.FTS.Galerkin.slice (Work.FTS.RegExportIface.RXT.GR α g) τ) hub hs
      have hfun : Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ
          = fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ
              + Work.FTS.Galerkin.slice (Work.FTS.RegExportIface.RXT.GR α g) τ z θ := rfl
      rw [hfun]
      exact h
    -- §2.5 continuity of the angular moment, hence of the density, on `(0,∞)`
    have hQcont : ContinuousOn (fun s => ∫ θ in Work.Spaces.Iθ,
        Work.Elliptic.Ktheta θ * Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ s θ) (Set.Ioi 0) := by
      intro s₀ hs₀
      refine (continuousAt_Qang_of_bounds (f := Work.Construction.Ftau
          (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) hs₀
        hFc.continuousOn (A := 20 + Cw * (2 * s₀) ^ ((3 : ℝ) / 2)) ?_).continuousWithinAt
      intro z θ hz hθ0 hθ1
      have hz0 : 0 < z := lt_of_lt_of_le (by linarith [show (0 : ℝ) < s₀ from hs₀] :
        (0 : ℝ) < s₀ / 2) hz.1.le
      have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ0.le, hθ1.le⟩
      have h1 : |Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ|
          ≤ 10 * |Work.FM.Fstar z| := abs_Fstar_le_ten hp0 hp1 hθI
      have h2 : |Work.FM.Fstar z| ≤ 2 := abs_FM_Fstar_le_two hz0.le
      have h3 : |Work.FTS.Galerkin.slice (Work.FTS.RegExportIface.RXT.GR α g) τ z θ|
          ≤ Cw * (2 * s₀) ^ ((3 : ℝ) / 2) :=
        le_trans (hub z θ hz0 hθ0 hθ1)
          (mul_le_mul_of_nonneg_left (weight_le_rpow hz0 hz.2.le) hCw0)
      rw [Work.Construction.Ftau]
      calc |Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ
            + Work.FTS.Galerkin.slice (Work.FTS.RegExportIface.RXT.GR α g) τ z θ|
          ≤ |Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ|
            + |Work.FTS.Galerkin.slice (Work.FTS.RegExportIface.RXT.GR α g) τ z θ| :=
            abs_add_le _ _
        _ ≤ 10 * |Work.FM.Fstar z| + Cw * (2 * s₀) ^ ((3 : ℝ) / 2) := add_le_add h1 h3
        _ ≤ 10 * 2 + Cw * (2 * s₀) ^ ((3 : ℝ) / 2) := by
            have h10 : 10 * |Work.FM.Fstar z| ≤ 10 * 2 :=
              mul_le_mul_of_nonneg_left h2 (by norm_num)
            linarith
        _ = 20 + Cw * (2 * s₀) ^ ((3 : ℝ) / 2) := by ring
    have hdens_eq : ∀ s : ℝ, Work.Construction.L12dens (Work.Construction.Ftau
          (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) s
        = (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ * Work.Construction.Ftau
            (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ s θ) / s :=
      fun s => L12dens_eq_thetaIntegral _ s
    have hcont : ContinuousOn (Work.Construction.L12dens (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ)) (Set.Ioi 0) :=
      (hQcont.div continuousOn_id (fun s hs => ne_of_gt hs)).congr
        (fun s _ => hdens_eq s)
    -- §2.6 integrability of the density, and the integral bound
    have hint : MeasureTheory.IntegrableOn (Work.Construction.L12dens (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ)) (Set.Ioi 0) := by
      refine MeasureTheory.Integrable.mono' hmaj_int
        (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
      rw [Real.norm_eq_abs]
      exact hpt s hs
    have hbnd : (∫ s in Set.Ioi 0, |Work.Construction.L12dens (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) s|)
          ≤ max 1 Cdb + 120 + 18 * Cw := by
      have h1 : (∫ s in Set.Ioi 0, |Work.Construction.L12dens (Work.Construction.Ftau
          (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) s|)
            ≤ ∫ s in Set.Ioi 0, 3 * (Real.pi / 2)
                * (20 / (1 + s) ^ 2 + Cw * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2)) := by
        refine MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall (fun s => abs_nonneg _)) hmaj_int ?_
        filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
        exact hpt s hs
      have h2 : (1 : ℝ) ≤ max 1 Cdb := le_max_left _ _
      have h3 : (0 : ℝ) ≤ 18 * Cw := by linarith
      linarith [hmaj_val, h1, h2, h3]
    -- §2.7 the datum
    have hCdb_le : Cdb ≤ max 1 Cdb + 120 + 18 * Cw := by
      have h0 : (0 : ℝ) ≤ 120 + 18 * Cw := by linarith
      have h1 : Cdb ≤ max 1 Cdb := le_max_right _ _
      linarith
    have hDbnd : Work.FTS_RegExport.RXT.Sys.DatumBnd (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ)
        (max 1 Cdb + 120 + 18 * Cw) := by
      intro z θ hz h1 h2
      obtain ⟨a1, a2, a3⟩ := hCdb τ hτ z θ hz h1 h2
      exact ⟨le_trans a1 hCdb_le, le_trans a2 hCdb_le, le_trans a3 hCdb_le⟩
    exact ⟨hFc, hDbnd, hint, hbnd⟩

end Work.FTS_RegExport.RXT.Sys
