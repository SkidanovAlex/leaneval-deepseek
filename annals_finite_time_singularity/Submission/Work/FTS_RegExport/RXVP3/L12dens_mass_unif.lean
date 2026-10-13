import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_RegExport.RXT.Sys.Ftau_datum_of_LimApprox
import Submission.Work.FTS_RegExport.RXT.Sys.abs_L12dens_Fstar_add_le
import Submission.Work.FTS_RegExport.RXT.Sys.majorant_Ioi_integrable
import Submission.Work.FTS_RegExport.RXT.Sys.continuousAt_Qang_of_bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXVP3

set_option autoImplicit false

open MeasureTheory Set

/-- **Mass (L¹) bound for the `L₁₂`-density of the profile `F(τ) = F_* + g(τ)`.**

The profile is `F(τ) = Ftau (pExp α) (GR α g) τ = fun z θ => Fstar (pExp α) z θ
+ slice (GR α g) τ z θ` (definitionally).  The two hypotheses are exactly the two pieces of
information the bound needs:

* `hu` bounds the slice `slice (GR α g) τ` by the weight `Cw·z^{3/2}/(1+z)²`, which is the
  input of `RXT.Sys.abs_L12dens_Fstar_add_le`: the angular part of the density is bounded
  by `3(π/2)(20/(1+s)² + Cw·s^{1/2}/(1+s)²)`;
* `hcont` is joint continuity of `F(τ)` on the open quadrant, which makes the angular moment
  continuous on `(0,∞)` (`RXT.Sys.continuousAt_Qang_of_bounds`), hence supplies the a.e.
  strong measurability needed for `MeasureTheory.Integrable.mono'`.

The majorant is integrable with integral `≤ 120 + 18·Cw` (`RXT.Sys.majorant_Ioi_integrable`),
and the statement of that lemma is *literal* — no `∃ C`, no `τ`, no horizon — which is why the
final constant here is exactly `120 + 18·Cw`. -/
theorem L12dens_mass_unif {α Cw : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hCw : 0 ≤ Cw)
    {g : Work.FTS.Galerkin.Fam}
    (hu : ∀ τ : ℝ, 0 ≤ τ → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.FTS.Galerkin.slice (Work.FTS.RegExportIface.RXT.GR α g) τ z θ|
        ≤ Cw * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2))
    (hcont : ∀ τ : ℝ, 0 ≤ τ → ContinuousOn (Function.uncurry
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ)) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ∀ τ : ℝ, 0 ≤ τ →
      MeasureTheory.IntegrableOn (Work.Construction.L12dens (Work.Construction.Ftau
          (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ)) (Set.Ioi 0) ∧
      (∫ s in Set.Ioi 0, |Work.Construction.L12dens (Work.Construction.Ftau
          (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) s|)
        ≤ 120 + 18 * Cw := by
  have hp0 : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hp1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  have hα1 : α ≤ 1 := le_trans hα13 (by norm_num)
  obtain ⟨hmaj_int, hmaj_val⟩ := Work.FTS_RegExport.RXT.Sys.majorant_Ioi_integrable hCw
  intro τ hτ
  set F : ℝ → ℝ → ℝ := Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
      (Work.FTS.RegExportIface.RXT.GR α g) τ with hFdef
  have hFsplit : F = fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ
      + Work.FTS.Galerkin.slice (Work.FTS.RegExportIface.RXT.GR α g) τ z θ := rfl
  -- ## §1 the pointwise bound of the `L₁₂`-density of `F(τ)` by the elementary majorant
  have hpt : ∀ s : ℝ, 0 < s →
      |Work.Construction.L12dens F s|
        ≤ 3 * (Real.pi / 2)
            * (20 / (1 + s) ^ 2 + Cw * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2)) := by
    intro s hs
    have h := Work.FTS_RegExport.RXT.Sys.abs_L12dens_Fstar_add_le
      (α := Work.FTS.Regularity.pExp α) hp0 hp1 hCw
      (u := Work.FTS.Galerkin.slice (Work.FTS.RegExportIface.RXT.GR α g) τ) (hu τ hτ) hs
    rw [hFsplit]
    exact h
  -- ## §2 continuity of the angular moment, hence of the density, on `(0,∞)`
  have hFc : ContinuousOn (Function.uncurry F)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    rw [hFsplit]
    exact hcont τ hτ
  have hQcont : ContinuousOn (fun s => ∫ θ in Work.Spaces.Iθ,
      Work.Elliptic.Ktheta θ * F s θ) (Set.Ioi 0) := by
    intro s₀ hs₀
    refine (Work.FTS_RegExport.RXT.Sys.continuousAt_Qang_of_bounds (f := F) hs₀
      hFc (A := 20 + Cw * (2 * s₀) ^ ((3 : ℝ) / 2)) ?_).continuousWithinAt
    intro z θ hz hθ0 hθ1
    have hz0 : 0 < z :=
      lt_of_lt_of_le (by linarith [show (0 : ℝ) < s₀ from hs₀] : (0 : ℝ) < s₀ / 2) hz.1.le
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ0.le, hθ1.le⟩
    have h1 : |Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ|
        ≤ 10 * |Work.FM.Fstar z| :=
      Work.FTS_RegExport.RXT.Sys.abs_Fstar_le_ten hp0 hp1 hθI
    have h2 : |Work.FM.Fstar z| ≤ 2 := Work.FTS_RegExport.RXT.Sys.abs_FM_Fstar_le_two hz0.le
    have h3 : |Work.FTS.Galerkin.slice (Work.FTS.RegExportIface.RXT.GR α g) τ z θ|
        ≤ Cw * (2 * s₀) ^ ((3 : ℝ) / 2) :=
      le_trans (hu τ hτ z θ hz0 hθ0 hθ1)
        (mul_le_mul_of_nonneg_left
          (Work.FTS_RegExport.RXT.Sys.weight_le_rpow hz0 hz.2.le) hCw)
    rw [hFsplit]
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
  have hdens_eq : ∀ s : ℝ, Work.Construction.L12dens F s
      = (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ * F s θ) / s :=
    fun s => Work.FTS_RegExport.RXT.Sys.L12dens_eq_thetaIntegral F s
  have hdenc : ContinuousOn (Work.Construction.L12dens F) (Set.Ioi 0) :=
    (hQcont.div continuousOn_id (fun s hs => ne_of_gt hs)).congr (fun s _ => hdens_eq s)
  -- ## §3 integrability of the density and the mass bound
  refine ⟨?_, ?_⟩
  · refine MeasureTheory.Integrable.mono' hmaj_int
      (hdenc.aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
    rw [Real.norm_eq_abs]
    exact hpt s hs
  · calc (∫ s in Set.Ioi 0, |Work.Construction.L12dens F s|)
        ≤ ∫ s in Set.Ioi 0, 3 * (Real.pi / 2)
            * (20 / (1 + s) ^ 2 + Cw * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2)) :=
          MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall (fun s => abs_nonneg _))
            hmaj_int (by
              filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
              exact hpt s hs)
      _ ≤ 120 + 18 * Cw := hmaj_val

end Work.FTS_RegExport.RXVP3
