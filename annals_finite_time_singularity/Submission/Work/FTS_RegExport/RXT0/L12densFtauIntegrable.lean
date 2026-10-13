import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS_RegExport.RXT.Sys.abs_L12dens_Fstar_add_le
import Submission.Work.FTS_RegExport.RXA2w.lim_mixed_weighted_proved
import Submission.Work.FTS_RegExport.RXT.L12Iter.Basic
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.FKJets
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.L12Deriv
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.L12Calc
import Submission.Work.FTS_RegExport.RXT.MixedUniform
import Submission.Work.FTS_RegExport.RXT.Sys.majorant_Ioi_integrable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT0

/-- The `L₁₂`-density of the profile `F(τ) = F_* + g(τ)` of the strong route is integrable on the
tail `(z,∞)`, `z > 0`, along the whole fake-time horizon.

`LimApprox` supplies the approximating class-`C` families `gn`; the weighted slot bound
`|D_z^kD_θ^a (slice (gn n) τ)| ≤ C·z^{3/2}/(1+z)²` (from the interior `L^∞`–`ℋ⁴` trade-off
`RXA1w.abs_mixed_le_HkNorm_C4_w_proved` and `Xn (slice (gn n) τ) ≤ C₀·(pExp α)²`) bounds the
integrand of the density pointwise against the elementary majorant
`3(π/2)(20/(1+s)² + C_{w}·s^{1/2}/(1+s)²)`, which is integrable on `(z,∞)`
(`abs_L12dens_Fstar_add_le` + `majorant_Ioi_integrable`).  The only remaining ingredient is the
a.e. strong measurability of the limiting density: each approximant density
`s ↦ L₁₂dens (F_* + slice (gn n) τ)(s) = 2β/(1+s)² + L₁₂dens (slice (gn n) τ)(s)` is continuous
on `(0,∞)` (`L12dens_Fstar_add_le`/`dens_add` + `L12dens_continuousOn`), and it converges
pointwise, for every `s > 0`, to the limiting density (`dens_tendsto`), so the limit is a.e.
strongly measurable (`aestronglyMeasurable_of_tendsto_ae`). -/
theorem L12densFtauIntegrable {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hA : Work.FTS.FinalV2.LimApprox (Work.FTS.Regularity.pExp α) C₀ Φs E g) :
    ∀ S > 0, ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z : ℝ, 0 < z →
      MeasureTheory.IntegrableOn (Work.Construction.L12dens
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ)) (Set.Ioi z) := by
  intro S hS τ hτ z hz
  have hβ : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hβ1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  -- the approximating families of `LimApprox`, and the weighted slot bounds of the limit family
  obtain ⟨gn, B, L, hC, hLip, hjet, hmu⟩ := hA S hS
  obtain ⟨Cw, hCw0, hCw⟩ := Work.FTS_RegExport.RXA2w.lim_mixed_weighted_proved
    (αG := Work.FTS.Regularity.pExp α) (C₀ := C₀) (Φs := Φs) (E := E) (g := g) hβ hβ1 hA S hS
  -- §1 the weighted bound for the `GR`-slice
  have hub : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.FTS.Galerkin.slice (Work.FTS.RegExportIface.RXT.GR α g) τ z θ|
        ≤ Cw * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := by
    intro z θ hz0 h0 h1
    rw [Work.FTS_RegExport.RXT.ftau_slice_GR_eq hτ.1 hz0 h0.le h1.le]
    have h := hCw τ hτ 0 0 (by norm_num) z θ hz0 h0 h1
    simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero] using h
  -- §2 the pointwise bound of the limiting density
  have hpt : ∀ s : ℝ, 0 < s →
      |Work.Construction.L12dens (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ) s|
        ≤ 3 * (Real.pi / 2)
            * (20 / (1 + s) ^ 2 + Cw * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2)) := by
    intro s hs
    have h := Work.FTS_RegExport.RXT.Sys.abs_L12dens_Fstar_add_le
      (α := Work.FTS.Regularity.pExp α) hβ hβ1 hCw0
      (u := Work.FTS.Galerkin.slice (Work.FTS.RegExportIface.RXT.GR α g) τ) hub hs
    have hfun : Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) τ
        = fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ
            + Work.FTS.Galerkin.slice (Work.FTS.RegExportIface.RXT.GR α g) τ z θ := rfl
    rw [hfun]
    exact h
  -- §3 the majorant is integrable on the tail
  have hmaj : MeasureTheory.IntegrableOn
      (fun s : ℝ => 3 * (Real.pi / 2)
        * (20 / (1 + s) ^ 2 + Cw * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2))) (Set.Ioi z) :=
    (Work.FTS_RegExport.RXT.Sys.majorant_Ioi_integrable hCw0).1.mono_set
      (Set.Ioi_subset_Ioi hz.le)
  -- §4 the standing data of the approximants
  have h4n : ∀ n : ℕ, ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Galerkin.slice (gn n) τ))
      Work.FTS.EllipticEst.Q0 := fun n => (hC n τ hτ).1.reg.forall 4
  obtain ⟨Cd, hCd0, hCd⟩ := Work.FTS_RegExport.RXA1w.abs_mixed_le_HkNorm_C4_w_proved hβ hβ1
  have hC0β : 0 ≤ C₀ * (Work.FTS.Regularity.pExp α) ^ 2 :=
    le_trans (Work.Spaces.HkNorm_nonneg (Work.FTS.Regularity.pExp α) 4
        (Work.FTS.Galerkin.slice (gn 0) 0)) (hC 0 0 ⟨le_rfl, hS.le⟩).2.1
  have hCwA0 : 0 ≤ Cd * (C₀ * (Work.FTS.Regularity.pExp α) ^ 2) := mul_nonneg hCd0 hC0β
  have hbd : ∀ (n k : ℕ), k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k (Work.FTS.Galerkin.slice (gn n) τ) z θ|
        ≤ (Cd * (C₀ * (Work.FTS.Regularity.pExp α) ^ 2))
            * Work.FTS_RegExport.RXT.Sys.L12FKaux.SW z := by
    intro n k hk z θ hz' h0 h1
    have hcl := (hC n τ hτ).1
    have h1' := hCd (Work.FTS.Galerkin.slice (gn n) τ) (hcl.reg.forall 4)
      (Work.FTS.ClassC.classC_hkMem_four hcl)
      (Work.FTS.ClassC.bdryTraces_mono (by norm_num) hcl.tr) k 0 (by omega) z θ hz' h0 h1
    rw [Work.Spaces.mixed_zero_right] at h1'
    have h2 : Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4 (Work.FTS.Galerkin.slice (gn n) τ)
        ≤ C₀ * (Work.FTS.Regularity.pExp α) ^ 2 := (hC n τ hτ).2.1
    calc |Work.Spaces.DzIter k (Work.FTS.Galerkin.slice (gn n) τ) z θ|
        ≤ Cd * Work.FTS_RegExport.RXT.Sys.L12FKaux.SW z
            * Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4
              (Work.FTS.Galerkin.slice (gn n) τ) := h1'
      _ ≤ Cd * Work.FTS_RegExport.RXT.Sys.L12FKaux.SW z
            * (C₀ * (Work.FTS.Regularity.pExp α) ^ 2) :=
          mul_le_mul_of_nonneg_left h2
            (mul_nonneg hCd0 (Work.FTS_RegExport.RXT.Sys.L12FKaux.SW_nonneg hz'.le))
      _ = (Cd * (C₀ * (Work.FTS.Regularity.pExp α) ^ 2))
            * Work.FTS_RegExport.RXT.Sys.L12FKaux.SW z := by ring
  -- §5 the slices of the approximants converge to those of `GR α g` on the open quadrant
  have hconv : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Filter.Tendsto (fun n => Work.FTS.Galerkin.slice (gn n) τ z θ) Filter.atTop
        (nhds (Work.FTS.Galerkin.slice (Work.FTS.RegExportIface.RXT.GR α g) τ z θ)) := by
    intro z θ hzθ
    have h := hjet τ hτ 0 0 (by norm_num) z θ hzθ
    have hGr : Work.FTS.Galerkin.slice (Work.FTS.RegExportIface.RXT.GR α g) τ z θ
        = Work.Spaces.mixed 0 0 (Work.FTS.Galerkin.slice g τ) z θ := by
      rw [Work.FTS_RegExport.RXT.ftau_slice_GR_eq hτ.1 hzθ.1 hzθ.2.1.le hzθ.2.2.le]
      simp only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero]
    rw [hGr]
    simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero] using h
  -- §6 the density of every approximant is continuous on `(0,∞)`
  have hcont : ∀ n : ℕ, ContinuousOn (Work.Construction.L12dens (Work.Construction.Ftau
      (Work.FTS.Regularity.pExp α) (gn n) τ)) (Set.Ioi 0) := by
    intro n
    have h1 : ContinuousOn (fun s : ℝ => 2 * Work.FTS.Regularity.pExp α / (1 + s) ^ 2)
        (Set.Ioi 0) :=
      continuousOn_const.div ((continuousOn_const.add continuousOn_id).pow 2)
        (fun s hs => pow_ne_zero 2 (by have hs0 : 0 < s := hs; linarith))
    have h2 := Work.FTS_RegExport.RXT.L12Iter.L12dens_continuousOn hCwA0 (h4n n) (hbd n)
    have h3 : ContinuousOn (fun s : ℝ => 2 * Work.FTS.Regularity.pExp α / (1 + s) ^ 2
        + Work.FM.L12dens Work.Spaces.K (Work.FTS.Galerkin.slice (gn n) τ) s) (Set.Ioi 0) :=
      h1.add h2
    refine h3.congr (fun s hs => ?_)
    exact Work.FTS_RegExport.RXT.Sys.L12FKaux.L12dens_Ftau_eq hβ hβ1 hCwA0 (h4n n) (hbd n)
      (u := Work.FTS.Galerkin.slice (gn n) τ) hs
  -- §7 a.e. strong measurability of the limiting density
  have haesm_n : ∀ n : ℕ, MeasureTheory.AEStronglyMeasurable (fun s => Work.Construction.L12dens
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ) s)
      (MeasureTheory.volume.restrict (Set.Ioi z)) := fun n =>
    ((hcont n).mono (Set.Ioi_subset_Ioi hz.le)).aestronglyMeasurable measurableSet_Ioi
  have hlim : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi z)),
      Filter.Tendsto (fun n => Work.Construction.L12dens (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (gn n) τ) s) Filter.atTop
        (nhds (Work.Construction.L12dens (Work.Construction.Ftau
          (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) s)) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun s hs =>
      Work.FTS_RegExport.RXT.Sys.L12FKaux.dens_tendsto
        (gn := gn) (h := Work.FTS.RegExportIface.RXT.GR α g) (τ := τ)
        hβ hβ1 hCwA0 h4n hbd hconv (show (0:ℝ) < s from lt_trans hz hs))
  have haesm : MeasureTheory.AEStronglyMeasurable (fun s => Work.Construction.L12dens
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) τ) s)
      (MeasureTheory.volume.restrict (Set.Ioi z)) :=
    aestronglyMeasurable_of_tendsto_ae Filter.atTop haesm_n hlim
  -- §8 conclusion
  refine MeasureTheory.Integrable.mono' hmaj haesm ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun s hs => ?_)
  rw [Real.norm_eq_abs]
  exact hpt s (show (0:ℝ) < s from lt_trans hz hs)

end Work.FTS_RegExport.RXT0
