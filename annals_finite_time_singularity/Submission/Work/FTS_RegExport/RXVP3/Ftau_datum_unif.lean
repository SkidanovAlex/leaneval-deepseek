import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_RegExport.RXT.Sys.Ftau_datum_of_LimApprox
import Submission.Work.FTS_RegExport.RXA2w.lim_mixed_weighted_proved
import Submission.Work.FTS_RegExport.RXT.Ftau_bounds
import Submission.Work.FTS_RegExport.RXT.Sys.EPCDefs
import Submission.Work.FTS_RegExport.RXT.Sys.abs_L12dens_Fstar_add_le
import Submission.Work.FTS_RegExport.RXT.Sys.majorant_Ioi_integrable
import Submission.Work.FTS_RegExport.RXT.Sys.continuousAt_Qang_of_bounds
import Submission.Work.FTS_RegExport.RXVP3.Ftau_bounds_unif
import Submission.Work.FTS_RegExport.RXVP3.L12dens_mass_unif

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXVP3

set_option autoImplicit false

/-! ## §1 The `τ`-uniform weighted bound for the slices of `g`

This is `Work.FTS_RegExport.RXA2w.lim_mixed_weighted_proved` with the horizon `max τ 1` moved
*inside* the `∀ τ`: the constant returned there is `Cw₀ · (C₀ α²)` with `Cw₀` from
`RXA1w.abs_mixed_le_HkNorm_C4_w_proved` and `C₀ α²` the class-`C` `ℋ⁴`-bound of the approximants,
neither of which mentions the horizon, so the same proof yields a horizon-free constant. -/
theorem mixed_weighted_unif {αG C₀ : ℝ} (hα : 0 < αG) (hα1 : αG ≤ 1)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hA : Work.FTS.FinalV2.LimApprox αG C₀ Φs E g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 ≤ τ → ∀ b a : ℕ, a + b ≤ 2 →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g τ) z θ|
          ≤ C * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := by
  obtain ⟨Cw, hCw0, hCw⟩ :=
    Work.FTS_RegExport.RXA1w.abs_mixed_le_HkNorm_C4_w_proved hα hα1
  -- the constant `C₀ αG²` is nonnegative (it dominates `Xn` at any slot of any approximant)
  have hC0sq : 0 ≤ C₀ * αG ^ 2 := by
    obtain ⟨gn, B, L, hC, -, -, -⟩ := hA 1 one_pos
    have hX0 : 0 ≤ Work.FTS.Nonlin.Xn αG (Work.FTS.Galerkin.slice (gn 0) 0) :=
      Work.Spaces.HkNorm_nonneg αG 4 _
    exact le_trans hX0 (hC 0 0 ⟨le_rfl, zero_le_one⟩).2.1
  refine ⟨Cw * (C₀ * αG ^ 2), mul_nonneg hCw0 hC0sq, ?_⟩
  intro τ hτ b a hab z θ hz hθ0 hθ1
  have hw0 : 0 ≤ z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2 :=
    div_nonneg (Real.rpow_nonneg hz.le _) (by positivity)
  obtain ⟨gn, B, L, hC, -, hjet, -⟩ :=
    hA (max τ 1) (lt_of_lt_of_le one_pos (le_max_right _ _))
  have hτT : τ ∈ Set.Icc (0 : ℝ) (max τ 1) := ⟨hτ, le_max_left _ _⟩
  -- the existential constant of `LimApprox` does not depend on `n`: the class-`C` bound
  -- transfers slotwise and the `ℋ⁴`-norm is dominated by `C₀ αG²`
  have hbound : ∀ n : ℕ,
      |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice (gn n) τ) z θ|
        ≤ Cw * (C₀ * αG ^ 2) * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := by
    intro n
    have hcls : Work.FTS.ClassC.ClassC αG (Work.FTS.Galerkin.slice (gn n) τ) := (hC n τ hτT).1
    have h4 : ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Galerkin.slice (gn n) τ))
        Work.FTS.EllipticEst.Q0 :=
      (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hcls.reg 4
    have hmem : Work.Spaces.HkMem αG 4 (Work.FTS.Galerkin.slice (gn n) τ) :=
      Work.FTS.OpenPkg.HkMem_mono_open hcls.reg 4 (by norm_num) hcls.mem
    have htr : Work.FTS.Nonlin.BdryTraces αG 4 (Work.FTS.Galerkin.slice (gn n) τ) :=
      Work.FTS.ClassC.bdryTraces_mono (by norm_num) hcls.tr
    have h1 := hCw _ h4 hmem htr b a hab z θ hz hθ0 hθ1
    have h2 : Work.Spaces.HkNorm αG 4 (Work.FTS.Galerkin.slice (gn n) τ) ≤ C₀ * αG ^ 2 :=
      (hC n τ hτT).2.1
    calc |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice (gn n) τ) z θ|
        ≤ Cw * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2)
            * Work.Spaces.HkNorm αG 4 (Work.FTS.Galerkin.slice (gn n) τ) := h1
      _ ≤ Cw * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) * (C₀ * αG ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg hCw0 hw0)
      _ = Cw * (C₀ * αG ^ 2) * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := by ring
  have hzθ : (z, θ) ∈ Work.Construction.Qd := ⟨hz, hθ0, hθ1⟩
  exact le_of_tendsto ((hjet τ hτT b a (by omega) z θ hzθ).abs)
    (Filter.Eventually.of_forall hbound)

/-- **`Ftau_datum_of_LimApprox` with a `τ`-uniform constant.**  This is
`Work.FTS_RegExport.RXT.Sys.Ftau_datum_of_LimApprox`
(`Submission/Work/FTS_RegExport/RXT/Sys/Ftau_datum_of_LimApprox.lean`) with the horizon removed
(unbounded `τ`, and the `hc2` hypothesis dropped because `DynOK'` supplies it through
`RegPkgMin.c4` for every `τ ≥ 0`).

PROOF ROUTE (read the two files first).  Every ingredient constant of the horizon-local proof is
already horizon-free:
* `RXA2w.lim_mixed_weighted_proved` returns `Cw₀ * (C₀ * (pExp α)^2)` with `Cw₀` from
  `RXA1w.abs_mixed_le_HkNorm_C4_w_proved` — no `T`.  Re-run its proof with the horizon
  `max τ 1` *inside* the `∀ τ` to obtain the `τ`-uniform weighted bound
  `∃ Cw, 0 ≤ Cw ∧ ∀ τ, 0 ≤ τ → ∀ b a, a + b ≤ 2 → ∀ z θ, 0 < z → 0 < θ → θ < π/2 →
     |mixed b a (slice (GR α g) τ) z θ| ≤ Cw * (z^{3/2}/(1+z)^2)`
  (use `ftau_slice_GR_eq` to move between `GR` and `g` on the quadrant, and `hOK.2` for the
  approximants at horizon `max τ 1`, `hOK.1.2` for `Xn ≤ C₀ α²`).
* `DatumBnd`: take it from the *proved, `τ`-uniform* `RXT.Ftau_bounds hα hα13 hOK τ hτ`
  (constant `10*M + |K|`, `K = 10/√(γ-1)·(C₀α²)`), instead of the horizon-local
  `Ftau_jets_bounded_of_LimApprox`.
* `ContDiffOn ℝ 2 (uncurry (Ftau (pExp α) (GR α g) τ)) Q0`: from `contDiffOn_Ftau_Q0 hOK τ hτ`.
* density majorant: `RXT.Sys.abs_L12dens_Fstar_add_le` with `u = slice (GR α g) τ` (note
  `Ftau (pExp α) (GR α g) τ = fun z θ => Fstar (pExp α) z θ + slice (GR α g) τ z θ` is `rfl`);
  integrability and the mass bound from `RXT.Sys.majorant_Ioi_integrable hCw0` via
  `MeasureTheory.Integrable.mono'` and `MeasureTheory.integral_mono_of_nonneg`, the a.e. strong
  measurability coming from continuity of the density on `(0,∞)`
  (`RXT.Sys.continuousAt_Qang_of_bounds` + `L12dens_eq_thetaIntegral`).
The final constant can be `max 1 Cdb + 120 + 18 * Cw` with `Cdb`, `Cw` the uniform constants
above; every step is importable from the existing modules. -/
theorem Ftau_datum_unif {α C₀ : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ τ : ℝ, 0 ≤ τ →
      Work.FTS_RegExport.RXT.Sys.DatumHyp
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ) C := by
  have hp0 : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hp1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  -- §A the two `τ`-uniform constants: weighted slice bounds and the profile jet bounds
  obtain ⟨Cw, hCw0, hCw⟩ := mixed_weighted_unif (αG := Work.FTS.Regularity.pExp α)
    (C₀ := C₀) (Φs := Φs) (E := E) (g := g) hp0 hp1 hOK.2
  obtain ⟨Cdb, -, hCdb⟩ := Ftau_bounds_unif hα hα13 hOK
  refine ⟨max 1 Cdb + 120 + 18 * Cw, ?_, ?_⟩
  · have h1 : (1 : ℝ) ≤ max 1 Cdb := le_max_left _ _
    have h2 : (0 : ℝ) ≤ 120 + 18 * Cw := by linarith
    linarith
  · -- §B the weighted bound for the `GR`-slice, uniformly in `τ`
    have huAll : ∀ τ : ℝ, 0 ≤ τ → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.FTS.Galerkin.slice (Work.FTS.RegExportIface.RXT.GR α g) τ z θ|
          ≤ Cw * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := by
      intro τ' hτ' z θ hz h1 h2
      rw [Work.FTS_RegExport.RXT.ftau_slice_GR_eq hτ' hz h1.le h2.le]
      exact hCw τ' hτ' 0 0 (by norm_num) z θ hz h1 h2
    -- the `C²`-regularity of `F(τ)` on the open quadrant, uniformly in `τ`
    have hFcAll : ∀ τ : ℝ, 0 ≤ τ → ContDiffOn ℝ 2
        (Function.uncurry (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ)) Work.FTS.EllipticEst.Q0 := by
      intro τ hτ
      have hGRc : ContDiffOn ℝ 2
          (Function.uncurry (Work.FTS.Galerkin.slice
            (Work.FTS.RegExportIface.RXT.GR α g) τ)) Work.FTS.EllipticEst.Q0 :=
        Work.FTS_RegExport.RXT.ftau_contDiffOn_slice_GR_Q0 hOK τ hτ
      have h1 : ContDiffOn ℝ 2
          (Function.uncurry (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)))
          Work.FTS.EllipticEst.Q0 := Work.FTS_RegExport.RXT.ftau_contDiffOn_Fstar_Q0 hp0 hp1
      have h2 := h1.add hGRc
      refine h2.congr (fun p _ => ?_)
      simp only [Function.uncurry, Work.Construction.Ftau, Work.FTS.Galerkin.slice]
    intro τ hτ
    -- §C the `L¹`-density: integrability and the mass bound
    obtain ⟨hint, hbnd⟩ := L12dens_mass_unif hα hα13 hCw0 (g := g) huAll
      (fun τ' hτ' => (hFcAll τ' hτ').continuousOn) τ hτ
    -- §D the pointwise jet bounds of `F(τ)`, with the single constant `max 1 Cdb + 120 + 18 Cw`
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
    have hbnd' : (∫ s in Set.Ioi 0, |Work.Construction.L12dens (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) s|)
        ≤ max 1 Cdb + 120 + 18 * Cw := by
      have h1 : (1 : ℝ) ≤ max 1 Cdb := le_max_left _ _
      linarith
    exact ⟨hFcAll τ hτ, hDbnd, hint, hbnd'⟩

end Work.FTS_RegExport.RXVP3
