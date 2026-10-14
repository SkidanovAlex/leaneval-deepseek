import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.PggParts
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.Pgs
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.FzFacts
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.VocabO2
-- ===== merged: Submission.Work.FTS.NonlinRows.Rl1.tools =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.NonlinRows.Rl1

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlinear.Pieces (Fa)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Elementary facts about the weights and the `ofReal`-`rpow` bridges -/

theorem w_nonneg' (r : ℝ) : 0 ≤ Work.Spaces.w r := by
  rw [Work.Spaces.w]; positivity


theorem one_le_w' {r : ℝ} (hr : 0 < r) : 1 ≤ Work.Spaces.w r := by
  rw [Work.Spaces.w, le_div_iff₀ (by positivity)]
  nlinarith

/-- `(ofReal x)^{1/2} = ofReal (√x)` for `x ≥ 0`. -/
theorem ofReal_rpow_half {x : ℝ} (hx : 0 ≤ x) :
    (ENNReal.ofReal x) ^ (1 / 2 : ℝ) = ENNReal.ofReal (Real.sqrt x) := by
  rw [ENNReal.ofReal_rpow_of_nonneg hx (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ← Real.sqrt_eq_rpow]

/-- `(ofReal x)^{2} = ofReal (x²)`. -/
theorem ofReal_rpow_two' {x : ℝ} (hx : 0 ≤ x) :
    (ENNReal.ofReal x) ^ (2 : ℝ) = ENNReal.ofReal (x ^ 2) := by
  rw [ENNReal.ofReal_rpow_of_nonneg hx (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_two]

theorem integrableOn_inv_one_add_sq' :
    IntegrableOn (fun r : ℝ => (1 / (1 + r)) ^ 2) (Set.Ioi 0) ∧
      (∫ r in Set.Ioi (0 : ℝ), (1 / (1 + r)) ^ 2) ≤ 2 :=
  ⟨Work.FTS.H2.InvOneAddSq.1, Work.FTS.H2.InvOneAddSq.2⟩

/-! ## The abstract `r`-step

Given an a.e. bound `(M r)² ≤ C·Ψ r` for a *variable* coefficient majorant `M`, an angular
majorant `θw` and the plain integrability of `Ψ`, the `L₁₂`-weight `r⁻¹` is absorbed into the
angular majorant and the whole thing is estimated by Cauchy–Schwarz:
`∫ r⁻¹ M r · θw r ≤ √C·(∫Ψ)^{1/2}·(∫θw²)^{1/2}`. -/

theorem outer_gen {C : ℝ} (hC : 0 ≤ C) {M Ψ θw : ℝ → ℝ}
    (hwnn : ∀ r, 0 ≤ θw r) (hMnn : ∀ r, 0 ≤ M r) (hΨnn : ∀ r, 0 ≤ Ψ r)
    (hwmeas : AEMeasurable θw (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (hΨmeas : AEMeasurable Ψ (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (hwint : IntegrableOn (fun r => (θw r) ^ 2) (Set.Ioi (0 : ℝ)))
    (hΨint : IntegrableOn Ψ (Set.Ioi (0 : ℝ)))
    (hMle : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))), (M r) ^ 2 ≤ C * Ψ r) :
    (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (θw r) * ENNReal.ofReal (M r))
      ≤ ENNReal.ofReal (Real.sqrt C * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), Ψ r)
          * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), (θw r) ^ 2)) := by
  have hstep : (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (θw r) * ENNReal.ofReal (M r))
      ≤ ENNReal.ofReal (Real.sqrt C)
        * (∫⁻ r in Set.Ioi (0 : ℝ),
            ENNReal.ofReal (θw r) * ENNReal.ofReal (Real.sqrt (Ψ r))) := by
    have hpoint : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
        ENNReal.ofReal (M r) ≤ ENNReal.ofReal (Real.sqrt C) * ENNReal.ofReal (Real.sqrt (Ψ r)) := by
      filter_upwards [hMle] with r hr
      have h1 : M r ≤ Real.sqrt (C * Ψ r) := by
        rw [Real.le_sqrt (hMnn r) (mul_nonneg hC (hΨnn r))]
        exact hr
      rw [Real.sqrt_mul hC (Ψ r)] at h1
      rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg C)]
      exact ENNReal.ofReal_le_ofReal h1
    calc (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (θw r) * ENNReal.ofReal (M r))
        ≤ ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (θw r)
            * (ENNReal.ofReal (Real.sqrt C) * ENNReal.ofReal (Real.sqrt (Ψ r))) :=
          MeasureTheory.lintegral_mono_ae
            (hpoint.mono (fun r hr => mul_le_mul_right hr _))
      _ = ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.sqrt C)
            * (ENNReal.ofReal (θw r) * ENNReal.ofReal (Real.sqrt (Ψ r))) := by
          refine MeasureTheory.lintegral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
          ring
      _ = ENNReal.ofReal (Real.sqrt C)
            * (∫⁻ r in Set.Ioi (0 : ℝ),
                ENNReal.ofReal (θw r) * ENNReal.ofReal (Real.sqrt (Ψ r))) :=
          MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq
    (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) (p := 2) (q := 2)
    Real.HolderConjugate.two_two (f := fun r => ENNReal.ofReal (θw r))
    (g := fun r => ENNReal.ofReal (Real.sqrt (Ψ r)))
    hwmeas.ennreal_ofReal (hΨmeas.sqrt).ennreal_ofReal
  simp only [Pi.mul_apply] at hholder
  have hF2 : (∫⁻ r in Set.Ioi (0 : ℝ), (ENNReal.ofReal (θw r)) ^ (2 : ℝ))
      = ENNReal.ofReal (∫ r in Set.Ioi (0 : ℝ), (θw r) ^ 2) := by
    rw [MeasureTheory.lintegral_congr_ae
      (Filter.Eventually.of_forall (fun r => ofReal_rpow_two' (hwnn r)))]
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hwint
      (Filter.Eventually.of_forall (fun r => sq_nonneg _))]
  have hG2 : (∫⁻ r in Set.Ioi (0 : ℝ), (ENNReal.ofReal (Real.sqrt (Ψ r))) ^ (2 : ℝ))
      = ENNReal.ofReal (∫ r in Set.Ioi (0 : ℝ), Ψ r) := by
    rw [MeasureTheory.lintegral_congr_ae
      (Filter.Eventually.of_forall (fun r => by
        rw [ofReal_rpow_two' (Real.sqrt_nonneg _), Real.sq_sqrt (hΨnn r)]))]
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hΨint
      (Filter.Eventually.of_forall hΨnn)]
  rw [hF2, hG2] at hholder
  calc (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (θw r) * ENNReal.ofReal (M r))
      ≤ ENNReal.ofReal (Real.sqrt C)
          * (∫⁻ r in Set.Ioi (0 : ℝ),
              ENNReal.ofReal (θw r) * ENNReal.ofReal (Real.sqrt (Ψ r))) := hstep
    _ ≤ ENNReal.ofReal (Real.sqrt C)
          * ((ENNReal.ofReal (∫ r in Set.Ioi (0 : ℝ), (θw r) ^ 2)) ^ (1 / 2 : ℝ)
              * (ENNReal.ofReal (∫ r in Set.Ioi (0 : ℝ), Ψ r)) ^ (1 / 2 : ℝ)) :=
          mul_le_mul_right hholder _
    _ = ENNReal.ofReal (Real.sqrt C)
          * (ENNReal.ofReal (Real.sqrt (∫ r in Set.Ioi (0 : ℝ), (θw r) ^ 2))
              * ENNReal.ofReal (Real.sqrt (∫ r in Set.Ioi (0 : ℝ), Ψ r))) := by
          rw [ofReal_rpow_half (MeasureTheory.integral_nonneg (fun r => sq_nonneg (θw r))),
            ofReal_rpow_half (MeasureTheory.integral_nonneg hΨnn)]
    _ = ENNReal.ofReal (Real.sqrt C * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), Ψ r)
          * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), (θw r) ^ 2)) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.sqrt_nonneg C),
            ← ENNReal.ofReal_mul (mul_nonneg (Real.sqrt_nonneg C) (Real.sqrt_nonneg _))]
          congr 1
          ring

/-! ## The angular energies of the three `g`-slots

`Phi0 g`, `Phi1 g`, `Phi2 g` are the (unweighted) angular energies of the slots `g`,
`D_θg`, `D_zg`.  The facts below are the ones consumed by the `θ`-Cauchy–Schwarz and the
`r`-step of the piecewise estimates. -/

/-- The slot data of a single angular slot `B` of the datum `G`, with energy `Φ`: everything
the piecewise estimates need about it. -/
structure SlotData (α : ℝ) (B : ℝ → ℝ → ℝ) (Φ : ℝ → ℝ) (Xs : ℝ) : Prop where
  nonneg : ∀ r, 0 ≤ Φ r
  aesm : ∀ r, 0 < r → MeasureTheory.AEStronglyMeasurable (fun θ => B r θ)
    (MeasureTheory.volume.restrict Work.Spaces.Iθ)
  sqint : ∀ r, 0 < r → MeasureTheory.IntegrableOn (fun θ => (B r θ) ^ 2) Work.Spaces.Iθ
  meas : AEMeasurable Φ (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
  int : MeasureTheory.IntegrableOn Φ (Set.Ioi (0 : ℝ))
  intw : MeasureTheory.IntegrableOn (fun r => Work.Spaces.w r * Φ r) (Set.Ioi (0 : ℝ))
  le : (∫ r in Set.Ioi (0 : ℝ), Φ r) ≤ Xs
  lew : (∫ r in Set.Ioi (0 : ℝ), Work.Spaces.w r * Φ r) ≤ Xs

/-- The `(0,0)`-slot `g` of a `SmoothQuad` datum in `ℋ⁴`. -/
theorem slot0 {α : ℝ} {g : Fn} (hsq : Work.FTS.LocData.SmoothQuad g)
    (hmem : Work.Spaces.HkMem α 4 g)
    (hsl0 : MeasureTheory.AEStronglyMeasurable (fun θ => g 0 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    SlotData α g (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g) (Work.Spaces.HkSq α 4 g) := by
  obtain ⟨h0nn, h0sq, h0meas, h0int, h0le⟩ :=
    Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0_props hsq hmem hsl0
  have hle : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g r
        ≤ Work.Spaces.w r * Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g r := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    exact le_mul_of_one_le_left (h0nn r) (one_le_w' hr)
  have hint : MeasureTheory.IntegrableOn
      (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g) (Set.Ioi (0 : ℝ)) :=
    Integrable.mono' h0int h0meas.aestronglyMeasurable
      (hle.mono (fun r hr => by
        rw [Real.norm_of_nonneg (h0nn r)]; exact hr))
  refine ⟨h0nn, ?_, h0sq, h0meas, hint, h0int, ?_, h0le⟩
  · intro r hr
    exact Work.FTS.Nonlinear.Pieces.rl1Pieces.aesm_slice_of_smoothQuad hsq hr
  · refine (integral_mono_ae hint h0int hle).trans h0le

/-- The `(0,1)`-slot `D_θg`. -/
theorem slot1 {α : ℝ} {g : Fn} (hα : 0 ≤ α) (hsq : Work.FTS.LocData.SmoothQuad g)
    (hmem : Work.Spaces.HkMem α 4 g)
    (hsl0 : MeasureTheory.AEStronglyMeasurable (fun θ => Work.Spaces.Dth g 0 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    SlotData α (Work.Spaces.Dth g) (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi1 g)
      (Work.Spaces.HkSq α 4 g) := by
  obtain ⟨h0nn, h0sq, h0meas, h0int, h0le⟩ :=
    Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi1_props hα hsq hmem hsl0
  have hle : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi1 g r
        ≤ Work.Spaces.w r * Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi1 g r := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    exact le_mul_of_one_le_left (h0nn r) (one_le_w' hr)
  have hint : MeasureTheory.IntegrableOn
      (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi1 g) (Set.Ioi (0 : ℝ)) :=
    Integrable.mono' h0int h0meas.aestronglyMeasurable
      (hle.mono (fun r hr => by
        rw [Real.norm_of_nonneg (h0nn r)]; exact hr))
  refine ⟨h0nn, ?_, h0sq, h0meas, hint, h0int, ?_, h0le⟩
  · intro r hr
    exact Work.FTS.Nonlinear.Pieces.rl1Pieces.aesm_slice_Dth_of_smoothQuad hsq hr
  · refine (integral_mono_ae hint h0int hle).trans h0le

/-- The `(1,0)`-slot `D_zg`. -/
theorem slot2 {α : ℝ} {g : Fn} (hsq : Work.FTS.LocData.SmoothQuad g)
    (hmem : Work.Spaces.HkMem α 4 g) :
    SlotData α (Work.Spaces.Dz g) (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi2 g)
      (Work.Spaces.HkSq α 4 g) := by
  obtain ⟨h0nn, h0sq, h0meas, h0int, h0le⟩ :=
    Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi2_props hsq hmem
  have hle : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi2 g r
        ≤ Work.Spaces.w r * Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi2 g r := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    exact le_mul_of_one_le_left (h0nn r) (one_le_w' hr)
  have hint : MeasureTheory.IntegrableOn
      (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi2 g) (Set.Ioi (0 : ℝ)) :=
    Integrable.mono' h0int h0meas.aestronglyMeasurable
      (hle.mono (fun r hr => by
        rw [Real.norm_of_nonneg (h0nn r)]; exact hr))
  refine ⟨h0nn, ?_, h0sq, h0meas, hint, h0int, ?_, h0le⟩
  · intro r hr
    exact Work.FTS.Nonlinear.Pieces.rl1Pieces.aesm_slice_Dz_of_smoothQuad hsq hr
  · refine (integral_mono_ae hint h0int hle).trans h0le

/-! ## The coefficient slot of an `ℋ⁴`-function

For a coefficient `A` in `ℋ⁴`, `angSupHk` bounds `|A|` pointwise by the *angular energy* of
its `HkIntegrand`; the facts below are what the `r`-step needs about that energy. -/

theorem HkSlot_data {α : ℝ} {A : Fn} (hmem : Work.Spaces.HkMem α 4 A) :
    AEMeasurable (fun r => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 A r θ)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) ∧
      MeasureTheory.IntegrableOn
        (fun r => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 A r θ) (Set.Ioi (0 : ℝ)) ∧
      (∫ r in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 A r θ)
        ≤ Work.Spaces.HkSq α 4 A := by
  have hint : MeasureTheory.IntegrableOn
      (fun r => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 A r θ)
      (Set.Ioi (0 : ℝ)) := hmem.2.mono_set Set.Ioi_subset_Ici_self
  refine ⟨hint.aemeasurable, hint, ?_⟩
  rw [show Work.Spaces.HkSq α 4 A
      = ∫ r in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 A r θ
    from rfl]
  refine MeasureTheory.setIntegral_mono_set hmem.2
    (Filter.Eventually.of_forall fun r =>
      MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 A r θ)
    (Filter.Eventually.of_forall fun r hr => Set.mem_Ici.mpr (le_of_lt hr))

/-- **The angular pointwise bound of an `ℋ⁴`-coefficient** (`angSupHk` in the shape used by
the pieces). -/
theorem angSup_le : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (A : Fn),
    0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen A → Work.Spaces.HkMem α 4 A →
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (A z θ) ^ 2 ≤ C / (Work.Spaces.gam α - 1)
        * ∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 A z θ' :=
  angSupHk

/-! ## The identity `K·𝒰 = -3cos³θ·(ℛ - 𝒱)`

This is the pointwise replacement for a bound of `𝒰(Φ̃_*)`: `StarPkgo` bounds `ℛ(Φ̃_*)` and
`𝒱(Φ̃_*)` but never `𝒰(Φ̃_*)`, so every occurrence of `𝒰` in a piece is rewritten through
this identity. -/


/-! ## The pointwise bounds of the star coefficients -/

theorem star_Rop_le {α Cs : ℝ} {Φs : Fn} (hα : 0 < α)
    (hs : Work.FTS.VocabO.StarPkgo α Cs Φs) (z : ℝ) (hz : 0 < z) (θ : ℝ)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ| ≤ max Cs 0 * α := by
  have h1 := Work.FTS.OpenPkg.WDMem_of_WDp_le hs.R.1 hs.R.2 0 0 (by norm_num) z θ hz hθ.1 hθ.2
  simp only [Work.Spaces.mixed_zero_left, Work.Spaces.DzIter_zero] at h1
  have hz1 : (0 : ℝ) < 1 + z := by linarith
  have hfac : Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ
      = (z / (1 + z)) * ((z + 1) / z
          * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ) := by
    field_simp
    ring
  rw [hfac, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ z / (1 + z))]
  calc (z / (1 + z)) * |(z + 1) / z * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ|
      ≤ 1 * |(z + 1) / z * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ| := by
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        rw [div_le_one hz1]; linarith
    _ = |(z + 1) / z * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ| := one_mul _
    _ ≤ Cs * α := h1
    _ ≤ max Cs 0 * α := mul_le_mul_of_nonneg_right (le_max_left Cs 0) hα.le

theorem star_Vop_le {α Cs : ℝ} {Φs : Fn} (hα : 0 < α)
    (hs : Work.FTS.VocabO.StarPkgo α Cs Φs) (z : ℝ) (hz : 0 < z) (θ : ℝ)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    |Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ| ≤ max Cs 0 * α := by
  have h1 := Work.FTS.OpenPkg.WDMem_of_WDp_le hs.V.1 hs.V.2 0 0 (by norm_num) z θ hz hθ.1 hθ.2
  simp only [Work.Spaces.mixed_zero_left, Work.Spaces.DzIter_zero] at h1
  exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left Cs 0) hα.le)


/-! ## The explicit profile bounds of `F_*`, `D_θF_*`, `D_zF_*`, `∂_θF_*` -/

theorem Fstar_pt {α z θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hz : 0 < z)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Construction.Fstar α z θ| ≤ 20 * α * z / (1 + z) ^ 2 :=
  Work.FTS.Nonlinear.Pieces.Rl1.n5_Fstar_abs_le hα hα1 hz hθ

theorem K_Fstar_pt {α z θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hz : 0 < z)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.K θ * Work.Construction.Fstar α z θ| ≤ 60 * α * z / (1 + z) ^ 2 := by
  have h1 := Fstar_pt hα hα1 hz hθ
  have h2 : Work.Spaces.K θ ≤ 3 :=
    Work.FTS.Nonlinear.Pieces.rl1Pieces.PggTools.K_le_three θ
  have h3 : 0 ≤ Work.Spaces.K θ :=
    Work.FTS.Nonlinear.Pieces.rl1Pieces.PggTools.K_nonneg_of_mem_Iθ hθ
  rw [abs_mul, abs_of_nonneg h3]
  have h4 : (0 : ℝ) ≤ 20 * α * z / (1 + z) ^ 2 := by positivity
  calc Work.Spaces.K θ * |Work.Construction.Fstar α z θ|
      ≤ 3 * (20 * α * z / (1 + z) ^ 2) := mul_le_mul h2 h1 (abs_nonneg _) (by norm_num)
    _ = 60 * α * z / (1 + z) ^ 2 := by ring

theorem DthFstar_pt {α z θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hz : 0 < z)
    (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    |Work.Spaces.Dth (Work.Construction.Fstar α) z θ|
      ≤ (80 / 3) * α ^ 2 * (z / (1 + z) ^ 2) := by
  have hc : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
  have hc0 : 0 < Work.Spaces.c α := by linarith
  have hG : 0 ≤ Work.Spaces.Gam α θ ∧ Work.Spaces.Gam α θ ≤ 1 :=
    Work.Spaces.Gam_bounds α θ hα ⟨hθ0.le, hθ1.le⟩
  have hq : |Work.Spaces.qfun θ| ≤ 4 / 3 := by
    rw [Work.Spaces.qfun_apply, abs_le]
    constructor <;> nlinarith [Real.neg_one_le_cos (2 * θ), Real.cos_le_one (2 * θ)]
  have hshape := (Work.FTS.Nonlinear.Pieces.rl1Tools.FzShape α hα).2.1 z θ hθ0 hθ1
  have hF : 0 < Work.FM.Fstar z := by
    rw [show Work.FM.Fstar z = 2 * z / (1 + z) ^ 2 from rfl]
    positivity
  have hval : |Work.Spaces.Dth (Work.Construction.Fstar α) z θ|
      = α ^ 2 * (|Work.Spaces.qfun θ| * Work.Spaces.Gam α θ / Work.Spaces.c α)
          * (2 * z / (1 + z) ^ 2) := by
    rw [hshape, abs_mul, abs_mul, abs_div, abs_mul, abs_of_nonneg (sq_nonneg α),
      abs_of_nonneg hG.1, abs_of_pos hc0, abs_of_nonneg hF.le,
      show Work.FM.Fstar z = 2 * z / (1 + z) ^ 2 from rfl]
  rw [hval]
  have hcd : Work.Spaces.Gam α θ / Work.Spaces.c α ≤ 10 := by
    rw [div_le_iff₀ hc0]; nlinarith [hG.2]
  have h3 : |Work.Spaces.qfun θ| * Work.Spaces.Gam α θ / Work.Spaces.c α ≤ (4 / 3) * 10 := by
    have hnum : |Work.Spaces.qfun θ| * Work.Spaces.Gam α θ ≤ 4 / 3 := by
      nlinarith [hq, hG.1, hG.2, abs_nonneg (Work.Spaces.qfun θ)]
    rw [div_le_iff₀ hc0]
    nlinarith [hnum, hc]
  calc α ^ 2 * (|Work.Spaces.qfun θ| * Work.Spaces.Gam α θ / Work.Spaces.c α)
        * (2 * z / (1 + z) ^ 2)
      ≤ α ^ 2 * ((4 / 3) * 10) * (2 * z / (1 + z) ^ 2) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left h3 (sq_nonneg α)
    _ = (80 / 3) * α ^ 2 * (z / (1 + z) ^ 2) := by ring


theorem DzFstar_pt {α z θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hz : 0 < z)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.Dz (Work.Construction.Fstar α) z θ| ≤ 20 * α * (z / (1 + z) ^ 2) := by
  have hz1 : (-1 : ℝ) < z := by linarith
  have hc : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
  have hc0 : 0 < Work.Spaces.c α := by linarith
  have hG : 0 ≤ Work.Spaces.Gam α θ ∧ Work.Spaces.Gam α θ ≤ 1 :=
    Work.Spaces.Gam_bounds α θ hα hθ
  have hshape := (Work.FTS.Nonlinear.Pieces.rl1Tools.FzShape α hα).2.2 z θ hz1
  have hderiv : deriv Work.FM.Fstar z = 2 * (1 - z) / (1 + z) ^ 3 :=
    (Work.FM.hasDerivAt_Fstar z hz1).deriv
  rw [hshape, hderiv, abs_mul, abs_mul, abs_of_nonneg hα.le,
    abs_div, abs_of_nonneg hG.1, abs_of_pos hc0]
  have hcd : Work.Spaces.Gam α θ / Work.Spaces.c α ≤ 10 := by
    rw [div_le_iff₀ hc0]; nlinarith [hG.2]
  have h2 : |z * (2 * (1 - z) / (1 + z) ^ 3)| ≤ 2 * z / (1 + z) ^ 2 := by
    have h1z : (0 : ℝ) < 1 + z := by linarith
    rw [abs_mul, abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_pow,
      abs_of_nonneg h1z.le, abs_of_nonneg hz.le]
    rw [show (2 * z / (1 + z) ^ 2) = z * (2 / (1 + z) ^ 2) from by ring]
    refine mul_le_mul_of_nonneg_left ?_ hz.le
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 : |1 - z| ≤ 1 + z := by
      rw [abs_le]; constructor <;> nlinarith
    nlinarith [sq_nonneg z, sq_nonneg (1 + z), hz.le]
  have hnn : (0 : ℝ) ≤ 2 * z / (1 + z) ^ 2 := by positivity
  calc α * (Work.Spaces.Gam α θ / Work.Spaces.c α) * |z * (2 * (1 - z) / (1 + z) ^ 3)|
      ≤ α * 10 * (2 * z / (1 + z) ^ 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hcd hα.le) h2 (abs_nonneg _) (by positivity)
    _ = 20 * α * (z / (1 + z) ^ 2) := by ring

theorem K_DzFstar_pt {α z θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hz : 0 < z)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.K θ * Work.Spaces.Dz (Work.Construction.Fstar α) z θ|
      ≤ 60 * α * (z / (1 + z) ^ 2) := by
  have h1 := DzFstar_pt hα hα1 hz hθ
  have h2 : Work.Spaces.K θ ≤ 3 :=
    Work.FTS.Nonlinear.Pieces.rl1Pieces.PggTools.K_le_three θ
  have h3 : 0 ≤ Work.Spaces.K θ :=
    Work.FTS.Nonlinear.Pieces.rl1Pieces.PggTools.K_nonneg_of_mem_Iθ hθ
  rw [abs_mul, abs_of_nonneg h3]
  have h4 : (0 : ℝ) ≤ 20 * α * (z / (1 + z) ^ 2) := by positivity
  calc Work.Spaces.K θ * |Work.Spaces.Dz (Work.Construction.Fstar α) z θ|
      ≤ 3 * (20 * α * (z / (1 + z) ^ 2)) :=
        mul_le_mul h2 h1 (abs_nonneg _) (by norm_num)
    _ = 60 * α * (z / (1 + z) ^ 2) := by ring

theorem K_pthFstar_pt {α r θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hr : 0 < r)
    (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    |Work.Spaces.K θ * Work.Spaces.pth (Work.Construction.Fstar α) r θ|
      ≤ 80 * α ^ 2 * (r / (1 + r) ^ 2) :=
  Work.FTS.Nonlinear.Pieces.rl1Pieces.abs_K_pth_Fstar_le hα hα1 hr hθ0 hθ1

theorem FK_Fstar_pt {α z : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.Construction.FK (Work.Construction.Fstar α) z = α * (2 * z / (1 + z) ^ 2) :=
  Work.FTS.Nonlin.FK_Fstar hα hα1

theorem FK_g_pt {g : Fn} {s : ℝ} (hs : 0 < s)
    (hg : MeasureTheory.IntegrableOn (fun θ => (g s θ) ^ 2) Work.Spaces.Iθ)
    (hgm : MeasureTheory.AEStronglyMeasurable (fun θ => g s θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    |Work.Construction.FK g s| ≤ 4 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2) :=
  Work.FTS.Nonlinear.Pieces.Rl1.n5_FK_abs_le hs hg hgm

/-- **A bounded slot is bounded in `L¹` by its `L²`-energy.**  The `L₁₂`-pieces whose slot is
`L²`-bounded but not pointwise bounded (the `D_θg`-slot of the `N₂^{∗g}` piece) are estimated
through this. -/
theorem lintegral_abs_le_sqrt {B : ℝ → ℝ → ℝ} {r : ℝ}
    (hBm : MeasureTheory.AEStronglyMeasurable (fun θ => B r θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hBi : MeasureTheory.IntegrableOn (fun θ => (B r θ) ^ 2) Work.Spaces.Iθ) :
    (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |B r θ|)
      ≤ ENNReal.ofReal (Real.sqrt (Real.pi / 2))
          * (ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, (B r θ) ^ 2)) ^ (1 / 2 : ℝ) := by
  have hvol : MeasureTheory.volume (Set.Icc (0 : ℝ) (Real.pi / 2))
      = ENNReal.ofReal (Real.pi / 2) := by
    rw [Real.volume_Icc, sub_zero]
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hone : (∫⁻ _θ in Work.Spaces.Iθ, (1 : ENNReal) ^ (2 : ℝ))
      = ENNReal.ofReal (Real.pi / 2) := by
    rw [show (1 : ENNReal) ^ (2 : ℝ) = 1 from by simp]
    rw [MeasureTheory.setLIntegral_const, one_mul]
    exact hvol
  have hg2 : (∫⁻ θ in Work.Spaces.Iθ, (ENNReal.ofReal |B r θ|) ^ (2 : ℝ))
      = ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, (B r θ) ^ 2) := by
    rw [MeasureTheory.setLIntegral_congr_fun hIθ (fun θ _ => by
      rw [ofReal_rpow_two' (abs_nonneg _), sq_abs])]
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hBi
      (Filter.Eventually.of_forall (fun θ => sq_nonneg _))]
  have hgm : AEMeasurable (fun θ => ENNReal.ofReal |B r θ|)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    hBm.aemeasurable.norm.ennreal_ofReal
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq
    (MeasureTheory.volume.restrict Work.Spaces.Iθ) (p := 2) (q := 2)
    Real.HolderConjugate.two_two (f := fun _ : ℝ => ENNReal.ofReal (1 : ℝ))
    (g := fun θ => ENNReal.ofReal |B r θ|)
    aestronglyMeasurable_const.aemeasurable hgm
  simp only [Pi.mul_apply, ENNReal.ofReal_one, one_mul] at hholder
  rw [hone, hg2] at hholder
  rw [ofReal_rpow_half (by positivity : (0 : ℝ) ≤ Real.pi / 2)] at hholder
  exact hholder

/-! ## The envelope of the `rl1` estimate -/

/-- The envelope `α² + √α·X + α^{-3/2}·X²` of the `rl1` zero-mode estimate, with
`X = Xn α g = |g|_{ℋ⁴}`.  Every piece of `N` is estimated by a multiple of it, and the
constants are added in the assembly. -/
def Env (α : ℝ) (g : Fn) : ℝ :=
  α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
    + α ^ (-(3 / 2 : ℝ)) * (Work.FTS.Nonlin.Xn α g) ^ 2

theorem Env_nonneg {α : ℝ} (g : Fn) (hα : 0 ≤ α) : 0 ≤ Env α g := by
  refine add_nonneg (add_nonneg (sq_nonneg α) ?_) ?_
  · exact mul_nonneg (Real.sqrt_nonneg α) (Work.Spaces.HkNorm_nonneg α 4 g)
  · exact mul_nonneg (Real.rpow_nonneg hα _) (sq_nonneg _)

end Work.FTS.NonlinRows.Rl1
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.StarDefs =====
section

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

/-- The `σ`-normalised zero-moment Dirichlet solution `v = u/σ` of `L₀u = h`:
`v' = −μ^{-1}∫_0^θ μh/σ` with `μ = sin²θcos³θ`.  (At `θ = π/2` the expression is Lean's junk
`0`; only the open interval is used.) -/
def Linv (h : ℝ → ℝ) : ℝ → ℝ := fun θ =>
  -((Real.sin θ ^ 2 * Real.cos θ ^ 3)⁻¹ *
    (∫ θ' in (0 : ℝ)..θ,
      Real.sin θ' ^ 2 * Real.cos θ' ^ 3 * h θ' / Work.Construction.s2 θ'))

/-- The iterates `𝒜^j φ` of the radial operator `𝒜a = αz²a'' + (5+α)z a'` applied to
`φ = VocabO.phiR`; `phiAj 1 = VocabO.phiA`.  Node P-C1 needs `𝒜²φ`, `𝒜³φ`. -/
def phiAj : ℕ → ℝ → ℝ → ℝ
  | 0 => fun _ z => Work.FTS.VocabO.phiR z
  | (j + 1) => fun α z =>
      α * z ^ 2 * iteratedDeriv 2 (phiAj j α) z + (5 + α) * z * deriv (phiAj j α) z

/-- **The zero-moment Dirichlet inverse itself**: `LinvI h = ∫_0^θ Linv h`, i.e. the `v` with
`L₀(sin 2θ · v) = h`.  (`Linv` is its derivative `v'`; the consumer needs `v`, and the identity
`L₀(σ·LinvI h) = h` is the node `LinvI_solves`.) -/
def LinvI (h : ℝ → ℝ) : ℝ → ℝ := fun θ => ∫ θ' in (0 : ℝ)..θ, Linv h θ'




/-- Boundedness of the first `l` derivatives of a source on `(0,∞)`; the hypothesis under which
the mode-wise radial Green function is estimated in node P-C2. -/
def BddDeriv (l : ℕ) (c : ℝ → ℝ) (K : ℝ) : Prop :=
  ∀ k : ℕ, k ≤ l → ∀ z : ℝ, 0 < z → |iteratedDeriv k c z| ≤ K

end Work.FTS.PhiStar
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.Vocab =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

open Work.FTS.Galerkin (Fn Fam slice gdot dynLin dynRHS IsDynEqOn IsDynGSolWith IsDynEq
  galFun galFam Slab)
open Work.FTS.Nonlin (Xn RegQ)
open Work.FTS.VocabO (HQo CoefTh CoefThMem WDp WDMem)
open Work.FTS.VocabO2 (StarPkgo2)
open Work.Coercivity (LGammaT HkIPStep H1IP wip)
open Work.Spaces (HkMem HkSq HkNorm Dz Dth mixed pth pzIter DthIter DzIter)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The elliptic law of the strong route

`IsBslSolPos` is the *positivised* elliptic (Biot–Savart) law of the strong-solution route: the
paper's (PolarBSL) problem on the open quadrant, with the Dirichlet data `Ψ z 0 = Ψ z (π/2) = 0`
asserted only for `z ≥ 0` (the frozen `Work.Elliptic.IsBslSol` asks it for every real `z`, which no
solution of the local problem with data on `Iz` satisfies — `FTS_INTEGRATION_AUDIT.md` §3), plus the
decay at infinity.  It is the `Law` argument of `IsDynGSolWith` in this route.

The definition is *character-for-character* the one of the sibling area `FTS/StrongLWP`
(`Work.FTS.StrongLWP.IsBslSolPos`, `StrongLWP/Defs.lean`) and logically the one of
`Work.FTS.Open3.IsBslSolPos`; `StrongPersist/Basic.lean` records the (definitional) bridge to the
former.  It is repeated here — and not imported — so that this chapter's core does not depend on
the `Open3`/`Open2`/`OpenPkg` chain. -/
def IsBslSolPos (α : ℝ) (F Ψ : Fn) : Prop :=
  (∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ) ∧
    (∀ z, 0 ≤ z → Ψ z 0 = 0 ∧ Ψ z (π / 2) = 0) ∧
      (∀ θ ∈ Work.Spaces.Iθ, Tendsto (fun z => Ψ z θ) atTop (𝓝 0))

/-! ## The level-six norm and inner product -/

/-- The `ℋ⁶`-norm of a profile: `Xn6 α f = |f|_{ℋ⁶}`.  (`Xn α f` of `FTS/Vocab.lean` is
`|f|_{ℋ⁴}`.) -/
abbrev Xn6 (α : ℝ) (f : Fn) : ℝ := Work.Spaces.HkNorm α 6 f

/-- Membership in `ℋ⁶`. -/
abbrev H6Mem (α : ℝ) (f : Fn) : Prop := Work.Spaces.HkMem α 6 f

/-- **The level-six coercivity class.**  The paper's coercivity of `𝓛_Γ^T` on `ℋ^k` is *not* a
statement about the whole space: the nonlocal term `L₁₂` and the behaviour at the axis and at the
angular ends matter.  The class below is the level-six instance of the class the coercivity
chapter's corrected induction lives on (`Vocab.CoerAdm` with `RegQ α 5` replaced by the honest
`HQo α 6`): the slice is in the honest `ℋ⁶`-class, vanishes on the two angular boundary lines, its
axis values and first radial derivative vanish at `z = 0`, and the zero mode `L₁₂(f)(0)` is zero
(the projector condition of the paper). -/
structure H6Adm (α : ℝ) (f : Fn) : Prop where
  /-- the honest `ℋ⁶`-class. -/
  reg : HQo α 6 f
  /-- vanishing on the angular boundary lines. -/
  vanish : Work.Spaces.VanishTheta f
  /-- vanishing of the values and the first radial derivative at the axis. -/
  axis : ∀ θ ∈ Work.Spaces.Iθ, f 0 θ = 0 ∧ Work.Spaces.pz f 0 θ = 0
  /-- the projector condition: the zero mode of `L₁₂` vanishes. -/
  l12 : Work.Construction.L12 f 0 = 0

/-- `HkSq α 6 f`, the square of the `ℋ⁶` norm (a name of its own for readability). -/
abbrev Sq6 (α : ℝ) (f : Fn) : ℝ := Work.Spaces.HkSq α 6 f

/-- The linear part `-𝓛_Γ^T f` of the fake-time equation as a function of the profile: by
`rfl`, `dynLin α g τ = linPart α (slice g τ)`.  (This is a definition, not an abbreviation, so
that `dynLin α g τ = linPart α (slice g τ)` holds by `rfl`.) -/
def linPart (α : ℝ) (f : Fn) : Fn := fun z θ => -(LGammaT α f z θ)

/-- **The `ℋ⁶` inner product.**  `IP6 e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' α` is the paper's
recursion (tex 686)

`IP^{k+1} = HkIPStep c₁ c₂ IP^k = IP^k + c₁ IP^k(D_θ·, D_θ·) + c₂ IP^k(D_z·, D_z·)`

applied twice on top of the `ℋ⁴` inner product `CoercivityFix.Assembly.IP4` of the coercivity
chapter: `IP6 = HkIPStep e₁ e₂ (HkIPStep f₁ f₂ IP4)`.

All ten coefficients are free: the coercivity of the level-six operator is a property of the
*coefficients*, and the design's small-step choice lives in the lower levels
(`CoercivityFix/Assembly/Defs.lean`).  The package `H6Coer` below asserts the properties of
`IP6` for the coefficients that the coercivity chapter's induction produces. -/
def IP6 (e₁ e₂ f₁ f₂ c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ) (α : ℝ) : Fn → Fn → ℝ :=
  HkIPStep e₁ e₂
    (HkIPStep f₁ f₂
      (Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α))


theorem dynLin_eq_linPart (α : ℝ) (g : Fam) (τ : ℝ) :
    dynLin α g τ = linPart α (slice g τ) := rfl

/-! ## The strong-solution predicate on `[0,T)` -/

/-- **The dynamic modulated equation on the half-open interval `[0,T)`.**  This is
`Galerkin.IsDynEqOn` cut down to `τ < T`; the derivative is taken *within* `[0,T)`, the honest
formulation for a solution whose maximal interval of existence is `[0,T)`. -/
def IsDynEqOnUpTo (α : ℝ) (Φ g : Fam) (T : ℝ) : Prop :=
  ∀ z θ τ, 0 ≤ τ → τ < T → (z, θ) ∈ Work.Construction.Qd →
    HasDerivWithinAt (fun s => g z θ s)
      (dynLin α g τ z θ + dynRHS α Φ g τ z θ) (Set.Ico 0 T) τ

/-- **A strong solution of the dynamic modulated problem on `[0,T)`**, with the corrected
elliptic law `IsBslSolPos` of design §1/§4. -/
def IsStrongSolOn (α : ℝ) (Φ g : Fam) (T : ℝ) : Prop :=
  (∀ τ, 0 ≤ τ → τ < T → IsBslSolPos α (Work.Construction.Ftau α g τ) (slice Φ τ)) ∧
    IsDynEqOnUpTo α Φ g T


/-- A strong solution on `[0,T)` is a strong solution on every `[0,T')` with `T' ≤ T`. -/
theorem IsStrongSolOn.mono {α T T' : ℝ} {Φ g : Fam} (h : IsStrongSolOn α Φ g T)
    (hT : T' ≤ T) : IsStrongSolOn α Φ g T' :=
  ⟨fun τ hτ hτT => h.1 τ hτ (lt_of_lt_of_le hτT hT),
    fun z θ τ hτ hτT hz =>
      (h.2 z θ τ hτ (lt_of_lt_of_le hτT hT) hz).mono (Set.Ico_subset_Ico_right hT)⟩




/-! ## The regularity packages

`RegPkgMin` is copied **verbatim** from design §1 (`FTS_STRONG_ROUTE.md`); only the names are
qualified. -/
structure RegPkgMin (α : ℝ) (g : Fam) : Prop where
  c1     : ContDiffOn ℝ 1 (fun p : ℝ×ℝ×ℝ => g p.1 p.2.1 p.2.2) (Ioi 0 ×ˢ Ioo 0 (π/2) ×ˢ Ioi 0)
  c4     : ∀ τ, 0 ≤ τ → ContDiffOn ℝ 4 (Function.uncurry (slice g τ)) Work.FTS.EllipticEst.Q0
  cont   : ∀ z θ, (z,θ) ∈ Work.Construction.Qd → ContinuousOn (fun τ => g z θ τ) (Ici 0)
  mem4   : ∀ τ, 0 ≤ τ → Work.Spaces.HkMem α 4 (slice g τ)
  dbd : ∀ S, 0 < S → ∃ Cd, ∀ τ, 0 < τ → τ < S →
    Work.Spaces.HkMem α 3 (gdot g τ) ∧ Work.Spaces.HkNorm α 3 (gdot g τ) ≤ Cd
  vanish : ∀ τ, 0 ≤ τ → ∀ z, 0 ≤ z → g z 0 τ = 0 ∧ g z (π/2) τ = 0

/-- `RegPkgMin` with the `ℋ⁶`-membership and the uniform `ℋ⁶` bound added: what S1–S2
produce and what S5 hands on to the regularity transfer. -/
structure RegPkgH6 (α C : ℝ) (g : Fam) : Prop where
  min : RegPkgMin α g
  mem6 : ∀ τ, 0 ≤ τ → H6Mem α (slice g τ)
  bd6 : ∀ τ, 0 ≤ τ → Xn6 α (slice g τ) ≤ C

end Work.FTS.StrongPersist
end
end
