/-
Copyright: work module for the Elgindi finite-time singularity project.

# Slice honesty of the cut-energy identities

This module proves `Work.FTS.EllipticEst.Prop.CutEnergyAux.sliceFacts`: for every datum
`AeData α u G` of the almost-everywhere class of the level-`0` elliptic estimate and every
`z > 0`, the eleven `θ`-integrands occurring in the cut-energy identities are `θ`-integrable
on `Iθ = [0,π/2]`.

## Route

Everything is dominated, a.e. on `Iθ`, by one of the five *σ-weighted* slices

* `u(z,·)² σ`, `G(z,·)² σ`, `(z²∂_z²u)(z,·)² σ`, `(z∂_zu)(z,·)² σ`, `(∂_θ²u)(z,·)² σ`,

with `σ = sEta θ = sin(2θ)^{-η}`, each of which is `θ`-integrable by
`Dispatch.slice_sigma_sq_of_hkMem_D` applied to the corresponding `ℋ⁰`-membership of the
datum (`Dispatch.hkMem_uM`, `Dispatch.hkMem_gradUD`, and the fields `memG`, `memRad2`,
`memAng2` of `AeData`).

The two transfers used throughout are:

* `σ ≥ 1` on the open interval `(0,π/2)`, so `F²` is dominated by `F²σ` there
  (`integrableOn_sq_of_sigma`), and `|FG| ≤ (F²σ + G²σ)/2` there
  (`integrableOn_mul_of_sigma`);
* `(0,π/2)` and `Iθ` differ by the two endpoints, a null set, so the two `IntegrableOn`
  statements are equivalent (`restrict_Iθ_eq_Ioo`).

The two `Lzero`/`bslOp` pairings use the pointwise equation
`Lzero u = bslOp α u + α²z²∂_z²u + α(5+α)z∂_zu` together with `bslOp α u = G` on the open
quadrant (`AeData.eq`), which reduces them to the pairings `G·u`, `(z²∂_z²u)·u`,
`(z∂_zu)·u` covered by the above.  The slice continuities needed for the a.e. strong
measurability come from the `SmoothOpen` calculus of `OpenQDefs` (via
`continuousOn_slice_of_smoothOpen`) and from `Endpt.continuousOn_pthIter2_of_strip`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.Dispatch.hkMemUD
import Submission.Work.FTS.EllipticEst.Dispatch.hkMemGradUD
import Submission.Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Prop.CutEnergyAux

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Elementary tooling -/

/-- The interval `Iθ = [0,π/2]` and the open interval `(0,π/2)` carry the same restriction of
Lebesgue measure (they differ by the two endpoints, a null set). -/
private theorem restrict_Iθ_eq_Ioo :
    volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
  (Measure.restrict_congr_set (by
    rw [Work.Spaces.Iθ]
    exact Ioo_ae_eq_Icc)).symm

/-- `σ = sEta θ = sin(2θ)^{-η}` is nonnegative on `Iθ`. -/
private theorem sEta_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.sEta θ :=
  Real.rpow_nonneg
    (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])) _

/-- `F²` is integrable on `Iθ` as soon as `F` is continuous on `(0,π/2)` and `F²σ` is
integrable on `Iθ`: on the open interval `σ ≥ 1`, and the endpoints are null. -/
private theorem integrableOn_sq_of_sigma {F : ℝ → ℝ}
    (hcont : ContinuousOn F (Set.Ioo 0 (Real.pi / 2)))
    (hint : IntegrableOn (fun θ => (F θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ) :
    IntegrableOn (fun θ => (F θ) ^ 2) Work.Spaces.Iθ := by
  have hint' : Integrable (fun θ => (F θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (volume.restrict (Set.Ioo 0 (Real.pi / 2))) := by
    simpa only [IntegrableOn, restrict_Iθ_eq_Ioo] using hint
  have hmain : Integrable (fun θ => (F θ) ^ 2)
      (volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    Integrable.mono' hint' ((hcont.pow 2).aestronglyMeasurable measurableSet_Ioo) (by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact le_mul_of_one_le_right (sq_nonneg _)
        (Work.FTS.EllipticEst.Dispatch.one_le_sEta_D hθ))
  simpa only [IntegrableOn, restrict_Iθ_eq_Ioo] using hmain

/-- `F·H` is integrable on `Iθ` as soon as `F`, `H` are continuous on `(0,π/2)` and `F²σ` and
`H²σ` are integrable on `Iθ` (AM–GM and `σ ≥ 1` on the open interval). -/
private theorem integrableOn_mul_of_sigma {F H : ℝ → ℝ}
    (hFcont : ContinuousOn F (Set.Ioo 0 (Real.pi / 2)))
    (hHcont : ContinuousOn H (Set.Ioo 0 (Real.pi / 2)))
    (hF : IntegrableOn (fun θ => (F θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ)
    (hH : IntegrableOn (fun θ => (H θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ) :
    IntegrableOn (fun θ => F θ * H θ) Work.Spaces.Iθ := by
  have hF' : Integrable (fun θ => (F θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (volume.restrict (Set.Ioo 0 (Real.pi / 2))) := by
    simpa only [IntegrableOn, restrict_Iθ_eq_Ioo] using hF
  have hH' : Integrable (fun θ => (H θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (volume.restrict (Set.Ioo 0 (Real.pi / 2))) := by
    simpa only [IntegrableOn, restrict_Iθ_eq_Ioo] using hH
  have hsum : Integrable (fun θ => (F θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
      + (H θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    hF'.add hH'
  have hmain : Integrable (fun θ => F θ * H θ)
      (volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    Integrable.mono' (hsum) ((hFcont.mul hHcont).aestronglyMeasurable measurableSet_Ioo) (by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
        have h1 : (1 : ℝ) ≤ Work.FTS.EllipticEst.sEta θ :=
          Work.FTS.EllipticEst.Dispatch.one_le_sEta_D hθ
        have hAM : |F θ| * |H θ| ≤ ((F θ) ^ 2 + (H θ) ^ 2) / 2 := by
          nlinarith [sq_nonneg (|F θ| - |H θ|), sq_abs (F θ), sq_abs (H θ),
            abs_nonneg (F θ), abs_nonneg (H θ)]
        have hle1 : (F θ) ^ 2 ≤ (F θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
          calc (F θ) ^ 2 = (F θ) ^ 2 * 1 := (mul_one _).symm
            _ ≤ (F θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
                mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
        have hle2 : (H θ) ^ 2 ≤ (H θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
          calc (H θ) ^ 2 = (H θ) ^ 2 * 1 := (mul_one _).symm
            _ ≤ (H θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
                mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
        have hnn : (0 : ℝ) ≤ (F θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
            + (H θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
          add_nonneg (mul_nonneg (sq_nonneg _) (le_trans zero_le_one h1))
            (mul_nonneg (sq_nonneg _) (le_trans zero_le_one h1))
        rw [Real.norm_eq_abs, abs_mul]
        linarith)
  simpa only [IntegrableOn, restrict_Iθ_eq_Ioo] using hmain

/-- The `θ`-slice of a function which is `C^∞` on the open quadrant is continuous on
`(0,π/2)`. -/
private theorem continuousOn_slice_of_smoothOpen {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) {z : ℝ} (hz : 0 < z) :
    ContinuousOn (fun θ => F z θ) (Set.Ioo 0 (Real.pi / 2)) := by
  have hmap : MapsTo (fun θ : ℝ => (z, θ)) (Set.Ioo 0 (Real.pi / 2))
      Work.FTS.EllipticEst.Q0 := fun θ hθ => ⟨hz, hθ⟩
  have hcont : ContinuousOn (fun θ : ℝ => (z, θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    (continuous_const.prodMk continuous_id).continuousOn
  have hcomp := hF.continuousOn.comp hcont hmap
  exact hcomp

/-- `((c·A)·B)·c⁻¹ = A·B` for `c ≠ 0`. -/
private theorem mul_eq_mul_inv {c A B : ℝ} (hc : c ≠ 0) : ((c * A) * B) * c⁻¹ = A * B := by
  field_simp

/-- `(c·A)²·(c²)⁻¹ = A²` for `c ≠ 0`. -/
private theorem sq_eq_sq_mul_inv_sq {c A : ℝ} (hc : c ≠ 0) : ((c * A) ^ 2) * (c ^ 2)⁻¹ = A ^ 2 := by
  field_simp

/-! ## The main theorem -/

theorem sliceFacts (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      MeasureTheory.IntegrableOn (fun θ => Work.Elliptic.bslOp α u z θ * u z θ)
          Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn (fun θ => Work.Elliptic.Lzero u z θ * u z θ)
          Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn (fun θ => Work.Spaces.pzIter 2 u z θ * u z θ)
          Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn (fun θ => Work.Spaces.pz u z θ * u z θ)
          Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn (fun θ => (z * Work.Spaces.pz u z θ) ^ 2)
          Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn (fun θ => (u z θ) ^ 2) Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pz u z θ) ^ 2)
          Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pzIter 2 u z θ) ^ 2)
          Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn (fun θ => (G z θ) ^ 2) Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn (fun θ => (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pthIter 2 u z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
  intro z hz
  have hzpos : 0 < z := hz
  -- ## the smoothness classes
  have hUso : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => h.smooth n)
  have hGso : Work.FTS.EllipticEst.SmoothOpen G :=
    Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
      (Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen (α := α) hUso)
      (fun z θ hz hθ hθ' => h.eq z hz θ hθ hθ')
  -- ## continuity of the slices on the open interval
  have hcnt_u : ContinuousOn (fun θ => u z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    continuousOn_slice_of_smoothOpen hUso hzpos
  have hcnt_pz : ContinuousOn (fun θ => Work.Spaces.pz u z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    continuousOn_slice_of_smoothOpen (hUso.pz) hzpos
  have hcnt_pz2 : ContinuousOn (fun θ => Work.Spaces.pzIter 2 u z θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
    continuousOn_slice_of_smoothOpen (hUso.pzIter 2) hzpos
  have hcnt_B : ContinuousOn (fun θ => Work.Spaces.pthIter 2 u z θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.Endpt.continuousOn_pthIter2_of_strip h.smooth hzpos
  have hcnt_G : ContinuousOn (fun θ => G z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    continuousOn_slice_of_smoothOpen hGso hzpos
  -- ## the five `σ`-weighted honest slices
  have P1 : IntegrableOn (fun θ => (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.Dispatch.slice_sigma_sq_of_hkMem_D
      (Work.FTS.EllipticEst.Dispatch.hkMem_uM α u G h) hzpos
  have P2 : IntegrableOn (fun θ => (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.Dispatch.slice_sigma_sq_of_hkMem_D h.memG hzpos
  have P3 : IntegrableOn
      (fun θ => (z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.Dispatch.slice_sigma_sq_of_hkMem_D h.memRad2 hzpos
  have P4 : IntegrableOn
      (fun θ => (z * Work.Spaces.pz u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
    have h4 := Work.FTS.EllipticEst.Dispatch.slice_sigma_sq_of_hkMem_D
      (Work.FTS.EllipticEst.Dispatch.hkMem_gradUD α u G h) hzpos
    simpa only [Work.FTS.EllipticEst.H2W.Ae.grad] using h4
  have P5 : IntegrableOn
      (fun θ => (Work.Spaces.pthIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.Dispatch.slice_sigma_sq_of_hkMem_D h.memAng2 hzpos
  -- ## the `Lzero` decomposition on the open quadrant
  have hLz : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.Elliptic.Lzero u z θ * u z θ
        = G z θ * u z θ + α ^ 2 * ((z ^ 2 * Work.Spaces.pzIter 2 u z θ) * u z θ)
          + (α * (5 + α)) * ((z * Work.Spaces.pz u z θ) * u z θ) := by
    intro θ hθ
    have heq := h.eq z hzpos θ hθ.1 hθ.2
    rw [Work.Elliptic.bslOp_apply] at heq
    have hL : Work.Elliptic.Lzero u z θ
        = G z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 u z θ)
          + α * (5 + α) * (z * Work.Spaces.pz u z θ) := by linarith
    rw [hL]; ring
  -- ## the pairings
  -- `G · u`
  have hGu : IntegrableOn (fun θ => G z θ * u z θ) Work.Spaces.Iθ :=
    integrableOn_mul_of_sigma hcnt_G hcnt_u P2 P1
  -- `(z² ∂_z²u) · u` and `(z ∂_zu) · u`
  have hAu : IntegrableOn (fun θ => (z ^ 2 * Work.Spaces.pzIter 2 u z θ) * u z θ)
      Work.Spaces.Iθ :=
    integrableOn_mul_of_sigma (hcnt_pz2.const_mul (z ^ 2)) hcnt_u P3 P1
  have hDu : IntegrableOn (fun θ => (z * Work.Spaces.pz u z θ) * u z θ) Work.Spaces.Iθ :=
    integrableOn_mul_of_sigma (hcnt_pz.const_mul z) hcnt_u P4 P1
  -- squares
  have hD2 : IntegrableOn (fun θ => (z * Work.Spaces.pz u z θ) ^ 2) Work.Spaces.Iθ :=
    integrableOn_sq_of_sigma (hcnt_pz.const_mul z) P4
  have hu2 : IntegrableOn (fun θ => (u z θ) ^ 2) Work.Spaces.Iθ :=
    integrableOn_sq_of_sigma hcnt_u P1
  have hG2 : IntegrableOn (fun θ => (G z θ) ^ 2) Work.Spaces.Iθ :=
    integrableOn_sq_of_sigma hcnt_G P2
  have hA2 : IntegrableOn (fun θ => (z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2)
      Work.Spaces.Iθ :=
    integrableOn_sq_of_sigma (hcnt_pz2.const_mul (z ^ 2)) P3
  -- ## the eleven conjuncts
  refine ⟨?_, ?_, ?_, ?_, hD2, hu2, ?_, ?_, hG2, P2, P5⟩
  · -- 1. `bslOp α u · u`
    refine Integrable.congr hGu ?_
    rw [restrict_Iθ_eq_Ioo]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    rw [h.eq z hzpos θ hθ.1 hθ.2]
  · -- 2. `Lzero u · u`
    have hsum : IntegrableOn (fun θ => G z θ * u z θ
        + α ^ 2 * ((z ^ 2 * Work.Spaces.pzIter 2 u z θ) * u z θ)
        + (α * (5 + α)) * ((z * Work.Spaces.pz u z θ) * u z θ)) Work.Spaces.Iθ :=
      (hGu.add (hAu.const_mul (α ^ 2))).add (hDu.const_mul (α * (5 + α)))
    refine Integrable.congr hsum ?_
    rw [restrict_Iθ_eq_Ioo]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    exact (hLz θ hθ).symm
  · -- 3. `∂_z²u · u`
    have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hzpos)
    have hscaled := hAu.mul_const ((z ^ 2)⁻¹)
    refine Integrable.congr hscaled (Filter.Eventually.of_forall fun θ => ?_)
    exact mul_eq_mul_inv hz2
  · -- 4. `∂_zu · u`
    have hscaled := hDu.mul_const (z⁻¹)
    refine Integrable.congr hscaled (Filter.Eventually.of_forall fun θ => ?_)
    exact mul_eq_mul_inv (ne_of_gt hzpos)
  · -- 7. `(∂_zu)²`
    have hscaled := hD2.mul_const ((z ^ 2)⁻¹)
    refine Integrable.congr hscaled (Filter.Eventually.of_forall fun θ => ?_)
    exact sq_eq_sq_mul_inv_sq (ne_of_gt hzpos)
  · -- 8. `(∂_z²u)²`
    have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hzpos)
    have hscaled := hA2.mul_const (((z ^ 2) ^ 2)⁻¹)
    refine Integrable.congr hscaled (Filter.Eventually.of_forall fun θ => ?_)
    exact sq_eq_sq_mul_inv_sq hz2

end

end Work.FTS.EllipticEst.Prop.CutEnergyAux
