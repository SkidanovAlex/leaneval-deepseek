/-
# The angular-transport coercivity in the *open* class `SmoothOpen`

`Work.FTS.CoercivityFix.Coer1.wip_transport_le_Q` proves

  `wip (Rho β) (Transport u) u ≤ 3|β - 1| · wip (Rho β) u u`

for `u` in the interior class `Work.FTS.LocData.SmoothQuad` (`C^∞` on the *strip*
`z > -1, 0 < θ < π/2`).  The route's data only carries the *open* class
`Work.FTS.EllipticEst.SmoothOpen` (`C^∞` on the open quadrant `z > 0, 0 < θ < π/2`), so the
estimate has to be re-run on that class.  This file is the verbatim adaptation: the only
mathematical input that changes class is the one-dimensional angular integration by parts,
which is available as `slice_ibp_gen_O` (the `SmoothOpen` twin of `slice_ibp_gen_Q`).

The proof is the one-dimensional integration by parts at fixed `z > 0` (the boundary term
`sin(2θ)^{1-β} u²` vanishing at `0⁺` and `(π/2)⁻`, which is precisely what the two vanishing
hypotheses `hvan0`, `hvan2` supply), Fubini, and the pointwise bound
`|cos(2θ)/(1+z)| ≤ 1` that converts the `z`-weight `w²/(1+z)` of the transport pairing into
the `z`-weight `w²` of the energy.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass
import Submission.Work.FTS.CoercivityFix.Coer1.thetaIBP
import Submission.Work.FTS.StrongEps.EpsE4Thr.slice_ibp_gen_O
import Submission.Work.FTS.CoercivityFix.Coer1.Defs
import Submission.Work.Coercivity.wip_eq_integral_prod

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem wip_transport_le_O (β : ℝ) (u : Work.FTS.Galerkin.Fn)
    (hu : Work.FTS.EllipticEst.SmoothOpen u)
    (hvan0 : ∀ z, 0 < z → Filter.Tendsto (fun θ => (Real.sin (2 * θ)) ^ (1 - β) * (u z θ) ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hvan2 : ∀ z, 0 < z → Filter.Tendsto (fun θ => (Real.sin (2 * θ)) ^ (1 - β) * (u z θ) ^ 2)
      (nhdsWithin (π / 2) (Set.Iio (π / 2))) (nhds 0))
    (hint : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-β) * Work.Spaces.Dth u z θ * u z θ
        / (1 + z))) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hint2 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho β) (Work.Coercivity.Transport u) u
      ≤ (3 * |β - 1|) * Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho β) u u := by
  -- the two integrands on the product space
  let Gp : ℝ × ℝ → ℝ := fun p =>
    Work.Spaces.w p.1 ^ 2 * (Real.sin (2 * p.2)) ^ (-β) * Work.Spaces.Dth u p.1 p.2 * u p.1 p.2
      / (1 + p.1)
  let Bp : ℝ × ℝ → ℝ := fun p =>
    Work.Spaces.w p.1 ^ 2 * (Real.sin (2 * p.2)) ^ (-β) * (u p.1 p.2) ^ 2
  have hvol : (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      = (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
          (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
  have hGp : MeasureTheory.Integrable Gp
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [hvol]; exact hint
  have hBp : MeasureTheory.Integrable Bp
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [hvol]; exact hint2
  have hGslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ => Gp (z, θ)) (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    hGp.prod_right_ae
  have hBslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ => Bp (z, θ)) (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    hBp.prod_right_ae
  have hzpos : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z := by
    rw [MeasureTheory.ae_restrict_iff (p := fun z => 0 < z) measurableSet_Ioi,
      MeasureTheory.ae_iff]
    have hset : {z : ℝ | ¬ (z ∈ Work.Spaces.Iz → 0 < z)} = {0} := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Work.Spaces.Iz, Set.mem_Ici, not_imp]
      constructor
      · rintro ⟨h1, h2⟩; exact le_antisymm (not_lt.mp h2) h1
      · rintro rfl; exact ⟨le_refl 0, lt_irrefl 0⟩
    rw [hset, Real.volume_singleton]
  -- the slice-wise inequality: `∫_θ Gp ≤ |β-1| ∫_θ Bp`
  have hkey : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (∫ θ, Gp (z, θ) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        ≤ |β - 1| * (∫ θ, Bp (z, θ) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    filter_upwards [hGslice, hBslice, hzpos] with z hGz hBz hzp
    have hwne : Work.Spaces.w z ^ 2 ≠ 0 := by
      have : 0 < Work.Spaces.w z := by rw [Work.Spaces.w]; positivity
      positivity
    -- the core integrabilities, obtained from the two product integrabilities
    have hBcore : MeasureTheory.Integrable
        (fun θ => (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      have hBz' : MeasureTheory.Integrable
          (fun θ => Work.Spaces.w z ^ 2 * ((Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2))
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
        refine hBz.congr (Filter.Eventually.of_forall (fun θ => ?_))
        dsimp only [Bp]; ring
      have h2 := hBz'.const_mul ((Work.Spaces.w z ^ 2))⁻¹
      refine h2.congr (Filter.Eventually.of_forall (fun θ => ?_))
      show (Work.Spaces.w z ^ 2)⁻¹ *
          (Work.Spaces.w z ^ 2 * ((Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2))
        = (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2
      rw [inv_mul_cancel_left₀ hwne]
    have hKcore : MeasureTheory.Integrable
        (fun θ => Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      Work.FTS.CoercivityFix.Coer1.cos_sin_integrable_Q β u hzp hBz
    have hIcore : MeasureTheory.Integrable
        (fun θ => (Real.sin (2 * θ)) ^ (-β) * Work.Spaces.Dth u z θ * u z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      refine (hGz.const_mul ((1 + z) / (Work.Spaces.w z) ^ 2)).congr
        (Filter.Eventually.of_forall (fun θ => ?_))
      dsimp only [Gp]
      have hw : Work.Spaces.w z ≠ 0 := by
        rw [Work.Spaces.w]; exact div_ne_zero (by positivity) (by positivity)
      have h1z : (1 : ℝ) + z ≠ 0 := by positivity
      field_simp
    -- the one-dimensional integration by parts
    have hslice := slice_ibp_gen_O β u hu hvan0 hvan2 z hzp hIcore hKcore
    -- the `θ`-independent factor `w z ^ 2/(1+z)` out of the slice integrals
    have h1 : (∫ θ, Gp (z, θ) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        = ((Work.Spaces.w z) ^ 2 / (1 + z)) *
            (∫ θ, (Real.sin (2 * θ)) ^ (-β) * Work.Spaces.Dth u z θ * u z θ
              ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
      rw [show (∫ θ, Gp (z, θ) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
          = ∫ θ, ((Work.Spaces.w z) ^ 2 / (1 + z)) *
              ((Real.sin (2 * θ)) ^ (-β) * Work.Spaces.Dth u z θ * u z θ)
              ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) from
        MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall (fun θ => by dsimp only [Gp]; ring))]
      rw [MeasureTheory.integral_const_mul]
    have hGval : (∫ θ, Gp (z, θ) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        = (β - 1) * (∫ θ, ((Work.Spaces.w z) ^ 2 / (1 + z)) *
            (Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2)
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
      rw [h1, hslice]
      rw [show ((Work.Spaces.w z) ^ 2 / (1 + z)) *
            ((β - 1) * (∫ θ, Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2
              ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)))
          = (β - 1) * (((Work.Spaces.w z) ^ 2 / (1 + z)) *
              (∫ θ, Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2
                ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))) from by ring]
      rw [MeasureTheory.integral_const_mul]
    -- the three integral comparisons
    have hc1 : (∫ θ, ((Work.Spaces.w z) ^ 2 / (1 + z)) *
            (Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2)
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        ≤ (∫ θ, Bp (z, θ) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
      have hintL : MeasureTheory.Integrable (fun θ => ((Work.Spaces.w z) ^ 2 / (1 + z)) *
          (Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2))
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
        (hKcore.const_mul ((Work.Spaces.w z) ^ 2 / (1 + z))).congr
          (Filter.Eventually.of_forall (fun θ => by ring_nf))
      refine MeasureTheory.integral_mono_ae hintL hBz ?_
      filter_upwards [MeasureTheory.ae_restrict_mem
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ hθ
      have hsin : 0 ≤ Real.sin (2 * θ) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
          (by linarith [hθ.2, Real.pi_pos])
      have hA : 0 ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2 :=
        mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin _)) (sq_nonneg _)
      have hcoef : Real.cos (2 * θ) / (1 + z) ≤ 1 := by
        have h1z : 0 < 1 + z := by linarith [hzp]
        rw [div_le_iff₀ h1z]
        linarith [Real.cos_le_one (2 * θ)]
      dsimp only [Bp]
      calc ((Work.Spaces.w z) ^ 2 / (1 + z)) *
              (Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2)
          = (Real.cos (2 * θ) / (1 + z)) *
              ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2) := by
            ring
        _ ≤ 1 * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2) :=
            mul_le_mul_of_nonneg_right hcoef hA
        _ = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2 := one_mul _
    have hc2 : (∫ θ, ((Work.Spaces.w z) ^ 2 / (1 + z)) *
            ((Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2)
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        ≤ (∫ θ, Bp (z, θ) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
      have hintL : MeasureTheory.Integrable (fun θ => ((Work.Spaces.w z) ^ 2 / (1 + z)) *
          ((Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2))
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
        (hBcore.const_mul ((Work.Spaces.w z) ^ 2 / (1 + z))).congr
          (Filter.Eventually.of_forall (fun θ => by ring))
      refine MeasureTheory.integral_mono_ae hintL hBz ?_
      filter_upwards [MeasureTheory.ae_restrict_mem
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ hθ
      have hsin : 0 ≤ Real.sin (2 * θ) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
          (by linarith [hθ.2, Real.pi_pos])
      have hX : 0 ≤ (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2 :=
        mul_nonneg (Real.rpow_nonneg hsin _) (sq_nonneg _)
      have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
      have hcoef : (Work.Spaces.w z) ^ 2 / (1 + z) ≤ (Work.Spaces.w z) ^ 2 := by
        have h1z : 0 < 1 + z := by linarith [hzp]
        rw [div_le_iff₀ h1z]; nlinarith [hzp, hw2]
      dsimp only [Bp]
      calc ((Work.Spaces.w z) ^ 2 / (1 + z)) * ((Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2)
          ≤ (Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2) :=
            mul_le_mul_of_nonneg_right hcoef hX
        _ = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2 := by ring
    have hc3 : -((∫ θ, ((Work.Spaces.w z) ^ 2 / (1 + z)) *
            ((Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2)
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)))
        ≤ (∫ θ, ((Work.Spaces.w z) ^ 2 / (1 + z)) *
            (Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2)
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
      have hneg : (∫ θ, -(((Work.Spaces.w z) ^ 2 / (1 + z)) *
            ((Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2))
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
          = -((∫ θ, ((Work.Spaces.w z) ^ 2 / (1 + z)) *
            ((Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2)
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))) := by
        simpa using MeasureTheory.integral_neg
          (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
          (f := fun θ => ((Work.Spaces.w z) ^ 2 / (1 + z)) *
            ((Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2))
      rw [← hneg]
      have hintL : MeasureTheory.Integrable (fun θ => -(((Work.Spaces.w z) ^ 2 / (1 + z)) *
          ((Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2)))
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
        ((hBcore.const_mul ((Work.Spaces.w z) ^ 2 / (1 + z))).neg).congr
          (Filter.Eventually.of_forall (fun θ => by simp only [Pi.neg_apply]))
      have hintR : MeasureTheory.Integrable (fun θ => ((Work.Spaces.w z) ^ 2 / (1 + z)) *
          (Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2))
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
        (hKcore.const_mul ((Work.Spaces.w z) ^ 2 / (1 + z))).congr
          (Filter.Eventually.of_forall (fun θ => by ring_nf))
      refine MeasureTheory.integral_mono_ae hintL hintR ?_
      filter_upwards [MeasureTheory.ae_restrict_mem
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ hθ
      have hsin : 0 ≤ Real.sin (2 * θ) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
          (by linarith [hθ.2, Real.pi_pos])
      have hc : 0 ≤ (Work.Spaces.w z) ^ 2 / (1 + z) :=
        div_nonneg (sq_nonneg _) (by linarith [hzp])
      have hX : 0 ≤ (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2 :=
        mul_nonneg (Real.rpow_nonneg hsin _) (sq_nonneg _)
      have hcos : -1 ≤ Real.cos (2 * θ) := Real.neg_one_le_cos (2 * θ)
      calc -(((Work.Spaces.w z) ^ 2 / (1 + z)) * ((Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2))
          = (Work.Spaces.w z) ^ 2 / (1 + z) *
              (-((Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2)) := by ring
        _ ≤ (Work.Spaces.w z) ^ 2 / (1 + z) *
              (Real.cos (2 * θ) * ((Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2)) := by
            refine mul_le_mul_of_nonneg_left ?_ hc
            have h1 : 0 ≤ (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2
                * (1 + Real.cos (2 * θ)) := mul_nonneg hX (by linarith)
            nlinarith [h1]
        _ = (Work.Spaces.w z) ^ 2 / (1 + z) *
              (Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2) := by ring
    -- combine, by cases on `β ≥ 1`
    rcases le_total (1 : ℝ) β with hb | hb
    · have hb1 : 0 ≤ β - 1 := by linarith
      have habs : |β - 1| = β - 1 := abs_of_nonneg hb1
      rw [hGval, habs]
      exact mul_le_mul_of_nonneg_left hc1 hb1
    · have hb1 : β - 1 ≤ 0 := by linarith
      have habs : |β - 1| = -(β - 1) := abs_of_nonpos hb1
      rw [hGval, habs]
      have hstep : (β - 1) * (∫ θ, ((Work.Spaces.w z) ^ 2 / (1 + z)) *
            (Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2)
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
          ≤ (β - 1) * (-(∫ θ, ((Work.Spaces.w z) ^ 2 / (1 + z)) *
            ((Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2)
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))) :=
        mul_le_mul_of_nonpos_left hc3 hb1
      have hstep2 : (β - 1) * (-(∫ θ, ((Work.Spaces.w z) ^ 2 / (1 + z)) *
            ((Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2)
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)))
          ≤ (-(β - 1)) * (∫ θ, Bp (z, θ) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
        nlinarith [hc2, hb1]
      linarith [hstep, hstep2]
  -- integrate over `z`
  have hFz : MeasureTheory.Integrable
      (fun z => ∫ θ, Gp (z, θ) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hGp.integral_prod_left
  have hBzI : MeasureTheory.Integrable
      (fun z => ∫ θ, Bp (z, θ) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hBp.integral_prod_left
  have hmono : (∫ z, (∫ θ, Gp (z, θ) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
      ≤ (∫ z, |β - 1| *
          (∫ θ, Bp (z, θ) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)) :=
    MeasureTheory.integral_mono_ae hFz (hBzI.const_mul _) hkey
  have hmono2 : (∫ z, |β - 1| *
          (∫ θ, Bp (z, θ) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
      = |β - 1| *
          (∫ z, (∫ θ, Bp (z, θ) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)) :=
    MeasureTheory.integral_const_mul _ _
  have hAG : (∫ p, Gp p
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      = (∫ z, (∫ θ, Gp (z, θ) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)) :=
    MeasureTheory.integral_prod Gp hGp
  have hAB : (∫ p, Bp p
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      = (∫ z, (∫ θ, Bp (z, θ) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)) :=
    MeasureTheory.integral_prod Bp hBp
  have hAGle : (∫ p, Gp p
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      ≤ |β - 1| * (∫ p, Bp p
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))) := by
    rw [hAG, hAB]
    linarith [hmono, hmono2]
  -- identify the two `wip`s with the product integrals
  have h2' : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ * u z θ *
        (Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-β)))) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine hint2.congr (Filter.Eventually.of_forall (fun p => by
      dsimp only [Function.uncurry]; ring))
  have hIntB : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ * u z θ * Work.FTS.CoercivityFix.Coer1.Rho β z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine h2'.congr (Filter.Eventually.of_forall (fun p => ?_))
    dsimp only [Function.uncurry, Work.FTS.CoercivityFix.Coer1.Rho,
      Work.FTS.CoercivityFix.Coer1.sig]
  have hwipB : Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho β) u u
      = (∫ p, Bp p
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))) := by
    rw [Work.Coercivity.wip_eq_integral_prod (Work.FTS.CoercivityFix.Coer1.Rho β) u u hIntB]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
    dsimp only [Bp, Work.FTS.CoercivityFix.Coer1.Rho, Work.FTS.CoercivityFix.Coer1.sig]
    ring
  have hA' : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Coercivity.Transport u z θ * u z θ
        * Work.FTS.CoercivityFix.Coer1.Rho β z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine (hint.const_mul 3).congr (Filter.Eventually.of_forall (fun p => ?_))
    dsimp only [Function.uncurry, Work.Coercivity.Transport, Work.FTS.CoercivityFix.Coer1.Rho,
      Work.FTS.CoercivityFix.Coer1.sig]
    ring
  have hwipA : Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho β)
        (Work.Coercivity.Transport u) u
      = 3 * (∫ p, Gp p
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))) := by
    rw [Work.Coercivity.wip_eq_integral_prod (Work.FTS.CoercivityFix.Coer1.Rho β)
      (Work.Coercivity.Transport u) u hA']
    rw [show (∫ p, Work.Coercivity.Transport u p.1 p.2 * u p.1 p.2
            * Work.FTS.CoercivityFix.Coer1.Rho β p.1 p.2
            ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
              (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
        = ∫ p, 3 * Gp p
            ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
              (MeasureTheory.volume.restrict Work.Spaces.Iθ)) from
      MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall (fun p => by
          dsimp only [Gp, Work.Coercivity.Transport, Work.FTS.CoercivityFix.Coer1.Rho,
            Work.FTS.CoercivityFix.Coer1.sig]
          ring))]
    rw [MeasureTheory.integral_const_mul]
  rw [hwipB, hwipA]
  linarith [hAGle]

end Work.FTS.StrongEps.EpsE4Thr
