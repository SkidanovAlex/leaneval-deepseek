/-
Copyright: work module for the Elgindi finite-time singularity project.

# `L₁₂(P₀ J_ε δ)(0) = 0` — the projection `P₀` kills the zero mode of the mollified datum

The design's projection `P₀ = Pz` is *defined* by
`Pz f = f − (L₁₂ f 0 / pzNorm) • bump` precisely so that `L₁₂(Pz f)(0) = 0`.  This module
proves that identity at the profile `f = J_ε δ` under the interface hypotheses of the
`ε`-scheme (`IsSmoothKernel ρ`, `α, ε ∈ (0,1]`, `δ` smooth on the open quadrant and level-`0`
`ε`-membership `EpsMem α δ`).

## Why this is not merely `Pz_l12`

`PZeroAux.Pz_l12` proves `L₁₂(Pz f)(0) = 0` under the two *integrability* hypotheses "the
`θ`-slice of the density is integrable for a.e. `s`" and "the density itself is integrable".
Neither is available here: `EpsMem α (J_ε δ)` (what the `ε`-scheme's interface supplies, via
`EpsSqIter_mixed_Jeps_le6`) is an `L²`-condition, and it does not by itself give
`L¹`-integrability of the density.  The route below avoids both hypotheses by exploiting the
fact that Mathlib's Bochner integral is the junk value `0` off the integrable functions
(`MeasureTheory.integral_undef`):

* the a.e.-in-`s` integrability of the angular slice of `J_ε δ` is obtained from the `L²`
  finiteness supplied by `EpsMem` through the elementary AM–GM bound
  `|K θ h θ/s| ≤ (3/(2s))((h θ · epsW)² + (1/w s)²)` (at the two endpoints `θ = 0, π/2` the
  weight `epsW` degenerates, but both are null);
* with that, the density of the projected profile is a.e. the difference of the densities of
  `J_ε δ` and of the correction, so on the *outer* integral: if the former density is not
  integrable on `(0,∞)`, `L₁₂(…)(0) = 0` outright by `MeasureTheory.integral_undef`;
  otherwise the density of `J_ε δ` is integrable too (it differs from the former by the
  integrable density of `bump`), and the two integrals cancel against the normalisation
  `pzNorm`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongEps.PZeroAux.Pz_l12
import Submission.Work.FTS.StrongEps.EpsSqTools.EpsSqIter_mixed_Jeps_le6
import Submission.Work.FTS.StrongEps.JepsHkMem.AuxMeas

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsSqTools.LinAux

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The `ε`-membership as a product-measure integrability -/

/-- The product of the two restricted measures is the restriction of the planar Lebesgue measure
to the closed quadrant `Iz ×ˢ Iθ`. -/
theorem quadrant_restrict_prod :
    (volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      = (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) := by
  rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod ℝ ℝ]

/-- `EpsMem` reformulated as `Integrable` for the product of the two restricted measures. -/
theorem EpsMem_integrable {α : ℝ} {f : ℝ → ℝ → ℝ} (h : Work.FTS.StrongEps.EpsMem α f) :
    MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (f p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
  rw [Work.FTS.StrongEps.EpsMem, MeasureTheory.IntegrableOn, quadrant_restrict_prod] at h
  exact h

/-- **The angular slice of the `ε`-weighted square is integrable for a.e. radial variable.**
This is Tonelli (`Integrable.prod_right_ae`) applied to `EpsMem`. -/
theorem ae_integrable_slice_epsW_sq {α : ℝ} {f : ℝ → ℝ → ℝ}
    (h : Work.FTS.StrongEps.EpsMem α f) :
    ∀ᵐ z ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.Integrable
        (fun θ => (f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2)
        (volume.restrict Work.Spaces.Iθ) := by
  rw [← Work.FTS.StrongEps.JepsHkMem.restrict_Iz_eq]
  exact (EpsMem_integrable h).prod_right_ae

/-! ## The AM–GM bound of the `L₁₂`-density integrand -/

/-- The weight `w` is positive on the open half-line. -/
theorem w_pos_of_pos {z : ℝ} (hz : 0 < z) : 0 < Work.Spaces.w z := by
  rw [Work.Spaces.w]
  positivity

/-- **The pointwise AM–GM bound of the `L₁₂`-density integrand by the `ε`-weighted square.**
On the *open* angular interval (where `epsW` does not degenerate),

  `|K θ · g θ / s| ≤ (3/(2s)) · ((g θ · epsW α s θ)² + (1/w s)²)`. -/
theorem abs_K_mul_div_le {α s : ℝ} (hs : 0 < s) (hgam : 0 ≤ Work.Spaces.gam α / 2)
    {g : ℝ → ℝ} {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |Work.Spaces.K θ * g θ / s|
      ≤ (3 / (2 * s)) * ((g θ * Work.FTS.StrongEps.epsW α s θ) ^ 2 + (1 / Work.Spaces.w s) ^ 2) := by
  have hIθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hw : 0 < Work.Spaces.w s := w_pos_of_pos hs
  have hSpow : 0 < Real.sin (2 * θ) ^ (Work.Spaces.gam α / 2) := Real.rpow_pos_of_pos hsin _
  have hK3 : |Work.Spaces.K θ| ≤ 3 := by
    rw [abs_of_nonneg (Work.FTS.GalBasis.cc.K_nonneg_of_mem_Iθ hIθ)]
    exact Work.FTS.GalBasis.cc.K_le_three_of_mem_Iθ hIθ
  -- `|g θ|` expressed through the `ε`-weighted square
  have hident : |g θ * Work.FTS.StrongEps.epsW α s θ|
      * (Real.sin (2 * θ) ^ (Work.Spaces.gam α / 2) / Work.Spaces.w s) = |g θ| := by
    have heps : Work.FTS.StrongEps.epsW α s θ
        = Work.Spaces.w s / Real.sin (2 * θ) ^ (Work.Spaces.gam α / 2) := rfl
    rw [heps, abs_mul, abs_of_pos (div_pos hw hSpow)]
    field_simp
  have hbound : |g θ| ≤ ((g θ * Work.FTS.StrongEps.epsW α s θ) ^ 2
      + (1 / Work.Spaces.w s) ^ 2) / 2 := by
    have hwnn : 0 ≤ Real.sin (2 * θ) ^ (Work.Spaces.gam α / 2) / Work.Spaces.w s :=
      div_nonneg (Real.rpow_nonneg hsin.le _) hw.le
    have hamgm : |g θ * Work.FTS.StrongEps.epsW α s θ|
        * (Real.sin (2 * θ) ^ (Work.Spaces.gam α / 2) / Work.Spaces.w s)
        ≤ ((g θ * Work.FTS.StrongEps.epsW α s θ) ^ 2
            + (Real.sin (2 * θ) ^ (Work.Spaces.gam α / 2) / Work.Spaces.w s) ^ 2) / 2 := by
      nlinarith [sq_nonneg (|g θ * Work.FTS.StrongEps.epsW α s θ|
          - Real.sin (2 * θ) ^ (Work.Spaces.gam α / 2) / Work.Spaces.w s),
        sq_abs (g θ * Work.FTS.StrongEps.epsW α s θ)]
    have hsincmp : Real.sin (2 * θ) ^ (Work.Spaces.gam α / 2) / Work.Spaces.w s
        ≤ 1 / Work.Spaces.w s :=
      div_le_div_of_nonneg_right (Real.rpow_le_one hsin.le (Real.sin_le_one _) hgam) hw.le
    have hsinsq : (Real.sin (2 * θ) ^ (Work.Spaces.gam α / 2) / Work.Spaces.w s) ^ 2
        ≤ (1 / Work.Spaces.w s) ^ 2 := by
      have h := mul_self_le_mul_self hwnn hsincmp
      simpa [pow_two] using h
    rw [hident] at hamgm
    linarith [hamgm, hsinsq]
  have hstep1 : |Work.Spaces.K θ * g θ / s| = |Work.Spaces.K θ| * |g θ| / s := by
    rw [abs_div, abs_mul, abs_of_pos hs]
  have hstep2 : |Work.Spaces.K θ| * |g θ| / s ≤ 3 * |g θ| / s := by
    rw [div_le_div_iff_of_pos_right hs]
    exact mul_le_mul_of_nonneg_right hK3 (abs_nonneg _)
  have hstep3 : 3 * |g θ| / s
      ≤ 3 * (((g θ * Work.FTS.StrongEps.epsW α s θ) ^ 2
          + (1 / Work.Spaces.w s) ^ 2) / 2) / s := by
    rw [div_le_div_iff_of_pos_right hs]
    exact mul_le_mul_of_nonneg_left hbound (by norm_num)
  rw [hstep1]
  refine le_trans hstep2 (le_trans hstep3 ?_)
  exact le_of_eq (by ring)

/-- The constant majorant `(3/(2s))(1/w s)²` is integrable on the angular interval. -/
theorem integrableOn_const_majorant (s : ℝ) :
    MeasureTheory.IntegrableOn
      (fun _ : ℝ => (3 / (2 * s)) * (1 / Work.Spaces.w s) ^ 2) Work.Spaces.Iθ := by
  have h1 : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ := by
    refine MeasureTheory.integrableOn_const (C := (1 : ℝ)) ?_ ?_
    · rw [Work.Spaces.Iθ, Real.volume_Icc]
      simp
    · simp
  have h2 : MeasureTheory.Integrable
      (fun _ : ℝ => (3 / (2 * s)) * (1 / Work.Spaces.w s) ^ 2 * 1)
      (volume.restrict Work.Spaces.Iθ) := h1.const_mul _
  exact h2.congr (Filter.Eventually.of_forall fun _ => by ring)

/-- **The `L₁₂`-density integrand is integrable as soon as the `ε`-weighted square is.** -/
theorem integrableOn_K_mul_div_of_integrable_epsW_sq {α s : ℝ} (hs : 0 < s)
    (hgam : 0 ≤ Work.Spaces.gam α / 2) {g : ℝ → ℝ}
    (hg : MeasureTheory.Integrable
      (fun θ => (g θ * Work.FTS.StrongEps.epsW α s θ) ^ 2)
      (volume.restrict Work.Spaces.Iθ))
    (haesm : AEStronglyMeasurable (fun θ => Work.Spaces.K θ * g θ / s)
      (volume.restrict Work.Spaces.Iθ)) :
    MeasureTheory.Integrable (fun θ => Work.Spaces.K θ * g θ / s)
      (volume.restrict Work.Spaces.Iθ) := by
  have hmaj : MeasureTheory.Integrable
      (fun θ => (3 / (2 * s)) * ((g θ * Work.FTS.StrongEps.epsW α s θ) ^ 2
        + (1 / Work.Spaces.w s) ^ 2)) (volume.restrict Work.Spaces.Iθ) := by
    have h1 : MeasureTheory.Integrable
        (fun θ => (3 / (2 * s)) * (g θ * Work.FTS.StrongEps.epsW α s θ) ^ 2)
        (volume.restrict Work.Spaces.Iθ) := hg.const_mul _
    have h2 : MeasureTheory.Integrable
        (fun θ => (3 / (2 * s)) * (1 / Work.Spaces.w s) ^ 2)
        (volume.restrict Work.Spaces.Iθ) := integrableOn_const_majorant s
    have hsum : MeasureTheory.Integrable
        ((fun θ : ℝ => (3 / (2 * s)) * (g θ * Work.FTS.StrongEps.epsW α s θ) ^ 2)
          + fun θ : ℝ => (3 / (2 * s)) * (1 / Work.Spaces.w s) ^ 2)
        (volume.restrict Work.Spaces.Iθ) := h1.add h2
    have heq : ((fun θ : ℝ => (3 / (2 * s)) * (g θ * Work.FTS.StrongEps.epsW α s θ) ^ 2)
          + fun θ : ℝ => (3 / (2 * s)) * (1 / Work.Spaces.w s) ^ 2)
        = fun θ : ℝ => (3 / (2 * s)) * ((g θ * Work.FTS.StrongEps.epsW α s θ) ^ 2
            + (1 / Work.Spaces.w s) ^ 2) := by
      funext θ
      simp only [Pi.add_apply]
      ring
    rwa [heq] at hsum
  refine hmaj.mono' haesm ?_
  have hIoo : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo 0 (π / 2) := by
    rw [Work.FTS.StrongEps.JepsHkMem.restrict_Iθ_eq]
    exact MeasureTheory.self_mem_ae_restrict measurableSet_Ioo
  filter_upwards [hIoo] with θ hθ
  simpa only [Real.norm_eq_abs] using abs_K_mul_div_le (α := α) hs hgam hθ

/-! ## Almost-everywhere integrability of the angular slice of `J_ε δ` -/

/-- The slices of `J_ε f` at `z > 0` are a.e. strongly measurable. -/
theorem ae_aesm_slice_Jeps {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {δ : ℝ → ℝ → ℝ}
    (hδ : ContinuousOn (Function.uncurry δ) Work.FTS.StrongEps.Quad) :
    ∀ᵐ z ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      AEStronglyMeasurable (fun θ => Work.FTS.StrongEps.Jeps ρ ε δ z θ)
        (volume.restrict Work.Spaces.Iθ) := by
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z hz
  exact Work.FTS.StrongEps.JepsHkMem.aestronglyMeasurable_Jeps_slice hρ hε hδ hz

/-! ## The theorem -/

theorem L12_Pz_Jeps_zero (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {α ε : ℝ} (hα : α ∈ Set.Ioc 0 1) (hε : ε ∈ Set.Ioc 0 1) {δ : ℝ → ℝ → ℝ}
    (hδ : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry δ) Work.FTS.EllipticEst.Q0)
    (hδmem : Work.FTS.StrongEps.EpsMem α δ) :
    Work.Construction.L12 (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε δ)) 0 = 0 := by
  set J : ℝ → ℝ → ℝ := Work.FTS.StrongEps.Jeps ρ ε δ with hJ
  set B : ℝ → ℝ → ℝ := Work.FTS.StrongEps.bump with hB
  have hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry δ) Work.FTS.StrongEps.Quad :=
    fun n => hδ n
  have hδc : ContinuousOn (Function.uncurry δ) Work.FTS.StrongEps.Quad := (hδ 0).continuousOn
  have hgam : 0 ≤ Work.Spaces.gam α / 2 := by rw [Work.Spaces.gam]; linarith [hα.1]
  -- The normalising constant is non-zero
  have hpz : Work.FTS.StrongEps.pzNorm ≠ 0 :=
    ne_of_gt Work.FTS.StrongEps.PZeroAux.pzNorm_pos
  -- `EpsMem` of the mollified profile
  obtain ⟨C, _hCpos, hC⟩ := Work.FTS.StrongEps.EpsSqTools.EpsSqIter_mixed_Jeps_le6 ρ hρ
  have hEpsJ : Work.FTS.StrongEps.EpsMem α J :=
    (hC α hα ε hε.1 hε.2 δ hsm hδmem).1
  -- The angular slice of the density of `J` is integrable for a.e. radial variable
  have hJslice : ∀ᵐ s ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ * J s θ / s) Work.Spaces.Iθ := by
    have h1 := ae_integrable_slice_epsW_sq (α := α) hEpsJ
    have h2 := ae_aesm_slice_Jeps (ρ := ρ) hρ.moll hε.1 hδc
    have h3 : ∀ᵐ s ∂(volume.restrict (Set.Ioi (0 : ℝ))), 0 < s :=
      MeasureTheory.self_mem_ae_restrict measurableSet_Ioi
    have hKc : Continuous Work.Spaces.K := by
      show Continuous fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2
      fun_prop
    filter_upwards [h1, h2, h3] with s hs1 hs2 hs3
    have haesm : AEStronglyMeasurable (fun θ => Work.Spaces.K θ * J s θ / s)
        (volume.restrict Work.Spaces.Iθ) :=
      ((hKc.div_const s).aestronglyMeasurable.mul hs2).congr
        (Filter.Eventually.of_forall fun θ => by
          simp only [Pi.mul_apply, hJ]
          ring)
    exact integrableOn_K_mul_div_of_integrable_epsW_sq hs3 hgam hs1 haesm
  -- The projection, as a functional identity
  set c : ℝ := Work.Construction.L12 J 0 / Work.FTS.StrongEps.pzNorm with hc
  have hPz : Work.FTS.StrongEps.Pz J = fun z θ => J z θ + (-c) * B z θ := by
    funext z θ
    rw [Work.FTS.StrongEps.Pz_apply, hc, hJ, hB]
    ring
  -- The correction has integrable angular slices and integrable density
  have hBslice : ∀ s : ℝ, 0 < s →
      MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ * B s θ / s) Work.Spaces.Iθ := by
    intro s hs
    have h := Work.FTS.StrongEps.PZeroAux.integrableOn_slice_bump (s := s) hs
    exact h.congr_fun (fun θ _ => by rw [hB]) measurableSet_Icc
  have hBdens : MeasureTheory.IntegrableOn (fun s => Work.FM.L12dens Work.Spaces.K B s)
      (Set.Ioi 0) := by
    have h := Work.FTS.StrongEps.PZeroAux.integrableOn_L12dens_bump
    rw [← hB] at h
    exact h
  -- The density identity, a.e. in the radial variable
  have hden : ∀ᵐ s ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      Work.FM.L12dens Work.Spaces.K (fun z θ => J z θ + (-c) * B z θ) s
        = Work.FM.L12dens Work.Spaces.K J s + (-c) * Work.FM.L12dens Work.Spaces.K B s := by
    have h4 : ∀ᵐ s ∂(volume.restrict (Set.Ioi (0 : ℝ))), 0 < s :=
      MeasureTheory.self_mem_ae_restrict measurableSet_Ioi
    filter_upwards [hJslice, h4] with s hsJ hs
    have hBint : MeasureTheory.IntegrableOn
        (fun θ => Work.Spaces.K θ * ((-c) * B s θ) / s) Work.Spaces.Iθ := by
      have h := hBslice s hs
      have h2 : MeasureTheory.IntegrableOn
          (fun θ => (-c) * (Work.Spaces.K θ * B s θ / s)) Work.Spaces.Iθ :=
        MeasureTheory.Integrable.const_mul h (-c)
      exact MeasureTheory.IntegrableOn.congr_fun h2 (fun θ _ => by ring) measurableSet_Icc
    have hlin := Work.FTS.LocData.L12dens_add_of_integrableOn Work.Spaces.K
      (a := J) (b := fun z θ => (-c) * B z θ) (s := s) hsJ hBint
    have hscale := Work.FTS.LocData.L12dens_const_mul Work.Spaces.K (-c) B s
    rw [hlin, hscale]
  -- The values of the two densities
  have hBval : (∫ s in Set.Ioi (0 : ℝ), Work.FM.L12dens Work.Spaces.K B s)
      = Work.FTS.StrongEps.pzNorm := by
    rw [hB, Work.FTS.StrongEps.pzNorm, Work.Construction.L12, Work.FM.L12]
  have hJval : (∫ s in Set.Ioi (0 : ℝ), Work.FM.L12dens Work.Spaces.K J s)
      = c * Work.FTS.StrongEps.pzNorm := by
    rw [hc]
    have h : Work.Construction.L12 J 0
        = ∫ s in Set.Ioi (0 : ℝ), Work.FM.L12dens Work.Spaces.K J s := by
      rw [Work.Construction.L12, Work.FM.L12]
    rw [h, div_mul_cancel₀ (∫ s in Set.Ioi (0 : ℝ), Work.FM.L12dens Work.Spaces.K J s) hpz]
  -- The goal, unfolded
  rw [hPz, Work.Construction.L12, Work.FM.L12]
  by_cases hZint : MeasureTheory.IntegrableOn
      (fun s => Work.FM.L12dens Work.Spaces.K (fun z θ => J z θ + (-c) * B z θ) s)
      (Set.Ioi 0)
  · -- The density of the projected profile is integrable: the outer integral splits
    have hae : (fun s => Work.FM.L12dens Work.Spaces.K (fun z θ => J z θ + (-c) * B z θ) s)
        =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
        fun s => Work.FM.L12dens Work.Spaces.K J s
          - c * Work.FM.L12dens Work.Spaces.K B s := by
      filter_upwards [hden] with s hs
      rw [hs]; ring
    have hYc : MeasureTheory.IntegrableOn
        (fun s => c * Work.FM.L12dens Work.Spaces.K B s) (Set.Ioi 0) :=
      MeasureTheory.Integrable.const_mul hBdens c
    have hJmem : MeasureTheory.IntegrableOn (fun s => Work.FM.L12dens Work.Spaces.K J s)
        (Set.Ioi 0) := by
      have h1 : MeasureTheory.Integrable
          (fun s => Work.FM.L12dens Work.Spaces.K (fun z θ => J z θ + (-c) * B z θ) s
            + c * Work.FM.L12dens Work.Spaces.K B s) (volume.restrict (Set.Ioi (0 : ℝ))) :=
        MeasureTheory.Integrable.add hZint hYc
      refine h1.congr ?_
      filter_upwards [hae] with s hs
      rw [hs]; ring
    have hsplit : (∫ s in Set.Ioi (0 : ℝ),
          Work.FM.L12dens Work.Spaces.K (fun z θ => J z θ + (-c) * B z θ) s)
        = ∫ s in Set.Ioi (0 : ℝ),
            (Work.FM.L12dens Work.Spaces.K J s
              - c * Work.FM.L12dens Work.Spaces.K B s) := by
      refine MeasureTheory.setIntegral_congr_ae measurableSet_Ioi ?_
      filter_upwards [(MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mp hae] with s hs
      intro hs'
      exact hs hs'
    rw [hsplit]
    rw [MeasureTheory.integral_sub hJmem hYc]
    rw [MeasureTheory.integral_const_mul, hJval, hBval]
    ring
  · exact MeasureTheory.integral_undef hZint

end Work.FTS.StrongEps.EpsSqTools.LinAux
