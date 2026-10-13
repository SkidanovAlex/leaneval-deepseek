/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsSqTools/L12_zero_le_EpsSq.lean`

The zero mode of the angular-moment operator `L₁₂` is controlled by the level-`0` weighted
`L²`-size `EpsSq` of the `ε`-scheme (with an `α`-independent constant):

`|L₁₂(h)(0)| ≤ 3 √(EpsSq α h)` for every `α ∈ (0,1]` and every `h` with `EpsMem α h`.

This is the `X`-space (`EpsSpace.lean`) form of the paper's bound
`|L₁₂(F)(0)| ≤ C ‖((1+z)/z) F‖_{L²}`: the weight of `EpsSq` is
`(epsW α z θ)² = w(z)² sin(2θ)^{-γ}` with `w(z) = (1+z)²/z²`, `γ = 1 + α/10 ≥ 1`, and on the
open quadrant it dominates the weight `w(z) = ((1+z)/z)²` that appears in the Cauchy–Schwarz
bound of `Work.FTS.Nonlinear.Pieces.L12_zero_le_weak`.

## The route

* `L12_zero_le_weak` gives `|L₁₂(f)(0)| ≤ 3 √(∫_{r>0} (∫_θ f²) w(r))` from two hypotheses: the
  angular slices `θ ↦ f(r,θ)²` are integrable for a.e. `r > 0`, and the weighted angular energy
  `r ↦ (∫_θ f²) · w(r)` is integrable on `(0,∞)`.
* `Work.FTS.OpenPkg.l12zero_of_weight_bound` produces both from an *integrable majorant* `Φ` of
  the weighted angular energy plus its a.e. strong measurability.  We take `Φ r = ∫_θ (f·epsW)²`,
  so that `∫_{r>0} Φ = EpsSq α f` **by definition** (`EpsSq` is the iterated integral of the same
  integrand, and `Ioi 0` is a.e. `Iz = Ici 0`).
* Everything is then read off from the single `EpsMem`-hypothesis, i.e. the joint integrability of
  `(f·epsW)²` on `Iz ×ˢ Iθ` (identified with the product of the two restricted measures by
  `Measure.prod_restrict` + `Measure.volume_eq_prod`), together with the a.e. description of that
  product measure by the open quadrant `Quad` (`EpsSqTools.ae_mem_quad`, where `epsW ≥ 1`):
  * `hΦ`: `Φ` is the `θ`-marginal of the integrand (`Integrable.integral_prod_left`);
  * `hsl`/integrability of the weighted energy: the closed-quadrant-weighted integrable function
    `h²·w` is obtained from `(h·epsW)²` by multiplying with the **bounded** factor
    `q = (sin(2θ)^{γ/2})² / w(z) ≤ 1` (`Integrable.mul_bdd`), the two integrands agreeing a.e. on
    the quadrant; its slicewise and radial marginals give both hypotheses
    (`Integrable.prod_right_ae`, `Integrable.integral_prod_left`), the factor `w(r)` being a
    non-zero *constant* on a slice;
  * `hbd`: the pointwise domination `f²·w ≤ (f·epsW)²` on the open quadrant, integrated in `θ`;
  * `hmeas`: `AEStronglyMeasurable` of the weighted energy, from its integrability.

All constants are explicit: the bound holds with `C = 3`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.StrongEps.EpsSpace
import Submission.Work.FTS.OpenPkg.l12zero_field
import Submission.Work.FTS.Nonlinear.Pieces.L12_zero_le_weak
import Submission.Work.FTS.StrongEps.EpsSqTools.Basic
import Submission.Work.FTS.StrongEps.EpsSqTools.Measurable
import Submission.Work.FTS.StrongEps.EpsSqTools.EpsSq_mul_le_of_sup
import Submission.Work.Construction.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsSqTools

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Pointwise facts on the open quadrant

The weight `epsW α z θ = w z / sin(2θ)^{γ/2}` of the `ε`-scheme dominates both `1` and the
closed-quadrant weight `w z` on the open quadrant, where `w z ≥ 1` and `0 < sin(2θ) ≤ 1`. -/

theorem one_le_w_of_pos {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w, one_le_div (by positivity)]
  nlinarith

theorem w_ne_zero_of_pos {z : ℝ} (hz : 0 < z) : Work.Spaces.w z ≠ 0 := by
  rw [Work.Spaces.w]
  exact div_ne_zero (pow_ne_zero 2 (by linarith)) (pow_ne_zero 2 hz.ne')

theorem div_sq_eq_w (r : ℝ) : ((1 + r) / r) ^ 2 = Work.Spaces.w r := by
  rw [Work.Spaces.w, div_pow]

theorem sin_two_pos_of_mem {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem gam_half_pos {α : ℝ} (hα : 0 < α) : 0 < Work.Spaces.gam α / 2 := by
  rw [Work.Spaces.gam]; linarith

theorem one_le_epsW {α z θ : ℝ} (hα : 0 < α) (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 1 ≤ epsW α z θ := by
  have hs := sin_two_pos_of_mem hθ
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hspos : 0 < Real.sin (2 * θ) ^ (Work.Spaces.gam α / 2) := Real.rpow_pos_of_pos hs _
  have hsle : Real.sin (2 * θ) ^ (Work.Spaces.gam α / 2) ≤ 1 :=
    Real.rpow_le_one hs.le hs1 (gam_half_pos hα).le
  rw [epsW, one_le_div hspos]
  exact le_trans hsle (one_le_w_of_pos hz)

theorem epsW_ne_zero {α z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    epsW α z θ ≠ 0 := by
  have hs := sin_two_pos_of_mem hθ
  have hspos : 0 < Real.sin (2 * θ) ^ (Work.Spaces.gam α / 2) := Real.rpow_pos_of_pos hs _
  exact div_ne_zero (w_ne_zero_of_pos hz) hspos.ne'

theorem w_le_epsW_sq {α z θ : ℝ} (hα : 0 < α) (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) : Work.Spaces.w z ≤ (epsW α z θ) ^ 2 := by
  have h1 := one_le_epsW hα hz hθ
  have hs := sin_two_pos_of_mem hθ
  have hspos : 0 < Real.sin (2 * θ) ^ (Work.Spaces.gam α / 2) := Real.rpow_pos_of_pos hs _
  have hsle : Real.sin (2 * θ) ^ (Work.Spaces.gam α / 2) ≤ 1 :=
    Real.rpow_le_one hs.le (Real.sin_le_one _) (gam_half_pos hα).le
  have hw0 : 0 ≤ Work.Spaces.w z := le_trans zero_le_one (one_le_w_of_pos hz)
  have hwe : Work.Spaces.w z ≤ epsW α z θ := by
    rw [epsW, le_div_iff₀ hspos]
    calc Work.Spaces.w z * Real.sin (2 * θ) ^ (Work.Spaces.gam α / 2)
        ≤ Work.Spaces.w z * 1 := mul_le_mul_of_nonneg_left hsle hw0
      _ = Work.Spaces.w z := mul_one _
  calc Work.Spaces.w z ≤ epsW α z θ := hwe
    _ ≤ (epsW α z θ) ^ 2 := by nlinarith

theorem mul_w_le_sq_epsW {α z θ : ℝ} (hα : 0 < α) (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) (x : ℝ) :
    x ^ 2 * Work.Spaces.w z ≤ (x * epsW α z θ) ^ 2 := by
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_left (w_le_epsW_sq hα hz hθ) (sq_nonneg x)

/-- On the open quadrant the two weights are exchanged by the bounded factor `q`. -/
theorem epsW_sq_mul_inv {α z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) (x : ℝ) :
    (x * epsW α z θ) ^ 2
        * ((Real.sin (2 * θ) ^ (Work.Spaces.gam α / 2)) ^ 2 / Work.Spaces.w z)
      = x ^ 2 * Work.Spaces.w z := by
  have hs := sin_two_pos_of_mem hθ
  have hspos : 0 < Real.sin (2 * θ) ^ (Work.Spaces.gam α / 2) := Real.rpow_pos_of_pos hs _
  have hw : Work.Spaces.w z ≠ 0 := w_ne_zero_of_pos hz
  rw [epsW]
  field_simp

/-- The angular interval is a.e. the open interval. -/
theorem theta_restrict_Ioo :
    MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) := by
  rw [Work.Spaces.Iθ]
  exact MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume)).symm

/-! ## The zero-mode bound of `L₁₂` in the `ε`-space -/

/- **The `L₁₂(0)` bound in the weighted space `X` of the `ε`-scheme.**  There is an
`α`-independent constant `C` (namely `3`) with
`|L₁₂(h)(0)| ≤ C √(EpsSq α h)` for every `α ∈ (0,1]` and every `h : Fn` with honest weighted
`L²`-membership `EpsMem α h`. -/
theorem L12_zero_le_EpsSq : ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 →
    ∀ h : Work.FTS.Galerkin.Fn, Work.FTS.StrongEps.EpsMem α h →
      |Work.Construction.L12 h 0| ≤ C * Real.sqrt (Work.FTS.StrongEps.EpsSq α h) := by
  refine ⟨3, by norm_num, ?_⟩
  intro α hαI h hf
  have hα : 0 < α := hαI.1
  -- the product measure on `Iz ×ˢ Iθ` is the product of the two restricted measures
  have hM : (MeasureTheory.volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      = (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ, ← MeasureTheory.Measure.prod_restrict]
  have hQuad : (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      = (MeasureTheory.volume : Measure (ℝ × ℝ)).restrict Work.FTS.StrongEps.Quad :=
    hM.symm.trans restrict_prod_eq_restrict_quad
  -- the `epsSq`-weighted square is integrable on the product
  have hG : Integrable (fun p : ℝ × ℝ => (h p.1 p.2 * epsW α p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [← hM]
    exact hf
  -- the auxiliary factor relating the two weights
  set q : ℝ × ℝ → ℝ :=
    fun p => (Real.sin (2 * p.2) ^ (Work.Spaces.gam α / 2)) ^ 2 / Work.Spaces.w p.1 with hq
  have hq_meas : Measurable q := by
    rw [hq]
    unfold Work.Spaces.w
    fun_prop
  have hq_aesm : AEStronglyMeasurable q
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := hq_meas.aestronglyMeasurable
  have hq_bdd : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)), ‖q p‖ ≤ 1 := by
    rw [hQuad]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_quad (fun p hp => ?_)
    obtain ⟨hz, hθ⟩ := Work.FTS.StrongEps.mem_Quad.mp hp
    have hs := sin_two_pos_of_mem hθ
    have hs1 : Real.sin (2 * p.2) ≤ 1 := Real.sin_le_one _
    have hspos : 0 < Real.sin (2 * p.2) ^ (Work.Spaces.gam α / 2) := Real.rpow_pos_of_pos hs _
    have hsle : Real.sin (2 * p.2) ^ (Work.Spaces.gam α / 2) ≤ 1 :=
      Real.rpow_le_one hs.le hs1 (gam_half_pos hα).le
    have hs2 : (Real.sin (2 * p.2) ^ (Work.Spaces.gam α / 2)) ^ 2 ≤ 1 := by
      nlinarith [hspos.le, hsle]
    have hw1 : 1 ≤ Work.Spaces.w p.1 := one_le_w_of_pos hz
    have hq0 : 0 ≤ (Real.sin (2 * p.2) ^ (Work.Spaces.gam α / 2)) ^ 2 / Work.Spaces.w p.1 :=
      div_nonneg (sq_nonneg _) (le_trans zero_le_one hw1)
    have hq1 : (Real.sin (2 * p.2) ^ (Work.Spaces.gam α / 2)) ^ 2 / Work.Spaces.w p.1 ≤ 1 := by
      rw [div_le_one (lt_of_lt_of_le zero_lt_one hw1)]
      exact le_trans hs2 hw1
    rw [hq, Real.norm_of_nonneg hq0]
    exact hq1
  -- integrability of the closed-quadrant weight times `h²`
  have hΞ : Integrable (fun p : ℝ × ℝ => (h p.1 p.2) ^ 2 * Work.Spaces.w p.1)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    have h1 : Integrable (fun p : ℝ × ℝ => (h p.1 p.2 * epsW α p.1 p.2) ^ 2 * q p)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      hG.mul_bdd hq_aesm hq_bdd
    refine h1.congr ?_
    rw [hQuad]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_quad (fun p hp => ?_)
    obtain ⟨hz, hθ⟩ := Work.FTS.StrongEps.mem_Quad.mp hp
    rw [hq]
    exact epsW_sq_mul_inv hz hθ (h p.1 p.2)
  -- a.e. slice integrability of `h²`
  have hzpos : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z := by
    have hmem : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), z ∈ Work.Spaces.Iz :=
      MeasureTheory.ae_restrict_mem measurableSet_Ici
    have hne : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), z ≠ 0 := by
      rw [MeasureTheory.ae_iff]
      have hset : {z : ℝ | ¬z ≠ 0} = ({0} : Set ℝ) := by
        ext z; simp
      rw [hset]
      rw [MeasureTheory.Measure.restrict_apply (measurableSet_singleton 0)]
      have hI : ({0} : Set ℝ) ∩ Work.Spaces.Iz = ({0} : Set ℝ) := by
        rw [Work.Spaces.Iz]
        ext z
        simp
      rw [hI]
      exact MeasureTheory.measure_singleton 0
    filter_upwards [hmem, hne] with z hz hz0
    exact lt_of_le_of_ne hz (Ne.symm hz0)
  have hslz : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      Integrable (fun θ => (h z θ) ^ 2) (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    filter_upwards [hΞ.prod_right_ae, hzpos] with z h1 hz
    have hw : Work.Spaces.w z ≠ 0 := w_ne_zero_of_pos hz
    have h2 : Integrable
        (fun θ => (Work.Spaces.w z)⁻¹ * ((h z θ) ^ 2 * Work.Spaces.w z))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := h1.const_mul _
    refine h2.congr (Filter.Eventually.of_forall (fun θ => ?_))
    show (Work.Spaces.w z)⁻¹ * ((h z θ) ^ 2 * Work.Spaces.w z) = (h z θ) ^ 2
    rw [mul_comm ((h z θ) ^ 2) (Work.Spaces.w z), inv_mul_cancel_left₀ hw]
  have hsl : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      IntegrableOn (fun θ => (h r θ) ^ 2) Work.Spaces.Iθ :=
    MeasureTheory.ae_mono
      (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume Set.Ioi_subset_Ici_self) hslz
  -- integrability of the weighted angular energy
  have hXint : Integrable
      (fun r => (∫ θ in Work.Spaces.Iθ, (h r θ) ^ 2) * Work.Spaces.w r)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h1 : Integrable
        (fun z => ∫ θ, (h z θ) ^ 2 * Work.Spaces.w z
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := hΞ.integral_prod_left
    refine h1.congr (Filter.Eventually.of_forall (fun r => ?_))
    show (∫ θ, (h r θ) ^ 2 * Work.Spaces.w r
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      = (∫ θ in Work.Spaces.Iθ, (h r θ) ^ 2) * Work.Spaces.w r
    rw [MeasureTheory.integral_mul_const]
  have hXfin : IntegrableOn
      (fun r => (∫ θ in Work.Spaces.Iθ, (h r θ) ^ 2) * Work.Spaces.w r)
      (Set.Ioi (0 : ℝ)) :=
    hXint.mono_measure
      (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume Set.Ioi_subset_Ici_self)
  -- a.e. strong measurability of the weighted angular energy
  have hmeas : AEStronglyMeasurable
      (fun r => (∫ θ in Work.Spaces.Iθ, (h r θ) ^ 2) * ((1 + r) / r) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    have h1 : AEStronglyMeasurable
        (fun r => (∫ θ in Work.Spaces.Iθ, (h r θ) ^ 2) * Work.Spaces.w r)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := hXfin.aestronglyMeasurable
    refine h1.congr (Filter.Eventually.of_forall (fun r => ?_))
    show (∫ θ in Work.Spaces.Iθ, (h r θ) ^ 2) * Work.Spaces.w r
      = (∫ θ in Work.Spaces.Iθ, (h r θ) ^ 2) * ((1 + r) / r) ^ 2
    rw [div_sq_eq_w r]
  -- integrability of the `epsSq`-weighted angular energy
  have hΦ : IntegrableOn (fun r => ∫ θ in Work.Spaces.Iθ, (h r θ * epsW α r θ) ^ 2)
      (Set.Ioi (0 : ℝ)) :=
    (hG.integral_prod_left).mono_measure
      (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume Set.Ioi_subset_Ici_self)
  -- the a.e. comparison of the two angular energies
  have h1ae : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      Integrable (fun θ => (h r θ) ^ 2 * Work.Spaces.w r)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.ae_mono
      (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume Set.Ioi_subset_Ici_self)
      hΞ.prod_right_ae
  have h2ae : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      Integrable (fun θ => (h r θ * epsW α r θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.ae_mono
      (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume Set.Ioi_subset_Ici_self)
      hG.prod_right_ae
  have hbd : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      (∫ θ in Work.Spaces.Iθ, (h r θ) ^ 2) * ((1 + r) / r) ^ 2
        ≤ ∫ θ in Work.Spaces.Iθ, (h r θ * epsW α r θ) ^ 2 := by
    filter_upwards [h1ae, h2ae, MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r h1r h2r hr
    have hr0 : 0 < r := hr
    have hpt : (fun θ => (h r θ) ^ 2 * Work.Spaces.w r)
        ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
          (fun θ => (h r θ * epsW α r θ) ^ 2) := by
      rw [theta_restrict_Ioo]
      exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
        (fun θ hθ => mul_w_le_sq_epsW hα hr0 hθ (h r θ))
    have hmono := MeasureTheory.integral_mono_ae h1r h2r hpt
    rw [MeasureTheory.integral_mul_const] at hmono
    rwa [div_sq_eq_w r]
  have hmain := Work.FTS.OpenPkg.l12zero_of_weight_bound (f := h)
    (Φ := fun r => ∫ θ in Work.Spaces.Iθ, (h r θ * epsW α r θ) ^ 2) hsl hmeas hΦ hbd
  have hEps : (∫ r in Set.Ioi (0 : ℝ),
        ∫ θ in Work.Spaces.Iθ, (h r θ * epsW α r θ) ^ 2) = EpsSq α h := by
    rw [EpsSq, Work.Spaces.Iz]
    exact MeasureTheory.setIntegral_congr_set MeasureTheory.Ioi_ae_eq_Ici
  calc |Work.Construction.L12 h 0|
      ≤ 3 * Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
          ∫ θ in Work.Spaces.Iθ, (h r θ * epsW α r θ) ^ 2) := hmain
    _ = 3 * Real.sqrt (EpsSq α h) := by rw [hEps]

end

end Work.FTS.StrongEps.EpsSqTools
