/-
# `Work.FTS.Nonlinear.Pieces.rl1Tools.FzFacts` — the `L¹`/`L²` facts about the profile `F_*`

The fundamental profile of Elgindi's paper is

  `F_*(z,θ) = α · (Γ(θ)/c(α)) · 2z/(1+z)²`,  `Γ(θ) = (sin θ · cos²θ)^{α/3}`,

where `c(α) = ∫_{Iθ} Γ·K` is the normalisation constant (`Work.Spaces.c`).  This file collects
the eight facts about `F_*` that the nonlinear (row) estimates of §3 need:

1. the defining shape (`rfl`);
2. `F_*` is `C^∞` on the open quadrant (`Work.FTS.LocData.SmoothQuad_Fstar`);
3–5. the angular `L¹`-bounds for `F_*`, `∂_θF_*` and `D_θF_* = sin(2θ)∂_θF_*`;
6–8. the weighted `L²`-bounds for `F_*`, `D_θF_*` and `D_zF_* = z∂_zF_*`.

The three ingredients are: the *pointwise factorisations* of `∂_θ, D_θ, D_z` of `F_*`
(`FzShape`), the angular integrals of `Γ` (`FzAngInts`), and the radial integrals of `F_*`
with the weight `w = (1+z)²/z²` (`FzRadInts`).  The numerical constants are very generous:
the sharp values are `∫_{Iθ}Γ ≤ π/2`, `∫_{Iθ}Γ² ≤ π/2`, `∫_{Iθ}|Γ'| ≤ 8`,
`∫_{(0,∞)} w F_*² = 4`, `∫_{(0,∞)} w (zF_*')² = 4/3`, while `3/5 ≤ c(α)`
(`Work.FTS.LocData.c_ge_three_fifths`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.FTS.LocData.Defs
import Submission.Work.FTS.LocData.SmoothQuad_Fstar
import Submission.Work.FTS.LocData.c_ge_three_fifths
import Submission.Work.FM.Core
import Submission.Work.Spaces.sin_rpow_le_majorant
import Submission.Work.Spaces.integrableOn_majorant_rpow
import Submission.Work.Spaces.integral_majorant_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.rl1Tools

set_option maxHeartbeats 1600000

/-! ## Elementary angular facts -/

/-- The angular interval has measure `π/2`. -/
private lemma volumeReal_Iθ : MeasureTheory.volume.real Work.Spaces.Iθ = Real.pi / 2 := by
  rw [Work.Spaces.Iθ, MeasureTheory.measureReal_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
  ring

/-- A set integral over `Iθ` is the same as one over the open interval `(0,π/2)`. -/
private lemma setIntegral_Iθ_eq_Ioo (f : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, f θ) = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), f θ := by
  rw [Work.Spaces.Iθ]
  exact MeasureTheory.setIntegral_congr_set MeasureTheory.Ioo_ae_eq_Icc.symm

/-- `|qfun θ| ≤ 4/3`, because `qfun θ = cos(2θ) - 1/3 ∈ [-4/3, 2/3]`. -/
private lemma abs_qfun_le (θ : ℝ) : |Work.Spaces.qfun θ| ≤ 4 / 3 := by
  rw [Work.Spaces.qfun_apply, abs_le]
  constructor
  · linarith [Real.neg_one_le_cos (2 * θ)]
  · linarith [Real.cos_le_one (2 * θ)]

/-- If `0 ≤ f ≤ C` on `Iθ`, then `∫_{Iθ} f ≤ C·(π/2)`. -/
private lemma integral_Iθ_le_const {f : ℝ → ℝ} {C : ℝ}
    (hf : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ f θ) (hle : ∀ θ ∈ Work.Spaces.Iθ, f θ ≤ C) :
    (∫ θ in Work.Spaces.Iθ, f θ) ≤ (Real.pi / 2) * C := by
  have hvol : MeasureTheory.volume Work.Spaces.Iθ ≠ ⊤ := by
    rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hint : MeasureTheory.Integrable (fun _ : ℝ => C)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.integrableOn_const hvol (by simp)
  have hae1 : ∀ᵐ x ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), (0 : ℝ) ≤ f x :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hf
  have hae2 : ∀ᵐ x ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), f x ≤ C :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hle
  calc (∫ θ in Work.Spaces.Iθ, f θ) ≤ ∫ θ in Work.Spaces.Iθ, C :=
        MeasureTheory.integral_mono_of_nonneg hae1 hint hae2
    _ = (Real.pi / 2) * C := by
        rw [MeasureTheory.setIntegral_const, volumeReal_Iθ, smul_eq_mul]

/-! ## The angular integrals of `Γ` -/

/-- The pointwise bound for `∂_θΓ` on the open interval: `|Γ'| ≤ (2α/3)(sinθcosθ)^{α/3-1}`.
This is `sin(2θ)Γ' = α q Γ` (`Work.Spaces.dthU_Gam`), `|q| ≤ 4/3` and
`Γ/sin(2θ) = (1/2)(sinθcosθ)^{α/3-1}cos^{α/3}θ`. -/
private lemma abs_deriv_Gam_le (α θ : ℝ) (hα : 0 < α) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    |deriv (fun t => Work.Spaces.Gam α t) θ|
      ≤ (2 * α / 3) * (Real.sin θ * Real.cos θ) ^ (α / 3 - 1) := by
  have h0 : 0 < θ := hθ.1
  have h1 : θ < Real.pi / 2 := hθ.2
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h1⟩
  have hs2 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hA : 0 < Real.sin θ * Real.cos θ := mul_pos hsin hcos
  have hG0 : 0 ≤ Work.Spaces.Gam α θ :=
    (Work.Spaces.Gam_bounds α θ hα ⟨h0.le, h1.le⟩).1
  have hdt : Real.sin (2 * θ) * deriv (fun t => Work.Spaces.Gam α t) θ
      = α * Work.Spaces.qfun θ * Work.Spaces.Gam α θ := by
    simpa only [Work.Spaces.dthU_apply] using Work.Spaces.dthU_Gam α θ hα hθ
  have hderiv : deriv (fun t => Work.Spaces.Gam α t) θ
      = α * Work.Spaces.qfun θ * Work.Spaces.Gam α θ / Real.sin (2 * θ) := by
    rw [eq_div_iff (ne_of_gt hs2)]; linarith [hdt]
  have hGam : Work.Spaces.Gam α θ
      = (Real.sin θ * Real.cos θ) ^ (α / 3) * (Real.cos θ) ^ (α / 3) := by
    rw [Work.Spaces.Gam,
      show Real.sin θ * Real.cos θ ^ 2 = (Real.sin θ * Real.cos θ) * Real.cos θ from by ring,
      Real.mul_rpow hA.le hcos.le]
  have hcos1 : (Real.cos θ) ^ (α / 3) ≤ 1 :=
    Real.rpow_le_one hcos.le (Real.cos_le_one θ) (by positivity)
  calc |deriv (fun t => Work.Spaces.Gam α t) θ|
      = α * |Work.Spaces.qfun θ| * Work.Spaces.Gam α θ / Real.sin (2 * θ) := by
        rw [hderiv, abs_div, abs_mul, abs_mul, abs_of_pos hα, abs_of_pos hs2, abs_of_nonneg hG0]
    _ ≤ α * (4 / 3) * Work.Spaces.Gam α θ / Real.sin (2 * θ) := by
        have hq := abs_qfun_le θ
        have hpos : 0 ≤ α * Work.Spaces.Gam α θ / Real.sin (2 * θ) :=
          div_nonneg (mul_nonneg hα.le hG0) hs2.le
        calc α * |Work.Spaces.qfun θ| * Work.Spaces.Gam α θ / Real.sin (2 * θ)
            = (α * Work.Spaces.Gam α θ / Real.sin (2 * θ)) * |Work.Spaces.qfun θ| := by ring
          _ ≤ (α * Work.Spaces.Gam α θ / Real.sin (2 * θ)) * (4 / 3) :=
              mul_le_mul_of_nonneg_left hq hpos
          _ = α * (4 / 3) * Work.Spaces.Gam α θ / Real.sin (2 * θ) := by ring
    _ = (2 * α / 3) * (Real.sin θ * Real.cos θ) ^ (α / 3 - 1) * (Real.cos θ) ^ (α / 3) := by
        rw [hGam, Real.sin_two_mul]
        have hkey : (Real.sin θ * Real.cos θ) ^ (α / 3)
            = (Real.sin θ * Real.cos θ) ^ (α / 3 - 1) * (Real.sin θ * Real.cos θ) := by
          conv_lhs => rw [show α / 3 = (α / 3 - 1) + 1 by ring]
          rw [Real.rpow_add hA (α / 3 - 1) 1, Real.rpow_one]
        rw [hkey]
        field_simp
        ring
    _ ≤ (2 * α / 3) * (Real.sin θ * Real.cos θ) ^ (α / 3 - 1) := by
        have hnn : 0 ≤ (2 * α / 3) * (Real.sin θ * Real.cos θ) ^ (α / 3 - 1) :=
          mul_nonneg (by positivity) (Real.rpow_nonneg hA.le _)
        calc (2 * α / 3) * (Real.sin θ * Real.cos θ) ^ (α / 3 - 1) * (Real.cos θ) ^ (α / 3)
            ≤ (2 * α / 3) * (Real.sin θ * Real.cos θ) ^ (α / 3 - 1) * 1 :=
              mul_le_mul_of_nonneg_left hcos1 hnn
          _ = (2 * α / 3) * (Real.sin θ * Real.cos θ) ^ (α / 3 - 1) := by ring

/-- `∫_{Iθ}|Γ'| ≤ 40` for `0 < α ≤ 1`, uniformly in `α`.

On `(0,π/2)`, `|Γ'| ≤ (2α/3)(sinθcosθ)^{α/3-1} = (2α/3)·2^p·(sin2θ)^{-p}` with
`p = 1-α/3 ∈ (0,1)`; the chord-bound majorant `Work.Spaces.sin_rpow_le_majorant` gives
`∫_{Iθ}(sin2θ)^{-p} ≤ π(1/2)^p/(1-p)`, so `∫|Γ'| ≤ (4α/3)(3π/α) = 4π ≤ 16`.  The endpoints
are a null set. -/
private lemma integral_abs_deriv_Gam_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    (∫ θ in Work.Spaces.Iθ, |deriv (fun t => Work.Spaces.Gam α t) θ|) ≤ 40 := by
  set p : ℝ := 1 - α / 3 with hpdef
  have hp0 : 0 < p := by simp only [hpdef]; linarith
  have hp1 : p < 1 := by simp only [hpdef]; linarith
  have hpp : -p = α / 3 - 1 := by simp only [hpdef]; ring
  -- the majorant, and its integrability
  have hIntMaj : MeasureTheory.Integrable
      (fun θ : ℝ => (4 * α / 3)
        * ((Real.pi / 4) ^ p * (θ ^ (-p) + (Real.pi / 2 - θ) ^ (-p))))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (Work.Spaces.integrableOn_majorant_rpow p hp0 hp1).const_mul (4 * α / 3)
  have hle : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      |deriv (fun t => Work.Spaces.Gam α t) θ|
        ≤ (4 * α / 3) * ((Real.pi / 4) ^ p * (θ ^ (-p) + (Real.pi / 2 - θ) ^ (-p))) := by
    rw [show MeasureTheory.volume.restrict Work.Spaces.Iθ
        = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) from by
      rw [Work.Spaces.Iθ]
      exact MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc.symm]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    have hb := abs_deriv_Gam_le α θ hα hθ
    have hsin : 0 < Real.sin θ :=
      Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    have hcos : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    have hA : 0 < Real.sin θ * Real.cos θ := mul_pos hsin hcos
    have hconv : (Real.sin θ * Real.cos θ) ^ (α / 3 - 1)
        = (2 : ℝ) ^ p * (Real.sin (2 * θ)) ^ (-p) := by
      have hsin2 : Real.sin (2 * θ) = 2 * (Real.sin θ * Real.cos θ) := by
        rw [Real.sin_two_mul]; ring
      rw [hsin2, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hA.le, ← mul_assoc,
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2) p (-p),
        show p + -p = 0 by ring, Real.rpow_zero, one_mul, hpp]
    have hmaj := Work.Spaces.sin_rpow_le_majorant p θ hp0 ⟨hθ.1.le, hθ.2.le⟩
    have h2p : (2 : ℝ) ^ p ≤ 2 := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (le_of_lt hp1)
      rwa [Real.rpow_one] at h
    have hs2nn : 0 ≤ (Real.sin (2 * θ)) ^ (-p) :=
      Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
        ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) _
    calc |deriv (fun t => Work.Spaces.Gam α t) θ|
        ≤ (2 * α / 3) * (Real.sin θ * Real.cos θ) ^ (α / 3 - 1) := hb
      _ = (2 * α / 3) * ((2 : ℝ) ^ p * (Real.sin (2 * θ)) ^ (-p)) := by rw [hconv]
      _ ≤ (2 * α / 3) * (2 * ((Real.pi / 4) ^ p * (θ ^ (-p) + (Real.pi / 2 - θ) ^ (-p)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul h2p hmaj hs2nn (by norm_num)) (by positivity)
      _ = (4 * α / 3) * ((Real.pi / 4) ^ p * (θ ^ (-p) + (Real.pi / 2 - θ) ^ (-p))) := by ring
  have hmono := MeasureTheory.integral_mono_of_nonneg
    (f := fun θ : ℝ => |deriv (fun t => Work.Spaces.Gam α t) θ|)
    (g := fun θ : ℝ => (4 * α / 3)
      * ((Real.pi / 4) ^ p * (θ ^ (-p) + (Real.pi / 2 - θ) ^ (-p))))
    (Filter.Eventually.of_forall (fun θ => abs_nonneg _)) hIntMaj hle
  have hval : (∫ θ in Work.Spaces.Iθ,
        (Real.pi / 4) ^ p * (θ ^ (-p) + (Real.pi / 2 - θ) ^ (-p)))
      = Real.pi * (1 / 2) ^ p / (1 - p) :=
    Work.Spaces.integral_majorant_rpow p hp0 hp1
  calc (∫ θ in Work.Spaces.Iθ, |deriv (fun t => Work.Spaces.Gam α t) θ|)
      ≤ ∫ θ in Work.Spaces.Iθ, (4 * α / 3)
          * ((Real.pi / 4) ^ p * (θ ^ (-p) + (Real.pi / 2 - θ) ^ (-p))) := hmono
    _ = (4 * α / 3) * (∫ θ in Work.Spaces.Iθ,
          (Real.pi / 4) ^ p * (θ ^ (-p) + (Real.pi / 2 - θ) ^ (-p))) :=
        MeasureTheory.integral_const_mul _ _
    _ = (4 * α / 3) * (Real.pi * (1 / 2) ^ p / (1 - p)) := by rw [hval]
    _ ≤ 40 := by
        have h1p : 1 - p = α / 3 := by simp only [hpdef]; ring
        have hhalf : (1 / 2 : ℝ) ^ p ≤ 1 :=
          Real.rpow_le_one (by norm_num) (by norm_num) (le_of_lt hp0)
        rw [h1p]
        have hkey : (4 * α / 3) * (Real.pi * (1 / 2) ^ p / (α / 3))
            = 4 * Real.pi * (1 / 2) ^ p := by
          field_simp
        rw [hkey]
        have hnn : (0 : ℝ) ≤ (1 / 2) ^ p := Real.rpow_nonneg (by norm_num) _
        nlinarith [Real.pi_pos, Real.pi_le_four, hhalf, hnn]

/-- **Angular integrals of `Γ`.**  For `0 < α ≤ 1`: `∫Γ ≤ 2`, `∫Γ² ≤ 2`, `∫q²Γ² ≤ 4` and
`∫|Γ'| ≤ 40`. -/
theorem FzAngInts (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.Gam α θ) ≤ 2 ∧
    (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ) ^ 2) ≤ 2 ∧
    (∫ θ in Work.Spaces.Iθ, (Work.Spaces.qfun θ) ^ 2 * (Work.Spaces.Gam α θ) ^ 2) ≤ 4 ∧
    (∫ θ in Work.Spaces.Iθ, |deriv (fun t => Work.Spaces.Gam α t) θ|) ≤ 40 := by
  have hb : ∀ θ ∈ Work.Spaces.Iθ,
      0 ≤ Work.Spaces.Gam α θ ∧ Work.Spaces.Gam α θ ≤ 1 :=
    fun θ hθ => Work.Spaces.Gam_bounds α θ hα hθ
  refine ⟨?_, ?_, ?_, integral_abs_deriv_Gam_le α hα hα1⟩
  · calc (∫ θ in Work.Spaces.Iθ, Work.Spaces.Gam α θ) ≤ (Real.pi / 2) * 1 :=
          integral_Iθ_le_const (fun θ hθ => (hb θ hθ).1) (fun θ hθ => (hb θ hθ).2)
      _ ≤ 2 := by linarith [Real.pi_le_four]
  · calc (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ) ^ 2) ≤ (Real.pi / 2) * 1 :=
          integral_Iθ_le_const (fun θ _ => sq_nonneg _)
            (fun θ hθ => by nlinarith [(hb θ hθ).1, (hb θ hθ).2])
      _ ≤ 2 := by linarith [Real.pi_le_four]
  · calc (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.qfun θ) ^ 2 * (Work.Spaces.Gam α θ) ^ 2) ≤ (Real.pi / 2) * (16 / 9) :=
          integral_Iθ_le_const (fun θ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
            (fun θ hθ => by
              have h1' : (Work.Spaces.qfun θ) ^ 2 ≤ (4 / 3) ^ 2 := by
                have h := abs_qfun_le θ
                rw [abs_le] at h
                exact sq_le_sq' h.1 h.2
              have h2 : (Work.Spaces.Gam α θ) ^ 2 ≤ 1 := by
                nlinarith [(hb θ hθ).1, (hb θ hθ).2]
              calc (Work.Spaces.qfun θ) ^ 2 * (Work.Spaces.Gam α θ) ^ 2
                  ≤ (4 / 3) ^ 2 * 1 := mul_le_mul h1' h2 (sq_nonneg _) (by norm_num)
                _ = 16 / 9 := by norm_num)
      _ ≤ 4 := by nlinarith [Real.pi_le_four]

/-! ## The `c`-normalised angular integrals -/

/-- `∫_{Iθ} Γ/c ≤ 10`. -/
private lemma Gam_div_c_int_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.Gam α θ / Work.Spaces.c α) ≤ 10 := by
  have hc := Work.FTS.LocData.c_ge_three_fifths α hα hα1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have h1 : (∫ θ in Work.Spaces.Iθ, Work.Spaces.Gam α θ / Work.Spaces.c α)
      = (∫ θ in Work.Spaces.Iθ, Work.Spaces.Gam α θ) / Work.Spaces.c α :=
    MeasureTheory.integral_div _ _
  rw [h1, div_le_iff₀ hcpos]
  have h2 := (FzAngInts α hα hα1).1
  nlinarith

/-- `∫_{Iθ} (Γ/c)² ≤ 10`. -/
private lemma Gam_div_c_sq_int_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2) ≤ 10 := by
  have hc := Work.FTS.LocData.c_ge_three_fifths α hα hα1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have h1 : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2)
      = (1 / (Work.Spaces.c α) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ) ^ 2) := by
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
  rw [h1]
  have h2 := (FzAngInts α hα hα1).2.1
  have h4 : (1 : ℝ) / (Work.Spaces.c α) ^ 2 ≤ 25 / 9 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have h5 : (1 / (Work.Spaces.c α) ^ 2) * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ) ^ 2)
      ≤ (25 / 9) * 2 :=
    mul_le_mul h4 h2 (MeasureTheory.integral_nonneg (fun θ => sq_nonneg _))
      (by norm_num)
  linarith

/-- `∫_{Iθ} q²(Γ/c)² ≤ 100`. -/
private lemma qfun_Gam_div_c_sq_int_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    (∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.qfun θ * Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2) ≤ 100 := by
  have hc := Work.FTS.LocData.c_ge_three_fifths α hα hα1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have h1 : (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.qfun θ * Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2)
      = (1 / (Work.Spaces.c α) ^ 2)
          * (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.qfun θ) ^ 2 * (Work.Spaces.Gam α θ) ^ 2) := by
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
  rw [h1]
  have h2 := (FzAngInts α hα hα1).2.2.1
  have h4 : (1 : ℝ) / (Work.Spaces.c α) ^ 2 ≤ 25 / 9 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have h5 : (1 / (Work.Spaces.c α) ^ 2)
      * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.qfun θ) ^ 2 * (Work.Spaces.Gam α θ) ^ 2)
      ≤ (25 / 9) * 4 :=
    mul_le_mul h4 h2 (MeasureTheory.integral_nonneg (fun θ => mul_nonneg (sq_nonneg _) (sq_nonneg _)))
      (by norm_num)
  linarith

/-- `∫_{Iθ} |Γ'|/c ≤ 100`. -/
private lemma deriv_Gam_div_c_int_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    (∫ θ in Work.Spaces.Iθ, |deriv (fun t => Work.Spaces.Gam α t) θ| / Work.Spaces.c α)
      ≤ 100 := by
  have hc := Work.FTS.LocData.c_ge_three_fifths α hα hα1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  rw [MeasureTheory.integral_div, div_le_iff₀ hcpos]
  have h2 := (FzAngInts α hα hα1).2.2.2
  nlinarith

/-! ## The radial profile `F_*` -/

/-- `F_*(z) = 2z/(1+z)² ≥ 0` for `z ≥ 0`. -/
private lemma Fstar_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ Work.FM.Fstar z := by
  rw [Work.FM.Fstar]
  exact div_nonneg (by linarith) (by positivity)

/-- The radial conversion factor: `m·F_*(z)·C ≤ 200·m·(z/(1+z)²)` whenever `C ≤ 100`, `m ≥ 0`
and `z ≥ 0`.  (Because `F_*(z) = 2z/(1+z)²` and hence `2C ≤ 200`.) -/
private lemma Fstar_factor_le {m C z : ℝ} (hm : 0 ≤ m) (hz : 0 ≤ z) (hC : C ≤ 100) :
    m * Work.FM.Fstar z * C ≤ 200 * m * (z / (1 + z) ^ 2) := by
  rw [Work.FM.Fstar]
  have hz0 : 0 ≤ z / (1 + z) ^ 2 := div_nonneg hz (by positivity)
  have h1 : 0 ≤ m * (z / (1 + z) ^ 2) := mul_nonneg hm hz0
  have h2 : 2 * C ≤ 200 := by linarith
  rw [show m * (2 * z / (1 + z) ^ 2) * C = (2 * C) * (m * (z / (1 + z) ^ 2)) from by ring,
    show 200 * m * (z / (1 + z) ^ 2) = 200 * (m * (z / (1 + z) ^ 2)) from by ring]
  exact mul_le_mul_of_nonneg_right h2 h1

/-- **Radial integrals of `F_*` with the weight `w = (1+z)²/z²`.**  Both `w·F_*²` and
`w·(zF_*')²` are integrable on `(0,∞)` with integrals `≤ 8` (the sharp values are `4` and `4/3`,
and both integrands are dominated by `4(1+z)^{-2}` whose integral is `1`). -/
theorem FzRadInts :
    MeasureTheory.IntegrableOn (fun z : ℝ => Work.Spaces.w z * (Work.FM.Fstar z) ^ 2)
      (Set.Ioi (0 : ℝ)) ∧
    MeasureTheory.IntegrableOn (fun z : ℝ => Work.Spaces.w z * (z * deriv Work.FM.Fstar z) ^ 2)
      (Set.Ioi (0 : ℝ)) ∧
    (∫ z in Set.Ioi (0 : ℝ), Work.Spaces.w z * (Work.FM.Fstar z) ^ 2) ≤ 8 ∧
    (∫ z in Set.Ioi (0 : ℝ), Work.Spaces.w z * (z * deriv Work.FM.Fstar z) ^ 2) ≤ 8 := by
  -- integrability of `(1+z)^{-2}` on `(0,∞)`
  have hbase_int : MeasureTheory.IntegrableOn (fun z : ℝ => (1 + z) ^ (-2 : ℝ))
      (Set.Ioi (0 : ℝ)) := by
    refine MeasureTheory.IntegrableOn.congr_fun
      (integrableOn_add_rpow_Ioi_of_lt (a := (-2 : ℝ)) (c := (0 : ℝ)) (m := (1 : ℝ))
        (by norm_num) (by norm_num)) ?_ measurableSet_Ioi
    intro z _
    show (z + 1) ^ (-2 : ℝ) = (1 + z) ^ (-2 : ℝ)
    rw [show z + 1 = 1 + z by ring]
  -- its value is `1`
  have hbase_val : (∫ z in Set.Ioi (0 : ℝ), (1 + z) ^ (-2 : ℝ)) = 1 := by
    have hderiv : ∀ x ∈ Set.Ioi (0 : ℝ),
        HasDerivAt (fun z : ℝ => -((1 + z)⁻¹)) ((1 + x) ^ (-2 : ℝ)) x := by
      intro x hx
      have hx0 : (0 : ℝ) < 1 + x := by
        have hx' : (0 : ℝ) < x := hx
        linarith
      have h1 : HasDerivAt (fun z : ℝ => 1 + z) (1 : ℝ) x := (hasDerivAt_id x).const_add 1
      have h2 : HasDerivAt (fun z : ℝ => (1 + z)⁻¹) (-((1 + x) ^ 2)⁻¹) x := by
        have h := h1.inv (ne_of_gt hx0)
        convert h using 1
        ring
      have h3 : HasDerivAt (fun z : ℝ => -((1 + z)⁻¹)) (-(-((1 + x) ^ 2)⁻¹)) x := h2.neg
      refine h3.congr_deriv ?_
      rw [neg_neg, show (-2 : ℝ) = -(2 : ℝ) by norm_num,
        Real.rpow_neg (x := 1 + x) (le_of_lt hx0) 2, Real.rpow_two]
    have hcont : ContinuousWithinAt (fun z : ℝ => -((1 + z)⁻¹)) (Set.Ici 0) 0 := by
      refine ContinuousAt.neg ?_ |>.continuousWithinAt
      exact ContinuousAt.inv₀ (continuousAt_const.add continuousAt_id) (by norm_num)
    have htend : Filter.Tendsto (fun z : ℝ => -((1 + z)⁻¹)) Filter.atTop (𝓝 (0 : ℝ)) := by
      have h : Filter.Tendsto (fun z : ℝ => (1 + z)⁻¹) Filter.atTop (𝓝 0) :=
        Filter.Tendsto.comp tendsto_inv_atTop_zero
          (tendsto_atTop_add_const_left atTop 1 tendsto_id)
      simpa using h.neg
    have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto (a := (0 : ℝ))
      (f := fun z : ℝ => -((1 + z)⁻¹)) (f' := fun z : ℝ => (1 + z) ^ (-2 : ℝ)) (m := 0)
      hcont hderiv hbase_int htend
    simpa using h
  -- pointwise identities
  have hpt1 : ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.Spaces.w z * (Work.FM.Fstar z) ^ 2 = 4 / (1 + z) ^ 2 := by
    intro z hz
    have hzpos : (0 : ℝ) < z := hz
    rw [Work.Spaces.w, Work.FM.Fstar]
    field_simp
    ring
  have hpt2 : ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.Spaces.w z * (z * deriv Work.FM.Fstar z) ^ 2 = 4 * (1 - z) ^ 2 / (1 + z) ^ 4 := by
    intro z hz
    have hzpos : (0 : ℝ) < z := hz
    rw [Work.Spaces.w, Work.FM.deriv_Fstar z (by linarith : -1 < z)]
    field_simp
    ring
  have hpt2le : ∀ z ∈ Set.Ioi (0 : ℝ),
      4 * (1 - z) ^ 2 / (1 + z) ^ 4 ≤ 4 / (1 + z) ^ 2 := by
    intro z hz
    have hzpos : (0 : ℝ) < z := hz
    have h1z : (1 - z) ^ 2 ≤ (1 + z) ^ 2 := by nlinarith
    have hpos : (0 : ℝ) < (1 + z) ^ 4 := by positivity
    have hpos2 : (0 : ℝ) < (1 + z) ^ 2 := by positivity
    rw [div_le_div_iff₀ hpos hpos2]
    nlinarith [h1z, hpos2]
  -- `4/(1+z)²` is integrable
  have hInt4 : MeasureTheory.Integrable (fun z : ℝ => 4 / (1 + z) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    MeasureTheory.IntegrableOn.congr_fun (hbase_int.const_mul 4) (fun z hz => by
      have hzpos : (0 : ℝ) < z := hz
      have hz0 : (0 : ℝ) < 1 + z := by linarith
      rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg hz0.le, Real.rpow_two,
        div_eq_mul_inv]) measurableSet_Ioi
  -- the two integrability statements
  have hInt1 : MeasureTheory.IntegrableOn
      (fun z : ℝ => Work.Spaces.w z * (Work.FM.Fstar z) ^ 2) (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.IntegrableOn.congr_fun (hbase_int.const_mul 4) (fun z hz => by
      rw [hpt1 z hz]
      have hzpos : (0 : ℝ) < z := hz
      have hz0 : (0 : ℝ) < 1 + z := by linarith
      rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg hz0.le, Real.rpow_two,
        div_eq_mul_inv]) measurableSet_Ioi
  have hInt3 : MeasureTheory.Integrable (fun z : ℝ => 4 * (1 - z) ^ 2 / (1 + z) ^ 4)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    refine hInt4.mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
      intro z hz
      have hzpos : (0 : ℝ) < z := hz
      positivity
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
      have hzpos : (0 : ℝ) < z := hz
      have h4 : (0 : ℝ) < (1 + z) ^ 4 := by positivity
      rw [Real.norm_of_nonneg (by positivity)]
      exact hpt2le z hz
  have hInt2 : MeasureTheory.IntegrableOn
      (fun z : ℝ => Work.Spaces.w z * (z * deriv Work.FM.Fstar z) ^ 2) (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.IntegrableOn.congr_fun hInt3 (fun z hz => (hpt2 z hz).symm) measurableSet_Ioi
  refine ⟨hInt1, hInt2, ?_, ?_⟩
  · calc (∫ z in Set.Ioi (0 : ℝ), Work.Spaces.w z * (Work.FM.Fstar z) ^ 2)
        = ∫ z in Set.Ioi (0 : ℝ), 4 / (1 + z) ^ 2 :=
          MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hpt1
      _ = 4 * (∫ z in Set.Ioi (0 : ℝ), (1 + z) ^ (-2 : ℝ)) := by
          rw [← MeasureTheory.integral_const_mul]
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
          have hzpos : (0 : ℝ) < z := hz
          have hz0 : (0 : ℝ) < 1 + z := by linarith
          rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg hz0.le, Real.rpow_two,
            div_eq_mul_inv]
      _ = 4 * 1 := by rw [hbase_val]
      _ ≤ 8 := by norm_num
  · calc (∫ z in Set.Ioi (0 : ℝ), Work.Spaces.w z * (z * deriv Work.FM.Fstar z) ^ 2)
        = ∫ z in Set.Ioi (0 : ℝ), 4 * (1 - z) ^ 2 / (1 + z) ^ 4 :=
          MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hpt2
      _ ≤ ∫ z in Set.Ioi (0 : ℝ), 4 / (1 + z) ^ 2 :=
          MeasureTheory.integral_mono_of_nonneg
            (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => by
              have hzpos : (0 : ℝ) < z := hz
              have h4 : (0 : ℝ) < (1 + z) ^ 4 := by positivity
              positivity))
            hInt4
            (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi hpt2le)
      _ = 4 * (∫ z in Set.Ioi (0 : ℝ), (1 + z) ^ (-2 : ℝ)) := by
          rw [← MeasureTheory.integral_const_mul]
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
          have hzpos : (0 : ℝ) < z := hz
          have hz0 : (0 : ℝ) < 1 + z := by linarith
          rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg hz0.le, Real.rpow_two,
            div_eq_mul_inv]
      _ = 4 * 1 := by rw [hbase_val]
      _ ≤ 8 := by norm_num

/-! ## The derivatives of `F_*` -/

/-- **The pointwise factorisations of `∂_θF_*`, `D_θF_*` and `D_zF_*`.** -/
theorem FzShape (α : ℝ) (hα : 0 < α) :
    (∀ z θ : ℝ, 0 < θ → θ < Real.pi / 2 → Work.Spaces.pth (Work.Construction.Fstar α) z θ
        = α * (deriv (fun t => Work.Spaces.Gam α t) θ / Work.Spaces.c α)
            * Work.FM.Fstar z) ∧
    (∀ z θ : ℝ, 0 < θ → θ < Real.pi / 2 → Work.Spaces.Dth (Work.Construction.Fstar α) z θ
        = α ^ 2 * (Work.Spaces.qfun θ * Work.Spaces.Gam α θ / Work.Spaces.c α)
            * Work.FM.Fstar z) ∧
    (∀ z θ : ℝ, -1 < z → Work.Spaces.Dz (Work.Construction.Fstar α) z θ
        = α * (Work.Spaces.Gam α θ / Work.Spaces.c α) * (z * deriv Work.FM.Fstar z)) := by
  have hpth : ∀ z θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pth (Work.Construction.Fstar α) z θ
        = α * (deriv (fun t => Work.Spaces.Gam α t) θ / Work.Spaces.c α)
            * Work.FM.Fstar z := by
    intro z θ h0 h1
    have hd : DifferentiableAt ℝ (fun t => Work.Spaces.Gam α t) θ :=
      Work.Spaces.Gam_differentiableAt α θ h0 h1
    rw [Work.Spaces.pth]
    have heq : (fun θ' => Work.Construction.Fstar α z θ')
        =ᶠ[𝓝 θ]
          (fun θ' => (α * Work.FM.Fstar z / Work.Spaces.c α) * Work.Spaces.Gam α θ') :=
      Filter.Eventually.of_forall (fun θ' => by
        simp only [Work.Construction.Fstar]; ring)
    rw [heq.deriv_eq, deriv_const_mul _ hd]
    ring
  refine ⟨hpth, ?_, ?_⟩
  · intro z θ h0 h1
    have hdt : Real.sin (2 * θ) * deriv (fun t => Work.Spaces.Gam α t) θ
        = α * Work.Spaces.qfun θ * Work.Spaces.Gam α θ := by
      simpa only [Work.Spaces.dthU_apply] using Work.Spaces.dthU_Gam α θ hα ⟨h0, h1⟩
    rw [Work.Spaces.Dth, hpth z θ h0 h1]
    rw [show Real.sin (2 * θ)
          * (α * (deriv (fun t => Work.Spaces.Gam α t) θ / Work.Spaces.c α)
              * Work.FM.Fstar z)
        = (α * Work.FM.Fstar z / Work.Spaces.c α)
            * (Real.sin (2 * θ) * deriv (fun t => Work.Spaces.Gam α t) θ) from by ring,
      hdt]
    ring
  · intro z θ hz
    have hd : DifferentiableAt ℝ Work.FM.Fstar z := (Work.FM.hasDerivAt_Fstar z hz).differentiableAt
    rw [Work.Spaces.Dz, Work.Spaces.pz]
    have heq : (fun z' => Work.Construction.Fstar α z' θ)
        =ᶠ[𝓝 z]
          (fun z' => (α * (Work.Spaces.Gam α θ / Work.Spaces.c α)) * Work.FM.Fstar z') :=
      Filter.Eventually.of_forall (fun z' => by
        simp only [Work.Construction.Fstar])
    rw [heq.deriv_eq, deriv_const_mul _ hd]
    ring

theorem FzFacts :
    (∀ α z θ : ℝ, Work.Construction.Fstar α z θ
      = α * (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z / (1 + z) ^ 2)) ∧
    (∀ α : ℝ, Work.FTS.LocData.SmoothQuad (Work.Construction.Fstar α)) ∧
    (∀ α : ℝ, 0 < α → α ≤ 1 → ∀ z ∈ Work.Spaces.Iz,
      ∫ θ in Work.Spaces.Iθ, |Work.Construction.Fstar α z θ| ≤ 200 * α * (z / (1 + z) ^ 2)) ∧
    (∀ α : ℝ, 0 < α → α ≤ 1 → ∀ z ∈ Work.Spaces.Iz,
      ∫ θ in Work.Spaces.Iθ, |Work.Spaces.pth (Work.Construction.Fstar α) z θ|
        ≤ 200 * α * (z / (1 + z) ^ 2)) ∧
    (∀ α : ℝ, 0 < α → α ≤ 1 → ∀ z ∈ Work.Spaces.Iz,
      ∫ θ in Work.Spaces.Iθ, |Work.Spaces.Dth (Work.Construction.Fstar α) z θ|
        ≤ 200 * α ^ 2 * (z / (1 + z) ^ 2)) ∧
    (∀ α : ℝ, 0 < α → α ≤ 1 →
      ∫ z in Set.Ioi (0 : ℝ), Work.Spaces.w z
        * (∫ θ in Work.Spaces.Iθ, (Work.Construction.Fstar α z θ) ^ 2) ≤ 1000 * α ^ 2) ∧
    (∀ α : ℝ, 0 < α → α ≤ 1 →
      ∫ z in Set.Ioi (0 : ℝ), Work.Spaces.w z
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ^ 2)
        ≤ 1000 * α ^ 4) ∧
    (∀ α : ℝ, 0 < α → α ≤ 1 →
      ∫ z in Set.Ioi (0 : ℝ), Work.Spaces.w z
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz (Work.Construction.Fstar α) z θ) ^ 2)
        ≤ 1000 * α ^ 2) := by
  have hshape := FzShape
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro α z θ
    rfl
  · intro α
    exact Work.FTS.LocData.SmoothQuad_Fstar α
  · -- `∫_{Iθ} |F_*| ≤ 200 α z/(1+z)²`
    intro α hα hα1 z hz
    have hz0 : 0 ≤ z := hz
    have hR : 0 ≤ Work.FM.Fstar z := Fstar_nonneg hz0
    have hcpos : 0 < Work.Spaces.c α := by
      have h := (Work.Spaces.c_bounds α hα hα1).1
      linarith
    have hkey : (∫ θ in Work.Spaces.Iθ, |Work.Construction.Fstar α z θ|)
        = α * Work.FM.Fstar z
            * (∫ θ in Work.Spaces.Iθ, Work.Spaces.Gam α θ / Work.Spaces.c α) := by
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
      have hG : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
      rw [abs_of_nonneg (by
        simp only [Work.Construction.Fstar]
        exact mul_nonneg (mul_nonneg hα.le (div_nonneg hG hcpos.le)) hR)]
      simp only [Work.Construction.Fstar]
      ring
    rw [hkey]
    have h1 : (∫ θ in Work.Spaces.Iθ, Work.Spaces.Gam α θ / Work.Spaces.c α) ≤ 10 :=
      Gam_div_c_int_le hα hα1
    calc α * Work.FM.Fstar z
          * (∫ θ in Work.Spaces.Iθ, Work.Spaces.Gam α θ / Work.Spaces.c α)
        ≤ α * Work.FM.Fstar z * 10 :=
          mul_le_mul_of_nonneg_left h1 (mul_nonneg hα.le hR)
      _ ≤ 200 * α * (z / (1 + z) ^ 2) := Fstar_factor_le hα.le hz0 (by norm_num)
  · -- `∫_{Iθ} |∂_θF_*| ≤ 200 α z/(1+z)²`
    intro α hα hα1 z hz
    have hz0 : 0 ≤ z := hz
    have hR : 0 ≤ Work.FM.Fstar z := Fstar_nonneg hz0
    have hcpos : 0 < Work.Spaces.c α := by
      have h := (Work.Spaces.c_bounds α hα hα1).1
      linarith
    have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |Work.Spaces.pth (Work.Construction.Fstar α) z θ|
          = α * Work.FM.Fstar z
              * (|deriv (fun t => Work.Spaces.Gam α t) θ| / Work.Spaces.c α) := by
      intro θ hθ
      rw [(hshape α hα).1 z θ hθ.1 hθ.2, abs_mul, abs_mul, abs_of_pos hα, abs_of_nonneg hR,
        abs_div, abs_of_pos hcpos]
      ring
    calc (∫ θ in Work.Spaces.Iθ, |Work.Spaces.pth (Work.Construction.Fstar α) z θ|)
        = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
            |Work.Spaces.pth (Work.Construction.Fstar α) z θ| := setIntegral_Iθ_eq_Ioo _
      _ = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), α * Work.FM.Fstar z
            * (|deriv (fun t => Work.Spaces.Gam α t) θ| / Work.Spaces.c α) :=
          MeasureTheory.setIntegral_congr_fun measurableSet_Ioo hpt
      _ = α * Work.FM.Fstar z
            * (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
                |deriv (fun t => Work.Spaces.Gam α t) θ| / Work.Spaces.c α) :=
          MeasureTheory.integral_const_mul _ _
      _ = α * Work.FM.Fstar z
            * (∫ θ in Work.Spaces.Iθ,
                |deriv (fun t => Work.Spaces.Gam α t) θ| / Work.Spaces.c α) := by
          rw [setIntegral_Iθ_eq_Ioo]
      _ ≤ α * Work.FM.Fstar z * 100 :=
          mul_le_mul_of_nonneg_left (deriv_Gam_div_c_int_le hα hα1) (mul_nonneg hα.le hR)
      _ ≤ 200 * α * (z / (1 + z) ^ 2) := Fstar_factor_le hα.le hz0 (by norm_num)
  · -- `∫_{Iθ} |D_θF_*| ≤ 200 α² z/(1+z)²`
    intro α hα hα1 z hz
    have hz0 : 0 ≤ z := hz
    have hR : 0 ≤ Work.FM.Fstar z := Fstar_nonneg hz0
    have hc0 : 0 < Work.Spaces.c α := by
      have h := (Work.Spaces.c_bounds α hα hα1).1
      linarith
    have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |Work.Spaces.Dth (Work.Construction.Fstar α) z θ|
          ≤ α ^ 2 * Work.FM.Fstar z * (20 / 9) := by
      intro θ hθ
      have hq := abs_qfun_le θ
      have hG := Work.Spaces.Gam_bounds α θ hα ⟨hθ.1.le, hθ.2.le⟩
      have hc3 : (3 : ℝ) / 5 ≤ Work.Spaces.c α :=
        Work.FTS.LocData.c_ge_three_fifths α hα hα1
      have hdiv : |Work.Spaces.qfun θ| * Work.Spaces.Gam α θ / Work.Spaces.c α ≤ 20 / 9 := by
        rw [div_le_iff₀ hc0]
        nlinarith [hq, hG.1, hG.2, hc3]
      have habs : |Work.Spaces.Dth (Work.Construction.Fstar α) z θ|
          = α ^ 2 * (|Work.Spaces.qfun θ| * Work.Spaces.Gam α θ / Work.Spaces.c α)
              * Work.FM.Fstar z := by
        rw [(hshape α hα).2.1 z θ hθ.1 hθ.2, abs_mul, abs_mul,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ α ^ 2), abs_of_nonneg hR, abs_div,
          abs_of_pos hc0, abs_mul, abs_of_nonneg hG.1]
      rw [habs]
      calc α ^ 2 * (|Work.Spaces.qfun θ| * Work.Spaces.Gam α θ / Work.Spaces.c α)
            * Work.FM.Fstar z
          = α ^ 2 * Work.FM.Fstar z
              * (|Work.Spaces.qfun θ| * Work.Spaces.Gam α θ / Work.Spaces.c α) := by ring
        _ ≤ α ^ 2 * Work.FM.Fstar z * (20 / 9) :=
            mul_le_mul_of_nonneg_left hdiv (mul_nonneg (by positivity) hR)
    have hIntC : MeasureTheory.Integrable (fun _ : ℝ => α ^ 2 * Work.FM.Fstar z * (20 / 9))
        (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
      MeasureTheory.integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
        (by finiteness)
    calc (∫ θ in Work.Spaces.Iθ, |Work.Spaces.Dth (Work.Construction.Fstar α) z θ|)
        = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
            |Work.Spaces.Dth (Work.Construction.Fstar α) z θ| := setIntegral_Iθ_eq_Ioo _
      _ ≤ ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), α ^ 2 * Work.FM.Fstar z * (20 / 9) :=
          MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall (fun θ => abs_nonneg _)) hIntC
            (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo hpt)
      _ = α ^ 2 * Work.FM.Fstar z * (20 / 9) * (Real.pi / 2) := by
          rw [MeasureTheory.setIntegral_congr_set (s := Set.Ioo (0 : ℝ) (Real.pi / 2))
            (t := Work.Spaces.Iθ) (f := fun _ => α ^ 2 * Work.FM.Fstar z * (20 / 9))
            MeasureTheory.Ioo_ae_eq_Icc,
            MeasureTheory.setIntegral_const, volumeReal_Iθ, smul_eq_mul]
          ring
      _ ≤ 200 * α ^ 2 * (z / (1 + z) ^ 2) := by
          have hcle : (20 / 9) * (Real.pi / 2) ≤ 100 := by nlinarith [Real.pi_le_four]
          have h := Fstar_factor_le (m := α ^ 2) (C := (20 / 9) * (Real.pi / 2))
            (by positivity) hz0 hcle
          calc α ^ 2 * Work.FM.Fstar z * (20 / 9) * (Real.pi / 2)
              = α ^ 2 * Work.FM.Fstar z * ((20 / 9) * (Real.pi / 2)) := by ring
            _ ≤ 200 * α ^ 2 * (z / (1 + z) ^ 2) := h
  · -- `∫_{(0,∞)} w·∫_{Iθ} F_*² ≤ 1000 α²`
    intro α hα hα1
    have hpt : ∀ z ∈ Set.Ioi (0 : ℝ), Work.Spaces.w z
        * (∫ θ in Work.Spaces.Iθ, (Work.Construction.Fstar α z θ) ^ 2)
        ≤ 10 * α ^ 2 * (Work.Spaces.w z * (Work.FM.Fstar z) ^ 2) := by
      intro z hz
      have hzpos : (0 : ℝ) < z := hz
      have hw : 0 ≤ Work.Spaces.w z := by rw [Work.Spaces.w]; positivity
      have hR : 0 ≤ Work.FM.Fstar z := Fstar_nonneg (le_of_lt hzpos)
      have hfac : (∫ θ in Work.Spaces.Iθ, (Work.Construction.Fstar α z θ) ^ 2)
          = (α * Work.FM.Fstar z) ^ 2
              * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2) := by
        rw [← MeasureTheory.integral_const_mul]
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
        simp only [Work.Construction.Fstar]
        ring
      rw [hfac]
      have h2 := Gam_div_c_sq_int_le hα hα1
      calc Work.Spaces.w z * ((α * Work.FM.Fstar z) ^ 2
            * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2))
          ≤ Work.Spaces.w z * ((α * Work.FM.Fstar z) ^ 2 * 10) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left h2 (sq_nonneg _)) hw
        _ = 10 * α ^ 2 * (Work.Spaces.w z * (Work.FM.Fstar z) ^ 2) := by ring
    have hInt : MeasureTheory.Integrable
        (fun z : ℝ => 10 * α ^ 2 * (Work.Spaces.w z * (Work.FM.Fstar z) ^ 2))
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      FzRadInts.1.const_mul (10 * α ^ 2)
    calc (∫ z in Set.Ioi (0 : ℝ), Work.Spaces.w z
          * (∫ θ in Work.Spaces.Iθ, (Work.Construction.Fstar α z θ) ^ 2))
        ≤ ∫ z in Set.Ioi (0 : ℝ),
            10 * α ^ 2 * (Work.Spaces.w z * (Work.FM.Fstar z) ^ 2) :=
          MeasureTheory.integral_mono_of_nonneg
            (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => by
              have hzpos : (0 : ℝ) < z := hz
              have hw : 0 ≤ Work.Spaces.w z := by rw [Work.Spaces.w]; positivity
              exact mul_nonneg hw (MeasureTheory.integral_nonneg (fun θ => sq_nonneg _))))
            hInt
            (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi hpt)
      _ = 10 * α ^ 2
            * (∫ z in Set.Ioi (0 : ℝ), Work.Spaces.w z * (Work.FM.Fstar z) ^ 2) :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ 10 * α ^ 2 * 8 := mul_le_mul_of_nonneg_left FzRadInts.2.2.1 (by positivity)
      _ ≤ 1000 * α ^ 2 := by nlinarith [sq_nonneg α]
  · -- `∫_{(0,∞)} w·∫_{Iθ} (D_θF_*)² ≤ 1000 α⁴`
    intro α hα hα1
    have hpt : ∀ z ∈ Set.Ioi (0 : ℝ), Work.Spaces.w z
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ^ 2)
        ≤ 100 * α ^ 4 * (Work.Spaces.w z * (Work.FM.Fstar z) ^ 2) := by
      intro z hz
      have hzpos : (0 : ℝ) < z := hz
      have hw : 0 ≤ Work.Spaces.w z := by rw [Work.Spaces.w]; positivity
      have hfac : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ^ 2)
          = (α ^ 2 * Work.FM.Fstar z) ^ 2
              * (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
                  (Work.Spaces.qfun θ * Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2) := by
        rw [setIntegral_Iθ_eq_Ioo
          (fun θ => (Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ^ 2)]
        rw [← MeasureTheory.integral_const_mul]
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ hθ => ?_)
        rw [(hshape α hα).2.1 z θ hθ.1 hθ.2]
        ring
      have h2 : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
            (Work.Spaces.qfun θ * Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2) ≤ 100 := by
        rw [MeasureTheory.setIntegral_congr_set (s := Set.Ioo (0 : ℝ) (Real.pi / 2))
          (t := Work.Spaces.Iθ)
          (f := fun θ => (Work.Spaces.qfun θ * Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2)
          MeasureTheory.Ioo_ae_eq_Icc]
        exact qfun_Gam_div_c_sq_int_le hα hα1
      rw [hfac]
      calc Work.Spaces.w z * ((α ^ 2 * Work.FM.Fstar z) ^ 2
            * (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
                (Work.Spaces.qfun θ * Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2))
          ≤ Work.Spaces.w z * ((α ^ 2 * Work.FM.Fstar z) ^ 2 * 100) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (sq_nonneg _)) hw
        _ = 100 * α ^ 4 * (Work.Spaces.w z * (Work.FM.Fstar z) ^ 2) := by ring
    have hInt : MeasureTheory.Integrable
        (fun z : ℝ => 100 * α ^ 4 * (Work.Spaces.w z * (Work.FM.Fstar z) ^ 2))
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      FzRadInts.1.const_mul (100 * α ^ 4)
    calc (∫ z in Set.Ioi (0 : ℝ), Work.Spaces.w z
          * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ^ 2))
        ≤ ∫ z in Set.Ioi (0 : ℝ),
            100 * α ^ 4 * (Work.Spaces.w z * (Work.FM.Fstar z) ^ 2) :=
          MeasureTheory.integral_mono_of_nonneg
            (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => by
              have hzpos : (0 : ℝ) < z := hz
              have hw : 0 ≤ Work.Spaces.w z := by rw [Work.Spaces.w]; positivity
              exact mul_nonneg hw (MeasureTheory.integral_nonneg (fun θ => sq_nonneg _))))
            hInt
            (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi hpt)
      _ = 100 * α ^ 4
            * (∫ z in Set.Ioi (0 : ℝ), Work.Spaces.w z * (Work.FM.Fstar z) ^ 2) :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ 100 * α ^ 4 * 8 := mul_le_mul_of_nonneg_left FzRadInts.2.2.1 (by positivity)
      _ ≤ 1000 * α ^ 4 := by nlinarith [sq_nonneg α]
  · -- `∫_{(0,∞)} w·∫_{Iθ} (D_zF_*)² ≤ 1000 α²`
    intro α hα hα1
    have hpt : ∀ z ∈ Set.Ioi (0 : ℝ), Work.Spaces.w z
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz (Work.Construction.Fstar α) z θ) ^ 2)
        ≤ 10 * α ^ 2 * (Work.Spaces.w z * (z * deriv Work.FM.Fstar z) ^ 2) := by
      intro z hz
      have hzpos : (0 : ℝ) < z := hz
      have hw : 0 ≤ Work.Spaces.w z := by rw [Work.Spaces.w]; positivity
      have hfac : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz (Work.Construction.Fstar α) z θ) ^ 2)
          = (α * (z * deriv Work.FM.Fstar z)) ^ 2
              * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2) := by
        rw [← MeasureTheory.integral_const_mul]
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
        rw [(hshape α hα).2.2 z θ (by linarith : (-1 : ℝ) < z)]
        ring
      rw [hfac]
      have h2 := Gam_div_c_sq_int_le hα hα1
      calc Work.Spaces.w z * ((α * (z * deriv Work.FM.Fstar z)) ^ 2
            * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2))
          ≤ Work.Spaces.w z * ((α * (z * deriv Work.FM.Fstar z)) ^ 2 * 10) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (sq_nonneg _)) hw
        _ = 10 * α ^ 2
              * (Work.Spaces.w z * (z * deriv Work.FM.Fstar z) ^ 2) := by ring
    have hInt : MeasureTheory.Integrable
        (fun z : ℝ => 10 * α ^ 2 * (Work.Spaces.w z * (z * deriv Work.FM.Fstar z) ^ 2))
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      FzRadInts.2.1.const_mul (10 * α ^ 2)
    calc (∫ z in Set.Ioi (0 : ℝ), Work.Spaces.w z
          * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz (Work.Construction.Fstar α) z θ) ^ 2))
        ≤ ∫ z in Set.Ioi (0 : ℝ),
            10 * α ^ 2 * (Work.Spaces.w z * (z * deriv Work.FM.Fstar z) ^ 2) :=
          MeasureTheory.integral_mono_of_nonneg
            (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => by
              have hzpos : (0 : ℝ) < z := hz
              have hw : 0 ≤ Work.Spaces.w z := by rw [Work.Spaces.w]; positivity
              exact mul_nonneg hw (MeasureTheory.integral_nonneg (fun θ => sq_nonneg _))))
            hInt
            (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi hpt)
      _ = 10 * α ^ 2
            * (∫ z in Set.Ioi (0 : ℝ),
                Work.Spaces.w z * (z * deriv Work.FM.Fstar z) ^ 2) :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ 10 * α ^ 2 * 8 := mul_le_mul_of_nonneg_left FzRadInts.2.2.2 (by positivity)
      _ ≤ 1000 * α ^ 2 := by nlinarith [sq_nonneg α]

end Work.FTS.Nonlinear.Pieces.rl1Tools
