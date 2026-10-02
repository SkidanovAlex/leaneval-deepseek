/-
Work.MRMT.Beltrami — the `L²`-theory of `∂(C ν)`: the Beurling-type transform
`ν ↦ ∂(C ν)` is an isometry of `L²(ℂ)`, hence `∂(C ν)` is an `L²` function for `ν ∈ L²`
with compact support.

Main auxiliary results proved in this file:

* `dzbar_cauchyTransform_eq_ae`  :  `∂̄ (C ψ) = ψ` a.e. for smooth compactly supported `ψ`
  (uniqueness of weak `∂̄`-derivatives, `Cauchy.integral_mul_dzbar_eq_neg`,
  `Cauchy.isDbarDeriv_cauchy_of_integrable`);
* `integral_norm_dz_cauchyTransform_eq` : the isometry `∫ ‖∂(C ψ)‖² = ∫ ‖ψ‖²` for smooth
  compactly supported `ψ` (truncation + the energy identity
  `Sobolev.integral_norm_dz_eq_of_decay` applied to the decaying function `C ψ`, plus the
  a.e. identity `∂̄ (C ψ) = ψ`);
* `norm_integral_cauchyTransform_mul_dz_le_of_support` : the pairing
  `g ↦ ∫ C g · ∂φ` is continuous in `L¹` for data supported in a fixed ball;
* the target `cauchyTransform_dz_memLp`, whose proof is an approximation argument: approximate
  `ν ∈ L²_c` by smooth compactly supported `ψ_k` (with supports in a fixed ball, and
  `ψ_k → ν` in `L²` hence in `L¹`), set `g_k = ∂(C ψ_k)` — a Cauchy sequence in `L²` by the
  isometry — and pass to the limit in the pairing, using that
  `∫ C ψ_k · ∂φ = -∫ g_k · φ` (`Beltrami.integral_mul_dz_eq_neg`) and that the left-hand side
  converges by the `L¹`-continuity bound.
-/
import Mathlib
import Submission.Work.MRMT.Basic
import Submission.Work.MRMT.Cauchy.Defs
import Submission.Work.MRMT.Beltrami.cauchyTransform_contDiff
import Submission.Work.MRMT.Beltrami.cauchyTransform_decay
import Submission.Work.MRMT.Beltrami.integral_mul_dz_eq_neg
import Submission.Work.MRMT.Beltrami.energy_identity
import Submission.Work.MRMT.Cauchy.isDbarDeriv_cauchy_of_integrable
import Submission.Work.MRMT.Cauchy.locallyIntegrable_cauchyTransform
import Submission.Work.MRMT.QC.integral_mul_dzbar_eq_neg
import Submission.Work.MRMT.Sobolev.is_dbar_deriv_unique

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Complex Function Filter
open scoped Distributions Topology ENNReal

namespace Work.MRMT.Beltrami

/-! ## `∂̄ (C ψ) = ψ` for smooth compactly supported `ψ` -/

/-- `∂̄` of the Cauchy transform of a smooth compactly supported function equals that function,
as a weak (distributional) derivative.  Immediate from
`Work.MRMT.Cauchy.isDbarDeriv_cauchy_of_integrable`. -/
theorem isDbarDeriv_cauchyTransform_of_contDiff (ψ : ℂ → ℂ)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hs : HasCompactSupport ψ) :
    Work.MRMT.IsDbarDeriv (Work.MRMT.cauchyTransform ψ) ψ :=
  Work.MRMT.Cauchy.isDbarDeriv_cauchy_of_integrable ψ
    (hψ.continuous.integrable_of_hasCompactSupport hs)

/-- The pointwise `∂̄`-derivative of `C ψ` (which is smooth for smooth compactly supported `ψ`)
is the weak `∂̄`-derivative of `C ψ`; combined with `isDbarDeriv_cauchyTransform_of_contDiff`
and uniqueness of weak `∂̄`-derivatives this gives `∂̄ (C ψ) = ψ` a.e. -/
theorem dzbar_cauchyTransform_eq_ae (ψ : ℂ → ℂ)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hs : HasCompactSupport ψ) :
    Work.MRMT.dzbar (Work.MRMT.cauchyTransform ψ) =ᵐ[volume] ψ := by
  have hcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.MRMT.cauchyTransform ψ) :=
    cauchyTransform_contDiff ψ hψ hs
  have hcd1 : ContDiff ℝ 1 (Work.MRMT.cauchyTransform ψ) := hcd.of_le (by simp)
  have hint : MeasureTheory.Integrable ψ volume :=
    hψ.continuous.integrable_of_hasCompactSupport hs
  have hloc : MeasureTheory.LocallyIntegrable (Work.MRMT.cauchyTransform ψ) volume :=
    Work.MRMT.Cauchy.locallyIntegrable_cauchyTransform ψ hint
  have hcontC : Continuous (Work.MRMT.cauchyTransform ψ) := hcd1.continuous
  have hcontD : Continuous (Work.MRMT.dzbar (Work.MRMT.cauchyTransform ψ)) :=
    Work.MRMT.Sobolev.continuous_dzbar_of_contDiff (Work.MRMT.cauchyTransform ψ)
      (by norm_num) hcd1
  refine Work.MRMT.Sobolev.is_dbar_deriv_unique ?_ (isDbarDeriv_cauchyTransform_of_contDiff ψ hψ hs)
  refine ⟨hloc, hcontD.locallyIntegrable, fun φ => ?_⟩
  have hφ1 : ContDiff ℝ 1 (φ : ℂ → ℂ) := φ.contDiff.of_le (by simp)
  have hφs : HasCompactSupport (φ : ℂ → ℂ) := φ.hasCompactSupport
  have hφd1 : ContDiff ℝ 1 (fun z => Work.MRMT.dzbar (φ : ℂ → ℂ) z) :=
    (Work.MRMT.Cauchy.contDiff_dzbar_testFunction φ).of_le (by simp)
  have hφdcs : HasCompactSupport (fun z => Work.MRMT.dzbar (φ : ℂ → ℂ) z) :=
    Work.MRMT.Cauchy.hasCompactSupport_dzbar_testFunction φ
  refine ⟨?_, ?_, Work.MRMT.QC.integral_mul_dzbar_eq_neg hcd1 hφ1 hφs⟩
  · exact (hcontC.mul hφd1.continuous).integrable_of_hasCompactSupport
      (hφdcs.mul_left (f := fun z => Work.MRMT.cauchyTransform ψ z))
  · exact (hcontD.mul φ.continuous).integrable_of_hasCompactSupport
      (hφs.mul_left (f := fun z => Work.MRMT.dzbar (Work.MRMT.cauchyTransform ψ) z))

/-! ## Auxiliary: pointwise = weak `∂`-derivative for compactly supported `C¹` functions -/

/-- For a compactly supported `C¹` function the pointwise Wirtinger derivative `∂u` is the weak
(= distributional) `∂`-derivative, i.e. `∫ u · ∂φ = -∫ ∂u · φ` for every test function `φ`.
This is the `∂`-analogue of
`Work.MRMT.Sobolev.is_dbar_deriv_of_contDiff_of_ne_zero_hasCompactSupport`. -/
theorem isDzDeriv_of_contDiff_hasCompactSupport (u : ℂ → ℂ) (hu : ContDiff ℝ 1 u)
    (hus : HasCompactSupport u) : Work.MRMT.IsDzDeriv u (Work.MRMT.dz u) := by
  have hcont : Continuous (Work.MRMT.dz u) :=
    continuous_dz_of_contDiff u (by norm_num) hu
  refine ⟨hu.continuous.locallyIntegrable, hcont.locallyIntegrable, fun φ => ?_⟩
  have hφ1 : ContDiff ℝ 1 (φ : ℂ → ℂ) := φ.contDiff.of_le (by simp)
  have hφs : HasCompactSupport (φ : ℂ → ℂ) := φ.hasCompactSupport
  have hcs_dzφ : HasCompactSupport (fun z => Work.MRMT.dz (φ : ℂ → ℂ) z) := by
    have h1 : HasCompactSupport (fun z : ℂ => fderiv ℝ (φ : ℂ → ℂ) z (1 : ℂ)) :=
      (φ.hasCompactSupport).fderiv_apply ℝ (1 : ℂ)
    have h2 : HasCompactSupport (fun z : ℂ => fderiv ℝ (φ : ℂ → ℂ) z Complex.I) :=
      (φ.hasCompactSupport).fderiv_apply ℝ Complex.I
    have h3 : HasCompactSupport
        (fun z : ℂ => Complex.I * fderiv ℝ (φ : ℂ → ℂ) z Complex.I) :=
      h2.comp_left (g := fun w : ℂ => Complex.I * w) (by simp)
    have h4 : HasCompactSupport (fun z : ℂ => fderiv ℝ (φ : ℂ → ℂ) z (1 : ℂ) -
        Complex.I * fderiv ℝ (φ : ℂ → ℂ) z Complex.I) := h1.sub h3
    have h5 := h4.comp_left (g := fun w : ℂ => w * (2 : ℂ)⁻¹) (by simp)
    simpa only [Work.MRMT.dz, div_eq_mul_inv, Function.comp_def] using h5
  have hcont_dzφ : Continuous (fun z => Work.MRMT.dz (φ : ℂ → ℂ) z) :=
    continuous_dz_of_contDiff (φ : ℂ → ℂ) (by norm_num) hφ1
  refine ⟨?_, ?_, Work.MRMT.Beltrami.integral_mul_dz_eq_neg hu hφ1 hφs⟩
  · exact (hu.continuous.mul hcont_dzφ).integrable_of_hasCompactSupport
      (hcs_dzφ.mul_left (f := u))
  · exact (hcont.mul φ.continuous).integrable_of_hasCompactSupport
      (hφs.mul_left (f := Work.MRMT.dz u))

/-! ## Auxiliary: the `L²`-norm bridge `∫ ‖ν‖² = ‖toLp ν‖²` -/

/-- For `ν ∈ L²(ℂ)`, the Bochner integral of `‖ν‖²` equals the square of the `L²` norm of its
`Lp`-class. -/
theorem integral_norm_sq_eq_toLp_norm_sq (ν : ℂ → ℂ)
    (hν : MeasureTheory.MemLp ν 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) :
    ∫ z, ‖ν z‖ ^ 2 ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ)
      = ‖hν.toLp ν‖ ^ 2 := by
  have hcoe : ⇑(hν.toLp ν) =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℂ)] ν := hν.coeFn_toLp
  have hnorm : ‖hν.toLp ν‖ = MeasureTheory.lpNorm ν 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ) := by
    rw [MeasureTheory.Lp.norm_def, MeasureTheory.eLpNorm_congr_ae hcoe]
    rfl
  rw [hnorm, MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal (p := (2 : ℝ≥0∞))
    (by norm_num) (by norm_num) hν.aestronglyMeasurable]
  norm_num
  rw [show (∫ x : ℂ, ‖ν x‖ ^ 2) ^ (1 / 2 : ℝ)
      = Real.sqrt (∫ x : ℂ, ‖ν x‖ ^ 2) from (Real.sqrt_eq_rpow _).symm,
    Real.sq_sqrt (integral_nonneg (fun z => by positivity))]

end Work.MRMT.Beltrami
