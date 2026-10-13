/-
# `Work.FTS.StrongPersist.L3Rhs.VfsJetMassAux.gamJetMass`

The `γ`-weighted angular mass of the `i`-th angular jet of the profile `Γ/c = VfsGc α`,
`1 ≤ i ≤ 4`, is bounded by `10¹⁵`, uniformly over `α ∈ (0,1]`.

## Route

Writing `X = sin(2θ)`, `γ = γ(α) = 1 + α/10`, the estimate is obtained from three
pointwise ingredients, exactly as in `Work.FTS.StrongPersist.L3Aux.GamJetBounds`:

* **quantitative jet bound.**  `|dthU^[i] (Γ/c)| ≤ α·10⁵·(Γ/c)`; since `VfsGc α = Γ/c` is a
  constant multiple of `Γ`, `dthU^[i] (VfsGc α) = (c α)⁻¹ · dthU^[i] Γ`
  (`Work.Spaces.dthU_iter_const_mul`), and the jet estimate with the factor `α` is
  `Work.Spaces.dthU_iter_Gam_abs_bound` together with the coefficient bound
  `Work.FTS.LocData.Tfun_abs_le`.
* **normalisation.**  `(Γ/c)² ≤ 100 Γ²` on `Iθ` (from `Γ ≤ 1` and `1/10 ≤ c ≤ 10`).
* **vanishing at the endpoints.**  `Γ² X^{-γ} ≤ 2^{-2α/3} X^{17α/30-1}`
  (`Work.FTS.LocData.GamSq_sin_neg_gam_le`), whose exponent `17α/30 - 1 = 2α/3 - γ` lies in
  `(-1, 0]`; `Work.Spaces.sin_two_rpow` then gives `∫ X^{17α/30-1} ≤ 3000/(17α)`.

Combining: the integrand is dominated by `α² · 10¹² · X^{17α/30-1}`, so it is integrable and
its integral is at most `α²·10¹²·3000/(17α) = 10¹²·3000·α/17 ≤ 10¹⁵`.

Note that this module deliberately re-proves the explicit numerical bound rather than
invoking `GamJetBounds`, whose constant is existentially quantified.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.L3Rhs.VfsAngMassDefs
import Submission.Work.FTS.LocData.DthIter_Gam_abs_le
import Submission.Work.Spaces.Gamma_WlInf
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.Gam_bounds
import Submission.Work.Spaces.c_bounds
import Submission.Work.FTS.LocData.angMaj_mem

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs.VfsJetMassAux

set_option autoImplicit false

/-! ## 1. `VfsGc` as a constant multiple of `Γ`, and the jet bound -/

/-- `VfsGc α = Γ/c = (c α)⁻¹ · Γ`, so its `dthU`-iterates are the `dthU`-iterates of `Γ`
scaled by `(c α)⁻¹`. -/
lemma dthU_iter_VfsGc_eq (α : ℝ) (i : ℕ) (θ : ℝ) :
    Work.Spaces.dthU^[i] (VfsGc α) θ
      = (Work.Spaces.c α)⁻¹ * Work.Spaces.dthU^[i] (fun t : ℝ => Work.Spaces.Gam α t) θ := by
  have h : VfsGc α = fun t : ℝ => (Work.Spaces.c α)⁻¹ * Work.Spaces.Gam α t := by
    funext t
    rw [VfsGc, div_eq_inv_mul]
  rw [h, Work.Spaces.dthU_iter_const_mul]

/-- **Quantitative jet bound.**  For `1 ≤ i ≤ 4` and `θ ∈ Iθ`,
`|dthU^[i] (Γ/c)| ≤ α · 10⁵ · (Γ/c)`.  The factor `α` is what makes the subsequent
`γ`-mass estimate uniform in `α`. -/
lemma abs_dthU_iter_VfsGc_le (i : ℕ) (hi1 : 1 ≤ i) (hi4 : i ≤ 4) (α : ℝ) (hα : 0 < α)
    (hα1 : α ≤ 1) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.dthU^[i] (VfsGc α) θ| ≤ α * 100000 * VfsGc α θ := by
  obtain ⟨hc1, hc2⟩ := Work.Spaces.c_bounds α hα hα1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hkey := Work.Spaces.dthU_iter_Gam_abs_bound i hi1 α hα 100000
    (fun θ' _ => Work.FTS.LocData.Tfun_abs_le (i - 1) (by omega) α hα hα1 θ')
  have hb : |Work.Spaces.dthU^[i] (fun t : ℝ => Work.Spaces.Gam α t) θ|
      ≤ α * 100000 * Work.Spaces.Gam α θ := hkey θ hθ
  rw [dthU_iter_VfsGc_eq, abs_mul, abs_of_nonneg (inv_nonneg.mpr hcpos.le), VfsGc,
    div_eq_mul_inv]
  calc (Work.Spaces.c α)⁻¹
        * |Work.Spaces.dthU^[i] (fun t : ℝ => Work.Spaces.Gam α t) θ|
      ≤ (Work.Spaces.c α)⁻¹ * (α * 100000 * Work.Spaces.Gam α θ) :=
        mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hcpos.le)
    _ = α * 100000 * (Work.Spaces.Gam α θ * (Work.Spaces.c α)⁻¹) := by ring

/-- On `Iθ`, `(Γ/c)² ≤ 100 Γ²` for `0 < α ≤ 1`. -/
lemma VfsGc_sq_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (VfsGc α θ) ^ 2 ≤ 100 * Work.Spaces.Gam α θ ^ 2 := by
  obtain ⟨hG0, hG1⟩ := Work.Spaces.Gam_bounds α θ hα hθ
  obtain ⟨hc1, hc2⟩ := Work.Spaces.c_bounds α hα hα1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hinv : (Work.Spaces.c α)⁻¹ ≤ 10 := by
    rw [inv_le_iff_one_le_mul₀ hcpos]
    linarith
  have h2 : ((Work.Spaces.c α)⁻¹) ^ 2 ≤ 100 := by
    have h := pow_le_pow_left₀ (inv_nonneg.mpr hcpos.le) hinv 2
    nlinarith [h]
  rw [VfsGc, div_eq_mul_inv, mul_pow]
  calc Work.Spaces.Gam α θ ^ 2 * (Work.Spaces.c α)⁻¹ ^ 2
      ≤ Work.Spaces.Gam α θ ^ 2 * 100 := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    _ = 100 * Work.Spaces.Gam α θ ^ 2 := by ring

/-! ## 2. The pointwise domination by `α²·10¹²·sin(2θ)^{17α/30-1}` -/

/-- **Pointwise domination of the jet mass.**  For `1 ≤ i ≤ 4`, `0 < α ≤ 1` and `θ ∈ Iθ`,

`(dthU^[i] (Γ/c) θ)² sin(2θ)^{-γ(α)} ≤ α² · 10¹² · sin(2θ)^{17α/30-1}`,

where `17α/30 - 1 = 2α/3 - γ(α) ∈ (-1, 0]`. -/
lemma gamJet_pt_le (i : ℕ) (hi1 : 1 ≤ i) (hi4 : i ≤ 4) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.dthU^[i] (VfsGc α) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ α ^ 2 * 10 ^ 12 * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) := by
  have hX0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
  have hXg : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := Real.rpow_nonneg hX0 _
  have hXp : 0 ≤ (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) := Real.rpow_nonneg hX0 _
  have hjet := abs_dthU_iter_VfsGc_le i hi1 hi4 α hα hα1 hθ
  have hD2 : (Work.Spaces.dthU^[i] (VfsGc α) θ) ^ 2
      ≤ (α * 100000) ^ 2 * (VfsGc α θ) ^ 2 := by
    rw [← sq_abs]
    have h := pow_le_pow_left₀ (abs_nonneg _) hjet 2
    rwa [mul_pow] at h
  have hcx := VfsGc_sq_le α hα hα1 hθ
  have hgs := Work.FTS.LocData.GamSq_sin_neg_gam_le α hα hα1 hθ
  have hstep1 : (Work.Spaces.dthU^[i] (VfsGc α) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ ((α * 100000) ^ 2 * (VfsGc α θ) ^ 2)
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
    mul_le_mul_of_nonneg_right hD2 hXg
  have hstep2 : ((α * 100000) ^ 2 * (VfsGc α θ) ^ 2)
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ ((α * 100000) ^ 2 * (100 * Work.Spaces.Gam α θ ^ 2))
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcx (by positivity)) hXg
  have hstep4 : (α * 100000) ^ 2 * 100 * (Work.Spaces.Gam α θ ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      ≤ (α * 100000) ^ 2 * 100 * (2 ^ (-(2 * α / 3))
        * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1)) :=
    mul_le_mul_of_nonneg_left hgs (by positivity)
  have hbc : (α * 100000) ^ 2 * 100 * 2 ^ (-(2 * α / 3)) ≤ α ^ 2 * 10 ^ 12 := by
    have h2 : (2 : ℝ) ^ (-(2 * α / 3)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith : -(2 * α / 3) ≤ 0)
    calc (α * 100000) ^ 2 * 100 * 2 ^ (-(2 * α / 3))
        ≤ (α * 100000) ^ 2 * 100 * 1 := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = α ^ 2 * 10 ^ 12 := by ring
  calc (Work.Spaces.dthU^[i] (VfsGc α) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ ((α * 100000) ^ 2 * (VfsGc α θ) ^ 2)
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := hstep1
    _ ≤ ((α * 100000) ^ 2 * (100 * Work.Spaces.Gam α θ ^ 2))
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := hstep2
    _ = (α * 100000) ^ 2 * 100 * (Work.Spaces.Gam α θ ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by ring
    _ ≤ (α * 100000) ^ 2 * 100 * (2 ^ (-(2 * α / 3))
        * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1)) := hstep4
    _ = ((α * 100000) ^ 2 * 100 * 2 ^ (-(2 * α / 3)))
        * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) := by ring
    _ ≤ α ^ 2 * 10 ^ 12 * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) :=
        mul_le_mul_of_nonneg_right hbc hXp

/-! ## 3. Measurability -/

/-- `dthU^[m] g` is measurable whenever `g` is: `dthU` multiplies `deriv` by `sin(2·)`, and
`measurable_deriv` is unconditional. -/
lemma measurable_dthU_iter (g : ℝ → ℝ) (hg : Measurable g) (m : ℕ) :
    Measurable (Work.Spaces.dthU^[m] g) := by
  induction m with
  | zero => simpa using hg
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact ((Real.measurable_sin.comp (measurable_const.mul measurable_id))).mul
        (measurable_deriv _)

/-- The integrand of `gamJetMass` is Borel measurable. -/
lemma measurable_gamJet (i : ℕ) (α : ℝ) :
    Measurable (fun θ : ℝ => (Work.Spaces.dthU^[i] (VfsGc α) θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
  have hg : Measurable (VfsGc α) := by
    have hfun : VfsGc α = fun θ : ℝ => Work.Spaces.Gam α θ / Work.Spaces.c α := by
      funext θ
      rw [VfsGc]
    rw [hfun]
    simp only [Work.Spaces.Gam]
    fun_prop
  have hJet : Measurable (Work.Spaces.dthU^[i] (VfsGc α)) := measurable_dthU_iter _ hg i
  have h1 : Measurable (fun θ : ℝ => (Work.Spaces.dthU^[i] (VfsGc α) θ) ^ 2) :=
    hJet.pow_const (2 : ℕ)
  have h2 : Measurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
    have hsin : Measurable (fun θ : ℝ => Real.sin (2 * θ)) := by fun_prop
    exact hsin.pow_const _
  exact h1.mul h2

/-! ## 4. The target -/

theorem gamJetMass (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (i : ℕ) (hi1 : 1 ≤ i) (hi4 : i ≤ 4) :
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.dthU^[i] (Work.FTS.StrongPersist.L3Rhs.VfsGc α) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ ∧
    (∫ θ in Work.Spaces.Iθ, (Work.Spaces.dthU^[i] (Work.FTS.StrongPersist.L3Rhs.VfsGc α) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) ≤ 10 ^ 15 := by
  have hmeasIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  -- The dominating function `α²·10¹²·sin(2θ)^{17α/30-1}` is integrable.
  have hp1 : -1 < 17 * α / 30 - 1 := by linarith
  have hp2 : 17 * α / 30 - 1 ≤ 0 := by linarith
  obtain ⟨hIntS, hBdS⟩ := Work.Spaces.sin_two_rpow (17 * α / 30 - 1) hp1 hp2
  have hBdS' : ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (17 * α / 30 - 1)
      ≤ 3000 / (17 * α) := by
    have heq : 100 / ((17 * α / 30 - 1) + 1) = 3000 / (17 * α) := by field_simp; ring
    rwa [heq] at hBdS
  have hdom : MeasureTheory.IntegrableOn
      (fun θ => α ^ 2 * 10 ^ 12 * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1))
      Work.Spaces.Iθ := hIntS.const_mul _
  -- Pointwise domination on `Iθ`.
  have hpt : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      (Work.Spaces.dthU^[i] (VfsGc α) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        ≤ α ^ 2 * 10 ^ 12 * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) := by
    filter_upwards [MeasureTheory.ae_restrict_mem hmeasIθ] with θ hθ
    exact gamJet_pt_le i hi1 hi4 α hα hα1 hθ
  have hmeas : AEStronglyMeasurable
      (fun θ : ℝ => (Work.Spaces.dthU^[i] (VfsGc α) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) (volume.restrict Work.Spaces.Iθ) :=
    (measurable_gamJet i α).aestronglyMeasurable
  have hIntf : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.dthU^[i] (VfsGc α) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ :=
    hdom.mono' hmeas (by
      filter_upwards [hpt, MeasureTheory.ae_restrict_mem hmeasIθ] with θ h1 h2
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (sin_two_nonneg_Iθ h2) _))]
      exact h1)
  refine ⟨hIntf, ?_⟩
  have hmono := MeasureTheory.integral_mono_ae hIntf hdom hpt
  calc ∫ θ in Work.Spaces.Iθ, (Work.Spaces.dthU^[i] (VfsGc α) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ ∫ θ in Work.Spaces.Iθ,
          α ^ 2 * 10 ^ 12 * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) := hmono
    _ = α ^ 2 * 10 ^ 12
          * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (17 * α / 30 - 1)) := by
        rw [MeasureTheory.integral_const_mul]
    _ ≤ α ^ 2 * 10 ^ 12 * (3000 / (17 * α)) :=
        mul_le_mul_of_nonneg_left hBdS' (by positivity)
    _ = 10 ^ 12 * 3000 * α / 17 := by field_simp
    _ ≤ 10 ^ 15 := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 17)]
        nlinarith [hα1]

end Work.FTS.StrongPersist.L3Rhs.VfsJetMassAux
