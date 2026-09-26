/-
# The slashed funnel bound transports to the cusp regions of `𝒟`

CKMRV (Cohn--Kumar--Miller--Radchenko--Viazovska, *Universal optimality of the `E₈` and
Leech lattices and interpolation formulas*, Ann. of Math. 196 (2022)) prove the moderate
growth of the `r`-seminorms of the kernel transform on the fundamental domain `𝒟` of `Γ(2)`
by a contour shift.  The four cusps are handled by the four `τ`-slashed kernels
`K^{(d)}|^τ_{d/2}γ` for `γ ∈ {I, S, TS, T⁻¹S}`; the input is the funnel bound

  `(|r|^k) ‖∂_r^l (kernelTransform (slashKernel ℓ d γ) τ ·) r‖ ≤ α (Im τ)^{-β} + γ' ‖τ‖^δ`

on `𝓕 = {τ ∈ 𝒟 : 2 ≤ Im τ}` (CKMRV Lemma 4.12 / the paper's `quotientbounds*`).

This file carries out the elementary transport of that slashed bound to a seminorm bound for
`K^{(d)}` itself on the cusp region

  `cuspRegion γ = {w ∈ ℍ : γ⁻¹ • w ∈ 𝒟 ∧ 2 ≤ (γ⁻¹ • w).im}`,

i.e. the theorem `Work.Asymptotics.seminorm_on_cuspRegion_of_slashed`.  The only ingredients
are the slash law `kernelTransform (slashKernel ℓ d γ) τ = j(γ,τ)^{-d/2} ·
kernelTransform K (γ·τ)` (`Work.Asymptotics.kernelTransform_slashKernel`), the formula
`Im(γ·τ) = Im τ / ‖j(γ,τ)‖²` (`Work.Kernels.im_smul_eq`) and the dichotomy
`γ 1 0 = 0` / `γ 1 0 ≠ 0` for the lower-left entry of `γ`.
-/
import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.FunnelSlashedDefs
import Submission.Work.Asymptotics.CuspRegionDefs

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics

open Work.Kernels

/-- **The `j`-power/imaginary-part bound on a cusp region.**  For the point `w` with
`τ = γ⁻¹ • w`, the product `‖j(γ,τ)‖^{d/2} · (Im τ)^δ` (`d = 8` or `24`, `δ ≥ 0`) is bounded
by `(Im w)^{-(d/2 + δ)} + ‖w‖^δ`.

On the cusp region the two summands correspond to the two possible behaviours of `γ`:

* if `γ 1 0 ≠ 0` then `‖j(γ,τ)‖ ≥ Im τ` and `Im(γ·τ) = Im τ / ‖j(γ,τ)‖²` force
  `Im τ ≤ 1 / Im w`, whence `‖j(γ,τ)‖^{d/2} (Im τ)^δ ≤ (Im w)^{-(d/2+δ)}`;
* if `γ 1 0 = 0` then `j(γ,τ) = γ 1 1 = ±1`, so `‖j(γ,τ)‖ = 1` and `Im τ = Im w`, whence
  `‖j(γ,τ)‖^{d/2} (Im τ)^δ = (Im w)^δ ≤ ‖w‖^δ`. -/
private lemma jpow_im_le (d : ℕ) (hd : d = 8 ∨ d = 24) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (w : UpperHalfPlane) (δ : ℝ) (hδ : 0 ≤ δ) :
    ‖Work.Kernels.jFun γ (((γ⁻¹ • w : UpperHalfPlane) : ℂ))‖^(d/2)
        * ((γ⁻¹ • w : UpperHalfPlane).im)^δ
      ≤ (w.im)^(-(((d/2:ℕ):ℝ) + δ)) + ‖(w:ℂ)‖^δ := by
  set τ : UpperHalfPlane := γ⁻¹ • w with hτdef
  have hw : γ • τ = w := by rw [hτdef, ← mul_smul, mul_inv_cancel, one_smul]
  have hmpos : 0 < w.im := w.im_pos
  have hypos : 0 < τ.im := τ.im_pos
  have hJpos : 0 < ‖Work.Kernels.jFun γ (τ:ℂ)‖ :=
    norm_pos_iff.mpr (Work.Kernels.jFun_ne_zero γ τ)
  have him := Work.Kernels.im_smul_eq γ τ
  rw [hw] at him
  have hJw : w.im * ‖Work.Kernels.jFun γ (τ:ℂ)‖^2 = τ.im :=
    ((div_eq_iff (pow_ne_zero 2 (norm_ne_zero_iff.mpr (Work.Kernels.jFun_ne_zero γ τ)))).mp
      him.symm).symm
  have hJ2 : ‖Work.Kernels.jFun γ (τ:ℂ)‖^2 = τ.im / w.im :=
    (eq_div_iff (ne_of_gt hmpos)).mpr (by rw [mul_comm]; exact hJw)
  have hDnat2 : d/2 = 2*(d/4) := by omega
  by_cases hc : γ 1 0 = 0
  · -- `γ 1 0 = 0`: the automorphy factor is `±1`
    have hJ1 : ‖Work.Kernels.jFun γ (τ:ℂ)‖ = 1 := by
      have hj : Work.Kernels.jFun γ (τ:ℂ) = ((γ 1 1 : ℤ) : ℂ) := by
        rw [Work.Kernels.jFun_apply, hc]; ring
      have hunit : γ 1 1 = 1 ∨ γ 1 1 = -1 := by
        have hdet : ((γ : Matrix (Fin 2) (Fin 2) ℤ).det) = 1 := γ.det_coe
        rw [Matrix.det_fin_two] at hdet
        rw [hc] at hdet
        have h : γ 1 1 * γ 0 0 = 1 := by rw [mul_comm]; linarith [hdet]
        exact Int.eq_one_or_neg_one_of_mul_eq_one h
      rw [hj]
      rcases hunit with h | h <;> rw [h] <;> simp
    have hy_eq : τ.im = w.im := by
      rw [hJ1, one_pow] at hJ2
      exact (div_eq_one_iff_eq (ne_of_gt hmpos)).mp hJ2.symm
    have hmle : w.im ≤ ‖(w:ℂ)‖ := by
      have h : |((w:ℂ)).im| ≤ ‖(w:ℂ)‖ := Complex.abs_im_le_norm _
      rwa [UpperHalfPlane.coe_im, abs_of_pos hmpos] at h
    have hle : w.im^δ ≤ ‖(w:ℂ)‖^δ := Real.rpow_le_rpow hmpos.le hmle hδ
    have hthis : ‖Work.Kernels.jFun γ (τ:ℂ)‖^(d/2) * τ.im^δ = w.im^δ := by
      rw [hJ1, one_pow, hy_eq, one_mul]
    rw [hthis]
    have hnn : 0 ≤ w.im^(-(((d/2:ℕ):ℝ) + δ)) := Real.rpow_nonneg hmpos.le _
    linarith [hle, hnn]
  · -- `γ 1 0 ≠ 0`: `‖j(γ,τ)‖ ≥ Im τ`
    have hgeo : (γ • τ).im ≤ 1 / τ.im := by
      rw [Work.Kernels.im_smul_eq]
      have him2 : (Work.Kernels.jFun γ (τ:ℂ)).im = ((γ 1 0 : ℤ) : ℝ) * τ.im := by
        rw [Work.Kernels.jFun_apply]
        simp [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im]
      have hcabs : (1:ℝ) ≤ |((γ 1 0 : ℤ) : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hc
      have hJ : τ.im ≤ ‖Work.Kernels.jFun γ (τ:ℂ)‖ := by
        have h1 : |(Work.Kernels.jFun γ (τ:ℂ)).im| ≤ ‖Work.Kernels.jFun γ (τ:ℂ)‖ :=
          Complex.abs_im_le_norm _
        rw [him2, abs_mul, abs_of_pos hypos] at h1
        have h2 : τ.im ≤ |((γ 1 0 : ℤ) : ℝ)| * τ.im := by
          calc τ.im = 1 * τ.im := (one_mul _).symm
            _ ≤ |((γ 1 0 : ℤ) : ℝ)| * τ.im := mul_le_mul_of_nonneg_right hcabs hypos.le
        linarith
      rw [div_le_div_iff₀ (pow_pos hJpos 2) hypos]
      nlinarith [hJ, hypos.le]
    have hy_le : τ.im ≤ 1 / w.im := by
      rw [hw] at hgeo
      rw [le_div_iff₀ hypos] at hgeo
      rw [le_div_iff₀ hmpos]
      linarith [hgeo, mul_comm w.im τ.im]
    have hy_m : τ.im * w.im ≤ 1 := (le_div_iff₀ hmpos).mp hy_le
    have h1a : τ.im/w.im ≤ 1/(w.im*w.im) := by
      rw [div_le_div_iff₀ hmpos (by positivity)]
      nlinarith [hy_m, hmpos.le]
    have h1b : (1/(w.im*w.im))^(((d/4:ℕ):ℝ)) = w.im^(-((d/2:ℕ):ℝ)) := by
      rw [one_div, Real.inv_rpow (by positivity : (0:ℝ) ≤ w.im*w.im),
          Real.mul_rpow hmpos.le hmpos.le, ← Real.rpow_add hmpos,
          ← Real.rpow_neg hmpos.le]
      congr 1
      have hcast : ((d/2:ℕ):ℝ) = ((d/4:ℕ):ℝ) + ((d/4:ℕ):ℝ) := by
        rw [hDnat2]; push_cast; ring
      rw [← hcast]
    have h1 : (τ.im/w.im)^(((d/4:ℕ):ℝ)) ≤ w.im^(-((d/2:ℕ):ℝ)) :=
      calc (τ.im/w.im)^(((d/4:ℕ):ℝ))
          ≤ (1/(w.im*w.im))^(((d/4:ℕ):ℝ)) :=
            Real.rpow_le_rpow (div_nonneg hypos.le hmpos.le) h1a (by positivity)
        _ = w.im^(-((d/2:ℕ):ℝ)) := h1b
    have h2 : τ.im^δ ≤ w.im^(-δ) := by
      calc τ.im^δ ≤ (1/w.im)^δ := Real.rpow_le_rpow hypos.le hy_le hδ
        _ = w.im^(-δ) := by rw [one_div, Real.inv_rpow hmpos.le, ← Real.rpow_neg hmpos.le]
    have hJD : ‖Work.Kernels.jFun γ (τ:ℂ)‖^(d/2) = (τ.im/w.im)^(d/4) := by
      rw [hDnat2, pow_mul, hJ2]
    rw [hJD, ← Real.rpow_natCast (τ.im/w.im) (d/4)]
    calc (τ.im/w.im)^(((d/4:ℕ):ℝ)) * τ.im^δ
        ≤ w.im^(-((d/2:ℕ):ℝ)) * w.im^(-δ) :=
          mul_le_mul h1 h2 (Real.rpow_nonneg hypos.le δ) (Real.rpow_nonneg hmpos.le _)
      _ = w.im^(-(((d/2:ℕ):ℝ) + δ)) := by
          rw [← Real.rpow_add hmpos]; congr 1; ring
      _ ≤ w.im^(-(((d/2:ℕ):ℝ) + δ)) + ‖(w:ℂ)‖^δ :=
          le_add_of_nonneg_right (Real.rpow_nonneg (norm_nonneg _) δ)

/-- **The moderate-growth bracket bound on the funnel.**  For `τ ∈ 𝒟` with `2 ≤ Im τ`, the
slashed bound's right-hand side is dominated by `(α + γ' 2^δ) (Im τ)^δ`. -/
private lemma bracket_le (α β γ' δ : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ')
    (hδ : 0 ≤ δ) {τ : UpperHalfPlane} (him : 2 ≤ τ.im) (hnrm : ‖(τ:ℂ)‖ ≤ 2*τ.im) :
    α * (τ.im)^(-β) + γ' * ‖(τ:ℂ)‖^δ ≤ (α + γ'*2^δ) * τ.im^δ := by
  have hy1 : (1:ℝ) ≤ τ.im := by linarith
  have hy0 : (0:ℝ) < τ.im := τ.im_pos
  have hpowβ : τ.im^(-β) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hy1 (by linarith)
  have hpowδ : (1:ℝ) ≤ τ.im^δ := Real.one_le_rpow hy1 hδ
  have hnrmδ : ‖(τ:ℂ)‖^δ ≤ (2*τ.im)^δ :=
    Real.rpow_le_rpow (norm_nonneg _) hnrm hδ
  have h2 : (2*τ.im)^δ = 2^δ * τ.im^δ := Real.mul_rpow (by norm_num) (le_of_lt hy0)
  calc α * (τ.im)^(-β) + γ' * ‖(τ:ℂ)‖^δ
      ≤ α * 1 + γ' * ((2*τ.im)^δ) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hpowβ hα
        · exact mul_le_mul_of_nonneg_left hnrmδ hγ
    _ = α + γ' * (2^δ * τ.im^δ) := by rw [h2]; ring
    _ ≤ α * τ.im^δ + γ' * 2^δ * τ.im^δ := by
        have h3 : α ≤ α * τ.im^δ := le_mul_of_one_le_right hα hpowδ
        nlinarith [h3, hγ, Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) δ, hpowδ]
    _ = (α + γ'*2^δ) * τ.im^δ := by ring

theorem seminorm_on_cuspRegion_of_slashed (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hslashed : ∀ k l : ℕ, ∃ α β γ' δ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ' ∧ 0 ≤ δ ∧
      ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im →
        (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Kernels.kernelTransform (Work.Asymptotics.slashKernel ℓ d γ) τ s) r‖
          ≤ α * (τ.im) ^ (-β) + γ' * (‖(τ : ℂ)‖) ^ δ) :
    ∀ k l : ℕ, ∃ α β γ' δ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ' ∧ 0 ≤ δ ∧
      ∀ (w : UpperHalfPlane) (r : ℝ), w ∈ Work.Asymptotics.cuspRegion γ →
        (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) w s) r‖
          ≤ α * (w.im) ^ (-β) + γ' * (‖(w : ℂ)‖) ^ δ := by
  intro k l
  obtain ⟨α, β, γ', δ, hα, hβ, hγ, hδ, hbound⟩ := hslashed k l
  refine ⟨α + γ'*2^δ, ((d/2:ℕ):ℝ) + δ, α + γ'*2^δ, δ, ?_, ?_, ?_, hδ, ?_⟩
  · exact add_nonneg hα (mul_nonneg hγ (Real.rpow_nonneg (by norm_num) δ))
  · exact add_nonneg (Nat.cast_nonneg _) hδ
  · exact add_nonneg hα (mul_nonneg hγ (Real.rpow_nonneg (by norm_num) δ))
  · intro w r hw
    have hA : 0 ≤ α + γ'*2^δ :=
      add_nonneg hα (mul_nonneg hγ (Real.rpow_nonneg (by norm_num) δ))
    set τ : UpperHalfPlane := γ⁻¹ • w with hτdef
    have hτmem : τ ∈ DomainD ∧ 2 ≤ τ.im := by rw [hτdef]; exact mem_cuspRegion.mp hw
    have hwτ : γ • τ = w := by rw [hτdef, ← mul_smul, mul_inv_cancel, one_smul]
    have hsl := hbound τ r hτmem.1 hτmem.2
    -- the slash law: `kernelTransform K w = j(γ,τ)^{d/2} · kernelTransform (slashKernel) τ`
    have hkey : ∀ s : ℝ, Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) w s
        = (Work.Kernels.jFun γ (τ:ℂ))^(((d/2:ℕ):ℤ))
          * Work.Kernels.kernelTransform (Work.Asymptotics.slashKernel ℓ d γ) τ s := by
      intro s
      have hD : (d : ℤ) / 2 = ((d/2:ℕ):ℤ) := by omega
      have h := Work.Asymptotics.kernelTransform_slashKernel ℓ d γ τ s
      rw [hwτ, hD] at h
      rw [h, ← mul_assoc, ← zpow_add₀ (Work.Kernels.jFun_ne_zero γ τ), add_neg_cancel,
        zpow_zero, one_mul]
    have hid : iteratedDeriv l (fun s : ℝ =>
          Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) w s) r
        = (Work.Kernels.jFun γ (τ:ℂ))^(((d/2:ℕ):ℤ))
          * iteratedDeriv l (fun s : ℝ =>
            Work.Kernels.kernelTransform (Work.Asymptotics.slashKernel ℓ d γ) τ s) r := by
      rw [show (fun s : ℝ => Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) w s)
          = (fun s : ℝ => (Work.Kernels.jFun γ (τ:ℂ))^(((d/2:ℕ):ℤ))
            * Work.Kernels.kernelTransform (Work.Asymptotics.slashKernel ℓ d γ) τ s)
          from funext hkey]
      rw [iteratedDeriv_const_mul_field]
    have hS : (|r|^k) * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) w s) r‖
        = ‖Work.Kernels.jFun γ (τ:ℂ)‖^(d/2)
          * ((|r|^k) * ‖iteratedDeriv l (fun s : ℝ =>
              Work.Kernels.kernelTransform (Work.Asymptotics.slashKernel ℓ d γ) τ s) r‖) := by
      rw [hid, norm_mul, norm_zpow, zpow_natCast]
      ring
    -- the bracket bound
    have hre_abs : |τ.re| ≤ 1 := by
      have h := (mem_DomainD.mp hτmem.1)
      rw [abs_le]
      exact ⟨by linarith [h.1], by linarith [h.2.1]⟩
    have hnrm : ‖(τ:ℂ)‖ ≤ 2*τ.im := by
      have h := Complex.norm_le_abs_re_add_abs_im (τ:ℂ)
      rw [UpperHalfPlane.coe_im, UpperHalfPlane.coe_re, abs_of_pos τ.im_pos] at h
      linarith [h, hre_abs, hτmem.2]
    have hbracket : α * (τ.im)^(-β) + γ' * ‖(τ:ℂ)‖^δ ≤ (α + γ'*2^δ) * τ.im^δ :=
      bracket_le α β γ' δ hα hβ hγ hδ hτmem.2 hnrm
    -- combine with the slashed funnel bound
    have hstep1 : (|r|^k) * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) w s) r‖
        ≤ ‖Work.Kernels.jFun γ (τ:ℂ)‖^(d/2) * ((α + γ'*2^δ) * τ.im^δ) := by
      rw [hS]
      calc ‖Work.Kernels.jFun γ (τ:ℂ)‖^(d/2)
            * ((|r|^k) * ‖iteratedDeriv l (fun s : ℝ =>
                Work.Kernels.kernelTransform (Work.Asymptotics.slashKernel ℓ d γ) τ s) r‖)
          ≤ ‖Work.Kernels.jFun γ (τ:ℂ)‖^(d/2)
              * (α * (τ.im)^(-β) + γ' * ‖(τ:ℂ)‖^δ) :=
            mul_le_mul_of_nonneg_left hsl (by positivity)
        _ ≤ ‖Work.Kernels.jFun γ (τ:ℂ)‖^(d/2) * ((α + γ'*2^δ) * τ.im^δ) :=
            mul_le_mul_of_nonneg_left hbracket (by positivity)
    -- the `j`-power / imaginary-part bound on the cusp region
    have hstep2 : ‖Work.Kernels.jFun γ (τ:ℂ)‖^(d/2) * ((α + γ'*2^δ) * τ.im^δ)
        ≤ (α + γ'*2^δ) * (w.im^(-(((d/2:ℕ):ℝ) + δ)) + ‖(w:ℂ)‖^δ) := by
      rw [hτdef]
      calc ‖Work.Kernels.jFun γ (((γ⁻¹ • w : UpperHalfPlane) : ℂ))‖^(d/2)
            * ((α + γ'*2^δ) * ((γ⁻¹ • w : UpperHalfPlane).im)^δ)
          = (α + γ'*2^δ) * (‖Work.Kernels.jFun γ (((γ⁻¹ • w : UpperHalfPlane) : ℂ))‖^(d/2)
              * ((γ⁻¹ • w : UpperHalfPlane).im)^δ) := by ring
        _ ≤ (α + γ'*2^δ) * (w.im^(-(((d/2:ℕ):ℝ) + δ)) + ‖(w:ℂ)‖^δ) :=
            mul_le_mul_of_nonneg_left (jpow_im_le d hd γ w δ hδ) hA
    calc (|r|^k) * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) w s) r‖
        ≤ (α + γ'*2^δ) * (w.im^(-(((d/2:ℕ):ℝ) + δ)) + ‖(w:ℂ)‖^δ) :=
          le_trans hstep1 hstep2
      _ = (α + γ'*2^δ) * (w.im)^(-(((d/2:ℕ):ℝ) + δ))
            + (α + γ'*2^δ) * (‖(w:ℂ)‖)^δ := by ring

end Work.Asymptotics
