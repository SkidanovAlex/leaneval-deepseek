/-
Work.MRMT.Found — the `L¹` bound for the conjugated composite `star ∘ F ∘ f ∘ F.symm`.

Given a `C¹` diffeomorphism `F` with Beltrami relation `∂̄F = μF · ∂F`, an anti-holomorphic
`f` (i.e. `star ∘ f` complex differentiable), a compact set `K` and a bound
`‖∂̄f z‖ ≤ C` on `K`, we bound the `L¹`-size of `∂̄(star ∘ F ∘ f ∘ F.symm)` on `F '' K` by
`C` times the `L¹`-size of the "defect" integrand `‖pullRev μF f − μF‖ · ‖∂F ∘ f‖ · ‖∂F‖`.

The proof combines the change of variables formula `lintegralAbsDbar_comp_eq` (with the
`∂̄`-defect of `star ∘ F ∘ f` computed in `conjAux.dzbar_sub_mul_dz_eq`) with the elementary
estimate `‖conjDen μF f z‖ = ‖∂̄f z‖ ≤ C` coming from anti-holomorphicity of `f`.
-/
import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Found.conjAux
import Submission.Work.MRMT.Found.lintegralAbsDbar_comp_eq
import Submission.Work.MRMT.Found.contDiff_one_of_antiholo

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Filter Topology Complex Function
open scoped Distributions Topology ENNReal

namespace Work.MRMT.Found

/-- Pointwise bound for the Wirtinger defect of `star ∘ F ∘ f`, at a point where `f` is
anti-holomorphic (`∂f z = 0`).  Writing `b = ∂̄f z` one has `conjDen μF f z = star b` and
`conjNum μF f z = star (μF (f z)) * b`; hence either `b = 0`, when both `conjNum` and
`conjDen` vanish, or `conjDen ≠ 0`, when `conjNum = pullRev · conjDen`. -/
private theorem norm_dzbar_conj_sub_mul_dz_le {F f μF : ℂ → ℂ} {z : ℂ} {C : ℝ}
    (hF : DifferentiableAt ℝ F (f z)) (hfd : DifferentiableAt ℝ f z)
    (hrel : dzbar F (f z) = μF (f z) * dz F (f z))
    (hdzf : dz f z = 0) (hCb : ‖dzbar f z‖ ≤ C) :
    ‖dzbar (star ∘ F ∘ f) z - μF z * dz (star ∘ F ∘ f) z‖
      ≤ C * (‖pullRev μF f z - μF z‖ * ‖dz F (f z)‖) := by
  have hden : conjDen μF f z = star (dzbar f z) := by
    simp [conjDen, hdzf]
  rw [dzbar_sub_mul_dz_eq hF hfd hrel]
  by_cases hd : conjDen μF f z = 0
  · -- `conjDen = 0` forces `∂̄f z = 0`, hence `conjNum = 0` too
    have hdbar : dzbar f z = 0 := by
      rw [hden] at hd; simpa using hd
    have hnum0 : conjNum μF f z = 0 := by
      simp [conjNum, hdzf, hdbar]
    have hC0 : 0 ≤ C := le_trans (norm_nonneg _) hCb
    rw [hnum0, hd]
    simp only [mul_zero, sub_zero, norm_zero]
    exact mul_nonneg hC0 (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  · -- `conjDen ≠ 0`: factor out the pull-back coefficient
    have hp : pullRev μF f z * conjDen μF f z = conjNum μF f z := by
      rw [pullRev_eq_div]; exact div_mul_cancel₀ _ hd
    have heq : conjNum μF f z - μF z * conjDen μF f z
        = (pullRev μF f z - μF z) * conjDen μF f z := by
      rw [sub_mul, hp]
    have hcden : ‖conjDen μF f z‖ ≤ C := by
      rw [hden]; simpa using hCb
    rw [heq]
    calc ‖star (dz F (f z)) * ((pullRev μF f z - μF z) * conjDen μF f z)‖
        = ‖dz F (f z)‖ * (‖pullRev μF f z - μF z‖ * ‖conjDen μF f z‖) := by
          simp only [norm_mul, norm_star]
      _ ≤ ‖dz F (f z)‖ * (‖pullRev μF f z - μF z‖ * C) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcden (norm_nonneg _))
            (norm_nonneg _)
      _ = C * (‖pullRev μF f z - μF z‖ * ‖dz F (f z)‖) := by ring

/-- The general form of `lintegralAbsDbar_conj_le`, stated for an arbitrary `C¹`
diffeomorphism `F` satisfying `∂̄F = μF · ∂F`. -/
private theorem lintegralAbsDbar_conj_le_aux {F : ℂ ≃ₜ ℂ} {μF f : ℂ → ℂ}
    (hF : ContDiff ℝ 1 (F : ℂ → ℂ)) (hFs : ContDiff ℝ 1 ((F.symm : ℂ → ℂ)))
    (hrel : ∀ z, dzbar (F : ℂ → ℂ) z = μF z * dz (F : ℂ → ℂ) z)
    (hf : Differentiable ℂ (star ∘ f)) {K : Set ℂ} (hK : IsCompact K) {C : ℝ} (hC : 0 ≤ C)
    (hCb : ∀ z ∈ K, ‖dzbar f z‖ ≤ C) :
    lintegralAbsDbar (star ∘ (F : ℂ → ℂ) ∘ f ∘ (F.symm : ℂ → ℂ)) (F '' K)
      ≤ ENNReal.ofReal C * ∫⁻ z in K, ENNReal.ofReal (‖pullRev μF f z - μF z‖
          * ‖dz (F : ℂ → ℂ) (f z)‖ * ‖dz (F : ℂ → ℂ) z‖) := by
  have hfcd : ContDiff ℝ 1 f := contDiff_one_of_antiholo hf
  have hHcd : ContDiff ℝ 1 (star ∘ (F : ℂ → ℂ) ∘ f) :=
    contDiff_one_star.comp (hF.comp hfcd)
  obtain ⟨C', hLip⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hK
    (hHcd.locallyLipschitz.locallyLipschitzOn (s := K))
  have hcov := lintegralAbsDbar_comp_eq (F := F) (μF := μF) (H := star ∘ (F : ℂ → ℂ) ∘ f)
    (K := K) hK hF hFs hrel C' hLip
  have hcomp : star ∘ (F : ℂ → ℂ) ∘ f ∘ (F.symm : ℂ → ℂ)
      = (star ∘ (F : ℂ → ℂ) ∘ f) ∘ (F.symm : ℂ → ℂ) := rfl
  rw [hcomp, hcov]
  unfold lintegralAbsBeltrami
  have hpt : ∀ z ∈ K, ENNReal.ofReal (‖dzbar (star ∘ (F : ℂ → ℂ) ∘ f) z
        - μF z * dz (star ∘ (F : ℂ → ℂ) ∘ f) z‖ * ‖dz (F : ℂ → ℂ) z‖)
      ≤ ENNReal.ofReal (C * (‖pullRev μF f z - μF z‖ * ‖dz (F : ℂ → ℂ) (f z)‖
          * ‖dz (F : ℂ → ℂ) z‖)) := by
    intro z hz
    apply ENNReal.ofReal_le_ofReal
    have h1 := norm_dzbar_conj_sub_mul_dz_le (F := (F : ℂ → ℂ)) (f := f) (μF := μF)
      (z := z) (C := C) (hF.differentiable (by norm_num) (f z))
      (hfcd.differentiable (by norm_num) z) (hrel (f z))
      (Work.MRMT.Wirtinger.dz_of_antiholo (hf z)) (hCb z hz)
    calc ‖dzbar (star ∘ (F : ℂ → ℂ) ∘ f) z - μF z * dz (star ∘ (F : ℂ → ℂ) ∘ f) z‖
          * ‖dz (F : ℂ → ℂ) z‖
        ≤ (C * (‖pullRev μF f z - μF z‖ * ‖dz (F : ℂ → ℂ) (f z)‖)) * ‖dz (F : ℂ → ℂ) z‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = C * (‖pullRev μF f z - μF z‖ * ‖dz (F : ℂ → ℂ) (f z)‖ * ‖dz (F : ℂ → ℂ) z‖) := by
          ring
  calc ∫⁻ z in K, ENNReal.ofReal (‖dzbar (star ∘ (F : ℂ → ℂ) ∘ f) z
          - μF z * dz (star ∘ (F : ℂ → ℂ) ∘ f) z‖ * ‖dz (F : ℂ → ℂ) z‖)
      ≤ ∫⁻ z in K, ENNReal.ofReal (C * (‖pullRev μF f z - μF z‖ * ‖dz (F : ℂ → ℂ) (f z)‖
          * ‖dz (F : ℂ → ℂ) z‖)) := setLIntegral_mono' hK.measurableSet hpt
    _ = ∫⁻ z in K, ENNReal.ofReal C * ENNReal.ofReal (‖pullRev μF f z - μF z‖
          * ‖dz (F : ℂ → ℂ) (f z)‖ * ‖dz (F : ℂ → ℂ) z‖) := by
        simp_rw [ENNReal.ofReal_mul hC]
    _ = ENNReal.ofReal C * ∫⁻ z in K, ENNReal.ofReal (‖pullRev μF f z - μF z‖
          * ‖dz (F : ℂ → ℂ) (f z)‖ * ‖dz (F : ℂ → ℂ) z‖) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem lintegralAbsDbar_conj_le {μ : ℂ → ℂ} (d : Work.MRMT.Found.PrincipalData μ) {f : ℂ → ℂ}
    (hf : Differentiable ℂ (star ∘ f)) {K : Set ℂ} (hK : IsCompact K) {C : ℝ} (hC : 0 ≤ C)
    (hCb : ∀ z ∈ K, ‖Work.MRMT.dzbar f z‖ ≤ C) (n : ℕ) :
    Work.MRMT.Found.lintegralAbsDbar
        (star ∘ ((d.Fn n) : ℂ → ℂ) ∘ f ∘ ((d.Fn n).symm : ℂ → ℂ)) ((d.Fn n) '' K)
      ≤ ENNReal.ofReal C *
        ∫⁻ z in K, ENNReal.ofReal (‖Work.MRMT.Found.pullRev (d.μn n) f z - d.μn n z‖
          * ‖Work.MRMT.dz ((d.Fn n) : ℂ → ℂ) (f z)‖ * ‖Work.MRMT.dz ((d.Fn n) : ℂ → ℂ) z‖) := by
  exact lintegralAbsDbar_conj_le_aux (F := d.Fn n) (μF := d.μn n) (f := f)
    (d.contDiff_Fn n) (d.contDiff_symm_Fn n) (d.beltrami_Fn n) hf hK hC hCb

end Work.MRMT.Found
