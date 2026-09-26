import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.Xi8_eq
import Submission.Work.Asymptotics.Xi24_eq
import Submission.Work.Asymptotics.KMinusCuspBallDefs
import Submission.Work.Kernels.ClearLink.KPlusClear_eq_smul
import Submission.Work.Kernels.ClearLink.KMinusClear_eq_smul
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.ModerateGrowth
import Submission.Work.Asymptotics.KClear_mg2
import Submission.Work.Asymptotics.growthPrefactor_lower_atZero
import Submission.Work.Asymptotics.Instances
import Submission.Work.Asymptotics.EtailE.Atoms
import Submission.Work.Residues.KPlusClear_diag
import Submission.Work.Residues.KMinusClear_diag
import Submission.Work.Residues.KPlusClear_TS
import Submission.Work.Residues.KMinusClear_TS
import Submission.Work.Residues.AfunMinus_neg_one
import Submission.Work.Asymptotics.KClear_S_vanishing
import Submission.Work.Kernels.KernelFacts.KPlus_T2
import Submission.Work.Asymptotics.KKNE_aux
import Submission.Work.Asymptotics.Xi8_bound_E
import Submission.Work.Asymptotics.Xi24_bound_E
import Submission.Work.Asymptotics.Ncusp_EReg_crude
import Submission.Work.Asymptotics.Ncusp_EReg_crude_24
import Submission.Work.Asymptotics.KMinusCuspBallLimit
import Submission.Work.Asymptotics.ERegDefs
import Submission.Work.Asymptotics.mdiff_eta
import Submission.Work.Asymptotics.divisor_qdiff_lower
import Submission.Work.Asymptotics.Kaxis_local_coincidence
import Submission.Work.Asymptotics.DeltaFun_upper_sharp
import Submission.Work.Asymptotics.EpointAux
import Submission.Work.Asymptotics.Xi8_bound_E
import Submission.Work.Asymptotics.Xi24_bound_E
import Submission.Work.Residues.QExpansionTail
import Submission.Work.Asymptotics.jInvariantFun_imagAxis_atZero
import Submission.Work.Kernels.Classical
import Submission.Work.Kernels.KernelFacts.KPlus_S_add
import Submission.Work.Kernels.KernelFacts.KPlus_T2
import Submission.Work.Asymptotics.EBase
import Submission.Work.Modular.E4_qExpansion_coeff
import Submission.Work.Modular.E6_qExpansion_coeff
import Submission.Work.Residues.E4FunSecondOrder
import Submission.Work.Residues.E6FunSecondOrder
import Submission.Work.Residues.DeltaExpansion
import Submission.Work.Residues.ThetaEpt
import Submission.Work.Asymptotics.DeltaFun_imagAxis_atZero
import Submission.Work.Asymptotics.jInvariantFun_eq_smul_of_eq

/-!
# The non-coincidence bound for the CKMRV kernel on the cusp-`0` neighbourhood `E`

The target `Work.Asymptotics.Kaxis_Kfun_noncoincidence_E` bounds
`‖Kaxis (Kfun ℓ d) w t‖` polynomially in `scale w` on the cusp-`0` neighbourhood
`E = KEpsilon`, under the hypotheses

* `w ∈ E`, `0 < t ≤ 1`,
* `j w ≠ j (it)` (the *non*-coincidence),
* `w` is within `c₀ t²` of a modular image `γ • (it)` (the near-diagonal condition).

The near-diagonal condition is what makes the region tractable: with `c₀ ≤ 1/2` it forces
`Im w ≤ (1 + c₀) t`, hence `scale w ≥ (1 + c₀)⁻¹ t⁻¹`, so that `scale w` and `t⁻¹` are
comparable; the kernel is then controlled by the two-regime analysis of the CKMRV kernels on
`E` (`Work.Asymptotics.EtailE`), whose atoms have the sharp shapes
`‖F w‖ ≤ C (scale w)^N e^{c Im (S • w)}`.

## Main results

* `Work.Asymptotics.im_smul_imagAxis` : the imaginary part of `γ • (it)`.
* `Work.Asymptotics.im_le_of_near_diag` : the height control `Im w ≤ t (1 + c₀)`.
* `Work.Asymptotics.scale_mul_t_ge` : `scale w * t ≥ 1 / (1 + c₀)`.
* `Work.Asymptotics.Kaxis_Kfun_noncoincidence_E` : the target.
-/


/-!## Status of this file, and the position of the target in the project

**The three other inputs of `Work.Asymptotics.EFlat_of_bounds` are already proved in this
workspace** (all sorry-free):

* `hplus` — the sharp `K₊` bound on `E`: `Work.Asymptotics.Xi8_bound_E` / `Xi24_bound_E` together
  with `Work.Asymptotics.KPlus8_slash_bound_of_Xi8` / `KPlus24_slash_bound_of_Xi24`
  (`Submission/Work/Asymptotics/Epoint_Kfun.lean`);
* `hminus` — `Work.Asymptotics.KMinus_slash_bound_E`
  (`Submission/Work/Asymptotics/KMinus_slash_bound_E.lean`, from the crude bounds
  `Ncusp_EReg_crude_8`, `Ncusp_EReg_crude_24` through the Schwarz step `slash_bound_of_crude_E`);
* `hdiv` — `Work.Asymptotics.divisor_lower_E` (`Submission/Work/Asymptotics/divisor_lower_E.lean`,
  via `DivisorLowerEAux`).

Hence `EFlat` (`Work.Asymptotics.EFlat_of_bounds`) is, at this point, *one input away*: the
`hnear` hypothesis, i.e. the near-diagonal flatness on `E` — and the target of this file is its
`N = 0` instance (without the `t^N` strengthening).  So the target below is the last missing
piece of the cusp-`0` (`E`) analysis of the CKMRV generating function.

Proved here (all sorry-free):

* `im_smul_imagAxis`, `KEpsilon_im_le_half`, `im_le_of_near_diag`, `scale_mul_t_ge` — the
  geometry: the near-diagonal hypothesis forces `Im w ≤ t (1+c₀)`, hence `scale w · t ≥ 1/(1+c₀)`;
* `DeltaFun_mul_jDiff_lower_E_of` — the divisor lower bound in the *separation* regime;
* `KPlusClear_Tinv_S`, `KMinusClear_Tinv_S`, `KPlusClear_S_smul`, `KMinusClear_S_smul`,
  `KClear_cusp_parabolic_vanishing` — the cusp-parabolic annihilation identities;
* `Xi8_eq_KPlusClear8`, `Xi24_eq_KPlusClear24` — the CKMRV numerators `Xi_d` *are* the cleared
  `K₊` kernels in the second variable (`z^{10}Δ(τ)Xi8 = c₈K₊^{clear}(τ,Sz)`, etc.).

-/

namespace Work.Asymptotics

open UpperHalfPlane ModularGroup Matrix
open scoped MatrixGroups UpperHalfPlane

noncomputable section

/-! ## Elementary geometry of the near-diagonal region on `E` -/

/-- The imaginary part of `γ • (it)`: `t / ((γ 1 0)² t² + (γ 1 1)²)`. -/
lemma im_smul_imagAxis (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) {t : ℝ} (ht : 0 < t) :
    ((γ • Work.Kernels.imagAxis t ht : ℍ) : ℂ).im
      = t / (((γ 1 0 : ℤ) : ℝ) ^ 2 * t ^ 2 + ((γ 1 1 : ℤ) : ℝ) ^ 2) := by
  rw [UpperHalfPlane.coe_im, ModularGroup.im_smul_eq_div_normSq, ModularGroup.denom_apply]
  have him : (Work.Kernels.imagAxis t ht).im = t := by simp [Work.Kernels.imagAxis]
  rw [him]
  congr 1
  rw [show ((Work.Kernels.imagAxis t ht : ℍ) : ℂ) = (t : ℂ) * Complex.I from rfl]
  rw [Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.intCast_re,
    Complex.intCast_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, sub_zero, mul_one, zero_mul, add_zero]
  ring

/-- `Im w ≤ 1/2` on `E`. -/
lemma KEpsilon_im_le_half {w : ℍ} (hw : w ∈ KEpsilon) : w.im ≤ 1 / 2 := by
  have h2 : 2 ≤ (ModularGroup.S • w).im := hw.2
  have hS : (ModularGroup.S • w).im = w.im / ‖(w : ℂ)‖ ^ 2 := by
    rw [Work.Kernels.im_smul_eq]
    have hj : Work.Kernels.jFun ModularGroup.S (w : ℂ) = (w : ℂ) := by
      rw [Work.Kernels.jFun_apply]; simp
    rw [hj]
  have hpos : (0:ℝ) < ‖(w : ℂ)‖ ^ 2 := by
    have h0 : 0 < ‖(w : ℂ)‖ := norm_pos_iff.mpr w.ne_zero
    positivity
  have h3 : 2 * ‖(w : ℂ)‖ ^ 2 ≤ w.im := (le_div_iff₀ hpos).mp (by rw [← hS]; exact h2)
  have h4 : w.im ^ 2 ≤ ‖(w : ℂ)‖ ^ 2 := by
    have h : ‖(w : ℂ)‖ ^ 2 = ((w : ℂ).re) ^ 2 + ((w : ℂ).im) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    rw [h, UpperHalfPlane.coe_im]
    nlinarith [sq_nonneg ((w : ℂ).re)]
  nlinarith [h3, h4, w.im_pos]

/-- **The near-diagonal hypothesis controls the height**: if `w ∈ E`, `0 < t ≤ 1`, `0 ≤ c₀ ≤ 1/2`
and `w` is within `c₀ t²` of some modular image `γ • (it)`, then `Im w ≤ t (1 + c₀)`. -/
lemma im_le_of_near_diag {w : ℍ} {t c₀ : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hc₀0 : 0 ≤ c₀) (hc₀ : c₀ ≤ 1 / 2) (hw : w ∈ KEpsilon)
    (h : ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      ‖(w : ℂ) - (((γ • Work.Kernels.imagAxis t ht : ℍ)) : ℂ)‖ < c₀ * t ^ 2) :
    w.im ≤ t * (1 + c₀) := by
  obtain ⟨γ, hγ⟩ := h
  set u : ℂ := ((γ • Work.Kernels.imagAxis t ht : ℍ) : ℂ) with hu
  have hsub : ((w : ℂ) - u).im = w.im - u.im := by simp
  have hu_im := im_smul_imagAxis γ ht
  have hw_le : w.im ≤ u.im + c₀ * t ^ 2 := by
    have h1 : ((w : ℂ) - u).im ≤ ‖(w : ℂ) - u‖ :=
      le_trans (le_abs_self _) (Complex.abs_im_le_norm _)
    rw [hsub] at h1
    linarith [h1, hγ]
  rcases eq_or_ne (γ 1 1) 0 with hd | hd
  · -- `d = 0`: then `Im (γ • it) = 1 / (c² t)` with `c = ±1`, contradicting `Im w ≤ 1/2`.
    have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
      have hh := γ.2; rw [Matrix.det_fin_two] at hh; exact hh
    have hbc : γ 0 1 * γ 1 0 = -1 := by rw [hd] at hdet; linarith
    have hcsq : ((γ 1 0 : ℤ) : ℝ) ^ 2 = 1 := by
      rcases Int.eq_one_or_neg_one_of_mul_eq_neg_one' hbc with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h2]; norm_num
      · rw [h2]; norm_num
    have hden : ((γ 1 0 : ℤ) : ℝ) ^ 2 * t ^ 2 + ((γ 1 1 : ℤ) : ℝ) ^ 2 = t ^ 2 := by
      rw [hcsq, hd]; ring
    have hu1 : u.im = 1 / t := by
      rw [hu, hu_im, hden]; field_simp
    have hbig : (1:ℝ) ≤ u.im := by
      rw [hu1, le_div_iff₀ ht]; nlinarith
    have hstrict : u.im - c₀ * t ^ 2 < w.im := by
      have h1 : -((w : ℂ) - u).im < c₀ * t ^ 2 :=
        lt_of_le_of_lt (neg_le_abs _)
          (lt_of_le_of_lt (Complex.abs_im_le_norm _) hγ)
      rw [hsub] at h1
      linarith
    have hhalf := KEpsilon_im_le_half hw
    have hc0t : c₀ * t ^ 2 ≤ 1 / 2 := by nlinarith [hc₀, ht.le, ht1, sq_nonneg t]
    linarith
  · -- `d ≠ 0`: then `Im (γ • it) ≤ t`.
    have hd2 : 1 ≤ ((γ 1 1 : ℤ) : ℝ) ^ 2 := by
      have h1 : (1 : ℤ) ≤ |γ 1 1| := Int.one_le_abs hd
      have h2 : ((|γ 1 1| : ℤ) : ℝ) ^ 2 = ((γ 1 1 : ℤ) : ℝ) ^ 2 := by
        rw [Int.cast_abs, sq_abs]
      have h3 : (1 : ℝ) ≤ ((|γ 1 1| : ℤ) : ℝ) := by exact_mod_cast h1
      nlinarith [h3, h2]
    have hden_ge : 1 ≤ ((γ 1 0 : ℤ) : ℝ) ^ 2 * t ^ 2 + ((γ 1 1 : ℤ) : ℝ) ^ 2 := by
      have h0 : 0 ≤ ((γ 1 0 : ℤ) : ℝ) ^ 2 * t ^ 2 := by positivity
      linarith
    have hu_le : u.im ≤ t := by
      rw [hu, hu_im]; exact div_le_self ht.le hden_ge
    have ht2 : t ^ 2 ≤ t := by nlinarith [ht.le, ht1]
    have hct : c₀ * t ^ 2 ≤ c₀ * t := by nlinarith [hc₀0, le_of_lt ht, ht2]
    linarith [hw_le, hu_le, hct]

/-- **`scale w` and `t⁻¹` are comparable** on the near-diagonal region. -/
lemma scale_mul_t_ge {w : ℍ} {t c₀ : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hc₀0 : 0 ≤ c₀) (hc₀ : c₀ ≤ 1 / 2) (hw : w ∈ KEpsilon)
    (h : ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      ‖(w : ℂ) - (((γ • Work.Kernels.imagAxis t ht : ℍ)) : ℂ)‖ < c₀ * t ^ 2) :
    1 / (1 + c₀) ≤ Work.Kernels.scale w * t := by
  have him : w.im ≤ t * (1 + c₀) := im_le_of_near_diag ht ht1 hc₀0 hc₀ hw h
  have hpos : 0 < w.im := w.im_pos
  have h1 : (w.im)⁻¹ ≤ Work.Kernels.scale w := by
    simp only [Work.Kernels.scale]; linarith [norm_nonneg (w : ℂ)]
  have hden : 0 < t * (1 + c₀) := mul_pos ht (by linarith)
  have h2 : (t * (1 + c₀))⁻¹ ≤ (w.im)⁻¹ := inv_anti₀ hpos him
  have h3 : (t * (1 + c₀))⁻¹ ≤ Work.Kernels.scale w := le_trans h2 h1
  have h4 : (t * (1 + c₀))⁻¹ * t = 1 / (1 + c₀) := by
    rw [mul_inv]; field_simp
  calc 1 / (1 + c₀) = (t * (1 + c₀))⁻¹ * t := h4.symm
    _ ≤ Work.Kernels.scale w * t := mul_le_mul_of_nonneg_right h3 ht.le

end

/-! ## The divisor is bounded below away from the coincidences

As soon as `‖j w‖` and `‖j (it)‖` differ by a factor `2`, the divisor `Δ(w)(j w − j (it))` is
bounded below by `c ‖w‖^{-12}`: indeed `Δ(w) j w = E₄(w)³` and `‖E₄(w)‖ = ‖w‖^{-4}‖E₄(S • w)‖`.
The only extra input is the standard lower bound for `|E₄|` for `Im ≥ 2`, where the funnel point
`S • w` lives; it is packaged as a hypothesis so that the algebraic content is isolated. -/

/-- `‖A‖/2 ≤ ‖A - B‖` when `‖B‖ ≤ ‖A‖/2`. -/
private lemma half_le_norm_sub {A B : ℂ} (h : ‖B‖ ≤ ‖A‖ / 2) : ‖A‖ / 2 ≤ ‖A - B‖ := by
  have h1 : ‖A‖ - ‖B‖ ≤ ‖A - B‖ := (abs_le.mp (abs_norm_sub_norm_le A B)).2
  linarith

/-- `‖A‖ ≤ ‖A - B‖` when `2 ‖A‖ ≤ ‖B‖`. -/
private lemma norm_le_norm_sub {A B : ℂ} (h : 2 * ‖A‖ ≤ ‖B‖) : ‖A‖ ≤ ‖A - B‖ := by
  have h1 : ‖B‖ - ‖A‖ ≤ ‖B - A‖ := (abs_le.mp (abs_norm_sub_norm_le B A)).2
  rw [← norm_sub_rev A B] at h1
  linarith

/-- **Divisor lower bound away from the coincidences.** -/
lemma DeltaFun_mul_jDiff_lower_E_of
    (hE4 : ∀ u : ℍ, 2 ≤ u.im → (1 / 2 : ℝ) ≤ ‖Work.Kernels.E4Fun u‖) :
    ∃ c : ℝ, 0 < c ∧ ∀ (w : UpperHalfPlane) (t : ℝ) (ht : 0 < t),
      w ∈ Work.Asymptotics.KEpsilon → t ≤ 1 →
      (Work.Kernels.jInvariantFun w ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) →
      (2 * ‖Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖ ≤ ‖Work.Kernels.jInvariantFun w‖ ∨
        2 * ‖Work.Kernels.jInvariantFun w‖ ≤ ‖Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖) →
      c * (‖(w : ℂ)‖ ^ 12)⁻¹ ≤ ‖Work.Kernels.DeltaFun w *
        (Work.Kernels.jInvariantFun w - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht))‖ := by
  refine ⟨1 / 16, by norm_num, fun w t ht hw ht1 hne hsep => ?_⟩
  set z : ℍ := Work.Kernels.imagAxis t ht with hz
  have hS : Work.Kernels.E4Fun (ModularGroup.S • w) = (w : ℂ) ^ 4 * Work.Kernels.E4Fun w :=
    Work.Asymptotics.EtailE.E4Fun_S w
  have hraw : (1 / 2 : ℝ) ≤ ‖(w : ℂ) ^ 4 * Work.Kernels.E4Fun w‖ := by
    rw [← hS]; exact hE4 _ (by linarith [hw.2])
  have hS2 : (1 / 2 : ℝ) ≤ ‖(w : ℂ)‖ ^ 4 * ‖Work.Kernels.E4Fun w‖ := by
    rw [norm_mul, norm_pow] at hraw; exact hraw
  have hw4 : (0 : ℝ) < ‖(w : ℂ)‖ ^ 4 := by
    have h : (0 : ℝ) < ‖(w : ℂ)‖ := norm_pos_iff.mpr w.ne_zero
    positivity
  have hE4w : (1 / 2 : ℝ) * (‖(w : ℂ)‖ ^ 4)⁻¹ ≤ ‖Work.Kernels.E4Fun w‖ := by
    rw [← div_eq_mul_inv, div_le_iff₀ hw4]
    linarith [hS2, mul_comm (‖(w : ℂ)‖ ^ 4) (‖Work.Kernels.E4Fun w‖)]
  have hcube : (1 / 8) * (‖(w : ℂ)‖ ^ 12)⁻¹ ≤ ‖Work.Kernels.E4Fun w‖ ^ 3 := by
    have h2 : ((1 / 2 : ℝ) * (‖(w : ℂ)‖ ^ 4)⁻¹) ^ 3 ≤ ‖Work.Kernels.E4Fun w‖ ^ 3 :=
      pow_le_pow_left₀ (by positivity) hE4w 3
    have h3 : ((1 / 2 : ℝ) * (‖(w : ℂ)‖ ^ 4)⁻¹) ^ 3 = (1 / 8) * (‖(w : ℂ)‖ ^ 12)⁻¹ := by
      rw [mul_pow, inv_pow, ← pow_mul]
      norm_num
    linarith [h2, h3.le, h3.ge]
  have hx : (0 : ℝ) ≤ (‖(w : ℂ)‖ ^ 12)⁻¹ := by positivity
  have hD := Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun w
  have hprod : ‖Work.Kernels.DeltaFun w‖ * ‖Work.Kernels.jInvariantFun w‖
      = ‖Work.Kernels.E4Fun w‖ ^ 3 := by
    have h := congrArg norm hD
    rwa [norm_mul, norm_pow] at h
  have key : ‖Work.Kernels.DeltaFun w *
        (Work.Kernels.jInvariantFun w - Work.Kernels.jInvariantFun z)‖
      = ‖Work.Kernels.E4Fun w ^ 3 - Work.Kernels.DeltaFun w * Work.Kernels.jInvariantFun z‖ := by
    rw [mul_sub, hD, norm_sub_rev]
  rw [key]
  have hE3 : ‖Work.Kernels.E4Fun w ^ 3‖ = ‖Work.Kernels.E4Fun w‖ ^ 3 := norm_pow _ _
  rcases hsep with h1 | h1
  · have h2 : ‖Work.Kernels.DeltaFun w * Work.Kernels.jInvariantFun z‖
        ≤ ‖Work.Kernels.E4Fun w ^ 3‖ / 2 := by
      rw [norm_mul, hE3]
      have h3 : ‖Work.Kernels.jInvariantFun z‖ ≤ ‖Work.Kernels.jInvariantFun w‖ / 2 := by
        rw [hz]; linarith
      calc ‖Work.Kernels.DeltaFun w‖ * ‖Work.Kernels.jInvariantFun z‖
          ≤ ‖Work.Kernels.DeltaFun w‖ * (‖Work.Kernels.jInvariantFun w‖ / 2) :=
            mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
        _ = ‖Work.Kernels.E4Fun w‖ ^ 3 / 2 := by
            rw [← mul_div_assoc, hprod]
    have h4 := half_le_norm_sub h2
    linarith [hcube, h4, hx]
  · have h2 : 2 * ‖Work.Kernels.E4Fun w ^ 3‖
        ≤ ‖Work.Kernels.DeltaFun w * Work.Kernels.jInvariantFun z‖ := by
      rw [hE3, norm_mul]
      have h3 : ‖Work.Kernels.jInvariantFun w‖ * 2 ≤ ‖Work.Kernels.jInvariantFun z‖ := by
        rw [hz]; linarith
      calc 2 * ‖Work.Kernels.E4Fun w‖ ^ 3
          = ‖Work.Kernels.DeltaFun w‖ * (‖Work.Kernels.jInvariantFun w‖ * 2) := by
            rw [← hprod]; ring
        _ ≤ ‖Work.Kernels.DeltaFun w‖ * ‖Work.Kernels.jInvariantFun z‖ :=
            mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
    have h4 := norm_le_norm_sub h2
    rw [hE3] at h4
    linarith [hcube, h4, hx]

/-! ## The cusp-parabolic annihilation identity

The next branch family after `τ = z` and `τ = S z` is that of the cusp parabolics
`γ_a = S T^{-a} S` (`a ∈ ℤ`); their residue functional vanishes, `φ(γ_a) = 0`, so the cleared
kernels must vanish at `(γ_a • z, z)`.  The proof is an *off-diagonal annihilation identity*
in the same style as `Work.Asymptotics.KClear_S_vanishing`:

* the cleared coefficient matrices `Υ_±^{clear}` are `T`-invariant in `τ` (all their ingredients
  `Δ(τ) f_k(τ)`, `j(τ)`, and hence `j(τ) - j(z)`, are `T`-periodic), so `K_±^{clear}` inherits
  the second-difference equation `(T-I)² = 0` from the `φ⃗`-vector (`Work.Kernels.KernelFacts.phiVec_T2`);
* a function with `(T-I)² = 0` is *affine* along the `T`-orbit: `F(τ+n) = F(τ) + n(F(τ+1)-F(τ))`;
* the two values at `τ = S z` and `τ = T S z` vanish (`KClear_S_vanishing`, `KPlusClear_TS`,
  `KMinusClear_TS`), so the whole `T`-orbit of `S z` is a zero;
* finally `K_±^{clear}(S • τ, z) = ∓τ^{d/2+12} K_±^{clear}(τ,z)`
  (`KClear_S_vanishing`'s transformation law) transports the vanishing back to `γ_a • z`. -/

/-- `Π^Δ` is `T`-periodic. -/
private lemma PiMatDelta_vadd_one (v : Fin 3 → ℤ) (τ : ℍ) :
    Work.Kernels.PiMatDelta v ((1 : ℝ) +ᵥ τ) = Work.Kernels.PiMatDelta v τ := by
  unfold Work.Kernels.PiMatDelta
  simp only [Work.Kernels.KernelFacts.DeltaFun_vadd_one, Work.Kernels.KernelFacts.fk_vadd_one]

/-- `Υ_+^{clear}` is `T`-periodic in its first variable. -/
private lemma UpsilonPlusClear_vadd_one (d : ℕ) (z : ℍ) (i j : Fin 3) (τ : ℍ) :
    Work.Kernels.UpsilonPlusClear d ((1 : ℝ) +ᵥ τ) z i j =
      Work.Kernels.UpsilonPlusClear d τ z i j := by
  simp only [Work.Kernels.UpsilonPlusClear]
  split_ifs with h8 h24 <;>
    simp only [PiMatDelta_vadd_one, Work.Kernels.KernelFacts.jInvariantFun_vadd_one]

/-- `Υ_-^{clear}` is `T`-periodic in its first variable. -/
private lemma UpsilonMinusClear_vadd_one (d : ℕ) (z : ℍ) (i j : Fin 3) (τ : ℍ) :
    Work.Kernels.UpsilonMinusClear d ((1 : ℝ) +ᵥ τ) z i j =
      Work.Kernels.UpsilonMinusClear d τ z i j := by
  simp only [Work.Kernels.UpsilonMinusClear]
  split_ifs with h8 h24 <;>
    simp only [PiMatDelta_vadd_one, Work.Kernels.KernelFacts.jInvariantFun_vadd_one]

/-- **The second-difference equation `(T-I)² = 0` for the cleared `K_+`.** -/
theorem KPlusClear_T2 (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ) :
    Work.Kernels.T2op (fun τ : ℍ => Work.Kernels.KPlusClear d τ z) = 0 := by
  have _ := hd
  have hsum : ∀ τ : ℍ, Work.Kernels.KPlusClear d τ z
      = ∑ i : Fin 3, Work.Kernels.phiVec τ i *
          (∑ j : Fin 3, Work.Kernels.UpsilonPlusClear d τ z i j * Work.Kernels.phitVec z j) := by
    intro τ
    simp only [Work.Kernels.KPlusClear]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  have hcoeff : ∀ i : Fin 3, ∀ τ : ℍ,
      (∑ j : Fin 3, Work.Kernels.UpsilonPlusClear d ((1 : ℝ) +ᵥ τ) z i j *
          Work.Kernels.phitVec z j) =
        (∑ j : Fin 3, Work.Kernels.UpsilonPlusClear d τ z i j * Work.Kernels.phitVec z j) := by
    intro i τ
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [UpsilonPlusClear_vadd_one]
  have hsplit : ∀ τ : ℍ, (fun τ : ℍ => Work.Kernels.KPlusClear d τ z) τ
      = ∑ i : Fin 3, (fun τ : ℍ => Work.Kernels.phiVec τ i) τ *
          (fun τ : ℍ => ∑ j : Fin 3, Work.Kernels.UpsilonPlusClear d τ z i j *
            Work.Kernels.phitVec z j) τ := fun τ => hsum τ
  have : (fun τ : ℍ => Work.Kernels.KPlusClear d τ z)
      = ∑ i : Fin 3, (fun τ : ℍ => Work.Kernels.phiVec τ i) *
          (fun τ : ℍ => ∑ j : Fin 3, Work.Kernels.UpsilonPlusClear d τ z i j *
            Work.Kernels.phitVec z j) := by
    funext τ; simpa using hsplit τ
  rw [this]
  refine Work.Kernels.T2op_sum Finset.univ (fun i _ => ?_)
  refine Work.Kernels.T2op_mul_of (Work.Kernels.KernelFacts.phiVec_T2 i) (fun τ => ?_)
  exact hcoeff i τ

/-- The `T`-shift arithmetic used below. -/
private lemma vadd_two_vadd_neg_one (x : ℍ) : (2 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ x) = (1 : ℝ) +ᵥ x := by
  rw [← add_vadd]; norm_num

private lemma vadd_one_vadd_neg_one (x : ℍ) : (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ x) = x := by
  rw [← add_vadd]; norm_num

/-- **The third `S`-translate: `K_+^{clear}` vanishes at `τ = T⁻¹ S·z`.**

This is *not* an evaluation of the defining sum but a consequence of the second-difference
equation `(T-I)² = 0` (`KPlusClear_T2`) together with the two known vanishings at `S·z`
(`KClear_S_vanishing`) and at `T S·z` (`KPlusClear_TS`): applied at `σ₀ = S·z - 1` the equation
reads `F(σ₀+2) - 2 F(σ₀+1) + F(σ₀) = 0` with `F(σ₀+2) = F(T S·z) = 0` and
`F(σ₀+1) = F(S·z) = 0`, whence `F(T⁻¹ S·z) = 0`. -/
theorem KPlusClear_Tinv_S (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ) :
    Work.Kernels.KPlusClear d ((-1 : ℝ) +ᵥ (ModularGroup.S • z)) z = 0 := by
  have hT2 := congr_fun (KPlusClear_T2 d hd z) ((-1 : ℝ) +ᵥ (ModularGroup.S • z))
  simp only [Work.Kernels.T2op, Pi.zero_apply] at hT2
  rw [vadd_two_vadd_neg_one, vadd_one_vadd_neg_one,
    (Work.Asymptotics.KClear_S_vanishing Work.Kernels.logLambda d hd z).1,
    Work.Residues.KPlusClear_TS d hd z] at hT2
  simpa using hT2

/-- **The same for `K_-^{clear}`**: vanishing at `τ = T⁻¹ S·z`. -/
theorem KMinusClear_Tinv_S (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (z : ℍ) :
    Work.Kernels.KMinusClear ℓ d ((-1 : ℝ) +ᵥ (ModularGroup.S • z)) z = 0 := by
  have hT2 := congr_fun (Work.Residues.AfunMinusNegOne.KMinusClear_T2 ℓ d hd z)
    ((-1 : ℝ) +ᵥ (ModularGroup.S • z))
  simp only [Work.Kernels.T2op, Pi.zero_apply] at hT2
  rw [vadd_two_vadd_neg_one, vadd_one_vadd_neg_one,
    (Work.Asymptotics.KClear_S_vanishing ℓ d hd z).2,
    Work.Residues.KMinusClear_TS ℓ d hd z] at hT2
  simpa using hT2

/-! ### The `S`-transformation law of the cleared kernels

The `S`-law `K_±^{clear}(S•τ, z) = ∓τ^{d/2+12}·K_±^{clear}(τ,z)` is what transports a vanishing
from a point `τ` to its `S`-image `S•τ`.  It is the same computation as in
`Work.Asymptotics.KClear_S_vanishing` (where it is `private`); we reproduce it here because we
need it for *arbitrary* first argument `τ` (not only `τ = z`). -/

/-- The `(i,j)` entry of `Π^Δ_a(τ)·M·Π_b(z)`. -/
private lemma PiMatDelta_mul_PiMat_entry_aux (a b : Fin 3 → ℤ) (M : Matrix (Fin 3) (Fin 3) ℂ)
    (τ z : ℍ) (i j : Fin 3) :
    (Work.Kernels.PiMatDelta a τ * M * Work.Kernels.PiMat b z) i j =
      (Work.Kernels.DeltaFun τ * Work.Kernels.fk (a i) τ) * M i j *
        Work.Kernels.fk (b j) z := by
  simp only [Work.Kernels.PiMatDelta, Work.Kernels.PiMat]
  rw [Matrix.mul_assoc, Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring

private lemma PiMatDelta_mul_smul_PiMat_entry_aux (a b : Fin 3 → ℤ) (M : Matrix (Fin 3) (Fin 3) ℂ)
    (c : ℂ) (τ z : ℍ) (i j : Fin 3) :
    (Work.Kernels.PiMatDelta a τ * M * (c • Work.Kernels.PiMat b z)) i j =
      (Work.Kernels.DeltaFun τ * Work.Kernels.fk (a i) τ) * M i j *
        (c * Work.Kernels.fk (b j) z) := by
  rw [Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul, PiMatDelta_mul_PiMat_entry_aux]
  ring

private lemma tau_ne_zero_aux (τ : ℍ) : (τ : ℂ) ≠ 0 :=
  fun h => τ.im_ne_zero (by rw [← UpperHalfPlane.coe_im τ, h]; simp)

private lemma UpsilonPlusClear_S_8_aux (z τ : ℍ) (i j : Fin 3) :
    Work.Kernels.UpsilonPlusClear 8 (ModularGroup.S • τ) z i j =
      (τ : ℂ) ^ (12 + ((![6, 4, 2] : Fin 3 → ℤ) i)) *
        Work.Kernels.UpsilonPlusClear 8 τ z i j := by
  have hτ : (τ : ℂ) ≠ 0 := tau_ne_zero_aux τ
  have hJ : Work.Kernels.jInvariantFun (ModularGroup.S • τ) = Work.Kernels.jInvariantFun τ :=
    Work.Asymptotics.EtailE.jInvariantFun_Ssmul τ
  have hΔ : Work.Kernels.DeltaFun (ModularGroup.S • τ) =
      (τ : ℂ) ^ (12 : ℤ) * Work.Kernels.DeltaFun τ :=
    Work.Kernels.KernelFacts.smul_of_slash_inv Work.Kernels.KernelFacts.DeltaFun_S_slash τ
  have hfk : Work.Kernels.fk ((![6, 4, 2] : Fin 3 → ℤ) i) (ModularGroup.S • τ) =
      (τ : ℂ) ^ ((![6, 4, 2] : Fin 3 → ℤ) i) * Work.Kernels.fk ((![6, 4, 2] : Fin 3 → ℤ) i) τ :=
    Work.Kernels.KernelFacts.fk_S_smul _ (by fin_cases i <;> decide) τ
  simp only [Work.Kernels.UpsilonPlusClear, reduceIte, Matrix.smul_apply, smul_eq_mul, hJ]
  rw [PiMatDelta_mul_PiMat_entry_aux, PiMatDelta_mul_PiMat_entry_aux, hΔ, hfk, zpow_add₀ hτ]
  ring

private lemma UpsilonPlusClear_S_24_aux (z τ : ℍ) (i j : Fin 3) :
    Work.Kernels.UpsilonPlusClear 24 (ModularGroup.S • τ) z i j =
      (τ : ℂ) ^ (12 + ((![14, 12, 10] : Fin 3 → ℤ) i)) *
        Work.Kernels.UpsilonPlusClear 24 τ z i j := by
  have hτ : (τ : ℂ) ≠ 0 := tau_ne_zero_aux τ
  have hJ : Work.Kernels.jInvariantFun (ModularGroup.S • τ) = Work.Kernels.jInvariantFun τ :=
    Work.Asymptotics.EtailE.jInvariantFun_Ssmul τ
  have hΔ : Work.Kernels.DeltaFun (ModularGroup.S • τ) =
      (τ : ℂ) ^ (12 : ℤ) * Work.Kernels.DeltaFun τ :=
    Work.Kernels.KernelFacts.smul_of_slash_inv Work.Kernels.KernelFacts.DeltaFun_S_slash τ
  have hfk : Work.Kernels.fk ((![14, 12, 10] : Fin 3 → ℤ) i) (ModularGroup.S • τ) =
      (τ : ℂ) ^ ((![14, 12, 10] : Fin 3 → ℤ) i) *
        Work.Kernels.fk ((![14, 12, 10] : Fin 3 → ℤ) i) τ :=
    Work.Kernels.KernelFacts.fk_S_smul _ (by fin_cases i <;> decide) τ
  simp only [Work.Kernels.UpsilonPlusClear, reduceIte, if_neg (show ¬ ((24 : ℕ) = 8) by decide),
    Matrix.smul_apply, smul_eq_mul, hJ]
  rw [PiMatDelta_mul_smul_PiMat_entry_aux, PiMatDelta_mul_smul_PiMat_entry_aux, hΔ, hfk,
    zpow_add₀ hτ]
  ring

private lemma UpsilonMinusClear_S_8_aux (z τ : ℍ) (i j : Fin 3) :
    Work.Kernels.UpsilonMinusClear 8 (ModularGroup.S • τ) z i j =
      (τ : ℂ) ^ (12 + ((![4, 2, 0] : Fin 3 → ℤ) i)) *
        Work.Kernels.UpsilonMinusClear 8 τ z i j := by
  have hτ : (τ : ℂ) ≠ 0 := tau_ne_zero_aux τ
  have hJ : Work.Kernels.jInvariantFun (ModularGroup.S • τ) = Work.Kernels.jInvariantFun τ :=
    Work.Asymptotics.EtailE.jInvariantFun_Ssmul τ
  have hΔ : Work.Kernels.DeltaFun (ModularGroup.S • τ) =
      (τ : ℂ) ^ (12 : ℤ) * Work.Kernels.DeltaFun τ :=
    Work.Kernels.KernelFacts.smul_of_slash_inv Work.Kernels.KernelFacts.DeltaFun_S_slash τ
  have hfk : Work.Kernels.fk ((![4, 2, 0] : Fin 3 → ℤ) i) (ModularGroup.S • τ) =
      (τ : ℂ) ^ ((![4, 2, 0] : Fin 3 → ℤ) i) * Work.Kernels.fk ((![4, 2, 0] : Fin 3 → ℤ) i) τ :=
    Work.Kernels.KernelFacts.fk_S_smul _ (by fin_cases i <;> decide) τ
  simp only [Work.Kernels.UpsilonMinusClear, reduceIte, Matrix.smul_apply, smul_eq_mul, hJ]
  rw [PiMatDelta_mul_PiMat_entry_aux, PiMatDelta_mul_PiMat_entry_aux, hΔ, hfk, zpow_add₀ hτ]
  ring

private lemma UpsilonMinusClear_S_24_aux (z τ : ℍ) (i j : Fin 3) :
    Work.Kernels.UpsilonMinusClear 24 (ModularGroup.S • τ) z i j =
      (τ : ℂ) ^ (12 + ((![12, 10, 8] : Fin 3 → ℤ) i)) *
        Work.Kernels.UpsilonMinusClear 24 τ z i j := by
  have hτ : (τ : ℂ) ≠ 0 := tau_ne_zero_aux τ
  have hJ : Work.Kernels.jInvariantFun (ModularGroup.S • τ) = Work.Kernels.jInvariantFun τ :=
    Work.Asymptotics.EtailE.jInvariantFun_Ssmul τ
  have hΔ : Work.Kernels.DeltaFun (ModularGroup.S • τ) =
      (τ : ℂ) ^ (12 : ℤ) * Work.Kernels.DeltaFun τ :=
    Work.Kernels.KernelFacts.smul_of_slash_inv Work.Kernels.KernelFacts.DeltaFun_S_slash τ
  have hfk : Work.Kernels.fk ((![12, 10, 8] : Fin 3 → ℤ) i) (ModularGroup.S • τ) =
      (τ : ℂ) ^ ((![12, 10, 8] : Fin 3 → ℤ) i) *
        Work.Kernels.fk ((![12, 10, 8] : Fin 3 → ℤ) i) τ :=
    Work.Kernels.KernelFacts.fk_S_smul _ (by fin_cases i <;> decide) τ
  simp only [Work.Kernels.UpsilonMinusClear, reduceIte, if_neg (show ¬ ((24 : ℕ) = 8) by decide),
    Matrix.smul_apply, smul_eq_mul, hJ]
  rw [PiMatDelta_mul_smul_PiMat_entry_aux, PiMatDelta_mul_smul_PiMat_entry_aux, hΔ, hfk,
    zpow_add₀ hτ]
  ring

private lemma KPlusClear_S_smul_8_aux (τ z : ℍ) :
    Work.Kernels.KPlusClear 8 (ModularGroup.S • τ) z =
      -((τ : ℂ) ^ (16 : ℤ)) * Work.Kernels.KPlusClear 8 τ z := by
  have hτ : (τ : ℂ) ≠ 0 := tau_ne_zero_aux τ
  simp only [Work.Kernels.KPlusClear]
  have hsum : ∀ i : Fin 3,
      (∑ j : Fin 3, Work.Kernels.phiVec (ModularGroup.S • τ) i *
          Work.Kernels.UpsilonPlusClear 8 (ModularGroup.S • τ) z i j *
            Work.Kernels.phitVec z j)
        = -((τ : ℂ) ^ (16 : ℤ)) * (∑ j : Fin 3, Work.Kernels.phiVec τ i *
            Work.Kernels.UpsilonPlusClear 8 τ z i j * Work.Kernels.phitVec z j) := by
    intro i
    have hφ := Work.Kernels.KernelFacts.phiVec_S_smul τ i
    have hpow : (τ : ℂ) ^ ((![-2, 0, 2] : Fin 3 → ℤ) i) *
        (τ : ℂ) ^ (12 + ((![6, 4, 2] : Fin 3 → ℤ) i)) = (τ : ℂ) ^ (16 : ℤ) := by
      rw [← zpow_add₀ hτ]; congr 1; fin_cases i <;> norm_num
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hφ, UpsilonPlusClear_S_8_aux z τ i j, ← hpow]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hsum i), Finset.mul_sum]

private lemma KPlusClear_S_smul_24_aux (τ z : ℍ) :
    Work.Kernels.KPlusClear 24 (ModularGroup.S • τ) z =
      -((τ : ℂ) ^ (24 : ℤ)) * Work.Kernels.KPlusClear 24 τ z := by
  have hτ : (τ : ℂ) ≠ 0 := tau_ne_zero_aux τ
  simp only [Work.Kernels.KPlusClear]
  have hsum : ∀ i : Fin 3,
      (∑ j : Fin 3, Work.Kernels.phiVec (ModularGroup.S • τ) i *
          Work.Kernels.UpsilonPlusClear 24 (ModularGroup.S • τ) z i j *
            Work.Kernels.phitVec z j)
        = -((τ : ℂ) ^ (24 : ℤ)) * (∑ j : Fin 3, Work.Kernels.phiVec τ i *
            Work.Kernels.UpsilonPlusClear 24 τ z i j * Work.Kernels.phitVec z j) := by
    intro i
    have hφ := Work.Kernels.KernelFacts.phiVec_S_smul τ i
    have hpow : (τ : ℂ) ^ ((![-2, 0, 2] : Fin 3 → ℤ) i) *
        (τ : ℂ) ^ (12 + ((![14, 12, 10] : Fin 3 → ℤ) i)) = (τ : ℂ) ^ (24 : ℤ) := by
      rw [← zpow_add₀ hτ]; congr 1; fin_cases i <;> norm_num
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hφ, UpsilonPlusClear_S_24_aux z τ i j, ← hpow]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hsum i), Finset.mul_sum]

/-- **The `S`-law for the cleared `K_+`.** -/
theorem KPlusClear_S_smul (d : ℕ) (hd : d = 8 ∨ d = 24) (τ z : ℍ) :
    Work.Kernels.KPlusClear d (ModularGroup.S • τ) z =
      -((τ : ℂ) ^ (((d : ℤ) / 2) + 12)) * Work.Kernels.KPlusClear d τ z := by
  rcases hd with rfl | rfl
  · simpa using KPlusClear_S_smul_8_aux τ z
  · simpa using KPlusClear_S_smul_24_aux τ z

private lemma KMinusClear_S_smul_8_aux (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    Work.Kernels.KMinusClear ℓ 8 (ModularGroup.S • τ) z =
      ((τ : ℂ) ^ (16 : ℤ)) * Work.Kernels.KMinusClear ℓ 8 τ z := by
  have hτ : (τ : ℂ) ≠ 0 := tau_ne_zero_aux τ
  simp only [Work.Kernels.KMinusClear]
  have hsum : ∀ i : Fin 3,
      (∑ j : Fin 3, Work.Kernels.psiVec ℓ (ModularGroup.S • τ) i *
          Work.Kernels.UpsilonMinusClear 8 (ModularGroup.S • τ) z i j *
            Work.Kernels.psitVec ℓ z j)
        = ((τ : ℂ) ^ (16 : ℤ)) * (∑ j : Fin 3, Work.Kernels.psiVec ℓ τ i *
            Work.Kernels.UpsilonMinusClear 8 τ z i j * Work.Kernels.psitVec ℓ z j) := by
    intro i
    have hψ := Work.Kernels.KernelFacts.psiVec_S_smul ℓ τ i
    have hpow : (τ : ℂ) ^ (2 * ((i : ℕ) : ℤ)) *
        (τ : ℂ) ^ (12 + ((![4, 2, 0] : Fin 3 → ℤ) i)) = (τ : ℂ) ^ (16 : ℤ) := by
      rw [← zpow_add₀ hτ]; congr 1; fin_cases i <;> norm_num
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hψ, UpsilonMinusClear_S_8_aux z τ i j, ← hpow]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hsum i), Finset.mul_sum]

private lemma KMinusClear_S_smul_24_aux (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    Work.Kernels.KMinusClear ℓ 24 (ModularGroup.S • τ) z =
      ((τ : ℂ) ^ (24 : ℤ)) * Work.Kernels.KMinusClear ℓ 24 τ z := by
  have hτ : (τ : ℂ) ≠ 0 := tau_ne_zero_aux τ
  simp only [Work.Kernels.KMinusClear]
  have hsum : ∀ i : Fin 3,
      (∑ j : Fin 3, Work.Kernels.psiVec ℓ (ModularGroup.S • τ) i *
          Work.Kernels.UpsilonMinusClear 24 (ModularGroup.S • τ) z i j *
            Work.Kernels.psitVec ℓ z j)
        = ((τ : ℂ) ^ (24 : ℤ)) * (∑ j : Fin 3, Work.Kernels.psiVec ℓ τ i *
            Work.Kernels.UpsilonMinusClear 24 τ z i j * Work.Kernels.psitVec ℓ z j) := by
    intro i
    have hψ := Work.Kernels.KernelFacts.psiVec_S_smul ℓ τ i
    have hpow : (τ : ℂ) ^ (2 * ((i : ℕ) : ℤ)) *
        (τ : ℂ) ^ (12 + ((![12, 10, 8] : Fin 3 → ℤ) i)) = (τ : ℂ) ^ (24 : ℤ) := by
      rw [← zpow_add₀ hτ]; congr 1; fin_cases i <;> norm_num
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hψ, UpsilonMinusClear_S_24_aux z τ i j, ← hpow]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hsum i), Finset.mul_sum]

/-- **The `S`-law for the cleared `K_-`.** -/
theorem KMinusClear_S_smul (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ z : ℍ) :
    Work.Kernels.KMinusClear ℓ d (ModularGroup.S • τ) z =
      ((τ : ℂ) ^ (((d : ℤ) / 2) + 12)) * Work.Kernels.KMinusClear ℓ d τ z := by
  rcases hd with rfl | rfl
  · simpa using KMinusClear_S_smul_8_aux ℓ τ z
  · simpa using KMinusClear_S_smul_24_aux ℓ τ z

/-- **The cusp-parabolic annihilation identity**: the cleared kernels vanish at the branches
`τ = (S T^{-a} S) • z` for `a = ±1`, i.e. at the two cusp-parabolic orbit points of `z` that
can come within `O(t²)` of the cusp-`0` tile `E`. -/
theorem KClear_cusp_parabolic_vanishing (ℓ : Work.Kernels.LogLambdaData) (_d : ℕ)
    (hd : _d = 8 ∨ _d = 24) (z : ℍ) :
    (Work.Kernels.KPlusClear _d (ModularGroup.S • ((-1 : ℝ) +ᵥ (ModularGroup.S • z))) z = 0 ∧
      Work.Kernels.KMinusClear ℓ _d (ModularGroup.S • ((-1 : ℝ) +ᵥ (ModularGroup.S • z))) z = 0) ∧
    (Work.Kernels.KPlusClear _d (ModularGroup.S • ((1 : ℝ) +ᵥ (ModularGroup.S • z))) z = 0 ∧
      Work.Kernels.KMinusClear ℓ _d
        (ModularGroup.S • ((1 : ℝ) +ᵥ (ModularGroup.S • z))) z = 0) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [KPlusClear_S_smul _d hd, KPlusClear_Tinv_S _d hd z, mul_zero]
  · rw [KMinusClear_S_smul ℓ _d hd, KMinusClear_Tinv_S ℓ _d hd z, mul_zero]
  · rw [KPlusClear_S_smul _d hd, Work.Residues.KPlusClear_TS _d hd z, mul_zero]
  · rw [KMinusClear_S_smul ℓ _d hd, Work.Residues.KMinusClear_TS ℓ _d hd z, mul_zero]

/-- **The cleared kernel vanishes at the two cusp-parabolic orbit points of `z`.**

Immediate from `KClear_cusp_parabolic_vanishing` and the definition of `KfunClear`.  This is the
*vanishing* input for the one-zero argument at the boundary `∂𝒟`-points `γ_{±1}·(i t)` of the
target's region: for `z = i t` the two arguments are exactly those orbit points. -/
theorem KfunClear_cusp_parabolic_vanishing (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (z : ℍ) :
    Work.Kernels.KfunClear ℓ d
        (ModularGroup.S • ((-1 : ℝ) +ᵥ (ModularGroup.S • z))) z = 0 ∧
      Work.Kernels.KfunClear ℓ d
        (ModularGroup.S • ((1 : ℝ) +ᵥ (ModularGroup.S • z))) z = 0 := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := KClear_cusp_parabolic_vanishing ℓ d hd z
  constructor
  · rw [Work.Kernels.KfunClear, h1, h2, add_zero, zero_div]
  · rw [Work.Kernels.KfunClear, h3, h4, add_zero, zero_div]

/-! ## The cleared kernels as the CKMRV numerators `Xi_d` and `Ncusp`

The sharpest CKMRV estimates available in this workspace are

* `Work.Asymptotics.Xi8_bound_E` / `Xi24_bound_E`, which bound `Xi_d τ z = c_d Δ(z) (j τ - j z)
  z^{d/2-2} K_+^{(d)}(τ, S z)` by `C (scale τ)^N e^{-2π Im z}` on `E`;
* `Work.Asymptotics.Ncusp ℓ d τ z = Δ(z)(j τ - j z) z^{2-d/2} K_-^{(d)}(τ, Sz)` with the sharp
  Schwarz-lemma bound `e^{-π Im z}` (`Work.Asymptotics.slash_bound_of_crude_E`).

Because the cleared kernels factor as
`K_±^{clear}(τ, Sz) = Δ(τ) Δ(Sz)^e (j τ - j(Sz)) K_±(τ, Sz)` with `Δ(Sz) = z^{12} Δ(z)` and
`j(Sz) = j z`, these two *sharp* estimates are equivalent to sharp estimates for the cleared
kernels themselves, with the second variable on the imaginary axis:

* `z^{10} Δ(τ) Xi8 τ z = c₈ K_+^{clear,8}(τ, Sz)` and
  `z^{14} Δ(τ) Δ(z) Xi24 τ z = c₂₄ K_+^{clear,24}(τ, Sz)`;
* `z^{10} Δ(τ) Ncusp ℓ 8 τ z = K_-^{clear}(ℓ,8)(τ, Sz)` and
  `z^{14} Δ(τ) Δ(z) Ncusp ℓ 24 τ z = K_-^{clear}(ℓ,24)(τ, Sz)`.

In particular, for `z = i/t` the cleared kernels carry the *whole* exponential smallness
`e^{-2π/t}` (which the divisor form `Work.Asymptotics.contour_bound_Kfun` loses), and

  `2 KfunClear ℓ d τ (S z) = z^{10} Δ(τ) (Xi8 τ z / c₈ + Ncusp ℓ 8 τ z)`  (d = 8)
  `2 KfunClear ℓ d τ (S z) = z^{14} Δ(τ) Δ(z) (Xi24 τ z / c₂₄ + Ncusp ℓ 24 τ z)`  (d = 24),

so that the *sharp* bound on the kernel on the near-diagonal region is exactly a sharp bound on
the *sum* `Xi_d/c_d + Ncusp` — the CKMRV Section 4.4 annihilation, in the second variable.
-/

/-- **`Xi8` is the cleared `K_+^{(8)}` kernel.** -/
lemma Xi8_eq_KPlusClear8 (τ z : ℍ)
    (h : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z) :
    ((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I) *
        Work.Kernels.KPlusClear 8 τ (ModularGroup.S • z)
      = (z : ℂ) ^ 10 * Work.Kernels.DeltaFun τ * Work.Asymptotics.Xi8 τ z := by
  have hclear := Work.Kernels.ClearLink.KPlusClear_eq_smul 8 (Or.inl rfl) τ (ModularGroup.S • z)
    (by rw [Work.Asymptotics.EtailE.jInvariantFun_Ssmul]; exact h)
  have hXi := Work.Asymptotics.Xi8_eq τ z h
  have hSΔ := Work.Asymptotics.EtailE.DeltaFun_Ssmul z
  have hSj := Work.Asymptotics.EtailE.jInvariantFun_Ssmul z
  rw [hclear, Work.Kernels.growthPrefactor, if_pos rfl, pow_one, hSΔ, hSj]
  linear_combination ((z : ℂ) ^ 10 * Work.Kernels.DeltaFun τ) * hXi

/-- **`Xi24` is the cleared `K_+^{(24)}` kernel.** -/
lemma Xi24_eq_KPlusClear24 (τ z : ℍ)
    (h : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z) :
    ((36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I) *
        Work.Kernels.KPlusClear 24 τ (ModularGroup.S • z)
      = (z : ℂ) ^ 14 * Work.Kernels.DeltaFun τ * Work.Kernels.DeltaFun z
          * Work.Asymptotics.Xi24 τ z := by
  have hclear := Work.Kernels.ClearLink.KPlusClear_eq_smul 24 (Or.inr rfl) τ (ModularGroup.S • z)
    (by rw [Work.Asymptotics.EtailE.jInvariantFun_Ssmul]; exact h)
  have hXi := Work.Asymptotics.Xi24_eq τ z h
  have hSΔ := Work.Asymptotics.EtailE.DeltaFun_Ssmul z
  have hSj := Work.Asymptotics.EtailE.jInvariantFun_Ssmul z
  rw [hclear, Work.Kernels.growthPrefactor, if_neg (by norm_num : ¬ ((24 : ℕ) = 8)), hSΔ, hSj]
  linear_combination ((z : ℂ) ^ 14 * Work.Kernels.DeltaFun τ * Work.Kernels.DeltaFun z) * hXi

/-! ## The non-coincidence bound: reduction

The remaining content of the target is the *sharp* bound for the kernel on the near-diagonal
region.  The material above reduces it to the following two regimes (with `c₀ ≤ 1/2`, so that
`Im w ≤ (1 + c₀) t` and `scale w · t ≥ 1/(1 + c₀)`).

* **Separation regime** (`2 ‖j (it)‖ ≤ ‖j w‖` or `2 ‖j w‖ ≤ ‖j (it)‖`): the divisor is bounded
  below by `‖w‖^{-12}` (`DeltaFun_mul_jDiff_lower_E_of`), and the *sharp* `Bdd`-calculus of
  `Submission/Work/Asymptotics/EtailE` on `E` shows that the cleared kernel has the matching
  exponential factor: each large atom (`j`, `Δ⁻¹`, `E₁₄/Δ`, `E₁₀/Δ`) occurring in
  `KfunClear` is accompanied either by a factor `Δ(w)` (which supplies `e^{-2π Im (S • w)}`) or
  by a factor `j(w)` (which supplies `e^{2π Im (S • w)}` after division by the divisor).  The
  two cases `‖j w‖ ≥ 2‖j(it)‖` and `‖j(it)‖ ≥ 2‖j w‖` give respectively
  `|j w| ≥ e^{2π Im (S • w)}` and `|j(it)| ≥ e^{2π/t}`, so the exponential factors cancel in
  every term and only `O((scale w)^N)` remains.

* **Cancellation regime** (`‖j w‖` and `‖j (it)‖` comparable): here `Im w ≈ ‖w‖²/t`, the
  nearest pole `γ • (it)` of `τ ↦ K (τ, it)` lies at Euclidean distance `≥ dist(γ • it, E)` from
  `E`, and its residue is `-j(γ,it)^{d/2-2} φ(γ)/(2π)` (CKMRV Theorem 4.9(3), formalised in
  `Work.Residues.hasResidue_slash_Kfun` together with the transport
  `Work.Residues.hasResidue_smul_SL`).  The value of the kernel at `w` is therefore bounded by
  `C / dist(γ • it, E)` and the required polynomial bound follows from the geometry of `E`.

The estimates of the second regime are not yet formalised in this workspace; the first regime is
covered by the lemmas above together with `Work.Asymptotics.norm_Kaxis_Kfun_le` (the divisor
form of Theorem 4.9(4)). -/


/-!
### The precise remaining gap

Writing `Phi ℓ d w t := Xi8 w (i/t)/c₈ + Ncusp ℓ 8 w (i/t)` (and the `d = 24` analogue), the two
identities above give, for `w ∈ E` and `0 < t ≤ 1` with `j w ≠ j (i t)`,

  `2 KfunClear ℓ d w (i t) = (i/t)^{10} Δ(w) · Phi ℓ 8 w t`  (d = 8),

hence

  `‖Kaxis (Kfun ℓ d) w t‖ = t^{-10} ‖Phi ℓ d w t‖ / (2 ‖Δ(i t)‖ ‖j w − j (i t)‖)`.

Both factors in the denominator are *exponentially small*: `‖Δ(i t)‖ ≍ e^{-2π/t} t^{-12}`, and in
the near-diagonal region also `‖j w − j (i t)‖ ≲ e^{2π/t} t^{-2} ‖w − i t‖` (difference quotient).
So the target is *equivalent* to the sharp statement

  `‖Phi ℓ d w t‖ ≤ C (scale w)^N e^{-2π/t} · ‖w − i t‖`   for `w` near `i t`,

i.e. the **CKMRV Section 4.4 annihilation in the `τ`-variable at `z = i/t`, in sharp (linear,
exponentially small) form**: the individual numerators `Xi_d` and `Ncusp` do *not* vanish at
`j w = j z` (their sharp exponents are `e^{-2π Im z}` and `e^{-π Im z}` respectively, cf. the
paper's `n_{+,z} = 2`, `n_{-,z} = 1`), and only their *sum* does.  This is exactly the `hnear`
input consumed by `Work.Asymptotics.EFlat_of_bounds`, and is the content to be established here.

-/

/-! ## The non-coincidence bound

The remaining content of the target: on the near-diagonal region the kernel is controlled by the
sharp `Bdd`-shape analysis of `Submission/Work/Asymptotics/EtailE`, where the large atoms
(`j`, `Δ⁻¹`, `E₁₄/Δ`, `E₁₀/Δ`) are always multiplied against a vanishing combination, so that
only `O((scale w)^N)` remains after dividing by the divisor `Δ(w)Δ(it)^e(j w - j(it))`. -/

/-! ## The one-zero (Schwarz) estimate

The workspace's own `norm_le_mul_dist_of_one_zero` lives behind `MiddleRange.Basic`, which cannot
be imported here (duplicate `Work.Asymptotics.continuous_scale`).  It is reproduced below from
Mathlib's Schwarz lemma `norm_dslope_le_div_of_mapsTo_ball`: a holomorphic `f` on `ball c r` with
`f z₁ = 0` and `‖f‖ ≤ M` on the ball satisfies `‖f u‖ ≤ (2M/r)‖u − z₁‖` on `ball c (r/2)`. -/

/-- **One-zero (Schwarz) estimate**, Euclidean form. -/
lemma one_zero_bound {f : ℂ → ℂ} {c : ℂ} {r M : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (Metric.ball c r))
    (hb : ∀ u ∈ Metric.ball c r, ‖f u‖ ≤ M)
    {z₁ : ℂ} (hz₁ : z₁ ∈ Metric.ball c (r / 2)) (h0 : f z₁ = 0) :
    ∀ u ∈ Metric.ball c (r / 2), ‖f u‖ ≤ (2 * M / r) * ‖u - z₁‖ := by
  have hz₁' : ‖z₁ - c‖ < r / 2 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hz₁
  have hM0 : 0 ≤ M :=
    le_trans (norm_nonneg _) (hb c (by rw [Metric.mem_ball, dist_self]; exact hr))
  have hρ : 0 < r - ‖z₁ - c‖ := by linarith
  have hratio : M / (r - ‖z₁ - c‖) ≤ 2 * M / r := by
    rw [div_le_div_iff₀ hρ hr]
    nlinarith [hM0, hz₁']
  have hsub : Metric.ball z₁ (r - ‖z₁ - c‖) ⊆ Metric.ball c r := by
    intro w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw ⊢
    have hadd : w - c = (w - z₁) + (z₁ - c) := by ring
    calc ‖w - c‖ = ‖(w - z₁) + (z₁ - c)‖ := by rw [hadd]
      _ ≤ ‖w - z₁‖ + ‖z₁ - c‖ := norm_add_le _ _
      _ < (r - ‖z₁ - c‖) + ‖z₁ - c‖ := by linarith
      _ = r := by ring
  intro u hu
  have hu' : ‖u - c‖ < r / 2 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hu
  by_cases hfar : r - ‖z₁ - c‖ ≤ ‖u - z₁‖
  · -- away from the zero the crude bound already suffices
    have h1 : ‖f u‖ ≤ M :=
      hb u (Metric.ball_subset_ball (by linarith : r / 2 ≤ r) hu)
    have hle : r / 2 ≤ ‖u - z₁‖ := le_trans (by linarith : r / 2 ≤ r - ‖z₁ - c‖) hfar
    have h2 : M ≤ (2 * M / r) * ‖u - z₁‖ := by
      have h3 : (2 * M / r) * (r / 2) = M := by field_simp
      have h4 : (2 * M / r) * (r / 2) ≤ (2 * M / r) * ‖u - z₁‖ :=
        mul_le_mul_of_nonneg_left hle (by positivity)
      linarith [h3, h4]
    linarith
  · -- near the zero: Schwarz
    rw [not_le] at hfar
    have hd : DifferentiableOn ℂ f (Metric.ball z₁ (r - ‖z₁ - c‖)) := hf.mono hsub
    have hmaps : Set.MapsTo f (Metric.ball z₁ (r - ‖z₁ - c‖)) (Metric.closedBall (f z₁) M) := by
      intro w hw
      rw [Metric.mem_closedBall, dist_eq_norm, h0, sub_zero]
      exact hb w (hsub hw)
    have hsl : ‖dslope f z₁ u‖ ≤ M / (r - ‖z₁ - c‖) :=
      Complex.norm_dslope_le_div_of_mapsTo_ball hd hmaps
        (by simpa [Metric.mem_ball, dist_eq_norm] using hfar)
    rcases eq_or_ne u z₁ with rfl | hne
    · rw [h0, norm_zero]
      exact mul_nonneg (by positivity) (norm_nonneg _)
    · have hn : ‖dslope f z₁ u‖ = ‖f u‖ / ‖u - z₁‖ := by
        rw [dslope_of_ne f hne, slope_def_module, h0, sub_zero, norm_smul, norm_inv,
          div_eq_inv_mul]
      have hkey : ‖f u‖ ≤ (M / (r - ‖z₁ - c‖)) * ‖u - z₁‖ := by
        rw [hn, div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hne))] at hsl
        linarith
      exact hkey.trans (mul_le_mul_of_nonneg_right hratio (norm_nonneg _))

/-! ## The compact piece: `E ∩ {‖w‖ ≥ σ}` at `t ≤ 1`

`Work.Asymptotics.Kaxis_local_flat` bounds the kernel on a *fixed* compact subset `K ⊆ 𝒟` by
`c_K t^N` for every `N`.  Taking `N = 0` and enlarging by `(scale w)^{N'} ≥ 1` gives the
`t`-uniform polynomial bound on any such `K` — in particular on the part of the target's region
whose closure misses the boundary `∂𝒟` (where the poles sit). -/

/-- **The kernel is bounded on a fixed compact subset of `𝒟`, in the target's shape.**

The input `hflat` is the conclusion of `Work.Asymptotics.Kaxis_local_flat` (it is taken as a
hypothesis here only because importing `Submission.Work.Asymptotics.Kaxis_local_flat` clashes
with an unrelated duplicate declaration elsewhere in the tree; the statement is that lemma with
`N = 0`).  With `scale w ≥ 1` and `N' ≥ 0` the factor `(scale w)^{N'}` is `≥ 1`, so the
`t`-uniform bound `c_K` converts into the target's shape. -/
lemma Kaxis_Kfun_le_of_compact (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {K : Set ℍ} (hK : IsCompact K) (hsub : K ⊆ Work.Asymptotics.DomainD)
    (hflat : ∀ N : ℝ, 0 ≤ N → ∃ c : ℝ, 0 < c ∧ ∀ (τ : ℍ) (t : ℝ),
      τ ∈ K → 0 < t → t ≤ 1 →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ c * t ^ N)
    (N' : ℝ) (hN' : 0 ≤ N') :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (w : ℍ) (t : ℝ),
      w ∈ K → 0 < t → t ≤ 1 →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t‖
          ≤ c * (Work.Kernels.scale w) ^ N' := by
  obtain ⟨c, hc, hb⟩ := hflat 0 (le_refl (0 : ℝ))
  refine ⟨c, hc.le, fun w t hw ht ht1 => ?_⟩
  have h1 : ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t‖ ≤ c := by
    have h := hb w t hw ht ht1
    rwa [Real.rpow_zero, mul_one] at h
  have h2 : (1 : ℝ) ≤ (Work.Kernels.scale w) ^ N' :=
    Real.one_le_rpow (Work.Kernels.one_le_scale w) hN'
  calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t‖ ≤ c := h1
    _ = c * 1 := (mul_one c).symm
    _ ≤ c * (Work.Kernels.scale w) ^ N' := mul_le_mul_of_nonneg_left h2 hc.le

/-! ## The remaining local piece on `∂𝒟`

`E` is the disc `{‖w − i/4‖ ≤ 1/4}` cut out of `𝒟`, so `E ∩ {‖w‖ ≥ σ}` is *precompact*, but its
closure meets `∂𝒟` in the cusp-parabolic orbit points `γ_{±1} · (i t)` (of modulus
`t/√(1+t²) ≥ σ` exactly when `t` is bounded below by a constant depending on `σ`).  Hence the
compactness input `Kaxis_Kfun_le_of_compact` applies to `E ∩ {‖w‖ ≥ σ}` with those finitely many
points removed, and the missing piece is the corresponding *local* bound at `γ_{±1} · (i t)`:
for each `σ > 0` there are `r, c, N'` with

  `‖Kaxis (Kfun ℓ d) w t‖ ≤ c (scale w)^{N'}`  for `|w − γ_{±1}·(i t)| < r`, `t ≤ 1`.

That bound is the one-zero argument at the *boundary* coincidence `γ_{±1}·(i t)`, whose
vanishing is exactly `Work.Asymptotics.KClear_cusp_parabolic_vanishing` (proved in this file):
`KfunClear` vanishes at `τ = γ_{±1}·(i t)` for every `z`, so `τ ↦ KfunClear ℓ d τ (i t)` has a
zero at the boundary point, and `E_one_zero_at` plus the difference quotient converts it into the
linear local bound; the constants are then uniform in `t` because the secant slope
`|j w − j(i t)|` is compared with `|j'(γ_{±1}·(i t))| ≈ e^{2π/t} t^{-2}` and
`‖Δ(i t)‖ ≍ e^{-2π/t} t^{-12}` at the same exponentially small scale. -/

/-! ## Route for the target

With `hplus`, `hminus`, `hdiv` all available (see the header), the target is the last missing
input.  The route with the tools in the workspace is a **bootstrap on the diagonal disc**:

* `τ ↦ KfunClear ℓ d τ (i t)` is holomorphic and vanishes at `τ = i t`
  (`Work.Asymptotics.KL.KfunClear_self`), so the one-zero estimate
  `Work.Asymptotics.E_one_zero_at` (or `KL.one_zero_apply` with `r ≈ t`) gives
  `‖KfunClear w (i t)‖ ≤ (8M/r)‖w − i t‖` where `M` bounds `|KfunClear (·) (i t)|` on the disc
  of radius `r` around `i t`;
* `M ≤ |Δ(i t)|^e · sup_disc |Δ| · sup_disc |j − j(i t)| · sup_disc |Kfun (·)(i t)|`, and the three
  first factors are *exponentially small* (`|Δ(i t)| ≍ e^{-2π/t} t^{-12}`,
  `|Δ(τ)| ≤ C (scale τ)^12 e^{-2π Im (S τ)}` with `Im (S τ) ≍ 1/t` on the disc, and
  `|j τ − j(i t)| ≲ e^{2π/t} t^{-2} r` by the difference-quotient);
* hence `M ≤ e^{-2π/t} poly(t, scale) · sup_disc |Kfun|`, and dividing by
  `‖Δ(w)Δ(i t)^e (j w − j(i t))‖ ≥ c t^{-12} |j w − j(i t)|` with
  `|j w − j(i t)| ≥ c |j'(i t)| |w − i t|` (difference quotient) leaves
  `‖Kfun w (i t)‖ ≤ e^{-2π/t} poly(t, scale w) · sup_disc |Kfun|`.

One ingredient must be stated with the *right radius*: the difference quotient of `j` at `i t`
with the constant keyed to `‖j'(i t)‖` is valid only on discs of radius `ρ t²` (`ρ > 0` small,
*not* on radius `t`): near the cusp `0` the function `j` oscillates on the scale `t²` because
`j(i t) = j(i/t)` and `d log j / dτ ≍ 2π/t²` there.  Concretely the needed statement is

  `∃ ρ c > 0, ∀ 0 < t ≤ 1/2, ∀ u v, ‖u − i t‖ ≤ ρ t² → ‖v − i t‖ ≤ ρ t² →
      c ‖E₄²E₆/Δ (i t)‖ ‖u − v‖ ≤ ‖j u − j v‖`,

which is the uniform-in-`t` form of `Work.Asymptotics.jDiff_lower_imagAxis` (there the constants
are only local).  Both reviewers checked it: with `‖E₄²E₆/Δ(i t)‖ = ‖j'(i t)‖/(2π)` and the
second-order cusp expansion `j(i/t + z) = q⁻¹ + 744 + O(‖q‖)`, `q = e^{2πi(i/t+z)}`, the Taylor
remainder is `≲ ρ sup |j''| |u−v|` with `sup|j''|/|j'| ≍ 2π/t²`, so any `ρ < 1/(2π)` works.

With that, the bootstrap contraction goes through: the one-zero disc may be taken of radius
`ρ t²` (which is where `w` lives — the hypothesis of the target is exactly `‖w − γ i t‖ < c₀ t²`),
`M` on that disc is controlled by the divisor form of Theorem 4.9(4) (`contour_bound_Kfun`)
together with the *sharp* factors `|Δ(i t)| ≍ e^{-2π/t} t^{-12}` and
`|j τ − j(i t)| ≍ |j'(i t)| |τ − i t|` on it, and the resulting inequality reads
`‖Kfun w (i t)‖ ≤ e^{-2π/t} poly(t, scale w) · sup_disc |Kfun|`.
Since `e^{-2π/t} poly(t) < 1` for `t ≤ t₀` small, one iteration from the crude (divisor-form)
bound gives the polynomial bound of the target on the cusp part `t ≤ t₀`; the part `t₀ ≤ t ≤ 1`
is handled by `Work.Asymptotics.Kaxis_local_flat` on the compact `E ∩ {‖w‖ ≥ σ}`, and the
remaining region `t ≤ t₀`, `‖w‖ ≤ σ` is covered by the same contraction with `scale w` powers. -/



/-! ## The cleared kernel vanishes at *every* cusp-parabolic orbit point

This block generalises `KClear_cusp_parabolic_vanishing` (proved above for the two points
`a = ±1`) to all `a ∈ ℤ`: for every `m : ℤ` and every `z`,

  `KfunClear ℓ d (S • ((m : ℝ) +ᵥ (S • z))) z = 0`.

The mechanism is the same as before, now run along the whole `T`-orbit of `S • z`: the cleared
kernels have vanishing second `T`-difference (`KPlusClear_T2`,
`AfunMinusNegOne.KMinusClear_T2`) and vanish at `S • z` and at `T (S • z)`, hence — by the
affine relation along the `T`-orbit — on the whole `T`-orbit of `S • z`; the `S`-transformation
law transports this to the cusp parabolics `S T^m S • z`. -/

/-- `(1:ℝ) +ᵥ ((1:ℝ) +ᵥ τ) = (2:ℝ) +ᵥ τ`. -/
private lemma vadd_one_one (τ : ℍ) : (1 : ℝ) +ᵥ ((1 : ℝ) +ᵥ τ) = (2 : ℝ) +ᵥ τ := by
  rw [← add_vadd]; norm_num

/-- **Affine propagation along the `T`-orbit.**  If `F` has vanishing second `T`-difference and
vanishes at `σ` and at `T σ = σ + 1`, then `F` vanishes on the whole `T`-orbit of `σ`. -/
private lemma T2_vanish_orbit {F : ℍ → ℂ}
    (hT2 : ∀ τ : ℍ, F ((2 : ℝ) +ᵥ τ) - 2 * F ((1 : ℝ) +ᵥ τ) + F τ = 0)
    {σ : ℍ} (h0 : F σ = 0) (h1 : F ((1 : ℝ) +ᵥ σ) = 0) :
    ∀ m : ℤ, F ((m : ℝ) +ᵥ σ) = 0 := by
  have hrec : ∀ τ : ℍ, F ((2 : ℝ) +ᵥ τ) = 2 * F ((1 : ℝ) +ᵥ τ) - F τ := by
    intro τ; have h := hT2 τ; linear_combination h
  have cast1 : ∀ n : ℕ, (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 := by intro n; push_cast; ring
  have cast2 : ∀ n : ℕ, (((n + 2 : ℕ)) : ℝ) = (n : ℝ) + 2 := by intro n; push_cast; ring
  have hpos : ∀ n : ℕ, F ((n : ℝ) +ᵥ σ) = 0 := by
    refine Nat.twoStepInduction (by simpa using h0) (by simpa using h1) ?_
    intro n ih₀ ih₁
    have h := hrec ((n : ℝ) +ᵥ σ)
    rw [show (2 : ℝ) +ᵥ ((n : ℝ) +ᵥ σ) = ((n : ℝ) + 2) +ᵥ σ from by
          rw [← add_vadd]; congr 1; ring,
        show (1 : ℝ) +ᵥ ((n : ℝ) +ᵥ σ) = (((n + 1 : ℕ)) : ℝ) +ᵥ σ from by
          rw [← add_vadd, cast1 n]; congr 1; ring] at h
    rw [show (((n + 2 : ℕ)) : ℝ) +ᵥ σ = ((n : ℝ) + 2) +ᵥ σ from by rw [cast2 n],
        h, ih₁, ih₀, mul_zero, sub_zero]
  have hneg : ∀ n : ℕ, F ((-(n : ℝ)) +ᵥ σ) = 0 := by
    refine Nat.twoStepInduction (by simpa using h0) ?_ ?_
    · have h := hrec ((-1 : ℝ) +ᵥ σ)
      rw [show (2 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ σ) = (1 : ℝ) +ᵥ σ from by
            rw [← add_vadd]; norm_num,
          show (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ σ) = σ from by rw [← add_vadd]; norm_num] at h
      have h' : F ((-1 : ℝ) +ᵥ σ) = 2 * F σ - F ((1 : ℝ) +ᵥ σ) := by linear_combination h
      rw [show (-(((1 : ℕ)) : ℝ)) +ᵥ σ = (-1 : ℝ) +ᵥ σ from by norm_num,
        h', h0, h1, mul_zero, sub_zero]
    · intro n ih₀ ih₁
      have h := hrec ((-(n : ℝ) - 2) +ᵥ σ)
      rw [show (2 : ℝ) +ᵥ ((-(n : ℝ) - 2) +ᵥ σ) = (-(n : ℝ)) +ᵥ σ from by
            rw [← add_vadd]; congr 1; ring,
          show (1 : ℝ) +ᵥ ((-(n : ℝ) - 2) +ᵥ σ) = (-((n : ℝ) + 1)) +ᵥ σ from by
            rw [← add_vadd]; congr 1; ring] at h
      have h' : F ((-(n : ℝ) - 2) +ᵥ σ)
          = 2 * F ((-((n : ℝ) + 1)) +ᵥ σ) - F ((-(n : ℝ)) +ᵥ σ) := by linear_combination h
      rw [show (-(((n + 2 : ℕ)) : ℝ)) +ᵥ σ = (-(n : ℝ) - 2) +ᵥ σ from by
            rw [cast2 n]; congr 1; ring,
        h']
      rw [show (-((n : ℝ) + 1)) +ᵥ σ = (-(((n + 1 : ℕ)) : ℝ)) +ᵥ σ from by
            rw [cast1 n],
        ih₁, ih₀, mul_zero, sub_zero]
  intro m
  by_cases hm : 0 ≤ m
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    exact hpos n
  · have hm' : m < 0 := not_le.mp hm
    obtain ⟨n, rfl⟩ := Int.eq_negSucc_of_lt_zero hm'
    have hcast : (((Int.negSucc n : ℤ)) : ℝ) = -(((n + 1 : ℕ) : ℝ)) := by
      rw [Int.negSucc_eq]; push_cast; ring
    rw [show (((Int.negSucc n : ℤ) : ℝ) +ᵥ σ) = (-(((n + 1 : ℕ)) : ℝ)) +ᵥ σ from by rw [hcast]]
    exact hneg (n + 1)

/-- **The cleared `K_+` vanishes at every cusp-parabolic orbit point.** -/
theorem KPlusClear_cuspParabolic_vanishing (d : ℕ) (hd : d = 8 ∨ d = 24) (m : ℤ) (z : ℍ) :
    Work.Kernels.KPlusClear d (ModularGroup.S • ((m : ℝ) +ᵥ (ModularGroup.S • z))) z = 0 := by
  have hF := T2_vanish_orbit
    (F := fun τ : ℍ => Work.Kernels.KPlusClear d τ z)
    (fun τ => by
      have h := congr_fun (KPlusClear_T2 d hd z) τ
      simpa only [Work.Kernels.T2op, Pi.zero_apply] using h)
    (KClear_S_vanishing Work.Kernels.logLambda d hd z).1
    (Work.Residues.KPlusClear_TS d hd z) m
  rw [KPlusClear_S_smul d hd ((m : ℝ) +ᵥ (ModularGroup.S • z)) z, hF, mul_zero]

/-- **The cleared `K_-` vanishes at every cusp-parabolic orbit point.** -/
theorem KMinusClear_cuspParabolic_vanishing (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (m : ℤ) (z : ℍ) :
    Work.Kernels.KMinusClear ℓ d (ModularGroup.S • ((m : ℝ) +ᵥ (ModularGroup.S • z))) z = 0 := by
  have hF := T2_vanish_orbit
    (F := fun τ : ℍ => Work.Kernels.KMinusClear ℓ d τ z)
    (fun τ => by
      have h := congr_fun (Work.Residues.AfunMinusNegOne.KMinusClear_T2 ℓ d hd z) τ
      simpa only [Work.Kernels.T2op, Pi.zero_apply] using h)
    (KClear_S_vanishing ℓ d hd z).2
    (Work.Residues.KMinusClear_TS ℓ d hd z) m
  rw [KMinusClear_S_smul ℓ d hd ((m : ℝ) +ᵥ (ModularGroup.S • z)) z, hF, mul_zero]

/-- **The cleared kernel vanishes at every cusp-parabolic orbit point.** -/
theorem KfunClear_cuspParabolic_vanishing (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (m : ℤ) (z : ℍ) :
    Work.Kernels.KfunClear ℓ d (ModularGroup.S • ((m : ℝ) +ᵥ (ModularGroup.S • z))) z = 0 := by
  rw [Work.Kernels.KfunClear, KPlusClear_cuspParabolic_vanishing d hd m z,
    KMinusClear_cuspParabolic_vanishing ℓ d hd m z, add_zero, zero_div]

/-! ## Progress log, Step-1 ingredients, and Lean gotchas

**Proved:** `T2_vanish_orbit` (affine propagation along the `T`-orbit from two consecutive
zeros), and hence `KfunClear ℓ d (S • (m +ᵥ S • z)) z = 0` for every `m : ℤ`
(`KPlusClear_cuspParabolic_vanishing`, `KMinusClear_cuspParabolic_vanishing`,
`KfunClear_cuspParabolic_vanishing`).

**Aux module `Submission/Work/Asymptotics/KKNE_aux.lean`** (imported here, no `sorry`):
`slash_KPlus_E` (from `Xi8_bound_E` / `Xi24_bound_E`) and `slash_KMinus_E` (the Schwarz upgrade
of `Ncusp_EReg_crude_8/24`, copied from `KMinus_slash_bound_E.lean` **with its unused
`KMinusCuspBallBound` import dropped**, so the module stays on the `Xi8_bound_E` side of the
`continuous_scale` conflict).

**Gotchas (they cost real time; do not rediscover them):**

* ℂ-valued identities need `linear_combination`/`ring` (`ring_nf` as fallback) — `linarith`
  fails silently on ℂ.
* `+ᵥ` is right-associative: handle shifts via `show ... from by rw [← add_vadd]; congr 1; ring`,
  and normalise ℕ→ℝ casts explicitly (helpers `cast1`, `cast2` in `T2_vanish_orbit`).
* **Never `set` a term whose type carries a proof component** (e.g. `imagAxis t⁻¹ h`): every
  later `rw [that_def]` is a dependent rewrite and dies with "motive is not type correct".
  (A `set` of a *real-valued* expression is harmless.)
* Names ambiguous with the `Matrix` namespace (this file has `open Matrix`) need qualifying:
  `_root_.mul_inv_rev`, `_root_.zpow_neg`, `_root_.inv_zpow`.
* ASCII identifiers in long `refine ⟨...⟩` terms.

**Working `divisor_bound_abstract` draft (in `_bk_kkne_ab_partial.lean` at the workspace root).**
The two `calc` chains for `hP` (the `K₊` bound) and `hM` (the `K₋` bound) are *closed* in that
draft, with the recipe:

* state `hX : K_± d w (S•z₁) = z₁^a * (z₁^{-a} * K_± d w (S•z₁))` (from `hsplit`, `a := (2:ℤ)-(d:ℤ)/2`)
  and `hnorm : ‖z₁^a * (z₁^{-a} * X)‖ = (t⁻¹)^a * ‖z₁^{-a} * X‖` (`by rw [norm_mul, hzp a]`);
* then the **stepwise** `calc` `‖K_± d w z‖ = ‖K_± d w (S•z₁)‖ := by rw [← hSS]`,
  `_ = ‖z₁^a * (z₁^{-a} * K_± d w (S•z₁))‖ := congrArg (fun Y : ℂ => ‖Y‖) hX`,
  `_ = (t⁻¹)^a * ‖z₁^{-a} * K_± d w (S•z₁)‖ := hnorm`, then the `≤` step against `hplus`/`hminus`.
  **Two traps here**: (i) `rw [hX]` rewrites the occurrence inside the *right-hand side* as well
  and leaves an unsolved goal — use `congrArg (fun Y : ℂ => ‖Y‖) hX`; (ii) `(1 + ‖z₁‖)^2 ≥ 0`
  needs `pow_nonneg (by positivity : (0:ℝ) ≤ 1 + ‖(z₁:ℂ)‖) 2`, not `pow_nonneg (norm_nonneg _) _`.
* in the instantiation, unfold `Kaxis` first (`rw [Work.Kernels.Kaxis, dif_pos ht]`) before
  applying the abstract lemma.

An updated copy of that draft, in which the `hsum` step is instead routed through the explicit
`hstep : Cp * S^Np * (X/B) + Cm * S^Nm * (X/B) = (Cp * S^Np + Cm * S^Nm) * (X/B)` closed by
`rw [add_mul]` (`ring` cannot distribute across `zpow` atoms with variable exponent), is
`_bk_kkne_ab_partial2.lean`.

What remained in that draft: the final assembly `hstep1`/`hstep2` (~5 error reports at
`rw [← add_mul] at h`, the two `show ... from by ring` division rearrangements, and two
`mul_le_mul` applications), plus re-checking the `Kaxis` unfolding. Everything before it is
discharged.

**Step 1 (`Kaxis_Kfun_divisor_bound`).**  Statement (fixed, normalised):

  `‖Kaxis (Kfun ℓ d) w t‖ ≤ C (scale w)^N t^{d/2-4} e^{-π/t} / ‖Δ(i/t)(j w - j(i t))‖`.

Recipe, and where the last draft stood:

1. prove an **abstract** lemma with `z₁ z : ℍ` and hypotheses `S • z₁ = z`, `‖z₁‖ = t⁻¹`,
   `z₁.im = t⁻¹`, the two slash bounds at `(w, z₁)` (this avoids all `imagAxis`
   proof-components): conclude the bound with the divisor `‖Δ z₁ * (j w - j z₁)‖`;
2. inside it: `hzp : ∀ k, ‖z₁^k‖ = (t⁻¹)^k` via `norm_zpow` + `hzn`; `hsplit : ∀ X, z₁^a * (z₁^{-a} * X) = X`
   via `← mul_assoc, ← zpow_add₀ hzne, add_neg_cancel, zpow_zero, one_mul` with
   `hzne : (z₁ : ℂ) ≠ 0` from `z₁.im ≠ 0`; then the two `calc` chains
   `‖K_±(w,z)‖ = ‖z₁^{a} * (z₁^{-a} * K_±(w, S•z₁))‖ = (t⁻¹)^a * ‖...‖ ≤ ...`
   (in the `rw [norm_mul, hzp]` step write **`hzp ((2 : ℤ) - (d : ℤ) / 2)`** — the bare `hzp`
   leaves an unsolved goal); **and** do not put `norm_mul` into a chain that also rewrites the
   right-hand side of the `calc` step: prove the equality
   `hnorm : ‖z₁^a * (z₁^{-a} * X)‖ = (t⁻¹)^a * ‖z₁^{-a} * X‖` by
   `rw [norm_mul, hzp ((2:ℤ) - (d:ℤ)/2)]` and then close the step with `rw [← hSS, hX, hnorm]`
   (with `hnorm` in hand the right-hand side is protected).  A draft in which the last step
   still reports an unsolved goal is in the transcript; the remaining goal there is the
   `= ((t⁻¹)^a * ‖z₁^{-a} * K‖)` shape, so the fix is to state `hX` with the *same* `A/D`
   grouping as `hP`/`hM` use;
3. `‖Kfun‖ ≤ (‖K₊‖ + ‖K₋‖)/2` (`rw [Work.Kernels.Kfun, norm_div, show ‖(2 : ℂ)‖ = 2 from by norm_num]`),
   then lift `Np`, `Nm` to `max Np Nm` with `Real.rpow_le_rpow_of_exponent_le (one_le_scale w)`
   and `(Cp + Cm)/2 ≤ max Cp Cm`;
4. finally `factor_le` with `hzn`/`hzim` to reach `t^{d/2-4} e^{-π/t}`;
5. instantiate at `z₁ := imagAxis t⁻¹ (inv_pos.mpr ht)`, `z := imagAxis t ht`, using
   `S_smul_imagAxis_inv`, `E_S_im_ge`, `EtailE.jInvariantFun_Ssmul` and `one_le_inv₀`.-/

/-- `S • (i/t) = i t`. -/
private lemma S_smul_imagAxis_inv {t : ℝ} (ht : 0 < t) :
    ModularGroup.S • Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht) = Work.Kernels.imagAxis t ht := by
  apply UpperHalfPlane.ext
  rw [Work.Kernels.S_smul_coe]
  have hcoe : ((Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht) : ℍ) : ℂ)
      = ((t⁻¹ : ℝ) : ℂ) * Complex.I := rfl
  rw [hcoe]
  have him : ((Work.Kernels.imagAxis t ht : ℍ) : ℂ) = ((t : ℝ) : ℂ) * Complex.I := rfl
  rw [him, _root_.mul_inv_rev, Complex.inv_I, ← Complex.ofReal_inv, inv_inv]
  ring

/-- `(t⁻¹)^{2-d/2} (1+t⁻¹)² ≤ 4 t^{d/2-4}` for `0 < t ≤ 1`. -/
private lemma factor_le (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) (d : ℕ) :
    (t⁻¹) ^ ((2 : ℤ) - (d : ℤ) / 2) * (1 + t⁻¹) ^ (2 : ℕ)
      ≤ 4 * t ^ ((d : ℤ) / 2 - 4) := by
  have h1 : (t⁻¹) ^ ((2 : ℤ) - (d : ℤ) / 2) = t ^ ((d : ℤ) / 2 - 2) := by
    rw [_root_.inv_zpow, ← _root_.zpow_neg]
    congr 1; ring
  rw [h1]
  have h2 : (1 + t⁻¹) ^ (2 : ℕ) ≤ 4 * t ^ (-(2 : ℤ)) := by
    have htinv : (1 : ℝ) ≤ t⁻¹ := (one_le_inv₀ ht).mpr ht1
    have h3 : (1 : ℝ) + t⁻¹ ≤ 2 * t⁻¹ := by linarith
    have h4 : (1 + t⁻¹) ^ 2 ≤ (2 * t⁻¹) ^ 2 := pow_le_pow_left₀ (by linarith) h3 2
    have h5 : (2 * t⁻¹) ^ 2 = 4 * t ^ (-(2 : ℤ)) := by
      rw [mul_pow, inv_pow, _root_.zpow_neg, zpow_ofNat]
      norm_num
    linarith [h4, h5.le, h5.ge]
  have h6 : t ^ ((d : ℤ) / 2 - 2) * (4 * t ^ (-(2 : ℤ))) = 4 * t ^ ((d : ℤ) / 2 - 4) := by
    rw [show t ^ ((d : ℤ) / 2 - 2) * (4 * t ^ (-(2 : ℤ)))
          = 4 * (t ^ ((d : ℤ) / 2 - 2) * t ^ (-(2 : ℤ))) from by ring,
      ← zpow_add₀ ht.ne', show ((d : ℤ) / 2 - 2) + (-(2 : ℤ)) = (d : ℤ) / 2 - 4 by ring]
  calc t ^ ((d : ℤ) / 2 - 2) * (1 + t⁻¹) ^ (2 : ℕ)
      ≤ t ^ ((d : ℤ) / 2 - 2) * (4 * t ^ (-(2 : ℤ))) :=
        mul_le_mul_of_nonneg_left h2 (zpow_nonneg ht.le _)
    _ = 4 * t ^ ((d : ℤ) / 2 - 4) := h6



/-! ## The `q`-difference and the sine

`Work.Asymptotics.divisor_qdiff_lower` compares the divisor with the `q`-difference
`‖q τ - q ζ‖`; the identity below rewrites that difference as a sine times an exponential of the
total height, so that its size can be read off from the position of `τ` relative to `i/t + ℤ`. -/

/-- `q τ - q ζ = e^{πi(τ+ζ)} · 2i sin(π(τ-ζ))`. -/
lemma qParamFun_sub (τ ζ : ℍ) :
    Work.Kernels.qParamFun τ - Work.Kernels.qParamFun ζ
      = Complex.exp (Real.pi * Complex.I * ((τ : ℂ) + (ζ : ℂ)))
        * (2 * Complex.I * Complex.sin (Real.pi * ((τ : ℂ) - (ζ : ℂ)))) := by
  have h1 : Work.Kernels.qParamFun τ
      = Complex.exp (Real.pi * Complex.I * ((τ : ℂ) + (ζ : ℂ)))
        * Complex.exp (Real.pi * Complex.I * ((τ : ℂ) - (ζ : ℂ))) := by
    rw [← Complex.exp_add, Work.Kernels.qParamFun]
    congr 1
    ring
  have h2 : Work.Kernels.qParamFun ζ
      = Complex.exp (Real.pi * Complex.I * ((τ : ℂ) + (ζ : ℂ)))
        * Complex.exp (-(Real.pi * Complex.I * ((τ : ℂ) - (ζ : ℂ)))) := by
    rw [← Complex.exp_add, Work.Kernels.qParamFun]
    congr 1
    ring
  have hsin : Complex.exp (Real.pi * Complex.I * ((τ : ℂ) - (ζ : ℂ)))
      - Complex.exp (-(Real.pi * Complex.I * ((τ : ℂ) - (ζ : ℂ))))
      = 2 * Complex.I * Complex.sin (Real.pi * ((τ : ℂ) - (ζ : ℂ))) := by
    set w : ℂ := Real.pi * ((τ : ℂ) - (ζ : ℂ)) with hw
    have h3 : Real.pi * Complex.I * ((τ : ℂ) - (ζ : ℂ)) = w * Complex.I := by
      rw [hw]; ring
    rw [h3, show -(w * Complex.I) = (-w) * Complex.I from by ring,
      Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
    rw [hw]
    ring
  rw [h1, h2, ← mul_sub, hsin]

/-- **The `q`-difference is a sine times an exponential of the total height.** -/
lemma norm_qParamFun_sub (τ ζ : ℍ) :
    ‖Work.Kernels.qParamFun τ - Work.Kernels.qParamFun ζ‖
      = 2 * Real.exp (-(Real.pi * (τ.im + ζ.im)))
          * ‖Complex.sin (Real.pi * ((τ : ℂ) - (ζ : ℂ)))‖ := by
  have h2I : ‖(2 : ℂ) * Complex.I‖ = 2 := by
    rw [norm_mul, Complex.norm_I, mul_one]
    norm_num
  rw [qParamFun_sub, norm_mul, norm_mul, h2I]
  have hA : ‖Complex.exp (Real.pi * Complex.I * ((τ : ℂ) + (ζ : ℂ)))‖
      = Real.exp (-(Real.pi * (τ.im + ζ.im))) := by
    rw [Complex.norm_exp]
    congr 1
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, UpperHalfPlane.coe_im, Complex.add_re, Complex.add_im,
      zero_mul, mul_zero, sub_zero, add_zero]
    ring
  rw [hA]
  ring

/-- **`‖sin‖²` in terms of the real and imaginary parts.** -/
lemma norm_sin_sq (z : ℂ) :
    ‖Complex.sin z‖ ^ 2 = Real.sin z.re ^ 2 + Real.sinh z.im ^ 2 := by
  have h1 : Complex.sin z
      = ((Real.sin z.re * Real.cosh z.im : ℝ) : ℂ)
        + ((Real.cos z.re * Real.sinh z.im : ℝ) : ℂ) * Complex.I := by
    rw [Complex.sin_eq, ← Complex.ofReal_sin, ← Complex.ofReal_cosh, ← Complex.ofReal_cos,
      ← Complex.ofReal_sinh]
    push_cast
    ring
  rw [h1, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, sub_zero, add_zero,
    zero_add, zero_mul]
  have hs : Real.sin z.re ^ 2 + Real.cos z.re ^ 2 = 1 := Real.sin_sq_add_cos_sq z.re
  have hc : Real.cosh z.im ^ 2 - Real.sinh z.im ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq z.im
  nlinarith [hs, hc]

/-- **The sine of `π(τ-ζ)` in terms of the coordinates of `τ - ζ`.** -/
lemma norm_sin_pi_sub (τ ζ : ℍ) :
    ‖Complex.sin (Real.pi * ((τ : ℂ) - (ζ : ℂ)))‖ ^ 2
      = Real.sin (Real.pi * ((τ : ℂ) - (ζ : ℂ)).re) ^ 2
        + Real.sinh (Real.pi * ((τ : ℂ) - (ζ : ℂ)).im) ^ 2 := by
  rw [norm_sin_sq]
  have h1 : (Real.pi * ((τ : ℂ) - (ζ : ℂ))).re = Real.pi * ((τ : ℂ) - (ζ : ℂ)).re := by
    simp [Complex.mul_re]
  have h2 : (Real.pi * ((τ : ℂ) - (ζ : ℂ))).im = Real.pi * ((τ : ℂ) - (ζ : ℂ)).im := by
    simp [Complex.mul_im]
  rw [h1, h2]

/-- **Step 1, abstract form.**  No `imagAxis` occurs in this statement or its proof: the divisor
is passed in as a *real number* `B` together with the equation `hB : B = ‖…‖`, so that the whole
proof is real arithmetic. -/
private lemma divisor_bound_abstract (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    {w z z₁ : ℍ} {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    {Cp Np Cm Nm : ℝ} (hCp : 0 ≤ Cp) (hCm : 0 ≤ Cm)
    (hSS : ModularGroup.S • z₁ = z) (hzn : ‖(z₁ : ℂ)‖ = t⁻¹) (hzim : z₁.im = t⁻¹)
    {B : ℝ} (hB : B = ‖Work.Kernels.DeltaFun z₁
        * (Work.Kernels.jInvariantFun w - Work.Kernels.jInvariantFun z₁)‖)
    (hplus : ‖(z₁ : ℂ) ^ (-((2 : ℤ) - (d : ℤ) / 2)) * Work.Kernels.KPlus d w (ModularGroup.S • z₁)‖
        ≤ Cp * (Work.Kernels.scale w) ^ Np * (1 + ‖(z₁ : ℂ)‖) ^ (2 : ℕ)
            * Real.exp (-(Real.pi * z₁.im)) / B)
    (hminus : ‖(z₁ : ℂ) ^ (-((2 : ℤ) - (d : ℤ) / 2)) * Work.Kernels.KMinus ℓ d w (ModularGroup.S • z₁)‖
        ≤ Cm * (Work.Kernels.scale w) ^ Nm * (1 + ‖(z₁ : ℂ)‖) ^ (2 : ℕ)
            * Real.exp (-(Real.pi * z₁.im)) / B) :
    ‖Work.Kernels.Kfun ℓ d w z‖
      ≤ 4 * max Cp Cm * (Work.Kernels.scale w) ^ (max Np Nm) * t ^ ((d : ℤ) / 2 - 4)
          * Real.exp (-(Real.pi / t)) / B := by
  have hBnn : 0 ≤ B := by rw [hB]; exact norm_nonneg _
  have hzne : (z₁ : ℂ) ≠ 0 := fun h => by
    have hpos := z₁.im_pos
    rw [← UpperHalfPlane.coe_im, h] at hpos
    simp at hpos
  have hzp : ∀ k : ℤ, ‖(z₁ : ℂ) ^ k‖ = (t⁻¹) ^ k := by intro k; rw [norm_zpow, hzn]
  have hsplit : ∀ X : ℂ, (z₁ : ℂ) ^ ((2 : ℤ) - (d : ℤ) / 2)
      * ((z₁ : ℂ) ^ (-((2 : ℤ) - (d : ℤ) / 2)) * X) = X := by
    intro X
    rw [← mul_assoc, ← zpow_add₀ hzne, add_neg_cancel, zpow_zero, one_mul]
  set AA : ℝ := (t⁻¹) ^ ((2 : ℤ) - (d : ℤ) / 2) * (1 + ‖(z₁ : ℂ)‖) ^ (2 : ℕ)
    * Real.exp (-(Real.pi * z₁.im)) with hAA
  have hA0 : 0 ≤ AA := by
    rw [hAA]
    exact mul_nonneg (mul_nonneg (zpow_nonneg (inv_nonneg.mpr ht.le) _)
      (pow_nonneg (by positivity : (0 : ℝ) ≤ 1 + ‖(z₁ : ℂ)‖) 2)) (Real.exp_nonneg _)
  have hP : ‖Work.Kernels.KPlus d w z‖ ≤ Cp * (Work.Kernels.scale w) ^ Np * (AA / B) := by
    have hX : Work.Kernels.KPlus d w (ModularGroup.S • z₁)
        = (z₁ : ℂ) ^ ((2 : ℤ) - (d : ℤ) / 2)
          * ((z₁ : ℂ) ^ (-((2 : ℤ) - (d : ℤ) / 2))
              * Work.Kernels.KPlus d w (ModularGroup.S • z₁)) := (hsplit _).symm
    have hnorm : ‖(z₁ : ℂ) ^ ((2 : ℤ) - (d : ℤ) / 2)
        * ((z₁ : ℂ) ^ (-((2 : ℤ) - (d : ℤ) / 2))
            * Work.Kernels.KPlus d w (ModularGroup.S • z₁))‖
        = (t⁻¹) ^ ((2 : ℤ) - (d : ℤ) / 2)
          * ‖(z₁ : ℂ) ^ (-((2 : ℤ) - (d : ℤ) / 2))
              * Work.Kernels.KPlus d w (ModularGroup.S • z₁)‖ := by
      rw [norm_mul, hzp ((2 : ℤ) - (d : ℤ) / 2)]
    calc ‖Work.Kernels.KPlus d w z‖
        = ‖Work.Kernels.KPlus d w (ModularGroup.S • z₁)‖ := by rw [← hSS]
      _ = ‖(z₁ : ℂ) ^ ((2 : ℤ) - (d : ℤ) / 2)
            * ((z₁ : ℂ) ^ (-((2 : ℤ) - (d : ℤ) / 2))
                * Work.Kernels.KPlus d w (ModularGroup.S • z₁))‖ :=
          congrArg (fun Y : ℂ => ‖Y‖) hX
      _ = (t⁻¹) ^ ((2 : ℤ) - (d : ℤ) / 2)
            * ‖(z₁ : ℂ) ^ (-((2 : ℤ) - (d : ℤ) / 2))
                * Work.Kernels.KPlus d w (ModularGroup.S • z₁)‖ := hnorm
      _ ≤ (t⁻¹) ^ ((2 : ℤ) - (d : ℤ) / 2)
            * (Cp * (Work.Kernels.scale w) ^ Np * (1 + ‖(z₁ : ℂ)‖) ^ (2 : ℕ)
                * Real.exp (-(Real.pi * z₁.im)) / B) :=
          mul_le_mul_of_nonneg_left hplus (zpow_nonneg (inv_nonneg.mpr ht.le) _)
      _ = Cp * (Work.Kernels.scale w) ^ Np * (AA / B) := by rw [hAA]; ring
  have hM : ‖Work.Kernels.KMinus ℓ d w z‖ ≤ Cm * (Work.Kernels.scale w) ^ Nm * (AA / B) := by
    have hX : Work.Kernels.KMinus ℓ d w (ModularGroup.S • z₁)
        = (z₁ : ℂ) ^ ((2 : ℤ) - (d : ℤ) / 2)
          * ((z₁ : ℂ) ^ (-((2 : ℤ) - (d : ℤ) / 2))
              * Work.Kernels.KMinus ℓ d w (ModularGroup.S • z₁)) := (hsplit _).symm
    have hnorm : ‖(z₁ : ℂ) ^ ((2 : ℤ) - (d : ℤ) / 2)
        * ((z₁ : ℂ) ^ (-((2 : ℤ) - (d : ℤ) / 2))
            * Work.Kernels.KMinus ℓ d w (ModularGroup.S • z₁))‖
        = (t⁻¹) ^ ((2 : ℤ) - (d : ℤ) / 2)
          * ‖(z₁ : ℂ) ^ (-((2 : ℤ) - (d : ℤ) / 2))
              * Work.Kernels.KMinus ℓ d w (ModularGroup.S • z₁)‖ := by
      rw [norm_mul, hzp ((2 : ℤ) - (d : ℤ) / 2)]
    calc ‖Work.Kernels.KMinus ℓ d w z‖
        = ‖Work.Kernels.KMinus ℓ d w (ModularGroup.S • z₁)‖ := by rw [← hSS]
      _ = ‖(z₁ : ℂ) ^ ((2 : ℤ) - (d : ℤ) / 2)
            * ((z₁ : ℂ) ^ (-((2 : ℤ) - (d : ℤ) / 2))
                * Work.Kernels.KMinus ℓ d w (ModularGroup.S • z₁))‖ :=
          congrArg (fun Y : ℂ => ‖Y‖) hX
      _ = (t⁻¹) ^ ((2 : ℤ) - (d : ℤ) / 2)
            * ‖(z₁ : ℂ) ^ (-((2 : ℤ) - (d : ℤ) / 2))
                * Work.Kernels.KMinus ℓ d w (ModularGroup.S • z₁)‖ := hnorm
      _ ≤ (t⁻¹) ^ ((2 : ℤ) - (d : ℤ) / 2)
            * (Cm * (Work.Kernels.scale w) ^ Nm * (1 + ‖(z₁ : ℂ)‖) ^ (2 : ℕ)
                * Real.exp (-(Real.pi * z₁.im)) / B) :=
          mul_le_mul_of_nonneg_left hminus (zpow_nonneg (inv_nonneg.mpr ht.le) _)
      _ = Cm * (Work.Kernels.scale w) ^ Nm * (AA / B) := by rw [hAA]; ring
  have hsum : ‖Work.Kernels.KPlus d w z‖ + ‖Work.Kernels.KMinus ℓ d w z‖
      ≤ (Cp * (Work.Kernels.scale w) ^ Np + Cm * (Work.Kernels.scale w) ^ Nm) * (AA / B) := by
    refine (add_le_add hP hM).trans_eq ?_
    ring
  have hscale1 : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
  have hscale0 : (0 : ℝ) ≤ Work.Kernels.scale w := le_trans zero_le_one hscale1
  have hpowp : (Work.Kernels.scale w) ^ Np ≤ (Work.Kernels.scale w) ^ (max Np Nm) :=
    Real.rpow_le_rpow_of_exponent_le hscale1 (le_max_left _ _)
  have hpowm : (Work.Kernels.scale w) ^ Nm ≤ (Work.Kernels.scale w) ^ (max Np Nm) :=
    Real.rpow_le_rpow_of_exponent_le hscale1 (le_max_right _ _)
  have hsm0 : (0 : ℝ) ≤ (Work.Kernels.scale w) ^ (max Np Nm) := Real.rpow_nonneg hscale0 _
  have hsmax : Cp * (Work.Kernels.scale w) ^ Np + Cm * (Work.Kernels.scale w) ^ Nm
      ≤ (Cp + Cm) * (Work.Kernels.scale w) ^ (max Np Nm) := by
    refine (add_le_add (mul_le_mul_of_nonneg_left hpowp hCp)
      (mul_le_mul_of_nonneg_left hpowm hCm)).trans_eq ?_
    ring
  have hAAb : AA ≤ 4 * t ^ ((d : ℤ) / 2 - 4) * Real.exp (-(Real.pi / t)) := by
    have hfac : (t⁻¹) ^ ((2 : ℤ) - (d : ℤ) / 2) * (1 + ‖(z₁ : ℂ)‖) ^ (2 : ℕ)
        ≤ 4 * t ^ ((d : ℤ) / 2 - 4) := by
      rw [hzn]; exact factor_le t ht ht1 d
    have hexpeq : Real.exp (-(Real.pi * z₁.im)) = Real.exp (-(Real.pi / t)) := by
      rw [hzim, div_eq_mul_inv]
    rw [hAA, hexpeq]
    exact mul_le_mul_of_nonneg_right hfac (Real.exp_nonneg _)
  have hhalf : (Cp + Cm) / 2 ≤ max Cp Cm := by
    linarith [le_max_left Cp Cm, le_max_right Cp Cm]
  have hAB : AA / B ≤ (4 * t ^ ((d : ℤ) / 2 - 4) * Real.exp (-(Real.pi / t))) / B :=
    div_le_div_of_nonneg_right hAAb hBnn
  have hmain : ‖Work.Kernels.Kfun ℓ d w z‖
      ≤ (‖Work.Kernels.KPlus d w z‖ + ‖Work.Kernels.KMinus ℓ d w z‖) / 2 := by
    rw [Work.Kernels.Kfun, norm_div, show ‖(2 : ℂ)‖ = 2 from by norm_num]
    exact div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
  have h3 : ((Cp + Cm) * (Work.Kernels.scale w) ^ (max Np Nm) * (AA / B)) / 2
      ≤ max Cp Cm * (Work.Kernels.scale w) ^ (max Np Nm)
          * ((4 * t ^ ((d : ℤ) / 2 - 4) * Real.exp (-(Real.pi / t))) / B) := by
    have h4 : ((Cp + Cm) * (Work.Kernels.scale w) ^ (max Np Nm) * (AA / B)) / 2
        = ((Cp + Cm) / 2) * (Work.Kernels.scale w) ^ (max Np Nm) * (AA / B) := by ring
    rw [h4]
    exact mul_le_mul (mul_le_mul_of_nonneg_right hhalf hsm0) hAB (div_nonneg hA0 hBnn)
      (mul_nonneg (le_trans hCp (le_max_left _ _)) hsm0)
  have h5 : max Cp Cm * (Work.Kernels.scale w) ^ (max Np Nm)
        * ((4 * t ^ ((d : ℤ) / 2 - 4) * Real.exp (-(Real.pi / t))) / B)
      = 4 * max Cp Cm * (Work.Kernels.scale w) ^ (max Np Nm) * t ^ ((d : ℤ) / 2 - 4)
          * Real.exp (-(Real.pi / t)) / B := by ring
  have hfinal : (‖Work.Kernels.KPlus d w z‖ + ‖Work.Kernels.KMinus ℓ d w z‖) / 2
      ≤ 4 * max Cp Cm * (Work.Kernels.scale w) ^ (max Np Nm) * t ^ ((d : ℤ) / 2 - 4)
          * Real.exp (-(Real.pi / t)) / B := by
    have h1 : (‖Work.Kernels.KPlus d w z‖ + ‖Work.Kernels.KMinus ℓ d w z‖) / 2
        ≤ ((Cp + Cm) * (Work.Kernels.scale w) ^ (max Np Nm) * (AA / B)) / 2 :=
      div_le_div_of_nonneg_right
        (hsum.trans (mul_le_mul_of_nonneg_right hsmax (div_nonneg hA0 hBnn))) (by norm_num)
    exact h1.trans (h3.trans_eq h5)
  exact hmain.trans hfinal

/-- **Step 1**: the divisor form of the bound on `E` (see the plan). -/
theorem Kaxis_Kfun_divisor_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (w : ℍ) (t : ℝ) (ht : 0 < t),
      (3 / 2 : ℝ) ≤ (ModularGroup.S • w).im → t ≤ 1 →
      Work.Kernels.jInvariantFun w ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t‖
        ≤ C * (Work.Kernels.scale w) ^ N * t ^ ((d : ℤ) / 2 - 4) * Real.exp (-(Real.pi / t))
          / ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht)) *
              (Work.Kernels.jInvariantFun w
                - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht)))‖ := by
  obtain ⟨Cp, Np, hCp, hNp, hbp⟩ := slash_KPlus_E d hd
  obtain ⟨Cm, Nm, hCm, hNm, hbm⟩ := slash_KMinus_E ℓ d hd
  refine ⟨4 * max Cp Cm, max Np Nm, by positivity, le_max_of_le_left hNp,
    fun w t ht hE ht1 hjne => ?_⟩
  have h1 : (1 : ℝ) ≤ t⁻¹ := (one_le_inv₀ ht).mpr ht1
  have hz₁im : (Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht)).im = t⁻¹ := by
    simp [Work.Kernels.imagAxis]
  have hz₁ : (1 : ℝ) ≤ (Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht)).im := by
    rw [hz₁im]; exact h1
  have hzn : ‖((Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht) : ℍ) : ℂ)‖ = t⁻¹ := by
    rw [show ((Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht) : ℍ) : ℂ)
          = ((t⁻¹ : ℝ) : ℂ) * Complex.I from rfl,
      norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr ht)]
  have hSS : ModularGroup.S • (Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht))
      = Work.Kernels.imagAxis t ht := S_smul_imagAxis_inv ht
  have hj : Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht))
      = Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) := by
    have h := (Work.Asymptotics.EtailE.jInvariantFun_Ssmul
      (Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht))).symm
    rw [hSS] at h
    exact h
  have hne : Work.Kernels.jInvariantFun w
      ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht)) := by
    intro h; exact hjne (h.trans hj)
  rw [Work.Kernels.Kaxis, dif_pos ht]
  refine divisor_bound_abstract ℓ d ht ht1 (le_of_lt hCp) (le_of_lt hCm) hSS hzn hz₁im rfl ?_ ?_
  · simpa using hbp w (Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht)) hE hz₁ hne
  · simpa using hbm w (Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht)) hE hz₁ hne

/-! ## Plan and status for the proof of the target (working notes)

**Reduction.**  Write `z = i t` (`t ≤ 1`), `y := Im (S • w) ≥ 2` (since `w ∈ E`), and

  `ζ := exp (2π i ((S • w) - z₀))`,  `z₀ := i/t = S • z`,  `r := |ζ| = exp (2π (1/t - y))`.

Then `q (S•w) / q z₀ = ζ` and `q z₀ = exp (-2π/t)`.

*Step 1 (numerator).*  The two CKMRV slash bounds (`KMinus_slash_bound_E` form, obtainable from
`Ncusp_EReg_crude_8/24` + the Schwarz step `slash_bound_of_crude_E`, and `Xi8_bound_E` /
`Xi24_bound_E` for `K₊`) give, at `z = i/t` (so `S • z = i t`),

  `‖Kaxis (Kfun ℓ d) w t‖ ≤ C (scale w)^N (1 + 1/t)^2 e^{-π/t} / ‖Δ(i/t) (j w - j (i t))‖`.

*Step 2 (separation regime).*  If `‖j w‖ ≤ ‖j (i t)‖/2` or `‖j (i t)‖ ≤ ‖j w‖/2` then
`‖j w - j (i t)‖ ≥ ‖j (i t)‖/2 ≥ c e^{2π/t}` (`jInvariantFun_imagAxis_atZero`), and with
`‖Δ(i/t)‖ ≳ e^{-2π/t}` and `t^{-2} ≤ ((1+c₀) scale w)^2` (`scale_mul_t_ge`, proved above) the
bound becomes polynomial in `scale w`.

*Step 3 (the `q`-difference bound).*  `Work.Asymptotics.divisor_qdiff_lower` (proved, on the
`Xi8_bound_E` side of the import conflict) states: for `T₀ ≤ Im τ`, `1/3 ≤ Im z`,

  `c ‖q τ - q z‖ ≤ ‖Δ τ · Δ z · (j τ - j z)‖`.

Applied to `(τ, z) = (S • w, i/t)` (requires `y ≥ T₀`) or, by symmetry, to `(i/t, S • w)`
(requires `1/t ≥ T₀`), it yields

  `|Δ(i/t) (j w - j (i t))| ≥ (c / C_Δ) · ‖1 - ζ‖ / r`

(using `‖Δ(S•w)‖ ≤ C_Δ e^{-2π y}` and `e^{-2πy} = r e^{-2π/t}`, and
`‖1 - ζ‖ = e^{2π/t} ‖q (S•w) - q z₀‖`).  Hence

  `‖Kaxis (Kfun ℓ d) w t‖ ≤ K (scale w)^{N} (1+1/t)^2 e^{-π/t} · r / ‖1 - ζ‖`.

This is polynomial in `scale w` unless `r ∈ [1/2, 2]` *and* `‖1 - ζ‖` is small.

*Step 4 (`r ∈ [1/2,2]`, `‖1 - ζ‖` small).*  Then `w` is within `O(δ) t²` of the cusp parabolic
orbit point `S • (i/t + i n)` (`n` the nearest integer to `Re (S • w)`), where the cleared kernel
vanishes (`KfunClear_cuspParabolic_vanishing`, the general-`m` form of
`Kclear_cusp_parabolic_vanishing`).  The Schwarz/one-zero estimate
`Work.Asymptotics.KL.one_zero_apply` (Euclidean form, proved) applied to
`τ ↦ KfunClear ℓ d τ (i t)` at the centre `S • (i/t + i n)` then gives
`‖KfunClear w (i t)‖ ≤ (2M/ρt²) ‖w - S • (i/t+in)‖`, with `M` bounded by the *cleared* form of
Step 1 (i.e. `C (scale)^N t^{-12e+...} D^{e-1} e^{-π/t} |Δ(τ)|`, which follows from the slash
bounds by multiplying back with `growthPrefactor`); and the `q`-difference bound applied to the
pair `(S • w, i/t + i n)` bounds `|j w - j (i t)|` below by `c' e^{2π/t} t^{-2} ‖w - S•(i/t+in)‖`,
cancelling the distance.  The result is again polynomial in `scale w`.

*Step 5 (the remaining region `y < T₀` and `1/t < T₀`).*  Here `|w| ≥ 1/(2T₀)` and
`Im w ≥ 1/(2T₀²)`, so `scale w` is *bounded*; it suffices to bound the kernel there.  The
bounded-set flatness `Work.Asymptotics.HalfFunnel.Kaxis_cusp_of_bounded` (proved) covers
`t ≤ δ`; the remaining compact `t`-range is covered by `Kaxis_local_middle` on the part of `E`
that stays off `∂𝒟`, while the pieces touching `∂𝒟` are exactly the neighbourhoods of the
points `γ_{±1} (i t)`, where the same Schwarz argument as in Step 4 applies (the vanishing on
`∂𝒟` is available for those points by `Kclear_cusp_parabolic_vanishing`).

**Lemmas still to write** (all on the `Xi8_bound_E` side of the import conflict, i.e. importing
`Xi8_bound_E`, `Ncusp_EReg_crude_8/24`, `Kaxis_local_coincidence`, `divisor_qdiff_lower`,
`HalfFunnel.Kaxis_cusp_of_bounded`, `E_jdiff`-free):

1. `KfunClear_cuspParabolic_vanishing` : `KfunClear ℓ d (S • (m +ᵥ S • z)) z = 0` for all `m : ℤ`
   (affine propagation along the `T`-orbit of `S • z` from the two zeros `S•z` and `T(S•z)`,
   using `KPlusClear_T2` / `AfunMinusNegOne.KMinusClear_T2` and the `S`-laws).
2. `slash_KPlus_E` / `slash_KMinus_E` : the two CKMRV slash bounds on `E`
   (`slash_KMinus_E` is the statement of `KMinus_slash_bound_E`; its proof can be copied from
   that file *without* its `KMinusCuspBallBound` import, which is unused).
3. `Kaxis_Kfun_divisor_bound` : Step 1 above.
4. `separation_bound` : Step 2.
5. `qdiff_divisor_lower_E` : Step 3.
6. `schwarz_step` : Step 4 (with the two geometric facts relating `ζ` and `‖S • w - z₀‖`).
7. assembly of the target from Steps 2–5.

**Import constraint.**  `E_jdiff_small` and `KPlusXiDefs` cannot both be imported (duplicate
`Work.Asymptotics.norm_qParamFun_le_one`); this file's closure already contains `KPlusXiDefs`
(via `Xi8_eq`), so `E_jdiff_small` is *not* available here and `divisor_qdiff_lower` (which is on
the `KPlusXiDefs` side, unlike `E_jdiff_small`) plays its role.
-/

/-! ## The divisor is bounded below by the sine form

`Work.Asymptotics.divisor_qdiff_lower` (applied to whichever of `τ`, `z₀` has height `≥ T₀`) with
the trivial upper bound `‖Δ τ‖ ≤ 2 e^{-2π Im τ}` and the sine form of the `q`-difference
(`norm_qParamFun_sub`) gives, for `1 ≤ Im τ`,

  `‖Δ z₀ (j τ - j z₀)‖ ≥ c · e^{π (Im τ - Im z₀)} · ‖sin (π(τ-z₀))‖`. -/
private lemma divisor_lower_sin {c T₀ : ℝ} (hc : 0 < c) (hT₀ : 1 / 3 ≤ T₀)
    (hmain : ∀ a b : ℍ, T₀ ≤ a.im → 1 / 3 ≤ b.im →
      c * ‖Work.Kernels.qParamFun a - Work.Kernels.qParamFun b‖
        ≤ ‖Work.Kernels.DeltaFun a * Work.Kernels.DeltaFun b
            * (Work.Kernels.jInvariantFun a - Work.Kernels.jInvariantFun b)‖)
    {τ z : ℍ} (hτ1 : 1 ≤ τ.im) (hτ13 : 1 / 3 ≤ τ.im) (hz13 : 1 / 3 ≤ z.im)
    (hcase : T₀ ≤ τ.im ∨ T₀ ≤ z.im) :
    c * Real.exp (Real.pi * (τ.im - z.im))
        * ‖Complex.sin (Real.pi * ((τ : ℂ) - (z : ℂ)))‖
      ≤ ‖Work.Kernels.DeltaFun z
          * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := by
  have hΔ : ‖Work.Kernels.DeltaFun τ‖ ≤ 2 * Real.exp (-(2 * Real.pi * τ.im)) :=
    Work.Asymptotics.DeltaFun_upper_sharp τ hτ1
  have hq := norm_qParamFun_sub τ z
  have hlow : c * ‖Work.Kernels.qParamFun τ - Work.Kernels.qParamFun z‖
      ≤ ‖Work.Kernels.DeltaFun τ‖
        * ‖Work.Kernels.DeltaFun z
            * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := by
    rcases hcase with hcase | hcase
    · have h := hmain τ z hcase hz13
      have h2 : ‖Work.Kernels.DeltaFun τ * Work.Kernels.DeltaFun z
            * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖
          = ‖Work.Kernels.DeltaFun τ‖
            * ‖Work.Kernels.DeltaFun z
                * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := by
        rw [mul_assoc, norm_mul]
      rwa [h2] at h
    · have h := hmain z τ hcase hτ13
      have h2 : ‖Work.Kernels.DeltaFun z * Work.Kernels.DeltaFun τ
            * (Work.Kernels.jInvariantFun z - Work.Kernels.jInvariantFun τ)‖
          = ‖Work.Kernels.DeltaFun τ‖
            * ‖Work.Kernels.DeltaFun z
                * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := by
        rw [mul_assoc,
          norm_mul (Work.Kernels.DeltaFun z) (Work.Kernels.DeltaFun τ *
            (Work.Kernels.jInvariantFun z - Work.Kernels.jInvariantFun τ)),
          norm_mul (Work.Kernels.DeltaFun τ)
            (Work.Kernels.jInvariantFun z - Work.Kernels.jInvariantFun τ),
          norm_mul (Work.Kernels.DeltaFun z)
            (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z),
          norm_sub_rev (Work.Kernels.jInvariantFun z) (Work.Kernels.jInvariantFun τ)]
        ring
      rw [norm_sub_rev (Work.Kernels.qParamFun z) (Work.Kernels.qParamFun τ), h2] at h
      exact h
  have hstep : c * (2 * Real.exp (-(Real.pi * (τ.im + z.im)))
        * ‖Complex.sin (Real.pi * ((τ : ℂ) - (z : ℂ)))‖)
      ≤ ‖Work.Kernels.DeltaFun z
            * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖
        * (2 * Real.exp (-(2 * Real.pi * τ.im))) := by
    calc c * (2 * Real.exp (-(Real.pi * (τ.im + z.im)))
          * ‖Complex.sin (Real.pi * ((τ : ℂ) - (z : ℂ)))‖)
        = c * ‖Work.Kernels.qParamFun τ - Work.Kernels.qParamFun z‖ := by rw [hq]
      _ ≤ ‖Work.Kernels.DeltaFun τ‖
            * ‖Work.Kernels.DeltaFun z
                * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := hlow
      _ ≤ (2 * Real.exp (-(2 * Real.pi * τ.im)))
            * ‖Work.Kernels.DeltaFun z
                * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ :=
          mul_le_mul_of_nonneg_right hΔ (norm_nonneg _)
      _ = ‖Work.Kernels.DeltaFun z
              * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖
            * (2 * Real.exp (-(2 * Real.pi * τ.im))) := by rw [mul_comm]
  have hBpos : 0 < 2 * Real.exp (-(2 * Real.pi * τ.im)) := by positivity
  have hexp : Real.exp (Real.pi * (τ.im - z.im)) * (2 * Real.exp (-(2 * Real.pi * τ.im)))
      = 2 * Real.exp (-(Real.pi * (τ.im + z.im))) := by
    rw [show Real.exp (Real.pi * (τ.im - z.im)) * (2 * Real.exp (-(2 * Real.pi * τ.im)))
        = 2 * (Real.exp (Real.pi * (τ.im - z.im))
            * Real.exp (-(2 * Real.pi * τ.im))) from by ring,
      ← Real.exp_add]
    congr 1
    ring
  have hgoal : c * Real.exp (Real.pi * (τ.im - z.im))
        * ‖Complex.sin (Real.pi * ((τ : ℂ) - (z : ℂ)))‖
      = (c * (2 * Real.exp (-(Real.pi * (τ.im + z.im)))
            * ‖Complex.sin (Real.pi * ((τ : ℂ) - (z : ℂ)))‖))
        / (2 * Real.exp (-(2 * Real.pi * τ.im))) := by
    rw [eq_div_iff (ne_of_gt hBpos),
      show (c * Real.exp (Real.pi * (τ.im - z.im))
            * ‖Complex.sin (Real.pi * ((τ : ℂ) - (z : ℂ)))‖)
          * (2 * Real.exp (-(2 * Real.pi * τ.im)))
        = (c * ‖Complex.sin (Real.pi * ((τ : ℂ) - (z : ℂ)))‖)
          * (Real.exp (Real.pi * (τ.im - z.im))
            * (2 * Real.exp (-(2 * Real.pi * τ.im)))) from by ring,
      hexp]
    ring
  rw [hgoal, div_le_iff₀ hBpos]
  exact hstep

/-- **Region II**: if one of `Im (S • w)`, `t⁻¹` is at least `T₀` (so that
`Work.Asymptotics.divisor_qdiff_lower` applies), then Step 1 (`Kaxis_Kfun_divisor_bound`)
together with `divisor_lower_sin` gives a polynomial bound in `scale w` as soon as the sine
`‖sin (π(S • w - i/t))‖` is bounded away from `0`. -/
private lemma region_II_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {c T₀ : ℝ} (hc : 0 < c) (hT₀ : 1 / 3 ≤ T₀)
    (hmain : ∀ a b : ℍ, T₀ ≤ a.im → 1 / 3 ≤ b.im →
      c * ‖Work.Kernels.qParamFun a - Work.Kernels.qParamFun b‖
        ≤ ‖Work.Kernels.DeltaFun a * Work.Kernels.DeltaFun b
            * (Work.Kernels.jInvariantFun a - Work.Kernels.jInvariantFun b)‖)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (w : ℍ) (t : ℝ) (ht : 0 < t),
      w ∈ Work.Asymptotics.KEpsilon → t ≤ 1 →
      Work.Kernels.jInvariantFun w ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) →
      (T₀ ≤ (ModularGroup.S • w).im ∨ T₀ ≤ t⁻¹) →
      ε₀ ≤ ‖Complex.sin (Real.pi * (((ModularGroup.S • w : ℍ) : ℂ)
        - ((Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht) : ℍ) : ℂ)))‖ →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t‖
        ≤ C * (Work.Kernels.scale w) ^ N := by
  obtain ⟨C₁, N₁, hC₁, hN₁, hb⟩ := Kaxis_Kfun_divisor_bound ℓ d hd
  refine ⟨C₁ / (c * ε₀) + 1, N₁, by positivity, hN₁, fun w t ht hw ht1 hjne hcase hsin => ?_⟩
  have hzpos : 0 < t⁻¹ := inv_pos.mpr ht
  set D : ℝ := ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t⁻¹ hzpos)
      * (Work.Kernels.jInvariantFun w
          - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t⁻¹ hzpos))‖ with hDdef
  set e : ℝ := Real.exp (Real.pi * ((ModularGroup.S • w).im - t⁻¹)) with hedef
  have hE : (3 / 2 : ℝ) ≤ (ModularGroup.S • w).im := Work.Asymptotics.E_S_im_ge w hw
  have hy0 : (0 : ℝ) ≤ (ModularGroup.S • w).im := le_trans (by norm_num) hE
  have hSz : ModularGroup.S • Work.Kernels.imagAxis t⁻¹ hzpos
      = Work.Kernels.imagAxis t ht := S_smul_imagAxis_inv ht
  have hjz : Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t⁻¹ hzpos)
      = Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) := by
    have h := (Work.Asymptotics.EtailE.jInvariantFun_Ssmul
      (Work.Kernels.imagAxis t⁻¹ hzpos)).symm
    rw [hSz] at h
    exact h
  have him : (Work.Kernels.imagAxis t⁻¹ hzpos).im = t⁻¹ := by
    simp [Work.Kernels.imagAxis]
  have hcase' : T₀ ≤ (ModularGroup.S • w).im
      ∨ T₀ ≤ (Work.Kernels.imagAxis t⁻¹ hzpos).im := by
    rcases hcase with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [him]; exact h)
  have hDlow : c * e * ε₀ ≤ D := by
    have h := divisor_lower_sin hc hT₀ hmain
      (τ := ModularGroup.S • w) (z := Work.Kernels.imagAxis t⁻¹ hzpos)
      (le_trans (by norm_num) hE) (le_trans (by norm_num) hE)
      (by rw [him]; exact le_trans (by norm_num) ((one_le_inv₀ ht).mpr ht1)) hcase'
    rw [him, ← hedef, Work.Asymptotics.EtailE.jInvariantFun_Ssmul w, ← hDdef] at h
    exact le_trans (mul_le_mul_of_nonneg_left hsin (by positivity)) h
  have hDpos : 0 < D := lt_of_lt_of_le (by positivity) hDlow
  have htpow : t ^ ((d : ℤ) / 2 - 4) ≤ 1 := by
    rcases hd with rfl | rfl
    · have h0 : (((8 : ℕ)) : ℤ) / 2 - 4 = 0 := by norm_num
      rw [h0, zpow_zero]
    · have h8 : (((24 : ℕ)) : ℤ) / 2 - 4 = 8 := by norm_num
      rw [h8, zpow_ofNat]
      exact pow_le_one₀ ht.le ht1
  have hn : t ^ ((d : ℤ) / 2 - 4) * Real.exp (-(Real.pi / t)) ≤ e := by
    rw [hedef]
    refine le_trans (mul_le_of_le_one_left (Real.exp_nonneg _) htpow) ?_
    rw [Real.exp_le_exp, div_eq_mul_inv, mul_sub]
    nlinarith [Real.pi_pos, hy0]
  have hA0 : 0 ≤ C₁ * (Work.Kernels.scale w) ^ N₁ :=
    mul_nonneg hC₁.le (Real.rpow_nonneg (le_trans (by norm_num)
      (Work.Kernels.one_le_scale w)) _)
  have hepos : 0 < e := Real.exp_pos _
  have hce : 0 < c * e * ε₀ := by positivity
  have hgroup : C₁ * (Work.Kernels.scale w) ^ N₁ * t ^ ((d : ℤ) / 2 - 4)
        * Real.exp (-(Real.pi / t)) / D
      = C₁ * (Work.Kernels.scale w) ^ N₁ * (t ^ ((d : ℤ) / 2 - 4)
          * Real.exp (-(Real.pi / t))) / D := by ring
  have h3 : C₁ * (Work.Kernels.scale w) ^ N₁
        * (t ^ ((d : ℤ) / 2 - 4) * Real.exp (-(Real.pi / t))) / D
      ≤ C₁ * (Work.Kernels.scale w) ^ N₁ * e / D :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hn hA0) (le_of_lt hDpos)
  have h4 : C₁ * (Work.Kernels.scale w) ^ N₁ * e / D
      ≤ C₁ * (Work.Kernels.scale w) ^ N₁ * e / (c * e * ε₀) :=
    div_le_div_of_nonneg_left (by positivity) hce hDlow
  have h5 : C₁ * (Work.Kernels.scale w) ^ N₁ * e / (c * e * ε₀)
      = C₁ * (Work.Kernels.scale w) ^ N₁ / (c * ε₀) := by
    field_simp
  have hA1 : C₁ * (Work.Kernels.scale w) ^ N₁ / (c * ε₀)
      ≤ (C₁ / (c * ε₀) + 1) * (Work.Kernels.scale w) ^ N₁ := by
    have h6 : C₁ * (Work.Kernels.scale w) ^ N₁ / (c * ε₀)
        = C₁ / (c * ε₀) * (Work.Kernels.scale w) ^ N₁ := by ring
    rw [h6]
    exact mul_le_mul_of_nonneg_right (by linarith)
      (Real.rpow_nonneg (le_trans (by norm_num) (Work.Kernels.one_le_scale w)) _)
  have h1 := hb w t ht (Work.Asymptotics.E_S_im_ge w hw) ht1 hjne
  calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t‖
      ≤ C₁ * (Work.Kernels.scale w) ^ N₁ * t ^ ((d : ℤ) / 2 - 4)
          * Real.exp (-(Real.pi / t)) / D := h1
    _ = C₁ * (Work.Kernels.scale w) ^ N₁
          * (t ^ ((d : ℤ) / 2 - 4) * Real.exp (-(Real.pi / t))) / D := hgroup
    _ ≤ C₁ * (Work.Kernels.scale w) ^ N₁ * e / D := h3
    _ ≤ C₁ * (Work.Kernels.scale w) ^ N₁ * e / (c * e * ε₀) := h4
    _ = C₁ * (Work.Kernels.scale w) ^ N₁ / (c * ε₀) := h5
    _ ≤ (C₁ / (c * ε₀) + 1) * (Work.Kernels.scale w) ^ N₁ := hA1

/-- On `[-π, π]`, `sin |x| = |sin x|`. -/
lemma sin_abs_of_abs_le_pi {x : ℝ} (hx : |x| ≤ Real.pi) : Real.sin |x| = |Real.sin x| := by
  have hxπ : x ≤ Real.pi := le_trans (le_abs_self x) hx
  have hxπ' : -Real.pi ≤ x := by
    have h := neg_le_abs x
    linarith
  rcases abs_choice x with hh | hh
  · have hx0 : 0 ≤ x := by rw [← hh]; exact abs_nonneg x
    rw [hh, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hx0 hxπ)]
  · have hx0 : x ≤ 0 := by have := le_abs_self x; rw [hh] at this; linarith
    rw [hh, Real.sin_neg, abs_of_nonpos (Real.sin_nonpos_of_nonpos_of_neg_pi_le hx0 hxπ')]

/-- `sinh |x| = |sinh x|`. -/
lemma sinh_abs (x : ℝ) : Real.sinh |x| = |Real.sinh x| := by
  rcases abs_choice x with hh | hh
  · have hx0 : 0 ≤ x := by rw [← hh]; exact abs_nonneg x
    rw [hh, abs_of_nonneg (Real.sinh_nonneg_iff.mpr hx0)]
  · have hx0 : x ≤ 0 := by have := le_abs_self x; rw [hh] at this; linarith
    have hs : Real.sinh x ≤ 0 := by
      have h1 : 0 ≤ Real.sinh (-x) := Real.sinh_nonneg_iff.mpr (by linarith)
      rw [Real.sinh_neg] at h1
      linarith
    rw [hh, Real.sinh_neg, abs_of_nonpos hs]

/-- **The sine is at least linear near a multiple of `π`.**  For `‖w‖ ≤ 1/3` and `m : ℤ`,
`2 ‖w‖ ≤ ‖sin (π (m + w))‖`. -/
private lemma two_mul_norm_le_norm_sin_pi_int_add (m : ℤ) {w : ℂ} (hw : ‖w‖ ≤ 1 / 3) :
    2 * ‖w‖ ≤ ‖Complex.sin (Real.pi * ((m : ℂ) + w))‖ := by
  have hre : (Real.pi * ((m : ℂ) + w)).re = Real.pi * ((m : ℝ) + w.re) := by
    simp [Complex.mul_re, Complex.add_re]
  have him : (Real.pi * ((m : ℂ) + w)).im = Real.pi * w.im := by
    simp [Complex.mul_im, Complex.add_im]
  have hsq := norm_sin_sq (Real.pi * ((m : ℂ) + w))
  rw [hre, him] at hsq
  have h1 : Real.sin (Real.pi * ((m : ℝ) + w.re)) ^ 2 = Real.sin (Real.pi * w.re) ^ 2 := by
    rw [show Real.pi * ((m : ℝ) + w.re) = Real.pi * w.re + (m : ℝ) * Real.pi by ring,
      Real.sin_add_int_mul_pi]
    have habs : |(-1 : ℝ) ^ m| = 1 := by rw [abs_zpow]; norm_num
    rw [show ((-1 : ℝ) ^ m * Real.sin (Real.pi * w.re)) ^ 2
        = |(-1 : ℝ) ^ m * Real.sin (Real.pi * w.re)| ^ 2 from (sq_abs _).symm,
      abs_mul, habs, one_mul, sq_abs]
  rw [h1] at hsq
  have hwr : |w.re| ≤ 1 / 3 := le_trans (Complex.abs_re_le_norm w) hw
  have hwi : |w.im| ≤ 1 / 3 := le_trans (Complex.abs_im_le_norm w) hw
  have h2 : 4 * w.re ^ 2 ≤ Real.sin (Real.pi * w.re) ^ 2 := by
    have h3 : |Real.pi * w.re| ≤ Real.pi / 2 := by
      rw [abs_mul, abs_of_pos Real.pi_pos]
      nlinarith [hwr, Real.pi_pos]
    have h4 := Real.mul_le_sin (abs_nonneg (Real.pi * w.re)) h3
    rw [sin_abs_of_abs_le_pi (le_trans h3 (by linarith [Real.pi_pos]))] at h4
    have h5 : 2 * |w.re| ≤ |Real.sin (Real.pi * w.re)| := by
      have h6 : 2 / Real.pi * |Real.pi * w.re| = 2 * |w.re| := by
        rw [abs_mul, abs_of_pos Real.pi_pos]
        field_simp
      linarith [h4, h6]
    have h6 : (2 * |w.re|) ^ 2 ≤ |Real.sin (Real.pi * w.re)| ^ 2 :=
      pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2 * |w.re|) h5 2
    rw [mul_pow, sq_abs, sq_abs] at h6
    nlinarith [h6]
  have h3 : 4 * w.im ^ 2 ≤ Real.sinh (Real.pi * w.im) ^ 2 := by
    have h4 : |Real.pi * w.im| ≤ Real.sinh |Real.pi * w.im| :=
      (Real.self_le_sinh_iff (x := |Real.pi * w.im|)).mpr (abs_nonneg _)
    have h5 : |Real.sinh (Real.pi * w.im)| = Real.sinh |Real.pi * w.im| := Real.abs_sinh _
    rw [← h5, abs_mul, abs_of_pos Real.pi_pos] at h4
    have h7 : 2 * |w.im| ≤ |Real.sinh (Real.pi * w.im)| := by
      nlinarith [h4, Real.pi_gt_three, abs_nonneg w.im]
    have h8 : (2 * |w.im|) ^ 2 ≤ |Real.sinh (Real.pi * w.im)| ^ 2 :=
      pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2 * |w.im|) h7 2
    rw [mul_pow, sq_abs, sq_abs] at h8
    nlinarith [h8]
  have hfin : (2 * ‖w‖) ^ 2 ≤ ‖Complex.sin (Real.pi * ((m : ℂ) + w))‖ ^ 2 := by
    have hw2 : (2 * ‖w‖) ^ 2 = 4 * (w.re ^ 2 + w.im ^ 2) := by
      rw [mul_pow, Complex.sq_norm, Complex.normSq_apply]
      ring
    rw [hw2, hsq]
    nlinarith [h2, h3]
  nlinarith [hfin, norm_nonneg (Complex.sin (Real.pi * ((m : ℂ) + w))), norm_nonneg w]

/-- **The bad case is geometrically a neighbourhood of an explicit zero.**  If
`‖sin (π(τ - z₀))‖ < ε` with `0 < ε`, then `τ` is within `ε (1/2 + 1/π)` of `z₀ + m` for some
integer `m`.  No hypothesis on `τ.re`, `z₀.re` is needed, and no bound on `|m|`: the vanishing
`KfunClear_cuspParabolic_vanishing` holds at `S • ((m:ℝ) +ᵥ S • z)` for *every* `m : ℤ`. -/
lemma exists_near_shift {τ z₀ : ℍ} {ε : ℝ} (hε : 0 < ε)
    (h : ‖Complex.sin (Real.pi * ((τ : ℂ) - (z₀ : ℂ)))‖ < ε) :
    ∃ m : ℤ, ‖(τ : ℂ) - ((z₀ : ℂ) + (m : ℂ))‖ ≤ ε * (1 / 2 + 1 / Real.pi) := by
  set d : ℂ := (τ : ℂ) - (z₀ : ℂ) with hd
  have hsq := norm_sin_pi_sub τ z₀
  rw [← hd] at hsq
  have hlt2 : ‖Complex.sin (Real.pi * d)‖ ^ 2 < ε ^ 2 :=
    by nlinarith [h, hε, norm_nonneg (Complex.sin (Real.pi * d))]
  have hsin2 : Real.sin (Real.pi * d.re) ^ 2 < ε ^ 2 :=
    by nlinarith [hsq, hlt2, sq_nonneg (Real.sinh (Real.pi * d.im))]
  have hsinh2 : Real.sinh (Real.pi * d.im) ^ 2 < ε ^ 2 :=
    by nlinarith [hsq, hlt2, sq_nonneg (Real.sin (Real.pi * d.re))]
  have hsin : |Real.sin (Real.pi * d.re)| < ε := by
    have h' := (sq_lt_sq).mp hsin2
    rwa [abs_of_pos hε] at h'
  have hsinh : |Real.sinh (Real.pi * d.im)| < ε := by
    have h' := (sq_lt_sq).mp hsinh2
    rwa [abs_of_pos hε] at h'
  set m : ℤ := ⌊d.re + 1 / 2⌋ with hm
  have hm1 : ((m : ℤ) : ℝ) ≤ d.re + 1 / 2 := Int.floor_le _
  have hm2 : d.re + 1 / 2 < ((m : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  have hdrem : |d.re - ((m : ℤ) : ℝ)| ≤ 1 / 2 := by
    have h1 : -((1 : ℝ) / 2) ≤ d.re - ((m : ℤ) : ℝ) := by
      have := hm1; linarith
    have h2 : d.re - ((m : ℤ) : ℝ) ≤ (1 : ℝ) / 2 := by
      have := hm2; linarith
    exact abs_le.mpr ⟨h1, h2⟩
  have hper : |Real.sin (Real.pi * d.re)| = |Real.sin (Real.pi * (d.re - ((m : ℤ) : ℝ)))| := by
    have hsplit : Real.pi * d.re
        = Real.pi * (d.re - ((m : ℤ) : ℝ)) + ((m : ℤ) : ℝ) * Real.pi := by ring
    rw [hsplit, Real.sin_add_int_mul_pi, abs_mul,
      show |((-1 : ℝ)) ^ m| = 1 by rw [abs_zpow]; norm_num, one_mul]
  have hpi : |Real.pi * (d.re - ((m : ℤ) : ℝ))| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    have h := mul_le_mul_of_nonneg_left hdrem Real.pi_pos.le
    linarith
  have hquarter : |d.re - ((m : ℤ) : ℝ)| ≤ |Real.sin (Real.pi * (d.re - ((m : ℤ) : ℝ)))| / 2 := by
    have h2 : (2 / Real.pi) * |Real.pi * (d.re - ((m : ℤ) : ℝ))|
        ≤ Real.sin |Real.pi * (d.re - ((m : ℤ) : ℝ))| := Real.mul_le_sin (abs_nonneg _) hpi
    rw [sin_abs_of_abs_le_pi (le_trans hpi (by linarith [Real.pi_pos]))] at h2
    have h4 : (2 / Real.pi) * |Real.pi * (d.re - ((m : ℤ) : ℝ))|
        = 2 * |d.re - ((m : ℤ) : ℝ)| := by
      simp only [abs_mul, abs_of_pos Real.pi_pos]
      field_simp
    rw [h4] at h2
    linarith
  have hre_bound : |d.re - ((m : ℤ) : ℝ)| ≤ ε / 2 := by
    rw [hper] at hsin
    linarith
  have him_bound : |d.im| ≤ ε / Real.pi := by
    have h2 : Real.pi * |d.im| ≤ |Real.sinh (Real.pi * d.im)| := by
      have h2' : |Real.pi * d.im| ≤ Real.sinh |Real.pi * d.im| :=
        Real.self_le_sinh_iff.mpr (abs_nonneg _)
      rw [sinh_abs] at h2'
      rw [abs_mul, abs_of_pos Real.pi_pos] at h2'
      linarith
    rw [le_div_iff₀ Real.pi_pos, mul_comm (|d.im|) Real.pi]
    exact le_of_lt (lt_of_le_of_lt h2 hsinh)
  refine ⟨m, ?_⟩
  have hcoe : (τ : ℂ) - ((z₀ : ℂ) + (m : ℂ)) = d - ((m : ℤ) : ℂ) := by rw [hd]; ring
  have hre : (d - ((m : ℤ) : ℂ)).re = d.re - ((m : ℤ) : ℝ) := by simp
  have him : (d - ((m : ℤ) : ℂ)).im = d.im := by simp
  rw [hcoe]
  calc ‖d - ((m : ℤ) : ℂ)‖ ≤ |(d - ((m : ℤ) : ℂ)).re| + |(d - ((m : ℤ) : ℂ)).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ = |d.re - ((m : ℤ) : ℝ)| + |d.im| := by rw [hre, him]
    _ ≤ ε / 2 + ε / Real.pi := add_le_add hre_bound him_bound
    _ = ε * (1 / 2 + 1 / Real.pi) := by ring

/-! ## Bounds for `‖Δ u‖` in terms of the height of `S • u`

These are the two halves of the `S`-law `Δ u = (S u)^{12} Δ(S u)` combined with the cusp bounds
`DeltaFun_upper_sharp` (upper) and `delta_lower_third` (lower) at the point `S • u`.  They are
exactly what the one-zero assembly at `w_m` needs: `M` carries a factor `‖Δ (i t)‖^e`, and the
cancellation against `divisor_lower_sin` needs `‖Δ u‖` comparable with `e^{-2π Im (S u)}`. -/

/-- `‖Δ u‖ ≤ 2 ‖u‖^{-12} e^{-2π Im (S • u)}` when `1 ≤ Im (S • u)`. -/
lemma norm_DeltaFun_le_of_im {u : ℍ} (hu : 1 ≤ (ModularGroup.S • u).im) :
    ‖Work.Kernels.DeltaFun u‖
      ≤ 2 * (‖(u : ℂ)‖ ^ (-(12 : ℤ)))
          * Real.exp (-(2 * Real.pi * (ModularGroup.S • u).im)) := by
  have hb := Work.Asymptotics.DeltaFun_upper_sharp (ModularGroup.S • u) hu
  have hslaw := Work.Asymptotics.DeltaFun_S_smul' u
  have hnorm : ‖(((ModularGroup.S • u : ℍ)) : ℂ)‖ = (‖(u : ℂ)‖)⁻¹ := by
    rw [Work.Kernels.S_smul_coe, norm_neg, norm_inv]
  have hpow : ((‖(u : ℂ)‖)⁻¹) ^ 12 = ‖(u : ℂ)‖ ^ (-(12 : ℤ)) := by
    rw [inv_pow, _root_.zpow_neg, zpow_ofNat]
  rw [hslaw, norm_mul, norm_pow, hnorm, hpow]
  calc ‖(u : ℂ)‖ ^ (-(12 : ℤ)) * ‖Work.Kernels.DeltaFun (ModularGroup.S • u)‖
      ≤ ‖(u : ℂ)‖ ^ (-(12 : ℤ))
          * (2 * Real.exp (-(2 * Real.pi * (ModularGroup.S • u).im))) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = 2 * (‖(u : ℂ)‖ ^ (-(12 : ℤ)))
          * Real.exp (-(2 * Real.pi * (ModularGroup.S • u).im)) := by ring

/-- `c ‖u‖^{-12} e^{-2π Im (S • u)} ≤ ‖Δ u‖` when `1/3 ≤ Im (S • u)`. -/
lemma norm_DeltaFun_ge_of_im {c : ℝ} (hc : 0 < c)
    (hlow : ∀ z : ℍ, 1 / 3 ≤ z.im → c * ‖Work.Kernels.qParamFun z‖ ≤ ‖Work.Kernels.DeltaFun z‖)
    {u : ℍ} (hu : 1 / 3 ≤ (ModularGroup.S • u).im) :
    c * (‖(u : ℂ)‖ ^ (-(12 : ℤ))
        * Real.exp (-(2 * Real.pi * (ModularGroup.S • u).im)))
      ≤ ‖Work.Kernels.DeltaFun u‖ := by
  have h := hlow (ModularGroup.S • u) hu
  rw [Work.Asymptotics.norm_qParamFun] at h
  have hslaw := Work.Asymptotics.DeltaFun_S_smul' u
  have hnorm : ‖(((ModularGroup.S • u : ℍ)) : ℂ)‖ = (‖(u : ℂ)‖)⁻¹ := by
    rw [Work.Kernels.S_smul_coe, norm_neg, norm_inv]
  have hpow : ((‖(u : ℂ)‖)⁻¹) ^ 12 = ‖(u : ℂ)‖ ^ (-(12 : ℤ)) := by
    rw [inv_pow, _root_.zpow_neg, zpow_ofNat]
  rw [hslaw, norm_mul, norm_pow, hnorm, hpow]
  calc c * (‖(u : ℂ)‖ ^ (-(12 : ℤ))
        * Real.exp (-(2 * Real.pi * (ModularGroup.S • u).im)))
      = ‖(u : ℂ)‖ ^ (-(12 : ℤ))
          * (c * Real.exp (-(2 * Real.pi * (ModularGroup.S • u).im))) := by ring
    _ ≤ ‖(u : ℂ)‖ ^ (-(12 : ℤ))
          * ‖Work.Kernels.DeltaFun (ModularGroup.S • u)‖ :=
        mul_le_mul_of_nonneg_left h (by positivity)

/-- **The one-zero ball stays in the tile `{3/2 ≤ Im (S • ·)}`.**

For `u` within `w_m.im/100` of `w_m`, both the height of `u` and its size are pinned to those of
`w_m` within `1` percent, so `Im (S • u) ≥ (99/100)(100/101)² Im (S • w_m) > 0.97 Im (S • w_m)`
(the factors `(101/100)²` from the size and `(100/101)²` cancel exactly).  In the bad case
`Im (S • w_m) = 1/t` with `t < 1/(2-ε₀/π) < 0.53`, so this exceeds `3/2`, i.e. Step 1 applies on
the whole ball. -/
lemma S_im_ge_of_ball {w_m u : ℍ} {r : ℝ} (hr : r ≤ w_m.im / 100)
    (hdist : ‖(u : ℂ) - (w_m : ℂ)‖ ≤ r) :
    (99 / 100) * (100 / 101) ^ 2 * (ModularGroup.S • w_m).im ≤ (ModularGroup.S • u).im := by
  have hrpos : 0 < w_m.im := w_m.im_pos
  -- heights
  have him : w_m.im - r ≤ u.im := by
    have h := Complex.abs_im_le_norm ((u : ℂ) - (w_m : ℂ))
    have h2 : ((u : ℂ) - (w_m : ℂ)).im = u.im - w_m.im := by simp
    have h3 : -(((u : ℂ) - (w_m : ℂ)).im) ≤ ‖(u : ℂ) - (w_m : ℂ)‖ :=
      le_trans (neg_le_abs (((u : ℂ) - (w_m : ℂ)).im)) h
    linarith [h3, hdist, h2]
  have huim : (99 / 100) * w_m.im ≤ u.im := by nlinarith [him, hrpos, hr]
  -- sizes
  have hu_norm : ‖(u : ℂ)‖ ≤ (101 / 100) * ‖(w_m : ℂ)‖ := by
    have h1 : ‖(u : ℂ)‖ ≤ ‖(w_m : ℂ)‖ + ‖(u : ℂ) - (w_m : ℂ)‖ := by
      have h := norm_add_le ((w_m : ℂ)) ((u : ℂ) - (w_m : ℂ))
      rw [add_sub_cancel] at h
      exact h
    have h2 : r ≤ (1 / 100) * ‖(w_m : ℂ)‖ := by
      have h3 := Work.Kernels.im_le_coe_norm w_m
      linarith
    linarith
  have hsq : ‖(u : ℂ)‖ ^ 2 ≤ ((101 / 100) * ‖(w_m : ℂ)‖) ^ 2 :=
    by nlinarith [hu_norm, norm_nonneg (u : ℂ), norm_nonneg (w_m : ℂ)]
  -- reduce to a real inequality
  rw [EReg_S_im u, EReg_S_im w_m, le_div_iff₀ (pow_pos (norm_pos_iff.mpr u.ne_zero) 2)]
  have hA : (0 : ℝ) ≤ (99 / 100) * (100 / 101) ^ 2 * (w_m.im / ‖(w_m : ℂ)‖ ^ 2) := by
    have hnn : (0 : ℝ) < ‖(w_m : ℂ)‖ ^ 2 := pow_pos (norm_pos_iff.mpr w_m.ne_zero) 2
    positivity
  have hnn' : ‖(w_m : ℂ)‖ ^ 2 ≠ 0 := (pow_pos (norm_pos_iff.mpr w_m.ne_zero) 2).ne'
  have h2 : (w_m.im / ‖(w_m : ℂ)‖ ^ 2) * ((101 / 100) * ‖(w_m : ℂ)‖) ^ 2
      = (101 / 100 : ℝ) ^ 2 * w_m.im := by
    rw [show ((101 / 100) * ‖(w_m : ℂ)‖) ^ 2 = (101 / 100) ^ 2 * ‖(w_m : ℂ)‖ ^ 2 by ring,
      div_mul_eq_mul_div, div_eq_iff hnn']
    try ring
  have h3 : (100 / 101 : ℝ) ^ 2 * ((101 / 100 : ℝ) ^ 2 * w_m.im) = w_m.im := by
    field_simp
    try ring
  calc (99 / 100) * (100 / 101) ^ 2 * (w_m.im / ‖(w_m : ℂ)‖ ^ 2) * ‖(u : ℂ)‖ ^ 2
      ≤ (99 / 100) * (100 / 101) ^ 2 * (w_m.im / ‖(w_m : ℂ)‖ ^ 2)
          * ((101 / 100) * ‖(w_m : ℂ)‖) ^ 2 := mul_le_mul_of_nonneg_left hsq hA
    _ = (99 / 100) * ((100 / 101) ^ 2 * ((w_m.im / ‖(w_m : ℂ)‖ ^ 2)
          * ((101 / 100) * ‖(w_m : ℂ)‖) ^ 2)) := by ring
    _ = (99 / 100) * ((100 / 101) ^ 2 * ((101 / 100 : ℝ) ^ 2 * w_m.im)) := by rw [h2]
    _ = (99 / 100) * w_m.im := by rw [h3]
    _ ≤ u.im := huim

/-- **Piece (A) of the `M`-bound: the identity `KfunClear = growthPrefactor · Kfun`.**

`‖KfunClear u z_c‖ ‖Δ z₀‖` equals `(‖Kfun u z_c‖ (‖Δ z₀‖ ‖j u - j z₀‖)) (‖Δ u‖ ‖Δ z_c‖^e)` — i.e.
the cleared kernel is the kernel *times* the growth prefactor, with the `‖j‖`-factor re-expressed
at `z₀` (using `j z₀ = j z_c`).  The right-hand grouping is chosen to match what the Step-1
application (piece (B)) multiplies through, so the final combination needs no large `ring`. -/
private lemma KfunClear_norm_eq (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {u z_c z₀ : ℍ}
    (hne : Work.Kernels.jInvariantFun u ≠ Work.Kernels.jInvariantFun z_c)
    (hj : Work.Kernels.jInvariantFun z₀ = Work.Kernels.jInvariantFun z_c) :
    ‖Work.Kernels.KfunClear ℓ d u z_c‖ * ‖Work.Kernels.DeltaFun z₀‖
      = (‖Work.Kernels.Kfun ℓ d u z_c‖
          * (‖Work.Kernels.DeltaFun z₀‖
            * ‖Work.Kernels.jInvariantFun u - Work.Kernels.jInvariantFun z₀‖))
        * (‖Work.Kernels.DeltaFun u‖
            * ‖Work.Kernels.DeltaFun z_c‖ ^ (if d = 8 then 1 else 2)) := by
  have hgp0 : Work.Kernels.growthPrefactor d u z_c ≠ 0 := by
    simp only [Work.Kernels.growthPrefactor]
    exact mul_ne_zero
      (mul_ne_zero (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero _)
        (pow_ne_zero _ (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero _)))
      (sub_ne_zero.mpr hne)
  have hker : Work.Kernels.KfunClear ℓ d u z_c
      = Work.Kernels.Kfun ℓ d u z_c * Work.Kernels.growthPrefactor d u z_c := by
    have h := Work.Asymptotics.KL.Kfun_eq_KfunClear_div ℓ d hd u z_c hne
    rw [h, div_mul_cancel₀ _ hgp0]
  have hjit : ‖Work.Kernels.jInvariantFun u - Work.Kernels.jInvariantFun z_c‖
      = ‖Work.Kernels.jInvariantFun u - Work.Kernels.jInvariantFun z₀‖ := by rw [← hj]
  rw [hker, norm_mul, Work.Asymptotics.KL.norm_growthPrefactor, hjit]
  ring

/-! ## PROGRESS LOG (updated) — read this first

**Builds now** (`lake build Submission.Work.Asymptotics.Kaxis_Kfun_noncoincidence_E`, rc = 0) with
exactly one real `sorry` = the target.  Newly proved and *available in this file*:

* `qParamFun_sub`           : `q τ - q ζ = e^{πi(τ+ζ)} · 2i sin(π(τ-ζ))`.
* `norm_qParamFun_sub`      : `‖q τ - q ζ‖ = 2 e^{-π(Im τ + Im ζ)} ‖sin (π(τ-ζ))‖`.
* `norm_sin_sq`             : `‖sin z‖² = sin(z.re)² + sinh(z.im)²`.
* `norm_sin_pi_sub`         : the previous two composed for `z = π(τ-ζ)`.
* `factor_le`, `S_smul_imagAxis_inv`, `divisor_bound_abstract`, `Kaxis_Kfun_divisor_bound`
  (Step 1: the divisor form), `one_zero_bound` (Schwarz one-zero), `T2_vanish_orbit`,
  `{KPlus,KMinus,Kfun}Clear_cuspParabolic_vanishing` (vanishing of the cleared kernel at
  `S • ((m:ℝ) +ᵥ (S • z))`, `m : ℤ`), `im_le_of_near_diag`, `scale_mul_t_ge`,
  `DeltaFun_mul_jDiff_lower_E_of`, `Kaxis_Kfun_le_of_compact`, `{KPlus,KMinus}Clear_S_smul`.

### The remaining proof of the target, concretely

Notation: `τ := S • w`, `z₀ := i/t`, `y := Im τ ≥ 2` (since `w ∈ E`), `D := ‖Δ z₀ · (j w - j z₀)‖`.

1. **`t ≤ δ₀`** (`δ₀` from `Kaxis_cusp_of_bounded ℓ d hd` applied to the bounded set
   `KEpsilon`, with `N = 0`): a constant bound; no `nd`/non-coincidence needed.  (`KEpsilon` is
   bounded because it lies in `‖w - i/4‖ ≤ 1/4`.)
2. **`t > δ₀`**, obtain `⟨c, T₀, hc, hT₀, hdiv⟩ := divisor_qdiff_lower` (hypotheses `T₀ ≤ a.im`,
   `1/3 ≤ b.im`).  Note `w.im ≤ 1/2` and `t ≤ 1`, so `divisor_qdiff_lower` is *never* applicable
   to the pair `(w, i t)`; only `(S•w, i/t)` and its reverse can qualify.  Hence the split:
   * (**Region II**) `T₀ ≤ y` or `T₀ ≤ 1/t`: `divisor_lower_sin` (see below) gives
     `D ≥ c e^{π(y-1/t)} ‖sin(π(τ-z₀))‖`.  With Step 1,
     `‖Kaxis (Kfun ℓ d) w t‖ ≤ C (scale w)^N t^{d/2-4} e^{-π/t} / D`, and
     `t^{d/2-4} ≤ 1`, `e^{-π/t} e^{-π(y-1/t)} = e^{-πy} ≤ e^{-2π}`; so if
     `‖sin(π(τ-z₀))‖ ≥ ε₀ > 0` the bound is `≤ (C/(c ε₀)) (scale w)^N`.
   * (**Region III**) `y < T₀` and `1/t < T₀`: then `w.im = y/|w|² ≥ 2/(1+T₀²)`, so `scale w` is
     *bounded* (a constant bound suffices).  Here the elementary inequality
     `‖j τ - j z₀‖ ≥ ‖q τ - q z₀‖(e^{2π(y+1/t)} - C_lip)` applies with `C_lip` the Lipschitz
     constant of `ε = j - q⁻¹ - 744` on the disc `‖q‖ ≤ e^{-2π}`; the needed sharp constant
     (`≈ 2.8e5`, from Cauchy on the disc of radius `2e^{-2π}`) satisfies
     `2 C_lip ≤ e^{6π}`, so again `D ≥ c ε₀` when `‖sin‖ ≥ ε₀`.  (Alternatively handle Region III
     by compactness: the closed set `closure 𝒟 ∩ {2 ≤ Im ≤ T₀}` is compact in `ℍ`, the only
     coincidences with `j z₀` there are `τ = i/t + b`, `b ∈ {-1,0,1}` — an elementary
     `Im γ(i/t) = t/(c²+d²t²)` computation — and those have `sin(π(τ-z₀)) = 0`.)
   * (**bad case**) `‖sin(π(τ-z₀))‖ < ε₀`: with `m := round (Re τ) ∈ {-1,0,1}` (because
     `|Re τ| < 1`) one has `|τ - (z₀+m)|` small, i.e. `w` is close to the *obvious zero*
     `w_m := S • ((m:ℝ) +ᵥ z₀) = S • (i/t + m)` of `τ ↦ KfunClear ℓ d τ (i t)`
     (`KfunClear_cuspParabolic_vanishing` with `z := imagAxis t ht`), and the one-zero estimate
     `one_zero_bound` at `w_m` gives
     `‖Kfun(w,it)‖ ≤ (2M/r) |w-w_m| / (‖Δ w‖ ‖Δ(it)‖^e ‖j w - j(it)‖)`;
     `|w-w_m|` cancels against the lower bound for `‖j w - j it‖` (from `divisor_lower_sin`
     applied through `sin ≈ π|τ-(z₀+m)| = π|w-w_m| |τ| |z₀+m|`, valid in the bad case because
     `y ≈ 1/t`, so `e^{π(y-1/t)} ≈ 1` and the extra factor `e^{2π/t}` from `|Δ(i/t)| ≈ e^{-2π/t}`
     cancels the `e^{-2π/t}` of `M`).  The ball radius `r` must satisfy `B(w_m,r) ⊆ {Im(S·) ≥ 3/2}`
     for Step 1 to bound `M`; in the bad case `y ≈ 1/t`, so this holds as soon as `t ≤ 1/2`
     (and `t > 1/2` is impossible in the bad case, because there `y ≥ 2 > 1/t`).
     Bounds used: `‖Δ u‖ ≥ c e^{-2π Im(S u)}` for `Im(S u) ≥ 1/3` (from `delta_lower_third` and
     the `S`-law `ΔFun_S_smul`), `‖Δ(it)‖^e` similarly, and
     `‖j'(w_m)‖ ≍ |j'(i/t)| |i/t+m|² ≍ e^{2π/t} t^{-2} · (m²+1/t²)`.
3. Assemble: the cusp bound is `≤ c_cusp ≤ c(scale w)^{N'}` since `scale w ≥ 1`.

### UPDATE (Region II DONE)

* `divisor_lower_sin` **done**.
* `region_II_bound` **done**: for fixed `c, T₀` from `divisor_qdiff_lower` and any `ε₀ > 0` there
  are `C, N` with
  `‖Kaxis (Kfun ℓ d) w t‖ ≤ C (scale w)^N` whenever `w ∈ KEpsilon`, `t ≤ 1`, non-coincidence,
  `T₀ ≤ Im (S•w) ∨ T₀ ≤ t⁻¹`, and `ε₀ ≤ ‖sin (π (S•w - i/t))‖`.
* The helper lemmas `qParamFun_sub`, `norm_qParamFun_sub`, `norm_sin_sq`, `norm_sin_pi_sub` are
  **done** as well.

**Two corrections to the plan above.**

1. `w ∈ KEpsilon` is literally `w ∈ DomainD ∧ 2 ≤ Im (S•w)` (`KEpsilon`'s definition), so use
   `hw.2` for `Im (S•w) ≥ 2`; `E_S_im_ge` only gives the weaker `3/2 ≤ Im (S•w)`.
2. `KEpsilon` is *not* bounded in the hyperbolic metric (it contains the cusp `0`: for
   `w = iε`, `dist (i/4) w → ∞`), so `Kaxis_cusp_of_bounded` may **not** be applied to
   `K = KEpsilon`.  This costs nothing: if `t` is small then, by `im_le_of_near_diag` (which
   needs `c₀ ≤ 1/2` — available, since `c₀` is ours to choose) together with the `E`-condition
   `‖w‖² ≤ w.im/2` (equivalently `2 ≤ Im (S•w)`), one gets
   `y = Im (S•w) ≥ 2 / (t (1+c₀))`, so `y ≥ T₀` as soon as `t ≤ 2/(T₀(1+c₀))`.  Hence the small-`t`
   region is *automatically* Region II, and no separate cusp lemma is needed.

**DONE: `exists_near_shift`, `sin_abs_of_abs_le_pi`, `sinh_abs`.**

`exists_near_shift {τ z₀ : ℍ} {ε : ℝ} (hε : 0 < ε) (h : ‖sin (π(τ - z₀))‖ < ε) :
  ∃ m : ℤ, ‖(τ : ℂ) - ((z₀ : ℂ) + (m : ℂ))‖ ≤ ε * (1/2 + 1/π)`

is proved (no hypothesis on `τ.re`, `z₀.re`, and no bound on `|m|`).  The two reusable
sign lemmas it needed are also proved here (file-local; promote them if wanted):
`sin_abs_of_abs_le_pi {x : ℝ} (hx : |x| ≤ π) : sin |x| = |sin x|` and
`sinh_abs (x : ℝ) : sinh |x| = |sinh x|` — Mathlib has neither (`Real.sin_abs` and
`Real.abs_sin` do not exist).

**DONE: Step 1 relaxed.**  `Kaxis_Kfun_divisor_bound` now takes the hypothesis
`(3/2 : ℝ) ≤ Im (S • w)` instead of `w ∈ KEpsilon` (the latter was only ever used through
`E_S_im_ge`; `region_II_bound` now passes that lemma explicitly).  This is what lets Step 1 be
applied on the one-zero ball `B(w_m, r)`, which lies *outside* `E` (its centre `w_m` is on the
boundary of `𝒟` when `m ≠ 0`).

**DRAFTED, REVERTED: `KfunClear_le_of_step1` (the `M`-bound).**  Now in *multiplied* form
(`‖KfunClear u (i t)‖ * ‖Δ (i/t)‖ ≤ …`), with `hker` fixed
(`rw [h, div_mul_cancel₀ _ hgp0]`, `hgp0` from `simp only [growthPrefactor]` +
`mul_ne_zero (mul_ne_zero (DeltaFun_ne_zero _) (pow_ne_zero _ (DeltaFun_ne_zero _)))
(sub_ne_zero.mpr hne)`), `hgp` by `rw [KL.norm_growthPrefactor]; try ring`, and the cancellation
by `(le_div_iff₀ hD0).mp h1` after `rw [Kaxis, dif_pos ht, norm_mul, hj] at h1`.
**Term-size refactor tried; the timeout survives it — next lever is different.**  I restated the
lemma with `z_c`, `z₀` as *variables* and the identifications `z_c = imagAxis t ht`,
`z₀ = imagAxis t⁻¹ (inv_pos.mpr ht)` as hypotheses (so each `imagAxis` term appears exactly once in
the statement, and the proof works with `z_c`, `z₀`), rewriting Step 1's conclusion with
`rw [Kaxis, dif_pos ht, ← hzc, ← hz₀, norm_mul] at h1`.  Result: the `whnf` heartbeat timeout
**still fires** (now at the `refine`/`hb` line), so repeated occurrence of the `imagAxis` term is
not the (only) driver.  Two further things are worth trying, in order:

1. name the positivity hypothesis (`ht`) explicitly — the `‹0 < t›` term holes fail with
   `Tactic 'assumption' failed`, so the statement as drafted does not even elaborate;
1b. **CORRECTION to the decoupling plan (checked against the tree).**  The compactness bound
   `exists_bound_KfunClear_of_balls ℓ d hd c₁ c₂ (R₁ < c₁.im) (R₂ < c₂.im) : ∃ M > 0, ∀ τ z,
   ‖τ - c₁‖ ≤ R₁ → ‖z - c₂‖ ≤ R₂ → ‖KfunClear ℓ d τ z‖ ≤ M` exists, but it is **not in this
   file's import closure** (it lives behind `KaxisMid`/`FlatMiddleAux`, on the `KernelBoundAux`
   side), *and* it would not do the job anyway: in our application the *second* centre is
   `imagAxis t ht`, which **moves with `t`**, so compactness gives an `M(t)` with no usable
   dependence on `t` — and the final estimate needs `M` uniform in `t` to produce
   `C (scale w)^{N}`.  So the `M` here must be explicit, i.e. Step-1-based (or a direct bound on
   the explicit `KfunClear` formula).  The decoupling idea is therefore only valid for the
   `∀ u`-uniformity (which compactness does give, for *fixed* `t`), not for the `t`-uniformity.
   NOTE ALSO (`#check`ed): `KL.norm_growthPrefactor` already returns the grouped form
   `(‖Δ τ‖ * ‖Δ z‖^e) * ‖j τ - j z‖`, so `hgp` needs **no** `ring` after the rewrite.
2b. **DONE: piece (A)** (`KfunClear_norm_eq`) — the identity, proved.  **Piece (B) still times
   out** (`Kfun_u_mul_le`: Step 1 applied and rearranged via `(le_div_iff₀ hD0).mp h1` after
   `rw [Kaxis, dif_pos ht, ← hzc, ← hz₀, norm_mul] at h1`).  Crucially, (B)'s goal is *small* —
   just `‖Kfun u z_c‖ * (‖Δ z₀‖ * ‖ju - j z₀‖) ≤ C₁ (scale u)^{N₁} t^{d/2-4} e^{-π/t}` — so **the
   timeout is not about goal size**; it is a specific unification, most likely the backwards
   rewrites `← hzc`, `← hz₀` (whose LHS `imagAxis t ht` carries the proof argument `ht`, so
   matching is not proof-irrelevant) or the instantiation of Step 1's long statement at `hb`.
   Next diagnostic (cheap, and *only* a diagnostic): `set_option maxHeartbeats 4000000 in` on this
   single lemma to distinguish "slow but terminating" from a genuine `whnf` loop; if it terminates
   with more budget, wrap the `hb`-instantiation in a `have` with the *explicit* divisor form to
   pin the metavariables before rewriting, and conversely drop the `← hzc`/`← hz₀` rewrites in
   favour of `subst`-free `simpa` on the final inequality.
3. if the timeout persists, split the `M`-bound into two small lemmas so that no single goal is
   large: (A) the *identity* `‖KfunClear u z_c‖ * ‖Δ z₀‖ = (‖Kfun u z_c‖ * (‖Δ z₀‖ * ‖j u - j z₀‖))
   * (‖Δ u‖ * ‖Δ z_c‖^e)` (from `KL.Kfun_eq_KfunClear_div` + `KL.norm_growthPrefactor`), and
   (B) the *Step-1 application* `‖Kfun u z_c‖ * (‖Δ z₀‖ * ‖j u - j z₀‖) ≤ C₁ (scale u)^{N₁}
   t^{d/2-4} e^{-π/t}` via `(le_div_iff₀ hD0).mp`.  Then the final bound is
   `(A).trans ((B) · nonneg)` with no `ring` on a large goal.  The older plan was to decouple: state the one-zero
   assembly with the ball bound `M` as a *hypothesis* (exactly the interface
   `E_one_zero_diag` uses: `hb : ∀ τ z, ‖τ - z₀‖ ≤ r → ‖z - z₀‖ ≤ r → ‖KfunClear ℓ d τ z‖ ≤ M`)
   and obtain `M` from a *separate*, cheaper argument — `exists_bound_KfunClear_of_balls`-style
   compactness of the Euclidean ball, which needs no `Step 1` and no divisor cancellation at all.
   The sharp Step-1 form of `M` (the one drafted above) is then only needed if the final constant
   has to be tracked explicitly, which the `∃ C` conclusion does not require.  The `set e`
atom did *not* remove it; the timeout moved to the closing `by ring` in
`hL.trans_le ((mul_le_mul_of_nonneg_right h1' (by positivity)).trans_eq (by ring))` and to the
lemma header, i.e. it is `whnf`/`isDefEq` churn on a goal whose *terms* are huge: the expression
`Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht)` (with its proof argument) occurs about eight times
in the statement and the proof, and every unification step re-traverses it.  So the fix is to
**shrink the terms**, not the exponent: state the lemma with an abstract point, e.g.

```
∀ (z : ℍ) (u : ℍ) (T : ℝ), 0 < T → 1 ≤ z.im → z.im = T⁻¹ → (3/2:ℝ) ≤ (S•u).im → j u ≠ j z →
  ‖KfunClear ℓ d u (imagAxis T hT)‖ * ‖Δ z‖ ≤ … ‖Δ (imagAxis T hT)‖ ^ e … / (…)
```

i.e. keep `z₀ := imagAxis T⁻¹ hT` out of the statement entirely and pass it as the hypothesis
`z.im = T⁻¹` (equivalently: use `S • z` in place of `imagAxis T hT` and carry `z.im = T`).  The
divisor identity then only ever mentions `z`.  (A `set` of the ℍ-valued point is *not* safe here —
its type carries a proof component, which breaks the dependent rewrites later; and a file-level
`maxHeartbeats` is still the wrong lever.) the `rw [Kaxis, dif_pos ht,
norm_mul, hj] at h1` step and the final `ring` blow the heartbeat budget
(`timeout at isDefEq` / `timeout at whnf`), because the exponent `(if d = 8 then 1 else 2)`
(a dependent `ℕ`-power) is unfolded over and over in unification.  Fix to apply next time:
`set e : ℕ := if d = 8 then 1 else 2 with he` at the start of the proof (making the exponent an
*atom* for `rw`/`ring`), prove the statement with `‖Δ (i t)‖ ^ e`, and `rw [he]` at the very end;
equivalently `rcases hd` and duplicate the (short) proof in the two cases.  A file-level
`set_option maxHeartbeats` is *not* the answer here — the loop is in unification, not in search.  Statement (divided form):

```
∃ C N, 0 < C ∧ 0 ≤ N ∧ ∀ u t ht, (3/2:ℝ) ≤ (S•u).im → t ≤ 1 → j u ≠ j (i t) →
  ‖KfunClear ℓ d u (i t)‖ ≤ C (scale u)^N * ‖Δ u‖ * ‖Δ (i t)‖^e * t^{d/2-4} e^{-π/t} / ‖Δ (i/t)‖
```

It compiled up to two points, both diagnosed:

* `hker : KfunClear u (i t) = Kfun u (i t) * growthPrefactor d u (i t)` from
  `KL.Kfun_eq_KfunClear_div`: the working proof is
  `rw [h, div_mul_cancel₀ _ hgp0]` where `hgp0 : growthPrefactor … ≠ 0` is
  `mul_ne_zero (mul_ne_zero (DeltaFun_ne_zero _) (pow_ne_zero _ (DeltaFun_ne_zero _)))
   (sub_ne_zero.mpr hne)` after `simp only [Work.Kernels.growthPrefactor]`.  (A bare
  `rw [h, div_mul_cancel₀]` then `intro h0; exact h0 rfl` is nonsense — the side goal needs the
  explicit `hgp0`.)
* the closing cancellation: **do not** try `rw [hD]` where
  `hD : ‖Δ(i/t) * (ju - j(i/t))‖ = ‖Δ(i/t)‖ * ‖ju - j(it)‖` — that product-norm is nowhere in the
  goal (the goal has the single factor `/‖Δ(i/t)‖`).  Instead state the lemma in **multiplied
  form**, `‖KfunClear u (i t)‖ * ‖Δ(i/t)‖ ≤ C (scale u)^N * (‖Δ u‖ * ‖Δ (i t)‖^e) * t^{d/2-4}
  e^{-π/t}`, and close by `(le_div_iff₀ hD0).mp h1` with
  `h1 : ‖Kfun u (i t)‖ ≤ C₁ (scale u)^N₁ t^{d/2-4} e^{-π/t} / (‖Δ(i/t)‖ * ‖ju - j(it)‖)` (after
  `rw [norm_mul, hjit] at h1`) and `hD0 : 0 < ‖Δ(i/t)‖ * ‖ju - j(it)‖`; the remaining `‖Δ u‖`,
  `‖Δ (i t)‖^e` factors then multiply through on both sides.  The associativity/grouping must be
  fixed *before* writing the calc (this file's recurring trap).

**The wiring to do next, with all the constants fixed:**

* **DONE: `S_im_ge_of_ball`** — `‖(u:ℂ) - (w_m:ℂ)‖ ≤ w_m.im/100 → (99/100)(100/101)²(S•w_m).im ≤ (S•u).im`.
  Proof: `Complex.abs_im_le_norm` + `neg_le_abs (((u:ℂ)-(w_m:ℂ)).im)` (the argument must be the
  *complex* `.im`, because the preceding `rw` has already rewritten the atom) for
  `w_m.im - r ≤ u.im`; `nlinarith [him, hrpos, hr]` for `(99/100)w_m.im ≤ u.im`;
  `norm_add_le` + `Work.Kernels.im_le_coe_norm` for `‖u‖ ≤ (101/100)‖w_m‖`, hence
  `hsq : ‖u‖² ≤ ((101/100)‖w_m‖)²`; then `EReg_S_im` twice, `le_div_iff₀`, and the numeral
  cancellation split as `h2 : (w_m.im/‖w_m‖²)*((101/100)‖w_m‖)² = (101/100)²*w_m.im` (by
  `show … by ring`, `div_mul_eq_mul_div`, `div_eq_iff hnn'`) and
  `h3 : (100/101)²*((101/100)²*w_m.im) = w_m.im`.  **Trap:** after `div_eq_iff`/`field_simp` the
  goal is often already closed, so the trailing `ring` must be `try ring`.
* OLD NOTE (superseded): (`S_im_ge_of_ball`: drafted and reverted — three snags only.  Statement:
  `‖(u:ℂ) - (w_m:ℂ)‖ ≤ w_m.im/100 → (99/100)(100/101)² (S•w_m).im ≤ (S•u).im`.
  Proof plan that compiles up to the noted steps: `Complex.abs_im_le_norm` gives
  `w_m.im - r ≤ u.im` (use `rw [h2, abs_le] at h` with `h2 : ((u:ℂ)-(w_m:ℂ)).im = u.im - w_m.im`,
  not `im_gt_sub_norm` — that name is not in this closure); `norm_add_le` plus
  `Work.Kernels.im_le_coe_norm` gives `‖u‖ ≤ (101/100)‖w_m‖`; then `EReg_S_im` twice and
  `le_div_iff₀`/`div_mul_eq_mul_div` with `hsq : ‖u‖² ≤ ((101/100)‖w_m‖)²`.  Outstanding:
  the `nlinarith` for `(99/100)w_m.im ≤ u.im` (needs `hr` and `hrpos` passed explicitly), the
  `h2 : r ≤ (1/100)‖w_m‖` step, and the final `(99/100)(100/101)² ≤ 99/100` combination.)
* `z := imagAxis t ht` (second variable), `z₀ := imagAxis t⁻¹ (inv_pos.mpr ht)`; `S • z = z₀`,
  `S • z₀ = z`, `z₀.im = 1/t`;
* `m` from `exists_near_shift` (with `ε := ε₀`), `w_m := S • ((m:ℝ) +ᵥ z₀)`, so
  `KfunClear ℓ d w_m z = 0` by `KfunClear_cuspParabolic_vanishing`;
* radius `r := w_m.im / 100` (`hr0 : 0 < r` from `w_m.im > 0`, `hrlt : r < w_m.im` by linarith);
  for `u ∈ B(w_m, r)`: `u.im ∈ [99 w_m.im/100, 101 w_m.im/100]`, `|u| ∈ [99,101]/100 |w_m|`, hence
  `Im (S•u) = u.im/|u|² ≥ (99/100)(100/101)²(1/t) > (2/3)(1/t)`, so the ball lies in
  `{3/2 ≤ Im (S•·)}` as soon as `t ≤ 2/3` (the bad case gives `t < 1/(2 - ε₀/π)`, so take
  `ε₀ ≤ 1/4`);
* `M := 2 ‖Δ z‖^e · sup_{B} ‖Δ(·)‖/‖Δ z₀‖ · C₁ (sup_B scale)^{N₁} t^{d/2-4} e^{-π/t}` — the
  Step-1 bound with the divisor cancelled: for `u ∈ B`, `j u ≠ j z ⟹`
  `‖KfunClear ℓ d u z‖ = ‖gp(u,z)‖‖Kfun(u,z)‖ ≤ ‖Δ u‖‖Δ z‖^e C₁(scale u)^{N₁} t^{d/2-4}
  e^{-π/t}/‖Δ z₀‖`; at a coincidence in `B` (only the centre `w_m` for `r` small) the value is
  `0`.  Bounds: `norm_DeltaFun_le_of_im` for `‖Δ u‖` and `‖Δ z‖` (note `S • (i t) = i/t`, height
  `1/t ≥ 1`, so `‖Δ (i t)‖ ≤ 2 t^{-12} e^{-2π/t}`), `norm_DeltaFun_ge_of_im` for `‖Δ z₀‖⁺¹`, and
  `scale u ≤ 2 scale w` (from `u.im ≥ w.im/2`);
* `KL.one_zero_apply` at `c := w_m`, zero `z₁ := w_m` (`hz` is `‖0‖ < r/2`), giving for `u = w`:
  `‖KfunClear ℓ d w z‖ ≤ (2M/r)‖(w:ℂ) - (w_m:ℂ)‖`;
* `‖(w:ℂ) - (w_m:ℂ)‖ = ‖(S•w) - ((m:ℝ)+ᵥz₀)‖/(‖S•w‖‖(m:ℝ)+ᵥz₀‖)` via `norm_S_sub_S`;
* `divisor_lower_sin` at `(S•w, z₀)` gives
  `‖j w - j(i t)‖ ≥ c e^{π(y - 1/t)}‖sin (π(S•w - z₀))‖/‖Δ z₀‖`, and
  `‖sin (π(S•w - z₀))‖ ≥ (2/π)·π‖(S•w) - ((m:ℝ)+ᵥz₀)‖/2` by `sin_abs_of_abs_le_pi` +
  `Real.mul_le_sin`, so the ratio `‖(w:ℂ)-(w_m:ℂ)‖/‖j w - j(i t)‖` is
  `≲ 1/(‖S•w‖‖z₀+m‖ e^{π(y-1/t)} c) ≲ t² e^{-2π/t}` (bad case: `y ≈ 1/t`);
* finally `Kfun = KfunClear/growthPrefactor` (`Kfun_eq_KfunClear_div`,
  `norm_growthPrefactor`) — the `‖Δ (i t)‖^e` of `M` cancels, leaving
  `t^{d/2-6} e^{-π/t}` times `(scale w)^{N₁}`.

**DONE (same session): `norm_DeltaFun_le_of_im`, `norm_DeltaFun_ge_of_im`** — the two halves of
the `S`-law `Δ u = (S u)^12 Δ(S u)` combined with `DeltaFun_upper_sharp` / `delta_lower_third`:

* `1 ≤ Im (S•u)  →  ‖Δ u‖ ≤ 2 ‖u‖^{-12} e^{-2π Im (S•u)}`
* `1/3 ≤ Im (S•u) →  c ‖u‖^{-12} e^{-2π Im (S•u)} ≤ ‖Δ u‖`

(Lean note: `zpow_neg` is *ambiguous* in this file because it has `open Matrix` — must write
`_root_.zpow_neg`.  And the direction for `((‖u‖)⁻¹)^12 = ‖u‖^(-(12:ℤ))` is
`rw [inv_pow, _root_.zpow_neg, zpow_ofNat]` — `inv_pow` first, then `zpow_neg` *forward* on the
right-hand side, then `zpow_ofNat`.)

Tactic lessons, for the next lemmas: after `set x := … with hx`, rewriting in a goal is
`rw [hx]` but in a *hypothesis* about the expression it is `rw [← hx]`; `linarith` cannot get
`y ≤ |y|` (use `le_abs_self` / `neg_le_abs`, and `neg_le_abs y : -y ≤ |y|` gives `-π ≤ y` only
*after* `linarith`); and `linarith` treats `Real.pi * |d.im|` as non-linear in the atoms, so
pass the hypotheses explicitly.  A repeated `rw [abs_mul]` fails silently the second time when
the first application already consumed the product.

So the only work left is:So the only work left is:

* **(bad case)** `‖sin (π(S•w - i/t))‖ < ε₀`: put `m := round (Re (S•w)) ∈ {-1,0,1}` (because
  `|Re (S•w)| < 1`, `τ ∈ 𝒟`); then `S•w` is close to `i/t + m`, i.e. `w` is close to the zero
  `w_m := S • ((m:ℝ) +ᵥ i/t)` of `τ ↦ KfunClear ℓ d τ (i t)`
  (`KfunClear_cuspParabolic_vanishing`, with `z := imagAxis t ht`).  Apply `one_zero_bound` at
  `w_m` with radius `r` (so that `B(w_m,r) ⊆ {3/2 ≤ Im (S•)}` in order that Step 1 bounds
  `M = sup_{B(w_m,r)} ‖KfunClear ℓ d · (i t)‖`), then divide by the lower bound for
  `‖j w - j (i t)‖` coming from `divisor_lower_sin` — in the bad case `Im (S•w) ≈ 1/t`, so
  `e^{π(y - 1/t)} ≈ 1` and `‖sin‖ ≥ c π |w - w_m| · |S•w| · |z₀+m|`, cancelling the `|w - w_m|`
  of the one-zero estimate.  Needed side inputs: `‖Δ u‖ ≥ c e^{-2π Im (S u)}` for
  `Im (S u) ≥ 1/3` (from `delta_lower_third` plus the `S`-law for `Δ`), `‖Δ (i t)‖ ≥ c e^{-2πt}`,
  and `‖j'(w_m)‖ ≳ e^{2π/t}`.
* **(Region III good part)** `y < T₀` and `1/t < T₀` (so `t > 1/T₀`, and `w.im ≥ 2/(1+T₀²)`, so
  `scale w` is bounded — a constant bound suffices): use the elementary inequality
  `‖j τ - j z‖ ≥ ‖q τ - q z‖ (e^{2π(Im τ + Im z)} - C_lip)` with `C_lip` the Lipschitz constant of
  `ε = j - q⁻¹ - 744` on the disc `‖q‖ ≤ e^{-2π}`; the required input
  (`Asymptotics/epsF_lipschitz_small`, statement reviewed and confirmed, `C_lip ≈ 2.9·10⁵ ≪ 7·10⁷`,
  so `2 C_lip ≤ e^{6π}` and `y + 1/t ≥ 3`) is still to be proved (or obtained by compactness:
  the unique coincidences with `j z₀` in `closure 𝒟 ∩ {3/2 ≤ Im ≤ T₀}` are `τ = i/t + b`,
  `b ∈ {-1,0,1}`, and those have `sin (π(τ-z₀)) = 0`).
* **assembly**: combine `region_II_bound` with the two remaining pieces; no `scale w`-growth
  occurs in Region III, and Region II contributes `(scale w)^{N₁}`.
-/


/-! ## The bridge to the sharp `j`-difference bound

The block below is a copy of the module `Submission.Work.Asymptotics.E_jdiff_small` (all
declarations renamed with the `cfx_` prefix, because that module declares
`Work.Asymptotics.norm_qParamFun_le_one` with a signature incompatible with the one in
`Submission.Work.Asymptotics.KPlusXiDefs`, so the two can never share an environment).  It
provides the sharp lower bound for `‖j w - j (i t)‖` on `E`, which is the input that makes the
near-diagonal (cancellation) regime tractable. -/

open ModularForm
open scoped ModularForm Modular Manifold Bundle


-- (section marker dropped)

-- OPEN open UpperHalfPlane ModularGroup ModularForm
-- OPEN open scoped MatrixGroups UpperHalfPlane Manifold

-- (namespace dropped)

/-! ## Elementary properties of the `q`-parameter -/

lemma cfx_norm_qParamFun_eq (τ : ℍ) :
    ‖Work.Kernels.qParamFun τ‖ = Real.exp (-(2 * Real.pi * τ.im)) := by
  rw [Work.Kernels.qParamFun, Complex.norm_exp]
  congr 1
  have hrw : 2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ)
      = ((2 * Real.pi : ℝ) : ℂ) * (Complex.I * (τ : ℂ)) := by push_cast; ring
  rw [hrw, Complex.mul_re, Complex.I_mul_re, Complex.ofReal_re, Complex.ofReal_im,
    UpperHalfPlane.coe_im]
  ring

lemma cfx_qParamFun_ne_zero (τ : ℍ) : Work.Kernels.qParamFun τ ≠ 0 := Complex.exp_ne_zero _

lemma cfx_norm_qParamFun_le_exp (τ : ℍ) (hτ : 1 ≤ τ.im) :
    ‖Work.Kernels.qParamFun τ‖ ≤ Real.exp (-(2 * Real.pi)) := by
  rw [cfx_norm_qParamFun_eq, Real.exp_le_exp]; nlinarith [Real.pi_pos, hτ]

lemma cfx_norm_qParamFun_le_one (τ : ℍ) : ‖Work.Kernels.qParamFun τ‖ ≤ 1 := by
  rw [cfx_norm_qParamFun_eq, ← Real.exp_zero]
  exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, τ.im_pos])

/-- `e^{-2π} ≤ 1/512`. -/
lemma cfx_exp_neg_two_pi_le_inv512 : Real.exp (-(2 * Real.pi)) ≤ 1 / 512 := by
  have hpi : (6.28 : ℝ) < 2 * Real.pi := by linarith [Real.pi_gt_d20]
  have h1 : Real.exp (-(2 * Real.pi)) ≤ Real.exp (-6.28) := by
    rw [Real.exp_le_exp]; linarith
  have h2 : Real.exp (-6.28) ≤ 1 / 512 := by
    have hexp : (512 : ℝ) ≤ Real.exp 6.28 := by
      have hsplit : Real.exp 6.28 = Real.exp 6 * Real.exp 0.28 := by
        rw [← Real.exp_add]; norm_num
      have h6 : (400 : ℝ) ≤ Real.exp 6 := by
        have h : Real.exp 6 = (Real.exp 1) ^ 6 := by simp
        rw [h]
        have h1' : (2.7182818283 : ℝ) ^ 6 ≤ (Real.exp 1) ^ 6 :=
          pow_le_pow_left₀ (by norm_num) (le_of_lt Real.exp_one_gt_d9) 6
        have h2' : (400 : ℝ) ≤ (2.7182818283 : ℝ) ^ 6 := by norm_num
        linarith
      have h028 : (1.28 : ℝ) ≤ Real.exp 0.28 := by
        have := Real.add_one_le_exp (0.28 : ℝ)
        linarith
      rw [hsplit]
      nlinarith
    have hpos : 0 < Real.exp 6.28 := Real.exp_pos _
    have hprod : Real.exp 6.28 * Real.exp (-6.28) = 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (-6.28 : ℝ)]
  linarith

lemma cfx_norm_qParamFun_le_inv512 (τ : ℍ) (hτ : 1 ≤ τ.im) :
    ‖Work.Kernels.qParamFun τ‖ ≤ 1 / 512 := by
  rw [cfx_norm_qParamFun_eq]
  have h1 : Real.exp (-(2 * Real.pi * τ.im)) ≤ Real.exp (-(2 * Real.pi)) := by
    rw [Real.exp_le_exp]; nlinarith [Real.pi_pos, hτ]
  linarith [cfx_exp_neg_two_pi_le_inv512]

/-- `n⁴ ≤ 4 · 3ⁿ` for all `n : ℕ`. -/
lemma cfx_pow_four_le_four_mul_three_pow (n : ℕ) : (n : ℝ) ^ 4 ≤ 4 * 3 ^ n := by
  have aux : ∀ m : ℕ, 5 ≤ m → ((m : ℝ)) ^ 4 ≤ 4 * (3 : ℝ) ^ m := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => norm_num
    | succ k hk ih =>
      have hk5 : (5 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := by linarith
      have h1 : (k : ℝ) + 1 ≤ (6 / 5) * (k : ℝ) := by linarith
      have h2 : ((k : ℝ) + 1) ^ 4 ≤ ((6 / 5) * (k : ℝ)) ^ 4 :=
        pow_le_pow_left₀ (by positivity) h1 4
      have h3 : ((6 / 5) * (k : ℝ)) ^ 4 = (1296 / 625) * (k : ℝ) ^ 4 := by ring
      have h4 : (1296 / 625 : ℝ) * (k : ℝ) ^ 4 ≤ 3 * (k : ℝ) ^ 4 := by
        nlinarith [pow_nonneg hk0 4]
      have h5 : 3 * (k : ℝ) ^ 4 ≤ 3 * (4 * (3 : ℝ) ^ k) := by linarith
      have h6 : 3 * (4 * (3 : ℝ) ^ k) = 4 * (3 : ℝ) ^ (k + 1) := by rw [pow_succ]; ring
      calc (((k + 1 : ℕ)) : ℝ) ^ 4 = ((k : ℝ) + 1) ^ 4 := by push_cast; ring
        _ ≤ ((6 / 5) * (k : ℝ)) ^ 4 := h2
        _ = (1296 / 625) * (k : ℝ) ^ 4 := h3
        _ ≤ 3 * (k : ℝ) ^ 4 := h4
        _ ≤ 4 * (3 : ℝ) ^ (k + 1) := by rw [← h6]; linarith
  rcases Nat.lt_or_ge n 5 with hn | hn
  · interval_cases n <;> norm_num
  · exact aux n hn

/-- `n⁶ ≤ 1000 · 4ⁿ` for all `n : ℕ`. -/
lemma cfx_pow_six_le (n : ℕ) : (n : ℝ) ^ 6 ≤ 1000 * 4 ^ n := by
  have aux : ∀ m : ℕ, 8 ≤ m → ((m : ℝ)) ^ 6 ≤ 1000 * (4 : ℝ) ^ m := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => norm_num
    | succ k hk ih =>
      have hk8 : (8 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := by linarith
      have h1 : (k : ℝ) + 1 ≤ (9 / 8) * (k : ℝ) := by linarith
      have h2 : ((k : ℝ) + 1) ^ 6 ≤ ((9 / 8) * (k : ℝ)) ^ 6 :=
        pow_le_pow_left₀ (by positivity) h1 6
      have h3 : ((9 / 8) * (k : ℝ)) ^ 6 = (531441 / 262144) * (k : ℝ) ^ 6 := by ring
      have h4 : (531441 / 262144 : ℝ) * (k : ℝ) ^ 6 ≤ 4 * (k : ℝ) ^ 6 := by
        nlinarith [pow_nonneg hk0 6]
      have h5 : 4 * (k : ℝ) ^ 6 ≤ 4 * (1000 * (4 : ℝ) ^ k) := by linarith
      have h6 : 4 * (1000 * (4 : ℝ) ^ k) = 1000 * (4 : ℝ) ^ (k + 1) := by rw [pow_succ]; ring
      calc (((k + 1 : ℕ)) : ℝ) ^ 6 = ((k : ℝ) + 1) ^ 6 := by push_cast; ring
        _ ≤ ((9 / 8) * (k : ℝ)) ^ 6 := h2
        _ = (531441 / 262144) * (k : ℝ) ^ 6 := h3
        _ ≤ 4 * (k : ℝ) ^ 6 := h4
        _ ≤ 1000 * (4 : ℝ) ^ (k + 1) := by rw [← h6]; linarith
  rcases Nat.lt_or_ge n 8 with hn | hn
  · interval_cases n <;> norm_num
  · exact aux n hn

/-! ## The three-term `q`-expansions of `E₄`, `E₆` and `Δ` on `Im τ ≥ 1` -/

/-- `((n : ℝ) + 3)⁶ ≤ 1100 · 4ⁿ` (the sharper comparison used for the `E₆` tail). -/
lemma cfx_pow_six_shift (n : ℕ) : ((n : ℝ) + 3) ^ 6 ≤ 1100 * 4 ^ n := by
  induction n with
  | zero => norm_num
  | succ k ih =>
      rcases Nat.lt_or_ge 5 k with hk | hk
      · have hk5 : (5 : ℝ) ≤ (k : ℝ) := by
          have : (5 : ℕ) ≤ k := le_of_lt hk
          exact_mod_cast this
        have hk0 : (0 : ℝ) ≤ (k : ℝ) := by linarith
        have h1 : (k : ℝ) + 4 ≤ (9 / 8) * ((k : ℝ) + 3) := by linarith
        have h2 : ((k : ℝ) + 4) ^ 6 ≤ ((9 / 8) * ((k : ℝ) + 3)) ^ 6 :=
          pow_le_pow_left₀ (by positivity) h1 6
        have h3 : ((9 / 8) * ((k : ℝ) + 3)) ^ 6 = (531441 / 262144) * ((k : ℝ) + 3) ^ 6 := by
          ring
        have h4 : (531441 / 262144 : ℝ) * ((k : ℝ) + 3) ^ 6 ≤ 4 * ((k : ℝ) + 3) ^ 6 := by
          nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ (k : ℝ) + 3) 6]
        have h5 : 4 * ((k : ℝ) + 3) ^ 6 ≤ 4 * (1100 * 4 ^ k) := by linarith
        have h6 : 4 * (1100 * (4 : ℝ) ^ k) = 1100 * 4 ^ (k + 1) := by rw [pow_succ]; ring
        have hgoal : (((k + 1 : ℕ)) : ℝ) + 3 = (k : ℝ) + 4 := by push_cast; ring
        rw [hgoal]
        calc ((k : ℝ) + 4) ^ 6 ≤ 4 * ((k : ℝ) + 3) ^ 6 :=
              le_trans h2 (le_trans (le_of_eq h3) h4)
          _ ≤ 1100 * 4 ^ (k + 1) := by rw [← h6]; linarith
      · interval_cases k <;> norm_num

/-- The coefficients of the `q`-expansion of `E₄` are `1, 240 σ₃(m)`. -/
lemma cfx_E4_qcoeff (m : ℕ) :
    (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff m =
      if m = 0 then 1 else 240 * ((ArithmeticFunction.sigma 3 m : ℕ) : ℂ) := by
  rw [show Work.Kernels.E4Fun = Work.Modular.E4 from rfl, Work.Modular.E4_qExpansion_coeff]

/-- The coefficients of the `q`-expansion of `E₆` are `1, -504 σ₅(m)`. -/
lemma cfx_E6_qcoeff (m : ℕ) :
    (UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff m =
      if m = 0 then 1 else -504 * ((ArithmeticFunction.sigma 5 m : ℕ) : ℂ) := by
  rw [show Work.Kernels.E6Fun = Work.Modular.E6 from rfl, Work.Modular.E6_qExpansion_coeff]

/-- Tail bound for `E₄` after three terms: on `Im w ≥ 1`,
`E₄ w = 1 + 240 q + 2160 q² + O(‖q‖³)` with explicit constant `30000`. -/
theorem cfx_E4_third_order (w : ℍ) (hw : 1 ≤ w.im) :
    ‖Work.Kernels.E4Fun w - 1 - 240 * Work.Kernels.qParamFun w
        - 2160 * Work.Kernels.qParamFun w ^ 2‖
      ≤ 30000 * ‖Work.Kernels.qParamFun w‖ ^ 3 := by
  have hper : Function.Periodic (Work.Kernels.E4Fun ∘ UpperHalfPlane.ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₄ one_mem_strictPeriods_SL
  have hhol : MDiff Work.Kernels.E4Fun := ModularForm.holo' ModularForm.E₄
  have hbdd : UpperHalfPlane.IsBoundedAtImInfty Work.Kernels.E4Fun :=
    ModularFormClass.bdd_at_infty ModularForm.E₄
  have hs := UpperHalfPlane.hasSum_qExpansion (h := 1) (f := Work.Kernels.E4Fun)
    one_pos hper hhol hbdd w
  have hs3 := (hasSum_nat_add_iff' 3).mpr hs
  have hq_eq : Function.Periodic.qParam 1 (w : ℂ) = Work.Kernels.qParamFun w := by
    simp [Function.Periodic.qParam, Work.Kernels.qParamFun]
  have hcoeff : ∀ m : ℕ, 3 ≤ m →
      ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff m‖ ≤ 240 * (m : ℝ) ^ 4 := by
    intro m hm
    have hm0 : m ≠ 0 := by omega
    rw [cfx_E4_qcoeff m, if_neg hm0, norm_mul]
    have hσ : (ArithmeticFunction.sigma 3 m : ℝ) ≤ (m : ℝ) ^ 4 := by
      have h' : ArithmeticFunction.sigma 3 m ≤ m ^ 4 := by
        simpa using ArithmeticFunction.sigma_le_pow_succ 3 m
      exact_mod_cast h'
    have h240 : ‖(240 : ℂ)‖ = (240 : ℝ) := by norm_num
    rw [h240, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left hσ (by norm_num)
  have hc0 : (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff 0 = 1 := by
    rw [cfx_E4_qcoeff]; norm_num
  have hc1 : (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff 1 = 240 := by
    rw [cfx_E4_qcoeff 1, if_neg (by norm_num : (1 : ℕ) ≠ 0)]
    norm_num [ArithmeticFunction.sigma_one]
  have hc2 : (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff 2 = 2160 := by
    rw [cfx_E4_qcoeff 2, if_neg (by norm_num : (2 : ℕ) ≠ 0)]
    have hs2 : ArithmeticFunction.sigma 3 2 = 9 := by decide +kernel
    rw [hs2]; norm_num
  have hsum3 : (∑ i ∈ Finset.range 3, (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff i
        • Function.Periodic.qParam 1 (w : ℂ) ^ i)
      = 1 + 240 * Function.Periodic.qParam 1 (w : ℂ)
        + 2160 * Function.Periodic.qParam 1 (w : ℂ) ^ 2 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, hc0, hc1, hc2]
    simp only [smul_eq_mul, pow_zero, pow_one, mul_one]
  rw [hsum3, hq_eq] at hs3
  have hr0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun w‖ := norm_nonneg _
  have hr : ‖Work.Kernels.qParamFun w‖ ≤ 1 / 512 := cfx_norm_qParamFun_le_inv512 w hw
  have hr3 : 3 * ‖Work.Kernels.qParamFun w‖ < 1 := by linarith
  -- termwise bound
  have hterm : ∀ n : ℕ,
      ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff (n + 3)
        • Work.Kernels.qParamFun w ^ (n + 3)‖
      ≤ (240 * 108 : ℝ) * ((3 * ‖Work.Kernels.qParamFun w‖) ^ n
          * ‖Work.Kernels.qParamFun w‖ ^ 3) := by
    intro n
    have hc := hcoeff (n + 3) (by omega)
    have h4 : (((n : ℝ) + 3)) ^ 4 ≤ 108 * 3 ^ n := by
      have h := cfx_pow_four_le_four_mul_three_pow (n + 3)
      have hcast : ((n + 3 : ℕ) : ℝ) = (n : ℝ) + 3 := by push_cast; ring
      rw [hcast] at h
      have h3 : (4 : ℝ) * 3 ^ (n + 3) = 108 * 3 ^ n := by rw [pow_add]; ring
      linarith [h, h3.le, h3.ge]
    have hc' : ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff (n + 3)‖
        ≤ 240 * (((n : ℝ) + 3) ^ 4) := by
      have hcast : ((n + 3 : ℕ) : ℝ) = (n : ℝ) + 3 := by push_cast; ring
      rw [hcast] at hc
      exact hc
    calc ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff (n + 3)
          • Work.Kernels.qParamFun w ^ (n + 3)‖
        = ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff (n + 3)‖
          * ‖Work.Kernels.qParamFun w‖ ^ (n + 3) := by rw [smul_eq_mul, norm_mul, norm_pow]
      _ ≤ (240 * (((n : ℝ) + 3) ^ 4)) * ‖Work.Kernels.qParamFun w‖ ^ (n + 3) :=
          mul_le_mul_of_nonneg_right hc' (by positivity)
      _ ≤ (240 * (108 * 3 ^ n)) * ‖Work.Kernels.qParamFun w‖ ^ (n + 3) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left h4 (by norm_num)
      _ = (240 * 108 : ℝ) * ((3 * ‖Work.Kernels.qParamFun w‖) ^ n
            * ‖Work.Kernels.qParamFun w‖ ^ 3) := by rw [pow_add, mul_pow]; ring
  have hgeo : Summable (fun n : ℕ => (3 * ‖Work.Kernels.qParamFun w‖) ^ n) :=
    summable_geometric_of_lt_one (by positivity) hr3
  have hmaj : Summable (fun n : ℕ => (240 * 108 : ℝ)
      * ((3 * ‖Work.Kernels.qParamFun w‖) ^ n * ‖Work.Kernels.qParamFun w‖ ^ 3)) :=
    (hgeo.mul_right _).mul_left _
  have hsumm : Summable (fun n : ℕ =>
      ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff (n + 3)
        • Work.Kernels.qParamFun w ^ (n + 3)‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hmaj
  have hkey : ‖Work.Kernels.E4Fun w - 1 - 240 * Work.Kernels.qParamFun w
        - 2160 * Work.Kernels.qParamFun w ^ 2‖
      = ‖∑' n : ℕ, (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff (n + 3)
          • Work.Kernels.qParamFun w ^ (n + 3)‖ := by
    rw [hs3.tsum_eq]
    congr 1
    ring
  rw [hkey]
  calc ‖∑' n : ℕ, (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff (n + 3)
        • Work.Kernels.qParamFun w ^ (n + 3)‖
      ≤ ∑' n : ℕ, ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff (n + 3)
        • Work.Kernels.qParamFun w ^ (n + 3)‖ := norm_tsum_le_tsum_norm hsumm
    _ ≤ ∑' n : ℕ, (240 * 108 : ℝ) * ((3 * ‖Work.Kernels.qParamFun w‖) ^ n
          * ‖Work.Kernels.qParamFun w‖ ^ 3) :=
        Summable.tsum_le_tsum hterm hsumm hmaj
    _ = (240 * 108 : ℝ) * (∑' n : ℕ, (3 * ‖Work.Kernels.qParamFun w‖) ^ n)
          * ‖Work.Kernels.qParamFun w‖ ^ 3 := by
        rw [tsum_mul_left, tsum_mul_right]; ring
    _ = (240 * 108 : ℝ) * (1 - 3 * ‖Work.Kernels.qParamFun w‖)⁻¹
          * ‖Work.Kernels.qParamFun w‖ ^ 3 := by
        rw [tsum_geometric_of_lt_one (by positivity) hr3]
    _ ≤ 30000 * ‖Work.Kernels.qParamFun w‖ ^ 3 := by
        have hpos : 0 < 1 - 3 * ‖Work.Kernels.qParamFun w‖ := by linarith
        have hb : (240 * 108 : ℝ) * (1 - 3 * ‖Work.Kernels.qParamFun w‖)⁻¹ ≤ 30000 := by
          rw [mul_inv_le_iff₀ hpos]
          nlinarith [hr, hr0]
        have hpow : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun w‖ ^ 3 := by positivity
        exact mul_le_mul_of_nonneg_right hb hpow

/-- Tail bound for `E₆` after three terms: on `Im w ≥ 1`,
`E₆ w = 1 - 504 q - 16632 q² + O(‖q‖³)` with explicit constant `10^6`. -/
theorem cfx_E6_third_order (w : ℍ) (hw : 1 ≤ w.im) :
    ‖Work.Kernels.E6Fun w - 1 + 504 * Work.Kernels.qParamFun w
        + 16632 * Work.Kernels.qParamFun w ^ 2‖
      ≤ 1000000 * ‖Work.Kernels.qParamFun w‖ ^ 3 := by
  have hper : Function.Periodic (Work.Kernels.E6Fun ∘ UpperHalfPlane.ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₆ one_mem_strictPeriods_SL
  have hhol : MDiff Work.Kernels.E6Fun := ModularForm.holo' ModularForm.E₆
  have hbdd : UpperHalfPlane.IsBoundedAtImInfty Work.Kernels.E6Fun :=
    ModularFormClass.bdd_at_infty ModularForm.E₆
  have hs := UpperHalfPlane.hasSum_qExpansion (h := 1) (f := Work.Kernels.E6Fun)
    one_pos hper hhol hbdd w
  have hs3 := (hasSum_nat_add_iff' 3).mpr hs
  have hq_eq : Function.Periodic.qParam 1 (w : ℂ) = Work.Kernels.qParamFun w := by
    simp [Function.Periodic.qParam, Work.Kernels.qParamFun]
  have hcoeff : ∀ m : ℕ, 3 ≤ m →
      ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff m‖ ≤ 504 * (m : ℝ) ^ 6 := by
    intro m hm
    have hm0 : m ≠ 0 := by omega
    rw [cfx_E6_qcoeff m, if_neg hm0, norm_mul]
    have hσ : (ArithmeticFunction.sigma 5 m : ℝ) ≤ (m : ℝ) ^ 6 := by
      have h' : ArithmeticFunction.sigma 5 m ≤ m ^ 6 := by
        simpa using ArithmeticFunction.sigma_le_pow_succ 5 m
      exact_mod_cast h'
    have h504 : ‖(-504 : ℂ)‖ = (504 : ℝ) := by norm_num
    rw [h504, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left hσ (by norm_num)
  have hc0 : (UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff 0 = 1 := by
    rw [cfx_E6_qcoeff]; norm_num
  have hc1 : (UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff 1 = -504 := by
    rw [cfx_E6_qcoeff 1, if_neg (by norm_num : (1 : ℕ) ≠ 0)]
    norm_num [ArithmeticFunction.sigma_one]
  have hc2 : (UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff 2 = -16632 := by
    rw [cfx_E6_qcoeff 2, if_neg (by norm_num : (2 : ℕ) ≠ 0)]
    have hs2 : ArithmeticFunction.sigma 5 2 = 33 := by decide +kernel
    rw [hs2]; norm_num
  have hsum3 : (∑ i ∈ Finset.range 3, (UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff i
        • Function.Periodic.qParam 1 (w : ℂ) ^ i)
      = 1 - 504 * Function.Periodic.qParam 1 (w : ℂ)
        - 16632 * Function.Periodic.qParam 1 (w : ℂ) ^ 2 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, hc0, hc1, hc2]
    simp only [smul_eq_mul, pow_zero, pow_one, mul_one]
    ring
  rw [hsum3, hq_eq] at hs3
  have hr0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun w‖ := norm_nonneg _
  have hr : ‖Work.Kernels.qParamFun w‖ ≤ 1 / 512 := cfx_norm_qParamFun_le_inv512 w hw
  have hr4 : 4 * ‖Work.Kernels.qParamFun w‖ < 1 := by linarith
  have hterm : ∀ n : ℕ,
      ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff (n + 3)
        • Work.Kernels.qParamFun w ^ (n + 3)‖
      ≤ (504 * 1100 : ℝ) * ((4 * ‖Work.Kernels.qParamFun w‖) ^ n
          * ‖Work.Kernels.qParamFun w‖ ^ 3) := by
    intro n
    have hc := hcoeff (n + 3) (by omega)
    have h6 : (((n : ℝ) + 3)) ^ 6 ≤ 1100 * 4 ^ n := cfx_pow_six_shift n
    have hc' : ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff (n + 3)‖
        ≤ 504 * (((n : ℝ) + 3) ^ 6) := by
      have hcast : ((n + 3 : ℕ) : ℝ) = (n : ℝ) + 3 := by push_cast; ring
      rw [hcast] at hc
      exact hc
    calc ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff (n + 3)
          • Work.Kernels.qParamFun w ^ (n + 3)‖
        = ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff (n + 3)‖
          * ‖Work.Kernels.qParamFun w‖ ^ (n + 3) := by rw [smul_eq_mul, norm_mul, norm_pow]
      _ ≤ (504 * (((n : ℝ) + 3) ^ 6)) * ‖Work.Kernels.qParamFun w‖ ^ (n + 3) :=
          mul_le_mul_of_nonneg_right hc' (by positivity)
      _ ≤ (504 * (1100 * 4 ^ n)) * ‖Work.Kernels.qParamFun w‖ ^ (n + 3) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left h6 (by norm_num)
      _ = (504 * 1100 : ℝ) * ((4 * ‖Work.Kernels.qParamFun w‖) ^ n
            * ‖Work.Kernels.qParamFun w‖ ^ 3) := by rw [pow_add, mul_pow]; ring
  have hgeo : Summable (fun n : ℕ => (4 * ‖Work.Kernels.qParamFun w‖) ^ n) :=
    summable_geometric_of_lt_one (by positivity) hr4
  have hmaj : Summable (fun n : ℕ => (504 * 1100 : ℝ)
      * ((4 * ‖Work.Kernels.qParamFun w‖) ^ n * ‖Work.Kernels.qParamFun w‖ ^ 3)) :=
    (hgeo.mul_right _).mul_left _
  have hsumm : Summable (fun n : ℕ =>
      ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff (n + 3)
        • Work.Kernels.qParamFun w ^ (n + 3)‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hmaj
  have hkey : ‖Work.Kernels.E6Fun w - 1 + 504 * Work.Kernels.qParamFun w
        + 16632 * Work.Kernels.qParamFun w ^ 2‖
      = ‖∑' n : ℕ, (UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff (n + 3)
          • Work.Kernels.qParamFun w ^ (n + 3)‖ := by
    rw [hs3.tsum_eq]
    congr 1
    ring
  rw [hkey]
  calc ‖∑' n : ℕ, (UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff (n + 3)
        • Work.Kernels.qParamFun w ^ (n + 3)‖
      ≤ ∑' n : ℕ, ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff (n + 3)
        • Work.Kernels.qParamFun w ^ (n + 3)‖ := norm_tsum_le_tsum_norm hsumm
    _ ≤ ∑' n : ℕ, (504 * 1100 : ℝ) * ((4 * ‖Work.Kernels.qParamFun w‖) ^ n
          * ‖Work.Kernels.qParamFun w‖ ^ 3) :=
        Summable.tsum_le_tsum hterm hsumm hmaj
    _ = (504 * 1100 : ℝ) * (∑' n : ℕ, (4 * ‖Work.Kernels.qParamFun w‖) ^ n)
          * ‖Work.Kernels.qParamFun w‖ ^ 3 := by
        rw [tsum_mul_left, tsum_mul_right]; ring
    _ = (504 * 1100 : ℝ) * (1 - 4 * ‖Work.Kernels.qParamFun w‖)⁻¹
          * ‖Work.Kernels.qParamFun w‖ ^ 3 := by
        rw [tsum_geometric_of_lt_one (by positivity) hr4]
    _ ≤ 1000000 * ‖Work.Kernels.qParamFun w‖ ^ 3 := by
        have hpos : 0 < 1 - 4 * ‖Work.Kernels.qParamFun w‖ := by linarith
        have hb : (504 * 1100 : ℝ) * (1 - 4 * ‖Work.Kernels.qParamFun w‖)⁻¹ ≤ 1000000 := by
          rw [mul_inv_le_iff₀ hpos]
          nlinarith [hr, hr0]
        have hpow : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun w‖ ^ 3 := by positivity
        exact mul_le_mul_of_nonneg_right hb hpow

/-! ## The three-term expansion of `Δ` -/

/-- On `Im w ≥ 1`, `Δ w = q - 24 q² + O(‖q‖³)` with explicit constant `10^5`. -/
theorem cfx_Delta_third_order (w : ℍ) (hw : 1 ≤ w.im) :
    ‖Work.Kernels.DeltaFun w - Work.Kernels.qParamFun w
        + 24 * Work.Kernels.qParamFun w ^ 2‖
      ≤ 100000 * ‖Work.Kernels.qParamFun w‖ ^ 3 := by
  set q := Work.Kernels.qParamFun w with hq
  have hr0 : (0 : ℝ) ≤ ‖q‖ := norm_nonneg _
  have hr : ‖q‖ ≤ 1 / 512 := by rw [hq]; exact cfx_norm_qParamFun_le_inv512 w hw
  have h4 : ‖Work.Kernels.E4Fun w - 1 - 240 * q - 2160 * q ^ 2‖ ≤ 30000 * ‖q‖ ^ 3 := by
    rw [hq]; exact cfx_E4_third_order w hw
  have h6 : ‖Work.Kernels.E6Fun w - 1 + 504 * q + 16632 * q ^ 2‖ ≤ 1000000 * ‖q‖ ^ 3 := by
    rw [hq]; exact cfx_E6_third_order w hw
  have hD : Work.Kernels.DeltaFun w
      = (Work.Kernels.E4Fun w ^ 3 - Work.Kernels.E6Fun w ^ 2) / 1728 := by
    have h1 : Work.Kernels.DeltaFun w = ModularForm.discriminant w := by
      rw [show Work.Kernels.DeltaFun = ⇑CuspForm.discriminant from rfl, CuspForm.coe_discriminant]
    rw [h1, ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq]
  -- abbreviations
  have hPnorm : ‖(1 : ℂ) + 240 * q + 2160 * q ^ 2‖ ≤ (3 / 2 : ℝ) := by
    have h1 : ‖(1 : ℂ) + 240 * q + 2160 * q ^ 2‖ ≤ 1 + 240 * ‖q‖ + 2160 * ‖q‖ ^ 2 := by
      calc ‖(1 : ℂ) + 240 * q + 2160 * q ^ 2‖ ≤ ‖(1 : ℂ) + 240 * q‖ + ‖2160 * q ^ 2‖ :=
            norm_add_le _ _
        _ ≤ (‖(1 : ℂ)‖ + ‖240 * q‖) + ‖2160 * q ^ 2‖ := by
            linarith [norm_add_le (1 : ℂ) (240 * q)]
        _ = 1 + 240 * ‖q‖ + 2160 * ‖q‖ ^ 2 := by
            rw [norm_one, norm_mul, norm_mul, norm_pow]
            norm_num
    nlinarith [hr, hr0]
  have hQnorm : ‖(1 : ℂ) - 504 * q - 16632 * q ^ 2‖ ≤ (3 : ℝ) := by
    have h1 : ‖(1 : ℂ) - 504 * q - 16632 * q ^ 2‖ ≤ 1 + 504 * ‖q‖ + 16632 * ‖q‖ ^ 2 := by
      calc ‖(1 : ℂ) - 504 * q - 16632 * q ^ 2‖ ≤ ‖(1 : ℂ) - 504 * q‖ + ‖16632 * q ^ 2‖ :=
            norm_sub_le _ _
        _ ≤ (‖(1 : ℂ)‖ + ‖504 * q‖) + ‖16632 * q ^ 2‖ := by
            linarith [norm_sub_le (1 : ℂ) (504 * q)]
        _ = 1 + 504 * ‖q‖ + 16632 * ‖q‖ ^ 2 := by
            rw [norm_one, norm_mul, norm_mul, norm_pow]
            norm_num
    nlinarith [hr, hr0]
  have hunorm4 : ‖Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2)‖ ≤ 30000 * ‖q‖ ^ 3 := by
    rw [show Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2)
        = Work.Kernels.E4Fun w - 1 - 240 * q - 2160 * q ^ 2 by ring]
    exact h4
  have hunorm6 : ‖Work.Kernels.E6Fun w - (1 - 504 * q - 16632 * q ^ 2)‖ ≤ 1000000 * ‖q‖ ^ 3 := by
    rw [show Work.Kernels.E6Fun w - (1 - 504 * q - 16632 * q ^ 2)
        = Work.Kernels.E6Fun w - 1 + 504 * q + 16632 * q ^ 2 by ring]
    exact h6
  -- the `E₄³` remainder
  have hA : ‖Work.Kernels.E4Fun w ^ 3 - 1 - 720 * q - 179280 * q ^ 2‖ ≤ 20000000 * ‖q‖ ^ 3 := by
    have hid : Work.Kernels.E4Fun w ^ 3 - 1 - 720 * q - 179280 * q ^ 2
        = (3110400 * q ^ 3 + 13996800 * q ^ 4 + (240 * q + 2160 * q ^ 2) ^ 3)
          + (3 * (1 + 240 * q + 2160 * q ^ 2) ^ 2 * (Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2))
            + 3 * (1 + 240 * q + 2160 * q ^ 2) * (Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2)) ^ 2
            + (Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2)) ^ 3) := by ring
    rw [hid]
    have h1 : ‖3110400 * q ^ 3 + 13996800 * q ^ 4 + (240 * q + 2160 * q ^ 2) ^ 3‖
        ≤ 17900000 * ‖q‖ ^ 3 := by
      have hw3 : ‖(240 * q + 2160 * q ^ 2) ^ 3‖ ≤ (245 : ℝ) ^ 3 * ‖q‖ ^ 3 := by
        rw [norm_pow]
        have hb : ‖240 * q + 2160 * q ^ 2‖ ≤ 245 * ‖q‖ := by
          calc ‖240 * q + 2160 * q ^ 2‖ ≤ ‖240 * q‖ + ‖2160 * q ^ 2‖ := norm_add_le _ _
            _ = 240 * ‖q‖ + 2160 * ‖q‖ ^ 2 := by rw [norm_mul, norm_mul, norm_pow]; norm_num
            _ ≤ 245 * ‖q‖ := by
                have : 2160 * ‖q‖ ^ 2 ≤ 5 * ‖q‖ := by
                  have h5 : ‖q‖ * ‖q‖ ≤ (1 / 512) * ‖q‖ :=
                    mul_le_mul_of_nonneg_right hr hr0
                  nlinarith
                linarith
        have hb0 : (0 : ℝ) ≤ ‖240 * q + 2160 * q ^ 2‖ := norm_nonneg _
        calc ‖240 * q + 2160 * q ^ 2‖ ^ 3 ≤ (245 * ‖q‖) ^ 3 :=
              pow_le_pow_left₀ hb0 hb 3
          _ = 245 ^ 3 * ‖q‖ ^ 3 := by rw [mul_pow]
      have hq3 : ‖q ^ 3‖ = ‖q‖ ^ 3 := norm_pow _ _
      have hq4 : ‖q ^ 4‖ = ‖q‖ ^ 4 := norm_pow _ _
      have h4b : ‖q‖ ^ 4 ≤ (1 / 512) * ‖q‖ ^ 3 := by
        have : ‖q‖ * ‖q‖ ^ 3 ≤ (1 / 512) * ‖q‖ ^ 3 := mul_le_mul_of_nonneg_right hr (by positivity)
        calc ‖q‖ ^ 4 = ‖q‖ * ‖q‖ ^ 3 := by ring
          _ ≤ (1 / 512) * ‖q‖ ^ 3 := this
      calc ‖3110400 * q ^ 3 + 13996800 * q ^ 4 + (240 * q + 2160 * q ^ 2) ^ 3‖
          ≤ ‖3110400 * q ^ 3 + 13996800 * q ^ 4‖ + ‖(240 * q + 2160 * q ^ 2) ^ 3‖ :=
            norm_add_le _ _
        _ ≤ (‖3110400 * q ^ 3‖ + ‖13996800 * q ^ 4‖) + (245 : ℝ) ^ 3 * ‖q‖ ^ 3 := by
            linarith [norm_add_le (3110400 * q ^ 3) (13996800 * q ^ 4), hw3]
        _ = (3110400 * ‖q‖ ^ 3 + 13996800 * ‖q‖ ^ 4) + 245 ^ 3 * ‖q‖ ^ 3 := by
            rw [norm_mul, norm_mul, hq3, hq4]; norm_num
        _ ≤ 17900000 * ‖q‖ ^ 3 := by
            have h2 : 13996800 * ‖q‖ ^ 4 ≤ 13996800 * ((1 / 512) * ‖q‖ ^ 3) :=
              mul_le_mul_of_nonneg_left h4b (by norm_num)
            have h3 : (0 : ℝ) ≤ ‖q‖ ^ 3 := by positivity
            nlinarith [h2, h3]
    have h2 : ‖3 * (1 + 240 * q + 2160 * q ^ 2) ^ 2 * (Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2))
        + 3 * (1 + 240 * q + 2160 * q ^ 2) * (Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2)) ^ 2
        + (Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2)) ^ 3‖ ≤ 400000 * ‖q‖ ^ 3 := by
      have hP2 : ‖(1 + 240 * q + 2160 * q ^ 2) ^ 2‖ ≤ (3 / 2 : ℝ) ^ 2 := by
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) hPnorm 2
      have hP0 : (0 : ℝ) ≤ ‖(1 : ℂ) + 240 * q + 2160 * q ^ 2‖ := norm_nonneg _
      have hu4b : ‖Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2)‖ ^ 2
          ≤ 30000 * ‖q‖ ^ 3 := by
        have h3 : (0 : ℝ) ≤ ‖q‖ ^ 3 := by positivity
        calc ‖Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2)‖ ^ 2
            ≤ (30000 * ‖q‖ ^ 3) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hunorm4 2
          _ = 900000000 * ‖q‖ ^ 6 := by ring
          _ ≤ 900000000 * ((1 / 512) ^ 3 * ‖q‖ ^ 3) := by
              have : ‖q‖ ^ 6 = ‖q‖ ^ 3 * ‖q‖ ^ 3 := by ring
              have hq3 : ‖q‖ ^ 3 ≤ (1 / 512) ^ 3 := pow_le_pow_left₀ hr0 hr 3
              nlinarith [hq3, h3]
          _ ≤ 30000 * ‖q‖ ^ 3 := by
              have h3' : (0 : ℝ) ≤ ‖q‖ ^ 3 := by positivity
              nlinarith [h3']
      have h3b : ‖Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2)‖ ^ 3 ≤ 30000 * ‖q‖ ^ 3 := by
        have h3 : (0 : ℝ) ≤ ‖q‖ ^ 3 := by positivity
        have hsmall : ‖Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2)‖ ≤ 1 := by
          calc _ ≤ 30000 * ‖q‖ ^ 3 := hunorm4
            _ ≤ 30000 * ((1 / 512) ^ 3 * 1) := by
                have hq3 : ‖q‖ ^ 3 ≤ (1 / 512) ^ 3 := pow_le_pow_left₀ hr0 hr 3
                nlinarith
            _ ≤ 1 := by norm_num
        calc ‖Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2)‖ ^ 3
            = ‖Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2)‖ ^ 2
              * ‖Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2)‖ := by ring
          _ ≤ (30000 * ‖q‖ ^ 3) * 1 :=
              mul_le_mul hu4b hsmall (norm_nonneg _) (by positivity)
          _ = 30000 * ‖q‖ ^ 3 := by ring
      calc ‖3 * (1 + 240 * q + 2160 * q ^ 2) ^ 2 * (Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2))
          + 3 * (1 + 240 * q + 2160 * q ^ 2) * (Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2)) ^ 2
          + (Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2)) ^ 3‖
          ≤ ‖3 * (1 + 240 * q + 2160 * q ^ 2) ^ 2 * (Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2))
              + 3 * (1 + 240 * q + 2160 * q ^ 2) * (Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2)) ^ 2‖
            + ‖(Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2)) ^ 3‖ := norm_add_le _ _
        _ ≤ (‖3 * (1 + 240 * q + 2160 * q ^ 2) ^ 2 * (Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2))‖
              + ‖3 * (1 + 240 * q + 2160 * q ^ 2) * (Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2)) ^ 2‖)
            + ‖Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2)‖ ^ 3 := by
            have h := norm_add_le (3 * (1 + 240 * q + 2160 * q ^ 2) ^ 2 * (Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2)))
              (3 * (1 + 240 * q + 2160 * q ^ 2) * (Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2)) ^ 2)
            rw [norm_pow] at *
            linarith
        _ ≤ 400000 * ‖q‖ ^ 3 := by
            have hterm1 : ‖3 * (1 + 240 * q + 2160 * q ^ 2) ^ 2 * (Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2))‖
                ≤ 3 * (3 / 2 : ℝ) ^ 2 * (30000 * ‖q‖ ^ 3) := by
              rw [norm_mul, norm_mul]
              have h3n : ‖(3 : ℂ)‖ = (3 : ℝ) := by norm_num
              rw [h3n]
              have hu0 : (0 : ℝ) ≤ ‖Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2)‖ := norm_nonneg _
              have h3nn : (0 : ℝ) ≤ (3 : ℝ) := by norm_num
              calc 3 * ‖(1 + 240 * q + 2160 * q ^ 2) ^ 2‖ * ‖Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2)‖
                  ≤ 3 * (3 / 2 : ℝ) ^ 2 * (30000 * ‖q‖ ^ 3) := by
                    apply mul_le_mul (mul_le_mul_of_nonneg_left hP2 h3nn) hunorm4 hu0 (by positivity)
                _ = _ := rfl
            have hterm2 : ‖3 * (1 + 240 * q + 2160 * q ^ 2) * (Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2)) ^ 2‖
                ≤ 3 * (3 / 2 : ℝ) * (30000 * ‖q‖ ^ 3) := by
              rw [norm_mul, norm_mul, norm_pow]
              have h3n : ‖(3 : ℂ)‖ = (3 : ℝ) := by norm_num
              rw [h3n]
              apply mul_le_mul (mul_le_mul_of_nonneg_left hPnorm (by norm_num : (0:ℝ) ≤ 3)) hu4b (by positivity) (by positivity)
            have h3pow : ‖Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2)‖ ^ 3 ≤ 30000 * ‖q‖ ^ 3 := h3b
            nlinarith [hterm1, hterm2, h3pow, hr0]
    calc ‖(3110400 * q ^ 3 + 13996800 * q ^ 4 + (240 * q + 2160 * q ^ 2) ^ 3)
          + (3 * (1 + 240 * q + 2160 * q ^ 2) ^ 2 * (Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2))
            + 3 * (1 + 240 * q + 2160 * q ^ 2) * (Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2)) ^ 2
            + (Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2)) ^ 3)‖
        ≤ ‖3110400 * q ^ 3 + 13996800 * q ^ 4 + (240 * q + 2160 * q ^ 2) ^ 3‖
          + ‖3 * (1 + 240 * q + 2160 * q ^ 2) ^ 2 * (Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2))
            + 3 * (1 + 240 * q + 2160 * q ^ 2) * (Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2)) ^ 2
            + (Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2)) ^ 3‖ := norm_add_le _ _
      _ ≤ 17900000 * ‖q‖ ^ 3 + 400000 * ‖q‖ ^ 3 := add_le_add h1 h2
      _ ≤ 20000000 * ‖q‖ ^ 3 := by
          have h3 : (0 : ℝ) ≤ ‖q‖ ^ 3 := by positivity
          linarith
  -- the `E₆²` remainder
  have hB : ‖Work.Kernels.E6Fun w ^ 2 - 1 + 1008 * q - 220752 * q ^ 2‖ ≤ 30000000 * ‖q‖ ^ 3 := by
    have hid : Work.Kernels.E6Fun w ^ 2 - 1 + 1008 * q - 220752 * q ^ 2
        = (16765056 * q ^ 3 + 276623424 * q ^ 4)
          + (2 * (1 - 504 * q - 16632 * q ^ 2) * (Work.Kernels.E6Fun w - (1 - 504 * q - 16632 * q ^ 2))
            + (Work.Kernels.E6Fun w - (1 - 504 * q - 16632 * q ^ 2)) ^ 2) := by ring
    rw [hid]
    have h1 : ‖16765056 * q ^ 3 + 276623424 * q ^ 4‖ ≤ 17400000 * ‖q‖ ^ 3 := by
      have hq3 : ‖q ^ 3‖ = ‖q‖ ^ 3 := norm_pow _ _
      have hq4 : ‖q‖ ^ 4 ≤ (1 / 512) * ‖q‖ ^ 3 := by
        have : ‖q‖ * ‖q‖ ^ 3 ≤ (1 / 512) * ‖q‖ ^ 3 := mul_le_mul_of_nonneg_right hr (by positivity)
        calc ‖q‖ ^ 4 = ‖q‖ * ‖q‖ ^ 3 := by ring
          _ ≤ (1 / 512) * ‖q‖ ^ 3 := this
      calc ‖16765056 * q ^ 3 + 276623424 * q ^ 4‖
          ≤ ‖16765056 * q ^ 3‖ + ‖276623424 * q ^ 4‖ := norm_add_le _ _
        _ = 16765056 * ‖q‖ ^ 3 + 276623424 * ‖q‖ ^ 4 := by
            rw [norm_mul, norm_mul, norm_pow, norm_pow]
            norm_num
        _ ≤ 17400000 * ‖q‖ ^ 3 := by
            have h2 : 276623424 * ‖q‖ ^ 4 ≤ 276623424 * ((1 / 512) * ‖q‖ ^ 3) :=
              mul_le_mul_of_nonneg_left hq4 (by norm_num)
            have h3 : (0 : ℝ) ≤ ‖q‖ ^ 3 := by positivity
            nlinarith [h2, h3]
    have h2 : ‖2 * (1 - 504 * q - 16632 * q ^ 2) * (Work.Kernels.E6Fun w - (1 - 504 * q - 16632 * q ^ 2))
        + (Work.Kernels.E6Fun w - (1 - 504 * q - 16632 * q ^ 2)) ^ 2‖ ≤ 8000000 * ‖q‖ ^ 3 := by
      have hv2 : ‖Work.Kernels.E6Fun w - (1 - 504 * q - 16632 * q ^ 2)‖ ^ 2 ≤ 1000000 * ‖q‖ ^ 3 := by
        have h3 : (0 : ℝ) ≤ ‖q‖ ^ 3 := by positivity
        calc ‖Work.Kernels.E6Fun w - (1 - 504 * q - 16632 * q ^ 2)‖ ^ 2
            ≤ (1000000 * ‖q‖ ^ 3) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hunorm6 2
          _ = 1000000000000 * ‖q‖ ^ 6 := by ring
          _ ≤ 1000000000000 * ((1 / 512) ^ 3 * ‖q‖ ^ 3) := by
              have : ‖q‖ ^ 6 = ‖q‖ ^ 3 * ‖q‖ ^ 3 := by ring
              have hq3 : ‖q‖ ^ 3 ≤ (1 / 512) ^ 3 := pow_le_pow_left₀ hr0 hr 3
              nlinarith [hq3, h3]
          _ ≤ 1000000 * ‖q‖ ^ 3 := by
              have h3' : (0 : ℝ) ≤ ‖q‖ ^ 3 := by positivity
              nlinarith [h3']
      calc ‖2 * (1 - 504 * q - 16632 * q ^ 2) * (Work.Kernels.E6Fun w - (1 - 504 * q - 16632 * q ^ 2))
          + (Work.Kernels.E6Fun w - (1 - 504 * q - 16632 * q ^ 2)) ^ 2‖
          ≤ ‖2 * (1 - 504 * q - 16632 * q ^ 2) * (Work.Kernels.E6Fun w - (1 - 504 * q - 16632 * q ^ 2))‖
            + ‖(Work.Kernels.E6Fun w - (1 - 504 * q - 16632 * q ^ 2)) ^ 2‖ := norm_add_le _ _
        _ = 2 * ‖(1 - 504 * q - 16632 * q ^ 2)‖ * ‖Work.Kernels.E6Fun w - (1 - 504 * q - 16632 * q ^ 2)‖
            + ‖Work.Kernels.E6Fun w - (1 - 504 * q - 16632 * q ^ 2)‖ ^ 2 := by
            rw [norm_mul, norm_mul, norm_pow]
            norm_num
        _ ≤ 2 * 3 * (1000000 * ‖q‖ ^ 3) + 1000000 * ‖q‖ ^ 3 := by
            have hv0 : (0 : ℝ) ≤ ‖Work.Kernels.E6Fun w - (1 - 504 * q - 16632 * q ^ 2)‖ := norm_nonneg _
            have h2 : 2 * ‖(1 - 504 * q - 16632 * q ^ 2)‖ ≤ 2 * 3 := by linarith [hQnorm]
            have h3 : 2 * ‖(1 - 504 * q - 16632 * q ^ 2)‖ * ‖Work.Kernels.E6Fun w - (1 - 504 * q - 16632 * q ^ 2)‖
                ≤ 6 * (1000000 * ‖q‖ ^ 3) := by
              calc _ ≤ (2 * 3) * (1000000 * ‖q‖ ^ 3) := by
                    apply mul_le_mul h2 hunorm6 hv0 (by norm_num)
                _ = 6 * (1000000 * ‖q‖ ^ 3) := by ring
            linarith [h3, hv2]
        _ ≤ 8000000 * ‖q‖ ^ 3 := by
            have h3 : (0 : ℝ) ≤ ‖q‖ ^ 3 := by positivity
            nlinarith [h3]
    calc ‖(16765056 * q ^ 3 + 276623424 * q ^ 4)
          + (2 * (1 - 504 * q - 16632 * q ^ 2) * (Work.Kernels.E6Fun w - (1 - 504 * q - 16632 * q ^ 2))
            + (Work.Kernels.E6Fun w - (1 - 504 * q - 16632 * q ^ 2)) ^ 2)‖
        ≤ ‖16765056 * q ^ 3 + 276623424 * q ^ 4‖
          + ‖2 * (1 - 504 * q - 16632 * q ^ 2) * (Work.Kernels.E6Fun w - (1 - 504 * q - 16632 * q ^ 2))
            + (Work.Kernels.E6Fun w - (1 - 504 * q - 16632 * q ^ 2)) ^ 2‖ := norm_add_le _ _
      _ ≤ 17400000 * ‖q‖ ^ 3 + 8000000 * ‖q‖ ^ 3 := add_le_add h1 h2
      _ ≤ 30000000 * ‖q‖ ^ 3 := by
          have h3 : (0 : ℝ) ≤ ‖q‖ ^ 3 := by positivity
          linarith
  -- conclusion
  have hkey : (Work.Kernels.E4Fun w ^ 3 - Work.Kernels.E6Fun w ^ 2) / 1728 - q + 24 * q ^ 2
      = ((Work.Kernels.E4Fun w ^ 3 - 1 - 720 * q - 179280 * q ^ 2)
          - (Work.Kernels.E6Fun w ^ 2 - 1 + 1008 * q - 220752 * q ^ 2)) / 1728 := by ring
  have hnum : ‖(Work.Kernels.E4Fun w ^ 3 - 1 - 720 * q - 179280 * q ^ 2)
      - (Work.Kernels.E6Fun w ^ 2 - 1 + 1008 * q - 220752 * q ^ 2)‖
      ≤ 50000000 * ‖q‖ ^ 3 := by
    calc _ ≤ ‖Work.Kernels.E4Fun w ^ 3 - 1 - 720 * q - 179280 * q ^ 2‖
          + ‖Work.Kernels.E6Fun w ^ 2 - 1 + 1008 * q - 220752 * q ^ 2‖ := norm_sub_le _ _
      _ ≤ 20000000 * ‖q‖ ^ 3 + 30000000 * ‖q‖ ^ 3 := add_le_add hA hB
      _ = 50000000 * ‖q‖ ^ 3 := by ring
  rw [hD, hkey, norm_div, Complex.norm_ofNat]
  have h3 : (0 : ℝ) ≤ ‖q‖ ^ 3 := by positivity
  calc ‖(Work.Kernels.E4Fun w ^ 3 - 1 - 720 * q - 179280 * q ^ 2)
        - (Work.Kernels.E6Fun w ^ 2 - 1 + 1008 * q - 220752 * q ^ 2)‖ / 1728
      ≤ (50000000 * ‖q‖ ^ 3) / 1728 := by
        exact div_le_div_of_nonneg_right hnum (by norm_num)
    _ ≤ 100000 * ‖q‖ ^ 3 := by linarith

/-! ## The main pointwise bound `‖j - q⁻¹ - 744‖ ≤ 10^7 ‖q‖` on `Im ≥ 1` -/

/-- Elementary power comparison: if `0 ≤ r ≤ c` then `r ^ (n+1) ≤ c * r ^ n`. -/
lemma cfx_pow_succ_le_mul {r c : ℝ} (h0 : 0 ≤ r) (h : r ≤ c) (n : ℕ) :
    r ^ (n + 1) ≤ c * r ^ n := by
  rw [pow_succ]
  calc r ^ n * r ≤ r ^ n * c := mul_le_mul_of_nonneg_left h (pow_nonneg h0 n)
    _ = c * r ^ n := by ring

/-- Second-order expansion of `E₄` with explicit constant: on `Im w ≥ 1`,
`E₄ w = 1 + 240 q + O(‖q‖²)`. -/
lemma cfx_E4_second_order_explicit (w : ℍ) (hw : 1 ≤ w.im) :
    ‖Work.Kernels.E4Fun w - 1 - 240 * Work.Kernels.qParamFun w‖
      ≤ 2300 * ‖Work.Kernels.qParamFun w‖ ^ 2 := by
  have h := cfx_E4_third_order w hw
  have hr : ‖Work.Kernels.qParamFun w‖ ≤ 1 / 512 := cfx_norm_qParamFun_le_inv512 w hw
  have hr0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun w‖ := norm_nonneg _
  have hid : Work.Kernels.E4Fun w - 1 - 240 * Work.Kernels.qParamFun w
      = 2160 * Work.Kernels.qParamFun w ^ 2
        + (Work.Kernels.E4Fun w - 1 - 240 * Work.Kernels.qParamFun w
            - 2160 * Work.Kernels.qParamFun w ^ 2) := by ring
  rw [hid]
  have h2160 : ‖(2160 : ℂ) * Work.Kernels.qParamFun w ^ 2‖
      = 2160 * ‖Work.Kernels.qParamFun w‖ ^ 2 := by
    rw [norm_mul, norm_pow]; norm_num
  calc ‖2160 * Work.Kernels.qParamFun w ^ 2
        + (Work.Kernels.E4Fun w - 1 - 240 * Work.Kernels.qParamFun w
            - 2160 * Work.Kernels.qParamFun w ^ 2)‖
      ≤ ‖2160 * Work.Kernels.qParamFun w ^ 2‖
        + ‖Work.Kernels.E4Fun w - 1 - 240 * Work.Kernels.qParamFun w
            - 2160 * Work.Kernels.qParamFun w ^ 2‖ := norm_add_le _ _
    _ ≤ 2160 * ‖Work.Kernels.qParamFun w‖ ^ 2 + 30000 * ‖Work.Kernels.qParamFun w‖ ^ 3 := by
        rw [h2160]; linarith [h]
    _ ≤ 2300 * ‖Work.Kernels.qParamFun w‖ ^ 2 := by
        have h3 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun w‖ ^ 2 := by positivity
        have h6 : ‖Work.Kernels.qParamFun w‖ ^ 3 ≤ (1 / 512) * ‖Work.Kernels.qParamFun w‖ ^ 2 :=
          cfx_pow_succ_le_mul hr0 hr 2
        nlinarith [h3, h6]

/-- Third-order expansion of the cube: on `Im w ≥ 1`, `E₄ w³ - 1 - 720 q = O(‖q‖²)`. -/
lemma cfx_E4_cube_bound (w : ℍ) (hw : 1 ≤ w.im) :
    ‖Work.Kernels.E4Fun w ^ 3 - 1 - 720 * Work.Kernels.qParamFun w‖
      ≤ 300000 * ‖Work.Kernels.qParamFun w‖ ^ 2 := by
  set q := Work.Kernels.qParamFun w with hq
  have hr : ‖q‖ ≤ 1 / 512 := by rw [hq]; exact cfx_norm_qParamFun_le_inv512 w hw
  have hr0 : (0 : ℝ) ≤ ‖q‖ := norm_nonneg _
  have h2 : ‖Work.Kernels.E4Fun w - (1 + 240 * q)‖ ≤ 2300 * ‖q‖ ^ 2 := by
    rw [show Work.Kernels.E4Fun w - (1 + 240 * q)
        = Work.Kernels.E4Fun w - 1 - 240 * q by ring]
    rw [hq]; exact cfx_E4_second_order_explicit w hw
  have hid : Work.Kernels.E4Fun w ^ 3 - 1 - 720 * q
      = 3 * (Work.Kernels.E4Fun w - (1 + 240 * q)) + 172800 * q ^ 2
        + 1440 * q * (Work.Kernels.E4Fun w - (1 + 240 * q))
        + 3 * (Work.Kernels.E4Fun w - (1 + 240 * q)) ^ 2
        + (240 * q + (Work.Kernels.E4Fun w - (1 + 240 * q))) ^ 3 := by ring
  rw [hid]
  -- individual bounds
  have hq2 : ‖q ^ 2‖ = ‖q‖ ^ 2 := norm_pow _ _
  have hq3 : ‖q ^ 3‖ = ‖q‖ ^ 3 := norm_pow _ _
  have h2sq : ‖Work.Kernels.E4Fun w - (1 + 240 * q)‖ ^ 2 ≤ 11000 * ‖q‖ ^ 3 := by
    have h3 : (0 : ℝ) ≤ ‖q‖ ^ 3 := by positivity
    calc ‖Work.Kernels.E4Fun w - (1 + 240 * q)‖ ^ 2 ≤ (2300 * ‖q‖ ^ 2) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h2 2
      _ = 5290000 * ‖q‖ ^ 4 := by ring
      _ ≤ 5290000 * ((1 / 512) * ‖q‖ ^ 3) :=
          mul_le_mul_of_nonneg_left (cfx_pow_succ_le_mul hr0 hr 3) (by norm_num)
      _ ≤ 11000 * ‖q‖ ^ 3 := by nlinarith [h3]
  have hsum_w : ‖240 * q + (Work.Kernels.E4Fun w - (1 + 240 * q))‖ ≤ 245 * ‖q‖ := by
    have hb : ‖240 * q + (Work.Kernels.E4Fun w - (1 + 240 * q))‖
        ≤ 240 * ‖q‖ + 2300 * ‖q‖ ^ 2 := by
      calc ‖240 * q + (Work.Kernels.E4Fun w - (1 + 240 * q))‖
          ≤ ‖240 * q‖ + ‖Work.Kernels.E4Fun w - (1 + 240 * q)‖ := norm_add_le _ _
        _ ≤ 240 * ‖q‖ + 2300 * ‖q‖ ^ 2 := by
            have h240 : ‖240 * q‖ = 240 * ‖q‖ := by rw [norm_mul]; norm_num
            rw [h240]; linarith [h2]
    have h5 : 2300 * ‖q‖ ^ 2 ≤ 5 * ‖q‖ := by
      have h6 : ‖q‖ ^ 2 ≤ (1 / 512) * ‖q‖ := by
        simpa using cfx_pow_succ_le_mul hr0 hr 1
      linarith [mul_le_mul_of_nonneg_left h6 (by norm_num : (0 : ℝ) ≤ 2300), hr0]
    linarith
  have hcu : ‖(240 * q + (Work.Kernels.E4Fun w - (1 + 240 * q))) ^ 3‖ ≤ 245 ^ 3 * ‖q‖ ^ 3 := by
    rw [norm_pow]
    calc ‖240 * q + (Work.Kernels.E4Fun w - (1 + 240 * q))‖ ^ 3 ≤ (245 * ‖q‖) ^ 3 :=
          pow_le_pow_left₀ (norm_nonneg _) hsum_w 3
      _ = 245 ^ 3 * ‖q‖ ^ 3 := by rw [mul_pow]
  calc ‖3 * (Work.Kernels.E4Fun w - (1 + 240 * q)) + 172800 * q ^ 2
        + 1440 * q * (Work.Kernels.E4Fun w - (1 + 240 * q))
        + 3 * (Work.Kernels.E4Fun w - (1 + 240 * q)) ^ 2
        + (240 * q + (Work.Kernels.E4Fun w - (1 + 240 * q))) ^ 3‖
      ≤ ‖3 * (Work.Kernels.E4Fun w - (1 + 240 * q)) + 172800 * q ^ 2
          + 1440 * q * (Work.Kernels.E4Fun w - (1 + 240 * q))
          + 3 * (Work.Kernels.E4Fun w - (1 + 240 * q)) ^ 2‖
        + ‖(240 * q + (Work.Kernels.E4Fun w - (1 + 240 * q))) ^ 3‖ := norm_add_le _ _
    _ ≤ (‖3 * (Work.Kernels.E4Fun w - (1 + 240 * q)) + 172800 * q ^ 2
          + 1440 * q * (Work.Kernels.E4Fun w - (1 + 240 * q))‖
          + ‖3 * (Work.Kernels.E4Fun w - (1 + 240 * q)) ^ 2‖) + 245 ^ 3 * ‖q‖ ^ 3 := by
        linarith [norm_add_le (3 * (Work.Kernels.E4Fun w - (1 + 240 * q)) + 172800 * q ^ 2
          + 1440 * q * (Work.Kernels.E4Fun w - (1 + 240 * q)))
          (3 * (Work.Kernels.E4Fun w - (1 + 240 * q)) ^ 2), hcu]
    _ ≤ ((‖3 * (Work.Kernels.E4Fun w - (1 + 240 * q)) + 172800 * q ^ 2‖
          + ‖1440 * q * (Work.Kernels.E4Fun w - (1 + 240 * q))‖)
          + ‖3 * (Work.Kernels.E4Fun w - (1 + 240 * q)) ^ 2‖) + 245 ^ 3 * ‖q‖ ^ 3 := by
        linarith [norm_add_le (3 * (Work.Kernels.E4Fun w - (1 + 240 * q)) + 172800 * q ^ 2)
          (1440 * q * (Work.Kernels.E4Fun w - (1 + 240 * q)))]
    _ ≤ (((‖3 * (Work.Kernels.E4Fun w - (1 + 240 * q))‖ + ‖172800 * q ^ 2‖)
          + ‖1440 * q * (Work.Kernels.E4Fun w - (1 + 240 * q))‖)
          + ‖3 * (Work.Kernels.E4Fun w - (1 + 240 * q)) ^ 2‖) + 245 ^ 3 * ‖q‖ ^ 3 := by
        linarith [norm_add_le (3 * (Work.Kernels.E4Fun w - (1 + 240 * q))) (172800 * q ^ 2)]
    _ ≤ (((3 * (2300 * ‖q‖ ^ 2) + 172800 * ‖q‖ ^ 2)
          + 1440 * (‖q‖ * (2300 * ‖q‖ ^ 2)))
          + 3 * (11000 * ‖q‖ ^ 3)) + 245 ^ 3 * ‖q‖ ^ 3 := by
        have h3n : ‖(3 : ℂ)‖ = (3 : ℝ) := by norm_num
        have h1440 : ‖(1440 : ℂ)‖ = (1440 : ℝ) := by norm_num
        have h172800 : ‖(172800 : ℂ)‖ = (172800 : ℝ) := by norm_num
        have hA : ‖3 * (Work.Kernels.E4Fun w - (1 + 240 * q))‖ ≤ 3 * (2300 * ‖q‖ ^ 2) := by
          rw [norm_mul, h3n]
          exact mul_le_mul_of_nonneg_left h2 (by norm_num)
        have hB : ‖172800 * q ^ 2‖ = 172800 * ‖q‖ ^ 2 := by rw [norm_mul, hq2, h172800]
        have hC : ‖1440 * q * (Work.Kernels.E4Fun w - (1 + 240 * q))‖
            ≤ 1440 * (‖q‖ * (2300 * ‖q‖ ^ 2)) := by
          rw [norm_mul, norm_mul, h1440]
          rw [show (1440 : ℝ) * (‖q‖ * (2300 * ‖q‖ ^ 2)) = (1440 * ‖q‖) * (2300 * ‖q‖ ^ 2) by ring]
          exact mul_le_mul_of_nonneg_left h2 (by positivity)
        have hD : ‖3 * (Work.Kernels.E4Fun w - (1 + 240 * q)) ^ 2‖
            ≤ 3 * (11000 * ‖q‖ ^ 3) := by
          rw [norm_mul, h3n, norm_pow]
          exact mul_le_mul_of_nonneg_left h2sq (by norm_num)
        linarith [hA, hB, hC, hD]
    _ ≤ 300000 * ‖q‖ ^ 2 := by
        have h3 : (0 : ℝ) ≤ ‖q‖ ^ 2 := by positivity
        have h6 : ‖q‖ ^ 3 ≤ (1 / 512) * ‖q‖ ^ 2 := cfx_pow_succ_le_mul hr0 hr 2
        nlinarith [h3, h6]

/-- **The second-order cusp expansion of `j` on `Im ≥ 1`, with an explicit constant.**
`‖j w - q⁻¹ - 744‖ ≤ 10^7 ‖q w‖` for `Im w ≥ 1`. -/
theorem cfx_E_j_pointwise_Im_one (w : ℍ) (hw : 1 ≤ w.im) :
    ‖Work.Kernels.jInvariantFun w - (Work.Kernels.qParamFun w)⁻¹ - 744‖
      ≤ 10 ^ 7 * ‖Work.Kernels.qParamFun w‖ := by
  set q := Work.Kernels.qParamFun w with hq
  have hr : ‖q‖ ≤ 1 / 512 := by rw [hq]; exact cfx_norm_qParamFun_le_inv512 w hw
  have hr0 : (0 : ℝ) ≤ ‖q‖ := norm_nonneg _
  have hq0 : q ≠ 0 := by rw [hq]; exact cfx_qParamFun_ne_zero w
  have hΔne : Work.Kernels.DeltaFun w ≠ 0 := by
    simpa [Work.Kernels.DeltaFun] using ModularForm.discriminant_ne_zero w
  have hΔ : ‖Work.Kernels.DeltaFun w - q + 24 * q ^ 2‖ ≤ 100000 * ‖q‖ ^ 3 := by
    rw [hq]; exact cfx_Delta_third_order w hw
  have hcube : ‖Work.Kernels.E4Fun w ^ 3 - 1 - 720 * q‖ ≤ 300000 * ‖q‖ ^ 2 := by
    rw [hq]; exact cfx_E4_cube_bound w hw
  -- the numerator `E₄³ - Δ (q⁻¹ + 744)`
  have hnum : ‖Work.Kernels.E4Fun w ^ 3 - Work.Kernels.DeltaFun w * (q⁻¹ + 744)‖
      ≤ 600000 * ‖q‖ ^ 2 := by
    have hid : Work.Kernels.E4Fun w ^ 3 - Work.Kernels.DeltaFun w * (q⁻¹ + 744)
        = (Work.Kernels.E4Fun w ^ 3 - 1 - 720 * q)
          - (Work.Kernels.DeltaFun w - q + 24 * q ^ 2) * q⁻¹
          - 744 * (Work.Kernels.DeltaFun w - q + 24 * q ^ 2) + 17856 * q ^ 2 := by
      field_simp
      ring
    rw [hid]
    have heq : ‖(Work.Kernels.DeltaFun w - q + 24 * q ^ 2) * q⁻¹‖ ≤ 100000 * ‖q‖ ^ 2 := by
      rw [norm_mul, norm_inv]
      calc ‖Work.Kernels.DeltaFun w - q + 24 * q ^ 2‖ * ‖q‖⁻¹
          ≤ (100000 * ‖q‖ ^ 3) * ‖q‖⁻¹ := mul_le_mul_of_nonneg_right hΔ (by positivity)
        _ = 100000 * ‖q‖ ^ 2 := by
            have hc : ‖q‖ ^ 3 * ‖q‖⁻¹ = ‖q‖ ^ 2 := by
              rw [show ‖q‖ ^ 3 = ‖q‖ ^ 2 * ‖q‖ by ring, mul_assoc,
                mul_inv_cancel₀ (norm_ne_zero_iff.mpr hq0), mul_one]
            calc (100000 * ‖q‖ ^ 3) * ‖q‖⁻¹ = 100000 * (‖q‖ ^ 3 * ‖q‖⁻¹) := by ring
              _ = 100000 * ‖q‖ ^ 2 := by rw [hc]
    have he7 : ‖744 * (Work.Kernels.DeltaFun w - q + 24 * q ^ 2)‖ ≤ 145500 * ‖q‖ ^ 2 := by
      rw [norm_mul]
      have h744 : ‖(744 : ℂ)‖ = (744 : ℝ) := by norm_num
      rw [h744]
      have h6 : ‖q‖ ^ 3 ≤ (1 / 512) * ‖q‖ ^ 2 := cfx_pow_succ_le_mul hr0 hr 2
      calc 744 * ‖Work.Kernels.DeltaFun w - q + 24 * q ^ 2‖
          ≤ 744 * (100000 * ‖q‖ ^ 3) := mul_le_mul_of_nonneg_left hΔ (by norm_num)
        _ ≤ 145500 * ‖q‖ ^ 2 := by nlinarith [h6]
    have h18 : ‖17856 * q ^ 2‖ = 17856 * ‖q‖ ^ 2 := by
      rw [norm_mul, norm_pow]; norm_num
    have hstep1 : ‖(Work.Kernels.E4Fun w ^ 3 - 1 - 720 * q)
          - (Work.Kernels.DeltaFun w - q + 24 * q ^ 2) * q⁻¹
          - 744 * (Work.Kernels.DeltaFun w - q + 24 * q ^ 2)‖
        ≤ 300000 * ‖q‖ ^ 2 + 100000 * ‖q‖ ^ 2 + 145500 * ‖q‖ ^ 2 := by
      calc _ ≤ ‖(Work.Kernels.E4Fun w ^ 3 - 1 - 720 * q)
            - (Work.Kernels.DeltaFun w - q + 24 * q ^ 2) * q⁻¹‖
            + ‖744 * (Work.Kernels.DeltaFun w - q + 24 * q ^ 2)‖ := norm_sub_le _ _
        _ ≤ (‖Work.Kernels.E4Fun w ^ 3 - 1 - 720 * q‖
            + ‖(Work.Kernels.DeltaFun w - q + 24 * q ^ 2) * q⁻¹‖) + 145500 * ‖q‖ ^ 2 := by
            linarith [norm_sub_le (Work.Kernels.E4Fun w ^ 3 - 1 - 720 * q)
              ((Work.Kernels.DeltaFun w - q + 24 * q ^ 2) * q⁻¹), he7]
        _ ≤ _ := by linarith [hcube, heq]
    calc ‖(Work.Kernels.E4Fun w ^ 3 - 1 - 720 * q)
          - (Work.Kernels.DeltaFun w - q + 24 * q ^ 2) * q⁻¹
          - 744 * (Work.Kernels.DeltaFun w - q + 24 * q ^ 2) + 17856 * q ^ 2‖
        ≤ ‖(Work.Kernels.E4Fun w ^ 3 - 1 - 720 * q)
          - (Work.Kernels.DeltaFun w - q + 24 * q ^ 2) * q⁻¹
          - 744 * (Work.Kernels.DeltaFun w - q + 24 * q ^ 2)‖ + ‖17856 * q ^ 2‖ :=
          norm_add_le _ _
      _ ≤ (300000 * ‖q‖ ^ 2 + 100000 * ‖q‖ ^ 2 + 145500 * ‖q‖ ^ 2) + 17856 * ‖q‖ ^ 2 := by
          rw [h18]; linarith [hstep1]
      _ ≤ 600000 * ‖q‖ ^ 2 := by
          have h3 : (0 : ℝ) ≤ ‖q‖ ^ 2 := by positivity
          linarith
  have hden : (1 / 2 : ℝ) * ‖q‖ ≤ ‖Work.Kernels.DeltaFun w‖ := by
    have h6 : ‖q‖ ^ 3 ≤ (1 / 512) * ‖q‖ ^ 2 := cfx_pow_succ_le_mul hr0 hr 2
    have h7 : ‖Work.Kernels.DeltaFun w - q‖ ≤ (1 / 2 : ℝ) * ‖q‖ := by
      have h24 : ‖24 * q ^ 2‖ = 24 * ‖q‖ ^ 2 := by rw [norm_mul, norm_pow]; norm_num
      calc ‖Work.Kernels.DeltaFun w - q‖
          ≤ ‖Work.Kernels.DeltaFun w - q + 24 * q ^ 2‖ + ‖24 * q ^ 2‖ := by
            have h := norm_add_le (Work.Kernels.DeltaFun w - q + 24 * q ^ 2) (-(24 * q ^ 2))
            have he : Work.Kernels.DeltaFun w - q + 24 * q ^ 2 + -(24 * q ^ 2)
                = Work.Kernels.DeltaFun w - q := by ring
            rw [he, norm_neg] at h
            exact h
        _ ≤ 100000 * ‖q‖ ^ 3 + 24 * ‖q‖ ^ 2 := by rw [h24]; linarith [hΔ]
        _ ≤ (1 / 2 : ℝ) * ‖q‖ := by
            have h3 : (0 : ℝ) ≤ ‖q‖ ^ 2 := by positivity
            nlinarith [h6, h3]
    have h2 : ‖q‖ - ‖Work.Kernels.DeltaFun w - q‖ ≤ ‖Work.Kernels.DeltaFun w‖ := by
      have h3 := norm_sub_le (Work.Kernels.DeltaFun w) (Work.Kernels.DeltaFun w - q)
      have he : Work.Kernels.DeltaFun w - (Work.Kernels.DeltaFun w - q) = q := by ring
      rw [he] at h3
      linarith
    linarith
  have hj : Work.Kernels.jInvariantFun w - q⁻¹ - 744
      = (Work.Kernels.E4Fun w ^ 3 - Work.Kernels.DeltaFun w * (q⁻¹ + 744))
        / Work.Kernels.DeltaFun w := by
    rw [Work.Kernels.jInvariantFun]
    field_simp
    ring
  have hΔpos : 0 < ‖Work.Kernels.DeltaFun w‖ := norm_pos_iff.mpr hΔne
  have hqpos : 0 < ‖q‖ := norm_pos_iff.mpr hq0
  rw [hj]
  calc ‖(Work.Kernels.E4Fun w ^ 3 - Work.Kernels.DeltaFun w * (q⁻¹ + 744))
        / Work.Kernels.DeltaFun w‖
      = ‖Work.Kernels.E4Fun w ^ 3 - Work.Kernels.DeltaFun w * (q⁻¹ + 744)‖
        / ‖Work.Kernels.DeltaFun w‖ := norm_div _ _
    _ ≤ (600000 * ‖q‖ ^ 2) / ((1 / 2 : ℝ) * ‖q‖) :=
        div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = 1200000 * ‖q‖ := by
        field_simp
        ring
    _ ≤ 10 ^ 7 * ‖q‖ := by nlinarith [hr0]

/-! ## The lift of `F = j - q⁻¹ - 744` and its mean-value bound -/

/-- The lift of `F w = j w - q w⁻¹ - 744` to the upper half plane (as a function on `ℂ`). -/
noncomputable def cfx_F_lift (z : ℂ) : ℂ :=
  Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex z)
    - (Work.Kernels.qParamFun (UpperHalfPlane.ofComplex z))⁻¹ - 744

lemma cfx_F_lift_eq (z : ℂ) :
    cfx_F_lift z = Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex z)
      - (Work.Kernels.qParamFun (UpperHalfPlane.ofComplex z))⁻¹ - 744 := rfl

lemma cfx_coe_ofComplex (z : ℂ) (hz : 0 < z.im) :
    ((UpperHalfPlane.ofComplex z : ℍ) : ℂ) = z := by
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz, UpperHalfPlane.coe_mk]

/-- `cfx_F_lift` satisfies the pointwise bound of `cfx_E_j_pointwise_Im_one`. -/
lemma cfx_F_lift_bound (z : ℂ) (hz : 1 ≤ z.im) :
    ‖cfx_F_lift z‖ ≤ 10 ^ 7 * Real.exp (-(2 * Real.pi * z.im)) := by
  have hpos : 0 < z.im := by linarith
  have hcoe := cfx_coe_ofComplex z hpos
  have him : 1 ≤ (UpperHalfPlane.ofComplex z).im := by
    rw [← UpperHalfPlane.coe_im, hcoe]; exact hz
  have h := cfx_E_j_pointwise_Im_one (UpperHalfPlane.ofComplex z) him
  have hq : ‖Work.Kernels.qParamFun (UpperHalfPlane.ofComplex z)‖
      = Real.exp (-(2 * Real.pi * z.im)) := by
    rw [cfx_norm_qParamFun_eq, ← UpperHalfPlane.coe_im, hcoe]
  rw [hq] at h
  rw [cfx_F_lift_eq]
  exact h

/-- `cfx_F_lift` is complex differentiable on the upper half plane. -/
lemma cfx_F_lift_differentiableOn :
    DifferentiableOn ℂ cfx_F_lift {z : ℂ | 0 < z.im} := by
  have hΔ : Work.Kernels.DeltaFun = ⇑CuspForm.discriminant := rfl
  have hDne : ∀ w : ℍ, Work.Kernels.DeltaFun w ≠ 0 := fun w => by
    rw [hΔ]; exact ModularForm.discriminant_ne_zero w
  have hj : MDiff Work.Kernels.jInvariantFun :=
    ((ModularFormClass.holo ModularForm.E₄).pow 3).div
      (CuspFormClass.holo CuspForm.discriminant) hDne
  have hq : MDiff (fun w : ℍ => (Work.Kernels.qParamFun w)⁻¹) := by
    have h1 : MDiff Work.Kernels.qParamFun := by
      rw [UpperHalfPlane.mdifferentiable_iff]
      have hg : DifferentiableOn ℂ
          (fun z : ℂ => Complex.exp (2 * Real.pi * Complex.I * z)) {z : ℂ | 0 < z.im} :=
        (by fun_prop : Differentiable ℂ
          (fun z : ℂ => Complex.exp (2 * Real.pi * Complex.I * z))).differentiableOn
      refine hg.congr (fun z hz => ?_)
      rw [Function.comp_apply, Work.Kernels.qParamFun, cfx_coe_ofComplex z hz]
    exact h1.inv fun w => cfx_qParamFun_ne_zero w
  have hF : MDiff (fun w : ℍ => Work.Kernels.jInvariantFun w
      - (Work.Kernels.qParamFun w)⁻¹ - 744) :=
    (hj.sub hq).sub mdifferentiable_const
  have := (UpperHalfPlane.mdifferentiable_iff).mp hF
  exact this

/-- The closed ball of radius `1/2` about a point of `Im ≥ 3/2` stays in `Im ≥ 1 > 0`. -/
lemma cfx_closedBall_subset_im_pos (z : ℂ) (hz : 3 / 2 ≤ z.im) :
    closure (Metric.ball z (1 / 2)) ⊆ {w : ℂ | 0 < w.im} := by
  intro w hw
  have hw' : w ∈ Metric.closedBall z (1 / 2) := Metric.closure_ball_subset_closedBall hw
  rw [Metric.mem_closedBall, Complex.dist_eq] at hw'
  have h2 : |(w - z).im| ≤ ‖w - z‖ := Complex.abs_im_le_norm _
  have h4 : -((w - z).im) ≤ ‖w - z‖ := le_trans (neg_le_abs _) h2
  rw [Complex.sub_im] at h4
  have : (0 : ℝ) < w.im := by linarith
  simpa using this

/-- **Cauchy's estimate for the derivative of the lift** (radius `1/2`). -/
lemma cfx_F_lift_deriv_bound (z : ℂ) (hz : 3 / 2 ≤ z.im) :
    ‖deriv cfx_F_lift z‖ ≤ 2 * 10 ^ 9 * Real.exp (-(2 * Real.pi * z.im)) := by
  have hR : (0 : ℝ) < 1 / 2 := by norm_num
  have hsub : Metric.ball z (1 / 2) ⊆ {w : ℂ | 0 < w.im} :=
    subset_closure.trans (cfx_closedBall_subset_im_pos z hz)
  have hdiff : DiffContOnCl ℂ cfx_F_lift (Metric.ball z (1 / 2)) :=
    ⟨cfx_F_lift_differentiableOn.mono hsub,
      cfx_F_lift_differentiableOn.continuousOn.mono (cfx_closedBall_subset_im_pos z hz)⟩
  have hexpπ : Real.exp Real.pi ≤ 55 := by
    have h1 : Real.exp Real.pi ≤ Real.exp 4 := Real.exp_le_exp.mpr (le_of_lt Real.pi_lt_four)
    have h2 : Real.exp 4 = (Real.exp 1) ^ 4 := by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
    rw [h2] at h1
    have h3 : (2.7182818286 : ℝ) ^ 4 ≤ 55 := by norm_num
    have h4 : (Real.exp 1) ^ 4 ≤ (2.7182818286 : ℝ) ^ 4 :=
      pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1)) (le_of_lt Real.exp_one_lt_d9) 4
    linarith
  have hsp : ∀ w ∈ Metric.sphere z (1 / 2),
      ‖cfx_F_lift w‖ ≤ 10 ^ 7 * Real.exp Real.pi * Real.exp (-(2 * Real.pi * z.im)) := by
    intro w hw
    have hw' : ‖w - z‖ = 1 / 2 := by
      rw [Metric.mem_sphere, Complex.dist_eq] at hw; exact hw
    have him : 1 ≤ w.im := by
      have h2 : |(w - z).im| ≤ ‖w - z‖ := Complex.abs_im_le_norm _
      have h3 : -((w - z).im) ≤ ‖w - z‖ := le_trans (neg_le_abs _) h2
      rw [Complex.sub_im] at h3
      linarith [hw']
    calc ‖cfx_F_lift w‖ ≤ 10 ^ 7 * Real.exp (-(2 * Real.pi * w.im)) := cfx_F_lift_bound w him
      _ ≤ 10 ^ 7 * Real.exp (-(2 * Real.pi * (z.im - 1 / 2))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Real.exp_le_exp.mpr
          have h3 : -((w - z).im) ≤ ‖w - z‖ := le_trans (neg_le_abs _) (Complex.abs_im_le_norm _)
          rw [Complex.sub_im] at h3
          have h3' : z.im - w.im ≤ 1 / 2 := by linarith [h3, hw']
          rw [show -(2 * Real.pi * (z.im - 1 / 2)) = -(2 * Real.pi * z.im) + Real.pi by ring]
          nlinarith [h3', Real.pi_pos]
      _ = 10 ^ 7 * Real.exp Real.pi * Real.exp (-(2 * Real.pi * z.im)) := by
          rw [show -(2 * Real.pi * (z.im - 1 / 2)) = Real.pi + -(2 * Real.pi * z.im) by ring,
            Real.exp_add]
          ring
  have hmain := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := z) (R := 1 / 2)
    (C := 10 ^ 7 * Real.exp Real.pi * Real.exp (-(2 * Real.pi * z.im))) hR hdiff hsp
  rw [div_eq_mul_inv] at hmain
  have hexp : (0 : ℝ) ≤ Real.exp (-(2 * Real.pi * z.im)) := (Real.exp_pos _).le
  calc ‖deriv cfx_F_lift z‖
      ≤ (10 ^ 7 * Real.exp Real.pi * Real.exp (-(2 * Real.pi * z.im))) * (1 / 2)⁻¹ := hmain
    _ = 2 * 10 ^ 7 * Real.exp Real.pi * Real.exp (-(2 * Real.pi * z.im)) := by norm_num; ring
    _ ≤ 2 * 10 ^ 9 * Real.exp (-(2 * Real.pi * z.im)) := by nlinarith [hexp, hexpπ]

/-- **The mean-value bound for the lift.**  If the segment joining `z₀` and `z` stays in
`Im ≥ 3/2`, then `‖cfx_F_lift z - cfx_F_lift z₀‖ ≤ 2·10⁹ e^{-2π min (Im z) (Im z₀)} ‖z - z₀‖`. -/
theorem cfx_F_lift_diff_bound (z z₀ : ℂ)
    (hseg : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → 3 / 2 ≤ (z₀ + s • (z - z₀)).im) :
    ‖cfx_F_lift z - cfx_F_lift z₀‖
      ≤ 2 * 10 ^ 9 * Real.exp (-(2 * Real.pi * min z.im z₀.im)) * ‖z - z₀‖ := by
  have hFdiff : ∀ w : ℂ, 0 < w.im → DifferentiableAt ℂ cfx_F_lift w := fun w hw =>
    cfx_F_lift_differentiableOn.differentiableAt
      (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds (by simpa using hw))
  have hγ : ∀ s : ℝ, HasDerivAt (fun s : ℝ => z₀ + s • (z - z₀)) (z - z₀) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => s • (z - z₀)) ((1 : ℝ) • (z - z₀)) s :=
      (hasDerivAt_id s).smul_const (z - z₀)
    have h2 := h1.const_add z₀
    simpa using h2
  have hcomp : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun s : ℝ => cfx_F_lift (z₀ + s • (z - z₀)))
        (deriv cfx_F_lift (z₀ + s • (z - z₀)) * (z - z₀)) (Set.Icc (0 : ℝ) 1) s := by
    intro s hs
    have him : 0 < (z₀ + s • (z - z₀)).im := by linarith [hseg s hs]
    exact (((hFdiff _ him).hasDerivAt).comp s (hγ s)).hasDerivWithinAt
  have him_le : ∀ s ∈ Set.Icc (0 : ℝ) 1, min z.im z₀.im ≤ (z₀ + s • (z - z₀)).im := by
    intro s hs
    have hγim : (z₀ + s • (z - z₀)).im = (1 - s) * z₀.im + s * z.im := by
      simp only [Complex.add_im, Complex.smul_im, Complex.sub_im]
      ring
    rw [hγim]
    have h1 : min z.im z₀.im ≤ z.im := min_le_left _ _
    have h2 : min z.im z₀.im ≤ z₀.im := min_le_right _ _
    nlinarith [hs.1, hs.2]
  have hbound : ∀ s ∈ Set.Ico (0 : ℝ) 1,
      ‖deriv cfx_F_lift (z₀ + s • (z - z₀)) * (z - z₀)‖
        ≤ 2 * 10 ^ 9 * Real.exp (-(2 * Real.pi * min z.im z₀.im)) * ‖z - z₀‖ := by
    intro s hs
    have hs' : s ∈ Set.Icc (0 : ℝ) 1 := Set.Ico_subset_Icc_self hs
    have him : 3 / 2 ≤ (z₀ + s • (z - z₀)).im := hseg s hs'
    calc ‖deriv cfx_F_lift (z₀ + s • (z - z₀)) * (z - z₀)‖
        = ‖deriv cfx_F_lift (z₀ + s • (z - z₀))‖ * ‖z - z₀‖ := norm_mul _ _
      _ ≤ (2 * 10 ^ 9 * Real.exp (-(2 * Real.pi * (z₀ + s • (z - z₀)).im))) * ‖z - z₀‖ :=
          mul_le_mul_of_nonneg_right (cfx_F_lift_deriv_bound _ him) (norm_nonneg _)
      _ ≤ (2 * 10 ^ 9 * Real.exp (-(2 * Real.pi * min z.im z₀.im))) * ‖z - z₀‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Real.exp_le_exp.mpr
          nlinarith [him_le s hs', Real.pi_pos]
  have hmain := norm_image_sub_le_of_norm_deriv_le_segment' (a := 0) (b := 1) hcomp hbound 1
    (by norm_num : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
  have h1 : cfx_F_lift (z₀ + (1 : ℝ) • (z - z₀)) = cfx_F_lift z := by
    rw [one_smul]; congr 1; ring
  have h0 : cfx_F_lift (z₀ + (0 : ℝ) • (z - z₀)) = cfx_F_lift z₀ := by
    rw [zero_smul, add_zero]
  rw [h1, h0, sub_zero, mul_one] at hmain
  exact hmain




/-! ## Integer translations of `j` and of `F` -/

/-- `F w = j w - q w⁻¹ - 744`. -/
noncomputable def cfx_Ffun (w : ℍ) : ℂ := Work.Kernels.jInvariantFun w - (Work.Kernels.qParamFun w)⁻¹ - 744

lemma cfx_Ffun_eq_F_lift (w : ℍ) : cfx_Ffun w = cfx_F_lift (w : ℂ) := by
  simp [cfx_Ffun, cfx_F_lift, UpperHalfPlane.ofComplex_apply]

lemma cfx_qParamFun_vadd_one (τ : ℍ) :
    Work.Kernels.qParamFun ((1 : ℝ) +ᵥ τ) = Work.Kernels.qParamFun τ := by
  simp only [Work.Kernels.qParamFun]
  rw [show ((((1 : ℝ) +ᵥ τ : ℍ)) : ℂ) = 1 + (τ : ℂ) by
    rw [UpperHalfPlane.coe_vadd]; push_cast; ring]
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (1 + (τ : ℂ))
      = (1 : ℤ) * (2 * (Real.pi : ℂ) * Complex.I) + 2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ) by
        push_cast; ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul]

lemma cfx_Ffun_vadd_one (τ : ℍ) : cfx_Ffun ((1 : ℝ) +ᵥ τ) = cfx_Ffun τ := by
  simp only [cfx_Ffun, cfx_qParamFun_vadd_one, Work.Kernels.KernelFacts.jInvariantFun_vadd_one]

lemma cfx_Ffun_nat_vadd : ∀ (m : ℕ) (τ : ℍ), cfx_Ffun ((m : ℝ) +ᵥ τ) = cfx_Ffun τ := by
  intro m
  induction m with
  | zero => intro τ; simp
  | succ k ih =>
      intro τ
      have h1 : ((k + 1 : ℕ) : ℝ) +ᵥ τ = (1 : ℝ) +ᵥ (((k : ℕ) : ℝ) +ᵥ τ) := by
        rw [← add_vadd]; push_cast; ring_nf
      rw [h1, cfx_Ffun_vadd_one, ih]

lemma cfx_Ffun_int_vadd (k : ℤ) (τ : ℍ) : cfx_Ffun ((k : ℝ) +ᵥ τ) = cfx_Ffun τ := by
  obtain ⟨m, hm | hm⟩ := Int.eq_nat_or_neg k
  · rw [hm]; push_cast; exact cfx_Ffun_nat_vadd m τ
  · rw [hm]
    have h1 : ((m : ℝ) +ᵥ ((-(m : ℝ)) +ᵥ τ)) = τ := by rw [← add_vadd]; simp
    have h2 := cfx_Ffun_nat_vadd m ((-(m : ℝ)) +ᵥ τ)
    rw [h1] at h2
    push_cast
    exact h2.symm

/-! ## Integer translations of `j` and of `q` -/

lemma cfx_jInvariantFun_nat_vadd : ∀ (m : ℕ) (τ : ℍ),
    Work.Kernels.jInvariantFun ((m : ℝ) +ᵥ τ) = Work.Kernels.jInvariantFun τ := by
  intro m
  induction m with
  | zero => intro τ; simp
  | succ k ih =>
      intro τ
      have h1 : ((k + 1 : ℕ) : ℝ) +ᵥ τ = (1 : ℝ) +ᵥ (((k : ℕ) : ℝ) +ᵥ τ) := by
        rw [← add_vadd]; push_cast; ring_nf
      rw [h1, Work.Kernels.KernelFacts.jInvariantFun_vadd_one, ih]

lemma cfx_jInvariantFun_int_vadd (k : ℤ) (τ : ℍ) :
    Work.Kernels.jInvariantFun ((k : ℝ) +ᵥ τ) = Work.Kernels.jInvariantFun τ := by
  obtain ⟨m, hm | hm⟩ := Int.eq_nat_or_neg k
  · rw [hm]; push_cast; exact cfx_jInvariantFun_nat_vadd m τ
  · rw [hm]
    have h1 : ((m : ℝ) +ᵥ ((-(m : ℝ)) +ᵥ τ)) = τ := by rw [← add_vadd]; simp
    have h2 := cfx_jInvariantFun_nat_vadd m ((-(m : ℝ)) +ᵥ τ)
    rw [h1] at h2
    push_cast
    exact h2.symm

lemma cfx_qParamFun_nat_vadd : ∀ (m : ℕ) (τ : ℍ),
    Work.Kernels.qParamFun ((m : ℝ) +ᵥ τ) = Work.Kernels.qParamFun τ := by
  intro m
  induction m with
  | zero => intro τ; simp
  | succ k ih =>
      intro τ
      have h1 : ((k + 1 : ℕ) : ℝ) +ᵥ τ = (1 : ℝ) +ᵥ (((k : ℕ) : ℝ) +ᵥ τ) := by
        rw [← add_vadd]; push_cast; ring_nf
      rw [h1, cfx_qParamFun_vadd_one, ih]

lemma cfx_qParamFun_int_vadd (k : ℤ) (τ : ℍ) :
    Work.Kernels.qParamFun ((k : ℝ) +ᵥ τ) = Work.Kernels.qParamFun τ := by
  obtain ⟨m, hm | hm⟩ := Int.eq_nat_or_neg k
  · rw [hm]; push_cast; exact cfx_qParamFun_nat_vadd m τ
  · rw [hm]
    have h1 : ((m : ℝ) +ᵥ ((-(m : ℝ)) +ᵥ τ)) = τ := by rw [← add_vadd]; simp
    have h2 := cfx_qParamFun_nat_vadd m ((-(m : ℝ)) +ᵥ τ)
    rw [h1] at h2
    push_cast
    exact h2.symm

/-! ## The exponential difference bound used in the "thin" case -/

/-- `|e^u - 1| ≥ |u|/2` for real `|u| ≤ 1`. -/
lemma cfx_abs_exp_sub_one_ge_half (u : ℝ) (hu : |u| ≤ 1) : |Real.exp u - 1| ≥ |u| / 2 := by
  rcases lt_or_ge u 0 with h | h
  · have h1 : Real.exp u ≤ 1 / (1 + (-u)) := by
      rw [le_div_iff₀ (by linarith)]
      have h3 : 1 + (-u) ≤ Real.exp (-u) := by linarith [Real.add_one_le_exp (-u)]
      have h4 : Real.exp u * Real.exp (-u) = 1 := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      nlinarith [Real.exp_pos u, Real.exp_pos (-u), h3, h4]
    rw [abs_of_neg h, abs_of_neg (by rw [sub_neg]; exact Real.exp_lt_one_iff.mpr h)]
    have h5 : 1 - 1 / (1 + (-u)) ≤ 1 - Real.exp u := by linarith
    have h6 : 1 - 1 / (1 + (-u)) = (-u) / (1 + (-u)) := by
      rw [one_sub_div (by linarith : (1 : ℝ) + (-u) ≠ 0)]
      ring
    have h7 : (-u) / 2 ≤ (-u) / (1 + (-u)) := by
      apply div_le_div_of_nonneg_left (by linarith) (by linarith)
      linarith [(abs_le.mp hu).1]
    linarith [h5, h6.le, h6.ge, h7]
  · rw [abs_of_nonneg h,
      abs_of_nonneg (by linarith [Real.add_one_le_exp u] : (0 : ℝ) ≤ Real.exp u - 1)]
    linarith [Real.add_one_le_exp u]

/-- **Key bound for the thin case.**  For `|Re X| ≤ 1/2` and `|Im X| ≤ 1/8`,
`‖exp (-2πiX) - 1‖ ≥ 2‖X‖`. -/
lemma cfx_norm_exp_neg_two_pi_I_sub_one_ge (X : ℂ) (h1 : |X.re| ≤ 1 / 2) (h2 : |X.im| ≤ 1 / 8) :
    ‖Complex.exp (-(2 * Real.pi * Complex.I * X)) - 1‖ ≥ 2 * ‖X‖ := by
  have harg : -(2 * Real.pi * Complex.I * X)
      = ((2 * Real.pi * X.im : ℝ) : ℂ) + ((-(2 * Real.pi * X.re) : ℝ) : ℂ) * Complex.I := by
    push_cast
    rw [Complex.ext_iff]
    constructor <;>
      simp only [Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.add_re,
        Complex.add_im] <;> ring
  have hRe : (-(2 * Real.pi * Complex.I * X)).re = 2 * Real.pi * X.im := by
    rw [harg, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re]
    ring
  have hIm : (-(2 * Real.pi * Complex.I * X)).im = -(2 * Real.pi * X.re) := by
    rw [harg, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_im]
    ring
  have hnorm : ‖Complex.exp (-(2 * Real.pi * Complex.I * X))‖ = Real.exp (2 * Real.pi * X.im) := by
    rw [Complex.norm_exp, hRe]
  have hReE : (Complex.exp (-(2 * Real.pi * Complex.I * X))).re
      = Real.exp (2 * Real.pi * X.im) * Real.cos (2 * Real.pi * X.re) := by
    rw [Complex.exp_re, hRe, hIm, Real.cos_neg]
  have hImE : (Complex.exp (-(2 * Real.pi * Complex.I * X))).im
      = -(Real.exp (2 * Real.pi * X.im) * Real.sin (2 * Real.pi * X.re)) := by
    rw [Complex.exp_im, hRe, hIm, Real.sin_neg]
    ring
  have hsq : ‖Complex.exp (-(2 * Real.pi * Complex.I * X)) - 1‖ ^ 2
      = (Real.exp (2 * Real.pi * X.im) - 1) ^ 2
        + 2 * Real.exp (2 * Real.pi * X.im) * (1 - Real.cos (2 * Real.pi * X.re)) := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, hReE, hImE,
      Complex.one_re, Complex.one_im]
    have htrig : Real.cos (Real.pi * X.re * 2) ^ 2 + Real.sin (Real.pi * X.re * 2) ^ 2 = 1 := by
      rw [show Real.pi * X.re * 2 = 2 * Real.pi * X.re by ring]
      exact Real.cos_sq_add_sin_sq _
    ring_nf
    nlinarith [htrig]
  have hcos : 1 - Real.cos (2 * Real.pi * X.re) ≥ 8 * X.re ^ 2 := by
    have h := Real.cos_le_one_sub_mul_cos_sq (x := 2 * Real.pi * X.re) (by
      rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
      nlinarith [Real.pi_pos, h1])
    have h' : (2 / Real.pi ^ 2) * (2 * Real.pi * X.re) ^ 2 = 8 * X.re ^ 2 := by
      have hπ : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
      field_simp
      ring
    linarith [h, h'.le, h'.ge]
  have hEim : (1 / 3 : ℝ) ≤ Real.exp (2 * Real.pi * X.im) := by
    have h3 : -(1 : ℝ) ≤ 2 * Real.pi * X.im := by
      have := neg_abs_le X.im
      nlinarith [Real.pi_pos, Real.pi_lt_four, h2, this]
    have h4 : Real.exp (-(1 : ℝ)) ≤ Real.exp (2 * Real.pi * X.im) := Real.exp_le_exp.mpr h3
    have h5 : (1 / 3 : ℝ) ≤ Real.exp (-(1 : ℝ)) := by
      rw [Real.exp_neg]
      have h6 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
      have h8 : (3 : ℝ)⁻¹ ≤ (Real.exp 1)⁻¹ :=
        (inv_le_inv₀ (by norm_num) (Real.exp_pos 1)).mpr h6
      simpa [one_div] using h8
    linarith
  have h6 : (Real.exp (2 * Real.pi * X.im) - 1) ^ 2 ≥ Real.pi ^ 2 * X.im ^ 2 := by
    have h7 : |2 * Real.pi * X.im| ≤ 1 := by
      calc |2 * Real.pi * X.im| = 2 * Real.pi * |X.im| := by
            rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
        _ ≤ 2 * Real.pi * (1 / 8) := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ ≤ 1 := by nlinarith [Real.pi_lt_four]
    have h8 := cfx_abs_exp_sub_one_ge_half (2 * Real.pi * X.im) h7
    have h9 : |2 * Real.pi * X.im| = 2 * Real.pi * |X.im| := by
      rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
    rw [h9] at h8
    have h10 : Real.pi * |X.im| ≤ |Real.exp (2 * Real.pi * X.im) - 1| := by linarith [h8]
    have h11 : (Real.pi * |X.im|) ^ 2 ≤ (Real.exp (2 * Real.pi * X.im) - 1) ^ 2 := by
      have h11a : (Real.pi * |X.im|) ^ 2 ≤ |Real.exp (2 * Real.pi * X.im) - 1| ^ 2 :=
        pow_le_pow_left₀ (by positivity) h10 2
      rwa [sq_abs (Real.exp (2 * Real.pi * X.im) - 1)] at h11a
    have h12b : |X.im| ^ 2 = X.im ^ 2 := sq_abs X.im
    rw [show (Real.pi * |X.im|) ^ 2 = Real.pi ^ 2 * |X.im| ^ 2 by ring, h12b] at h11
    exact h11
  have h10 : 2 * Real.exp (2 * Real.pi * X.im) * (1 - Real.cos (2 * Real.pi * X.re))
      ≥ 2 * (1 / 3) * (8 * X.re ^ 2) := by
    have h1 : (1 / 3 : ℝ) * (8 * X.re ^ 2)
        ≤ Real.exp (2 * Real.pi * X.im) * (1 - Real.cos (2 * Real.pi * X.re)) :=
      mul_le_mul hEim hcos (by positivity) (by positivity)
    linarith
  have h11 : Real.pi ^ 2 * X.im ^ 2 ≥ 4 * X.im ^ 2 := by
    have hπ : (4 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
    have h := mul_le_mul_of_nonneg_right hπ (sq_nonneg X.im)
    linarith [h]
  have h12 : 2 * (1 / 3 : ℝ) * (8 * X.re ^ 2) ≥ 4 * X.re ^ 2 := by nlinarith [sq_nonneg X.re]
  have h13 : (2 * ‖X‖) ^ 2 = 4 * (X.re ^ 2 + X.im ^ 2) := by
    rw [mul_pow, Complex.sq_norm, Complex.normSq_apply]; ring
  have h14 : ‖Complex.exp (-(2 * Real.pi * Complex.I * X)) - 1‖ ^ 2 ≥ (2 * ‖X‖) ^ 2 := by
    have h6' : Real.pi ^ 2 * X.im ^ 2 ≤ (Real.exp (2 * Real.pi * X.im) - 1) ^ 2 := h6
    have h10' : 2 * (1 / 3 : ℝ) * (8 * X.re ^ 2)
        ≤ 2 * Real.exp (2 * Real.pi * X.im) * (1 - Real.cos (2 * Real.pi * X.re)) := h10
    rw [hsq, h13]
    linarith [h6', h10', h11, h12]
  have h15 := Real.sqrt_le_sqrt h14
  rw [Real.sqrt_sq (by positivity), Real.sqrt_sq (norm_nonneg _)] at h15
  exact h15
/-! ## Numeric relations for the case analysis -/

lemma cfx_exp_mul_exp_neg (u : ℝ) : Real.exp u * Real.exp (-u) = 1 := by
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]

lemma cfx_exp_neg_mul_exp (u : ℝ) : Real.exp (-u) * Real.exp u = 1 := by
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

/-- `2 ≤ e^{3/4}`, used to detect that a large `‖Eun‖` forces `‖1 - Eun‖` to be large. -/
lemma cfx_exp_three_quarters_ge_two : (2 : ℝ) ≤ Real.exp (3 / 4) := by
  have h1 : Real.exp (3 / 4 : ℝ) = (Real.exp (1 / 8)) ^ 6 := by
    rw [show (3 / 4 : ℝ) = ((6 : ℕ) : ℝ) * (1 / 8) by norm_num, Real.exp_nat_mul]
  rw [h1]
  have h2 : (1.125 : ℝ) ≤ Real.exp (1 / 8) := by
    have h := Real.add_one_le_exp (1 / 8 : ℝ)
    linarith
  have h3 : (1.125 : ℝ) ^ 6 ≤ (Real.exp (1 / 8)) ^ 6 := pow_le_pow_left₀ (by norm_num) h2 6
  have h4 : (2 : ℝ) ≤ (1.125 : ℝ) ^ 6 := by norm_num
  linarith

lemma cfx_exp_four_le_sixty (v : ℝ) (h1 : v ≤ 1 / 10) : Real.exp (4 * Real.pi * v) ≤ 60 := by
  have h2 : 4 * Real.pi * v ≤ 2 := by nlinarith [Real.pi_lt_d20, Real.pi_pos]
  have h3 : Real.exp (4 * Real.pi * v) ≤ Real.exp 2 := Real.exp_le_exp.mpr h2
  have h4 : Real.exp 2 = (Real.exp 1) ^ 2 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
  have h5 : (Real.exp 1) ^ 2 ≤ 9 := by
    have h6 : Real.exp 1 ≤ 3 := le_of_lt Real.exp_one_lt_three
    nlinarith [h6, Real.exp_pos 1]
  rw [h4] at h3
  linarith

lemma cfx_exp_two_pi_le_598 : Real.exp (2 * Real.pi) ≤ 598 := by
  have h1 : 2 * Real.pi ≤ 6.3 := by nlinarith [Real.pi_lt_d20]
  refine le_trans (Real.exp_le_exp.mpr h1) ?_
  have h3 : (6.3 : ℝ) = 6 + 0.3 := by norm_num
  rw [h3, Real.exp_add]
  have h4 : Real.exp 6 ≤ 404 := by
    have h5 : Real.exp 6 = (Real.exp 1) ^ 6 := by
      rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
    rw [h5]
    have h6 : Real.exp 1 ≤ 2.7182818286 := le_of_lt Real.exp_one_lt_d9
    have h7 : (2.7182818286 : ℝ) ^ 6 ≤ 404 := by norm_num
    exact le_trans (pow_le_pow_left₀ (Real.exp_pos 1).le h6 6) h7
  have h8 : Real.exp 0.3 ≤ 1.43 := by
    have h9 := Real.exp_bound_div_one_sub_of_interval (x := 0.3) (by norm_num) (by norm_num)
    have h10 : (1 : ℝ) / (1 - 0.3) ≤ 1.43 := by norm_num
    linarith
  calc Real.exp 6 * Real.exp 0.3 ≤ 404 * 1.43 :=
        mul_le_mul h4 h8 (Real.exp_pos 0.3).le (by norm_num)
    _ ≤ 598 := by norm_num

lemma cfx_exp_four_mul_le (v : ℝ) (h1 : 1 / 10 ≤ v) (h2 : v ≤ 1) :
    Real.exp (4 * Real.pi * v) ≤ 601 * (Real.exp (2 * Real.pi * v) - 1) := by
  have hp : 0 < Real.pi := Real.pi_pos
  have hz : 0 < Real.exp (2 * Real.pi * v) := Real.exp_pos _
  have hlo : (1.5 : ℝ) ≤ Real.exp (2 * Real.pi * v) := by
    have h3 : (0.5 : ℝ) ≤ 2 * Real.pi * v := by nlinarith [Real.pi_gt_three]
    calc (1.5 : ℝ) = 0.5 + 1 := by norm_num
      _ ≤ Real.exp 0.5 := by linarith [Real.add_one_le_exp (0.5 : ℝ)]
      _ ≤ Real.exp (2 * Real.pi * v) := Real.exp_le_exp.mpr h3
  have hhi : Real.exp (2 * Real.pi * v) ≤ 598 := by
    have h3 : 2 * Real.pi * v ≤ 2 * Real.pi := by nlinarith [hp, h2]
    exact le_trans (Real.exp_le_exp.mpr h3) cfx_exp_two_pi_le_598
  have he : Real.exp (4 * Real.pi * v)
      = Real.exp (2 * Real.pi * v) * Real.exp (2 * Real.pi * v) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [he]
  have key : 1 ≤ (Real.exp (2 * Real.pi * v) - 1) * (600 - Real.exp (2 * Real.pi * v)) := by
    nlinarith [hlo, hhi]
  nlinarith [key, hz]

/-- For `0 ≤ v ≤ 1`: `e^{4πv} ≤ 601 · max (1/10) (e^{2πv} - 1)`. -/
lemma cfx_max_exp_relation (v : ℝ) (h0 : 0 ≤ v) (h1 : v ≤ 1) :
    Real.exp (4 * Real.pi * v) ≤ 601 * max (1 / 10) (Real.exp (2 * Real.pi * v) - 1) := by
  rcases lt_or_ge v (1 / 10) with hv | hv
  · have h2 : Real.exp (4 * Real.pi * v) ≤ 60 := cfx_exp_four_le_sixty v hv.le
    have h3 : (1 / 10 : ℝ) ≤ max (1 / 10) (Real.exp (2 * Real.pi * v) - 1) := le_max_left _ _
    nlinarith
  · have h2 : (1 / 10 : ℝ) ≤ Real.exp (2 * Real.pi * v) - 1 := by
      have h3 : (2 * Real.pi) * (1 / 10) ≤ 2 * Real.pi * v := by nlinarith [Real.pi_pos, hv]
      have h4 : Real.exp ((2 * Real.pi) * (1 / 10)) ≤ Real.exp (2 * Real.pi * v) :=
        Real.exp_le_exp.mpr h3
      have h5 : (1 / 10 : ℝ) ≤ Real.exp ((2 * Real.pi) * (1 / 10)) - 1 := by
        have h6 : (2 * Real.pi) * (1 / 10) + 1 ≤ Real.exp ((2 * Real.pi) * (1 / 10)) :=
          Real.add_one_le_exp _
        nlinarith [Real.pi_gt_three, h6]
      linarith
    rw [max_eq_right h2]
    exact cfx_exp_four_mul_le v hv h1

lemma cfx_exp_8pi_ge : (2.6 * 10 ^ 10 : ℝ) ≤ Real.exp (8 * Real.pi) := by
  have h2 : (24 : ℝ) ≤ 8 * Real.pi := by nlinarith [Real.pi_gt_three]
  have h3 : Real.exp 24 ≤ Real.exp (8 * Real.pi) := Real.exp_le_exp.mpr h2
  have h4 : Real.exp 24 = (Real.exp 1) ^ 24 := by
    rw [show (24 : ℝ) = ((24 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
  have h5 : (2.6 * 10 ^ 10 : ℝ) ≤ (Real.exp 1) ^ 24 := by
    have h6 : (2.7182818283 : ℝ) ^ 24 ≤ (Real.exp 1) ^ 24 :=
      pow_le_pow_left₀ (by norm_num) (le_of_lt Real.exp_one_gt_d9) 24
    have h7 : (2.6 * 10 ^ 10 : ℝ) ≤ (2.7182818283 : ℝ) ^ 24 := by norm_num
    linarith
  rw [h4] at h3
  linarith

lemma cfx_exp_23_ge : (8 * 10 ^ 9 : ℝ) ≤ Real.exp 23 := by
  have h4 : Real.exp 23 = (Real.exp 1) ^ 23 := by
    rw [show (23 : ℝ) = ((23 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
  rw [h4]
  have h6 : (2.7182818283 : ℝ) ^ 23 ≤ (Real.exp 1) ^ 23 :=
    pow_le_pow_left₀ (by norm_num) (le_of_lt Real.exp_one_gt_d9) 23
  have h7 : (8 * 10 ^ 9 : ℝ) ≤ (2.7182818283 : ℝ) ^ 23 := by norm_num
  linarith

lemma cfx_exp_two_pi_sub_one_ge_500 : (500 : ℝ) ≤ Real.exp (2 * Real.pi) - 1 := by
  have h1 : Real.exp 6 * Real.exp 0.28 ≤ Real.exp (2 * Real.pi) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith [Real.pi_gt_d20])
  have h2 : (1.28 : ℝ) ≤ Real.exp 0.28 := by
    have h := Real.add_one_le_exp (0.28 : ℝ)
    linarith
  have h3 : (403 : ℝ) ≤ Real.exp 6 := by
    have h4 : Real.exp 6 = (Real.exp 1) ^ 6 := by
      rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
    rw [h4]
    have h5 : (2.7182818283 : ℝ) ^ 6 ≤ (Real.exp 1) ^ 6 :=
      pow_le_pow_left₀ (by norm_num) (le_of_lt Real.exp_one_gt_d9) 6
    have h6 : (403 : ℝ) ≤ (2.7182818283 : ℝ) ^ 6 := by norm_num
    linarith
  nlinarith [h1, h2, h3]

lemma cfx_exp_neg_4pi_le : Real.exp (-(4 * Real.pi)) ≤ 1 / 100000 := by
  have h1 : Real.exp (-(4 * Real.pi)) ≤ Real.exp (-(12 : ℝ)) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three])
  refine le_trans h1 ?_
  rw [Real.exp_neg, inv_eq_one_div]
  refine one_div_le_one_div_of_le (by norm_num) ?_
  have h4 : Real.exp 12 = (Real.exp 1) ^ 12 := by
    rw [show (12 : ℝ) = ((12 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
  rw [h4]
  have h5 : (2.7182818283 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 :=
    pow_le_pow_left₀ (by norm_num) (le_of_lt Real.exp_one_gt_d9) 12
  have h6 : (100000 : ℝ) ≤ (2.7182818283 : ℝ) ^ 12 := by norm_num
  linarith

/-- **Non-thin case, real arithmetic.** -/
lemma cfx_nonthin_real {A B err D : ℝ} (hA : 2 ≤ A) (hB : 1 ≤ B)
    (hD1 : Real.exp (2 * Real.pi * A) * (1 / 10) ≤ D)
    (hD2 : |Real.exp (2 * Real.pi * A) - Real.exp (2 * Real.pi * B)| ≤ D)
    (herr : err ≤ 2 * 10 ^ 7 * Real.exp (-(2 * Real.pi * min A B))) : err ≤ D / 2 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hA8 : 8 * Real.pi ≤ 4 * Real.pi * A := by nlinarith [hpi, hA]
  have hbig : 4 * 10 ^ 7 * 601 ≤ Real.exp (4 * Real.pi * A) := by
    have h1 : Real.exp (8 * Real.pi) ≤ Real.exp (4 * Real.pi * A) := Real.exp_le_exp.mpr hA8
    have h2 : (4 * 10 ^ 7 * 601 : ℝ) ≤ 2.6 * 10 ^ 10 := by norm_num
    linarith [cfx_exp_8pi_ge, h1, h2]
  have hbig2 : (4 * 10 ^ 8 : ℝ) ≤ Real.exp (4 * Real.pi * A) := by
    have h1 : (4 * 10 ^ 8 : ℝ) ≤ 4 * 10 ^ 7 * 601 := by norm_num
    linarith [hbig, h1]
  rcases lt_or_ge B A with hBA | hBA
  · rw [min_eq_right hBA.le] at herr
    have hD2' : Real.exp (2 * Real.pi * B) * (Real.exp (2 * Real.pi * (A - B)) - 1) ≤ D := by
      have h3 : Real.exp (2 * Real.pi * A) - Real.exp (2 * Real.pi * B)
          = Real.exp (2 * Real.pi * B) * (Real.exp (2 * Real.pi * (A - B)) - 1) := by
        rw [mul_sub, mul_one, ← Real.exp_add]
        congr 1
        ring
      have h4 : 0 ≤ Real.exp (2 * Real.pi * A) - Real.exp (2 * Real.pi * B) := by
        have h5 : Real.exp (2 * Real.pi * B) ≤ Real.exp (2 * Real.pi * A) :=
          Real.exp_le_exp.mpr (by nlinarith [hpi, hBA.le])
        linarith
      rw [abs_of_nonneg h4, h3] at hD2
      exact hD2
    have hDm : Real.exp (2 * Real.pi * B) * max (1 / 10) (Real.exp (2 * Real.pi * (A - B)) - 1)
        ≤ D := by
      rw [mul_max_of_nonneg _ _ (Real.exp_pos _).le]
      refine max_le ?_ hD2'
      have h6 : Real.exp (2 * Real.pi * B) ≤ Real.exp (2 * Real.pi * A) :=
        Real.exp_le_exp.mpr (by nlinarith [hpi, hBA.le])
      linarith [hD1, h6]
    rcases lt_or_ge (A - B) 1 with hv1 | hv1
    · have hv0 : 0 ≤ A - B := by linarith [hBA.le]
      have hm := cfx_max_exp_relation (A - B) hv0 hv1.le
      have hdiv : Real.exp (4 * Real.pi * (A - B)) / 601
          ≤ max (1 / 10) (Real.exp (2 * Real.pi * (A - B)) - 1) := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 601)]
        linarith [hm]
      have hm2 : Real.exp (2 * Real.pi * B) * (Real.exp (4 * Real.pi * (A - B)) / 601)
          ≤ Real.exp (2 * Real.pi * B)
            * max (1 / 10) (Real.exp (2 * Real.pi * (A - B)) - 1) :=
        mul_le_mul_of_nonneg_left hdiv (Real.exp_pos _).le
      have key : 4 * 10 ^ 7 * Real.exp (-(2 * Real.pi * B))
          ≤ Real.exp (2 * Real.pi * B) * (Real.exp (4 * Real.pi * (A - B)) / 601) := by
        have h601 : (0 : ℝ) < 601 := by norm_num
        rw [show Real.exp (2 * Real.pi * B) * (Real.exp (4 * Real.pi * (A - B)) / 601)
              = Real.exp (2 * Real.pi * B) * Real.exp (4 * Real.pi * (A - B)) / 601 by ring]
        rw [le_div_iff₀ h601]
        have hC : (4 * 10 ^ 7 * 601 : ℝ) * Real.exp (-(2 * Real.pi * B))
            ≤ Real.exp (4 * Real.pi * A) * Real.exp (-(2 * Real.pi * B)) :=
          mul_le_mul_of_nonneg_right hbig (Real.exp_pos _).le
        have h1 : Real.exp (4 * Real.pi * A) * Real.exp (-(2 * Real.pi * B))
            = Real.exp (2 * Real.pi * B) * Real.exp (4 * Real.pi * (A - B)) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
        rw [h1] at hC
        have he : (4 * 10 ^ 7 * 601 : ℝ) * Real.exp (-(2 * Real.pi * B))
            = 4 * 10 ^ 7 * Real.exp (-(2 * Real.pi * B)) * 601 := by ring
        rw [he] at hC
        exact hC
      have h2err : 2 * err ≤ D := by
        have e1 : 2 * err ≤ 4 * 10 ^ 7 * Real.exp (-(2 * Real.pi * B)) := by linarith [herr]
        exact le_trans e1 (le_trans key (le_trans hm2 hDm))
      linarith
    · have hD2'' : Real.exp (2 * Real.pi * B) * (Real.exp (2 * Real.pi) - 1) ≤ D := by
        have h4 : Real.exp (2 * Real.pi) - 1 ≤ Real.exp (2 * Real.pi * (A - B)) - 1 := by
          have h5 : Real.exp (2 * Real.pi) ≤ Real.exp (2 * Real.pi * (A - B)) :=
            Real.exp_le_exp.mpr (by nlinarith [hpi, hv1])
          linarith
        have h6 := mul_le_mul_of_nonneg_left h4 (Real.exp_pos (2 * Real.pi * B)).le
        linarith [hD2', h6]
      have key2 : 4 * 10 ^ 7 * Real.exp (-(2 * Real.pi * B))
          ≤ Real.exp (2 * Real.pi * B) * (Real.exp (2 * Real.pi) - 1) := by
        have h4 : 4 * 10 ^ 7 * Real.exp (-(4 * Real.pi * B)) ≤ Real.exp (2 * Real.pi) - 1 := by
          have h5 : Real.exp (-(4 * Real.pi * B)) ≤ Real.exp (-(4 * Real.pi)) :=
            Real.exp_le_exp.mpr (by nlinarith [hpi, hB])
          have h6 : 4 * 10 ^ 7 * Real.exp (-(4 * Real.pi)) ≤ Real.exp (2 * Real.pi) - 1 := by
            have h7 : 4 * 10 ^ 7 * Real.exp (-(4 * Real.pi)) ≤ 4 * 10 ^ 7 * (1 / 100000) :=
              mul_le_mul_of_nonneg_left cfx_exp_neg_4pi_le (by norm_num)
            linarith [h7, cfx_exp_two_pi_sub_one_ge_500]
          calc 4 * 10 ^ 7 * Real.exp (-(4 * Real.pi * B))
                ≤ 4 * 10 ^ 7 * Real.exp (-(4 * Real.pi)) :=
                mul_le_mul_of_nonneg_left h5 (by norm_num)
            _ ≤ Real.exp (2 * Real.pi) - 1 := h6
        have h8 := mul_le_mul_of_nonneg_right h4 (Real.exp_pos (2 * Real.pi * B)).le
        have h9 : (4 * 10 ^ 7 * Real.exp (-(4 * Real.pi * B))) * Real.exp (2 * Real.pi * B)
            = 4 * 10 ^ 7 * Real.exp (-(2 * Real.pi * B)) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 1
          ring
        rw [h9] at h8
        linarith [h8]
      have h2err : 2 * err ≤ D := by
        have e1 : 2 * err ≤ 4 * 10 ^ 7 * Real.exp (-(2 * Real.pi * B)) := by linarith [herr]
        exact le_trans e1 (le_trans key2 hD2'')
      linarith
  · rw [min_eq_left hBA] at herr
    have key3 : 4 * 10 ^ 7 * Real.exp (-(2 * Real.pi * A))
        ≤ Real.exp (2 * Real.pi * A) * (1 / 10) := by
      rw [show Real.exp (2 * Real.pi * A) * (1 / 10) = Real.exp (2 * Real.pi * A) / 10 by ring]
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 10)]
      have h10 : Real.exp (-(2 * Real.pi * A)) * Real.exp (2 * Real.pi * A) = 1 :=
        cfx_exp_neg_mul_exp _
      have h11 : Real.exp (2 * Real.pi * A) * Real.exp (2 * Real.pi * A)
          = Real.exp (4 * Real.pi * A) := by
        rw [← Real.exp_add]; congr 1; ring
      have s1 : (4 * 10 ^ 8 : ℝ)
          ≤ Real.exp (2 * Real.pi * A) * Real.exp (2 * Real.pi * A) := by
        rw [h11]; exact hbig2
      have s2 : (4 * 10 ^ 8) * Real.exp (-(2 * Real.pi * A))
          ≤ (Real.exp (2 * Real.pi * A) * Real.exp (2 * Real.pi * A))
            * Real.exp (-(2 * Real.pi * A)) :=
        mul_le_mul_of_nonneg_right s1 (Real.exp_pos _).le
      have s3 : (Real.exp (2 * Real.pi * A) * Real.exp (2 * Real.pi * A))
            * Real.exp (-(2 * Real.pi * A)) = Real.exp (2 * Real.pi * A) := by
        calc (Real.exp (2 * Real.pi * A) * Real.exp (2 * Real.pi * A))
              * Real.exp (-(2 * Real.pi * A))
            = Real.exp (2 * Real.pi * A)
              * (Real.exp (2 * Real.pi * A) * Real.exp (-(2 * Real.pi * A))) := by ring
          _ = Real.exp (2 * Real.pi * A) * 1 := by rw [cfx_exp_mul_exp_neg]
          _ = Real.exp (2 * Real.pi * A) := by ring
      rw [s3] at s2
      have s4 : (4 * 10 ^ 8) * Real.exp (-(2 * Real.pi * A))
          = 4 * 10 ^ 7 * Real.exp (-(2 * Real.pi * A)) * 10 := by ring
      rw [s4] at s2
      exact s2
    have h2err : 2 * err ≤ D := by
      have e1 : 2 * err ≤ 4 * 10 ^ 7 * Real.exp (-(2 * Real.pi * A)) := by linarith [herr]
      exact le_trans e1 (le_trans key3 hD1)
    linarith

/-- **Thin case, real arithmetic.** -/
lemma cfx_thin_real {A B err D X : ℝ} (hA : 2 ≤ A) (hB : 15 / 8 ≤ B) (hX : 0 ≤ X)
    (hD : 2 * Real.exp (2 * Real.pi * B) * X ≤ D)
    (herr : err ≤ 2 * 10 ^ 9 * Real.exp (-(2 * Real.pi * (15 / 8))) * X) : err ≤ D / 2 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hKey : 4 * 10 ^ 9 ≤ Real.exp (15 * Real.pi / 2) := by
    have h1 : (23 : ℝ) ≤ 15 * Real.pi / 2 := by nlinarith [Real.pi_gt_d20]
    have h2 : Real.exp 23 ≤ Real.exp (15 * Real.pi / 2) := Real.exp_le_exp.mpr h1
    linarith [cfx_exp_23_ge, h2]
  have hE : Real.exp (2 * Real.pi * (15 / 8)) = Real.exp (15 * Real.pi / 4) := by
    congr 1; ring
  have hD2 : Real.exp (15 * Real.pi / 4) * X ≤ D / 2 := by
    have h1 : Real.exp (2 * Real.pi * (15 / 8)) ≤ Real.exp (2 * Real.pi * B) :=
      Real.exp_le_exp.mpr (by nlinarith [hpi, hB])
    have h2 : Real.exp (2 * Real.pi * (15 / 8)) * X ≤ Real.exp (2 * Real.pi * B) * X :=
      mul_le_mul_of_nonneg_right h1 hX
    rw [hE] at h2
    linarith [h2, hD]
  have hstep : 2 * 10 ^ 9 * Real.exp (-(2 * Real.pi * (15 / 8))) * X
      ≤ Real.exp (15 * Real.pi / 4) * X := by
    have h1 : 2 * 10 ^ 9 * Real.exp (-(15 * Real.pi / 4)) ≤ Real.exp (15 * Real.pi / 4) := by
      have h2 : (4 * 10 ^ 9) * Real.exp (-(15 * Real.pi / 4))
          ≤ Real.exp (15 * Real.pi / 2) * Real.exp (-(15 * Real.pi / 4)) :=
        mul_le_mul_of_nonneg_right hKey (Real.exp_pos _).le
      have h3 : Real.exp (15 * Real.pi / 2) * Real.exp (-(15 * Real.pi / 4))
          = Real.exp (15 * Real.pi / 4) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [h3] at h2
      have h4 : (2 * 10 ^ 9 : ℝ) * Real.exp (-(15 * Real.pi / 4))
          ≤ (4 * 10 ^ 9) * Real.exp (-(15 * Real.pi / 4)) :=
        mul_le_mul_of_nonneg_right (by norm_num) (Real.exp_pos _).le
      linarith [h2, h4]
    have h5 : Real.exp (-(2 * Real.pi * (15 / 8))) = Real.exp (-(15 * Real.pi / 4)) := by
      congr 1; ring
    rw [h5]
    exact mul_le_mul_of_nonneg_right h1 hX
  linarith [herr, hstep, hD2]

/-! ## Auxiliary computations -/

/-- The point `i s` of the upper half plane, as a complex number. -/
lemma cfx_imagAxis_coe (s : ℝ) (hs : 0 < s) :
    ((Work.Kernels.imagAxis s hs : ℍ) : ℂ) = (s : ℂ) * Complex.I :=
  UpperHalfPlane.coe_mk _ _

/-- `j(i t) = j(i / t)`: `S` exchanges the two points. -/
lemma cfx_jInvariantFun_imagAxis_inv (t : ℝ) (ht : 0 < t) :
    Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)
      = Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht)) := by
  rw [← Work.Kernels.KernelFacts.jInvariantFun_S_smul (Work.Kernels.imagAxis t ht),
    Work.Asymptotics.imagAxis_smul_S t ht]

/-- `-((t i)⁻¹) = i/t` (as complex numbers). -/
lemma cfx_neg_inv_mul_I (t : ℝ) (ht : 0 < t) :
    -(((t : ℂ) * Complex.I)⁻¹) = ((Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht) : ℍ) : ℂ) := by
  rw [cfx_imagAxis_coe t⁻¹ (inv_pos.mpr ht), mul_inv, Complex.inv_I, ← Complex.ofReal_inv]
  ring

/-- Every real number is within `1/2` of an integer. -/
lemma cfx_exists_int_abs_sub_le_half (x : ℝ) : ∃ n : ℤ, |x - (n : ℝ)| ≤ 1 / 2 := by
  rcases lt_or_ge (x - (⌊x⌋ : ℝ)) (1 / 2) with h | h
  · refine ⟨⌊x⌋, ?_⟩
    rw [abs_of_nonneg (by linarith [Int.floor_le x])]
    linarith
  · refine ⟨⌊x⌋ + 1, ?_⟩
    rw [abs_of_nonpos (by push_cast; linarith [Int.lt_floor_add_one x])]
    push_cast
    linarith [Int.lt_floor_add_one x]

/-! ## The main theorem -/

set_option maxHeartbeats 2000000 in
theorem cfx_E_jdiff_small :
    ∃ c : ℝ, 0 < c ∧ ∀ (w : UpperHalfPlane) (t : ℝ) (ht : 0 < t),
      w ∈ Work.Asymptotics.KEpsilon → t ≤ 1 →
        c * Real.exp (2 * Real.pi * (ModularGroup.S • w).im)
            * ‖1 - Complex.exp (2 * Real.pi * Complex.I
                * ((((ModularGroup.S • w : UpperHalfPlane)) : ℂ) - (-(((t : ℂ) * Complex.I)⁻¹))))‖
          ≤ ‖Work.Kernels.jInvariantFun w
              - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖ := by
  refine ⟨1 / 10, by norm_num, ?_⟩
  intro w t ht hw htle
  rw [cfx_neg_inv_mul_I t ht]
  set w' : ℍ := ModularGroup.S • w with hw'def
  set τ₀ : ℍ := Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht) with hτ₀def
  set Eun : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((w' : ℂ) - (τ₀ : ℂ))) with hEun_def
  have hA2 : 2 ≤ w'.im := hw.2
  have hBge : 1 ≤ t⁻¹ := (one_le_inv₀ ht).mpr htle
  have hτ₀im : τ₀.im = t⁻¹ := by
    rw [hτ₀def]
    simp [Work.Kernels.imagAxis]
  have hτ₀coe : ((τ₀ : ℍ) : ℂ) = ((t⁻¹ : ℝ) : ℂ) * Complex.I := by
    rw [hτ₀def]
    exact cfx_imagAxis_coe t⁻¹ (inv_pos.mpr ht)
  have hjw : Work.Kernels.jInvariantFun w = Work.Kernels.jInvariantFun w' := by
    rw [hw'def]
    exact (Work.Kernels.KernelFacts.jInvariantFun_S_smul w).symm
  have hjt : Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)
      = Work.Kernels.jInvariantFun τ₀ := by
    rw [hτ₀def]
    exact cfx_jInvariantFun_imagAxis_inv t ht
  have hqwn : ‖Work.Kernels.qParamFun w'‖ = Real.exp (-(2 * Real.pi * w'.im)) :=
    cfx_norm_qParamFun_eq w'
  have hqtn : ‖Work.Kernels.qParamFun τ₀‖ = Real.exp (-(2 * Real.pi * t⁻¹)) := by
    rw [cfx_norm_qParamFun_eq, hτ₀im]
  have hqw0 : Work.Kernels.qParamFun w' ≠ 0 := cfx_qParamFun_ne_zero w'
  have hEun0 : Eun ≠ 0 := by
    rw [hEun_def]
    exact Complex.exp_ne_zero _
  have hqrel : Work.Kernels.qParamFun w' * (Work.Kernels.qParamFun τ₀)⁻¹ = Eun := by
    rw [hEun_def]
    simp only [Work.Kernels.qParamFun]
    rw [← Complex.exp_neg, ← Complex.exp_add]
    congr 1
    ring
  have hDnorm1 : ‖(Work.Kernels.qParamFun w')⁻¹‖ = Real.exp (2 * Real.pi * w'.im) := by
    rw [norm_inv, hqwn, ← Real.exp_neg]
    congr 1
    ring
  have hDnorm2 : ‖(Work.Kernels.qParamFun τ₀)⁻¹‖ = Real.exp (2 * Real.pi * t⁻¹) := by
    rw [norm_inv, hqtn, ← Real.exp_neg]
    congr 1
    ring
  have hDnorm : ‖(Work.Kernels.qParamFun w')⁻¹ - (Work.Kernels.qParamFun τ₀)⁻¹‖
      = Real.exp (2 * Real.pi * w'.im) * ‖1 - Eun‖ := by
    have h1 : (Work.Kernels.qParamFun w')⁻¹ - (Work.Kernels.qParamFun τ₀)⁻¹
        = (Work.Kernels.qParamFun w')⁻¹ * (1 - Eun) := by
      rw [← hqrel, mul_sub, mul_one, ← mul_assoc, inv_mul_cancel₀ hqw0, one_mul]
    rw [h1, norm_mul, hDnorm1]
  have hsplit : ‖Work.Kernels.jInvariantFun w
        - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖
      ≥ ‖(Work.Kernels.qParamFun w')⁻¹ - (Work.Kernels.qParamFun τ₀)⁻¹‖
        - ‖cfx_Ffun w' - cfx_Ffun τ₀‖ := by
    have h1 : Work.Kernels.jInvariantFun w
          - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)
        = (cfx_Ffun w' - cfx_Ffun τ₀)
          + ((Work.Kernels.qParamFun w')⁻¹ - (Work.Kernels.qParamFun τ₀)⁻¹) := by
      rw [hjw, hjt]
      simp only [cfx_Ffun]
      ring
    rw [h1]
    have h2 := abs_norm_sub_norm_le
      ((Work.Kernels.qParamFun w')⁻¹ - (Work.Kernels.qParamFun τ₀)⁻¹)
      (-(cfx_Ffun w' - cfx_Ffun τ₀))
    have h3 : ‖(Work.Kernels.qParamFun w')⁻¹ - (Work.Kernels.qParamFun τ₀)⁻¹‖
          - ‖cfx_Ffun w' - cfx_Ffun τ₀‖
        ≤ ‖((Work.Kernels.qParamFun w')⁻¹ - (Work.Kernels.qParamFun τ₀)⁻¹)
            - (-(cfx_Ffun w' - cfx_Ffun τ₀))‖ := by
      have h := (abs_le.mp h2).2
      rwa [norm_neg] at h
    have h4 : ((Work.Kernels.qParamFun w')⁻¹ - (Work.Kernels.qParamFun τ₀)⁻¹)
          - (-(cfx_Ffun w' - cfx_Ffun τ₀))
        = (cfx_Ffun w' - cfx_Ffun τ₀)
          + ((Work.Kernels.qParamFun w')⁻¹ - (Work.Kernels.qParamFun τ₀)⁻¹) := by ring
    rw [h4] at h3
    exact h3
  obtain ⟨n, hn⟩ := cfx_exists_int_abs_sub_le_half w'.re
  set ζ : ℍ := (n : ℝ) +ᵥ τ₀ with hζdef
  set X : ℂ := (w' : ℂ) - (ζ : ℂ) with hXdef
  have hζcoe : ((ζ : ℍ) : ℂ) = ((n : ℤ) : ℂ) + (τ₀ : ℂ) := by
    rw [hζdef, UpperHalfPlane.coe_vadd]
    push_cast
    ring
  have hζim : ζ.im = t⁻¹ := by
    rw [← UpperHalfPlane.coe_im, hζcoe, hτ₀coe]
    simp only [Complex.add_im, Complex.intCast_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hFζ : cfx_Ffun ζ = cfx_Ffun τ₀ := by
    rw [hζdef]
    exact cfx_Ffun_int_vadd n τ₀
  have hXre : |X.re| ≤ 1 / 2 := by
    have h1 : X.re = w'.re - (n : ℝ) := by
      rw [hXdef, hζcoe, hτ₀coe]
      simp only [Complex.sub_re, Complex.add_re, Complex.intCast_re, UpperHalfPlane.coe_re,
        Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im]
      ring
    rw [h1]
    exact hn
  have hXim : X.im = w'.im - t⁻¹ := by
    rw [hXdef, hζcoe, hτ₀coe]
    simp only [Complex.sub_im, Complex.add_im, Complex.intCast_im, UpperHalfPlane.coe_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
    ring
  -- the error bound in the non-thin case
  have herr_nonthin : ‖cfx_Ffun w' - cfx_Ffun τ₀‖
      ≤ 2 * 10 ^ 7 * Real.exp (-(2 * Real.pi * min w'.im t⁻¹)) := by
    have h3 : ‖cfx_F_lift (w' : ℂ)‖ ≤ 10 ^ 7 * Real.exp (-(2 * Real.pi * w'.im)) := by
      have h := cfx_F_lift_bound (w' : ℂ) (by rw [UpperHalfPlane.coe_im]; linarith)
      rwa [UpperHalfPlane.coe_im] at h
    have h4 : ‖cfx_F_lift (τ₀ : ℂ)‖ ≤ 10 ^ 7 * Real.exp (-(2 * Real.pi * t⁻¹)) := by
      have h := cfx_F_lift_bound (τ₀ : ℂ) (by rw [UpperHalfPlane.coe_im, hτ₀im]; linarith)
      rwa [UpperHalfPlane.coe_im, hτ₀im] at h
    have h9 : 10 ^ 7 * Real.exp (-(2 * Real.pi * w'.im))
          + 10 ^ 7 * Real.exp (-(2 * Real.pi * t⁻¹))
        ≤ 2 * 10 ^ 7 * Real.exp (-(2 * Real.pi * min w'.im t⁻¹)) := by
      have h6 : Real.exp (-(2 * Real.pi * w'.im))
          ≤ Real.exp (-(2 * Real.pi * min w'.im t⁻¹)) :=
        Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, min_le_left w'.im t⁻¹])
      have h7 : Real.exp (-(2 * Real.pi * t⁻¹))
          ≤ Real.exp (-(2 * Real.pi * min w'.im t⁻¹)) :=
        Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, min_le_right w'.im t⁻¹])
      have ha : (10 : ℝ) ^ 7 = 10000000 := by norm_num
      rw [ha]
      linarith
    calc ‖cfx_Ffun w' - cfx_Ffun τ₀‖
        = ‖cfx_F_lift (w' : ℂ) - cfx_F_lift (τ₀ : ℂ)‖ := by
          rw [cfx_Ffun_eq_F_lift w', cfx_Ffun_eq_F_lift τ₀]
      _ ≤ ‖cfx_F_lift (w' : ℂ)‖ + ‖cfx_F_lift (τ₀ : ℂ)‖ := norm_sub_le _ _
      _ ≤ 10 ^ 7 * Real.exp (-(2 * Real.pi * w'.im))
            + 10 ^ 7 * Real.exp (-(2 * Real.pi * t⁻¹)) := add_le_add h3 h4
      _ ≤ 2 * 10 ^ 7 * Real.exp (-(2 * Real.pi * min w'.im t⁻¹)) := h9
  by_cases hthin : ‖1 - Eun‖ < 1 / 10
  · -- ### the thin case
    have hEunnorm : ‖Eun‖ = Real.exp (-(2 * Real.pi * (w'.im - t⁻¹))) := by
      have hre : (2 * Real.pi * Complex.I * ((w' : ℂ) - (τ₀ : ℂ))).re
          = -(2 * Real.pi * (w'.im - t⁻¹)) := by
        have h2pi : (2 * Real.pi * Complex.I : ℂ) = ((2 * Real.pi : ℝ) : ℂ) * Complex.I := by
          push_cast; ring
        rw [hτ₀coe, h2pi]
        simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
          UpperHalfPlane.coe_im]
        ring
      rw [hEun_def, Complex.norm_exp, hre]
    have hXim_le : X.im ≤ 1 / 8 := by
      by_contra h
      push_neg at h
      have h1 : Real.exp (-(2 * Real.pi * X.im)) ≤ 1 / 2 := by
        have h6 : Real.exp (-(2 * Real.pi * X.im)) ≤ Real.exp (-(3 / 4 : ℝ)) := by
          rw [Real.exp_le_exp]
          nlinarith [Real.pi_gt_three, h]
        have h7 : Real.exp (-(3 / 4 : ℝ)) ≤ 1 / 2 := by
          have h8 : (2 : ℝ) ≤ Real.exp (3 / 4) := cfx_exp_three_quarters_ge_two
          have h9 : (Real.exp (3 / 4))⁻¹ ≤ (2 : ℝ)⁻¹ :=
            (inv_le_inv₀ (Real.exp_pos _) (by norm_num)).mpr h8
          rw [Real.exp_neg]
          simpa using h9
        linarith
      have h2 : ‖Eun‖ ≤ 1 / 2 := by
        rw [hEunnorm, ← hXim]
        exact h1
      have h3 := abs_norm_sub_norm_le Eun 1
      rw [norm_one, norm_sub_rev] at h3
      have h4 : (1 / 2 : ℝ) ≤ ‖1 - Eun‖ := by
        have h5 : |‖Eun‖ - 1| = 1 - ‖Eun‖ := by
          rw [abs_of_nonpos (by linarith)]
          ring
        linarith [h3, h2, h5]
      linarith [hthin, h4]
    have hXim_ge : -(1 / 8) ≤ X.im := by
      by_contra h
      push_neg at h
      have h1 : (2 : ℝ) ≤ Real.exp (-(2 * Real.pi * X.im)) := by
        have h6 : Real.exp (3 / 4) ≤ Real.exp (-(2 * Real.pi * X.im)) := by
          rw [Real.exp_le_exp]
          nlinarith [Real.pi_gt_three, h]
        linarith [cfx_exp_three_quarters_ge_two, h6]
      have h2 : 2 ≤ ‖Eun‖ := by
        rw [hEunnorm, ← hXim]
        exact h1
      have h3 := abs_norm_sub_norm_le Eun 1
      rw [norm_one, norm_sub_rev] at h3
      have h4 : (1 : ℝ) ≤ ‖1 - Eun‖ := by
        have h5 : |‖Eun‖ - 1| = ‖Eun‖ - 1 := by
          rw [abs_of_nonneg (by linarith)]
        linarith [h3, h2, h5]
      linarith [hthin, h4]
    have hXimabs : |X.im| ≤ 1 / 8 := abs_le.mpr ⟨hXim_ge, hXim_le⟩
    have hB15 : 15 / 8 ≤ t⁻¹ := by
      have h7 : t⁻¹ = w'.im - X.im := by rw [hXim]; ring
      rw [h7]
      linarith [hA2, hXim_le]
    have hEuninv : Complex.exp (-(2 * Real.pi * Complex.I * X)) = Eun⁻¹ := by
      have h1 : -(2 * Real.pi * Complex.I * X)
          = -(2 * Real.pi * Complex.I * ((w' : ℂ) - (τ₀ : ℂ)))
            + ((n : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
        rw [hXdef, hζcoe]
        ring
      rw [h1, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, hEun_def,
        ← Complex.exp_neg]
    have h2 : ‖Eun⁻¹ - 1‖ ≥ 2 * ‖X‖ := by
      have h3 := cfx_norm_exp_neg_two_pi_I_sub_one_ge X hXre hXimabs
      rwa [hEuninv] at h3
    have h4 : ‖1 - Eun‖ = ‖Eun‖ * ‖Eun⁻¹ - 1‖ := by
      have h5 : 1 - Eun = Eun * (Eun⁻¹ - 1) := by
        rw [mul_sub, mul_one, mul_inv_cancel₀ hEun0]
      rw [h5, norm_mul]
    have h6 : ‖Eun‖ * (2 * ‖X‖) ≤ ‖1 - Eun‖ := by
      rw [h4]
      exact mul_le_mul_of_nonneg_left h2 (norm_nonneg Eun)
    have hDthin : 2 * Real.exp (2 * Real.pi * t⁻¹) * ‖X‖
        ≤ ‖(Work.Kernels.qParamFun w')⁻¹ - (Work.Kernels.qParamFun τ₀)⁻¹‖ := by
      rw [hDnorm]
      have h7 : Real.exp (2 * Real.pi * w'.im) * (‖Eun‖ * (2 * ‖X‖))
          ≤ Real.exp (2 * Real.pi * w'.im) * ‖1 - Eun‖ :=
        mul_le_mul_of_nonneg_left h6 (Real.exp_pos _).le
      have h8 : Real.exp (2 * Real.pi * w'.im) * (‖Eun‖ * (2 * ‖X‖))
          = 2 * Real.exp (2 * Real.pi * t⁻¹) * ‖X‖ := by
        have h9 : Real.exp (2 * Real.pi * w'.im) * Real.exp (-(2 * Real.pi * X.im))
            = Real.exp (2 * Real.pi * t⁻¹) := by
          rw [← Real.exp_add]
          congr 1
          rw [hXim]
          ring
        rw [hEunnorm, ← hXim, ← h9]
        ring
      linarith [h7, h8]
    have herr_thin : ‖cfx_Ffun w' - cfx_Ffun τ₀‖
        ≤ 2 * 10 ^ 9 * Real.exp (-(2 * Real.pi * (15 / 8))) * ‖X‖ := by
      have hseg : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
          3 / 2 ≤ ((ζ : ℂ) + s • ((w' : ℂ) - (ζ : ℂ))).im := by
        intro s hs
        have h1 : ((ζ : ℂ) + s • ((w' : ℂ) - (ζ : ℂ))).im = (1 - s) * ζ.im + s * w'.im := by
          simp only [Complex.add_im, Complex.smul_im, Complex.sub_im, UpperHalfPlane.coe_im]
          ring
        rw [h1]
        have h2 : 15 / 8 ≤ ζ.im := by
          rw [hζim]
          exact hB15
        nlinarith [hs.1, hs.2, h2, hA2]
      have hdiff := cfx_F_lift_diff_bound (w' : ℂ) (ζ : ℂ) hseg
      simp only [UpperHalfPlane.coe_im, hζim] at hdiff
      have h2 : 15 / 8 ≤ min w'.im t⁻¹ := le_min (by linarith) hB15
      have h3 : Real.exp (-(2 * Real.pi * min w'.im t⁻¹))
          ≤ Real.exp (-(2 * Real.pi * (15 / 8))) :=
        Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, h2])
      have h4 : cfx_Ffun w' - cfx_Ffun τ₀ = cfx_F_lift (w' : ℂ) - cfx_F_lift (ζ : ℂ) := by
        rw [cfx_Ffun_eq_F_lift w', ← hFζ, cfx_Ffun_eq_F_lift ζ]
      have h5 : ‖(w' : ℂ) - (ζ : ℂ)‖ = ‖X‖ := by rw [← hXdef]
      rw [h4]
      calc ‖cfx_F_lift (w' : ℂ) - cfx_F_lift (ζ : ℂ)‖
          ≤ 2 * 10 ^ 9 * Real.exp (-(2 * Real.pi * min w'.im t⁻¹))
              * ‖(w' : ℂ) - (ζ : ℂ)‖ := hdiff
        _ ≤ 2 * 10 ^ 9 * Real.exp (-(2 * Real.pi * (15 / 8))) * ‖X‖ := by
            have hz : (0 : ℝ) ≤ 2 * 10 ^ 9 := by norm_num
            have hN : 0 ≤ ‖X‖ := norm_nonneg _
            have h6 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hz) hN
            rw [h5] at h6
            exact h6
    have hmain := cfx_thin_real (A := w'.im) (B := t⁻¹) (err := ‖cfx_Ffun w' - cfx_Ffun τ₀‖)
      (D := ‖(Work.Kernels.qParamFun w')⁻¹ - (Work.Kernels.qParamFun τ₀)⁻¹‖) (X := ‖X‖)
      hA2 hB15 (norm_nonneg X) hDthin herr_thin
    have hfin : (1 / 10) * ‖(Work.Kernels.qParamFun w')⁻¹ - (Work.Kernels.qParamFun τ₀)⁻¹‖
        ≤ ‖Work.Kernels.jInvariantFun w
            - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖ := by
      have h2 : ‖(Work.Kernels.qParamFun w')⁻¹ - (Work.Kernels.qParamFun τ₀)⁻¹‖ / 2
          ≤ ‖(Work.Kernels.qParamFun w')⁻¹ - (Work.Kernels.qParamFun τ₀)⁻¹‖
            - ‖cfx_Ffun w' - cfx_Ffun τ₀‖ := by
        linarith [hmain]
      linarith [hsplit, h2,
        norm_nonneg ((Work.Kernels.qParamFun w')⁻¹ - (Work.Kernels.qParamFun τ₀)⁻¹)]
    calc 1 / 10 * Real.exp (2 * Real.pi * w'.im) * ‖1 - Eun‖
        = 1 / 10 * ‖(Work.Kernels.qParamFun w')⁻¹ - (Work.Kernels.qParamFun τ₀)⁻¹‖ := by
          rw [hDnorm]; ring
      _ ≤ ‖Work.Kernels.jInvariantFun w
            - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖ := hfin
  · -- ### the non-thin case
    push_neg at hthin
    have hD1 : Real.exp (2 * Real.pi * w'.im) * (1 / 10)
        ≤ ‖(Work.Kernels.qParamFun w')⁻¹ - (Work.Kernels.qParamFun τ₀)⁻¹‖ := by
      rw [hDnorm]
      exact mul_le_mul_of_nonneg_left hthin (Real.exp_pos _).le
    have hD2 : |Real.exp (2 * Real.pi * w'.im) - Real.exp (2 * Real.pi * t⁻¹)|
        ≤ ‖(Work.Kernels.qParamFun w')⁻¹ - (Work.Kernels.qParamFun τ₀)⁻¹‖ := by
      refine abs_le.mpr ⟨?_, ?_⟩
      · have h := abs_norm_sub_norm_le (Work.Kernels.qParamFun τ₀)⁻¹
          (Work.Kernels.qParamFun w')⁻¹
        rw [hDnorm2, hDnorm1, norm_sub_rev, abs_sub_comm] at h
        exact (abs_le.mp h).1
      · have h := abs_norm_sub_norm_le (Work.Kernels.qParamFun w')⁻¹
          (Work.Kernels.qParamFun τ₀)⁻¹
        rw [hDnorm1, hDnorm2] at h
        exact (abs_le.mp h).2
    have hmain := cfx_nonthin_real (A := w'.im) (B := t⁻¹) (err := ‖cfx_Ffun w' - cfx_Ffun τ₀‖)
      (D := ‖(Work.Kernels.qParamFun w')⁻¹ - (Work.Kernels.qParamFun τ₀)⁻¹‖)
      hA2 hBge hD1 hD2 herr_nonthin
    have hfin : (1 / 10) * ‖(Work.Kernels.qParamFun w')⁻¹ - (Work.Kernels.qParamFun τ₀)⁻¹‖
        ≤ ‖Work.Kernels.jInvariantFun w
            - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖ := by
      have h2 : ‖(Work.Kernels.qParamFun w')⁻¹ - (Work.Kernels.qParamFun τ₀)⁻¹‖ / 2
          ≤ ‖(Work.Kernels.qParamFun w')⁻¹ - (Work.Kernels.qParamFun τ₀)⁻¹‖
            - ‖cfx_Ffun w' - cfx_Ffun τ₀‖ := by
        linarith [hmain]
      linarith [hsplit, h2,
        norm_nonneg ((Work.Kernels.qParamFun w')⁻¹ - (Work.Kernels.qParamFun τ₀)⁻¹)]
    calc 1 / 10 * Real.exp (2 * Real.pi * w'.im) * ‖1 - Eun‖
        = 1 / 10 * ‖(Work.Kernels.qParamFun w')⁻¹ - (Work.Kernels.qParamFun τ₀)⁻¹‖ := by
          rw [hDnorm]; ring
      _ ≤ ‖Work.Kernels.jInvariantFun w
            - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖ := hfin

-- (end dropped)


/-- **The sharp lower bound for `‖j w - j (i t)‖` on the cusp-`0` neighbourhood `E`**, in the
form used below: `c · e^{2π Im (S • w)} · ‖1 - exp (2π i ((S • w) - i/t))‖ ≤ ‖j w - j (i t)‖`. -/
private lemma jDiff_lower_E :
    ∃ c : ℝ, 0 < c ∧ ∀ (w : ℍ) (t : ℝ) (ht : 0 < t), w ∈ KEpsilon → t ≤ 1 →
      c * (Real.exp (2 * Real.pi * (ModularGroup.S • w).im) *
        ‖1 - Complex.exp (2 * Real.pi * Complex.I *
          (((ModularGroup.S • w : ℍ) : ℂ)
            - ((Work.Kernels.imagAxis (t⁻¹) (inv_pos.mpr ht) : ℍ) : ℂ)))‖)
        ≤ ‖Work.Kernels.jInvariantFun w - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖ := by
  obtain ⟨c, hc, H⟩ := cfx_E_jdiff_small
  refine ⟨c, hc, fun w t ht hw ht1 => ?_⟩
  have h := H w t ht hw ht1
  rw [cfx_neg_inv_mul_I t ht] at h
  simpa only [mul_assoc] using h


/-! ## The good case: `‖sin (π (S • w - i/t))‖ ≥ 1/1000` -/

/-! ## The good case: `‖sin (π (S • w - i/t))‖ ≥ 1/1000` -/

/-! ## The good case

Step 1 (`Kaxis_Kfun_divisor_bound`), the sharp `j`-difference lower bound (`jDiff_lower_E`) and
the divisor lower bound at `i/t` give the bound when
`‖sin (π ((S • w) - i/t))‖ ≥ 1/1000`: the factors `e^{±π/t}` cancel. -/

set_option maxHeartbeats 1000000 in
/-! ## The good case

Step 1 (`Kaxis_Kfun_divisor_bound`), the sharp `j`-difference lower bound (`jDiff_lower_E`) and
the divisor lower bound at `i/t` give the bound when
`‖sin (π ((S • w) - i/t))‖ ≥ 1/1000`: the factors `e^{±π/t}` cancel. -/

set_option maxHeartbeats 1000000 in
/-- **The exact modulus of `1 - exp (2π i ((S • w) - i/t))`.** -/
private lemma one_sub_Eun_eq {w : ℍ} {t : ℝ} (ht : 0 < t) :
    ‖1 - Complex.exp (2 * Real.pi * Complex.I *
        (((ModularGroup.S • w : ℍ) : ℂ)
          - ((Work.Kernels.imagAxis (t⁻¹) (inv_pos.mpr ht) : ℍ) : ℂ)))‖
      = 2 * Real.exp (Real.pi * (t⁻¹ - (ModularGroup.S • w).im)) *
        ‖Complex.sin (Real.pi * (((ModularGroup.S • w : ℍ) : ℂ)
          - ((Work.Kernels.imagAxis (t⁻¹) (inv_pos.mpr ht) : ℍ) : ℂ)))‖ := by
  set w' : ℍ := ModularGroup.S • w with hw'def
  set τ₀ : ℍ := Work.Kernels.imagAxis (t⁻¹) (inv_pos.mpr ht) with hτ₀def
  have hτim : τ₀.im = t⁻¹ := by rw [hτ₀def]; simp [Work.Kernels.imagAxis]
  have hqrel : Complex.exp (2 * Real.pi * Complex.I * ((w' : ℂ) - (τ₀ : ℂ)))
      = Work.Kernels.qParamFun w' * (Work.Kernels.qParamFun τ₀)⁻¹ := by
    simp only [Work.Kernels.qParamFun]
    rw [← Complex.exp_neg, ← Complex.exp_add]
    congr 1
    ring
  have hne : 1 - Complex.exp (2 * Real.pi * Complex.I * ((w' : ℂ) - (τ₀ : ℂ)))
      = (Work.Kernels.qParamFun τ₀ - Work.Kernels.qParamFun w')
        * (Work.Kernels.qParamFun τ₀)⁻¹ := by
    rw [hqrel, sub_mul,
      mul_inv_cancel₀ (Complex.exp_ne_zero (2 * Real.pi * Complex.I * (τ₀ : ℂ)))]
  rw [hne, norm_mul, norm_inv, Work.Asymptotics.norm_qParamFun τ₀,
    Work.Asymptotics.norm_qParamFun_sub τ₀ w']
  rw [show ‖Complex.sin (Real.pi * ((τ₀ : ℂ) - (w' : ℂ)))‖
      = ‖Complex.sin (Real.pi * ((w' : ℂ) - (τ₀ : ℂ)))‖ by
    rw [show Real.pi * ((τ₀ : ℂ) - (w' : ℂ)) = -(Real.pi * ((w' : ℂ) - (τ₀ : ℂ))) by ring,
      Complex.sin_neg, norm_neg]]
  rw [hτim]
  rw [show (Real.exp (-(2 * Real.pi * t⁻¹)))⁻¹ = Real.exp (2 * Real.pi * t⁻¹) by
    rw [← Real.exp_neg]; congr 1; ring]
  rw [show 2 * Real.exp (-(Real.pi * (t⁻¹ + w'.im)))
        * ‖Complex.sin (Real.pi * ((w' : ℂ) - (τ₀ : ℂ)))‖ * Real.exp (2 * Real.pi * t⁻¹)
      = 2 * (Real.exp (-(Real.pi * (t⁻¹ + w'.im))) * Real.exp (2 * Real.pi * t⁻¹))
        * ‖Complex.sin (Real.pi * ((w' : ℂ) - (τ₀ : ℂ)))‖ by ring]
  rw [show Real.exp (-(Real.pi * (t⁻¹ + w'.im))) * Real.exp (2 * Real.pi * t⁻¹)
      = Real.exp (Real.pi * (t⁻¹ - w'.im)) by
    rw [← Real.exp_add]; congr 1; ring]

set_option maxHeartbeats 1000000 in
/-- **The good case**: `‖sin (π ((S • w) - i/t))‖ ≥ 1/1000`. -/
private lemma good_case_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (w : ℍ) (t : ℝ) (ht : 0 < t),
      w ∈ KEpsilon → t ≤ 1 →
      Work.Kernels.jInvariantFun w ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) →
      (1 / 1000 : ℝ) ≤ ‖Complex.sin (Real.pi * (((ModularGroup.S • w : ℍ) : ℂ)
        - ((Work.Kernels.imagAxis (t⁻¹) (inv_pos.mpr ht) : ℍ) : ℂ)))‖ →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t‖ ≤ C * (Work.Kernels.scale w) ^ N := by
  obtain ⟨C₁, N₁, hC₁, hN₁, hb₁⟩ := Kaxis_Kfun_divisor_bound ℓ d hd
  obtain ⟨cJ, hcJ, hJL⟩ := jDiff_lower_E
  obtain ⟨cΔ, hcΔ, hΔ₀⟩ := delta_lower_third
  refine ⟨C₁ / (2 * cΔ * cJ * (1 / 1000)) + 1, N₁, by positivity, hN₁,
    fun w t ht hw ht1 hne hsin => ?_⟩
  have hE : (3 / 2 : ℝ) ≤ (ModularGroup.S • w).im := Work.Asymptotics.E_S_im_ge w hw
  have hy0 : (0 : ℝ) ≤ (ModularGroup.S • w).im := le_trans (by norm_num) hE
  have hz1 : (1 / 3 : ℝ) ≤ (Work.Kernels.imagAxis (t⁻¹) (inv_pos.mpr ht)).im := by
    rw [show (Work.Kernels.imagAxis (t⁻¹) (inv_pos.mpr ht)).im = t⁻¹ by
      simp [Work.Kernels.imagAxis]]
    exact le_trans (by norm_num) ((one_le_inv₀ ht).mpr ht1)
  have hΔlow : cΔ * Real.exp (-(2 * Real.pi * t⁻¹))
      ≤ ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis (t⁻¹) (inv_pos.mpr ht))‖ := by
    have h := hΔ₀ (Work.Kernels.imagAxis (t⁻¹) (inv_pos.mpr ht)) hz1
    rw [Work.Asymptotics.norm_qParamFun,
      show (Work.Kernels.imagAxis (t⁻¹) (inv_pos.mpr ht)).im = t⁻¹ by
        simp [Work.Kernels.imagAxis]] at h
    exact h
  have hjz : Work.Kernels.jInvariantFun (Work.Kernels.imagAxis (t⁻¹) (inv_pos.mpr ht))
      = Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) := by
    have h := (Work.Asymptotics.EtailE.jInvariantFun_Ssmul
      (Work.Kernels.imagAxis (t⁻¹) (inv_pos.mpr ht))).symm
    rw [S_smul_imagAxis_inv] at h
    exact h
  -- the sharp `j`-difference lower bound in the sine form, at `z₀ = i/t`
  have hJsin : 2 * cJ * Real.exp (Real.pi * (t⁻¹ + (ModularGroup.S • w).im))
      * ‖Complex.sin (Real.pi * (((ModularGroup.S • w : ℍ) : ℂ)
        - ((Work.Kernels.imagAxis (t⁻¹) (inv_pos.mpr ht) : ℍ) : ℂ)))‖
      ≤ ‖Work.Kernels.jInvariantFun w
          - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis (t⁻¹) (inv_pos.mpr ht))‖ := by
    have h := hJL w t ht hw ht1
    rw [← hjz] at h
    rw [one_sub_Eun_eq (w := w) ht] at h
    have hexp : Real.exp (2 * Real.pi * (ModularGroup.S • w).im)
        * Real.exp (Real.pi * (t⁻¹ - (ModularGroup.S • w).im))
        = Real.exp (Real.pi * (t⁻¹ + (ModularGroup.S • w).im)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [show cJ * (Real.exp (2 * Real.pi * (ModularGroup.S • w).im)
          * (2 * Real.exp (Real.pi * (t⁻¹ - (ModularGroup.S • w).im))
            * ‖Complex.sin (Real.pi * (((ModularGroup.S • w : ℍ) : ℂ)
              - ((Work.Kernels.imagAxis (t⁻¹) (inv_pos.mpr ht) : ℍ) : ℂ)))‖))
        = cJ * (2 * (Real.exp (2 * Real.pi * (ModularGroup.S • w).im)
          * Real.exp (Real.pi * (t⁻¹ - (ModularGroup.S • w).im)))
          * ‖Complex.sin (Real.pi * (((ModularGroup.S • w : ℍ) : ℂ)
            - ((Work.Kernels.imagAxis (t⁻¹) (inv_pos.mpr ht) : ℍ) : ℂ)))‖) by ring,
      hexp] at h
    convert h using 1
    ring
  have hJlow : 2 * cJ * (1 / 1000) * Real.exp (Real.pi * (t⁻¹ + (ModularGroup.S • w).im))
      ≤ ‖Work.Kernels.jInvariantFun w
          - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis (t⁻¹) (inv_pos.mpr ht))‖ := by
    have hpos : (0 : ℝ) ≤ 2 * cJ * Real.exp (Real.pi * (t⁻¹ + (ModularGroup.S • w).im)) := by positivity
    calc 2 * cJ * (1 / 1000) * Real.exp (Real.pi * (t⁻¹ + (ModularGroup.S • w).im))
        = (2 * cJ * Real.exp (Real.pi * (t⁻¹ + (ModularGroup.S • w).im))) * (1 / 1000) := by ring
      _ ≤ (2 * cJ * Real.exp (Real.pi * (t⁻¹ + (ModularGroup.S • w).im)))
            * ‖Complex.sin (Real.pi * (((ModularGroup.S • w : ℍ) : ℂ)
              - ((Work.Kernels.imagAxis (t⁻¹) (inv_pos.mpr ht) : ℍ) : ℂ)))‖ :=
          mul_le_mul_of_nonneg_left hsin hpos
      _ ≤ ‖Work.Kernels.jInvariantFun w
            - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis (t⁻¹) (inv_pos.mpr ht))‖ := by
          simpa only [mul_assoc] using hJsin
  have hden : cΔ * Real.exp (-(2 * Real.pi * t⁻¹))
        * (2 * cJ * (1 / 1000)
            * Real.exp (Real.pi * (t⁻¹ + (ModularGroup.S • w).im)))
      ≤ ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis (t⁻¹) (inv_pos.mpr ht))
          * (Work.Kernels.jInvariantFun w
            - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis (t⁻¹) (inv_pos.mpr ht)))‖ := by
    rw [norm_mul]
    exact mul_le_mul hΔlow hJlow (by positivity) (norm_nonneg _)
  have hstep := hb₁ w t ht hE ht1 hne
  -- the cancellation
  have hB : (0 : ℝ) < cΔ * Real.exp (-(2 * Real.pi * t⁻¹))
      * (2 * cJ * (1 / 1000) * Real.exp (Real.pi * (t⁻¹ + (ModularGroup.S • w).im))) := by positivity
  have hA0 : (0 : ℝ) ≤ C₁ * (Work.Kernels.scale w) ^ N₁ * t ^ ((d : ℤ) / 2 - 4)
      * Real.exp (-(Real.pi / t)) :=
    mul_nonneg (mul_nonneg (mul_nonneg hC₁.le
      (Real.rpow_nonneg (Work.Kernels.scale_pos w).le N₁)) (zpow_nonneg ht.le _))
      (Real.exp_nonneg _)
  have hDpos : 0 < ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis (t⁻¹) (inv_pos.mpr ht))
          * (Work.Kernels.jInvariantFun w
            - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis (t⁻¹) (inv_pos.mpr ht)))‖ :=
    lt_of_lt_of_le hB hden
  have h1 : ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t‖
      ≤ C₁ * (Work.Kernels.scale w) ^ N₁ * t ^ ((d : ℤ) / 2 - 4) * Real.exp (-(Real.pi / t))
        / (cΔ * Real.exp (-(2 * Real.pi * t⁻¹))
          * (2 * cJ * (1 / 1000) * Real.exp (Real.pi * (t⁻¹ + (ModularGroup.S • w).im)))) := by
    refine le_trans hstep ?_
    rw [div_le_div_iff₀ hDpos hB]
    exact mul_le_mul_of_nonneg_left hden hA0
  have hAB : C₁ * (Work.Kernels.scale w) ^ N₁ * t ^ ((d : ℤ) / 2 - 4) * Real.exp (-(Real.pi / t))
        / (cΔ * Real.exp (-(2 * Real.pi * t⁻¹))
          * (2 * cJ * (1 / 1000) * Real.exp (Real.pi * (t⁻¹ + (ModularGroup.S • w).im))))
      ≤ C₁ / (2 * cΔ * cJ * (1 / 1000)) * (Work.Kernels.scale w) ^ N₁ := by
    -- rewrite the quotient as `(C₁/(K)) * (s^N * (t^e * exp(-πy)))`
    have hBs : cΔ * Real.exp (-(2 * Real.pi * t⁻¹))
          * (2 * cJ * (1 / 1000) * Real.exp (Real.pi * (t⁻¹ + (ModularGroup.S • w).im)))
        = (2 * cΔ * cJ * (1 / 1000)) * Real.exp (Real.pi * ((ModularGroup.S • w).im - t⁻¹)) := by
      rw [show cΔ * Real.exp (-(2 * Real.pi * t⁻¹))
            * (2 * cJ * (1 / 1000) * Real.exp (Real.pi * (t⁻¹ + (ModularGroup.S • w).im)))
          = cΔ * (2 * cJ * (1 / 1000)) * (Real.exp (-(2 * Real.pi * t⁻¹))
              * Real.exp (Real.pi * (t⁻¹ + (ModularGroup.S • w).im))) by ring]
      rw [show Real.exp (-(2 * Real.pi * t⁻¹)) * Real.exp (Real.pi * (t⁻¹ + (ModularGroup.S • w).im))
          = Real.exp (Real.pi * ((ModularGroup.S • w).im - t⁻¹)) by
        rw [← Real.exp_add]; congr 1; ring]
      ring
    have hAs : Real.exp (-(Real.pi / t)) = Real.exp (-(Real.pi * t⁻¹)) := by rw [div_eq_mul_inv]
    rw [hBs, hAs,
      show C₁ * (Work.Kernels.scale w) ^ N₁ * t ^ ((d : ℤ) / 2 - 4) * Real.exp (-(Real.pi * t⁻¹))
          / ((2 * cΔ * cJ * (1 / 1000)) * Real.exp (Real.pi * ((ModularGroup.S • w).im - t⁻¹)))
        = (C₁ / (2 * cΔ * cJ * (1 / 1000)))
          * ((Work.Kernels.scale w) ^ N₁ * (t ^ ((d : ℤ) / 2 - 4)
            * (Real.exp (-(Real.pi * t⁻¹)) / Real.exp (Real.pi * ((ModularGroup.S • w).im - t⁻¹))))) by
        have h3 : (2 * cΔ * cJ * (1 / 1000)) ≠ 0 := by positivity
        field_simp,
      show Real.exp (-(Real.pi * t⁻¹)) / Real.exp (Real.pi * ((ModularGroup.S • w).im - t⁻¹))
          = Real.exp (-(Real.pi * (ModularGroup.S • w).im)) by
        rw [← Real.exp_sub]; congr 1; ring]
    have hK : (0 : ℝ) < 2 * cΔ * cJ * (1 / 1000) := by positivity
    have hle2 : (Work.Kernels.scale w) ^ N₁
          * (t ^ ((d : ℤ) / 2 - 4) * Real.exp (-(Real.pi * (ModularGroup.S • w).im)))
        ≤ (Work.Kernels.scale w) ^ N₁ := by
      have ht1' : t ^ ((d : ℤ) / 2 - 4) ≤ 1 := by
        rcases hd with rfl | rfl
        · rw [show (((8 : ℕ) : ℤ) / 2 - 4) = 0 by norm_num, zpow_zero]
        · rw [show (((24 : ℕ) : ℤ) / 2 - 4) = ((8 : ℕ) : ℤ) by norm_num, zpow_natCast]
          exact pow_le_one₀ (le_of_lt ht) ht1
      have hexp2 : Real.exp (-(Real.pi * (ModularGroup.S • w).im)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by
          have hp := mul_nonneg (le_of_lt Real.pi_pos) hy0
          linarith)
      have h1 : (0 : ℝ) ≤ t ^ ((d : ℤ) / 2 - 4) := zpow_nonneg (le_of_lt ht) _
      have hle1 : t ^ ((d : ℤ) / 2 - 4) * Real.exp (-(Real.pi * (ModularGroup.S • w).im)) ≤ 1 := by
        nlinarith [ht1', hexp2, h1]
      simpa using mul_le_mul_of_nonneg_left hle1
        (Real.rpow_nonneg (Work.Kernels.scale_pos w).le N₁)
    exact mul_le_mul_of_nonneg_left hle2 (by positivity)
  have hK : (0 : ℝ) < 2 * cΔ * cJ * (1 / 1000) := by positivity
  have h1le : (1 : ℝ) ≤ (Work.Kernels.scale w) ^ N₁ :=
    Real.one_le_rpow (Work.Kernels.one_le_scale w) hN₁
  have hbig : C₁ / (2 * cΔ * cJ * (1 / 1000)) * (Work.Kernels.scale w) ^ N₁
      ≤ (C₁ / (2 * cΔ * cJ * (1 / 1000)) + 1) * (Work.Kernels.scale w) ^ N₁ := by
    have h3 : (0 : ℝ) ≤ (Work.Kernels.scale w) ^ N₁ := by positivity
    nlinarith [h1le, h3]
  exact le_trans (le_trans h1 hAB) hbig

/-! ## The bad case: the cuspidal-coincidence neighbourhood of the contour

Here `‖sin (π ((S • w) - i/t))‖ < 1/1000`, so `w` is close to a cuspidal coincidence
`w_m = S • (i/t + m)`, at which the *cleared* kernel vanishes
(`KfunClear_cuspParabolic_vanishing`).  The one-zero (Schwarz) estimate `KL.one_zero_apply` at
`w_m` together with the sharp lower bound for `‖j w - j (i/t)‖` (`jDiff_lower_E`) gives the
bound. -/

/-- `Im (S • (γ • (i t))) = t / ((γ 0 0)² t² + (γ 0 1)²)`. -/
private lemma im_S_smul_smul_imagAxis (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) {t : ℝ}
    (ht : 0 < t) :
    (ModularGroup.S • (γ • Work.Kernels.imagAxis t ht)).im
      = t / (((γ 0 0 : ℤ) : ℝ) ^ 2 * t ^ 2 + ((γ 0 1 : ℤ) : ℝ) ^ 2) := by
  have hS : ModularGroup.S • (γ • Work.Kernels.imagAxis t ht)
      = (ModularGroup.S * γ) • Work.Kernels.imagAxis t ht := (mul_smul _ _ _).symm
  rw [hS]
  have h := Work.Asymptotics.im_smul_imagAxis (ModularGroup.S * γ) ht
  simp only [UpperHalfPlane.coe_im] at h ⊢
  rw [h]
  congr 1
  have h10 : ((ModularGroup.S * γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 0) = γ 0 0 := by
    show ((ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 = _
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    simp [ModularGroup.coe_S]
  have h11 : ((ModularGroup.S * γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 1) = γ 0 1 := by
    show ((ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ)) 1 1 = _
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    simp [ModularGroup.coe_S]
  rw [h10, h11]

set_option maxHeartbeats 1000000 in
/-- **The coincidences of the one-zero ball are cuspidal.** -/
lemma KfunClear_zero_of_coincidence_E (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {u : ℍ} {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 9 / 10)
    (hu : (99 / 100) * (100 / 101) ^ 2 * t⁻¹ ≤ (ModularGroup.S • u).im)
    (hcoin : Work.Kernels.jInvariantFun u
      = Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) :
    Work.Kernels.KfunClear ℓ d u (Work.Kernels.imagAxis t ht) = 0 := by
  obtain ⟨γ, hγ⟩ := Work.Asymptotics.jInvariantFun_eq_smul_of_eq hcoin
  have hκ : (0 : ℝ) < (99 / 100) * (100 / 101) ^ 2 := by norm_num
  set a : ℤ := γ 0 0 with ha
  set b : ℤ := γ 0 1 with hb
  set cc : ℤ := γ 1 0 with hcc
  set e : ℤ := γ 1 1 with he
  have hdet : a * e - b * cc = 1 := by
    have h := γ.2
    rw [Matrix.det_fin_two] at h
    rw [ha, hb, hcc, he]
    exact_mod_cast h
  -- `Im (S • u) = t / (a²t² + b²)`
  have hSu : (ModularGroup.S • u).im = t / ((a : ℝ) ^ 2 * t ^ 2 + (b : ℝ) ^ 2) := by
    rw [← hγ, ha, hb]
    exact im_S_smul_smul_imagAxis γ ht
  -- `κ (a²t²+b²) ≤ t²`
  have hAB : (99 / 100) * (100 / 101) ^ 2 * ((a : ℝ) ^ 2 * t ^ 2 + (b : ℝ) ^ 2) ≤ t ^ 2 := by
    have hApos : 0 < (a : ℝ) ^ 2 * t ^ 2 + (b : ℝ) ^ 2 := by
      rcases eq_or_ne a 0 with h | h
      · have hbne : b ≠ 0 := by
          intro hb0'
          rw [h, hb0'] at hdet
          omega
        have h'' : (0 : ℝ) < (b : ℝ) ^ 2 := by
          have h' : (b : ℝ) ≠ 0 := by exact_mod_cast hbne
          positivity
        have h3 : (0 : ℝ) ≤ (a : ℝ) ^ 2 * t ^ 2 := by positivity
        linarith
      · have h'' : (0 : ℝ) < (a : ℝ) ^ 2 * t ^ 2 := by
          have h' : (0 : ℝ) < (a : ℝ) ^ 2 := by
            have h2 : (a : ℝ) ≠ 0 := by exact_mod_cast h
            positivity
          exact mul_pos h' (by positivity)
        linarith [sq_nonneg (b : ℝ)]
    have h2 : (99 / 100) * (100 / 101) ^ 2
        * ((a : ℝ) ^ 2 * t ^ 2 + (b : ℝ) ^ 2) ≤ t ^ 2 := by
      have h3 := hu
      rw [hSu] at h3
      have h6 : (99 / 100) * (100 / 101) ^ 2
          ≤ t ^ 2 / ((a : ℝ) ^ 2 * t ^ 2 + (b : ℝ) ^ 2) := by
        have h7 := mul_le_mul_of_nonneg_right h3 ht.le
        have h8 : (99 / 100) * (100 / 101) ^ 2 * t⁻¹ * t
            = (99 / 100) * (100 / 101) ^ 2 := by
          rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt ht), mul_one]
        have h9 : t / ((a : ℝ) ^ 2 * t ^ 2 + (b : ℝ) ^ 2) * t
            = t ^ 2 / ((a : ℝ) ^ 2 * t ^ 2 + (b : ℝ) ^ 2) := by
          field_simp
        rw [h8, h9] at h7
        exact h7
      exact (le_div_iff₀ hApos).mp h6
    exact h2
  have hb0 : b = 0 := by
    have h0 : (0 : ℝ) ≤ (a : ℝ) ^ 2 * t ^ 2 := by positivity
    have h1 : (b : ℝ) ^ 2 ≤ t ^ 2 / ((99 / 100) * (100 / 101) ^ 2) := by
      rw [le_div_iff₀ hκ]
      nlinarith [hAB]
    have h2 : (b : ℝ) ^ 2 < 1 := by
      have h3 : t ^ 2 ≤ (9 / 10 : ℝ) ^ 2 := by nlinarith [ht.le, ht1]
      have h4 : t ^ 2 / ((99 / 100) * (100 / 101) ^ 2)
          ≤ (9 / 10 : ℝ) ^ 2 / ((99 / 100) * (100 / 101) ^ 2) :=
        div_le_div_of_nonneg_right h3 hκ.le
      have h5 : (9 / 10 : ℝ) ^ 2 / ((99 / 100) * (100 / 101) ^ 2) < 1 := by
        rw [div_lt_one hκ]; norm_num
      linarith
    have h6 : ((b : ℤ) : ℝ) < 1 := by nlinarith [h2, sq_nonneg (((b : ℤ) : ℝ) - 1)]
    have h7 : -1 < ((b : ℤ) : ℝ) := by nlinarith [h2, sq_nonneg (((b : ℤ) : ℝ) + 1)]
    have h8 : b < 1 := by exact_mod_cast h6
    have h9 : -1 < b := by exact_mod_cast h7
    omega
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0, hb0] at hdet
    omega
  have ha2 : a ^ 2 = 1 := by
    have h2 : (b : ℝ) ^ 2 = 0 := by rw [hb0]; norm_num
    have h1 : ((99 / 100) * (100 / 101) ^ 2 * (a : ℝ) ^ 2) * t ^ 2 ≤ 1 * t ^ 2 := by
      have h3 := hAB
      rw [h2, add_zero] at h3
      ring_nf at h3 ⊢
      exact h3
    have ht2 : (0 : ℝ) < t ^ 2 := by positivity
    have h3 : (99 / 100) * (100 / 101) ^ 2 * (a : ℝ) ^ 2 ≤ 1 :=
      le_of_mul_le_mul_right h1 ht2
    have h4 : (a : ℝ) ^ 2 ≤ 4 := by
      have h5 : (1 / 4 : ℝ) < (99 / 100) * (100 / 101) ^ 2 := by norm_num
      nlinarith [h3, h5]
    have h5 : ((a : ℤ) : ℝ) < 2 := by nlinarith [h4, sq_nonneg (((a : ℤ) : ℝ) - 2)]
    have h6 : -2 < ((a : ℤ) : ℝ) := by nlinarith [h4, sq_nonneg (((a : ℤ) : ℝ) + 2)]
    have h7 : a < 2 := by exact_mod_cast h5
    have h8 : -2 < a := by exact_mod_cast h6
    have h9 : a ≠ 0 := by
      intro h0
      rw [h0, hb0] at hdet
      omega
    have h10 : a = -1 ∨ a = 1 := by omega
    rcases h10 with h10 | h10 <;> rw [h10] <;> norm_num
  have he_a : e = a := by
    have h1 : a * e = 1 := by rw [hb0] at hdet; simpa using hdet
    have h2 : a * (e - a) = 0 := by nlinarith [h1, ha2]
    have h3 : e - a = 0 := (mul_eq_zero.mp h2).resolve_left ha0
    omega
  -- `S • u = i/t - c a`
  have hSu_eq : ((ModularGroup.S • u : ℍ) : ℂ)
      = ((-(cc * a) : ℤ) : ℂ) + ((t⁻¹ : ℝ) : ℂ) * Complex.I := by
    rw [← hγ, Work.Kernels.S_smul_coe, UpperHalfPlane.coe_specialLinearGroup_apply]
    simp only [← ha, ← hb, ← hcc, ← he, hb0, he_a, zero_add]
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' (by rw [← sq]; exact ha2) with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [h1]
      rw [show ((Work.Kernels.imagAxis t ht : ℍ) : ℂ) = (t : ℂ) * Complex.I from rfl]
      norm_num
      have hden : ((cc : ℤ) : ℂ) * ((t : ℂ) * Complex.I) + 1 ≠ 0 := by
        intro h0
        have hh := congrArg Complex.re h0
        simp at hh
      field_simp
      ring_nf
      rw [Complex.I_sq]
      have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ht)
      field_simp
      ring
    · rw [h1]
      rw [show ((Work.Kernels.imagAxis t ht : ℍ) : ℂ) = (t : ℂ) * Complex.I from rfl]
      norm_num
      have hden : ((cc : ℤ) : ℂ) * ((t : ℂ) * Complex.I) - 1 ≠ 0 := by
        intro h0
        have hh := congrArg Complex.re h0
        simp at hh
      field_simp
      ring_nf
      rw [Complex.I_sq]
      have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ht)
      field_simp
      ring
  -- identify `u` as a cuspidal coincidence
  have hSupt : ModularGroup.S • u
      = (((-(cc * a) : ℤ) : ℝ) +ᵥ Work.Kernels.imagAxis (t⁻¹) (inv_pos.mpr ht)) := by
    apply UpperHalfPlane.ext
    rw [hSu_eq]
    rw [UpperHalfPlane.coe_vadd]
    simp [Work.Kernels.imagAxis]
  have hu_eq : u = ModularGroup.S •
      (((-(cc * a) : ℤ) : ℝ) +ᵥ Work.Kernels.imagAxis (t⁻¹) (inv_pos.mpr ht)) := by
    have h := congrArg (fun w : ℍ => ModularGroup.S • w) hSupt
    rwa [S_smul_S_smul] at h
  have hSit : Work.Kernels.imagAxis (t⁻¹) (inv_pos.mpr ht)
      = ModularGroup.S • Work.Kernels.imagAxis t ht := by
    rw [← S_smul_imagAxis_inv ht, S_smul_S_smul]
  have h := Work.Asymptotics.KfunClear_cuspParabolic_vanishing ℓ d hd (-(cc * a))
    (Work.Kernels.imagAxis t ht)
  rw [show ModularGroup.S • Work.Kernels.imagAxis t ht
      = Work.Kernels.imagAxis (t⁻¹) (inv_pos.mpr ht) from hSit.symm] at h
  rw [hu_eq]
  exact h



-- (M-bound lemma: moved below, being rewritten)



/-- **Geometry of the one-zero ball.**  For `u` within `w_m.im / 100` of `w_m`: the height, the
norm and the `scale` of `u` are pinned to those of `w_m` (up to the factors `99/100`, `101/100`
and `2`), and `Im (S • u) ≥ (99/100)(100/101)² Im (S • w_m)`. -/
private lemma ball_geometry {w_m u : ℍ} (hu : ‖(u : ℂ) - (w_m : ℂ)‖ ≤ w_m.im / 100) :
    (99 / 100) * w_m.im ≤ u.im ∧ (99 / 100) * ‖(w_m : ℂ)‖ ≤ ‖(u : ℂ)‖ ∧
      ‖(u : ℂ)‖ ≤ (101 / 100) * ‖(w_m : ℂ)‖ ∧
      Work.Kernels.scale u ≤ 2 * Work.Kernels.scale w_m ∧
      (99 / 100) * (100 / 101) ^ 2 * (ModularGroup.S • w_m).im ≤ (ModularGroup.S • u).im := by
  have hr : (0 : ℝ) < w_m.im := w_m.im_pos
  have him : (99 / 100) * w_m.im ≤ u.im := by
    have h := Complex.abs_im_le_norm ((u : ℂ) - (w_m : ℂ))
    have h2 : ((u : ℂ) - (w_m : ℂ)).im = u.im - w_m.im := by simp
    have h3 : -(((u : ℂ) - (w_m : ℂ)).im) ≤ ‖(u : ℂ) - (w_m : ℂ)‖ :=
      le_trans (neg_le_abs _) h
    rw [h2] at h3
    nlinarith [h3, hu, hr]
  have hnorm_ge : (99 / 100) * ‖(w_m : ℂ)‖ ≤ ‖(u : ℂ)‖ := by
    have h := (abs_le.mp (abs_norm_sub_norm_le (u : ℂ) ((w_m : ℂ)))).1
    have h4 := Work.Kernels.im_le_coe_norm w_m
    linarith [h, hu, h4]
  have hnorm_le : ‖(u : ℂ)‖ ≤ (101 / 100) * ‖(w_m : ℂ)‖ := by
    have h1 : ‖(u : ℂ)‖ ≤ ‖(w_m : ℂ)‖ + ‖(u : ℂ) - (w_m : ℂ)‖ := by
      have h := norm_add_le ((w_m : ℂ)) ((u : ℂ) - (w_m : ℂ))
      rw [add_sub_cancel] at h
      exact h
    have h2 : w_m.im / 100 ≤ (1 / 100) * ‖(w_m : ℂ)‖ := by
      have h3 := Work.Kernels.im_le_coe_norm w_m
      linarith
    linarith [h1, hu, h2]
  have hscale : Work.Kernels.scale u ≤ 2 * Work.Kernels.scale w_m := by
    have h1a : u.im⁻¹ ≤ ((99 / 100) * w_m.im)⁻¹ :=
      (inv_le_inv₀ u.im_pos (by positivity)).mpr him
    have h1b : ((99 / 100) * w_m.im)⁻¹ = (100 / 99) * w_m.im⁻¹ := by
      field_simp
      try ring
    have h1 : u.im⁻¹ ≤ (100 / 99) * w_m.im⁻¹ := by rw [h1b] at h1a; exact h1a
    simp only [Work.Kernels.scale]
    nlinarith [h1, hnorm_le, norm_nonneg (u : ℂ), norm_nonneg (w_m : ℂ),
      inv_nonneg.mpr hr.le]
  exact ⟨him, hnorm_ge, hnorm_le, hscale, S_im_ge_of_ball (by norm_num) hu⟩



/-- `(imagAxis t ht).im = t`. -/
private lemma im_imagAxis {t : ℝ} (ht : 0 < t) : (Work.Kernels.imagAxis t ht).im = t := by
  simp [Work.Kernels.imagAxis]

/-- `‖(imagAxis t ht : ℂ)‖ = t`. -/
private lemma norm_imagAxis {t : ℝ} (ht : 0 < t) :
    ‖((Work.Kernels.imagAxis t ht : ℍ) : ℂ)‖ = t := by
  rw [show ((Work.Kernels.imagAxis t ht : ℍ) : ℂ) = (t : ℂ) * Complex.I from rfl,
    norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]

/-- `Im (S • (it)) = 1/t`. -/
private lemma S_im_imagAxis {t : ℝ} (ht : 0 < t) :
    (ModularGroup.S • Work.Kernels.imagAxis t ht).im = t⁻¹ := by
  rw [Work.Asymptotics.EReg_S_im, im_imagAxis ht, norm_imagAxis ht]
  field_simp


set_option maxHeartbeats 4000000 in
/-- **The `M`-bound of the one-zero estimate.**  On the closed ball of radius `w_m.im / 100`
about a cuspidal coincidence `w_m` of height `1/t`, the cleared kernel is bounded by the Step-1
expression with the divisor cancelled. -/
lemma KfunClear_le_of_ball (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (cΔ : ℝ) (hcΔ : 0 < cΔ)
    (hΔ₀ : ∀ z : ℍ, 1 / 3 ≤ z.im → cΔ * ‖Work.Kernels.qParamFun z‖ ≤ ‖Work.Kernels.DeltaFun z‖) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ (t : ℝ) (ht : 0 < t) (htinv : 1 ≤ t⁻¹)
        (h32 : (3 / 2 : ℝ) ≤ (99 / 100) * (100 / 101) ^ 2 * t⁻¹) (w_m : ℍ),
        (ModularGroup.S • w_m).im = t⁻¹ →
        Work.Kernels.KfunClear ℓ d w_m (Work.Kernels.imagAxis t ht) = 0 →
        ∀ u : ℍ, ‖(u : ℂ) - (w_m : ℂ)‖ ≤ w_m.im / 100 →
          ‖Work.Kernels.KfunClear ℓ d u (Work.Kernels.imagAxis t ht)‖
            ≤ C * (2 * Work.Kernels.scale w_m) ^ N * t ^ ((d : ℤ) / 2 - 4)
              * Real.exp (-(Real.pi / t))
              * (‖(w_m : ℂ)‖ ^ (-(12 : ℤ)) * Real.exp (-(Real.pi * (9 / 5) / t)))
              * (2 * t ^ (-(12 : ℤ)) * Real.exp (-(2 * Real.pi / t)))
                  ^ (if d = 8 then 1 else 2)
              / (cΔ * Real.exp (-(2 * Real.pi / t))) := by
  obtain ⟨C₁, N₁, hC₁, hN₁, hb₁⟩ := Kaxis_Kfun_divisor_bound ℓ d hd
  have hκ9 : (9 / 10 : ℝ) ≤ (99 / 100) * (100 / 101) ^ 2 := by norm_num
  refine ⟨C₁ * 2 * (100 / 99 : ℝ) ^ 12 * 2 ^ (if d = 8 then 1 else 2) + 1, N₁,
    by positivity, hN₁, fun t ht htinv h32 w_m hwm hzero u hu => ?_⟩
  have ht9 : t ≤ 9 / 10 := by
    have hκ1 : (99 / 100) * (100 / 101) ^ 2 ≤ 1 := by norm_num
    have h1 : (10 / 9 : ℝ) ≤ t⁻¹ := by
      have h2 : (3 / 2 : ℝ) / ((99 / 100) * (100 / 101) ^ 2) ≤ t⁻¹ := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < (99 / 100) * (100 / 101) ^ 2)]
        linarith [h32]
      have h3 : (10 / 9 : ℝ) ≤ (3 / 2) / ((99 / 100) * (100 / 101) ^ 2) := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < (99 / 100) * (100 / 101) ^ 2)]
        nlinarith [hκ1]
      linarith [h2, h3]
    have h4 : (10 / 9 : ℝ) * t ≤ 1 := by
      have h5 := mul_le_mul_of_nonneg_right h1 ht.le
      rwa [inv_mul_cancel₀ ht.ne'] at h5
    linarith [h4]
  have htle1 : t ≤ 1 := le_trans ht9 (by norm_num)
  obtain ⟨him, hnorm_ge, hnorm_le, hscale, hSu_ge⟩ := ball_geometry hu
  rw [hwm] at hSu_ge
  have hSu1 : (3 / 2 : ℝ) ≤ (ModularGroup.S • u).im := by linarith [hSu_ge, h32]
  by_cases hne : Work.Kernels.jInvariantFun u
      = Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)
  · rw [KfunClear_zero_of_coincidence_E ℓ d hd ht ht9 hSu_ge hne, norm_zero]
    have hA : (0 : ℝ) ≤ (C₁ * 2 * (100 / 99 : ℝ) ^ 12 * 2 ^ (if d = 8 then 1 else 2) + 1)
        * (2 * Work.Kernels.scale w_m) ^ N₁ := by
      refine mul_nonneg (by positivity) ?_
      exact Real.rpow_nonneg (mul_nonneg (by norm_num) (Work.Kernels.scale_pos w_m).le) N₁
    have hB : (0 : ℝ) ≤ t ^ ((d : ℤ) / 2 - 4) := zpow_nonneg ht.le _
    have hC : (0 : ℝ) ≤ Real.exp (-(Real.pi / t)) := (Real.exp_pos _).le
    have hD : (0 : ℝ) ≤ ‖(w_m : ℂ)‖ ^ (-(12 : ℤ)) * Real.exp (-(Real.pi * (9 / 5) / t)) :=
      mul_nonneg (by positivity : (0 : ℝ) ≤ ‖(w_m : ℂ)‖ ^ (-(12 : ℤ))) (Real.exp_nonneg _)
    have hE : (0 : ℝ) ≤ (2 * t ^ (-(12 : ℤ)) * Real.exp (-(2 * Real.pi / t)))
        ^ (if d = 8 then 1 else 2) :=
      pow_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
          (zpow_nonneg ht.le (-(12 : ℤ))))
        (Real.exp_nonneg (-(2 * Real.pi / t))))
        (n := (if d = 8 then (1 : ℕ) else 2))
    have hF : (0 : ℝ) ≤ (cΔ * Real.exp (-(2 * Real.pi / t)))⁻¹ :=
      inv_nonneg.mpr (mul_nonneg hcΔ.le (Real.exp_nonneg _))
    rw [div_eq_mul_inv]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hA hB) hC) hD) hE) hF
  · have hjz : Work.Kernels.jInvariantFun (Work.Kernels.imagAxis (t⁻¹) (inv_pos.mpr ht))
        = Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) := by
      have h := (Work.Asymptotics.EtailE.jInvariantFun_Ssmul
        (Work.Kernels.imagAxis (t⁻¹) (inv_pos.mpr ht))).symm
      rw [S_smul_imagAxis_inv] at h
      exact h
    have hstep := hb₁ u t ht hSu1 htle1 hne
    rw [Work.Kernels.Kaxis, dif_pos ht] at hstep
    have hgp0 : Work.Kernels.growthPrefactor d u (Work.Kernels.imagAxis t ht) ≠ 0 := by
      simp only [Work.Kernels.growthPrefactor]
      exact mul_ne_zero
        (mul_ne_zero (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero _)
          (pow_ne_zero _ (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero _)))
        (sub_ne_zero.mpr hne)
    have hgp : Work.Kernels.KfunClear ℓ d u (Work.Kernels.imagAxis t ht)
        = Work.Kernels.Kfun ℓ d u (Work.Kernels.imagAxis t ht)
          * Work.Kernels.growthPrefactor d u (Work.Kernels.imagAxis t ht) := by
      have h := Work.Asymptotics.KL.Kfun_eq_KfunClear_div ℓ d hd u (Work.Kernels.imagAxis t ht) hne
      rw [h, div_mul_cancel₀ _ hgp0]
    have hDpos : 0 < ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis (t⁻¹) (inv_pos.mpr ht))
        * (Work.Kernels.jInvariantFun u
          - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis (t⁻¹) (inv_pos.mpr ht)))‖ := by
      rw [norm_mul, hjz]
      exact mul_pos (norm_pos_iff.mpr (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero _))
        (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
    have hD : ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis (t⁻¹) (inv_pos.mpr ht))
        * (Work.Kernels.jInvariantFun u
          - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis (t⁻¹) (inv_pos.mpr ht)))‖
        = ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis (t⁻¹) (inv_pos.mpr ht))‖
          * ‖Work.Kernels.jInvariantFun u
            - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖ := by
      rw [norm_mul, hjz]
    -- Step 1 multiplied through by the divisor
    have hstep2 : ‖Work.Kernels.Kfun ℓ d u (Work.Kernels.imagAxis t ht)‖
        * (‖Work.Kernels.DeltaFun u‖
          * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ ^ (if d = 8 then 1 else 2)
          * ‖Work.Kernels.jInvariantFun u
            - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖)
        * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis (t⁻¹) (inv_pos.mpr ht))‖
        ≤ C₁ * Work.Kernels.scale u ^ N₁ * t ^ ((d : ℤ) / 2 - 4) * Real.exp (-(Real.pi / t))
          * (‖Work.Kernels.DeltaFun u‖
            * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ ^ (if d = 8 then 1 else 2)) := by
      have h := (le_div_iff₀ hDpos).mp hstep
      rw [hD] at h
      have hpos : (0 : ℝ) ≤ ‖Work.Kernels.DeltaFun u‖
          * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ ^ (if d = 8 then 1 else 2) :=
        mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)
      have h2 := mul_le_mul_of_nonneg_right h hpos
      calc ‖Work.Kernels.Kfun ℓ d u (Work.Kernels.imagAxis t ht)‖
            * (‖Work.Kernels.DeltaFun u‖
              * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ ^ (if d = 8 then 1 else 2)
              * ‖Work.Kernels.jInvariantFun u
                - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖)
            * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis (t⁻¹) (inv_pos.mpr ht))‖
          = (‖Work.Kernels.Kfun ℓ d u (Work.Kernels.imagAxis t ht)‖
              * (‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis (t⁻¹) (inv_pos.mpr ht))‖
                * ‖Work.Kernels.jInvariantFun u
                  - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖))
            * (‖Work.Kernels.DeltaFun u‖
              * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ ^ (if d = 8 then 1 else 2)) := by
            ring
        _ ≤ (C₁ * Work.Kernels.scale u ^ N₁ * t ^ ((d : ℤ) / 2 - 4) * Real.exp (-(Real.pi / t)))
              * (‖Work.Kernels.DeltaFun u‖
                * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ ^ (if d = 8 then 1 else 2)) := h2
    -- the three factor bounds
    have hΔu : ‖Work.Kernels.DeltaFun u‖
        ≤ 2 * (100 / 99 : ℝ) ^ 12 * (‖(w_m : ℂ)‖ ^ (-(12 : ℤ))
            * Real.exp (-(Real.pi * (9 / 5) / t))) := by
      have hSu1' : (1 : ℝ) ≤ (ModularGroup.S • u).im := by linarith [hSu1]
      have h1 := Work.Asymptotics.norm_DeltaFun_le_of_im (u := u) hSu1'
      have hineq : (‖(u : ℂ)‖)⁻¹ ≤ ((99 / 100) * ‖(w_m : ℂ)‖)⁻¹ :=
        (inv_le_inv₀ (norm_pos_iff.mpr u.ne_zero)
          (mul_pos (by norm_num) (norm_pos_iff.mpr w_m.ne_zero))).mpr hnorm_ge
      have hineq2 : (‖(u : ℂ)‖)⁻¹ ≤ (100 / 99 : ℝ) * (‖(w_m : ℂ)‖)⁻¹ := by
        have h2 : ((99 / 100) * ‖(w_m : ℂ)‖)⁻¹ = (100 / 99) * (‖(w_m : ℂ)‖)⁻¹ := by
          field_simp
          try ring
        rw [h2] at hineq
        exact hineq
      have hpow : ‖(u : ℂ)‖ ^ (-(12 : ℤ))
          ≤ (100 / 99 : ℝ) ^ 12 * ‖(w_m : ℂ)‖ ^ (-(12 : ℤ)) := by
        have h2 : (‖(u : ℂ)‖)⁻¹ ^ (12 : ℕ)
            ≤ ((100 / 99 : ℝ) * (‖(w_m : ℂ)‖)⁻¹) ^ (12 : ℕ) :=
          pow_le_pow_left₀ (by positivity) hineq2 12
        rw [mul_pow] at h2
        rw [_root_.zpow_neg, _root_.zpow_neg, zpow_ofNat, zpow_ofNat, ← _root_.inv_pow,
          ← _root_.inv_pow]
        exact h2
      have hexp : Real.exp (-(2 * Real.pi * (ModularGroup.S • u).im))
          ≤ Real.exp (-(Real.pi * (9 / 5) / t)) := by
        rw [Real.exp_le_exp]
        have h3 : (9 / 10 : ℝ) / t ≤ (ModularGroup.S • u).im := by
          have h := mul_le_mul_of_nonneg_right hκ9 (inv_nonneg.mpr ht.le)
          have h5 : (9 / 10 : ℝ) * t⁻¹ = (9 / 10) / t := by ring
          rw [h5] at h
          linarith [hSu_ge, h]
        have h4 : Real.pi * (9 / 5) / t = 2 * Real.pi * ((9 / 10) / t) := by ring
        rw [h4, neg_le_neg_iff]
        exact mul_le_mul_of_nonneg_left h3 (by positivity)
      calc ‖Work.Kernels.DeltaFun u‖
          ≤ 2 * (‖(u : ℂ)‖ ^ (-(12 : ℤ)))
              * Real.exp (-(2 * Real.pi * (ModularGroup.S • u).im)) := h1
        _ ≤ 2 * ((100 / 99 : ℝ) ^ 12 * ‖(w_m : ℂ)‖ ^ (-(12 : ℤ)))
              * Real.exp (-(Real.pi * (9 / 5) / t)) := by
            have h5 : (0 : ℝ) ≤ Real.exp (-(Real.pi * (9 / 5) / t)) := (Real.exp_pos _).le
            have h6 : (0 : ℝ) ≤ (100 / 99 : ℝ) ^ 12 * ‖(w_m : ℂ)‖ ^ (-(12 : ℤ)) := by positivity
            have h7 : (0 : ℝ) ≤ ‖(u : ℂ)‖ ^ (-(12 : ℤ)) := by positivity
            have h8 : (0 : ℝ) ≤ Real.exp (-(2 * Real.pi * (ModularGroup.S • u).im)) :=
              (Real.exp_pos _).le
            have hA : ‖(u : ℂ)‖ ^ (-(12 : ℤ))
                * Real.exp (-(2 * Real.pi * (ModularGroup.S • u).im))
                ≤ ((100 / 99 : ℝ) ^ 12 * ‖(w_m : ℂ)‖ ^ (-(12 : ℤ)))
                  * Real.exp (-(Real.pi * (9 / 5) / t)) :=
              mul_le_mul hpow hexp h8 h6
            nlinarith [hA]
        _ = 2 * (100 / 99 : ℝ) ^ 12 * (‖(w_m : ℂ)‖ ^ (-(12 : ℤ))
              * Real.exp (-(Real.pi * (9 / 5) / t))) := by ring
    have hΔz : ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖
          ^ (if d = 8 then 1 else 2)
        ≤ (2 * t ^ (-(12 : ℤ)) * Real.exp (-(2 * Real.pi / t)))
            ^ (if d = 8 then 1 else 2) := by
      have h1 : (1 : ℝ) ≤ (ModularGroup.S • Work.Kernels.imagAxis t ht).im := by
        rw [S_im_imagAxis ht]
        linarith [htinv]
      have h2 := Work.Asymptotics.norm_DeltaFun_le_of_im (u := Work.Kernels.imagAxis t ht) h1
      rw [norm_imagAxis ht, S_im_imagAxis ht,
        show -(2 * Real.pi * t⁻¹) = -(2 * Real.pi / t) by rw [div_eq_mul_inv]] at h2
      exact pow_le_pow_left₀ (norm_nonneg _) h2 (if d = 8 then 1 else 2)
    have hΔzlow : cΔ * Real.exp (-(2 * Real.pi / t))
        ≤ ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis (t⁻¹) (inv_pos.mpr ht))‖ := by
      have h1 : (1 / 3 : ℝ) ≤ (Work.Kernels.imagAxis (t⁻¹) (inv_pos.mpr ht)).im := by
        rw [im_imagAxis (inv_pos.mpr ht)]
        linarith [htinv]
      have h := hΔ₀ _ h1
      rw [Work.Asymptotics.norm_qParamFun, im_imagAxis (inv_pos.mpr ht)] at h
      simpa only [div_eq_mul_inv] using h
    -- combine: Step 1 times the divisor, then divide by `‖Δ(i/t)‖`
    have hΔitpos : 0 < ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis (t⁻¹) (inv_pos.mpr ht))‖ :=
      norm_pos_iff.mpr (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero _)
    have hcle : ‖Work.Kernels.KfunClear ℓ d u (Work.Kernels.imagAxis t ht)‖
        * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis (t⁻¹) (inv_pos.mpr ht))‖
        ≤ (C₁ * Work.Kernels.scale u ^ N₁ * t ^ ((d : ℤ) / 2 - 4) * Real.exp (-(Real.pi / t)))
          * (‖Work.Kernels.DeltaFun u‖
            * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ ^ (if d = 8 then 1 else 2)) := by
      have h3 : ‖Work.Kernels.KfunClear ℓ d u (Work.Kernels.imagAxis t ht)‖
          = ‖Work.Kernels.Kfun ℓ d u (Work.Kernels.imagAxis t ht)‖
            * (‖Work.Kernels.DeltaFun u‖
              * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ ^ (if d = 8 then 1 else 2)
              * ‖Work.Kernels.jInvariantFun u
                - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖) := by
        rw [hgp, norm_mul, Work.Asymptotics.KL.norm_growthPrefactor]
      rw [h3]
      exact hstep2
    have h1 : ‖Work.Kernels.KfunClear ℓ d u (Work.Kernels.imagAxis t ht)‖
        ≤ (C₁ * Work.Kernels.scale u ^ N₁ * t ^ ((d : ℤ) / 2 - 4) * Real.exp (-(Real.pi / t)))
          * (‖Work.Kernels.DeltaFun u‖
            * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ ^ (if d = 8 then 1 else 2))
          / ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis (t⁻¹) (inv_pos.mpr ht))‖ :=
      (le_div_iff₀ hΔitpos).mpr hcle
    have hRHS_pos : 0 < cΔ * Real.exp (-(2 * Real.pi / t)) := by positivity
    have hY : (0 : ℝ) ≤ 2 * (100 / 99 : ℝ) ^ 12 * (‖(w_m : ℂ)‖ ^ (-(12 : ℤ))
        * Real.exp (-(Real.pi * (9 / 5) / t))) := by
      refine mul_nonneg (by norm_num) ?_
      exact mul_nonneg (by positivity) (Real.exp_nonneg _)
    have hZ : (0 : ℝ) ≤ (2 * t ^ (-(12 : ℤ)) * Real.exp (-(2 * Real.pi / t)))
        ^ (if d = 8 then 1 else 2) :=
      pow_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
          (zpow_nonneg ht.le (-(12 : ℤ))))
        (Real.exp_nonneg (-(2 * Real.pi / t))))
        (n := (if d = 8 then (1 : ℕ) else 2))
    have h2 : ‖Work.Kernels.KfunClear ℓ d u (Work.Kernels.imagAxis t ht)‖
        ≤ (C₁ * Work.Kernels.scale u ^ N₁ * t ^ ((d : ℤ) / 2 - 4) * Real.exp (-(Real.pi / t)))
          * (2 * (100 / 99 : ℝ) ^ 12 * (‖(w_m : ℂ)‖ ^ (-(12 : ℤ))
              * Real.exp (-(Real.pi * (9 / 5) / t))))
          * (2 * t ^ (-(12 : ℤ)) * Real.exp (-(2 * Real.pi / t)))
              ^ (if d = 8 then 1 else 2)
          / (cΔ * Real.exp (-(2 * Real.pi / t))) := by
      refine le_trans h1 ?_
      have hX : (0 : ℝ) ≤ C₁ * Work.Kernels.scale u ^ N₁ * t ^ ((d : ℤ) / 2 - 4)
          * Real.exp (-(Real.pi / t)) :=
        mul_nonneg (mul_nonneg (mul_nonneg hC₁.le
          (Real.rpow_nonneg (Work.Kernels.scale_pos u).le N₁))
          (zpow_nonneg ht.le ((d : ℤ) / 2 - 4))) (Real.exp_nonneg _)
      have hBC : (0 : ℝ) ≤ ‖Work.Kernels.DeltaFun u‖
          * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ ^ (if d = 8 then 1 else 2) :=
        mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)
      have hq : ‖Work.Kernels.DeltaFun u‖
            * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ ^ (if d = 8 then 1 else 2)
            / ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis (t⁻¹) (inv_pos.mpr ht))‖
          ≤ (2 * (100 / 99 : ℝ) ^ 12 * (‖(w_m : ℂ)‖ ^ (-(12 : ℤ))
              * Real.exp (-(Real.pi * (9 / 5) / t))))
            * (2 * t ^ (-(12 : ℤ)) * Real.exp (-(2 * Real.pi / t)))
              ^ (if d = 8 then 1 else 2)
            / (cΔ * Real.exp (-(2 * Real.pi / t))) := by
        rw [div_le_div_iff₀ hΔitpos hRHS_pos]
        have hBC : (0 : ℝ) ≤ ‖Work.Kernels.DeltaFun u‖
            * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ ^ (if d = 8 then 1 else 2) :=
          mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)
        have hYZ : (0 : ℝ) ≤ (2 * (100 / 99 : ℝ) ^ 12 * (‖(w_m : ℂ)‖ ^ (-(12 : ℤ))
              * Real.exp (-(Real.pi * (9 / 5) / t))))
            * (2 * t ^ (-(12 : ℤ)) * Real.exp (-(2 * Real.pi / t)))
              ^ (if d = 8 then 1 else 2) := mul_nonneg hY hZ
        have hnum : ‖Work.Kernels.DeltaFun u‖
            * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ ^ (if d = 8 then 1 else 2)
            ≤ (2 * (100 / 99 : ℝ) ^ 12 * (‖(w_m : ℂ)‖ ^ (-(12 : ℤ))
                * Real.exp (-(Real.pi * (9 / 5) / t))))
              * (2 * t ^ (-(12 : ℤ)) * Real.exp (-(2 * Real.pi / t)))
                ^ (if d = 8 then 1 else 2) :=
          mul_le_mul hΔu hΔz (pow_nonneg (norm_nonneg _) _) hY
        have h1 := mul_le_mul_of_nonneg_right hnum hRHS_pos.le
        have h2' := mul_le_mul_of_nonneg_left hΔzlow hYZ
        linarith [h1, h2']
      rw [div_le_div_iff₀ hΔitpos hRHS_pos] at hq
      rw [div_le_div_iff₀ hΔitpos hRHS_pos]
      have key := mul_le_mul_of_nonneg_left hq hX
      ring_nf at key ⊢
      exact key
    refine le_trans h2 ?_
    have h8 : C₁ * (Work.Kernels.scale u) ^ N₁ * (2 * (100 / 99 : ℝ) ^ 12)
        ≤ (C₁ * 2 * (100 / 99 : ℝ) ^ 12 * 2 ^ (if d = 8 then 1 else 2) + 1)
          * (2 * Work.Kernels.scale w_m) ^ N₁ := by
      have h1 : (Work.Kernels.scale u) ^ N₁ ≤ (2 * Work.Kernels.scale w_m) ^ N₁ :=
        Real.rpow_le_rpow (Work.Kernels.scale_pos u).le hscale hN₁
      have h2 : C₁ * (Work.Kernels.scale u) ^ N₁ * (2 * (100 / 99 : ℝ) ^ 12)
          ≤ C₁ * (2 * Work.Kernels.scale w_m) ^ N₁ * (2 * (100 / 99 : ℝ) ^ 12) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hC₁.le) (by norm_num)
      have h3 : (0 : ℝ) ≤ (2 * Work.Kernels.scale w_m) ^ N₁ :=
        Real.rpow_nonneg (mul_nonneg (by norm_num) (Work.Kernels.scale_pos w_m).le) N₁
      have h4 : (1 : ℝ) ≤ 2 ^ (if d = 8 then 1 else 2) := by
        rcases hd with h | h <;> rw [h] <;> norm_num
      have h5 : C₁ * (2 * Work.Kernels.scale w_m) ^ N₁ * (2 * (100 / 99 : ℝ) ^ 12)
          ≤ (C₁ * 2 * (100 / 99 : ℝ) ^ 12 * 2 ^ (if d = 8 then 1 else 2) + 1)
            * (2 * Work.Kernels.scale w_m) ^ N₁ := by
        have h6 : C₁ * 2 * (100 / 99 : ℝ) ^ 12 ≤ C₁ * 2 * (100 / 99 : ℝ) ^ 12
            * 2 ^ (if d = 8 then 1 else 2) :=
          le_mul_of_one_le_right (by positivity) h4
        nlinarith [h3, hC₁, h6]
      linarith [h2, h5]
    have hgoal : (C₁ * (Work.Kernels.scale u) ^ N₁ * t ^ ((d : ℤ) / 2 - 4)
          * Real.exp (-(Real.pi / t)))
        * (2 * (100 / 99 : ℝ) ^ 12 * (‖(w_m : ℂ)‖ ^ (-(12 : ℤ))
            * Real.exp (-(Real.pi * (9 / 5) / t))))
        * (2 * t ^ (-(12 : ℤ)) * Real.exp (-(2 * Real.pi / t)))
            ^ (if d = 8 then 1 else 2)
        / (cΔ * Real.exp (-(2 * Real.pi / t)))
        ≤ (C₁ * 2 * (100 / 99 : ℝ) ^ 12 * 2 ^ (if d = 8 then 1 else 2) + 1)
          * (2 * Work.Kernels.scale w_m) ^ N₁ * t ^ ((d : ℤ) / 2 - 4)
            * Real.exp (-(Real.pi / t))
            * (‖(w_m : ℂ)‖ ^ (-(12 : ℤ)) * Real.exp (-(Real.pi * (9 / 5) / t)))
            * (2 * t ^ (-(12 : ℤ)) * Real.exp (-(2 * Real.pi / t)))
                ^ (if d = 8 then 1 else 2)
            / (cΔ * Real.exp (-(2 * Real.pi / t))) := by
      have hfac : (0 : ℝ) ≤ t ^ ((d : ℤ) / 2 - 4) * Real.exp (-(Real.pi / t))
          * (‖(w_m : ℂ)‖ ^ (-(12 : ℤ)) * Real.exp (-(Real.pi * (9 / 5) / t)))
          * (2 * t ^ (-(12 : ℤ)) * Real.exp (-(2 * Real.pi / t)))
              ^ (if d = 8 then 1 else 2)
          / (cΔ * Real.exp (-(2 * Real.pi / t))) := by positivity
      have e1 : (C₁ * (Work.Kernels.scale u) ^ N₁ * t ^ ((d : ℤ) / 2 - 4)
            * Real.exp (-(Real.pi / t)))
          * (2 * (100 / 99 : ℝ) ^ 12 * (‖(w_m : ℂ)‖ ^ (-(12 : ℤ))
              * Real.exp (-(Real.pi * (9 / 5) / t))))
          * (2 * t ^ (-(12 : ℤ)) * Real.exp (-(2 * Real.pi / t)))
              ^ (if d = 8 then 1 else 2)
          / (cΔ * Real.exp (-(2 * Real.pi / t)))
          = (C₁ * (Work.Kernels.scale u) ^ N₁ * (2 * (100 / 99 : ℝ) ^ 12))
            * (t ^ ((d : ℤ) / 2 - 4) * Real.exp (-(Real.pi / t))
              * (‖(w_m : ℂ)‖ ^ (-(12 : ℤ)) * Real.exp (-(Real.pi * (9 / 5) / t)))
              * (2 * t ^ (-(12 : ℤ)) * Real.exp (-(2 * Real.pi / t)))
                  ^ (if d = 8 then 1 else 2)
              / (cΔ * Real.exp (-(2 * Real.pi / t)))) := by ring
      have e2 : (C₁ * 2 * (100 / 99 : ℝ) ^ 12 * 2 ^ (if d = 8 then 1 else 2) + 1)
          * (2 * Work.Kernels.scale w_m) ^ N₁ * t ^ ((d : ℤ) / 2 - 4)
            * Real.exp (-(Real.pi / t))
            * (‖(w_m : ℂ)‖ ^ (-(12 : ℤ)) * Real.exp (-(Real.pi * (9 / 5) / t)))
            * (2 * t ^ (-(12 : ℤ)) * Real.exp (-(2 * Real.pi / t)))
                ^ (if d = 8 then 1 else 2)
            / (cΔ * Real.exp (-(2 * Real.pi / t)))
          = ((C₁ * 2 * (100 / 99 : ℝ) ^ 12 * 2 ^ (if d = 8 then 1 else 2) + 1)
            * (2 * Work.Kernels.scale w_m) ^ N₁)
            * (t ^ ((d : ℤ) / 2 - 4) * Real.exp (-(Real.pi / t))
              * (‖(w_m : ℂ)‖ ^ (-(12 : ℤ)) * Real.exp (-(Real.pi * (9 / 5) / t)))
              * (2 * t ^ (-(12 : ℤ)) * Real.exp (-(2 * Real.pi / t)))
                  ^ (if d = 8 then 1 else 2)
              / (cΔ * Real.exp (-(2 * Real.pi / t)))) := by ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_right h8 hfac
    exact hgoal



/-- The `M`-bound with the last exponential pulled out of the denominator: the form consumed by
the bad-case estimate. -/
private lemma KfunClear_le_of_ball_exp (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24)
    (cΔ : ℝ) (hcΔ : 0 < cΔ)
    (hΔ₀ : ∀ z : ℍ, 1 / 3 ≤ z.im → cΔ * ‖Work.Kernels.qParamFun z‖ ≤ ‖Work.Kernels.DeltaFun z‖) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ (t : ℝ) (ht : 0 < t) (htinv : 1 ≤ t⁻¹)
        (h32 : (3 / 2 : ℝ) ≤ (99 / 100) * (100 / 101) ^ 2 * t⁻¹) (w_m : ℍ),
        (ModularGroup.S • w_m).im = t⁻¹ →
        Work.Kernels.KfunClear ℓ d w_m (Work.Kernels.imagAxis t ht) = 0 →
        ∀ u : ℍ, ‖(u : ℂ) - (w_m : ℂ)‖ ≤ w_m.im / 100 →
          ‖Work.Kernels.KfunClear ℓ d u (Work.Kernels.imagAxis t ht)‖
            ≤ C * (2 * Work.Kernels.scale w_m) ^ N * t ^ ((d : ℤ) / 2 - 4)
              * Real.exp (-(Real.pi / t))
              * (‖(w_m : ℂ)‖ ^ (-(12 : ℤ)) * Real.exp (-(Real.pi * (9 / 5) / t)))
              * (2 * t ^ (-(12 : ℤ)) * Real.exp (-(2 * Real.pi / t)))
                  ^ (if d = 8 then 1 else 2)
              * Real.exp (2 * Real.pi / t)
              / cΔ := by
  obtain ⟨CM, NM, hCM, hNM, hMb⟩ := KfunClear_le_of_ball ℓ d hd cΔ hcΔ hΔ₀
  refine ⟨CM, NM, hCM, hNM, fun t ht htinv h32 w_m hwm hzero u hu => ?_⟩
  have h := hMb t ht htinv h32 w_m hwm hzero u hu
  refine le_trans h ?_
  rw [div_eq_mul_inv, _root_.mul_inv_rev, ← Real.exp_neg (-(2 * Real.pi / t)), neg_neg,
    div_eq_mul_inv]
  ring_nf
  linarith

set_option maxHeartbeats 8000000 in
/-- **The bad case**: `‖sin (π ((S • w) - i/t))‖ < 1/1000`, so that `w` lies near a cusp point at
which the cleared kernel vanishes.  The one-zero (Schwarz) estimate produces the linear vanishing
that cancels the divisor. -/
private lemma bad_case_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ (w : ℍ) (t : ℝ) (ht : 0 < t),
        w ∈ KEpsilon → t ≤ 1 →
        Work.Kernels.jInvariantFun w ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) →
        (∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
          ‖(w : ℂ) - (((γ • Work.Kernels.imagAxis t ht : ℍ)) : ℂ)‖ < (1 / 2) * t ^ 2) →
        ‖Complex.sin (Real.pi * (((ModularGroup.S • w : ℍ) : ℂ)
          - ((Work.Kernels.imagAxis (t⁻¹) (inv_pos.mpr ht) : ℍ) : ℂ)))‖ < 1 / 1000 →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t‖
          ≤ C * (Work.Kernels.scale w) ^ N := by
  obtain ⟨cΔ, hcΔ, hΔ₀⟩ := Work.Asymptotics.delta_lower_third
  obtain ⟨cJ, hcJ, hJL⟩ := jDiff_lower_E
  obtain ⟨CM, NM, hCM, hNM, hMb2⟩ := KfunClear_le_of_ball_exp ℓ d hd cΔ hcΔ hΔ₀
  refine ⟨1000 * CM * 24 ^ NM * 3 ^ 14 / (cJ * (min cΔ 1) ^ 4), 2 * NM + 14,
    div_pos (mul_pos (mul_pos (mul_pos (by norm_num) hCM)
      (Real.rpow_pos_of_pos (by norm_num) NM)) (pow_pos (by norm_num) 14))
      (mul_pos hcJ (pow_pos (lt_min hcΔ zero_lt_one) 4)),
    by positivity, ?_⟩
  intro w t ht hwE ht1 hne hnear hbad
  -- ## geometry
  obtain ⟨m, hmdist⟩ := exists_near_shift (by norm_num : (0 : ℝ) < 1 / 1000) hbad
  have hS_it : ModularGroup.S • Work.Kernels.imagAxis t ht
      = Work.Kernels.imagAxis (t⁻¹) (inv_pos.mpr ht) := by
    rw [← S_smul_imagAxis_inv ht, S_smul_S_smul]
  set z₀ : ℍ := ModularGroup.S • Work.Kernels.imagAxis t ht with hz₀
  set z_m : ℍ := (m : ℝ) +ᵥ z₀ with hz_m
  set w_m : ℍ := ModularGroup.S • z_m with hw_m
  have hS_wm : ModularGroup.S • w_m = z_m := by rw [hw_m, S_smul_S_smul]
  have hzm_im : z_m.im = t⁻¹ := by
    rw [hz_m, UpperHalfPlane.vadd_im, hz₀, S_im_imagAxis ht]
  have hwm_im : (ModularGroup.S • w_m).im = t⁻¹ := by rw [hS_wm, hzm_im]
  have hzero : Work.Kernels.KfunClear ℓ d w_m (Work.Kernels.imagAxis t ht) = 0 := by
    rw [hw_m, hz_m]
    exact KfunClear_cuspParabolic_vanishing ℓ d hd m (Work.Kernels.imagAxis t ht)
  set ζ : ℝ := (1 / 1000) * (1 / 2 + 1 / Real.pi) with hζdef
  have hζpos : 0 < ζ := by rw [hζdef]; positivity
  have hpi2 : (2 : ℝ) ≤ Real.pi := le_of_lt (lt_trans (by norm_num) Real.pi_gt_three)
  have hone_pi : 1 / Real.pi ≤ 1 / 2 := by
    rw [div_le_div_iff₀ Real.pi_pos (by norm_num)]
    linarith [hpi2]
  have hζ13 : ζ ≤ 1 / 3 := by rw [hζdef]; nlinarith [hone_pi]
  have hζ1000 : ζ ≤ 1 / 1000 := by rw [hζdef]; nlinarith [hone_pi]
  have hzeq : (z_m : ℂ)
      = ((Work.Kernels.imagAxis (t⁻¹) (inv_pos.mpr ht) : ℍ) : ℂ) + (m : ℂ) := by
    have h1 : (z_m : ℂ) = ((m : ℝ) : ℂ) + (z₀ : ℂ) := by
      rw [hz_m, UpperHalfPlane.coe_vadd]
    have h2 : (z₀ : ℂ) = ((Work.Kernels.imagAxis (t⁻¹) (inv_pos.mpr ht) : ℍ) : ℂ) := by
      rw [hz₀]
      exact congrArg (fun z : ℍ => ((z : ℂ))) hS_it
    rw [h1, h2]
    push_cast
    ring
  have hzdist : ‖((ModularGroup.S • w : ℍ) : ℂ) - (z_m : ℂ)‖ ≤ ζ := by
    have h := hmdist
    rw [← hzeq] at h
    rw [hζdef]
    exact h
  have hσim_ge : (2 : ℝ) ≤ (ModularGroup.S • w).im := hwE.2
  have hσim_le : (ModularGroup.S • w).im ≤ t⁻¹ + ζ := by
    have h1 : (((ModularGroup.S • w : ℍ) : ℂ) - (z_m : ℂ)).im
        = (ModularGroup.S • w).im - z_m.im := by simp
    have h2 : (((ModularGroup.S • w : ℍ) : ℂ) - (z_m : ℂ)).im
        ≤ ‖((ModularGroup.S • w : ℍ) : ℂ) - (z_m : ℂ)‖ :=
      le_trans (le_abs_self _) (Complex.abs_im_le_norm _)
    rw [h1, hzm_im] at h2
    linarith [h2, hzdist]
  have htinv : (1 : ℝ) ≤ t⁻¹ := by linarith [hσim_ge, hσim_le, hζ13]
  have ht53 : (5 / 3 : ℝ) ≤ t⁻¹ := by linarith [hσim_ge, hσim_le, hζ13]
  have h32 : (3 / 2 : ℝ) ≤ (99 / 100) * (100 / 101) ^ 2 * t⁻¹ := by
    have hκ : (9 / 10 : ℝ) ≤ (99 / 100) * (100 / 101) ^ 2 := by norm_num
    calc (3 / 2 : ℝ) = (9 / 10) * (5 / 3) := by norm_num
      _ ≤ (99 / 100) * (100 / 101) ^ 2 * t⁻¹ :=
          mul_le_mul hκ ht53 (by norm_num) (by norm_num)
  set s : ℝ := Work.Kernels.scale w with hsdef
  have hs1 : (1 : ℝ) ≤ s := by rw [hsdef]; exact Work.Kernels.one_le_scale w
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs1
  have hwinv_le_s : (w.im)⁻¹ ≤ s := by
    rw [hsdef, Work.Kernels.scale]; linarith [norm_nonneg (w : ℂ)]
  have hwim_le : w.im ≤ (3 / 2) * t := by
    have h := im_le_of_near_diag ht ht1 (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1 / 2) hwE hnear
    linarith [h]
  have ht_low : t⁻¹ ≤ (3 / 2) * s := by
    have h1 : t⁻¹ ≤ 3 / (2 * w.im) := by
      rw [inv_eq_one_div, div_le_div_iff₀ ht (by positivity)]
      linarith [hwim_le]
    have h2 : 3 / (2 * w.im) = (3 / 2) * (1 / w.im) := by ring
    have h3 : 1 / w.im ≤ s := by rw [one_div]; exact hwinv_le_s
    linarith [h1, h2, h3]
  have hwnorm_le : ‖(w : ℂ)‖ ≤ 1 / 2 := Work.Asymptotics.E_norm_le_half hwE
  have hwnorm_pos : 0 < ‖(w : ℂ)‖ := norm_pos_iff.mpr w.ne_zero
  have hσnorm : ‖((ModularGroup.S • w : ℍ) : ℂ)‖ = (‖(w : ℂ)‖)⁻¹ := by
    rw [Work.Kernels.S_smul_coe, norm_neg, norm_inv]
  have hσsq : ‖((ModularGroup.S • w : ℍ) : ℂ)‖ ^ 2 = (ModularGroup.S • w).im / w.im := by
    rw [hσnorm, Work.Asymptotics.EReg_S_im]
    field_simp
  have hσnorm_le : ‖((ModularGroup.S • w : ℍ) : ℂ)‖ ≤ 2 * s := by
    have h1 : ‖((ModularGroup.S • w : ℍ) : ℂ)‖ ^ 2 ≤ (2 * s) ^ 2 := by
      rw [hσsq, div_le_iff₀ w.im_pos]
      have h2 : (ModularGroup.S • w).im ≤ (3 / 2) * s + ζ := by linarith [hσim_le, ht_low]
      have h3 : (3 / 2) * s + ζ ≤ (5 / 2) * s := by linarith [hζ13, hs1]
      have h4 : (1 : ℝ) ≤ s * w.im := by
        have h5 : (w.im)⁻¹ * w.im = 1 := inv_mul_cancel₀ w.im_pos.ne'
        nlinarith [hwinv_le_s, h5, w.im_pos, hspos]
      nlinarith [h2, h3, h4, w.im_pos, hspos]
    nlinarith [h1, norm_nonneg ((ModularGroup.S • w : ℍ) : ℂ), hspos]
  have hzm_norm_le : ‖(z_m : ℂ)‖ ≤ 3 * s := by
    have h2 : ‖(z_m : ℂ)‖
        ≤ ‖((ModularGroup.S • w : ℍ) : ℂ)‖ + ‖((ModularGroup.S • w : ℍ) : ℂ) - (z_m : ℂ)‖ := by
      have h5 : ((ModularGroup.S • w : ℍ) : ℂ) - (((ModularGroup.S • w : ℍ) : ℂ) - (z_m : ℂ))
          = (z_m : ℂ) := by ring
      calc ‖(z_m : ℂ)‖
          = ‖((ModularGroup.S • w : ℍ) : ℂ) - (((ModularGroup.S • w : ℍ) : ℂ) - (z_m : ℂ))‖ := by
            rw [h5]
        _ ≤ ‖((ModularGroup.S • w : ℍ) : ℂ)‖
              + ‖((ModularGroup.S • w : ℍ) : ℂ) - (z_m : ℂ)‖ := norm_sub_le _ _
    linarith [h2, hzdist, hσnorm_le, hζ13, hs1]
  have hzm_norm_ge : (1 : ℝ) ≤ ‖(z_m : ℂ)‖ := by
    have h2 : ‖((ModularGroup.S • w : ℍ) : ℂ)‖ - ‖(z_m : ℂ)‖ ≤ ζ := by
      have h3 : |‖((ModularGroup.S • w : ℍ) : ℂ)‖ - ‖(z_m : ℂ)‖|
          ≤ ‖((ModularGroup.S • w : ℍ) : ℂ) - (z_m : ℂ)‖ :=
        abs_norm_sub_norm_le _ _
      have h4 := (abs_le.mp (le_trans h3 hzdist)).2
      linarith [h4]
    have h5 : (2 : ℝ) ≤ ‖((ModularGroup.S • w : ℍ) : ℂ)‖ := by
      rw [hσnorm, inv_eq_one_div]
      rw [le_div_iff₀ hwnorm_pos]
      linarith [hwnorm_le]
    linarith [h2, h5, hζ13]
  have hwm_norm_eq : ‖(w_m : ℂ)‖ = (‖(z_m : ℂ)‖)⁻¹ := by
    have h := Work.Kernels.S_smul_coe w_m
    rw [hS_wm] at h
    have h2 : ‖(z_m : ℂ)‖ = (‖(w_m : ℂ)‖)⁻¹ := by rw [h, norm_neg, norm_inv]
    rw [h2, inv_inv]
  have hwm_le_one : ‖(w_m : ℂ)‖ ≤ 1 := by
    rw [hwm_norm_eq]
    exact inv_le_one_of_one_le₀ hzm_norm_ge
  have hwm_le_s : ‖(w_m : ℂ)‖ ≤ s := le_trans hwm_le_one hs1
  have hwml : ‖(w_m : ℂ)‖ ^ 2 = t * w_m.im := by
    have h := Work.Asymptotics.EReg_S_im w_m
    rw [hS_wm, hzm_im] at h
    have hn2 : ‖(w_m : ℂ)‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr w_m.ne_zero)
    have h2 : t⁻¹ * ‖(w_m : ℂ)‖ ^ 2 = w_m.im := by
      rw [h, div_mul_cancel₀ _ hn2]
    calc ‖(w_m : ℂ)‖ ^ 2 = t * (t⁻¹ * ‖(w_m : ℂ)‖ ^ 2) := by
          rw [← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul]
      _ = t * w_m.im := by rw [h2]
  have hwmim_eq : w_m.im = ‖(w_m : ℂ)‖ ^ 2 / t := by
    rw [hwml]
    field_simp
  have hratio : ‖(w : ℂ) - (w_m : ℂ)‖
      = ‖((ModularGroup.S • w : ℍ) : ℂ) - (z_m : ℂ)‖ * ‖(w : ℂ)‖ * ‖(w_m : ℂ)‖ := by
    have h := Work.Asymptotics.KL.norm_S_sub_S (ModularGroup.S • w) z_m
    rw [S_smul_S_smul, ← hw_m] at h
    have hwne : (‖(w : ℂ)‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr w.ne_zero
    have hzme : (‖(z_m : ℂ)‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr z_m.ne_zero
    rw [h, hσnorm, hwm_norm_eq]
    field_simp
  have hwzm : ‖(w : ℂ)‖ * ‖(z_m : ℂ)‖ ≤ 2 := by
    have h1 : ‖(z_m : ℂ)‖ ≤ ‖((ModularGroup.S • w : ℍ) : ℂ)‖ + ζ := by
      have h2 : ‖(z_m : ℂ)‖
          ≤ ‖((ModularGroup.S • w : ℍ) : ℂ)‖ + ‖((ModularGroup.S • w : ℍ) : ℂ) - (z_m : ℂ)‖ := by
        have h5 : ((ModularGroup.S • w : ℍ) : ℂ) - (((ModularGroup.S • w : ℍ) : ℂ) - (z_m : ℂ))
            = (z_m : ℂ) := by ring
        calc ‖(z_m : ℂ)‖
            = ‖((ModularGroup.S • w : ℍ) : ℂ) - (((ModularGroup.S • w : ℍ) : ℂ) - (z_m : ℂ))‖ := by
              rw [h5]
          _ ≤ ‖((ModularGroup.S • w : ℍ) : ℂ)‖
                + ‖((ModularGroup.S • w : ℍ) : ℂ) - (z_m : ℂ)‖ := norm_sub_le _ _
      linarith [h2, hzdist]
    have h2 : ‖(w : ℂ)‖ * ‖((ModularGroup.S • w : ℍ) : ℂ)‖ = 1 := by
      rw [hσnorm, mul_inv_cancel₀ (norm_ne_zero_iff.mpr w.ne_zero)]
    nlinarith [h1, h2, hwnorm_le, hζ13, norm_nonneg (w : ℂ), norm_nonneg (z_m : ℂ)]
  have hww : ‖(w : ℂ) - (w_m : ℂ)‖ < w_m.im / 200 := by
    have hkey : ‖((ModularGroup.S • w : ℍ) : ℂ) - (z_m : ℂ)‖ * (‖(w : ℂ)‖ * ‖(z_m : ℂ)‖)
        * (200 * t) < 1 := by
      have h1 : ‖((ModularGroup.S • w : ℍ) : ℂ) - (z_m : ℂ)‖ * (‖(w : ℂ)‖ * ‖(z_m : ℂ)‖)
          ≤ ζ * 2 :=
        mul_le_mul hzdist hwzm (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hζpos.le
      have h2 : ‖((ModularGroup.S • w : ℍ) : ℂ) - (z_m : ℂ)‖ * (‖(w : ℂ)‖ * ‖(z_m : ℂ)‖)
          * (200 * t) ≤ ζ * 2 * (200 * t) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
      have h3 : ζ * 2 * (200 * t) < 1 := by nlinarith [hζ1000, ht1, ht.le, hζpos]
      linarith [h2, h3]
    have hZ : 0 < ‖(z_m : ℂ)‖ := norm_pos_iff.mpr z_m.ne_zero
    have hgoal : ‖((ModularGroup.S • w : ℍ) : ℂ) - (z_m : ℂ)‖ * ‖(w : ℂ)‖ * (‖(z_m : ℂ)‖)⁻¹
        < 1 / ((‖(z_m : ℂ)‖) ^ 2 * t * 200) := by
      rw [lt_div_iff₀ (by positivity : (0 : ℝ) < (‖(z_m : ℂ)‖) ^ 2 * t * 200)]
      have heq : ‖((ModularGroup.S • w : ℍ) : ℂ) - (z_m : ℂ)‖ * ‖(w : ℂ)‖ * (‖(z_m : ℂ)‖)⁻¹
            * ((‖(z_m : ℂ)‖) ^ 2 * t * 200)
          = ‖((ModularGroup.S • w : ℍ) : ℂ) - (z_m : ℂ)‖ * (‖(w : ℂ)‖ * ‖(z_m : ℂ)‖)
            * (200 * t) := by
        field_simp
      rw [heq]
      exact hkey
    rw [hratio, hwmim_eq, hwm_norm_eq,
      show ((‖(z_m : ℂ)‖)⁻¹) ^ 2 / t / 200 = 1 / ((‖(z_m : ℂ)‖) ^ 2 * t * 200) by
        field_simp]
    exact hgoal

  -- ## the `M`-bound and the one-zero estimate
  set Mn : ℝ := CM * (2 * Work.Kernels.scale w_m) ^ NM * t ^ ((d : ℤ) / 2 - 4)
      * Real.exp (-(Real.pi / t))
      * (‖(w_m : ℂ)‖ ^ (-(12 : ℤ)) * Real.exp (-(Real.pi * (9 / 5) / t)))
      * (2 * t ^ (-(12 : ℤ)) * Real.exp (-(2 * Real.pi / t))) ^ (if d = 8 then 1 else 2)
      * Real.exp (2 * Real.pi / t) / cΔ with hMndef
  have hbd2 : ∀ u : ℍ, ‖(u : ℂ) - (w_m : ℂ)‖ ≤ w_m.im / 100 →
      ‖Work.Kernels.KfunClear ℓ d u (Work.Kernels.imagAxis t ht)‖ ≤ Mn := by
    intro u hu
    rw [hMndef]
    exact hMb2 t ht htinv h32 w_m hwm_im hzero u hu
  clear hMb2
  have hr0 : (0 : ℝ) < w_m.im / 100 := by linarith [w_m.im_pos]
  have hr : w_m.im / 100 < w_m.im := by linarith [w_m.im_pos]
  have hww' : ‖(w : ℂ) - (w_m : ℂ)‖ < w_m.im / 100 / 2 := by
    rw [show w_m.im / 100 / 2 = w_m.im / 200 by ring]
    exact hww
  have hone := Work.Asymptotics.KL.one_zero_apply
    (f := fun τ : ℍ => Work.Kernels.KfunClear ℓ d τ (Work.Kernels.imagAxis t ht))
    (Work.Asymptotics.KL.mdifferentiable_KfunClear_fst ℓ d hd (Work.Kernels.imagAxis t ht))
    (c := w_m) (r := w_m.im / 100) (M := Mn) hr0 hr hbd2
    (w₀ := w_m) (by rw [sub_self, norm_zero]; linarith [w_m.im_pos]) hzero w hww'
  set a : ℝ := ‖(w : ℂ) - (w_m : ℂ)‖ with hadef
  set Dσ : ℝ := ‖((ModularGroup.S • w : ℍ) : ℂ) - (z_m : ℂ)‖ with hDσdef
  have hDσ_nn : (0 : ℝ) ≤ Dσ := by rw [hDσdef]; exact norm_nonneg _
  set B : ℝ := ‖(w : ℂ)‖ * ‖(w_m : ℂ)‖ with hBdef
  set D1 : ℝ := ‖Work.Kernels.DeltaFun w‖ with hD1def
  set D2 : ℝ := ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ with hD2def
  set Jj : ℝ := ‖Work.Kernels.jInvariantFun w
      - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖ with hJdef
  set Lw : ℝ := ‖(w : ℂ)‖ ^ (-(12 : ℤ))
      * Real.exp (-(2 * Real.pi * (ModularGroup.S • w).im)) with hLwdef
  set Lt : ℝ := t ^ (-(12 : ℤ)) * Real.exp (-(2 * Real.pi / t)) with hLtdef
  set Kk : ℝ := 4 * cJ * Real.exp (Real.pi * ((ModularGroup.S • w).im + t⁻¹)) with hKdef
  set DD : ℝ := (cΔ * Lw) * (cΔ * Lt) ^ (if d = 8 then 1 else 2) * (Kk * Dσ) with hDDdef
  have hnum : ‖Work.Kernels.KfunClear ℓ d w (Work.Kernels.imagAxis t ht)‖
      ≤ (200 * Mn * t / ‖(w_m : ℂ)‖ ^ 2) * a := by
    have h2 : 2 * Mn / (w_m.im / 100) = 200 * Mn * t / ‖(w_m : ℂ)‖ ^ 2 := by
      rw [hwmim_eq]
      field_simp
      ring
    rw [h2] at hone
    exact hone
  have hLwpos : 0 < Lw := by
    rw [hLwdef]
    exact mul_pos (zpow_pos (norm_pos_iff.mpr w.ne_zero) _) (Real.exp_pos _)
  have hLtpos : 0 < Lt := by
    rw [hLtdef]
    exact mul_pos (zpow_pos ht _) (Real.exp_pos _)
  have hKkpos : 0 < Kk := by
    rw [hKdef]; positivity
  have hD1low : cΔ * Lw ≤ D1 := by
    rw [hD1def, hLwdef]
    exact norm_DeltaFun_ge_of_im hcΔ hΔ₀ (u := w) (by linarith [hσim_ge])
  have hD2low : cΔ * Lt ≤ D2 := by
    rw [hD2def, hLtdef]
    have h := norm_DeltaFun_ge_of_im hcΔ hΔ₀ (u := Work.Kernels.imagAxis t ht)
      (by rw [S_im_imagAxis ht]; linarith [htinv])
    rwa [norm_imagAxis ht, S_im_imagAxis ht] at h
  have harg : (((ModularGroup.S • w : ℍ) : ℂ)
        - ((Work.Kernels.imagAxis (t⁻¹) (inv_pos.mpr ht) : ℍ) : ℂ)) - (m : ℂ)
      = ((ModularGroup.S • w : ℍ) : ℂ) - (z_m : ℂ) := by
    rw [hzeq]
    ring
  have hle3 : ‖(((ModularGroup.S • w : ℍ) : ℂ)
        - ((Work.Kernels.imagAxis (t⁻¹) (inv_pos.mpr ht) : ℍ) : ℂ)) - (m : ℂ)‖ ≤ 1 / 3 := by
    rw [harg, ← hDσdef]
    linarith [hzdist, hζ13]
  have hJlow : Kk * Dσ ≤ Jj := by
    rw [hKdef, hDσdef, hJdef]
    have h1 := hJL w t ht hwE ht1
    rw [one_sub_Eun_eq ht] at h1
    have hsin := two_mul_norm_le_norm_sin_pi_int_add m (w := (((ModularGroup.S • w : ℍ) : ℂ)
        - ((Work.Kernels.imagAxis (t⁻¹) (inv_pos.mpr ht) : ℍ) : ℂ)) - (m : ℂ)) hle3
    rw [show (m : ℂ) + ((((ModularGroup.S • w : ℍ) : ℂ)
          - ((Work.Kernels.imagAxis (t⁻¹) (inv_pos.mpr ht) : ℍ) : ℂ)) - (m : ℂ))
        = ((ModularGroup.S • w : ℍ) : ℂ)
          - ((Work.Kernels.imagAxis (t⁻¹) (inv_pos.mpr ht) : ℍ) : ℂ) by ring] at hsin
    have hsin' : 2 * ‖((ModularGroup.S • w : ℍ) : ℂ) - (z_m : ℂ)‖
        ≤ ‖Complex.sin (Real.pi * (((ModularGroup.S • w : ℍ) : ℂ)
          - ((Work.Kernels.imagAxis (t⁻¹) (inv_pos.mpr ht) : ℍ) : ℂ)))‖ := by
      rw [← harg]
      exact hsin
    have hee : Real.exp (2 * Real.pi * (ModularGroup.S • w).im)
        * Real.exp (Real.pi * (t⁻¹ - (ModularGroup.S • w).im))
        = Real.exp (Real.pi * ((ModularGroup.S • w).im + t⁻¹)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h3 : Real.exp (2 * Real.pi * (ModularGroup.S • w).im)
        * (2 * Real.exp (Real.pi * (t⁻¹ - (ModularGroup.S • w).im))
          * ‖Complex.sin (Real.pi * (((ModularGroup.S • w : ℍ) : ℂ)
            - ((Work.Kernels.imagAxis (t⁻¹) (inv_pos.mpr ht) : ℍ) : ℂ)))‖)
        = 2 * Real.exp (Real.pi * ((ModularGroup.S • w).im + t⁻¹))
          * ‖Complex.sin (Real.pi * (((ModularGroup.S • w : ℍ) : ℂ)
            - ((Work.Kernels.imagAxis (t⁻¹) (inv_pos.mpr ht) : ℍ) : ℂ)))‖ := by
      rw [← hee]
      ring
    rw [h3] at h1
    have h4 : 2 * Real.exp (Real.pi * ((ModularGroup.S • w).im + t⁻¹))
          * (2 * ‖((ModularGroup.S • w : ℍ) : ℂ) - (z_m : ℂ)‖)
        ≤ 2 * Real.exp (Real.pi * ((ModularGroup.S • w).im + t⁻¹))
          * ‖Complex.sin (Real.pi * (((ModularGroup.S • w : ℍ) : ℂ)
            - ((Work.Kernels.imagAxis (t⁻¹) (inv_pos.mpr ht) : ℍ) : ℂ)))‖ :=
      mul_le_mul_of_nonneg_left hsin' (by positivity)
    have h5 : cJ * (2 * Real.exp (Real.pi * ((ModularGroup.S • w).im + t⁻¹))
          * (2 * ‖((ModularGroup.S • w : ℍ) : ℂ) - (z_m : ℂ)‖)) ≤ Jj :=
      le_trans (mul_le_mul_of_nonneg_left h4 hcJ.le) h1
    linarith [h5]
  have hden : DD ≤ D1 * D2 ^ (if d = 8 then 1 else 2) * Jj := by
    rw [hDDdef]
    clear hΔ₀ hJL
    have hA : (0 : ℝ) ≤ (cΔ * Lt) ^ (if d = 8 then 1 else 2) :=
      pow_nonneg (le_of_lt (mul_pos hcΔ hLtpos)) _
    have hB : (0 : ℝ) ≤ D1 := by rw [hD1def]; exact norm_nonneg _
    have h1a : (cΔ * Lt) ^ (if d = 8 then 1 else 2) ≤ D2 ^ (if d = 8 then 1 else 2) := by
      apply pow_le_pow_left₀ (le_of_lt (mul_pos hcΔ hLtpos)) hD2low
    have h1 : (cΔ * Lw) * (cΔ * Lt) ^ (if d = 8 then 1 else 2)
        ≤ D1 * D2 ^ (if d = 8 then 1 else 2) :=
      mul_le_mul hD1low h1a hA hB
    have hC : (0 : ℝ) ≤ Kk * Dσ := mul_nonneg hKkpos.le hDσ_nn
    have hD : (0 : ℝ) ≤ D1 * D2 ^ (if d = 8 then 1 else 2) :=
      mul_nonneg hB (pow_nonneg (by rw [hD2def]; exact norm_nonneg _) _)
    exact mul_le_mul h1 hJlow hC hD
  have hzeq2 : a = Dσ * B := by
    rw [hratio, hBdef]
    ring
  have hKax : ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t‖
      = ‖Work.Kernels.KfunClear ℓ d w (Work.Kernels.imagAxis t ht)‖
        / (D1 * D2 ^ (if d = 8 then 1 else 2) * Jj) := by
    rw [Work.Kernels.Kaxis, dif_pos ht,
      Work.Asymptotics.KL.Kfun_eq_KfunClear_div ℓ d hd w (Work.Kernels.imagAxis t ht) hne,
      norm_div, Work.Asymptotics.KL.norm_growthPrefactor, ← hD1def, ← hD2def, ← hJdef]
  have hDpos : 0 < D1 * D2 ^ (if d = 8 then 1 else 2) * Jj := by
    rw [hD1def, hD2def, hJdef]
    exact mul_pos (mul_pos (norm_pos_iff.mpr (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero _))
      (pow_pos (norm_pos_iff.mpr (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero _)) _))
      (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
  have hDden : 0 < (cΔ * Lw) * (cΔ * Lt) ^ (if d = 8 then 1 else 2) * Kk :=
    mul_pos (mul_pos (mul_pos hcΔ hLwpos) (pow_pos (mul_pos hcΔ hLtpos) _)) hKkpos
  by_cases hDσ0 : Dσ = 0
  · have ha0 : a = 0 := by rw [hzeq2, hDσ0, zero_mul]
    rw [hKax]
    have hKm : ‖Work.Kernels.KfunClear ℓ d w (Work.Kernels.imagAxis t ht)‖ = 0 := by
      have h := hnum
      rw [ha0, mul_zero] at h
      exact le_antisymm h (norm_nonneg _)
    rw [hKm, zero_div]
    exact mul_nonneg (le_of_lt (div_pos (mul_pos (mul_pos (mul_pos (by norm_num) hCM)
      (Real.rpow_pos_of_pos (by norm_num) NM)) (pow_pos (by norm_num) 14))
      (mul_pos hcJ (pow_pos (lt_min hcΔ zero_lt_one) 4))))
      (Real.rpow_nonneg hspos.le _)
  · have hDσpos : 0 < Dσ := lt_of_le_of_ne hDσ_nn (Ne.symm hDσ0)
    have hDDpos : 0 < DD := by
      rw [hDDdef]
      exact mul_pos (mul_pos (mul_pos hcΔ hLwpos)
        (pow_pos (mul_pos hcΔ hLtpos) _)) (mul_pos hKkpos hDσpos)
    have hcore : (200 * Mn * t / ‖(w_m : ℂ)‖ ^ 2) * B
        ≤ (1000 * CM * 24 ^ NM * 3 ^ 14 / (cJ * (min cΔ 1) ^ 4)) * s ^ (2 * NM + 14)
          * ((cΔ * Lw) * (cΔ * Lt) ^ (if d = 8 then 1 else 2) * Kk) := by
      have hratio2 : ((200 * Mn * t / ‖(w_m : ℂ)‖ ^ 2) * B)
            / ((cΔ * Lw) * (cΔ * Lt) ^ (if d = 8 then 1 else 2) * Kk)
          = (200 * CM * 2 ^ (if d = 8 then 1 else 2)
              / (4 * cJ * cΔ ^ 2 * cΔ ^ (if d = 8 then 1 else 2)))
            * ((2 * Work.Kernels.scale w_m) ^ NM)
            * (t ^ ((d : ℤ) / 2 - 4) * t)
            * ((‖(w_m : ℂ)‖ ^ (-(12 : ℤ)) * ‖(w_m : ℂ)‖ * (‖(w_m : ℂ)‖ ^ 2)⁻¹)
                * ((‖(w : ℂ)‖ ^ (-(12 : ℤ)))⁻¹ * ‖(w : ℂ)‖))
            * (Real.exp (-(Real.pi / t)) * Real.exp (-(Real.pi * (9 / 5) / t))
                * Real.exp (2 * Real.pi / t)
                * (Real.exp (-(2 * Real.pi * (ModularGroup.S • w).im)))⁻¹
                * (Real.exp (Real.pi * ((ModularGroup.S • w).im + t⁻¹)))⁻¹) := by
        rw [hMndef, hBdef, hLwdef, hLtdef, hKdef]
        rw [mul_pow, mul_pow]
        field_simp
        ring
      have hkey2 : ((200 * CM * 2 ^ (if d = 8 then 1 else 2)
              / (4 * cJ * cΔ ^ 2 * cΔ ^ (if d = 8 then 1 else 2)))
            * ((2 * Work.Kernels.scale w_m) ^ NM)
            * (t ^ ((d : ℤ) / 2 - 4) * t)
            * ((‖(w_m : ℂ)‖ ^ (-(12 : ℤ)) * ‖(w_m : ℂ)‖ * (‖(w_m : ℂ)‖ ^ 2)⁻¹)
                * ((‖(w : ℂ)‖ ^ (-(12 : ℤ)))⁻¹ * ‖(w : ℂ)‖))
            * (Real.exp (-(Real.pi / t)) * Real.exp (-(Real.pi * (9 / 5) / t))
                * Real.exp (2 * Real.pi / t)
                * (Real.exp (-(2 * Real.pi * (ModularGroup.S • w).im)))⁻¹
                * (Real.exp (Real.pi * ((ModularGroup.S • w).im + t⁻¹)))⁻¹))
          ≤ (1000 * CM * 24 ^ NM * 3 ^ 14 / (cJ * (min cΔ 1) ^ 4)) * s ^ (2 * NM + 14) := by
        have hmc : 0 < min cΔ 1 := lt_min hcΔ zero_lt_one
        have hPw : 2 ^ (if d = 8 then 1 else 2) ≤ (4 : ℝ) := by
          rcases hd with h | h <;> rw [h] <;> norm_num
        have hQe : (min cΔ 1) ^ 4 ≤ cΔ ^ 2 * cΔ ^ (if d = 8 then 1 else 2) := by
          rw [← pow_add]
          have h1 : (min cΔ 1) ^ 4 ≤ (min cΔ 1) ^ (2 + (if d = 8 then 1 else 2)) := by
            refine pow_le_pow_of_le_one (le_of_lt hmc) (min_le_right _ _) ?_
            rcases hd with h | h <;> rw [h] <;> norm_num
          have h2 : (min cΔ 1) ^ (2 + (if d = 8 then 1 else 2))
              ≤ cΔ ^ (2 + (if d = 8 then 1 else 2)) :=
            pow_le_pow_left₀ (le_of_lt hmc) (min_le_left _ _) _
          linarith [h1, h2]
        have hP1 : 200 * CM * 2 ^ (if d = 8 then 1 else 2)
              / (4 * cJ * cΔ ^ 2 * cΔ ^ (if d = 8 then 1 else 2))
            ≤ 200 * CM * 4 / (4 * cJ * (min cΔ 1) ^ 4) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have h := mul_le_mul hPw hQe (by positivity) (by norm_num)
          have h2 := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 200 * CM * (4 * cJ))
          linarith [h2]
        have hYge : ((3 : ℝ) * s)⁻¹ ≤ ‖(w_m : ℂ)‖ := by
          rw [hwm_norm_eq]
          exact (inv_le_inv₀ (by positivity) (norm_pos_iff.mpr z_m.ne_zero)).mpr hzm_norm_le
        have h2inv : (‖(w_m : ℂ)‖ ^ 2)⁻¹ ≤ 9 * s ^ 2 := by
          have h4 : ((3 * s)⁻¹) ^ 2 ≤ ‖(w_m : ℂ)‖ ^ 2 :=
            pow_le_pow_left₀ (by positivity) hYge 2
          have h5 : (‖(w_m : ℂ)‖ ^ 2)⁻¹ ≤ (((3 * s)⁻¹) ^ 2)⁻¹ :=
            (inv_le_inv₀ (pow_pos (norm_pos_iff.mpr w_m.ne_zero) 2)
              (pow_pos (by positivity) 2)).mpr h4
          have h6 : (((3 * s)⁻¹) ^ 2)⁻¹ = 9 * s ^ 2 := by
            rw [inv_pow, inv_inv, mul_pow]
            norm_num
          linarith [h5, h6]
        have hsw : 2 * Work.Kernels.scale w_m ≤ 24 * s ^ 2 := by
          have h2 : (w_m.im)⁻¹ ≤ 9 * s ^ 2 := by
            have h3 : (0 : ℝ) ≤ (‖(w_m : ℂ)‖ ^ 2)⁻¹ :=
              inv_nonneg.mpr (by positivity)
            rw [hwmim_eq, div_eq_mul_inv, _root_.mul_inv_rev, inv_inv]
            exact le_trans (mul_le_of_le_one_left h3 ht1) h2inv
          rw [Work.Kernels.scale]
          nlinarith [hwm_le_one, h2, hs1, hspos]
        have hV : (2 * Work.Kernels.scale w_m) ^ NM ≤ 24 ^ NM * s ^ (2 * NM) := by
          calc (2 * Work.Kernels.scale w_m) ^ NM ≤ (24 * s ^ 2) ^ NM :=
                Real.rpow_le_rpow
                (le_of_lt (mul_pos (by norm_num) (Work.Kernels.scale_pos w_m))) hsw hNM
            _ = 24 ^ NM * s ^ (2 * NM) := by
                rw [Real.mul_rpow (by norm_num) (by positivity),
                  ← Real.rpow_natCast s 2, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ s)]
                norm_num
        have hT : t ^ ((d : ℤ) / 2 - 4) * t ≤ 1 := by
          have h1 : t ^ ((d : ℤ) / 2 - 4) ≤ 1 := by
            rcases hd with h | h
            · rw [h, show (((8 : ℕ) : ℤ) / 2 - 4) = 0 by omega, zpow_zero]
            · rw [h, show (((24 : ℕ) : ℤ) / 2 - 4) = ((8 : ℕ) : ℤ) by omega]
              have h2 := zpow_le_zpow_left₀ (show (0 : ℤ) ≤ ((8 : ℕ) : ℤ) by norm_num) ht.le ht1
              rw [_root_.one_zpow] at h2
              exact h2
          exact mul_le_one₀ h1 ht.le ht1
        have hW : (‖(w_m : ℂ)‖ ^ (-(12 : ℤ)) * ‖(w_m : ℂ)‖ * (‖(w_m : ℂ)‖ ^ 2)⁻¹)
              * ((‖(w : ℂ)‖ ^ (-(12 : ℤ)))⁻¹ * ‖(w : ℂ)‖) ≤ (3 * s) ^ 14 := by
          have h1 : ‖(w_m : ℂ)‖ ^ (-(12 : ℤ)) ≤ (3 * s) ^ 12 := by
            rw [_root_.zpow_neg, zpow_ofNat]
            have h4 : ((3 * s)⁻¹) ^ 12 ≤ ‖(w_m : ℂ)‖ ^ 12 :=
              pow_le_pow_left₀ (by positivity) hYge 12
            have h5 : (‖(w_m : ℂ)‖ ^ 12)⁻¹ ≤ (((3 * s)⁻¹) ^ 12)⁻¹ :=
              (inv_le_inv₀ (pow_pos (norm_pos_iff.mpr w_m.ne_zero) 12)
                (pow_pos (by positivity) 12)).mpr h4
            rwa [inv_pow, inv_inv] at h5
          have hwone : ‖(w : ℂ)‖ ≤ 1 := le_trans hwnorm_le (by norm_num)
          have h6 : (‖(w : ℂ)‖ ^ (-(12 : ℤ)))⁻¹ ≤ 1 := by
            rw [_root_.zpow_neg, zpow_ofNat, inv_inv]
            exact pow_le_one₀ (norm_nonneg _) hwone
          calc (‖(w_m : ℂ)‖ ^ (-(12 : ℤ)) * ‖(w_m : ℂ)‖ * (‖(w_m : ℂ)‖ ^ 2)⁻¹)
                * ((‖(w : ℂ)‖ ^ (-(12 : ℤ)))⁻¹ * ‖(w : ℂ)‖)
              ≤ ((3 * s) ^ 12 * 1 * (9 * s ^ 2)) * (1 * 1) := by
                refine mul_le_mul (mul_le_mul (mul_le_mul h1 hwm_le_one (norm_nonneg _)
                  (by positivity)) h2inv (by positivity) (by positivity))
                  (mul_le_mul h6 hwone (norm_nonneg _) (by norm_num)) (by positivity)
                  (by positivity)
            _ = (3 * s) ^ 14 := by
                rw [mul_one, mul_one, mul_pow, mul_pow]
                ring
        have hEgrp : Real.exp (-(Real.pi / t)) * Real.exp (-(Real.pi * (9 / 5) / t))
              * Real.exp (2 * Real.pi / t)
              * (Real.exp (-(2 * Real.pi * (ModularGroup.S • w).im)))⁻¹
              * (Real.exp (Real.pi * ((ModularGroup.S • w).im + t⁻¹)))⁻¹ ≤ 1 := by
          rw [← Real.exp_neg (-(2 * Real.pi * (ModularGroup.S • w).im)), neg_neg,
            ← Real.exp_neg (Real.pi * ((ModularGroup.S • w).im + t⁻¹))]
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
          rw [Real.exp_le_one_iff]
          have h1 : (ModularGroup.S • w).im ≤ 9 * t⁻¹ / 5 := by
            have h2 : ζ ≤ 4 * t⁻¹ / 5 := by
              have h3 : ζ ≤ 4 / 5 := le_trans hζ13 (by norm_num)
              have h4a := mul_le_mul_of_nonneg_left htinv (by norm_num : (0 : ℝ) ≤ 4 / 5)
              linarith [h3, h4a]
            have h5 : t⁻¹ + 4 * t⁻¹ / 5 = 9 * t⁻¹ / 5 := by ring
            linarith [hσim_le, h2, h5]
          have h1' : Real.pi * (ModularGroup.S • w).im ≤ Real.pi * (9 * t⁻¹ / 5) :=
            mul_le_mul_of_nonneg_left h1 Real.pi_pos.le
          ring_nf
          linarith [h1']
        have hprod : ((200 * CM * 2 ^ (if d = 8 then 1 else 2)
              / (4 * cJ * cΔ ^ 2 * cΔ ^ (if d = 8 then 1 else 2)))
            * ((2 * Work.Kernels.scale w_m) ^ NM)
            * (t ^ ((d : ℤ) / 2 - 4) * t)
            * ((‖(w_m : ℂ)‖ ^ (-(12 : ℤ)) * ‖(w_m : ℂ)‖ * (‖(w_m : ℂ)‖ ^ 2)⁻¹)
                * ((‖(w : ℂ)‖ ^ (-(12 : ℤ)))⁻¹ * ‖(w : ℂ)‖))
            * (Real.exp (-(Real.pi / t)) * Real.exp (-(Real.pi * (9 / 5) / t))
                * Real.exp (2 * Real.pi / t)
                * (Real.exp (-(2 * Real.pi * (ModularGroup.S • w).im)))⁻¹
                * (Real.exp (Real.pi * ((ModularGroup.S • w).im + t⁻¹)))⁻¹))
            ≤ (200 * CM * 4 / (4 * cJ * (min cΔ 1) ^ 4))
              * (24 ^ NM * s ^ (2 * NM)) * 1 * (3 * s) ^ 14 * 1 := by
          have hP1nn : (0 : ℝ) ≤ 200 * CM * 4 / (4 * cJ * (min cΔ 1) ^ 4) :=
            le_of_lt (div_pos (by positivity) (by positivity))
          have hVnn : (0 : ℝ) ≤ 24 ^ NM * s ^ (2 * NM) :=
            mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hspos.le _)
          have hTnn : (0 : ℝ) ≤ t ^ ((d : ℤ) / 2 - 4) * t :=
            mul_nonneg (zpow_nonneg ht.le _) ht.le
          have hWnn : (0 : ℝ) ≤ (‖(w_m : ℂ)‖ ^ (-(12 : ℤ)) * ‖(w_m : ℂ)‖
              * (‖(w_m : ℂ)‖ ^ 2)⁻¹) * ((‖(w : ℂ)‖ ^ (-(12 : ℤ)))⁻¹ * ‖(w : ℂ)‖) :=
            mul_nonneg (mul_nonneg (mul_nonneg (zpow_nonneg (norm_nonneg _) _) (norm_nonneg _))
              (inv_nonneg.mpr (by positivity))) (mul_nonneg (inv_nonneg.mpr (zpow_nonneg (norm_nonneg _) _)) (norm_nonneg _))
          have hVp : (0 : ℝ) ≤ (2 * Work.Kernels.scale w_m) ^ NM :=
            Real.rpow_nonneg (le_of_lt (mul_pos (by norm_num) (Work.Kernels.scale_pos w_m))) _
          have hEgnn : (0 : ℝ) ≤ Real.exp (-(Real.pi / t)) * Real.exp (-(Real.pi * (9 / 5) / t))
              * Real.exp (2 * Real.pi / t)
              * (Real.exp (-(2 * Real.pi * (ModularGroup.S • w).im)))⁻¹
              * (Real.exp (Real.pi * ((ModularGroup.S • w).im + t⁻¹)))⁻¹ := by positivity
          have hABnn : (0 : ℝ) ≤ 200 * CM * 4 / (4 * cJ * (min cΔ 1) ^ 4)
              * (24 ^ NM * s ^ (2 * NM)) := mul_nonneg hP1nn hVnn
          exact mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul hP1 hV hVp hP1nn) hT hTnn hABnn)
            hW hWnn (mul_nonneg hABnn (by norm_num))) hEgrp hEgnn
            (mul_nonneg (mul_nonneg hABnn (by norm_num)) (by positivity))
        refine le_trans hprod ?_
        set Vb : ℝ := 24 ^ NM * s ^ (2 * NM) with hVb
        set Wb : ℝ := (3 * s) ^ 14 with hWb
        have hVbWb : Vb * Wb = 24 ^ NM * 3 ^ 14 * s ^ (2 * NM + 14) := by
          rw [hVb, hWb, mul_pow]
          have h1 : s ^ (2 * NM) * s ^ 14 = s ^ (2 * NM + 14) := by
            rw [← Real.rpow_natCast s 14, ← Real.rpow_add hspos]
            norm_num
          have h2 : 24 ^ NM * s ^ (2 * NM) * (3 ^ 14 * s ^ 14)
              = 24 ^ NM * 3 ^ 14 * (s ^ (2 * NM) * s ^ 14) := by ring
          rw [h2, h1]
        have hc : (200 : ℝ) * CM * 4 / (4 * cJ * (min cΔ 1) ^ 4)
            ≤ 1000 * CM / (cJ * (min cΔ 1) ^ 4) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have h2 : (0 : ℝ) ≤ CM * (cJ * (min cΔ 1) ^ 4) := by positivity
          have h3 := mul_le_mul_of_nonneg_right (show (200 : ℝ) * 4 ≤ 1000 * 4 by norm_num) h2
          linarith [h3]
        have hc' : (0 : ℝ) ≤ 1000 * CM / (cJ * (min cΔ 1) ^ 4) :=
          le_of_lt (div_pos (by positivity) (by positivity))
        have hstep : (200 * CM * 4 / (4 * cJ * (min cΔ 1) ^ 4)) * (Vb * Wb)
            ≤ (1000 * CM / (cJ * (min cΔ 1) ^ 4)) * (Vb * Wb) :=
          mul_le_mul_of_nonneg_right hc (by rw [hVb, hWb]; positivity)
        have hfin : (1000 * CM / (cJ * (min cΔ 1) ^ 4)) * (Vb * Wb)
            = (1000 * CM * 24 ^ NM * 3 ^ 14 / (cJ * (min cΔ 1) ^ 4)) * s ^ (2 * NM + 14) := by
          rw [hVbWb]
          ring
        calc (200 * CM * 4 / (4 * cJ * (min cΔ 1) ^ 4)) * Vb * 1 * Wb * 1
            = (200 * CM * 4 / (4 * cJ * (min cΔ 1) ^ 4)) * (Vb * Wb) := by ring
          _ ≤ (1000 * CM / (cJ * (min cΔ 1) ^ 4)) * (Vb * Wb) := hstep
          _ = (1000 * CM * 24 ^ NM * 3 ^ 14 / (cJ * (min cΔ 1) ^ 4)) * s ^ (2 * NM + 14) := hfin
      have h2 : ((200 * Mn * t / ‖(w_m : ℂ)‖ ^ 2) * B)
            / ((cΔ * Lw) * (cΔ * Lt) ^ (if d = 8 then 1 else 2) * Kk)
          ≤ (1000 * CM * 24 ^ NM * 3 ^ 14 / (cJ * (min cΔ 1) ^ 4)) * s ^ (2 * NM + 14) := by
        rw [hratio2]
        exact hkey2
      rwa [div_le_iff₀ hDden] at h2
    have hstep1 : ‖Work.Kernels.KfunClear ℓ d w (Work.Kernels.imagAxis t ht)‖
          / (D1 * D2 ^ (if d = 8 then 1 else 2) * Jj)
        ≤ ((200 * Mn * t / ‖(w_m : ℂ)‖ ^ 2) * a) / DD := by
      rw [div_le_div_iff₀ hDpos hDDpos]
      have h1 := mul_le_mul_of_nonneg_right hnum hDDpos.le
      have h2 := mul_le_mul_of_nonneg_left hden (le_trans (norm_nonneg _) hnum)
      linarith [h1, h2]
    have hstep2 : ((200 * Mn * t / ‖(w_m : ℂ)‖ ^ 2) * a) / DD
        ≤ (1000 * CM * 24 ^ NM * 3 ^ 14 / (cJ * (min cΔ 1) ^ 4)) * s ^ (2 * NM + 14) := by
      rw [div_le_iff₀ hDDpos]
      rw [hzeq2, hDDdef]
      have h := mul_le_mul_of_nonneg_right hcore hDσpos.le
      linarith [h]
    rw [hKax]
    exact le_trans hstep1 hstep2


/-! ## STATUS AND REMAINING WORK (for the continuation)

**Proved in this file, sorry-free** (all needed by the final assembly):

* `jDiff_lower_E` — the sharp `j`-difference lower bound on `E`
  (`c · e^{2π Im (S•w)} · ‖1 - exp (2π i ((S•w) - i/t))‖ ≤ ‖j w - j (i t)‖`), obtained from the
  `cfx_`-copy of `Submission.Work.Asymptotics.E_jdiff_small` (that module declares
  `Work.Asymptotics.norm_qParamFun_le_one` with a *different* signature than
  `Submission.Work.Asymptotics.KPlusXiDefs`, so the two can never share an environment; the copy is
  renamed `cfx_` throughout);
* `one_sub_Eun_eq` — `‖1 - exp (2π i Z)‖ = 2 e^{π(1/t - Im (S•w))} ‖sin (π Z)‖`, `Z = (S•w) - i/t`;
* `good_case_bound` — for `‖sin (π ((S•w) - i/t))‖ ≥ 1/1000`,
  `∃ C N, 0 < C ∧ 0 ≤ N ∧ ‖Kaxis (Kfun ℓ d) w t‖ ≤ C (scale w)^N` for `w ∈ E`, `t ≤ 1`,
  non-coincidence.  Uses Step 1 `Kaxis_Kfun_divisor_bound` + `jDiff_lower_E` + `delta_lower_third`
  at `i/t`; the `e^{±π/t}` factors cancel;
* `im_S_smul_smul_imagAxis` — `Im (S • (γ • i t)) = t/((γ 0 0)²t² + (γ 0 1)²)`;
* `KfunClear_zero_of_coincidence_E` — if `j u = j (i t)`, `t ≤ 1/2` and
  `(99/100)(100/101)²/t ≤ Im (S • u)`, then `KfunClear ℓ d u (i t) = 0` (the coincidences in the
  one-zero ball are cuspidal, hence `KfunClear_cuspParabolic_vanishing` applies).

**REMAINING** (the "bad case" `‖sin (π ((S•w) - i/t))‖ < 1/1000`, and the assembly):

* **DRAFT, NOT COMPILING (in `_mywork/mbound_draft.lean`)**: `KfunClear_le_of_ball`, the
  `M`-bound.  Diagnosis of the remaining elaboration errors of that draft:
  * `Work.Kernels.scale τ = 1 + (τ.im)⁻¹ + ‖τ‖` (NOT `max …`): the `scale u ≤ 2 * scale w_m`
    step must be done from `u.im ≥ 99/100 w_m.im` (`u.im⁻¹ ≤ 100/99 w_m.im⁻¹`) and
    `‖u‖ ≤ 101/100 ‖w_m‖`, and **not** by `rw [Work.Kernels.scale, …]` + `max`-lemmas;
  * in the coincidence case the goal `(0:ℝ) ≤ RHS` needs the RHS written as an explicit
    `mul_nonneg` chain (`positivity` alone fails on the `t^(…)`-zpow);
  * `ball_geometry` (DONE, in the file, sorry-free): the ball controls `u.im`, `‖u‖`, `scale u`
    and `Im (S • u)` — the M-bound should now consume it instead of re-deriving those;
  * round-4 findings (all applied inside the stashed draft): `hb₁` (Step 1) needs
    `(3/2 : ℝ) ≤ Im (S • u)` — take `hSu1 : (3/2:ℝ) ≤ …` from `(99/100)(100/101)²·t⁻¹ ≥ 3/2`
    (`t ≤ 1/2`); `inv_le_inv₀` must be called as `(inv_le_inv₀ u_pos wm_pos).mpr hnorm_ge` to get
    `‖u‖⁻¹ ≤ ((99/100)‖w_m‖)⁻¹`; and inside the coincidence `mul_nonneg` chain every
    `by positivity`/`by norm_num` needs its *type* annotated (otherwise Lean leaves a
    metavariable: `0 ≤ ?m`), while the `^(if d = 8 then 1 else 2)` factor needs the exponent's
    type pinned (`pow_nonneg … (n := (if d = 8 then (1:ℕ) else 2))`, or state the exponent at
    `ℕ` explicitly).  Residual after that: the `hq`/`hgoal` comparisons (the association of the
    statement's RHS is `((((C·(2s)^N)·t^{…})·exp)·(Y·Z'))·Z'' / (cΔ·exp)`).
  * round-3 findings (draft `_mywork/mbound_draft.lean` now has `ball_geometry` consumed, the
    `set_option maxHeartbeats 4000000 in` *before* the docstring, `Real.rpow_nonneg` for the
    `(2·scale w_m)^N₁` factor and `pow_nonneg … (n := (if d = 8 then (1:ℕ) else 2))` — the
    remaining errors are: the coincidence-case `mul_nonneg` chain's association must match the
    statement's RHS exactly (it is `(((C·(2s)^N)·t^{…})·exp)·(Y·Z) / (cΔ·exp)`), the
    `hfin`/`hgoal` product comparisons still need splitting into two `have`s, and
    `‖Δu‖`'s chain needs `inv_le_inv₀`-with-`(99/100)‖w_m‖` (not `‖w_m‖`) plus
    `mul_pow`/`zpow_neg`/`inv_pow` conversions;
  * round-2 findings (draft stashed again, 329 lines, in `_mywork/mbound_draft.lean`):
    - `inv_le_inv₀ (ha : 0 < a) (hb : 0 < b) : a⁻¹ ≤ b⁻¹ ↔ b ≤ a` — so
      `u.im⁻¹ ≤ ((99/100)*w_m.im)⁻¹` is `(inv_le_inv₀ u.im_pos (by positivity)).mpr hu_im`, and
      the factor `((99/100)*w_m.im)⁻¹ = (100/99)*w_m.im⁻¹` needs `field_simp; ring`;
    - `pow_nonneg base (exponent)` must be given the *explicit* `(if d = 8 then 1 else 2)`
      (a bare `_` in exponent position is a parse error);
    - the coincidence case needs an explicit `mul_nonneg` chain in the *left-associated*
      shape of the statement's RHS, ending with `rw [div_eq_mul_inv]`;
    - the non-coincidence branch as drafted still hits `isDefEq`/`tactic` heartbeats
      (`set_option maxHeartbeats 2000000` was not enough): the `hgoal` product comparison
      should be split into two small `have`s (the `C`-factor comparison first, then a
      `mul_le_mul_of_nonneg_right` after factoring by `ring`-`show`s).
  * the final comparison is best done as: `C₁ (scale u)^N₁ · (2(100/99)^12) ≤ C (2 scale w_m)^N₁`
    (an explicit `nlinarith` from `rpow_le_rpow hscale hN₁`), then factor both sides of the
    quotient by `(t^{…} · e^{-π/t} · Y · Z / Blow)` via `ring`-`show`s and
    `mul_le_mul_of_nonneg_right`.
1. `M`-bound on the closed ball `B(w_m, r)`, `r := w_m.im/100`, for
   `w_m := S • ((m:ℝ) +ᵥ z₀)`, `z₀ := imagAxis t⁻¹ _` (with `m` from `exists_near_shift` and
   `ε := 1/1000`):
   * if `j u ≠ j (i t)`: Step 1 (`hb₁`) at `u` (its hypothesis `3/2 ≤ Im (S•u)` holds on the ball
     by `S_im_ge_of_ball`: `(99/100)(100/101)²/t ≥ 3/2` because the bad case gives
     `t ≤ 1/(2 - ε(1/2+1/π)) ≤ 1/2`), combined with
     `KL.Kfun_eq_KfunClear_div` and `KL.norm_growthPrefactor`, so that
     `‖KfunClear ℓ d u (i t)‖ = ‖Kfun u (i t)‖ ‖gp(u, i t)‖` and the factor `‖j u - j (i t)‖`
     cancels against the divisor, leaving
     `M := C₁ (2 scale w_m)^N₁ t^{d/2-4} e^{-π/t} · 4 (100/99)^12 ‖w_m‖^{-12} e^{-1.9π/t}
        · (2 t^{-12} e^{-2π/t})^e / (c_Δ e^{-2π/t})`
     (`norm_DeltaFun_le_of_im` at `u` and at `i t`, `norm_DeltaFun_ge_of_im`/`delta_lower_third` at
     `i/t`; `scale u ≤ 2 scale w_m ≤ 4 scale w`);
   * if `j u = j (i t)`: `KfunClear_zero_of_coincidence_E` gives the value `0 ≤ M`.
2. One-zero: `KL.one_zero_apply` for `f := fun τ => KfunClear ℓ d τ (imagAxis t ht)`
   (`hf` from `KL.mdifferentiable_KfunClear_fst`), `c := w₀ := w_m`, radius `r`, `M` as above,
   `‖w - w_m‖ < r/2` ⟹ `‖KfunClear ℓ d w (i t)‖ ≤ (2M/r)‖w - w_m‖`.
3. Geometry: `‖σ - σ_m‖ ≤ ζ` (`σ := S•w`, `σ_m := z₀ + m`, from `exists_near_shift`);
   `|w_m|² = t · w_m.im` (from `EReg_S_im` at `w_m`), `‖w - w_m‖ ≤ 2ζ|w_m|² ≤ (r/2)` needs
   `ζ t ≤ 1/400`; `‖w - w_m‖ ≥ ‖X - m‖ |w_m|²/2` with `X := σ - z₀`.
4. `j`-difference in the bad case: `jDiff_lower_E` at `w` gives
   `‖j w - j (i t)‖ ≥ c_J e^{2πy} 2 e^{-π(1/t - y)} ‖sin (π X)‖ ≥ 4 c_J e^{-πζ} e^{πy + π/t}‖X - m‖`
   using `‖sin (π (X - m))‖ ≥ 2‖X - m‖` (`|sin z| ≥ 2|z|/π`) and `‖X - m‖ = ‖σ - σ_m‖`.
5. Final: `‖Kaxis (Kfun ℓ d) w t‖ = ‖KfunClear ℓ d w (i t)‖/‖gp(w, i t)‖` with
   `‖gp(w, i t)‖ = ‖Δ w‖‖Δ(i t)‖^e‖j w - j (i t)‖`, then the exponential bookkeeping
   (`e^{-π/t}`, `e^{2πy}`, `e^{2π/t}`, `e^{-2πe/t}`) leaves `(scale w)^{N}`, using
   `|w_m|²/r = 100 t` and `|σ_m|² = 1/|w_m|² ≤ t · scale w`.
6. Assembly: split on `‖sin‖ < 1/1000`, take `c₀ := 1/2`, `c := max` of the two constants,
   `N' := max` of the two exponents.  **The near-diagonal hypothesis of the target is not needed**
   (both cases work for all `w ∈ E`, `t ≤ 1` with non-coincidence).
-/

/-! ## The target -/

theorem Kaxis_Kfun_noncoincidence_E (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ c₀ c N' : ℝ, 0 < c₀ ∧ 0 ≤ c ∧ 0 ≤ N' ∧
      ∀ (w : UpperHalfPlane) (t : ℝ) (ht : 0 < t),
        w ∈ Work.Asymptotics.KEpsilon → t ≤ 1 →
        Work.Kernels.jInvariantFun w ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) →
        (∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
          ‖(w : ℂ) - (((γ • Work.Kernels.imagAxis t ht : UpperHalfPlane)) : ℂ)‖ < c₀ * t ^ 2) →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t‖ ≤ c * (Work.Kernels.scale w) ^ N' := by
  obtain ⟨Cg, Ng, hCg, hNg, hgood⟩ := good_case_bound ℓ d hd
  obtain ⟨Cb, Nb, hCb, hNb, hbadcase⟩ := bad_case_bound ℓ d hd
  refine ⟨1 / 2, max Cg Cb, max Ng Nb, by norm_num,
    le_trans hCg.le (le_max_left _ _), le_trans hNg (le_max_left _ _), ?_⟩
  intro w t ht hwE ht1 hne hnear
  have hspos : 0 < Work.Kernels.scale w := Work.Kernels.scale_pos w
  have hs1 : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
  rcases lt_or_ge (‖Complex.sin (Real.pi * (((ModularGroup.S • w : ℍ) : ℂ)
    - ((Work.Kernels.imagAxis (t⁻¹) (inv_pos.mpr ht) : ℍ) : ℂ)))‖) (1 / 1000) with hlt | hge
  · have h := hbadcase w t ht hwE ht1 hne hnear hlt
    refine le_trans h ?_
    refine mul_le_mul (le_max_right _ _) ?_ ?_ (le_trans hCb.le (le_max_right _ _))
    · exact Real.rpow_le_rpow_of_exponent_le hs1 (le_max_right _ _)
    · exact Real.rpow_nonneg hspos.le _
  · have h := hgood w t ht hwE ht1 hne hge
    refine le_trans h ?_
    refine mul_le_mul (le_max_left _ _) ?_ ?_ (le_trans hCg.le (le_max_left _ _))
    · exact Real.rpow_le_rpow_of_exponent_le hs1 (le_max_left _ _)
    · exact Real.rpow_nonneg hspos.le _

end Work.Asymptotics
