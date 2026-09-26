import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.Kaxis_Kfun_coincidence_E
import Submission.Work.Asymptotics.Kaxis_Kfun_noncoincidence_E
import Submission.Work.Kernels.Kernels

namespace Work.Asymptotics

set_option linter.unusedSimpArgs false

open UpperHalfPlane ModularGroup Matrix
open scoped MatrixGroups

noncomputable section

/-!
# The near-diagonal bound for the CKMRV kernel on the cusp-`0` neighbourhood `E`

The target `Work.Asymptotics.near_diag_bound_E` bounds `‖Kaxis (Kfun ℓ d) w t‖` by
`c * (scale w) ^ N' * t ^ N` for `w ∈ E = KEpsilon`, `0 < t ≤ 1`, on the *near-diagonal* part of
the region, i.e. under the hypothesis that `w` is within `c₀ t ^ 2` of a modular image `γ • (it)`
of the contour point `it`.

The proof splits the region into the coincidence points and the rest:

* at a coincidence `j w = j (it)` inside `E` the constant bound
  `Work.Asymptotics.Kaxis_Kfun_coincidence_E` applies;
* otherwise `Work.Asymptotics.Kaxis_Kfun_noncoincidence_E` applies;
* the two bounds, which are polynomial in `scale w`, are converted into the requested
  `c * (scale w) ^ N' * t ^ N` using the *key geometric consequence of the near-diagonal
  hypothesis*: `Im w ≤ t * (1 + c₀)`, hence `scale w * t ≥ 1 / (1 + c₀)`, and the factorisation
  `scale w ^ P = scale w ^ (P + N) * ((scale w * t) ^ N)⁻¹ * t ^ N`.

This is why the target is *not* a formal consequence of the two sub-lemmas for the same
exponents `c, N'`: the factor `t ^ N` has to be paid for by the `N` extra powers of `scale w`
produced by `scale w ≳ 1 / t`.
-/

/-! ## Elementary geometry of `E` -/

/-- `Im (S • w) = Im w / ‖w‖ ^ 2`. -/
private lemma nd_im_S_smul (z₀ : ℍ) : (ModularGroup.S • z₀).im = z₀.im / ‖(z₀ : ℂ)‖ ^ 2 := by
  have h1 : ((ModularGroup.S • z₀ : ℍ) : ℂ) = (-(z₀ : ℂ))⁻¹ := by
    rw [UpperHalfPlane.modular_S_smul]
  have h2 : (ModularGroup.S • z₀ : ℍ).im = ((-(z₀ : ℂ))⁻¹).im := by
    rw [← UpperHalfPlane.coe_im (ModularGroup.S • z₀), h1]
  rw [h2, Complex.inv_im, Complex.neg_im, UpperHalfPlane.coe_im, Complex.normSq_neg,
    Complex.normSq_eq_norm_sq]
  ring

/-- The explicit disc form of `E`: `w ∈ E` implies `‖w - i/4‖ ≤ 1/4`. -/
private lemma nd_KEpsilon_norm_sub_le {w : ℍ} (hw : w ∈ KEpsilon) :
    ‖(w : ℂ) - (1 / 4 : ℂ) * Complex.I‖ ≤ 1 / 4 := by
  have h2 : 2 ≤ (ModularGroup.S • w).im := hw.2
  rw [nd_im_S_smul] at h2
  have hpos : (0:ℝ) < ‖(w : ℂ)‖ ^ 2 := by
    have := norm_pos_iff.mpr w.ne_zero; positivity
  have hnorm : ‖(w : ℂ)‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    ring
  have h3 : 2 * (w.re ^ 2 + w.im ^ 2) ≤ w.im := by
    rw [← hnorm]; exact (le_div_iff₀ hpos).mp h2
  have hsq : ‖(w : ℂ) - (1 / 4 : ℂ) * Complex.I‖ ^ 2 = w.re ^ 2 + (w.im - 1 / 4) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, mul_one,
      UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    norm_num
    ring
  have h4 : ‖(w : ℂ) - (1 / 4 : ℂ) * Complex.I‖ ^ 2 ≤ 1 / 16 := by
    rw [hsq]; nlinarith
  nlinarith [norm_nonneg ((w : ℂ) - (1 / 4 : ℂ) * Complex.I)]

/-- `Im w ≤ 1/2` on `E`. -/
private lemma nd_KEpsilon_im_le_half {w : ℍ} (hw : w ∈ KEpsilon) : w.im ≤ 1 / 2 := by
  have h := nd_KEpsilon_norm_sub_le hw
  have h2 : |((w : ℂ) - (1 / 4 : ℂ) * Complex.I).im| ≤ 1 / 4 := by
    refine le_trans (Complex.abs_im_le_norm _) h
  have h3 : ((w : ℂ) - (1 / 4 : ℂ) * Complex.I).im = w.im - 1 / 4 := by
    simp
  rw [h3] at h2
  have h4 := (abs_le.mp h2).2
  linarith

/-! ## The near-diagonal hypothesis forces `Im w ≲ t` -/

/-- The imaginary part of `γ • (it)`: `t / ((γ 1 0)² t² + (γ 1 1)²)`. -/
private lemma nd_im_smul_imagAxis (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) {t : ℝ} (ht : 0 < t) :
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

/-- **The near-diagonal hypothesis bounds `Im w` by `t (1 + c₀)`.** -/
private lemma nd_im_le_of_near_diag {w : ℍ} {t c₀ : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hc₀0 : 0 ≤ c₀) (hc₀ : c₀ ≤ 1 / 2) (hw : w ∈ KEpsilon)
    (h : ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      ‖(w : ℂ) - (((γ • Work.Kernels.imagAxis t ht : ℍ)) : ℂ)‖ < c₀ * t ^ 2) :
    w.im ≤ t * (1 + c₀) := by
  obtain ⟨γ, hγ⟩ := h
  set u : ℂ := ((γ • Work.Kernels.imagAxis t ht : ℍ) : ℂ) with hu
  have him : |((w : ℂ) - u).im| ≤ ‖(w : ℂ) - u‖ := Complex.abs_im_le_norm _
  have hsub : ((w : ℂ) - u).im = w.im - u.im := by simp
  have hu_im := nd_im_smul_imagAxis γ ht
  have hw_le : w.im ≤ u.im + c₀ * t ^ 2 := by
    have h1 : ((w : ℂ) - u).im ≤ ‖(w : ℂ) - u‖ := le_trans (le_abs_self _) him
    rw [hsub] at h1
    linarith [h1, hγ]
  rcases eq_or_ne (γ 1 1) 0 with hd | hd
  · -- `d = 0`: then `Im (γ • it) = 1 / (c² t) ≥ 1`, contradicting `Im w ≤ 1/2`.
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
    have hhalf := nd_KEpsilon_im_le_half hw
    have hc0t : c₀ * t ^ 2 ≤ 1 / 2 := by nlinarith [hc₀, ht.le, ht1, sq_nonneg t]
    linarith
  · -- `d ≠ 0`: then `Im (γ • it) ≤ t`, so `Im w ≤ t (1 + c₀)`.
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
    have : c₀ * t ^ 2 ≤ c₀ * t := hct
    linarith [hw_le, hu_le, this, mul_nonneg hc₀0 ht.le]

end

set_option linter.unusedSimpArgs false

noncomputable section

/-- **The scale factorisation.**  For `s ≥ 1`, `0 < t`, `N ≥ 0` and `s * t ≥ 1 / (1 + c₀)` one
has `s ^ P ≤ (1 + c₀) ^ N * (s ^ (P + N) * t ^ N)`: the `N` extra powers of `s` produced by
`s ≳ 1 / t` pay for the factor `t ^ N`. -/
private lemma scale_pow_le {s t c₀ N P : ℝ} (hN : 0 ≤ N) (hs : 1 ≤ s) (ht : 0 < t)
    (hc : 0 < 1 + c₀) (hst : 1 / (1 + c₀) ≤ s * t) :
    s ^ P ≤ (1 + c₀) ^ N * (s ^ (P + N) * t ^ N) := by
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hdiv : 0 < (1 + c₀) * t := mul_pos hc ht
  have hsge : ((1 + c₀) * t)⁻¹ ≤ s := by
    rw [inv_eq_one_div, div_le_iff₀ hdiv]
    have h : 1 ≤ (s * t) * (1 + c₀) := (div_le_iff₀ hc).mp hst
    calc (1 : ℝ) = 1 := rfl
      _ ≤ (s * t) * (1 + c₀) := h
      _ = s * ((1 + c₀) * t) := by ring
  have hpow : s ^ (-N) ≤ ((1 + c₀) * t) ^ N := by
    have h := Real.rpow_le_rpow_of_nonpos (x := ((1 + c₀) * t)⁻¹) (y := s)
      (inv_pos.mpr hdiv) hsge (by linarith : -N ≤ 0)
    rw [Real.inv_rpow hdiv.le, Real.rpow_neg hdiv.le, inv_inv] at h
    exact h
  have hkey : s ^ (-N) ≤ (1 + c₀) ^ N * t ^ N := by
    rw [← Real.mul_rpow hc.le ht.le (z := N)]
    exact hpow
  have hsplit : s ^ P = s ^ (P + N) * s ^ (-N) := by
    rw [← Real.rpow_add hspos]
    congr 1
    ring
  rw [hsplit]
  calc s ^ (P + N) * s ^ (-N) ≤ s ^ (P + N) * ((1 + c₀) ^ N * t ^ N) :=
        mul_le_mul_of_nonneg_left hkey (Real.rpow_nonneg hspos.le _)
    _ = (1 + c₀) ^ N * (s ^ (P + N) * t ^ N) := by ring

/-- **Assembly.**  Two polynomial bounds on `E` — one at the coincidence points `j w = j (it)`,
one elsewhere — imply the target near-diagonal bound `c * (scale w) ^ N' * t ^ N`. -/
theorem near_diag_bound_E_of (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (hcoin : ∃ c N' : ℝ, 0 ≤ c ∧ 0 ≤ N' ∧
      ∀ (w : UpperHalfPlane) (t : ℝ) (ht : 0 < t), w ∈ KEpsilon → t ≤ 1 →
        Work.Kernels.jInvariantFun w = Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t‖ ≤ c * (Work.Kernels.scale w) ^ N')
    (hnon : ∃ c₀ c N' : ℝ, 0 < c₀ ∧ 0 ≤ c ∧ 0 ≤ N' ∧
      ∀ (w : UpperHalfPlane) (t : ℝ) (ht : 0 < t), w ∈ KEpsilon → t ≤ 1 →
        Work.Kernels.jInvariantFun w ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) →
        (∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
          ‖(w : ℂ) - (((γ • Work.Kernels.imagAxis t ht : UpperHalfPlane)) : ℂ)‖ < c₀ * t ^ 2) →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t‖ ≤ c * (Work.Kernels.scale w) ^ N') :
    ∀ N : ℝ, 0 ≤ N → ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ c N' : ℝ, 0 ≤ c ∧
      ∀ (w : UpperHalfPlane) (t : ℝ) (ht : 0 < t), w ∈ KEpsilon → t ≤ 1 →
        (∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
          ‖(w : ℂ) - (((γ • Work.Kernels.imagAxis t ht : UpperHalfPlane)) : ℂ)‖ < c₀ * t ^ 2) →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t‖ ≤ c * (Work.Kernels.scale w) ^ N' * t ^ N := by
  intro N hN
  obtain ⟨cJ, NJ, hcJ, hNJ, hJ⟩ := hcoin
  obtain ⟨c₀H, cH, NH, hc₀H, hcH, hNH, hH⟩ := hnon
  set c₀ : ℝ := min c₀H (1 / 2) with hc₀def
  have hc₀pos : 0 < c₀ := lt_min hc₀H (by norm_num)
  have hc₀leH : c₀ ≤ c₀H := min_le_left _ _
  have hc₀le : c₀ ≤ 1 / 2 := min_le_right _ _
  have hc₀0 : 0 ≤ c₀ := hc₀pos.le
  have hcpos : 0 < 1 + c₀ := by linarith
  set P₀ : ℝ := max NJ NH with hP₀def
  refine ⟨c₀, hc₀pos, max cJ cH * (1 + c₀) ^ N, P₀ + N, ?_, ?_⟩
  · have h1 : (0:ℝ) ≤ max cJ cH := le_trans hcJ (le_max_left cJ cH)
    have h2 : (0:ℝ) ≤ (1 + c₀) ^ N := Real.rpow_nonneg hcpos.le N
    exact mul_nonneg h1 h2
  · intro w t ht hw ht1 hdist
    have hdistH : ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
        ‖(w : ℂ) - (((γ • Work.Kernels.imagAxis t ht : UpperHalfPlane)) : ℂ)‖ < c₀H * t ^ 2 := by
      obtain ⟨γ, hγ⟩ := hdist
      refine ⟨γ, lt_of_lt_of_le hγ ?_⟩
      have : (0:ℝ) ≤ t ^ 2 := sq_nonneg t
      nlinarith [hc₀leH, this]
    have himle : w.im ≤ t * (1 + c₀) :=
      nd_im_le_of_near_diag ht ht1 hc₀0 hc₀le hw hdist
    have hs1 : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
    have hspos : 0 < Work.Kernels.scale w := Work.Kernels.scale_pos w
    have hst : 1 / (1 + c₀) ≤ Work.Kernels.scale w * t := by
      have himpos : 0 < w.im := w.im_pos
      have hsc : 1 / w.im ≤ Work.Kernels.scale w := by
        rw [one_div, Work.Kernels.scale]
        linarith [norm_nonneg (w : ℂ)]
      have hinv : 1 / (t * (1 + c₀)) ≤ 1 / w.im :=
        one_div_le_one_div_of_le himpos himle
      have h1 : 1 / (1 + c₀) ≤ t * (1 / w.im) := by
        have h2 : t * (1 / (t * (1 + c₀))) = 1 / (1 + c₀) := by
          field_simp
        calc 1 / (1 + c₀) = t * (1 / (t * (1 + c₀))) := h2.symm
          _ ≤ t * (1 / w.im) := mul_le_mul_of_nonneg_left hinv ht.le
      calc 1 / (1 + c₀) ≤ t * (1 / w.im) := h1
        _ ≤ t * Work.Kernels.scale w := mul_le_mul_of_nonneg_left hsc ht.le
        _ = Work.Kernels.scale w * t := by ring
    have hscale := scale_pow_le (P := P₀) hN hs1 ht hcpos hst
    have hNJ' : NJ ≤ P₀ := by
      have h1 : NJ ≤ max NJ NH := le_max_left NJ NH
      linarith [hP₀def]
    have hNH' : NH ≤ P₀ := by
      have h1 : NH ≤ max NJ NH := le_max_right NJ NH
      linarith [hP₀def]
    rcases eq_or_ne (Work.Kernels.jInvariantFun w)
        (Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) with hj | hj
    · have hb := hJ w t ht hw ht1 hj
      have hle : ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t‖
          ≤ max cJ cH * (Work.Kernels.scale w) ^ P₀ := by
        have h1 : (Work.Kernels.scale w) ^ NJ ≤ (Work.Kernels.scale w) ^ P₀ :=
          Real.rpow_le_rpow_of_exponent_le hs1 hNJ'
        calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t‖
            ≤ cJ * (Work.Kernels.scale w) ^ NJ := hb
          _ ≤ max cJ cH * (Work.Kernels.scale w) ^ P₀ := by
              refine le_trans ?_ (mul_le_mul_of_nonneg_left h1 (le_trans hcJ (le_max_left cJ cH)))
              exact mul_le_mul_of_nonneg_right (le_max_left cJ cH)
                (Real.rpow_nonneg hspos.le _)
      calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t‖
          ≤ max cJ cH * (Work.Kernels.scale w) ^ P₀ := hle
        _ ≤ max cJ cH * ((1 + c₀) ^ N * ((Work.Kernels.scale w) ^ (P₀ + N) * t ^ N)) :=
              mul_le_mul_of_nonneg_left hscale (le_trans hcJ (le_max_left cJ cH))
        _ = max cJ cH * (1 + c₀) ^ N *
              (Work.Kernels.scale w) ^ (P₀ + N) * t ^ N := by ring
    · have hb := hH w t ht hw ht1 hj hdistH
      have hle : ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t‖
          ≤ max cJ cH * (Work.Kernels.scale w) ^ P₀ := by
        have h1 : (Work.Kernels.scale w) ^ NH ≤ (Work.Kernels.scale w) ^ P₀ :=
          Real.rpow_le_rpow_of_exponent_le hs1 hNH'
        calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t‖
            ≤ cH * (Work.Kernels.scale w) ^ NH := hb
          _ ≤ max cJ cH * (Work.Kernels.scale w) ^ P₀ := by
              refine le_trans ?_ (mul_le_mul_of_nonneg_left h1 (le_trans hcH (le_max_right cJ cH)))
              exact mul_le_mul_of_nonneg_right (le_max_right cJ cH)
                (Real.rpow_nonneg hspos.le _)
      calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t‖
          ≤ max cJ cH * (Work.Kernels.scale w) ^ P₀ := hle
        _ ≤ max cJ cH * ((1 + c₀) ^ N * ((Work.Kernels.scale w) ^ (P₀ + N) * t ^ N)) :=
              mul_le_mul_of_nonneg_left hscale (le_trans hcH (le_max_right cJ cH))
        _ = max cJ cH * (1 + c₀) ^ N *
              (Work.Kernels.scale w) ^ (P₀ + N) * t ^ N := by ring

end

/-- **The near-diagonal bound for the CKMRV kernel on the cusp-`0` neighbourhood `E`.**

Combines the coincidence bound `Work.Asymptotics.Kaxis_Kfun_coincidence_E` and the
non-coincidence bound `Work.Asymptotics.Kaxis_Kfun_noncoincidence_E` through the assembly
`Work.Asymptotics.near_diag_bound_E_of`. -/
theorem near_diag_bound_E (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∀ N : ℝ, 0 ≤ N → ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ c N' : ℝ, 0 ≤ c ∧
      ∀ (w : UpperHalfPlane) (t : ℝ) (ht : 0 < t),
        w ∈ Work.Asymptotics.KEpsilon → t ≤ 1 →
        (∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
          ‖(w : ℂ) - (((γ • Work.Kernels.imagAxis t ht : UpperHalfPlane)) : ℂ)‖ < c₀ * t ^ 2) →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t‖
          ≤ c * (Work.Kernels.scale w) ^ N' * t ^ N :=
  near_diag_bound_E_of ℓ d hd (Kaxis_Kfun_coincidence_E ℓ d hd) (Kaxis_Kfun_noncoincidence_E ℓ d hd)

end Work.Asymptotics
