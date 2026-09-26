/-
# Auxiliary lemmas for the tile flatness bound `Work.Asymptotics.Kaxis_tile_flat_below_pole`

This file collects the elementary *geometric* inputs of the tile bound for the CKMRV kernel at
the cusp-`±1` tiles `n + E` (`n = ±1`, `E = KEpsilon`):

* `tile_im_le_half`: `Im w ≤ 1/2` on `E`;
* `im_S_smul_eq`, `im_S_smul_le_inv_im`: the imaginary part of `S • w`;
* `tile_im_S_le`: `Im (S • w) ≤ 1/(2 t)` whenever `t ≤ Im w / 2` (the "below the pole"
  hypothesis of the target controls the height of the cusp-`0` image);
* `exp_neg_div_le_mul_rpow'`: `e^{-c/t} ≤ K t^N` on `0 < t ≤ 1`;
* `tile_one_le_scale_mul`: `1 ≤ 2 t · scale w` on the tile region, which converts powers of
  `1/t` into powers of `scale w`.
-/
import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.ERegDefs
import Submission.Work.Asymptotics.jInvariantFun_eq_smul_of_eq
import Submission.Work.Asymptotics.orbit_imagAxis_of_mem_DomainD
import Submission.Work.Asymptotics.eq_one_or_neg_one_or_S_of_smul_imagAxis
import Submission.Work.Kernels.KernelFacts.KPlus_T2
import Submission.Work.Asymptotics.DeltaFun_imagAxis_atZero

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics

open Work.Kernels

/-! ## The geometry of `E` and of its `S`-image -/

/-- `(S • w).im = w.im / ‖w‖²`. -/
lemma im_S_smul_eq (w : ℍ) : (ModularGroup.S • w).im = w.im / ‖(w : ℂ)‖ ^ 2 :=
  EReg_S_im w

/-- On the cusp-`0` tile `E` the imaginary part is at most `1/2`. -/
lemma tile_im_le_half {w : ℍ} (hw : w ∈ KEpsilon) : w.im ≤ 1 / 2 := by
  rw [mem_KEpsilon] at hw
  have h2 : (2 : ℝ) ≤ w.im / ‖(w : ℂ)‖ ^ 2 := by
    rw [← im_S_smul_eq]; exact hw.2
  have hn : 0 < ‖(w : ℂ)‖ ^ 2 := pow_pos (norm_pos_iff.mpr w.ne_zero) 2
  rw [le_div_iff₀ hn] at h2
  have him2 : w.im ^ 2 ≤ ‖(w : ℂ)‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    nlinarith [sq_nonneg w.re]
  nlinarith [w.im_pos, h2, him2]

/-- `‖w‖² ≥ (Im w)²`, so `Im (S w) ≤ 1/Im w`. -/
lemma im_S_smul_le_inv_im (w : ℍ) : (ModularGroup.S • w).im ≤ (w.im)⁻¹ := by
  rw [im_S_smul_eq]
  have him2 : w.im ^ 2 ≤ ‖(w : ℂ)‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    nlinarith [sq_nonneg w.re]
  have hn : 0 < ‖(w : ℂ)‖ ^ 2 := pow_pos (norm_pos_iff.mpr w.ne_zero) 2
  rw [div_le_iff₀ hn, inv_mul_eq_div, le_div_iff₀ w.im_pos]
  nlinarith [him2]

/-- **The height control on the tile region.**  If `w ∈ E` and `0 < t ≤ Im w / 2` then
`Im (S • w) ≤ 1/(2 t)`. -/
lemma tile_im_S_le {w : ℍ} (_hw : w ∈ KEpsilon) {t : ℝ} (ht : 0 < t) (htle : t ≤ w.im / 2) :
    (ModularGroup.S • w).im ≤ (1 / 2 : ℝ) / t := by
  have h1 : (ModularGroup.S • w).im ≤ (w.im)⁻¹ := im_S_smul_le_inv_im w
  have h2 : (w.im)⁻¹ ≤ (1 / 2 : ℝ) / t := by
    rw [le_div_iff₀ ht, show (w.im)⁻¹ * t = t / w.im by field_simp]
    rw [div_le_iff₀ w.im_pos]
    linarith [htle]
  linarith

/-- **Exponential decay beats every power.**  For `0 < c` and any `N` there is `K > 0` with
`e^{-c/t} ≤ K t^N` for `0 < t ≤ 1`. -/
lemma exp_neg_div_le_mul_rpow' (c N : ℝ) (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 0 < t → t ≤ 1 → Real.exp (-(c / t)) ≤ K * t ^ N := by
  set m : ℕ := Nat.ceil N with hm
  have hmN : N ≤ (m : ℝ) := Nat.le_ceil N
  set K : ℝ := (m.factorial : ℝ) / c ^ m with hK
  have hKpos : 0 < K := div_pos (by exact_mod_cast m.factorial_pos) (pow_pos hc m)
  refine ⟨max K 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun t ht ht1 => ?_⟩
  have hmf : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast m.factorial_pos
  have hpow : (c / t) ^ m / (m.factorial : ℝ) ≤ Real.exp (c / t) :=
    Real.pow_div_factorial_le_exp (c / t) (by positivity) m
  have hpos : 0 < (c / t) ^ m / (m.factorial : ℝ) := by positivity
  have hkey : Real.exp (-(c / t)) ≤ K * t ^ m := by
    have hinv : (Real.exp (c / t))⁻¹ ≤ ((c / t) ^ m / (m.factorial : ℝ))⁻¹ :=
      (inv_le_inv₀ (Real.exp_pos _) hpos).mpr hpow
    have hval : ((c / t) ^ m / (m.factorial : ℝ))⁻¹ = (m.factorial : ℝ) * t ^ m / c ^ m := by
      rw [inv_div, div_pow]; field_simp
    rw [← Real.exp_neg, hval] at hinv
    have h2 : (m.factorial : ℝ) * t ^ m / c ^ m = K * t ^ m := by rw [hK]; ring
    rw [h2] at hinv
    exact hinv
  have hmle : t ^ m ≤ t ^ N := by
    have h := Real.rpow_le_rpow_of_exponent_ge ht ht1 hmN
    simpa [Real.rpow_natCast] using h
  calc Real.exp (-(c / t)) ≤ K * t ^ m := hkey
    _ ≤ K * t ^ N := mul_le_mul_of_nonneg_left hmle hKpos.le
    _ ≤ max K 1 * t ^ N :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg ht.le N)

/-- A point of the imaginary axis is `i` times its imaginary part (local copy of the
classification input of `Work.Asymptotics.Kaxis_local_middle`). -/
lemma eq_imagAxis_of_re_eq_zero' {z : ℍ} (hz : (z : ℂ).re = 0) :
    z = Work.Kernels.imagAxis z.im z.im_pos := by
  apply UpperHalfPlane.ext
  show (z : ℂ) = (z.im : ℂ) * Complex.I
  have h := Complex.re_add_im (z : ℂ)
  rw [hz, UpperHalfPlane.coe_im] at h
  rw [← h]
  simp

/-- **The coincidences with the imaginary axis, locally.**  If `τ ∈ 𝒟`, a point `z` of the
imaginary axis satisfies `j τ = j z` only if `z = τ` or `z = S τ` (local copy of
`Work.Asymptotics.eq_or_eq_S_of_re_eq_zero`, stated here so that this file does not need to
import `Work.Asymptotics.MiddleRange.Classify`, which clashes with the `KernelBoundAux` branch
of the workspace). -/
lemma eq_or_eq_S_of_re_eq_zero' {τ z : ℍ} (hτ : τ ∈ DomainD) (hz : (z : ℂ).re = 0)
    (h : Work.Kernels.jInvariantFun τ = Work.Kernels.jInvariantFun z) :
    z = τ ∨ z = ModularGroup.S • τ := by
  obtain ⟨γ, hγ⟩ := jInvariantFun_eq_smul_of_eq h
  have hzγ : z = γ⁻¹ • τ := by rw [← hγ, inv_smul_smul]
  have hτre : τ.re = 0 := by
    refine orbit_imagAxis_of_mem_DomainD τ hτ γ⁻¹ ?_
    rw [← hzγ]
    exact hz
  have hτ' : τ = Work.Kernels.imagAxis τ.im τ.im_pos := eq_imagAxis_of_re_eq_zero' hτre
  have hz' : z = Work.Kernels.imagAxis z.im z.im_pos := eq_imagAxis_of_re_eq_zero' hz
  have hsz : γ⁻¹ • Work.Kernels.imagAxis τ.im τ.im_pos = Work.Kernels.imagAxis z.im z.im_pos := by
    rw [← hτ', ← hz', hzγ]
  rcases eq_one_or_neg_one_or_S_of_smul_imagAxis τ.im_pos z.im_pos hsz with h1 | h1 | h1 | h1
  · left
    rw [hzγ, h1]; simp
  · left
    rw [hzγ, h1]
    simpa using ModularGroup.SL_neg_smul (g := (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)) τ
  · right
    rw [hzγ, h1]
  · right
    rw [hzγ, h1,
      show (-(ModularGroup.S) : Matrix.SpecialLinearGroup (Fin 2) ℤ)
        = (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) * ModularGroup.S from (neg_one_mul _).symm,
      mul_smul]
    simpa using ModularGroup.SL_neg_smul (g := (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ))
      (ModularGroup.S • τ)

/-- **Non-coincidence on the tile region.**  For `w ∈ E`, `n = ±1` and `0 < t ≤ Im w / 2` the
tile point `n + w` is not equivalent to `i t`, so `j (n + w) ≠ j (i t)`.

The proof is `Work.Asymptotics.eq_or_eq_S_of_re_eq_zero` (the classification of the
imaginary-axis coincidences for points of the fundamental domain) together with `Im w ≤ 1/2`. -/
theorem tile_noncoincidence (w : ℍ) (hw : w ∈ KEpsilon) (n : ℤ) (hn : n = 1 ∨ n = -1)
    (t : ℝ) (ht : 0 < t) (htle : t ≤ w.im / 2) :
    Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w) ≠
      Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) := by
  intro h
  have hjn : Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w) = Work.Kernels.jInvariantFun w := by
    rcases hn with rfl | rfl
    · norm_num
      exact Work.Kernels.KernelFacts.jInvariantFun_vadd_one w
    · norm_num
      have h1 : Work.Kernels.jInvariantFun ((1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ w))
          = Work.Kernels.jInvariantFun ((-1 : ℝ) +ᵥ w) :=
        Work.Kernels.KernelFacts.jInvariantFun_vadd_one ((-1 : ℝ) +ᵥ w)
      rw [show (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ w) = w by
        rw [← add_vadd, add_neg_cancel, zero_vadd]] at h1
      exact h1.symm
  rw [hjn] at h
  have hre : ((Work.Kernels.imagAxis t ht : ℍ) : ℂ).re = 0 := by
    simp [Work.Kernels.imagAxis]
  rcases eq_or_eq_S_of_re_eq_zero' (KEpsilon_subset_DomainD hw) hre h with h1 | h1
  · have h2 : (Work.Kernels.imagAxis t ht).im = t := by simp [Work.Kernels.imagAxis]
    have h3 : (Work.Kernels.imagAxis t ht).im = w.im := by rw [h1]
    rw [h2] at h3
    linarith
  · have hw' : w = Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht) := by
      rw [show w = ModularGroup.S • (ModularGroup.S • w) from (S_smul_S_smul w).symm, ← h1,
        imagAxis_smul_S t ht]
    have him : w.im = t⁻¹ := by rw [hw']; simp [Work.Kernels.imagAxis]
    have ht4 : t ≤ 1 / 4 := by
      have h2 := tile_im_le_half hw
      linarith
    have hge : 4 ≤ t⁻¹ := by
      rw [le_inv_comm₀ (by norm_num : (0:ℝ) < 4) ht]
      simpa using ht4
    have hle := tile_im_le_half hw
    rw [him] at hle
    linarith


/-- **The tile bound from the two one-sided tile bounds.**  If the two halves `K_±` of the
CKMRV kernel obey the sharp flat "below the pole" bound on the tiles `n + E`, then so does the
kernel `K = (K_+ + K_-)/2` itself, in the exact shape of
`Work.Asymptotics.Kaxis_tile_flat_below_pole`. -/
theorem Kaxis_tile_flat_of_parts (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hplus : ∃ C N K c : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ K ∧ 0 < c ∧
      ∀ (w : ℍ) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ KEpsilon →
        ∀ (t : ℝ) (ht : 0 < t), t ≤ w.im / 2 →
          ‖Work.Kernels.KPlus d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)‖
            ≤ C * (Work.Kernels.scale w) ^ N * (1 + t⁻¹) ^ K * Real.exp (-(c / t)))
    (hminus : ∃ C N K c : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ K ∧ 0 < c ∧
      ∀ (w : ℍ) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ KEpsilon →
        ∀ (t : ℝ) (ht : 0 < t), t ≤ w.im / 2 →
          ‖Work.Kernels.KMinus ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)‖
            ≤ C * (Work.Kernels.scale w) ^ N * (1 + t⁻¹) ^ K * Real.exp (-(c / t)))
    (N : ℝ) (hN : 0 ≤ N) :
    ∃ c N' : ℝ, 0 ≤ c ∧ 0 ≤ N' ∧ ∀ (w : ℍ) (n : ℤ),
      (n = 1 ∨ n = -1) → w ∈ KEpsilon → ∀ t : ℝ, 0 < t →
      t ≤ min 1 (w.im / 2) →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t‖
        ≤ c * (Work.Kernels.scale w) ^ N' * t ^ N := by
  obtain ⟨C₁, N₁, K₁, c₁, hC₁, hN₁, hK₁, hc₁, hb₁⟩ := hplus
  obtain ⟨C₂, N₂, K₂, c₂, hC₂, hN₂, hK₂, hc₂, hb₂⟩ := hminus
  obtain ⟨K₀, hK₀pos, hK₀⟩ := exp_neg_div_le_mul_rpow' (min c₁ c₂) (max K₁ K₂ + N) (lt_min hc₁ hc₂)
  refine ⟨max (max C₁ C₂ * 2 ^ max K₁ K₂) 1 * K₀, max N₁ N₂,
    mul_nonneg (le_trans zero_le_one (le_max_right _ _)) hK₀pos.le,
    le_max_of_le_left hN₁, fun w n hn hw t ht htmin => ?_⟩
  have htle : t ≤ w.im / 2 := le_trans htmin (min_le_right _ _)
  have ht1 : t ≤ 1 := le_trans htmin (min_le_left _ _)
  have hsc1 : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
  have hsc0 : (0 : ℝ) < Work.Kernels.scale w := Work.Kernels.scale_pos w
  have h₁ := hb₁ w n hn hw t ht htle
  have h₂ := hb₂ w n hn hw t ht htle
  -- combine
  have hKaxis : Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
      = Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht) := by
    rw [Work.Kernels.Kaxis, dif_pos ht]
  rw [hKaxis, Work.Kernels.Kfun]
  have hcomb : ‖(Work.Kernels.KPlus d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)
        + Work.Kernels.KMinus ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)) / 2‖
      ≤ max C₁ C₂ * (Work.Kernels.scale w) ^ max N₁ N₂ * (1 + t⁻¹) ^ max K₁ K₂
          * Real.exp (-(min c₁ c₂ / t)) := by
    have hsum : ‖Work.Kernels.KPlus d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)
          + Work.Kernels.KMinus ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)‖
        ≤ C₁ * (Work.Kernels.scale w) ^ N₁ * (1 + t⁻¹) ^ K₁ * Real.exp (-(min c₁ c₂ / t))
          + C₂ * (Work.Kernels.scale w) ^ N₂ * (1 + t⁻¹) ^ K₂ * Real.exp (-(min c₁ c₂ / t)) := by
      have hc1 : Real.exp (-(c₁ / t)) ≤ Real.exp (-(min c₁ c₂ / t)) := by
        rw [Real.exp_le_exp, neg_le_neg_iff]
        exact div_le_div_of_nonneg_right (min_le_left _ _) ht.le
      have hc2 : Real.exp (-(c₂ / t)) ≤ Real.exp (-(min c₁ c₂ / t)) := by
        rw [Real.exp_le_exp, neg_le_neg_iff]
        exact div_le_div_of_nonneg_right (min_le_right _ _) ht.le
      have h₁' : ‖Work.Kernels.KPlus d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)‖
          ≤ C₁ * (Work.Kernels.scale w) ^ N₁ * (1 + t⁻¹) ^ K₁
              * Real.exp (-(min c₁ c₂ / t)) :=
        le_trans h₁ (mul_le_mul_of_nonneg_left hc1 (by positivity))
      have h₂' : ‖Work.Kernels.KMinus ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)‖
          ≤ C₂ * (Work.Kernels.scale w) ^ N₂ * (1 + t⁻¹) ^ K₂
              * Real.exp (-(min c₁ c₂ / t)) :=
        le_trans h₂ (mul_le_mul_of_nonneg_left hc2 (by positivity))
      exact le_trans (norm_add_le _ _) (add_le_add h₁' h₂')
    have h1t : (0 : ℝ) < 1 + t⁻¹ := by positivity
    have he : (0 : ℝ) < Real.exp (-(min c₁ c₂ / t)) := Real.exp_pos _
    have hC : C₁ ≤ max C₁ C₂ := le_max_left _ _
    have hC' : C₂ ≤ max C₁ C₂ := le_max_right _ _
    have hN : (Work.Kernels.scale w) ^ N₁ ≤ (Work.Kernels.scale w) ^ max N₁ N₂ :=
      Real.rpow_le_rpow_of_exponent_le hsc1 (le_max_left _ _)
    have hN' : (Work.Kernels.scale w) ^ N₂ ≤ (Work.Kernels.scale w) ^ max N₁ N₂ :=
      Real.rpow_le_rpow_of_exponent_le hsc1 (le_max_right _ _)
    have hKt : (1 + t⁻¹) ^ K₁ ≤ (1 + t⁻¹) ^ max K₁ K₂ :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [inv_nonneg.mpr ht.le]) (le_max_left _ _)
    have hKt' : (1 + t⁻¹) ^ K₂ ≤ (1 + t⁻¹) ^ max K₁ K₂ :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [inv_nonneg.mpr ht.le]) (le_max_right _ _)
    have hmaxC : (0 : ℝ) ≤ max C₁ C₂ := le_trans hC₁.le (le_max_left _ _)
    have hsN : (0 : ℝ) ≤ (Work.Kernels.scale w) ^ max N₁ N₂ := Real.rpow_nonneg hsc0.le _
    have hmaxK : (0 : ℝ) ≤ max K₁ K₂ := le_max_of_le_left hK₁
    have h1tK : (0 : ℝ) ≤ (1 + t⁻¹) ^ max K₁ K₂ :=
      Real.rpow_nonneg (by linarith [inv_nonneg.mpr ht.le]) _
    have e1 : C₁ * (Work.Kernels.scale w) ^ N₁ * (1 + t⁻¹) ^ K₁ * Real.exp (-(min c₁ c₂ / t))
        ≤ max C₁ C₂ * (Work.Kernels.scale w) ^ max N₁ N₂ * (1 + t⁻¹) ^ max K₁ K₂
            * Real.exp (-(min c₁ c₂ / t)) := by
      have hm1 : C₁ * (Work.Kernels.scale w) ^ N₁
          ≤ max C₁ C₂ * (Work.Kernels.scale w) ^ max N₁ N₂ :=
        mul_le_mul hC hN (Real.rpow_nonneg hsc0.le _) hmaxC
      have hm2 : (1 + t⁻¹) ^ K₁ * Real.exp (-(min c₁ c₂ / t))
          ≤ (1 + t⁻¹) ^ max K₁ K₂ * Real.exp (-(min c₁ c₂ / t)) :=
        mul_le_mul_of_nonneg_right hKt he.le
      calc C₁ * (Work.Kernels.scale w) ^ N₁ * (1 + t⁻¹) ^ K₁ * Real.exp (-(min c₁ c₂ / t))
          = (C₁ * (Work.Kernels.scale w) ^ N₁) * ((1 + t⁻¹) ^ K₁ * Real.exp (-(min c₁ c₂ / t))) := by
            ring
        _ ≤ (max C₁ C₂ * (Work.Kernels.scale w) ^ max N₁ N₂)
              * ((1 + t⁻¹) ^ max K₁ K₂ * Real.exp (-(min c₁ c₂ / t))) :=
            mul_le_mul hm1 hm2 (by positivity) (by positivity)
        _ = max C₁ C₂ * (Work.Kernels.scale w) ^ max N₁ N₂ * (1 + t⁻¹) ^ max K₁ K₂
              * Real.exp (-(min c₁ c₂ / t)) := by ring
    have e2 : C₂ * (Work.Kernels.scale w) ^ N₂ * (1 + t⁻¹) ^ K₂ * Real.exp (-(min c₁ c₂ / t))
        ≤ max C₁ C₂ * (Work.Kernels.scale w) ^ max N₁ N₂ * (1 + t⁻¹) ^ max K₁ K₂
            * Real.exp (-(min c₁ c₂ / t)) := by
      have hm1 : C₂ * (Work.Kernels.scale w) ^ N₂
          ≤ max C₁ C₂ * (Work.Kernels.scale w) ^ max N₁ N₂ :=
        mul_le_mul hC' hN' (Real.rpow_nonneg hsc0.le _) hmaxC
      have hm2 : (1 + t⁻¹) ^ K₂ * Real.exp (-(min c₁ c₂ / t))
          ≤ (1 + t⁻¹) ^ max K₁ K₂ * Real.exp (-(min c₁ c₂ / t)) :=
        mul_le_mul_of_nonneg_right hKt' he.le
      calc C₂ * (Work.Kernels.scale w) ^ N₂ * (1 + t⁻¹) ^ K₂ * Real.exp (-(min c₁ c₂ / t))
          = (C₂ * (Work.Kernels.scale w) ^ N₂) * ((1 + t⁻¹) ^ K₂ * Real.exp (-(min c₁ c₂ / t))) := by
            ring
        _ ≤ (max C₁ C₂ * (Work.Kernels.scale w) ^ max N₁ N₂)
              * ((1 + t⁻¹) ^ max K₁ K₂ * Real.exp (-(min c₁ c₂ / t))) :=
            mul_le_mul hm1 hm2 (by positivity) (by positivity)
        _ = max C₁ C₂ * (Work.Kernels.scale w) ^ max N₁ N₂ * (1 + t⁻¹) ^ max K₁ K₂
              * Real.exp (-(min c₁ c₂ / t)) := by ring
    calc ‖(Work.Kernels.KPlus d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)
          + Work.Kernels.KMinus ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)) / 2‖
        = ‖Work.Kernels.KPlus d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)
          + Work.Kernels.KMinus ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)‖ / 2 := by
          rw [norm_div]; norm_num
      _ ≤ (C₁ * (Work.Kernels.scale w) ^ N₁ * (1 + t⁻¹) ^ K₁ * Real.exp (-(min c₁ c₂ / t))
          + C₂ * (Work.Kernels.scale w) ^ N₂ * (1 + t⁻¹) ^ K₂ * Real.exp (-(min c₁ c₂ / t))) / 2 :=
          div_le_div_of_nonneg_right hsum (by norm_num)
      _ ≤ (max C₁ C₂ * (Work.Kernels.scale w) ^ max N₁ N₂ * (1 + t⁻¹) ^ max K₁ K₂
            * Real.exp (-(min c₁ c₂ / t))
          + max C₁ C₂ * (Work.Kernels.scale w) ^ max N₁ N₂ * (1 + t⁻¹) ^ max K₁ K₂
            * Real.exp (-(min c₁ c₂ / t))) / 2 :=
          div_le_div_of_nonneg_right (add_le_add e1 e2) (by norm_num)
      _ = max C₁ C₂ * (Work.Kernels.scale w) ^ max N₁ N₂ * (1 + t⁻¹) ^ max K₁ K₂
            * Real.exp (-(min c₁ c₂ / t)) := by ring
  -- convert the `t`-powers
  have hpow : (1 + t⁻¹) ^ max K₁ K₂ ≤ 2 ^ max K₁ K₂ * t ^ (-(max K₁ K₂)) := by
    have h1 : (1 + t⁻¹) ≤ 2 * t⁻¹ := by
      have : (1 : ℝ) ≤ t⁻¹ := (one_le_inv₀ ht).mpr ht1
      linarith
    calc (1 + t⁻¹) ^ max K₁ K₂ ≤ (2 * t⁻¹) ^ max K₁ K₂ :=
          Real.rpow_le_rpow (by have h : (0:ℝ) < t⁻¹ := inv_pos.mpr ht; linarith) h1
            (le_max_of_le_left hK₁)
      _ = 2 ^ max K₁ K₂ * t ^ (-(max K₁ K₂)) := by
          rw [Real.mul_rpow (by norm_num) (by positivity), Real.inv_rpow ht.le,
            Real.rpow_neg ht.le]
  have hexp : Real.exp (-(min c₁ c₂ / t)) ≤ K₀ * t ^ (max K₁ K₂ + N) := hK₀ t ht ht1
  have hexp' : t ^ (-(max K₁ K₂)) * Real.exp (-(min c₁ c₂ / t)) ≤ K₀ * t ^ N := by
    have h1 : t ^ (-(max K₁ K₂)) * (K₀ * t ^ (max K₁ K₂ + N))
        = K₀ * (t ^ (-(max K₁ K₂)) * t ^ (max K₁ K₂ + N)) := by ring
    calc t ^ (-(max K₁ K₂)) * Real.exp (-(min c₁ c₂ / t))
        ≤ t ^ (-(max K₁ K₂)) * (K₀ * t ^ (max K₁ K₂ + N)) :=
          mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg ht.le _)
      _ = K₀ * t ^ N := by
          rw [h1, ← Real.rpow_add ht, show -(max K₁ K₂) + (max K₁ K₂ + N) = N by ring]
  have hstep : max C₁ C₂ * (Work.Kernels.scale w) ^ max N₁ N₂ * (1 + t⁻¹) ^ max K₁ K₂
      * Real.exp (-(min c₁ c₂ / t))
      ≤ (max C₁ C₂ * 2 ^ max K₁ K₂) * (Work.Kernels.scale w) ^ max N₁ N₂ * (K₀ * t ^ N) := by
    calc max C₁ C₂ * (Work.Kernels.scale w) ^ max N₁ N₂ * (1 + t⁻¹) ^ max K₁ K₂
          * Real.exp (-(min c₁ c₂ / t))
        = (max C₁ C₂ * (Work.Kernels.scale w) ^ max N₁ N₂)
            * ((1 + t⁻¹) ^ max K₁ K₂ * Real.exp (-(min c₁ c₂ / t))) := by ring
      _ ≤ (max C₁ C₂ * (Work.Kernels.scale w) ^ max N₁ N₂)
            * ((2 ^ max K₁ K₂ * t ^ (-(max K₁ K₂))) * Real.exp (-(min c₁ c₂ / t))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg _)) (by positivity)
      _ = (max C₁ C₂ * (Work.Kernels.scale w) ^ max N₁ N₂) * 2 ^ max K₁ K₂
            * (t ^ (-(max K₁ K₂)) * Real.exp (-(min c₁ c₂ / t))) := by ring
      _ ≤ (max C₁ C₂ * (Work.Kernels.scale w) ^ max N₁ N₂) * 2 ^ max K₁ K₂ * (K₀ * t ^ N) :=
          mul_le_mul_of_nonneg_left hexp' (by positivity)
      _ = (max C₁ C₂ * 2 ^ max K₁ K₂) * (Work.Kernels.scale w) ^ max N₁ N₂ * (K₀ * t ^ N) := by
          ring
  refine le_trans hcomb (le_trans hstep ?_)
  have h5 : (0 : ℝ) ≤ (Work.Kernels.scale w) ^ max N₁ N₂ := Real.rpow_nonneg hsc0.le _
  have h6 : (0 : ℝ) ≤ t ^ N := Real.rpow_nonneg ht.le N
  calc (max C₁ C₂ * 2 ^ max K₁ K₂) * (Work.Kernels.scale w) ^ max N₁ N₂ * (K₀ * t ^ N)
      = K₀ * (max C₁ C₂ * 2 ^ max K₁ K₂) * ((Work.Kernels.scale w) ^ max N₁ N₂ * t ^ N) := by ring
    _ ≤ K₀ * (max (max C₁ C₂ * 2 ^ max K₁ K₂) 1) * ((Work.Kernels.scale w) ^ max N₁ N₂ * t ^ N) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_max_left _ _) hK₀pos.le)
          (mul_nonneg h5 h6)
    _ = max (max C₁ C₂ * 2 ^ max K₁ K₂) 1 * K₀ * (Work.Kernels.scale w) ^ max N₁ N₂ * t ^ N := by ring

end Work.Asymptotics
