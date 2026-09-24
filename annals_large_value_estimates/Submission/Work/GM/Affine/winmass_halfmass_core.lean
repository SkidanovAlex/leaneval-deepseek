import Mathlib
import Submission.Work.GM.Affine.setup
import Submission.Work.GM.Affine.tent_defs
import Submission.Work.GM.Affine.periodization_identity
import Submission.Work.GM.Affine.periodization_tsum_finsum
import Submission.Work.GM.Affine.tent_cos_integral
import Submission.Work.GM.Affine.twisted_periodization
import Submission.Work.GM.Affine.integral_periodization_sq

/-!
# The half-mass core of GM §9

The main content of this file is the elementary "positive definite" inequality: for a finite
nonnegative sequence `a` and `0 < T ≤ 1/2`,

  `(T/2) * ∑_ℓ a_ℓ ^ 2 ≤ ∫_0^T ‖∑_ℓ a_ℓ e (ℓ u)‖ ^ 2 du`.

Its proof uses the triangular weight `tent T` of `Work.GM.Affine.tent_defs`: the quadratic form
`∫ tent T u * ‖∑ a_ℓ e (ℓ u)‖ ^ 2 du = ∑_{ℓ,m} a_ℓ a_m c (ℓ - m)` has nonnegative coefficients
`c (d) = ∫ tent T u * cos (2 π d u) du ≥ 0`, so it dominates `c 0 * ∑ a_ℓ ^ 2 = T ^ 2 ∑ a_ℓ ^ 2`;
and since `tent T ≤ T · 1_{[-T,T]}`, the same integral is at most `2 T ∫_0^T ‖∑ a_ℓ e (ℓ u)‖ ^ 2 du`.

Feeding this into the twisted periodization identity for `h` (sampling = periodization) gives
`(T/2) ∫ h ^ 2 ≤ ∫_0^T ∑'_ℓ ‖Fhat h (ℓ + u)‖ ^ 2 du`, which is the target
`Work.GM.Affine.winmass_halfmass_core` with `θ = 1/2`.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.GM.Affine

noncomputable section

/-! ## Elementary facts about `efun` -/

lemma efun_im (x : ℝ) : (efun x).im = Real.sin (2 * Real.pi * x) := by
  rw [efun]
  rw [show (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.exp_ofReal_mul_I_im _

lemma efun_re (x : ℝ) : (efun x).re = Real.cos (2 * Real.pi * x) := by
  rw [efun]
  rw [show (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.exp_ofReal_mul_I_re _

lemma efun_conj (x : ℝ) : star (efun x) = efun (-x) := by
  refine Complex.ext ?_ ?_
  · rw [Complex.star_def, Complex.conj_re, efun_re, efun_re]
    rw [show 2 * Real.pi * -x = -(2 * Real.pi * x) by ring, Real.cos_neg]
  · rw [Complex.star_def, Complex.conj_im, efun_im, efun_im]
    rw [show 2 * Real.pi * -x = -(2 * Real.pi * x) by ring, Real.sin_neg]

lemma star_ofReal_apply (r : ℝ) : star ((r : ℝ) : ℂ) = ((r : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.conj_ofReal]

lemma continuous_efun : Continuous efun := by unfold efun; fun_prop

/-- Expansion of the squared modulus of a finite exponential sum with nonnegative (real)
coefficients into a double cosine sum. -/
lemma normSq_exp_sum (s : Finset ℤ) (a : ℤ → ℝ) (u : ℝ) :
    ‖∑ ℓ ∈ s, ((a ℓ : ℝ) : ℂ) * efun ((ℓ : ℝ) * u)‖ ^ 2
      = ∑ ℓ ∈ s, ∑ m ∈ s,
          (a ℓ * a m) * Real.cos (2 * Real.pi * (((ℓ : ℝ) - (m : ℝ)) * u)) := by
  set A : ℂ := ∑ ℓ ∈ s, ((a ℓ : ℝ) : ℂ) * efun ((ℓ : ℝ) * u) with hA
  have hconj : A * star A
      = ∑ ℓ ∈ s, ∑ m ∈ s, ((a ℓ * a m : ℝ) : ℂ) * efun (((ℓ : ℝ) - (m : ℝ)) * u) := by
    rw [hA, star_sum]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun ℓ hℓ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [star_mul, efun_conj, star_ofReal_apply]
    have he : efun ((ℓ : ℝ) * u) * efun (-((m : ℝ) * u)) = efun (((ℓ : ℝ) - (m : ℝ)) * u) := by
      rw [← efun_add]; congr 1; ring
    calc ((a ℓ : ℝ) : ℂ) * efun ((ℓ : ℝ) * u) * (efun (-((m : ℝ) * u)) * ((a m : ℝ) : ℂ))
        = ((a ℓ : ℝ) : ℂ) * ((a m : ℝ) : ℂ)
            * (efun ((ℓ : ℝ) * u) * efun (-((m : ℝ) * u))) := by ring
      _ = ((a ℓ : ℝ) : ℂ) * ((a m : ℝ) : ℂ) * efun (((ℓ : ℝ) - (m : ℝ)) * u) := by rw [he]
      _ = (((a ℓ * a m : ℝ)) : ℂ) * efun (((ℓ : ℝ) - (m : ℝ)) * u) := by
            rw [← Complex.ofReal_mul]
  have h1 : (A * star A).re = ‖A‖ ^ 2 := by
    rw [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im,
      ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  rw [← h1, hconj, Complex.re_sum]
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Complex.re_ofReal_mul, efun_re]

/-- The sequence inequality: for a finite nonnegative family `a` and `0 < T ≤ 1/2`,
`(T/2) ∑ a_ℓ ^ 2 ≤ ∫_0^T ‖∑_ℓ a_ℓ e (ℓ u)‖ ^ 2 du`, given the two elementary facts about the
Fourier coefficients of the tent weight `c d = ∫ tent T u * cos (2 π d u) du` (nonnegativity and
`c 0 = T ^ 2`). -/
lemma seq_lower_core {T : ℝ} (hT : 0 < T) (hT2 : T ≤ 1 / 2) (s : Finset ℤ) (a : ℤ → ℝ)
    (ha : ∀ ℓ ∈ s, 0 ≤ a ℓ)
    (hc : ∀ d : ℤ,
      0 ≤ ∫ u in (-(1 / 2) : ℝ)..(1 / 2), tent T u * Real.cos (2 * Real.pi * (d : ℝ) * u))
    (hc0 : (∫ u in (-(1 / 2) : ℝ)..(1 / 2), tent T u) = T ^ 2) :
    (T / 2) * (∑ ℓ ∈ s, (a ℓ) ^ 2) ≤
      (∫ u in (0 : ℝ)..T, ‖∑ ℓ ∈ s, ((a ℓ : ℝ) : ℂ) * efun ((ℓ : ℝ) * u)‖ ^ 2) := by
  set A : ℝ → ℂ := fun u => ∑ ℓ ∈ s, ((a ℓ : ℝ) : ℂ) * efun ((ℓ : ℝ) * u) with hAdef
  have hAc : Continuous A := by
    rw [hAdef]
    exact continuous_finsetSum _ (fun ℓ hℓ =>
      continuous_const.mul (continuous_efun.comp (continuous_const.mul continuous_id)))
  have hsummand : ∀ ℓ ∈ s, ∀ m ∈ s, Continuous (fun u : ℝ =>
      (a ℓ * a m) * (tent T u * Real.cos (2 * Real.pi * (((ℓ : ℝ) - (m : ℝ)) * u)))) := by
    intro ℓ hℓ m hm
    exact continuous_const.mul ((tent_continuous T).mul
      (Real.continuous_cos.comp
        ((continuous_id.const_mul ((ℓ : ℝ) - (m : ℝ))).const_mul (2 * Real.pi))))
  have hrow : ∀ ℓ ∈ s, Continuous (fun u : ℝ => ∑ m ∈ s,
      (a ℓ * a m) * (tent T u * Real.cos (2 * Real.pi * (((ℓ : ℝ) - (m : ℝ)) * u)))) :=
    fun ℓ hℓ => continuous_finsetSum _ (fun m hm => hsummand ℓ hℓ m hm)
  have hpt : ∀ u : ℝ, tent T u * ‖A u‖ ^ 2 = ∑ ℓ ∈ s, ∑ m ∈ s,
      (a ℓ * a m) * (tent T u * Real.cos (2 * Real.pi * (((ℓ : ℝ) - (m : ℝ)) * u))) := by
    intro u
    rw [hAdef, normSq_exp_sum]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ℓ hℓ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    ring
  have hInt : (∫ u in (-(1 / 2) : ℝ)..(1 / 2), tent T u * ‖A u‖ ^ 2)
      = ∑ ℓ ∈ s, ∑ m ∈ s, (a ℓ * a m) *
          (∫ u in (-(1 / 2) : ℝ)..(1 / 2),
            tent T u * Real.cos (2 * Real.pi * (((ℓ : ℝ) - (m : ℝ)) * u))) := by
    rw [intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall (fun u _ => hpt u))]
    rw [intervalIntegral.integral_finsetSum (fun ℓ hℓ => (hrow ℓ hℓ).intervalIntegrable _ _)]
    refine Finset.sum_congr rfl fun ℓ hℓ => ?_
    rw [intervalIntegral.integral_finsetSum (fun m hm => (hsummand ℓ hℓ m hm).intervalIntegrable _ _)]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [intervalIntegral.integral_const_mul]
  have hnonneg : ∀ ℓ ∈ s, ∀ m ∈ s, 0 ≤ (a ℓ * a m) *
      (∫ u in (-(1 / 2) : ℝ)..(1 / 2),
        tent T u * Real.cos (2 * Real.pi * (((ℓ : ℝ) - (m : ℝ)) * u))) := by
    intro ℓ hℓ m hm
    refine mul_nonneg (mul_nonneg (ha ℓ hℓ) (ha m hm)) ?_
    have h := hc (ℓ - m)
    have hcast : (((ℓ - m : ℤ)) : ℝ) = ((ℓ : ℝ) - (m : ℝ)) := by push_cast; ring
    have heq : (∫ u in (-(1 / 2) : ℝ)..(1 / 2),
          tent T u * Real.cos (2 * Real.pi * (((ℓ : ℝ) - (m : ℝ)) * u)))
        = ∫ u in (-(1 / 2) : ℝ)..(1 / 2),
          tent T u * Real.cos (2 * Real.pi * (((ℓ - m : ℤ)) : ℝ) * u) := by
      have harg : ∀ u : ℝ, 2 * Real.pi * (((ℓ : ℝ) - (m : ℝ)) * u)
          = 2 * Real.pi * (((ℓ - m : ℤ)) : ℝ) * u := by
        intro u; rw [hcast]; ring
      refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun u _ => ?_)
      simp only [harg u]
    rw [heq]
    exact h
  have hsum_low : (∑ ℓ ∈ s, (a ℓ * a ℓ) *
      (∫ u in (-(1 / 2) : ℝ)..(1 / 2),
        tent T u * Real.cos (2 * Real.pi * (((ℓ : ℝ) - (ℓ : ℝ)) * u))))
      ≤ ∑ ℓ ∈ s, ∑ m ∈ s, (a ℓ * a m) *
          (∫ u in (-(1 / 2) : ℝ)..(1 / 2),
            tent T u * Real.cos (2 * Real.pi * (((ℓ : ℝ) - (m : ℝ)) * u))) :=
    Finset.sum_le_sum fun ℓ hℓ => Finset.single_le_sum (fun m hm => hnonneg ℓ hℓ m hm) hℓ
  have hdiag : (∑ ℓ ∈ s, (a ℓ * a ℓ) *
      (∫ u in (-(1 / 2) : ℝ)..(1 / 2),
        tent T u * Real.cos (2 * Real.pi * (((ℓ : ℝ) - (ℓ : ℝ)) * u))))
      = T ^ 2 * ∑ ℓ ∈ s, (a ℓ) ^ 2 := by
    have hc_ell : ∀ ℓ : ℤ, (∫ u in (-(1 / 2) : ℝ)..(1 / 2),
        tent T u * Real.cos (2 * Real.pi * (((ℓ : ℝ) - (ℓ : ℝ)) * u))) = T ^ 2 := by
      intro ℓ
      have h0 : (fun u : ℝ => tent T u * Real.cos (2 * Real.pi * (((ℓ : ℝ) - (ℓ : ℝ)) * u)))
          = fun u : ℝ => tent T u := by
        funext u
        rw [show ((ℓ : ℝ) - (ℓ : ℝ)) = 0 by ring, zero_mul, mul_zero, Real.cos_zero, mul_one]
      rw [h0, hc0]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ℓ hℓ => ?_
    rw [hc_ell ℓ]; ring
  have hlow : T ^ 2 * ∑ ℓ ∈ s, (a ℓ) ^ 2
      ≤ (∫ u in (-(1 / 2) : ℝ)..(1 / 2), tent T u * ‖A u‖ ^ 2) := by
    rw [hInt, ← hdiag]
    exact hsum_low
  have hcontA : Continuous (fun u : ℝ => tent T u * ‖A u‖ ^ 2) :=
    (tent_continuous T).mul (hAc.norm.pow 2)
  have hcontP : Continuous (fun u : ℝ => T * ‖A u‖ ^ 2) :=
    continuous_const.mul (hAc.norm.pow 2)
  have hnormnn : ∀ u : ℝ, 0 ≤ ‖A u‖ ^ 2 := fun u => sq_nonneg _
  have hle : ∀ u ∈ Set.Icc (-T) T, tent T u * ‖A u‖ ^ 2 ≤ T * ‖A u‖ ^ 2 := fun u _ =>
    mul_le_mul_of_nonneg_right (tent_le_of_nonneg hT.le u) (hnormnn u)
  have hmid : (∫ u in (-T)..T, tent T u * ‖A u‖ ^ 2)
      ≤ (∫ u in (-T)..T, T * ‖A u‖ ^ 2) :=
    intervalIntegral.integral_mono_on (by linarith) (hcontA.intervalIntegrable _ _)
      (hcontP.intervalIntegrable _ _) hle
  have hzero₁ : (∫ u in (-(1 / 2) : ℝ)..(-T), tent T u * ‖A u‖ ^ 2) = 0 := by
    rw [← intervalIntegral.integral_zero (a := (-(1 / 2) : ℝ)) (b := -T)]
    refine intervalIntegral.integral_congr fun u hu => ?_
    have hmem : T ≤ |u| := by
      rw [Set.uIcc_of_le (by linarith)] at hu
      rw [abs_of_neg (by linarith [hu.2] : u < 0)]
      linarith [hu.2]
    rw [tent_eq_zero_of_le hmem, zero_mul]
  have hzero₂ : (∫ u in T..(1 / 2), tent T u * ‖A u‖ ^ 2) = 0 := by
    rw [← intervalIntegral.integral_zero (a := T) (b := (1 / 2 : ℝ))]
    refine intervalIntegral.integral_congr fun u hu => ?_
    have hmem : T ≤ |u| := by
      rw [Set.uIcc_of_le hT2] at hu
      rw [abs_of_pos (by linarith [hu.1] : 0 < u)]
      linarith [hu.1]
    rw [tent_eq_zero_of_le hmem, zero_mul]
  have hsplit₁ : (∫ u in (-(1 / 2) : ℝ)..(1 / 2), tent T u * ‖A u‖ ^ 2)
      = (∫ u in (-(1 / 2) : ℝ)..(-T), tent T u * ‖A u‖ ^ 2)
        + (∫ u in (-T)..(1 / 2), tent T u * ‖A u‖ ^ 2) :=
    (intervalIntegral.integral_add_adjacent_intervals (hcontA.intervalIntegrable _ _)
      (hcontA.intervalIntegrable _ _)).symm
  have hsplit₂ : (∫ u in (-T)..(1 / 2), tent T u * ‖A u‖ ^ 2)
      = (∫ u in (-T)..T, tent T u * ‖A u‖ ^ 2)
        + (∫ u in T..(1 / 2), tent T u * ‖A u‖ ^ 2) :=
    (intervalIntegral.integral_add_adjacent_intervals (hcontA.intervalIntegrable _ _)
      (hcontA.intervalIntegrable _ _)).symm
  have hneg : ∀ v : ℝ, A (-v) = star (A v) := by
    intro v
    rw [hAdef, star_sum]
    refine Finset.sum_congr rfl fun ℓ hℓ => ?_
    rw [star_mul, efun_conj, star_ofReal_apply, mul_comm]
    congr 1
    ring_nf
  have heven : (∫ u in (-T)..0, ‖A u‖ ^ 2) = (∫ u in (0 : ℝ)..T, ‖A u‖ ^ 2) := by
    have h := intervalIntegral.integral_comp_neg (fun u : ℝ => ‖A u‖ ^ 2) (a := (0 : ℝ)) (b := T)
    rw [neg_zero] at h
    rw [← h]
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun u _ => ?_)
    rw [hneg u, norm_star]
  have hsplit₃ : (∫ u in (-T)..T, ‖A u‖ ^ 2) = 2 * (∫ u in (0 : ℝ)..T, ‖A u‖ ^ 2) := by
    have h1 : (∫ u in (-T)..0, ‖A u‖ ^ 2) + (∫ u in (0 : ℝ)..T, ‖A u‖ ^ 2)
        = (∫ u in (-T)..T, ‖A u‖ ^ 2) :=
      intervalIntegral.integral_add_adjacent_intervals (a := -T) (b := 0) (c := T)
        ((hAc.norm.pow 2).intervalIntegrable (μ := volume) (-T) 0)
        ((hAc.norm.pow 2).intervalIntegrable (μ := volume) 0 T)
    rw [← h1, heven]; ring_nf
  have hupper : (∫ u in (-(1 / 2) : ℝ)..(1 / 2), tent T u * ‖A u‖ ^ 2)
      ≤ 2 * T * (∫ u in (0 : ℝ)..T, ‖A u‖ ^ 2) := by
    rw [hsplit₁, hsplit₂, hzero₁, hzero₂]
    simp only [zero_add, add_zero]
    calc (∫ u in (-T)..T, tent T u * ‖A u‖ ^ 2)
        ≤ (∫ u in (-T)..T, T * ‖A u‖ ^ 2) := hmid
      _ = T * (∫ u in (-T)..T, ‖A u‖ ^ 2) := by rw [intervalIntegral.integral_const_mul]
      _ = T * (2 * (∫ u in (0 : ℝ)..T, ‖A u‖ ^ 2)) := by rw [hsplit₃]
      _ = 2 * T * (∫ u in (0 : ℝ)..T, ‖A u‖ ^ 2) := by ring_nf
  have hmain : T ^ 2 * ∑ ℓ ∈ s, (a ℓ) ^ 2 ≤ 2 * T * (∫ u in (0 : ℝ)..T, ‖A u‖ ^ 2) :=
    le_trans hlow hupper
  have hAeval : (∫ u in (0 : ℝ)..T, ‖A u‖ ^ 2)
      = ∫ u in (0 : ℝ)..T, ‖∑ ℓ ∈ s, ((a ℓ : ℝ) : ℂ) * efun ((ℓ : ℝ) * u)‖ ^ 2 := by
    congr 1 with u
  rw [hAeval] at hmain
  nlinarith [hmain, hT]

/-- The finite-sum quadratic form used in the proof of `winmass_halfmass_core`. -/
private noncomputable def winG (h : ℝ → ℝ) (s : Finset ℤ) (u y : ℝ) : ℝ :=
  ‖∑ ℓ ∈ s, ((h (y + (ℓ : ℝ)) : ℝ) : ℂ) * efun ((ℓ : ℝ) * u)‖ ^ 2

private lemma winG_cont₁ {h : ℝ → ℝ} (hcont : Continuous h) (s : Finset ℤ) :
    Continuous (fun p : ℝ × ℝ => winG h s p.1 p.2) := by
  unfold winG
  refine (continuous_finsetSum _ (fun ℓ hℓ => ?_)).norm.pow 2
  have h1 : Continuous (fun p : ℝ × ℝ => ((h (p.2 + (ℓ : ℝ)) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (hcont.comp (continuous_snd.add continuous_const))
  have h2 : Continuous (fun p : ℝ × ℝ => efun ((ℓ : ℝ) * p.1)) :=
    continuous_efun.comp (continuous_const.mul continuous_fst)
  exact h1.mul h2

private lemma winG_cont₂ {h : ℝ → ℝ} (hcont : Continuous h) (s : Finset ℤ) :
    Continuous (fun p : ℝ × ℝ => winG h s p.2 p.1) := by
  unfold winG
  refine (continuous_finsetSum _ (fun ℓ hℓ => ?_)).norm.pow 2
  have h1 : Continuous (fun p : ℝ × ℝ => ((h (p.1 + (ℓ : ℝ)) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (hcont.comp (continuous_fst.add continuous_const))
  have h2 : Continuous (fun p : ℝ × ℝ => efun ((ℓ : ℝ) * p.2)) :=
    continuous_efun.comp (continuous_const.mul continuous_snd)
  exact h1.mul h2

/-- The sequence inequality, with the tent's Fourier coefficients supplied by
`Work.GM.Affine.tent_cos_integral`. -/
lemma seq_lower {T : ℝ} (hT : 0 < T) (hT2 : T ≤ 1 / 2) (s : Finset ℤ) (a : ℤ → ℝ)
    (ha : ∀ ℓ ∈ s, 0 ≤ a ℓ) :
    (T / 2) * (∑ ℓ ∈ s, (a ℓ) ^ 2) ≤
      (∫ u in (0 : ℝ)..T, ‖∑ ℓ ∈ s, ((a ℓ : ℝ) : ℂ) * efun ((ℓ : ℝ) * u)‖ ^ 2) := by
  refine seq_lower_core hT hT2 s a ha ?_ ?_
  · intro d
    rw [tent_cos_integral hT hT2 d]
    split_ifs with hd
    · positivity
    · exact div_nonneg (sq_nonneg _) (by positivity)
  · simpa using tent_cos_integral hT hT2 0

theorem winmass_halfmass_core : ∃ θ : ℝ, 0 < θ ∧ ∀ {h : ℝ → ℝ}, Continuous h → (∀ t, 0 ≤ h t) → HasCompactSupport h → ∀ {T : ℝ}, 0 < T → T ≤ 1 / 2 → θ * T * (∫ t, (h t) ^ 2) ≤ ∫ u in (0 : ℝ)..T, ∑' ℓ : ℤ, ‖Fhat h ((ℓ : ℝ) + u)‖ ^ 2 := by
  refine ⟨1 / 2, by norm_num, ?_⟩
  intro h hcont hnn hcs T hT hT2
  obtain ⟨R, hR0, hRf⟩ := exists_support_bound hcs
  obtain ⟨K, hK⟩ : ∃ K : ℕ, R + 1 ≤ (K : ℝ) := ⟨⌈R + 1⌉₊, Nat.le_ceil _⟩
  set s : Finset ℤ := Finset.Icc (-(K : ℤ)) (K : ℤ) with hs
  -- every term with index outside the window `[-K,K]` vanishes on `[0,1]`
  have hvan : ∀ y ∈ Set.Icc (0 : ℝ) 1, ∀ ℓ : ℤ, ℓ ∉ s → h (y + (ℓ : ℝ)) = 0 := by
    intro y hy ℓ hℓ
    apply hRf
    have hKabs : (K : ℝ) < |(ℓ : ℝ)| := by
      by_contra hcon
      rw [not_lt] at hcon
      refine hℓ ?_
      rw [hs, Finset.mem_Icc]
      exact ⟨by exact_mod_cast (abs_le.mp hcon).1, by exact_mod_cast (abs_le.mp hcon).2⟩
    have hy1 : |y| ≤ 1 := by rw [abs_of_nonneg hy.1]; exact hy.2
    have h2 : |(ℓ : ℝ)| ≤ |y + (ℓ : ℝ)| + |y| := by
      have h3 : |(ℓ : ℝ)| = |(y + (ℓ : ℝ)) - y| := by
        congr 1
        ring
      calc |(ℓ : ℝ)| = |(y + (ℓ : ℝ)) - y| := h3
        _ ≤ |y + (ℓ : ℝ)| + |y| := abs_sub _ _
    linarith
  have hfin : ∀ y ∈ Set.Icc (0 : ℝ) 1, ∀ u : ℝ,
      (∑' ℓ : ℤ, ((h (y + (ℓ : ℝ)) : ℝ) : ℂ) * efun ((ℓ : ℝ) * u))
        = ∑ ℓ ∈ s, ((h (y + (ℓ : ℝ)) : ℝ) : ℂ) * efun ((ℓ : ℝ) * u) := by
    intro y hy u
    refine tsum_eq_sum (fun ℓ hℓ => ?_)
    rw [hvan y hy ℓ hℓ]
    simp
  have hGcont₁ : Continuous (fun p : ℝ × ℝ => winG h s p.1 p.2) := winG_cont₁ hcont s
  have hGcont₂ : Continuous (fun p : ℝ × ℝ => winG h s p.2 p.1) := winG_cont₂ hcont s
  -- Step 1: the twisted periodization identity
  have hstep1 : (∫ u in (0 : ℝ)..T, ∑' ℓ : ℤ, ‖Fhat h ((ℓ : ℝ) + u)‖ ^ 2)
      = ∫ u in (0 : ℝ)..T, ∫ y in (0 : ℝ)..1,
          ‖∑' ℓ : ℤ, ((h (y + (ℓ : ℝ)) : ℝ) : ℂ) * efun ((ℓ : ℝ) * u)‖ ^ 2 := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun u _ => ?_)
    exact twisted_periodization hcont hcs u
  -- Step 2: the twisted periodization is a finite sum on `[0,1]`
  have hstep2 : (∫ u in (0 : ℝ)..T, ∫ y in (0 : ℝ)..1,
        ‖∑' ℓ : ℤ, ((h (y + (ℓ : ℝ)) : ℝ) : ℂ) * efun ((ℓ : ℝ) * u)‖ ^ 2)
      = ∫ u in (0 : ℝ)..T, ∫ y in (0 : ℝ)..1, winG h s u y := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun u _ => ?_)
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun y hy => ?_)
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hy
    rw [hfin y ⟨le_of_lt hy.1, hy.2⟩ u]
    rfl
  -- Step 3: Fubini
  have hstep3 : (∫ u in (0 : ℝ)..T, ∫ y in (0 : ℝ)..1, winG h s u y)
      = ∫ y in (0 : ℝ)..1, ∫ u in (0 : ℝ)..T, winG h s u y := by
    have hint : IntegrableOn (Function.uncurry (fun u y : ℝ => winG h s u y))
        (Set.uIoc (0 : ℝ) T ×ˢ Set.uIoc (0 : ℝ) 1) volume := by
      refine IntegrableOn.mono_set
        (t := Set.Icc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) (μ := volume) ?_ ?_
      · exact hGcont₁.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
      · intro p hp
        rw [Set.mem_prod, Set.uIoc_of_le (le_of_lt hT),
          Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hp
        rw [Set.mem_prod, Set.mem_Icc, Set.mem_Icc]
        exact ⟨⟨le_of_lt hp.1.1, hp.1.2⟩, ⟨le_of_lt hp.2.1, hp.2.2⟩⟩
    exact MeasureTheory.intervalIntegral_intervalIntegral_swap hint
  -- Step 4: the sequence inequality, pointwise in `y`
  have hbound : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      (T / 2) * (∑ ℓ ∈ s, (h (y + (ℓ : ℝ))) ^ 2) ≤ (∫ u in (0 : ℝ)..T, winG h s u y) := by
    intro y hy
    have h := seq_lower hT hT2 s (fun ℓ => h (y + (ℓ : ℝ))) (fun ℓ hℓ => hnn _)
    simpa only [winG] using h
  have hmono : (∫ y in (0 : ℝ)..1, (T / 2) * (∑ ℓ ∈ s, (h (y + (ℓ : ℝ))) ^ 2))
      ≤ ∫ y in (0 : ℝ)..1, ∫ u in (0 : ℝ)..T, winG h s u y := by
    refine intervalIntegral.integral_mono_on (by norm_num) ?_ ?_ ?_
    · exact (continuous_const.mul (continuous_finsetSum _ (fun ℓ hℓ =>
        (hcont.comp (continuous_id.add continuous_const)).pow 2))).intervalIntegrable
        (μ := volume) 0 1
    · have hpar : Continuous (fun y : ℝ => ∫ u in (0 : ℝ)..T, winG h s u y) := by
        have h' : Continuous (Function.uncurry (fun y u : ℝ => winG h s u y)) := hGcont₂
        have := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (μ := volume)
          (a₀ := (0 : ℝ)) (f := fun y u : ℝ => winG h s u y) h'
          (s := fun _ : ℝ => T) continuous_const
        simpa using this
      exact hpar.intervalIntegrable (μ := volume) 0 1
    · intro y hy
      exact hbound y hy
  have hfinite : (∫ y in (0 : ℝ)..1, ∑ ℓ ∈ s, (h (y + (ℓ : ℝ))) ^ 2) = ∫ y : ℝ, (h y) ^ 2 :=
    integral_periodization_sq hcont hRf hK
  have hconst : (∫ y in (0 : ℝ)..1, (T / 2) * (∑ ℓ ∈ s, (h (y + (ℓ : ℝ))) ^ 2))
      = (T / 2) * (∫ y : ℝ, (h y) ^ 2) := by
    rw [intervalIntegral.integral_const_mul, hfinite]
  calc (1 / 2) * T * (∫ t, (h t) ^ 2)
      = (T / 2) * (∫ y : ℝ, (h y) ^ 2) := by ring
    _ = (∫ y in (0 : ℝ)..1, (T / 2) * (∑ ℓ ∈ s, (h (y + (ℓ : ℝ))) ^ 2)) := hconst.symm
    _ ≤ ∫ y in (0 : ℝ)..1, ∫ u in (0 : ℝ)..T, winG h s u y := hmono
    _ = ∫ u in (0 : ℝ)..T, ∫ y in (0 : ℝ)..1, winG h s u y := hstep3.symm
    _ = ∫ u in (0 : ℝ)..T, ∫ y in (0 : ℝ)..1,
          ‖∑' ℓ : ℤ, ((h (y + (ℓ : ℝ)) : ℝ) : ℂ) * efun ((ℓ : ℝ) * u)‖ ^ 2 := hstep2.symm
    _ = ∫ u in (0 : ℝ)..T, ∑' ℓ : ℤ, ‖Fhat h ((ℓ : ℝ) + u)‖ ^ 2 := hstep1.symm

end

end Work.GM.Affine
