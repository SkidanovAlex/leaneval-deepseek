import Mathlib
import Submission.Work.Pert.Basic

/-!
# PERT · `Work.Pert.scale_lattice`

The gates of Shishikura (A.1.7)(ii) keep distance `≥ ξ/2` from the lattice `ℤ/α`: this is the
elementary two-cone geometry below, requiring only `InF1 α` (`|Im α| < Re α`).

The two conjuncts are `gate_lattice_plus` / `gate_lattice_minus` of `Submission/Work/Pert/gate.lean`,
which are `private` there; the proofs (and the small private helpers they use) are copied verbatim
into this file so that they can be imported by other areas.
-/

namespace Work.Pert

open MandelDim
open Complex

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

private lemma half_le_norm_of_re_add_abs_im {ζ : ℂ} {ξ : ℝ} (h : ξ ≤ ζ.re + |ζ.im|) :
    ξ / 2 ≤ ‖ζ‖ := by
  have h1 : |ζ.re| ≤ ‖ζ‖ := Complex.abs_re_le_norm ζ
  have h2 : |ζ.im| ≤ ‖ζ‖ := Complex.abs_im_le_norm ζ
  have h3 : ζ.re ≤ |ζ.re| := le_abs_self ζ.re
  linarith

private lemma half_le_norm_of_abs_re_add_abs_im {ζ : ℂ} {ξ : ℝ} (h : ξ < |ζ.re| + |ζ.im|) :
    ξ / 2 ≤ ‖ζ‖ := by
  have h1 : |ζ.re| ≤ ‖ζ‖ := Complex.abs_re_le_norm ζ
  have h2 : |ζ.im| ≤ ‖ζ‖ := Complex.abs_im_le_norm ζ
  linarith

private lemma one_div_re_pos {α : ℂ} (hα : MandelDim.InF1 α) : 0 < (1 / α).re := by
  simp only [MandelDim.InF1] at hα
  have hre : 0 < α.re := by have := abs_nonneg α.im; linarith
  have hne : α ≠ 0 := by intro h; rw [h] at hre; simp at hre
  have hns : 0 < Complex.normSq α := Complex.normSq_pos.mpr hne
  rw [Complex.div_re]
  simp only [Complex.one_re, Complex.one_im, zero_mul, zero_div, one_mul, add_zero]
  exact div_pos hre hns

private lemma one_div_im_abs_lt {α : ℂ} (hα : MandelDim.InF1 α) :
    |(1 / α).im| < (1 / α).re := by
  simp only [MandelDim.InF1] at hα
  have hre : 0 < α.re := by have := abs_nonneg α.im; linarith
  have hne : α ≠ 0 := by intro h; rw [h] at hre; simp at hre
  have hns : 0 < Complex.normSq α := Complex.normSq_pos.mpr hne
  rw [Complex.div_re, Complex.div_im]
  simp only [Complex.one_re, Complex.one_im, zero_mul, zero_div, one_mul, add_zero, sub_zero,
    zero_sub]
  rw [abs_neg, abs_div, abs_of_pos hns, div_lt_div_iff_of_pos_right hns]
  exact hα

private theorem gate_lattice_plus {α : ℂ} {ξ : ℝ} {w : ℂ} (hξ : 0 < ξ) (hα : MandelDim.InF1 α)
    (hw : w ∈ MandelDim.Qreg (some (ξ : ℂ)) (some (-(ξ : ℂ) + 1 / α))) (k : ℤ) :
    ξ / 2 ≤ ‖w - (k : ℂ) / α‖ := by
  set A : ℂ := 1 / α with hA
  have hp : 0 < A.re := by rw [hA]; exact one_div_re_pos hα
  have hq : |A.im| ≤ A.re := le_of_lt (by rw [hA]; exact one_div_im_abs_lt hα)
  have hdiv : (k : ℂ) / α = (k : ℂ) * A := by rw [hA, one_div, div_eq_mul_inv]
  rw [hdiv]
  -- the two region conditions, in coordinates
  have h1 : -|w.im| < w.re - ξ := by
    have h := hw.1 (ξ : ℂ) (by simp)
    have e : (w - (ξ : ℂ)).im = w.im := by simp
    have e' : (w - (ξ : ℂ)).re = w.re - ξ := by simp
    rwa [e, e'] at h
  have h2 : w.re + ξ - A.re < |w.im - A.im| := by
    have h := hw.2 (-(ξ : ℂ) + A) (by simp [hA])
    have e : (w - (-(ξ : ℂ) + A)).re = w.re + ξ - A.re := by
      simp only [Complex.sub_re, Complex.add_re, Complex.neg_re, Complex.ofReal_re]; ring
    have e' : (w - (-(ξ : ℂ) + A)).im = w.im - A.im := by
      simp only [Complex.sub_im, Complex.add_im, Complex.neg_im, Complex.ofReal_im]; ring
    rwa [e, e'] at h
  have hre : ∀ j : ℤ, (w - (j : ℂ) * A).re = w.re - (j : ℝ) * A.re := by
    intro j; rw [Complex.sub_re, Complex.mul_re]; simp
  have him : ∀ j : ℤ, (w - (j : ℂ) * A).im = w.im - (j : ℝ) * A.im := by
    intro j; rw [Complex.sub_im, Complex.mul_im]; simp
  -- k ≤ 0 : use the condition at b₁ = ξ
  have keyA : ∀ j : ℤ, j ≤ 0 → ξ ≤ (w - (j : ℂ) * A).re + |(w - (j : ℂ) * A).im| := by
    intro j hj
    have hj' : (j : ℝ) ≤ 0 := by exact_mod_cast hj
    have hjabs : |(j : ℝ)| = -(j : ℝ) := abs_of_nonpos hj'
    have hm : (0 : ℝ) ≤ -(j : ℝ) := by linarith
    have hwe : w.im = (w - (j : ℂ) * A).im + (j : ℝ) * A.im := by rw [him j]; ring
    have hle : |w.im| ≤ |(w - (j : ℂ) * A).im| + (-(j : ℝ)) * A.re := by
      rw [hwe]
      have h3 : |(j : ℝ) * A.im| ≤ (-(j : ℝ)) * A.re := by
        rw [abs_mul, hjabs]
        exact mul_le_mul_of_nonneg_left hq hm
      calc |(w - (j : ℂ) * A).im + (j : ℝ) * A.im|
          ≤ |(w - (j : ℂ) * A).im| + |(j : ℝ) * A.im| := abs_add_le _ _
        _ ≤ |(w - (j : ℂ) * A).im| + (-(j : ℝ)) * A.re := by linarith
    have hwr : w.re = (w - (j : ℂ) * A).re + (j : ℝ) * A.re := by rw [hre j]; ring
    calc ξ ≤ w.re + |w.im| := le_of_lt (by linarith [h1])
      _ = (w - (j : ℂ) * A).re + (j : ℝ) * A.re + |w.im| := by rw [hwr]
      _ ≤ (w - (j : ℂ) * A).re + (j : ℝ) * A.re
            + (|(w - (j : ℂ) * A).im| + (-(j : ℝ)) * A.re) := by linarith [hle]
      _ = (w - (j : ℂ) * A).re + |(w - (j : ℂ) * A).im| := by ring
  -- k ≥ 1 : use the condition at b₂ = -ξ + 1/α
  have keyB : ∀ j : ℤ, 1 ≤ j → (w - (j : ℂ) * A).re + ξ < |(w - (j : ℂ) * A).im| := by
    intro j hj
    have hj' : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    have hcoef : (0 : ℝ) ≤ (j : ℝ) - 1 := by linarith
    have hwe : w.im - A.im = (w - (j : ℂ) * A).im + ((j : ℝ) - 1) * A.im := by rw [him j]; ring
    have hle : |w.im - A.im| ≤ |(w - (j : ℂ) * A).im| + ((j : ℝ) - 1) * A.re := by
      rw [hwe]
      have h3 : |((j : ℝ) - 1) * A.im| ≤ ((j : ℝ) - 1) * A.re := by
        rw [abs_mul, abs_of_nonneg hcoef]
        exact mul_le_mul_of_nonneg_left hq hcoef
      calc |(w - (j : ℂ) * A).im + ((j : ℝ) - 1) * A.im|
          ≤ |(w - (j : ℂ) * A).im| + |((j : ℝ) - 1) * A.im| := abs_add_le _ _
        _ ≤ |(w - (j : ℂ) * A).im| + ((j : ℝ) - 1) * A.re := by linarith
    have hwr : w.re + ξ - A.re
        = (w - (j : ℂ) * A).re + ξ + ((j : ℝ) - 1) * A.re := by rw [hre j]; ring
    have h3 : (w - (j : ℂ) * A).re + ξ + ((j : ℝ) - 1) * A.re < |w.im - A.im| := by
      rw [← hwr]; exact h2
    linarith [h3, hle]
  rcases le_total k 0 with hk | hk
  · exact half_le_norm_of_re_add_abs_im (keyA k hk)
  · rcases eq_or_lt_of_le hk with h0 | hpos
    · exact half_le_norm_of_re_add_abs_im (keyA k (le_of_eq h0.symm))
    · have hk1 : (1 : ℤ) ≤ k := hpos
      have hsrc : (w - (k : ℂ) * A).re + ξ < |(w - (k : ℂ) * A).im| := keyB k hk1
      have h4 : ξ < |(w - (k : ℂ) * A).re| + |(w - (k : ℂ) * A).im| := by
        rcases le_total 0 (w - (k : ℂ) * A).re with hr | hr
        · rw [abs_of_nonneg hr]; linarith [hsrc, abs_nonneg (w - (k : ℂ) * A).im]
        · rw [abs_of_nonpos hr]; linarith [hsrc]
      exact half_le_norm_of_abs_re_add_abs_im h4

private theorem gate_lattice_minus {α : ℂ} {ξ : ℝ} {w : ℂ} (hξ : 0 < ξ) (hα : MandelDim.InF1 α)
    (hw : w ∈ MandelDim.Qreg (some ((ξ : ℂ) - 1 / α)) (some (-(ξ : ℂ)))) (k : ℤ) :
    ξ / 2 ≤ ‖w - (k : ℂ) / α‖ := by
  set A : ℂ := 1 / α with hA
  have hp : 0 < A.re := by rw [hA]; exact one_div_re_pos hα
  have hq : |A.im| ≤ A.re := le_of_lt (by rw [hA]; exact one_div_im_abs_lt hα)
  have hdiv : (k : ℂ) / α = (k : ℂ) * A := by rw [hA, one_div, div_eq_mul_inv]
  rw [hdiv]
  have h1 : w.re - ξ + A.re > -|w.im + A.im| := by
    have h := hw.1 ((ξ : ℂ) - A) (by simp [hA])
    have e : (w - ((ξ : ℂ) - A)).re = w.re - ξ + A.re := by
      simp only [Complex.sub_re, Complex.ofReal_re]; ring
    have e' : (w - ((ξ : ℂ) - A)).im = w.im + A.im := by
      simp only [Complex.sub_im, Complex.ofReal_im]; ring
    rwa [e, e'] at h
  have h2 : w.re + ξ < |w.im| := by
    have h := hw.2 (-(ξ : ℂ)) (by simp)
    have e : (w - (-(ξ : ℂ))).re = w.re + ξ := by
      simp only [Complex.sub_re, Complex.neg_re, Complex.ofReal_re]; ring
    have e' : (w - (-(ξ : ℂ))).im = w.im := by
      simp only [Complex.sub_im, Complex.neg_im, Complex.ofReal_im]; ring
    rwa [e, e'] at h
  have hre : ∀ j : ℤ, (w - (j : ℂ) * A).re = w.re - (j : ℝ) * A.re := by
    intro j; rw [Complex.sub_re, Complex.mul_re]; simp
  have him : ∀ j : ℤ, (w - (j : ℂ) * A).im = w.im - (j : ℝ) * A.im := by
    intro j; rw [Complex.sub_im, Complex.mul_im]; simp
  -- 0 ≤ k : use the condition at b₂ = -ξ
  have keyA : ∀ j : ℤ, 0 ≤ j → (w - (j : ℂ) * A).re + ξ < |(w - (j : ℂ) * A).im| := by
    intro j hj
    have hj' : (0 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    have hwe : w.im = (w - (j : ℂ) * A).im + (j : ℝ) * A.im := by rw [him j]; ring
    have hle : |w.im| ≤ |(w - (j : ℂ) * A).im| + (j : ℝ) * A.re := by
      rw [hwe]
      have h3 : |(j : ℝ) * A.im| ≤ (j : ℝ) * A.re := by
        rw [abs_mul, abs_of_nonneg hj']
        exact mul_le_mul_of_nonneg_left hq hj'
      calc |(w - (j : ℂ) * A).im + (j : ℝ) * A.im|
          ≤ |(w - (j : ℂ) * A).im| + |(j : ℝ) * A.im| := abs_add_le _ _
        _ ≤ |(w - (j : ℂ) * A).im| + (j : ℝ) * A.re := by linarith
    have hwr : w.re + ξ = (w - (j : ℂ) * A).re + ξ + (j : ℝ) * A.re := by rw [hre j]; ring
    have h3 : (w - (j : ℂ) * A).re + ξ + (j : ℝ) * A.re < |w.im| := by
      rw [← hwr]; exact h2
    linarith [h3, hle]
  -- k ≤ -1 : use the condition at b₁ = ξ - 1/α
  have keyB : ∀ j : ℤ, j ≤ -1 → ξ ≤ (w - (j : ℂ) * A).re + |(w - (j : ℂ) * A).im| := by
    intro j hj
    have hj' : (j : ℝ) ≤ -1 := by exact_mod_cast hj
    set m : ℝ := -((j : ℝ) + 1) with hm_def
    have hm : 0 ≤ m := by rw [hm_def]; linarith
    have hwe : w.im + A.im = (w - (j : ℂ) * A).im - m * A.im := by rw [him j, hm_def]; ring
    have hle : |w.im + A.im| ≤ |(w - (j : ℂ) * A).im| + m * A.re := by
      rw [hwe]
      have h3 : |m * A.im| ≤ m * A.re := by
        rw [abs_mul, abs_of_nonneg hm]
        exact mul_le_mul_of_nonneg_left hq hm
      calc |(w - (j : ℂ) * A).im - m * A.im|
          = |(w - (j : ℂ) * A).im + -(m * A.im)| := by ring_nf
        _ ≤ |(w - (j : ℂ) * A).im| + |-(m * A.im)| := abs_add_le _ _
        _ = |(w - (j : ℂ) * A).im| + |m * A.im| := by rw [abs_neg]
        _ ≤ |(w - (j : ℂ) * A).im| + m * A.re := by linarith
    have hwr : w.re - ξ + A.re = (w - (j : ℂ) * A).re - m * A.re - ξ := by
      rw [hre j, hm_def]; ring
    have h3 : -|w.im + A.im| < (w - (j : ℂ) * A).re - m * A.re - ξ := by
      rw [← hwr]; exact h1
    linarith [h3, hle]
  rcases lt_or_ge k 0 with hk | hk
  · have hk1 : k ≤ -1 := by omega
    exact half_le_norm_of_re_add_abs_im (keyB k hk1)
  · have hsrc : (w - (k : ℂ) * A).re + ξ < |(w - (k : ℂ) * A).im| := keyA k hk
    have h4 : ξ < |(w - (k : ℂ) * A).re| + |(w - (k : ℂ) * A).im| := by
      rcases le_total 0 (w - (k : ℂ) * A).re with hr | hr
      · rw [abs_of_nonneg hr]; linarith [hsrc, abs_nonneg (w - (k : ℂ) * A).im]
      · rw [abs_of_nonpos hr]; linarith [hsrc]
    exact half_le_norm_of_abs_re_add_abs_im h4


-- This is the conjunction of the two PRIVATE theorems `gate_lattice_plus` and
-- `gate_lattice_minus` already fully proved in Submission/Work/Pert/gate.lean (lines ~313-465).
-- They are private there, so they cannot be imported: please copy those two proofs (and the small
-- private helpers they use: `one_div_re_pos`, `one_div_im_abs_lt`,
-- `half_le_norm_of_re_add_abs_im`, `half_le_norm_of_abs_re_add_abs_im`) into the new file verbatim.
theorem scale_lattice {α : ℂ} {ξ : ℝ} (hξ : 0 < ξ) (hα : MandelDim.InF1 α) :
    (∀ {w : ℂ}, w ∈ MandelDim.Qreg (some (ξ : ℂ)) (some (-(ξ : ℂ) + 1 / α)) →
        ∀ k : ℤ, ξ / 2 ≤ ‖w - (k : ℂ) / α‖) ∧
      (∀ {w : ℂ}, w ∈ MandelDim.Qreg (some ((ξ : ℂ) - 1 / α)) (some (-(ξ : ℂ))) →
        ∀ k : ℤ, ξ / 2 ≤ ‖w - (k : ℂ) / α‖) := by
  refine ⟨?_, ?_⟩
  · intro w hw k
    exact gate_lattice_plus hξ hα hw k
  · intro w hw k
    exact gate_lattice_minus hξ hα hw k

end

end Work.Pert
