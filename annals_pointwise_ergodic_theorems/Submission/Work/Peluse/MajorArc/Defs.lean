/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Mathlib
import Submission.Work.Peluse.Tools.dualFn_supportIn

/-!
# Vocabulary for `Work.Peluse.majorarc`

This module fixes the notation used in the proof of `Work.Peluse.PeluseMajorArc` (Peluse's
Lemma 3.10 / Lemma 8.1 in the case `ℓ = 2`):

* `ee x = exp (2 π i x)`, the additive character;
* `eeG β f`, the function `u ↦ f u · e (β u)`;
* `eeH M P β`, the weight `y ↦ e (β P y)` cut down to the interval `[1, M]`;
* `winDFT L K A s k`, the windowed discrete Fourier transform
  `∑_{n ∈ [-K,K]} A n · e (s k n / L)` of a function supported in `[-K,K]`.

The proof of `majorarc` proceeds by (i) reindexing the correlation of the dual function
`dualFn M P f₀ f₁` with the character `x ↦ e (β x)` as the triple sum
`∑_{u,y} eeG β f₀ u · f₁ (u+y) · eeH M P β y`, (ii) evaluating that triple sum by the discrete
Fourier transform of its three factors, (iii) reading off a large Weyl sum
`∑_{y ∈ [1,M]} e (β P y - ξ y)` for some `ξ ∈ [0,1)`, and (iv) applying the inverse form of
Weyl's exponential-sum estimate (`Work.KMTAreas.A4.IW`) to that real polynomial.
-/

set_option autoImplicit false

open scoped BigOperators
open Polynomial

namespace Work.Peluse

noncomputable section

/-! ## The additive character -/

/-- `ee x = exp (2 π i x)`, the additive character of `ℝ` of period `1`. -/
def ee (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))

@[simp] lemma ee_zero : ee 0 = 1 := by simp [ee]

lemma ee_add (x y : ℝ) : ee (x + y) = ee x * ee y := by
  rw [ee, ee, ee, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma ee_sub (x y : ℝ) : ee (x - y) = ee x * ee (-y) := by
  rw [← ee_add]; ring_nf

lemma ee_neg (x : ℝ) : ee (-x) = (ee x)⁻¹ := by
  have h : ee x * ee (-x) = 1 := by rw [← ee_add]; simp
  exact eq_inv_of_mul_eq_one_right h

lemma ee_norm (x : ℝ) : ‖ee x‖ = 1 := by
  rw [ee]
  have h : (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

lemma star_ee (x : ℝ) : star (ee x) = ee (-x) := by
  rw [ee, Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_ofNat]
  push_cast
  ring

/-- `e` of an integer is `1`. -/
lemma ee_int (n : ℤ) : ee (n : ℝ) = 1 := by
  have h : ee (n : ℝ) = ee (1 : ℝ) ^ n := by
    rw [ee, ee]
    have h2 : (2 * (Real.pi : ℂ) * Complex.I * ((n : ℝ) : ℂ))
        = (n : ℂ) * (2 * Real.pi * Complex.I * ((1 : ℝ) : ℂ)) := by push_cast; ring
    rw [h2, Complex.exp_int_mul]
  rw [h]
  have h1 : ee (1 : ℝ) = 1 := by
    rw [ee, Complex.exp_eq_one_iff]
    exact ⟨1, by push_cast; ring⟩
  rw [h1, one_zpow]

/-- **The kernel of the additive character**: `ee x = 1` exactly for the integers. -/
theorem ee_eq_one_iff (x : ℝ) : ee x = 1 ↔ ∃ n : ℤ, x = (n : ℝ) := by
  constructor
  · intro h
    rw [ee] at h
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
    refine ⟨n, ?_⟩
    have hI : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [Complex.I_ne_zero, Real.pi_ne_zero]
    have h2 : ((x : ℂ)) * (2 * Real.pi * Complex.I) = (n : ℂ) * (2 * Real.pi * Complex.I) := by
      rw [← hn]; ring
    have := mul_right_cancel₀ hI h2
    exact_mod_cast this
  · rintro ⟨n, rfl⟩
    exact ee_int n

/-- The two forms of `ee` used in the workspace agree. -/
lemma ee_eq_exp (x : ℝ) : ee x = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) := rfl

/-- `ee` is multiplicative in the `exp` form used in the workspace. -/
lemma exp_mul_eq_ee (β : ℝ) (x : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I * (β : ℂ) * (x : ℂ)) = ee (β * (x : ℝ)) := by
  rw [ee]
  congr 1
  push_cast
  ring

/-! ## The three factors of the triple sum -/

/-- `eeG β f = fun u => f u * ee (β u)`. -/
def eeG (β : ℝ) (f : ℤ → ℂ) : ℤ → ℂ := fun u => f u * ee (β * (u : ℝ))

/-- The weight `y ↦ ee (β (P y))`, cut down to `[1, M]`. -/
def eeH (M : ℕ) (P : Polynomial ℤ) (β : ℝ) : ℤ → ℂ :=
  fun y => if y ∈ Finset.Icc (1 : ℤ) (M : ℤ) then ee (β * ((P.eval y : ℤ) : ℝ)) else 0

@[simp] lemma eeH_apply_of_mem {M : ℕ} {P : Polynomial ℤ} {β : ℝ} {y : ℤ}
    (hy : y ∈ Finset.Icc (1 : ℤ) (M : ℤ)) :
    eeH M P β y = ee (β * ((P.eval y : ℤ) : ℝ)) := by
  simp [eeH, hy]

@[simp] lemma eeH_apply_of_not_mem {M : ℕ} {P : Polynomial ℤ} {β : ℝ} {y : ℤ}
    (hy : y ∉ Finset.Icc (1 : ℤ) (M : ℤ)) : eeH M P β y = 0 := by
  simp [eeH, hy]

/-- The windowed discrete Fourier transform `∑_{n ∈ [-K,K]} A n * ee (s k n / L)`. -/
def winDFT (L K : ℕ) (A : ℤ → ℂ) (s : ℝ) (k : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), A n * ee (s * (k : ℝ) * (n : ℝ) / (L : ℝ))

lemma winDFT_apply (L K : ℕ) (A : ℤ → ℂ) (s : ℝ) (k : ℕ) :
    winDFT L K A s k
      = ∑ n ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), A n * ee (s * (k : ℝ) * (n : ℝ) / (L : ℝ)) :=
  rfl

end

end Work.Peluse
