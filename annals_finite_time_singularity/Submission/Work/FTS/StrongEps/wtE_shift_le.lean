/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/wtE_shift_le.lean` — the shift bound for the `η`-weight `wtE`

The weight of the pure `D_z`-slots of the `ε`-scheme is
`wtE z θ = wtZ z * sEtaW θ = w z² · sin(2θ)^{-η}`, `w z = (1+z)²/z²`, `η = 99/100`
(`Submission/Work/FTS/StrongEps/Weights.lean`).  This file proves that the log-coordinate shift

  `z ↦ zShift z p₁ = z e^{-p₁}`,   `θ ↦ thShift θ p₂ = arctan (tan θ · e^{-p₂})`

changes `wtE` by at most a factor `e^{C(|p₁|+|p₂|)}`, with `C = 2`.

Both halves are elementary and are proved separately:

* **the `z`-half** — `w (z e^{-p}) = ((z + e^p)/z)²` and `((z+e^p)/(1+z)) ≤ e^{|p|}` for `z > 0`,
  whence `w (zShift z p) ≤ e^{2|p|} w z` and `wtZ (zShift z p) ≤ e^{4|p|} wtZ z`
  (the factor `e^{|p|}` of the first bound is optimal: the ratio tends to `e^{2p}` as `z → 0⁺`);
* **the `θ`-half** — writing `z`-independent quantities `s = sin θ`, `c = cos θ`, one has the exact
  identity `sin (2·thShift θ p) = sin(2θ) / (e^p c² + e^{-p} s²)` (because
  `tan (thShift θ p) = tan θ · e^{-p}` and `sin (2 arctan u) = 2u/(1+u²)`), while the denominator
  `e^p c² + e^{-p} s²` — a convex combination of `e^p` and `e^{-p}` — lies in
  `[e^{-|p|}, e^{|p|}]`.  Since `0 < η ≤ 1`, this gives `sEtaW (thShift θ p) ≤ e^{|p|} sEtaW θ`.

The two halves are combined multiplicatively; `C = 4` already suffices.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Weights

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

set_option autoImplicit false

/-! ## The elementary trigonometric identity `sin (2 arctan u) = 2u/(1+u²)` -/

theorem sin_two_mul_arctan (u : ℝ) : Real.sin (2 * Real.arctan u) = 2 * u / (1 + u ^ 2) := by
  have hpos : 0 < √(1 + u ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hsq : √(1 + u ^ 2) * √(1 + u ^ 2) = 1 + u ^ 2 := by
    rw [← sq, Real.sq_sqrt (by positivity)]
  rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
  field_simp
  rw [Real.sq_sqrt (by positivity)]

/-! ## The `z`-half: `w (zShift z p) ≤ e^{2|p|} w z`, hence `wtZ (zShift) ≤ e^{4|p|} wtZ` -/

/-- `w` is nonnegative. -/
theorem w_nonneg (z : ℝ) : 0 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w]; positivity

/-- The radial weight is shifted by at most `e^{2|p|}`:  for `z > 0` and any `p`,
`((1 + z e^{-p})/(z e^{-p}))² ≤ e^{2|p|} ((1+z)/z)²`. -/
theorem w_zShift_le (z p : ℝ) (hz : 0 < z) :
    Work.Spaces.w (zShift z p) ≤ Real.exp (2 * |p|) * Work.Spaces.w z := by
  have hone : 1 ≤ Real.exp |p| := Real.one_le_exp (abs_nonneg p)
  have hexp : Real.exp p ≤ Real.exp |p| := Real.exp_le_exp.2 (le_abs_self p)
  have h2 : z + Real.exp p ≤ Real.exp |p| * (1 + z) := by
    have h3 : z ≤ Real.exp |p| * z := by nlinarith [hz, hone]
    have h4 : z + Real.exp p ≤ Real.exp |p| * z + Real.exp |p| := add_le_add h3 hexp
    linarith [h4]
  have hsq : (z + Real.exp p) ^ 2 ≤ Real.exp (2 * |p|) * (1 + z) ^ 2 := by
    have h5 : (z + Real.exp p) ^ 2 ≤ (Real.exp |p| * (1 + z)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h2 2
    have h6 : (Real.exp |p| * (1 + z)) ^ 2 = Real.exp (2 * |p|) * (1 + z) ^ 2 := by
      rw [mul_pow]
      congr 1
      rw [show (2 : ℝ) * |p| = |p| + |p| by ring, Real.exp_add, sq]
    linarith [h5, h6.le, h6.ge]
  have hz2 : (0 : ℝ) < z ^ 2 := pow_pos hz 2
  have hw1 : Work.Spaces.w (zShift z p) = (z + Real.exp p) ^ 2 / z ^ 2 := by
    rw [Work.Spaces.w, zShift]
    have hze : z * Real.exp (-p) = z / Real.exp p := by
      rw [Real.exp_neg]; ring
    rw [hze, div_pow]
    field_simp
    ring
  have hw2 : Work.Spaces.w z = (1 + z) ^ 2 / z ^ 2 := rfl
  rw [hw1, hw2]
  calc (z + Real.exp p) ^ 2 / z ^ 2
      ≤ (Real.exp (2 * |p|) * (1 + z) ^ 2) / z ^ 2 := div_le_div_of_nonneg_right hsq hz2.le
    _ = Real.exp (2 * |p|) * ((1 + z) ^ 2 / z ^ 2) := by rw [mul_div_assoc]

theorem wtZ_zShift_le (z p : ℝ) (hz : 0 < z) :
    wtZ (zShift z p) ≤ Real.exp (4 * |p|) * wtZ z := by
  have h := w_zShift_le z p hz
  have h2 : (Real.exp (2 * |p|) * Work.Spaces.w z) ^ 2
      = Real.exp (4 * |p|) * wtZ z := by
    rw [mul_pow, wtZ]
    rw [show (4 : ℝ) * |p| = 2 * |p| + 2 * |p| by ring, Real.exp_add, sq]
  calc wtZ (zShift z p) = Work.Spaces.w (zShift z p) ^ 2 := rfl
    _ ≤ (Real.exp (2 * |p|) * Work.Spaces.w z) ^ 2 := pow_le_pow_left₀ (w_nonneg _) h 2
    _ = Real.exp (4 * |p|) * wtZ z := h2

/-! ## The `θ`-half: `sEtaW (thShift θ p) ≤ e^{|p|} sEtaW θ` -/

theorem sEtaW_thShift_le {θ p : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    sEtaW (thShift θ p) ≤ Real.exp |p| * sEtaW θ := by
  have hcosp : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
  have hsin2pos : 0 < Real.sin (2 * θ) := sin_two_pos hθ
  have hEE : Real.exp p * Real.exp (-p) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hEE' : Real.exp (-p) * Real.exp p = 1 := by rw [mul_comm, hEE]
  have hsin2 : Real.sin (2 * θ) = 2 * Real.tan θ * Real.cos θ ^ 2 := by
    rw [Real.sin_two_mul, Real.tan_eq_sin_div_cos]; field_simp
  set Dd : ℝ := Real.exp p * Real.cos θ ^ 2 + Real.exp (-p) * Real.sin θ ^ 2 with hDd
  have hDpos : 0 < Dd := by
    rw [hDd]
    have h1 : 0 < Real.exp p * Real.cos θ ^ 2 := mul_pos (Real.exp_pos p) (pow_pos hcosp 2)
    have h2 : 0 ≤ Real.exp (-p) * Real.sin θ ^ 2 :=
      mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
    linarith
  have hDle : Dd ≤ Real.exp |p| := by
    rw [hDd]
    have h1 : Real.exp p ≤ Real.exp |p| := Real.exp_le_exp.2 (le_abs_self p)
    have h2 : Real.exp (-p) ≤ Real.exp |p| := Real.exp_le_exp.2 (neg_le_abs p)
    have hs : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := by
      linarith [Real.sin_sq_add_cos_sq θ]
    calc Real.exp p * Real.cos θ ^ 2 + Real.exp (-p) * Real.sin θ ^ 2
        ≤ Real.exp |p| * Real.cos θ ^ 2 + Real.exp |p| * Real.sin θ ^ 2 :=
          add_le_add (mul_le_mul_of_nonneg_right h1 (sq_nonneg _))
            (mul_le_mul_of_nonneg_right h2 (sq_nonneg _))
      _ = Real.exp |p| := by rw [← mul_add, hs, mul_one]
  have hsinid : Real.sin (2 * thShift θ p) = Real.sin (2 * θ) / Dd := by
    rw [hDd]
    have hE : Real.exp p ≠ 0 := Real.exp_ne_zero p
    have hE' : Real.exp (-p) ≠ 0 := Real.exp_ne_zero (-p)
    have hc : Real.cos θ ≠ 0 := hcosp.ne'
    rw [thShift]
    rw [show Real.sin (2 * Real.arctan (Real.tan θ * Real.exp (-p)))
        = 2 * (Real.tan θ * Real.exp (-p)) / (1 + (Real.tan θ * Real.exp (-p)) ^ 2) from
      sin_two_mul_arctan _]
    rw [hsin2, Real.tan_eq_sin_div_cos]
    field_simp
    ring_nf
    have hkey : Real.sin θ * Real.exp (-p) * Real.cos θ ^ 2 * Real.exp p
        = Real.sin θ * Real.cos θ ^ 2 := by
      rw [show Real.sin θ * Real.exp (-p) * Real.cos θ ^ 2 * Real.exp p
          = Real.sin θ * Real.cos θ ^ 2 * (Real.exp (-p) * Real.exp p) by ring, hEE', mul_one]
    linarith [hkey]
  rw [sEtaW, sEtaW, hsinid]
  have heta0 : 0 ≤ Work.Spaces.eta := by rw [Work.Spaces.eta]; norm_num
  have heta1 : Work.Spaces.eta ≤ 1 := by rw [Work.Spaces.eta]; norm_num
  have hrw : (Real.sin (2 * θ) / Dd) ^ (-(Work.Spaces.eta))
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * Dd ^ Work.Spaces.eta := by
    rw [Real.div_rpow hsin2pos.le hDpos.le, Real.rpow_neg hDpos.le, div_inv_eq_mul]
  rw [hrw]
  have hDpow : Dd ^ Work.Spaces.eta ≤ Real.exp |p| := by
    calc Dd ^ Work.Spaces.eta ≤ (Real.exp |p|) ^ Work.Spaces.eta :=
          Real.rpow_le_rpow hDpos.le hDle heta0
      _ = Real.exp (|p| * Work.Spaces.eta) := (Real.exp_mul |p| _).symm
      _ ≤ Real.exp |p| := Real.exp_le_exp.2 (by nlinarith [abs_nonneg p, heta1])
  have hnn : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    Real.rpow_nonneg hsin2pos.le _
  calc (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * Dd ^ Work.Spaces.eta
      ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * Real.exp |p| :=
        mul_le_mul_of_nonneg_left hDpow hnn
    _ = Real.exp |p| * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by ring

/-! ## The shift bound for `wtE` -/

theorem wtE_shift_le :
    ∃ C : ℝ, 0 < C ∧ ∀ z θ p₁ p₂ : ℝ,
      0 < z → θ ∈ Set.Ioo 0 (π / 2) →
        wtE (zShift z p₁) (thShift θ p₂)
          ≤ Real.exp (C * (|p₁| + |p₂|)) * wtE z θ := by
  refine ⟨4, by norm_num, fun z θ p₁ p₂ hz hθ => ?_⟩
  simp only [wtE_eq]
  have hZ : wtZ (zShift z p₁) ≤ Real.exp (4 * |p₁|) * wtZ z := wtZ_zShift_le z p₁ hz
  have hA : sEtaW (thShift θ p₂) ≤ Real.exp |p₂| * sEtaW θ := sEtaW_thShift_le hθ
  have hA0 : 0 ≤ sEtaW (thShift θ p₂) :=
    (sEtaW_pos (thShift_mem hθ)).le
  have hZ0 : 0 ≤ Real.exp (4 * |p₁|) * wtZ z :=
    mul_nonneg (Real.exp_pos _).le (wtZ_nonneg z)
  have hθIcc : θ ∈ Set.Icc 0 (π / 2) := ⟨hθ.1.le, hθ.2.le⟩
  have hfin : 0 ≤ wtZ z * sEtaW θ := mul_nonneg (wtZ_nonneg z) (sEtaW_nonneg hθIcc)
  calc wtZ (zShift z p₁) * sEtaW (thShift θ p₂)
      ≤ (Real.exp (4 * |p₁|) * wtZ z) * (Real.exp |p₂| * sEtaW θ) :=
        mul_le_mul hZ hA hA0 hZ0
    _ = Real.exp (4 * |p₁| + |p₂|) * (wtZ z * sEtaW θ) := by
        rw [Real.exp_add]; ring
    _ ≤ Real.exp (4 * (|p₁| + |p₂|)) * (wtZ z * sEtaW θ) :=
        mul_le_mul_of_nonneg_right
          (Real.exp_le_exp.2 (by nlinarith [abs_nonneg p₂])) hfin

end Work.FTS.StrongEps
