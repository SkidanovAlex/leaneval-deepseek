import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.dzSelf1d
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.truncBound
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.boundarySeqs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T5bAux

open MeasureTheory Set Filter
open scoped Real Topology Interval

noncomputable section

/-! ## The weighted radial self-pairing with a multiplier

This file proves `dzSelf1dW`: for the radial weight `w z = (1+z)²/z²` and a multiplier `ψ`
with `|ψ| ≤ A`, `|z ψ'| ≤ B` on `(0,∞)`, one has

`|∫_0^∞ w² ψ (z Y') Y| ≤ (3A+B) ∫_0^∞ w² Y²`.

The proof follows `dzSelf1d` (the case `ψ ≡ 1`, constant `2`): the exact identity
`s = z w²` (so `s t = (1+t)⁴/t³`),

`(ψ s Y²)' = (ψ s)' Y² + 2 w² ψ (z Y') Y`, with `(ψ s)' = ψ' s + ψ s'`,

integrated over `[ε, M] ⊂ (0,∞)`, gives the truncated bound `truncBoundW_aux` below; passing
to the limit along the dyadic minimisers of `H = w² Y²` at `0` and the minimisers on
`[k+1, 2k+2]` at `∞` (as furnished by `boundarySeqs`) kills the boundary terms, and the
pointwise bounds `|ψ| ≤ A`, `|z ψ'| ≤ B`, `|s'| ≤ 4 w²` give the constants. -/

/-- The integrand `w(z)² ψ(z) (z ∂_z Y(z)) Y(z)` of the weighted self-pairing. -/
def psiSelfFW (ψ Y : ℝ → ℝ) : ℝ → ℝ :=
  fun z => (Work.Spaces.w z) ^ 2 * ψ z * ((z * deriv Y z) * Y z)

/-- The truncated form of the weighted self-pairing bound: on `[a,b] ⊂ (0,∞)` one has
`|∫_a^b w² ψ (z Y') Y| ≤ (A/2) (w(b)²Y(b)²b + w(a)²Y(a)²a) + ((B+4A)/2) ∫_a^b w² Y²`,
from the exact derivative `(ψ t (t w(t)²) Y(t)²)' = (ψ' t (t w t²) + ψ t (t w t²)') Y t²
+ 2 w t² ψ t (z Y') Y`, the FTC on `[a,b]`, and `|t w t²'| ≤ 4 w t²`, `|ψ| ≤ A`, `|t ψ'| ≤ B`. -/
theorem truncBoundW_aux {ψ Y : ℝ → ℝ} {A B : ℝ}
    (hψsm : ContDiffOn ℝ 1 ψ (Set.Ioi 0))
    (hψA : ∀ z ∈ Set.Ioi (0 : ℝ), |ψ z| ≤ A)
    (hψB : ∀ z ∈ Set.Ioi (0 : ℝ), |z * deriv ψ z| ≤ B)
    (hY : ContDiffOn ℝ 1 Y (Set.Ioi 0)) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    |∫ z in Set.Ioc a b, (Work.Spaces.w z) ^ 2 * ψ z * ((z * deriv Y z) * Y z)|
      ≤ (A / 2) * (((Work.Spaces.w b) ^ 2 * (Y b) ^ 2) * b
            + ((Work.Spaces.w a) ^ 2 * (Y a) ^ 2) * a)
        + ((B + 4 * A) / 2) * ∫ z in Set.Ioc a b, (Work.Spaces.w z) ^ 2 * (Y z) ^ 2 := by
  have hA0 : 0 ≤ A := by
    have h1 : |ψ 1| ≤ A := hψA 1 (by norm_num)
    have h2 : (0 : ℝ) ≤ |ψ 1| := abs_nonneg _
    linarith
  have hB0 : 0 ≤ B := by
    have h1 : |(1 : ℝ) * deriv ψ 1| ≤ B := hψB 1 (by norm_num)
    have h2 : (0 : ℝ) ≤ |(1 : ℝ) * deriv ψ 1| := abs_nonneg _
    linarith
  have hIoc1 : (∫ z in Set.Ioc a b, (Work.Spaces.w z) ^ 2 * ψ z * ((z * deriv Y z) * Y z))
      = ∫ z in a..b, (Work.Spaces.w z) ^ 2 * ψ z * ((z * deriv Y z) * Y z) :=
    (intervalIntegral.integral_of_le hab).symm
  have hIoc2 : (∫ z in Set.Ioc a b, (Work.Spaces.w z) ^ 2 * (Y z) ^ 2)
      = ∫ z in a..b, (Work.Spaces.w z) ^ 2 * (Y z) ^ 2 :=
    (intervalIntegral.integral_of_le hab).symm
  rw [hIoc1, hIoc2]
  have huI : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab
  have hsub : Set.Icc a b ⊆ Set.Ioi 0 := fun z hz => lt_of_lt_of_le ha hz.1
  have hYd : ∀ z ∈ Set.Icc a b, HasDerivAt Y (deriv Y z) z := fun z hz =>
    ((hY.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioi.mem_nhds (hsub hz))).hasDerivAt
  have hψd : ∀ z ∈ Set.Icc a b, HasDerivAt ψ (deriv ψ z) z := fun z hz =>
    ((hψsm.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioi.mem_nhds (hsub hz))).hasDerivAt
  have hYc : ContinuousOn Y (Set.Icc a b) := (hY.continuousOn).mono hsub
  have hψc : ContinuousOn ψ (Set.Icc a b) := (hψsm.continuousOn).mono hsub
  have hYdc : ContinuousOn (deriv Y) (Set.Icc a b) :=
    (hY.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).mono hsub
  have hψdc : ContinuousOn (deriv ψ) (Set.Icc a b) :=
    (hψsm.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).mono hsub
  have hw : ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Icc a b) := by
    change ContinuousOn (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (Set.Icc a b)
    refine ContinuousOn.div ?_ ?_ (fun z hz => pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le ha hz.1)))
    · fun_prop
    · fun_prop
  have hW'c : ContinuousOn (fun z : ℝ => ((1 + z) ^ 3 * (z - 3)) / z ^ 4) (Set.Icc a b) := by
    refine ContinuousOn.div ?_ ?_ (fun z hz => pow_ne_zero 4 (ne_of_gt (lt_of_lt_of_le ha hz.1)))
    · fun_prop
    · fun_prop
  have hInt : ∀ f : ℝ → ℝ, ContinuousOn f (Set.Icc a b) → IntervalIntegrable f volume a b :=
    fun f hf => (show ContinuousOn f (Set.uIcc a b) from by rw [huI]; exact hf).intervalIntegrable
  have habsW' : ∀ z ∈ Set.Icc a b,
      |((1 + z) ^ 3 * (z - 3)) / z ^ 4| ≤ 4 * (Work.Spaces.w z) ^ 2 :=
    fun z hz => abs_deriv_tmul_w_sq_le (hsub hz)
  have hWd : ∀ z ∈ Set.Icc a b, HasDerivAt (fun s : ℝ => s * (Work.Spaces.w s) ^ 2)
      (((1 + z) ^ 3 * (z - 3)) / z ^ 4) z := fun z hz => deriv_tmul_w_sq (hsub hz)
  -- the derivative of `t ↦ ψ t * (t (w t)²) * (Y t)²`
  have hGd : ∀ z ∈ Set.uIcc a b,
      HasDerivAt (fun t : ℝ => ψ t * (t * (Work.Spaces.w t) ^ 2) * (Y t) ^ 2)
        ((ψ z * (((1 + z) ^ 3 * (z - 3)) / z ^ 4)
            + deriv ψ z * (z * (Work.Spaces.w z) ^ 2)) * (Y z) ^ 2
          + 2 * ((Work.Spaces.w z) ^ 2 * ψ z * ((z * deriv Y z) * Y z))) z := by
    intro z hz
    rw [huI] at hz
    have h1 : HasDerivAt (fun t : ℝ => ψ t * (t * (Work.Spaces.w t) ^ 2))
        (deriv ψ z * (z * (Work.Spaces.w z) ^ 2)
          + ψ z * (((1 + z) ^ 3 * (z - 3)) / z ^ 4)) z :=
      (hψd z hz).mul (hWd z hz)
    have h2 := (hYd z hz).pow 2
    have h3 := h1.mul h2
    have hfun : (fun t : ℝ => ψ t * (t * (Work.Spaces.w t) ^ 2) * (Y t) ^ 2)
        = (fun t : ℝ => ψ t * (t * (Work.Spaces.w t) ^ 2)) * (fun t : ℝ => (Y t) ^ 2) :=
      rfl
    rw [hfun]
    convert h3 using 1
    simp only [Pi.pow_apply]
    ring
  have hcont1 : ContinuousOn (fun z : ℝ => (ψ z * (((1 + z) ^ 3 * (z - 3)) / z ^ 4)
      + deriv ψ z * (z * (Work.Spaces.w z) ^ 2))) (Set.Icc a b) :=
    (hψc.mul hW'c).add (hψdc.mul (continuousOn_id.mul (hw.pow 2)))
  have hcont2 : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2 * ψ z
      * ((z * deriv Y z) * Y z)) (Set.Icc a b) :=
    ((hw.pow 2).mul hψc).mul ((continuousOn_id.mul hYdc).mul hYc)
  have hIntI1 : IntervalIntegrable
      (fun z : ℝ => (ψ z * (((1 + z) ^ 3 * (z - 3)) / z ^ 4)
          + deriv ψ z * (z * (Work.Spaces.w z) ^ 2)) * (Y z) ^ 2) volume a b :=
    hInt _ (hcont1.mul (hYc.pow 2))
  have hIntI2 : IntervalIntegrable
      (fun z : ℝ => 2 * ((Work.Spaces.w z) ^ 2 * ψ z * ((z * deriv Y z) * Y z))) volume a b :=
    hInt _ (continuousOn_const.mul hcont2)
  have hFTC : ∫ z in a..b, ((ψ z * (((1 + z) ^ 3 * (z - 3)) / z ^ 4)
          + deriv ψ z * (z * (Work.Spaces.w z) ^ 2)) * (Y z) ^ 2
        + 2 * ((Work.Spaces.w z) ^ 2 * ψ z * ((z * deriv Y z) * Y z)))
      = ψ b * (b * (Work.Spaces.w b) ^ 2) * (Y b) ^ 2
        - ψ a * (a * (Work.Spaces.w a) ^ 2) * (Y a) ^ 2 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro z hz; exact hGd z hz
    · exact hIntI1.add hIntI2
  have hsplit : (∫ z in a..b, ((ψ z * (((1 + z) ^ 3 * (z - 3)) / z ^ 4)
          + deriv ψ z * (z * (Work.Spaces.w z) ^ 2)) * (Y z) ^ 2
        + 2 * ((Work.Spaces.w z) ^ 2 * ψ z * ((z * deriv Y z) * Y z))))
      = (∫ z in a..b, (ψ z * (((1 + z) ^ 3 * (z - 3)) / z ^ 4)
          + deriv ψ z * (z * (Work.Spaces.w z) ^ 2)) * (Y z) ^ 2)
        + 2 * (∫ z in a..b, (Work.Spaces.w z) ^ 2 * ψ z * ((z * deriv Y z) * Y z)) := by
    rw [intervalIntegral.integral_add hIntI1 hIntI2, intervalIntegral.integral_const_mul]
  have hI1 : |∫ z in a..b, (ψ z * (((1 + z) ^ 3 * (z - 3)) / z ^ 4)
        + deriv ψ z * (z * (Work.Spaces.w z) ^ 2)) * (Y z) ^ 2|
      ≤ (B + 4 * A) * (∫ z in a..b, (Work.Spaces.w z) ^ 2 * (Y z) ^ 2) := by
    calc |∫ z in a..b, (ψ z * (((1 + z) ^ 3 * (z - 3)) / z ^ 4)
          + deriv ψ z * (z * (Work.Spaces.w z) ^ 2)) * (Y z) ^ 2|
        ≤ ∫ z in a..b, |(ψ z * (((1 + z) ^ 3 * (z - 3)) / z ^ 4)
          + deriv ψ z * (z * (Work.Spaces.w z) ^ 2)) * (Y z) ^ 2| :=
          intervalIntegral.abs_integral_le_integral_abs hab
      _ = ∫ z in a..b, |(ψ z * (((1 + z) ^ 3 * (z - 3)) / z ^ 4)
          + deriv ψ z * (z * (Work.Spaces.w z) ^ 2))| * (Y z) ^ 2 := by
          apply intervalIntegral.integral_congr
          intro z _
          dsimp only
          rw [abs_mul, abs_of_nonneg (sq_nonneg (Y z))]
      _ ≤ ∫ z in a..b, (B + 4 * A) * ((Work.Spaces.w z) ^ 2 * (Y z) ^ 2) := by
          apply intervalIntegral.integral_mono_on hab
          · exact hInt _ (hcont1.abs.mul (hYc.pow 2))
          · exact hInt _ (continuousOn_const.mul ((hw.pow 2).mul (hYc.pow 2)))
          · intro z hz
            have hzpos : z ∈ Set.Ioi (0 : ℝ) := hsub hz
            have h1 : |ψ z * (((1 + z) ^ 3 * (z - 3)) / z ^ 4)|
                ≤ A * (4 * (Work.Spaces.w z) ^ 2) := by
              rw [abs_mul]
              calc |ψ z| * |((1 + z) ^ 3 * (z - 3)) / z ^ 4|
                  ≤ A * |((1 + z) ^ 3 * (z - 3)) / z ^ 4| :=
                    mul_le_mul_of_nonneg_right (hψA z hzpos) (abs_nonneg _)
                _ ≤ A * (4 * (Work.Spaces.w z) ^ 2) :=
                    mul_le_mul_of_nonneg_left (habsW' z hz) hA0
            have h2 : |deriv ψ z * (z * (Work.Spaces.w z) ^ 2)|
                ≤ B * (Work.Spaces.w z) ^ 2 := by
              have hwz : (0 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
              calc |deriv ψ z * (z * (Work.Spaces.w z) ^ 2)|
                  = |z * deriv ψ z| * (Work.Spaces.w z) ^ 2 := by
                    rw [show deriv ψ z * (z * (Work.Spaces.w z) ^ 2)
                        = (z * deriv ψ z) * (Work.Spaces.w z) ^ 2 from by ring]
                    rw [abs_mul, abs_of_nonneg hwz]
                _ ≤ B * (Work.Spaces.w z) ^ 2 :=
                    mul_le_mul_of_nonneg_right (hψB z hzpos) hwz
            have hsum : |ψ z * (((1 + z) ^ 3 * (z - 3)) / z ^ 4)|
                + |deriv ψ z * (z * (Work.Spaces.w z) ^ 2)|
                ≤ (B + 4 * A) * (Work.Spaces.w z) ^ 2 := by
              linarith [h1, h2]
            calc |ψ z * (((1 + z) ^ 3 * (z - 3)) / z ^ 4)
                    + deriv ψ z * (z * (Work.Spaces.w z) ^ 2)| * (Y z) ^ 2
                ≤ (|ψ z * (((1 + z) ^ 3 * (z - 3)) / z ^ 4)|
                    + |deriv ψ z * (z * (Work.Spaces.w z) ^ 2)|) * (Y z) ^ 2 :=
                  mul_le_mul_of_nonneg_right (abs_add_le _ _) (sq_nonneg (Y z))
              _ ≤ (B + 4 * A) * ((Work.Spaces.w z) ^ 2 * (Y z) ^ 2) := by
                  calc (|ψ z * (((1 + z) ^ 3 * (z - 3)) / z ^ 4)|
                        + |deriv ψ z * (z * (Work.Spaces.w z) ^ 2)|) * (Y z) ^ 2
                      ≤ ((B + 4 * A) * (Work.Spaces.w z) ^ 2) * (Y z) ^ 2 :=
                        mul_le_mul_of_nonneg_right hsum (sq_nonneg (Y z))
                    _ = (B + 4 * A) * ((Work.Spaces.w z) ^ 2 * (Y z) ^ 2) := by ring
      _ = (B + 4 * A) * (∫ z in a..b, (Work.Spaces.w z) ^ 2 * (Y z) ^ 2) := by
          rw [intervalIntegral.integral_const_mul]
  have hkey : 2 * (∫ z in a..b, (Work.Spaces.w z) ^ 2 * ψ z * ((z * deriv Y z) * Y z))
      = (ψ b * (b * (Work.Spaces.w b) ^ 2) * (Y b) ^ 2
          - ψ a * (a * (Work.Spaces.w a) ^ 2) * (Y a) ^ 2)
        - ∫ z in a..b, (ψ z * (((1 + z) ^ 3 * (z - 3)) / z ^ 4)
            + deriv ψ z * (z * (Work.Spaces.w z) ^ 2)) * (Y z) ^ 2 := by
    linarith [hFTC, hsplit]
  have hI2 : (∫ z in a..b, (Work.Spaces.w z) ^ 2 * ψ z * ((z * deriv Y z) * Y z))
      = (1 / 2) * ((ψ b * (b * (Work.Spaces.w b) ^ 2) * (Y b) ^ 2
            - ψ a * (a * (Work.Spaces.w a) ^ 2) * (Y a) ^ 2)
          - ∫ z in a..b, (ψ z * (((1 + z) ^ 3 * (z - 3)) / z ^ 4)
              + deriv ψ z * (z * (Work.Spaces.w z) ^ 2)) * (Y z) ^ 2) := by
    linarith [hkey]
  rw [hI2]
  have hbpos : (0 : ℝ) < b := lt_of_lt_of_le ha hab
  have hBb : |ψ b * (b * (Work.Spaces.w b) ^ 2) * (Y b) ^ 2|
      ≤ A * (((Work.Spaces.w b) ^ 2 * (Y b) ^ 2) * b) := by
    have h1 : |ψ b| ≤ A := hψA b hbpos
    have h2 : (0 : ℝ) ≤ ((Work.Spaces.w b) ^ 2 * (Y b) ^ 2) * b := by positivity
    have h3 : |ψ b * (b * (Work.Spaces.w b) ^ 2) * (Y b) ^ 2|
        = |ψ b| * (((Work.Spaces.w b) ^ 2 * (Y b) ^ 2) * b) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (Y b)),
        abs_of_nonneg (mul_nonneg hbpos.le (sq_nonneg (Work.Spaces.w b)))]
      ring
    rw [h3]
    exact mul_le_mul_of_nonneg_right h1 h2
  have hBa : |ψ a * (a * (Work.Spaces.w a) ^ 2) * (Y a) ^ 2|
      ≤ A * (((Work.Spaces.w a) ^ 2 * (Y a) ^ 2) * a) := by
    have h1 : |ψ a| ≤ A := hψA a ha
    have h2 : (0 : ℝ) ≤ ((Work.Spaces.w a) ^ 2 * (Y a) ^ 2) * a := by positivity
    have h3 : |ψ a * (a * (Work.Spaces.w a) ^ 2) * (Y a) ^ 2|
        = |ψ a| * (((Work.Spaces.w a) ^ 2 * (Y a) ^ 2) * a) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (Y a)),
        abs_of_nonneg (mul_nonneg ha.le (sq_nonneg (Work.Spaces.w a)))]
      ring
    rw [h3]
    exact mul_le_mul_of_nonneg_right h1 h2
  have habstri : ∀ u v : ℝ, |u - v| ≤ |u| + |v| := by
    intro u v
    have h := abs_add_le u (-v)
    simpa [sub_eq_add_neg, abs_neg] using h
  have hBd : |(ψ b * (b * (Work.Spaces.w b) ^ 2) * (Y b) ^ 2
        - ψ a * (a * (Work.Spaces.w a) ^ 2) * (Y a) ^ 2)|
      ≤ A * (((Work.Spaces.w b) ^ 2 * (Y b) ^ 2) * b)
        + A * (((Work.Spaces.w a) ^ 2 * (Y a) ^ 2) * a) := by
    have hxb := abs_le.mp hBb
    have hxa := abs_le.mp hBa
    refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith [hxb.1, hxb.2, hxa.1, hxa.2]
  calc |(1 / 2) * ((ψ b * (b * (Work.Spaces.w b) ^ 2) * (Y b) ^ 2
            - ψ a * (a * (Work.Spaces.w a) ^ 2) * (Y a) ^ 2)
          - ∫ z in a..b, (ψ z * (((1 + z) ^ 3 * (z - 3)) / z ^ 4)
              + deriv ψ z * (z * (Work.Spaces.w z) ^ 2)) * (Y z) ^ 2)|
      = (1 / 2) * |(ψ b * (b * (Work.Spaces.w b) ^ 2) * (Y b) ^ 2
            - ψ a * (a * (Work.Spaces.w a) ^ 2) * (Y a) ^ 2)
          - ∫ z in a..b, (ψ z * (((1 + z) ^ 3 * (z - 3)) / z ^ 4)
              + deriv ψ z * (z * (Work.Spaces.w z) ^ 2)) * (Y z) ^ 2| := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    _ ≤ (1 / 2) * (|(ψ b * (b * (Work.Spaces.w b) ^ 2) * (Y b) ^ 2
            - ψ a * (a * (Work.Spaces.w a) ^ 2) * (Y a) ^ 2)|
          + |∫ z in a..b, (ψ z * (((1 + z) ^ 3 * (z - 3)) / z ^ 4)
              + deriv ψ z * (z * (Work.Spaces.w z) ^ 2)) * (Y z) ^ 2|) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply habstri
    _ ≤ (1 / 2) * ((A * (((Work.Spaces.w b) ^ 2 * (Y b) ^ 2) * b)
            + A * (((Work.Spaces.w a) ^ 2 * (Y a) ^ 2) * a))
          + (B + 4 * A) * (∫ z in a..b, (Work.Spaces.w z) ^ 2 * (Y z) ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        linarith [hBd, hI1]
    _ = (A / 2) * (((Work.Spaces.w b) ^ 2 * (Y b) ^ 2) * b
          + ((Work.Spaces.w a) ^ 2 * (Y a) ^ 2) * a)
        + ((B + 4 * A) / 2) * (∫ z in a..b, (Work.Spaces.w z) ^ 2 * (Y z) ^ 2) := by ring

theorem dzSelf1dW {ψ Y : ℝ → ℝ} {A B : ℝ}
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hψsm : ContDiffOn ℝ 1 ψ (Set.Ioi 0))
    (hψA : ∀ z ∈ Set.Ioi (0 : ℝ), |ψ z| ≤ A)
    (hψB : ∀ z ∈ Set.Ioi (0 : ℝ), |z * deriv ψ z| ≤ B)
    (hY : ContDiffOn ℝ 1 Y (Set.Ioi 0))
    (hF : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * (Y z) ^ 2) (Set.Ioi 0))
    (hD : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * (z * deriv Y z) ^ 2)
      (Set.Ioi 0)) :
    |∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2 * ψ z * ((z * deriv Y z) * Y z)|
      ≤ (3 * A + B) * ∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2 * (Y z) ^ 2 := by
  have hHint : IntegrableOn (selfH Y) (Set.Ioi 0) := by
    change IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * (Y z) ^ 2) (Set.Ioi 0)
    exact hF
  have hHnn : ∀ z, 0 ≤ selfH Y z := by
    intro z
    change 0 ≤ (Work.Spaces.w z) ^ 2 * (Y z) ^ 2
    positivity
  have hHnnI : 0 ≤ ∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2 * (Y z) ^ 2 :=
    setIntegral_nonneg measurableSet_Ioi (fun z _ => by positivity)
  change |∫ z in Set.Ioi (0 : ℝ), psiSelfFW ψ Y z|
      ≤ (3 * A + B) * ∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2 * (Y z) ^ 2
  by_cases hint : IntegrableOn (psiSelfFW ψ Y) (Set.Ioi 0)
  · obtain ⟨ε, M, hεpos, hεM, hε0, hMtop, hHε, hHM⟩ :=
      boundarySeqs (selfH Y) hHint hHnn
        (fun k => continuousOn_selfH hY (by positivity))
        (fun k => continuousOn_selfH hY (by positivity))
    have hL1 : Tendsto (fun k => ∫ z in Set.Ioc (ε k) (M k), psiSelfFW ψ Y z) atTop
        (𝓝 (∫ z in Set.Ioi 0, psiSelfFW ψ Y z)) :=
      Work.FTS.EllipticEst.zHardy_tendsto_setIntegral_Ioc (psiSelfFW ψ Y) hint hεpos hε0 hMtop
    have hL2 : Tendsto (fun k => ∫ z in Set.Ioc (ε k) (M k), selfH Y z) atTop
        (𝓝 (∫ z in Set.Ioi 0, selfH Y z)) :=
      Work.FTS.EllipticEst.zHardy_tendsto_setIntegral_Ioc (selfH Y) hHint hεpos hε0 hMtop
    have hk : ∀ k : ℕ, |∫ z in Set.Ioc (ε k) (M k), psiSelfFW ψ Y z|
        ≤ (A / 2) * (selfH Y (M k) * M k + selfH Y (ε k) * ε k)
          + ((B + 4 * A) / 2) * ∫ z in Set.Ioc (ε k) (M k), selfH Y z := by
      intro k
      have htb := truncBoundW_aux (ψ := ψ) (Y := Y) (A := A) (B := B)
        hψsm hψA hψB hY (hεpos k) (hεM k)
      simpa only [psiSelfFW, selfH] using htb
    have hbound : Tendsto
        (fun k => (A / 2) * (selfH Y (M k) * M k + selfH Y (ε k) * ε k)
          + ((B + 4 * A) / 2) * ∫ z in Set.Ioc (ε k) (M k), selfH Y z) atTop
        (𝓝 (((B + 4 * A) / 2) * ∫ z in Set.Ioi 0, selfH Y z)) := by
      have hmid : Tendsto
          (fun k => (A / 2) * (selfH Y (M k) * M k + selfH Y (ε k) * ε k)) atTop (𝓝 0) := by
        have h := (hHM.add hHε).const_mul (A / 2)
        simpa using h
      have h2 : Tendsto (fun k => ((B + 4 * A) / 2) * ∫ z in Set.Ioc (ε k) (M k), selfH Y z)
          atTop (𝓝 (((B + 4 * A) / 2) * ∫ z in Set.Ioi 0, selfH Y z)) :=
        hL2.const_mul _
      simpa using hmid.add h2
    have hmain : |∫ z in Set.Ioi 0, psiSelfFW ψ Y z|
        ≤ ((B + 4 * A) / 2) * ∫ z in Set.Ioi 0, selfH Y z :=
      le_of_tendsto_of_tendsto' hL1.abs hbound hk
    have hcoef : (B + 4 * A) / 2 ≤ 3 * A + B := by linarith
    calc |∫ z in Set.Ioi 0, psiSelfFW ψ Y z|
        ≤ ((B + 4 * A) / 2) * ∫ z in Set.Ioi 0, selfH Y z := hmain
      _ = ((B + 4 * A) / 2) * ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (Y z) ^ 2 := by
          simp only [selfH]
      _ ≤ (3 * A + B) * ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (Y z) ^ 2 :=
          mul_le_mul_of_nonneg_right hcoef hHnnI
  · rw [integral_undef hint, abs_zero]
    exact mul_nonneg (by linarith) hHnnI

end

end Work.FTS.StrongPersist.H6Pair6Aux.T5bAux
