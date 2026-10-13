/-
Copyright: work module for the Elgindi finite-time singularity project.

# The pointwise derivative bound for the cut-off Agmon vector field

With `ρ = w² = cutRho`, `w z = (1+z)²/z²`, and `u = cutU h ψ = ρ z ψ² (z h')`, the product rule
gives, at every `z > 0`,

  `u'(z) = (ρ z)'(z) ψ(z)² (z h'(z)) + 2 (ρ z)(z) ψ(z) ψ'(z) (z h'(z)) + (ρ z)(z) ψ(z)² (h'(z) + z h''(z))`.

The three factors satisfy

* `|(ρ z)'| ≤ 3 ρ`  (`abs_deriv_cutRho_mul_id_le`, from `ρ z = (1+z)^4/z^3` and `|z-3| ≤ 3(1+z)`),
* `|z ψ'| ≤ K` pointwise by hypothesis (so `|2ρz ψ ψ' (zh')| ≤ 2K ρ |ψ| |zh'|`),
* `z (h' + z h'') = z h' + z² h'' = rDzIter 2 h` (by definition of `rDz`, `rDzIter`),

so that

  `|u'(z)| ≤ 3 ρ(z) ψ(z)² |z h'(z)| + 2 K ρ(z) |ψ(z)| |z h'(z)| + ρ(z) ψ(z)² |rDzIter 2 h z|`,

which is the estimate used in the cut-off proof of the Agmon inequality. -/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.AgmonSlice.CutDefs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AgmonFts

open MeasureTheory Set Filter
open scoped Real Topology
open Work.FTS.EllipticEst.AgmonSlice

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The derivative of `z ↦ ρ z · z` -/

private lemma cutRho_eq (z : ℝ) : cutRho z = (1 + z) ^ 4 / z ^ 4 := by
  simp only [cutRho, Work.Spaces.w, div_pow]
  ring

private lemma deriv_cutRho_mul_id {z : ℝ} (hz : 0 < z) :
    deriv (fun y : ℝ => cutRho y * y) z = (z - 3) / (1 + z) * cutRho z := by
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hfun : (fun y : ℝ => cutRho y * y) = fun y : ℝ => (1 + y) ^ 4 / y ^ 3 := by
    funext y
    rcases eq_or_ne y 0 with rfl | hy
    · norm_num [cutRho, Work.Spaces.w]
    · rw [cutRho_eq]
      field_simp
  rw [hfun]
  have hd1 : DifferentiableAt ℝ (fun w : ℝ => (1 + w) ^ 4) z := by fun_prop
  have hd2 : DifferentiableAt ℝ (fun w : ℝ => w ^ 3) z := by fun_prop
  have hd3 : (fun w : ℝ => w ^ 3) z ≠ 0 := by simpa using pow_ne_zero 3 hz0
  rw [show (fun w : ℝ => (1 + w) ^ 4 / w ^ 3)
      = (fun w : ℝ => (1 + w) ^ 4) / (fun w : ℝ => w ^ 3) from rfl]
  rw [deriv_div hd1 hd2 hd3]
  have hv1 : deriv (fun w : ℝ => (1 + w) ^ 4) z = 4 * (1 + z) ^ 3 := by
    change deriv ((fun w : ℝ => 1 + w) ^ 4) z = 4 * (1 + z) ^ 3
    rw [deriv_pow (by fun_prop : DifferentiableAt ℝ (fun w : ℝ => 1 + w) z)]
    simp
  have hv2 : deriv (fun w : ℝ => w ^ 3) z = 3 * z ^ 2 := by
    change deriv ((fun w : ℝ => w) ^ 3) z = 3 * z ^ 2
    rw [deriv_pow (by fun_prop : DifferentiableAt ℝ (fun w : ℝ => w) z)]
    simp
  rw [hv1, hv2, cutRho_eq]
  field_simp
  ring

/-- `|(ρ z)'| ≤ 3 ρ` for `z > 0`: the first summand of the product rule. -/
private lemma abs_deriv_cutRho_mul_id_le {z : ℝ} (hz : 0 < z) :
    |deriv (fun w : ℝ => cutRho w * w) z| ≤ 3 * cutRho z := by
  have h1 : 0 < 1 + z := by linarith
  have h2 : |z - 3| ≤ 3 * (1 + z) := by
    rcases le_total 3 z with h | h
    · rw [abs_of_nonneg (by linarith)]; linarith
    · rw [abs_of_nonpos (by linarith)]; linarith
  have h3 : |z - 3| / (1 + z) ≤ 3 := by
    rw [div_le_iff₀ h1]
    linarith
  rw [deriv_cutRho_mul_id hz, abs_mul, abs_div, abs_of_pos h1,
    abs_of_nonneg (cutRho_nonneg z)]
  exact mul_le_mul_of_nonneg_right h3 (cutRho_nonneg z)

private lemma contDiffOn_cutRho_mul_id :
    ContDiffOn ℝ 1 (fun y : ℝ => cutRho y * y) (Set.Ioi (0:ℝ)) := by
  have heq : (fun y : ℝ => cutRho y * y) = fun y : ℝ => (1 + y) ^ 4 / y ^ 3 := by
    funext y
    rcases eq_or_ne y 0 with rfl | hy
    · norm_num [cutRho, Work.Spaces.w]
    · rw [cutRho_eq]; field_simp
  rw [heq]
  exact ContDiffOn.div (by fun_prop) (by fun_prop) (fun y hy => pow_ne_zero 3 (ne_of_gt hy))

/-- The triangle inequality for a sum of four terms. -/
private lemma abs_sum_four_le (a b c d : ℝ) : |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  have h1 := abs_add_le (a + b + c) d
  have h2 := abs_add_le (a + b) c
  have h3 := abs_add_le a b
  linarith

/-! ## The pointwise bound -/

theorem abs_deriv_cutU_mul_le (h ψ : ℝ → ℝ) (K : ℝ)
    (hh : ContDiffOn ℝ 2 h (Set.Ioi 0)) (hψ : ContDiffOn ℝ 2 ψ (Set.Ioi 0))
    (hψ1 : ∀ z : ℝ, |ψ z| ≤ 1)
    (hK : ∀ z ∈ Set.Ioi (0 : ℝ), |z * deriv ψ z| ≤ K) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      |deriv (Work.FTS.EllipticEst.AgmonSlice.cutU h ψ) z|
        ≤ 3 * Work.FTS.EllipticEst.AgmonSlice.cutRho z * ψ z ^ 2 * |z * deriv h z|
          + 2 * K * Work.FTS.EllipticEst.AgmonSlice.cutRho z * |ψ z| * |z * deriv h z|
          + Work.FTS.EllipticEst.AgmonSlice.cutRho z * ψ z ^ 2
              * |Work.FTS.EllipticEst.rDzIter 2 h z| := by
  intro z hz
  have hz0 : 0 < z := hz
  have hρnn : 0 ≤ cutRho z := cutRho_nonneg z
  have hsqψ : |ψ z| * |ψ z| = ψ z ^ 2 := by rw [← sq, sq_abs]
  -- differentiability of the factors of `cutU h ψ` at `z`
  have hψ_at : DifferentiableAt ℝ ψ z :=
    (hψ.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hz)
  have hdh_cd : ContDiffOn ℝ 1 (deriv h) (Set.Ioi (0 : ℝ)) :=
    hh.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hdh_at : DifferentiableAt ℝ (deriv h) z :=
    (hdh_cd.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hz)
  have hA_at : DifferentiableAt ℝ (fun y : ℝ => cutRho y * y) z :=
    (contDiffOn_cutRho_mul_id.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioi.mem_nhds hz)
  have hC_at : DifferentiableAt ℝ (fun y : ℝ => y * deriv h y) z :=
    differentiableAt_id.mul hdh_at
  -- the product rule for `cutU`
  have hU : cutU h ψ = ((fun y : ℝ => cutRho y * y) * ψ * ψ) * (fun y : ℝ => y * deriv h y) := by
    funext y; simp only [cutU, Pi.mul_apply]; ring
  have hCderiv : deriv (fun y : ℝ => y * deriv h y) z = deriv h z + z * deriv (deriv h) z := by
    change deriv (id * deriv h) z = deriv h z + z * deriv (deriv h) z
    rw [deriv_mul differentiableAt_id hdh_at, deriv_id]
    simp only [id_eq, one_mul]
  have hderiv : deriv (cutU h ψ) z
      = deriv (fun y : ℝ => cutRho y * y) z * (ψ z * ψ z) * (z * deriv h z)
        + ((cutRho z * z) * deriv ψ z * ψ z) * (z * deriv h z)
        + ((cutRho z * z) * ψ z * deriv ψ z) * (z * deriv h z)
        + (cutRho z * z * (ψ z * ψ z)) * (deriv h z + z * deriv (deriv h) z) := by
    rw [hU]
    rw [deriv_mul ((hA_at.mul hψ_at).mul hψ_at) hC_at,
      deriv_mul (hA_at.mul hψ_at) hψ_at,
      deriv_mul hA_at hψ_at,
      hCderiv]
    simp only [Pi.mul_apply]
    ring_nf
  -- the first summand
  have hT1 : |deriv (fun y : ℝ => cutRho y * y) z * (ψ z * ψ z) * (z * deriv h z)|
      ≤ 3 * cutRho z * ψ z ^ 2 * (z * |deriv h z|) := by
    rw [show |deriv (fun y : ℝ => cutRho y * y) z * (ψ z * ψ z) * (z * deriv h z)|
        = |deriv (fun y : ℝ => cutRho y * y) z| * ψ z ^ 2 * (z * |deriv h z|) by
      simp only [abs_mul, abs_of_pos hz0, hsqψ]]
    have h1 := abs_deriv_cutRho_mul_id_le hz0
    have h3 := mul_le_mul_of_nonneg_right h1
      (mul_nonneg (sq_nonneg (ψ z)) (mul_nonneg hz0.le (abs_nonneg (deriv h z))))
    linarith [h3]
  have hzψ : z * |deriv ψ z| ≤ K := by
    have h := hK z hz
    rwa [abs_mul, abs_of_pos hz0] at h
  -- the two middle summands
  have hT2 : |((cutRho z * z) * deriv ψ z * ψ z) * (z * deriv h z)|
      ≤ K * cutRho z * |ψ z| * (z * |deriv h z|) := by
    rw [show |((cutRho z * z) * deriv ψ z * ψ z) * (z * deriv h z)|
        = (cutRho z * z) * |deriv ψ z| * |ψ z| * (z * |deriv h z|) by
      simp only [abs_mul, abs_of_pos hz0, abs_of_nonneg hρnn]]
    rw [show (cutRho z * z) * |deriv ψ z| * |ψ z| * (z * |deriv h z|)
        = (z * |deriv ψ z|) * cutRho z * |ψ z| * (z * |deriv h z|) by ring]
    have hstep : (z * |deriv ψ z|) * cutRho z * |ψ z| ≤ K * cutRho z * |ψ z| := by
      have hh := mul_le_mul_of_nonneg_right hzψ (mul_nonneg hρnn (abs_nonneg (ψ z)))
      linarith [hh]
    exact mul_le_mul_of_nonneg_right hstep (mul_nonneg hz0.le (abs_nonneg (deriv h z)))
  have hT3 : |((cutRho z * z) * ψ z * deriv ψ z) * (z * deriv h z)|
      ≤ K * cutRho z * |ψ z| * (z * |deriv h z|) := by
    rw [show |((cutRho z * z) * ψ z * deriv ψ z) * (z * deriv h z)|
        = (cutRho z * z) * |ψ z| * |deriv ψ z| * (z * |deriv h z|) by
      simp only [abs_mul, abs_of_pos hz0, abs_of_nonneg hρnn]]
    rw [show (cutRho z * z) * |ψ z| * |deriv ψ z| * (z * |deriv h z|)
        = (z * |deriv ψ z|) * cutRho z * |ψ z| * (z * |deriv h z|) by ring]
    have hstep : (z * |deriv ψ z|) * cutRho z * |ψ z| ≤ K * cutRho z * |ψ z| := by
      have hh := mul_le_mul_of_nonneg_right hzψ (mul_nonneg hρnn (abs_nonneg (ψ z)))
      linarith [hh]
    exact mul_le_mul_of_nonneg_right hstep (mul_nonneg hz0.le (abs_nonneg (deriv h z)))
  -- `z (h' + z h'') = rDzIter 2 h`
  have hE : z * (deriv h z + z * deriv (deriv h) z) = Work.FTS.EllipticEst.rDzIter 2 h z := by
    have hrDz_h : (Work.FTS.EllipticEst.rDz h) = fun y : ℝ => y * deriv h y := rfl
    have h2u : Work.FTS.EllipticEst.rDzIter 2 h
        = Work.FTS.EllipticEst.rDz (Work.FTS.EllipticEst.rDz h) := by
      simp only [Work.FTS.EllipticEst.rDzIter_succ, Work.FTS.EllipticEst.rDzIter_zero]
    rw [h2u, hrDz_h]
    show z * (deriv h z + z * deriv (deriv h) z) = z * deriv (fun y : ℝ => y * deriv h y) z
    rw [hCderiv]
  -- the last summand
  have hT4 : |(cutRho z * z * (ψ z * ψ z)) * (deriv h z + z * deriv (deriv h) z)|
      ≤ cutRho z * ψ z ^ 2 * |Work.FTS.EllipticEst.rDzIter 2 h z| := by
    rw [show |(cutRho z * z * (ψ z * ψ z)) * (deriv h z + z * deriv (deriv h) z)|
        = (cutRho z * z * ψ z ^ 2) * |deriv h z + z * deriv (deriv h) z| by
      simp only [abs_mul, abs_of_pos hz0, abs_of_nonneg hρnn, hsqψ]]
    rw [show (cutRho z * z * ψ z ^ 2) * |deriv h z + z * deriv (deriv h) z|
        = cutRho z * ψ z ^ 2 * (z * |deriv h z + z * deriv (deriv h) z|) by ring]
    rw [show z * |deriv h z + z * deriv (deriv h) z| = |Work.FTS.EllipticEst.rDzIter 2 h z| by
      conv_rhs => rw [← hE]
      rw [abs_mul, abs_of_pos hz0]]
  have hzabs : z * |deriv h z| = |z * deriv h z| := by rw [abs_mul, abs_of_pos hz0]
  calc |deriv (cutU h ψ) z|
      ≤ 3 * cutRho z * ψ z ^ 2 * (z * |deriv h z|)
          + K * cutRho z * |ψ z| * (z * |deriv h z|)
          + K * cutRho z * |ψ z| * (z * |deriv h z|)
          + cutRho z * ψ z ^ 2 * |Work.FTS.EllipticEst.rDzIter 2 h z| := by
        rw [hderiv]
        refine le_trans (abs_sum_four_le _ _ _ _) ?_
        linarith [hT1, hT2, hT3, hT4]
    _ = 3 * cutRho z * ψ z ^ 2 * |z * deriv h z|
          + 2 * K * cutRho z * |ψ z| * |z * deriv h z|
          + cutRho z * ψ z ^ 2 * |Work.FTS.EllipticEst.rDzIter 2 h z| := by
        rw [hzabs]
        ring

end Work.FTS.EllipticEst.AgmonFts
