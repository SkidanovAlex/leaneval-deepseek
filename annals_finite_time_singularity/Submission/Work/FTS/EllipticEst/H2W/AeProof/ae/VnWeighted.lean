import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.FTS.EllipticEst.H2W.AeProof.ae.CutSeq
import Submission.Work.FTS.EllipticEst.PropL2Cut
import Submission.Work.FTS.EllipticEst.PropL2CutKids.Wc_deriv_bdd
import Submission.Work.FTS.EllipticEst.weight_algebra_fts
import Submission.Work.FTS.EllipticEst.H2W.AeProof.ae.VnRescaledBounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The weighted transfer bounds for the shifted cutoff family `Vn`

`Vn n z = ψ((n+1)z - 2)·χ(z/(n+1))` (see `CutSeq`), `w z = (1+z)²/z²` (see `Spaces`).

The theorem `VnWeighted` proved here is the truncation ingredient of the weighted radial
energy identity: the transfer quantities `(z²·Vn n·w²)''` and `(z·Vn n·w²)'` are bounded,
*uniformly in `n`*, by a multiple of `w²`; and they converge, for each fixed `z > 0`, to the
corresponding quantities with `Vn n` replaced by `1`.

The uniform bound is a consequence of the two-scale structure together with the rescaled
derivative bounds `VnRescaledBounds` (`|z ∂_zVn n| ≤ 2M`, `|z² ∂_z²Vn n| ≤ 4M²`, uniform in
`n` and `z`) and of the elementary estimates

* `|deriv (z²w²)| ≤ 2z·w²`,  `|deriv² (z²w²)| ≤ 6·w²`,  `|deriv (zw²)| ≤ 3·w²`  (`z > 0`)

for the weight.  The transfer lemmas `vw_dderiv_bound`, `vw_deriv_bound` below are stated for
an *arbitrary* smooth `V` with such rescaled bounds, and are applied to `V = Vn n`.
-/

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.AeProof.ae

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Rational bounds for the derivatives of the radial weight -/

/-- `|deriv (z²w²)| ≤ 2z·w²` in closed form. -/
private lemma vw_g_bound (z : ℝ) (hz : 0 < z) :
    |2 * (z - 1) * (1 + z) ^ 3 / z ^ 3| ≤ 2 * (z * (Work.Spaces.w z) ^ 2) := by
  have hle : |z - 1| ≤ 1 + z := by rw [abs_le]; constructor <;> linarith
  calc |2 * (z - 1) * (1 + z) ^ 3 / z ^ 3|
      = 2 * |z - 1| * (1 + z) ^ 3 / z ^ 3 := by
        rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < z^3), abs_mul, abs_mul,
          abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
          abs_of_nonneg (by positivity : (0:ℝ) ≤ (1+z)^3)]
    _ ≤ 2 * (1 + z) * (1 + z) ^ 3 / z ^ 3 := by gcongr
    _ = 2 * (z * (Work.Spaces.w z) ^ 2) := by rw [Work.Spaces.w]; field_simp

/-- `|deriv² (z²w²)| ≤ 6w²` in closed form. -/
private lemma vw_g2_bound (z : ℝ) (hz : 0 < z) :
    |(1 + z) ^ 2 * (2 * z ^ 2 - 4 * z + 6) / z ^ 4| ≤ 6 * (Work.Spaces.w z) ^ 2 := by
  have hnum : 0 < 2 * z ^ 2 - 4 * z + 6 := by nlinarith [sq_nonneg (z - 1)]
  rw [abs_of_nonneg (by positivity)]
  rw [div_le_iff₀ (by positivity : (0:ℝ) < z ^ 4)]
  rw [Work.Spaces.w]
  rw [show 6 * ((1 + z) ^ 2 / z ^ 2) ^ 2 * z ^ 4 = 6 * (1 + z) ^ 4 from by field_simp]
  nlinarith [sq_nonneg (1 + z), sq_nonneg z, hz]

/-- `|deriv (zw²)| ≤ 3w²` in closed form. -/
private lemma vw_h_bound (z : ℝ) (hz : 0 < z) :
    |(z - 3) * (1 + z) ^ 3 / z ^ 4| ≤ 3 * (Work.Spaces.w z) ^ 2 := by
  have hle : |z - 3| ≤ 3 * (1 + z) := by rw [abs_le]; constructor <;> linarith
  calc |(z - 3) * (1 + z) ^ 3 / z ^ 4|
      = |z - 3| * (1 + z) ^ 3 / z ^ 4 := by
        rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < z^4), abs_mul,
          abs_of_nonneg (by positivity : (0:ℝ) ≤ (1+z)^3)]
    _ ≤ 3 * (1 + z) * (1 + z) ^ 3 / z ^ 4 := by gcongr
    _ = 3 * (Work.Spaces.w z) ^ 2 := by rw [Work.Spaces.w]; field_simp

/-! ## Differentiability of the weight functions away from `0` -/

private lemma vw_w_diff (z : ℝ) (hz : z ≠ 0) :
    DifferentiableAt ℝ (fun y : ℝ => Work.Spaces.w y) z := by
  simp only [Work.Spaces.w]
  exact DifferentiableAt.div (by fun_prop) (by fun_prop) (pow_ne_zero 2 hz)

private lemma vw_F_diff (z : ℝ) (hz : z ≠ 0) :
    DifferentiableAt ℝ (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z :=
  (differentiableAt_id.pow 2).mul ((vw_w_diff z hz).pow 2)

private lemma vw_G_diff (z : ℝ) (hz : z ≠ 0) :
    DifferentiableAt ℝ (fun y : ℝ => y * (Work.Spaces.w y) ^ 2) z :=
  differentiableAt_id.mul ((vw_w_diff z hz).pow 2)

/-! ## The two transfer bounds -/

/-- **First derivative transfer bound.**  If `|z ∂_zV| ≤ A` and `|V| ≤ 1`, then the first
derivative of `z·V·w²` is bounded by `(3+A)·w²`. -/
private lemma vw_deriv_bound (V : ℝ → ℝ) (hV : ContDiff ℝ ∞ V) (A : ℝ)
    (hAb : ∀ y : ℝ, |y * deriv V y| ≤ A) (hV1 : ∀ y : ℝ, |V y| ≤ 1)
    (z : ℝ) (hz : 0 < z) :
    |deriv (fun y : ℝ => y * V y * (Work.Spaces.w y) ^ 2) z|
      ≤ (3 + A) * (Work.Spaces.w z) ^ 2 := by
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hVd : Differentiable ℝ V := hV.differentiable (by simp)
  have hGd : DifferentiableAt ℝ (fun y : ℝ => y * (Work.Spaces.w y) ^ 2) z := vw_G_diff z hz0
  have hp : deriv (fun y : ℝ => y * (Work.Spaces.w y) ^ 2 * V y) z
      = deriv (fun y : ℝ => y * (Work.Spaces.w y) ^ 2) z * V z
        + (z * (Work.Spaces.w z) ^ 2) * deriv V z := by
    have h := deriv_mul hGd (hVd.differentiableAt (x := z))
    have he : (fun y : ℝ => y * (Work.Spaces.w y) ^ 2 * V y)
        = (fun y : ℝ => y * (Work.Spaces.w y) ^ 2) * V := rfl
    rw [he, h]
  have heq : (fun y : ℝ => y * V y * (Work.Spaces.w y) ^ 2)
      = fun y : ℝ => y * (Work.Spaces.w y) ^ 2 * V y := by funext y; ring
  rw [heq, hp, Work.FTS.EllipticEst.weight_algebra_fts.2.2.2.1 z hz0]
  have hV'z : |deriv V z| ≤ A / z := by
    rw [le_div_iff₀ hz]
    have h := hAb z
    rw [abs_mul, abs_of_pos hz, mul_comm] at h
    exact h
  have b1 : |(z - 3) * (1 + z) ^ 3 / z ^ 4 * V z| ≤ 3 * (Work.Spaces.w z) ^ 2 := by
    rw [abs_mul]
    calc _ ≤ (3 * (Work.Spaces.w z) ^ 2) * 1 :=
          mul_le_mul (vw_h_bound z hz) (hV1 z) (abs_nonneg _) (by positivity)
      _ = 3 * (Work.Spaces.w z) ^ 2 := by ring
  have b2 : |z * (Work.Spaces.w z) ^ 2 * deriv V z| ≤ A * (Work.Spaces.w z) ^ 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    refine le_trans (mul_le_mul_of_nonneg_left hV'z (by positivity)) ?_
    rw [show z * (Work.Spaces.w z) ^ 2 * (A / z) = A * (Work.Spaces.w z) ^ 2 from by field_simp]
  have h1 := abs_add_le ((z - 3) * (1 + z) ^ 3 / z ^ 4 * V z)
    (z * (Work.Spaces.w z) ^ 2 * deriv V z)
  linarith

/-- **Second derivative transfer bound.**  If `|z ∂_zV| ≤ A`, `|z² ∂_z²V| ≤ B` and `|V| ≤ 1`,
then the second derivative of `z²·V·w²` is bounded by `(6 + 4A + B)·w²`. -/
private lemma vw_dderiv_bound (V : ℝ → ℝ) (hV : ContDiff ℝ ∞ V) (A B : ℝ)
    (hAb : ∀ y : ℝ, |y * deriv V y| ≤ A)
    (hBb : ∀ y : ℝ, |y ^ 2 * deriv (deriv V) y| ≤ B)
    (hV1 : ∀ y : ℝ, |V y| ≤ 1) (z : ℝ) (hz : 0 < z) :
    |deriv (deriv (fun y : ℝ => y ^ 2 * V y * (Work.Spaces.w y) ^ 2)) z|
      ≤ (6 + 4 * A + B) * (Work.Spaces.w z) ^ 2 := by
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hVd : Differentiable ℝ V := hV.differentiable (by simp)
  have hV'd : Differentiable ℝ (deriv V) := (ContDiff.iterate_deriv 1 hV).differentiable (by simp)
  have hFd : DifferentiableAt ℝ (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z := vw_F_diff z hz0
  have hgd : DifferentiableAt ℝ (fun y : ℝ => 2 * (y - 1) * (1 + y) ^ 3 / y ^ 3) z :=
    DifferentiableAt.div (by fun_prop) (by fun_prop) (pow_ne_zero 3 hz0)
  -- the first derivative is, near `z`, the explicit sum of products
  have hAu : deriv (fun y : ℝ => y ^ 2 * V y * (Work.Spaces.w y) ^ 2) =ᶠ[𝓝 z]
      (fun y : ℝ => (2 * (y - 1) * (1 + y) ^ 3 / y ^ 3) * V y
        + (y ^ 2 * (Work.Spaces.w y) ^ 2) * deriv V y) := by
    filter_upwards [isOpen_ne.mem_nhds hz0] with y hy
    have hFdy : DifferentiableAt ℝ (fun t : ℝ => t ^ 2 * (Work.Spaces.w t) ^ 2) y := vw_F_diff y hy
    have hmp : deriv (fun t : ℝ => t ^ 2 * (Work.Spaces.w t) ^ 2 * V t) y
        = deriv (fun t : ℝ => t ^ 2 * (Work.Spaces.w t) ^ 2) y * V y
          + (y ^ 2 * (Work.Spaces.w y) ^ 2) * deriv V y := by
      have h := deriv_mul hFdy (hVd.differentiableAt (x := y))
      have he : (fun t : ℝ => t ^ 2 * (Work.Spaces.w t) ^ 2 * V t)
          = (fun t : ℝ => t ^ 2 * (Work.Spaces.w t) ^ 2) * V := rfl
      rw [he, h]
    have heq : (fun t : ℝ => t ^ 2 * V t * (Work.Spaces.w t) ^ 2)
        = fun t : ℝ => t ^ 2 * (Work.Spaces.w t) ^ 2 * V t := by funext t; ring
    rw [heq, hmp, Work.FTS.EllipticEst.weight_algebra_fts.2.2.1 y hy]
  have hstep : deriv (deriv (fun y : ℝ => y ^ 2 * V y * (Work.Spaces.w y) ^ 2)) z
      = deriv (fun y : ℝ => (2 * (y - 1) * (1 + y) ^ 3 / y ^ 3) * V y
          + (y ^ 2 * (Work.Spaces.w y) ^ 2) * deriv V y) z :=
    Filter.EventuallyEq.deriv_eq hAu
  -- the derivative of the rational prefactor
  have hgg : deriv (fun y : ℝ => 2 * (y - 1) * (1 + y) ^ 3 / y ^ 3) z
      = deriv (deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2)) z := by
    have hev : (fun y : ℝ => 2 * (y - 1) * (1 + y) ^ 3 / y ^ 3) =ᶠ[𝓝 z]
        deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) := by
      filter_upwards [isOpen_ne.mem_nhds hz0] with y hy
      exact (Work.FTS.EllipticEst.weight_algebra_fts.2.2.1 y hy).symm
    exact Filter.EventuallyEq.deriv_eq hev
  have hg' : HasDerivAt (fun y : ℝ => 2 * (y - 1) * (1 + y) ^ 3 / y ^ 3)
      ((1 + z) ^ 2 * (2 * z ^ 2 - 4 * z + 6) / z ^ 4) z := by
    refine hgd.hasDerivAt.congr_deriv ?_
    rw [hgg, Work.FTS.EllipticEst.weight_algebra_fts.2.2.2.2.1 z hz0]
  have hF' : HasDerivAt (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2)
      (2 * (z - 1) * (1 + z) ^ 3 / z ^ 3) z := by
    refine hFd.hasDerivAt.congr_deriv ?_
    rw [Work.FTS.EllipticEst.weight_algebra_fts.2.2.1 z hz0]
  have hVh : HasDerivAt V (deriv V z) z := hVd.differentiableAt.hasDerivAt
  have hV'h : HasDerivAt (deriv V) (deriv (deriv V) z) z := hV'd.differentiableAt.hasDerivAt
  have hval := ((hg'.mul hVh).add (hF'.mul hV'h)).deriv
  -- the rescaled bounds on the two derivatives of `V`
  have hV'z : |deriv V z| ≤ A / z := by
    rw [le_div_iff₀ hz]
    have h := hAb z
    rw [abs_mul, abs_of_pos hz, mul_comm] at h
    exact h
  have hV''z : |deriv (deriv V) z| ≤ B / z ^ 2 := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < z ^ 2)]
    have h := hBb z
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < z ^ 2), mul_comm] at h
    exact h
  have b1 : |(1 + z) ^ 2 * (2 * z ^ 2 - 4 * z + 6) / z ^ 4 * V z|
      ≤ 6 * (Work.Spaces.w z) ^ 2 := by
    rw [abs_mul]
    calc _ ≤ (6 * (Work.Spaces.w z) ^ 2) * 1 :=
          mul_le_mul (vw_g2_bound z hz) (hV1 z) (abs_nonneg _) (by positivity)
      _ = 6 * (Work.Spaces.w z) ^ 2 := by ring
  have b2 : |2 * (z - 1) * (1 + z) ^ 3 / z ^ 3 * deriv V z|
      ≤ 2 * A * (Work.Spaces.w z) ^ 2 := by
    rw [abs_mul]
    refine le_trans (mul_le_mul (vw_g_bound z hz) hV'z (abs_nonneg _) (by positivity)) ?_
    rw [show 2 * (z * (Work.Spaces.w z) ^ 2) * (A / z)
        = 2 * A * (Work.Spaces.w z) ^ 2 from by field_simp]
  have b3 : |z ^ 2 * (Work.Spaces.w z) ^ 2 * deriv (deriv V) z| ≤ B * (Work.Spaces.w z) ^ 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    refine le_trans (mul_le_mul_of_nonneg_left hV''z (by positivity)) ?_
    rw [show z ^ 2 * (Work.Spaces.w z) ^ 2 * (B / z ^ 2)
        = B * (Work.Spaces.w z) ^ 2 from by field_simp]
  have hfun : (fun y : ℝ => 2 * (y - 1) * (1 + y) ^ 3 / y ^ 3 * V y
        + y ^ 2 * (Work.Spaces.w y) ^ 2 * deriv V y)
      = ((fun y : ℝ => 2 * (y - 1) * (1 + y) ^ 3 / y ^ 3) * V
        + (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) * deriv V) := rfl
  rw [hstep, hfun, hval]
  have h1 := abs_add_le
    ((1 + z) ^ 2 * (2 * z ^ 2 - 4 * z + 6) / z ^ 4 * V z
      + 2 * (z - 1) * (1 + z) ^ 3 / z ^ 3 * deriv V z)
    (2 * (z - 1) * (1 + z) ^ 3 / z ^ 3 * deriv V z
      + z ^ 2 * (Work.Spaces.w z) ^ 2 * deriv (deriv V) z)
  have h2 := abs_add_le
    ((1 + z) ^ 2 * (2 * z ^ 2 - 4 * z + 6) / z ^ 4 * V z)
    (2 * (z - 1) * (1 + z) ^ 3 / z ^ 3 * deriv V z)
  have h3 := abs_add_le
    (2 * (z - 1) * (1 + z) ^ 3 / z ^ 3 * deriv V z)
    (z ^ 2 * (Work.Spaces.w z) ^ 2 * deriv (deriv V) z)
  linarith

/-! ## `Vn n` is eventually `1` on a neighbourhood of any `z > 0` -/

private lemma vw_Vn_eventually_one (z : ℝ) (hz : 0 < z) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ᶠ y : ℝ in 𝓝 z, Vn n y = 1 := by
  obtain ⟨N, hN⟩ := exists_nat_ge (max (6 / z) (2 * z))
  filter_upwards [eventually_ge_atTop N] with n hn
  have hn' : max (6 / z) (2 * z) ≤ (n : ℝ) := le_trans hN (by exact_mod_cast hn)
  filter_upwards [Ioo_mem_nhds (by linarith : z / 2 < z) (by linarith : z < 2 * z)] with y hy
  obtain ⟨hy1, hy2⟩ := hy
  have hypos : 0 < y := by linarith
  have hc : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h1 : 1 ≤ ((n : ℝ) + 1) * y - 2 := by
    have h : 6 / z ≤ (n : ℝ) + 1 := by
      have := le_trans (le_max_left _ _) hn'; linarith
    rw [div_le_iff₀ hz] at h
    have h3 : 3 ≤ ((n : ℝ) + 1) * y := by
      have := mul_le_mul_of_nonneg_left hy1.le hc.le
      nlinarith
    linarith
  have h2 : |y / ((n : ℝ) + 1)| ≤ 1 := by
    rw [abs_of_nonneg (div_nonneg hypos.le hc.le), div_le_one hc]
    have h : 2 * z ≤ (n : ℝ) + 1 := by
      have := le_trans (le_max_right _ _) hn'; linarith
    linarith
  unfold Vn
  rw [Real.smoothTransition.one_of_one_le h1, Work.Stability.chi_eq_one h2, one_mul]

/-! ## The theorem -/

theorem VnWeighted : ∃ C : ℝ, 0 < C ∧
    (∀ n z, 0 < z → |deriv (deriv (fun y : ℝ =>
        y ^ 2 * (Work.FTS.EllipticEst.H2W.AeProof.ae.Vn n y) * (Work.Spaces.w y) ^ 2)) z|
      ≤ C * (Work.Spaces.w z) ^ 2) ∧
    (∀ n z, 0 < z → |deriv (fun y : ℝ =>
        y * (Work.FTS.EllipticEst.H2W.AeProof.ae.Vn n y) * (Work.Spaces.w y) ^ 2) z|
      ≤ C * (Work.Spaces.w z) ^ 2) ∧
    (∀ z, 0 < z → Filter.Tendsto (fun n : ℕ => deriv (deriv (fun y : ℝ =>
        y ^ 2 * (Work.FTS.EllipticEst.H2W.AeProof.ae.Vn n y) * (Work.Spaces.w y) ^ 2)) z)
        Filter.atTop (nhds (deriv (deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2)) z))) ∧
    (∀ z, 0 < z → Filter.Tendsto (fun n : ℕ => deriv (fun y : ℝ =>
        y * (Work.FTS.EllipticEst.H2W.AeProof.ae.Vn n y) * (Work.Spaces.w y) ^ 2) z)
        Filter.atTop (nhds (deriv (fun y : ℝ => y * (Work.Spaces.w y) ^ 2) z))) := by
  obtain ⟨M, hM1, hM2, hM3⟩ := VnRescaledBounds
  have hVn1 : ∀ n : ℕ, ∀ y : ℝ, |Vn n y| ≤ 1 := fun n y => by
    rw [abs_of_nonneg (Vn_nonneg n y)]
    exact Vn_le_one n y
  have hA0 : (0 : ℝ) ≤ 2 * M := by linarith
  have hB0 : (0 : ℝ) ≤ 4 * M ^ 2 := by nlinarith
  refine ⟨6 + 4 * (2 * M) + 4 * M ^ 2, by nlinarith, ?_, ?_, ?_, ?_⟩
  · intro n z hz
    exact vw_dderiv_bound (Vn n) (Vn_contDiff n) (2 * M) (4 * M ^ 2)
      (fun y => hM2 n y) (fun y => hM3 n y) (hVn1 n) z hz
  · intro n z hz
    have h := vw_deriv_bound (Vn n) (Vn_contDiff n) (2 * M) (fun y => hM2 n y) (hVn1 n) z hz
    have hw2 : (0 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
    have hC : (3 + 2 * M) * (Work.Spaces.w z) ^ 2
        ≤ (6 + 4 * (2 * M) + 4 * M ^ 2) * (Work.Spaces.w z) ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ hw2
      nlinarith
    linarith
  · intro z hz
    have hev : ∀ᶠ n : ℕ in Filter.atTop,
        deriv (deriv (fun y : ℝ => y ^ 2 * Vn n y * (Work.Spaces.w y) ^ 2)) z
          = deriv (deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2)) z := by
      filter_upwards [vw_Vn_eventually_one z hz] with n hn
      have h1 : (fun y : ℝ => y ^ 2 * Vn n y * (Work.Spaces.w y) ^ 2)
          =ᶠ[𝓝 z] (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) := by
        filter_upwards [hn] with y hy
        rw [hy]; ring
      exact (h1.deriv).deriv_eq
    exact Filter.Tendsto.congr' (Filter.EventuallyEq.symm hev) tendsto_const_nhds
  · intro z hz
    have hev : ∀ᶠ n : ℕ in Filter.atTop,
        deriv (fun y : ℝ => y * Vn n y * (Work.Spaces.w y) ^ 2) z
          = deriv (fun y : ℝ => y * (Work.Spaces.w y) ^ 2) z := by
      filter_upwards [vw_Vn_eventually_one z hz] with n hn
      have h1 : (fun y : ℝ => y * Vn n y * (Work.Spaces.w y) ^ 2)
          =ᶠ[𝓝 z] (fun y : ℝ => y * (Work.Spaces.w y) ^ 2) := by
        filter_upwards [hn] with y hy
        rw [hy]; ring
      exact h1.deriv_eq
    exact Filter.Tendsto.congr' (Filter.EventuallyEq.symm hev) tendsto_const_nhds

end Work.FTS.EllipticEst.H2W.AeProof.ae
