import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.MiddleRange.exists_j_sub_lower_lambda_near_I
import Submission.Work.Asymptotics.MiddleRange.exists_lambdaFun_lipschitz
import Submission.Work.Asymptotics.jDiff_lower_imagAxis
import Submission.Work.Kernels.LogLambda.LambdaLaws
import Submission.Work.Rigidity.LambdaBasic
import Submission.Work.Rigidity.lamC_neg_inv
import Submission.Work.Residues.KMinusClear_T

/-!
# The `j`-invariant vanishes to second order at the elliptic point `i`

This file proves `Work.Asymptotics.j_sub_I_quadratic`: on a neighbourhood of the elliptic point
`i = Complex.I` of `SL(2, ℤ)`, the difference `j z - j i = j z - 1728` is comparable to the
*square* of the Euclidean distance `‖z - i‖`:

  `c ‖z - i‖² ≤ ‖j z - j i‖ ≤ C ‖z - i‖²`   (`c, C > 0`).

## The mathematics

`j` has a critical point at `i` (`j' = -2πi E₄²E₆/Δ` and `E₆(i) = 0`, while `j''(i) ≠ 0`), so
`j - 1728` has a *double* zero at `i`: the map `j : ℍ → ℂ` is two-to-one near `i`, the two sheets
being interchanged by `S : z ↦ -1/z`.

The proof goes through the modular `λ`-function, for which `j` is the explicit rational function

  `j = Φ (λ - 1/2)`,   `Φ u = 256 (3/4 + u²)³ / (1/4 - u²)²`   (`Φ 0 = 1728`),

because `λ(i) = 1/2` and `1/4 - u² = λ(1 - λ) ≠ 0` on `ℍ`.  The numerator of `Φ` is even and
vanishes to second order at `u = 0`:

  `Φ u - 1728 = u² · ψ u`,   `ψ u = 256 (u⁴ - (9/2)u² + 81/16) / (1/4 - u²)²`,

with `ψ 0 = 20736 ≠ 0`.  Since `ψ` is continuous at the origin it is bounded above and below
there, and since `λ` is a local bi-Lipschitz homeomorphism at `i` (strict differentiability of
`λ` at `i`, whose derivative `λ' = π i λ (1-λ) θ₀₀⁴` does not vanish), `‖λ z - 1/2‖` is itself
comparable to `‖z - i‖` near `i` in both directions.  Combining the two comparisons gives the
asserted two-sided quadratic bound.

## Main result

* `Work.Asymptotics.j_sub_I_quadratic`
-/

namespace Work.Asymptotics

open UpperHalfPlane

noncomputable section

/-! ## The value of `λ` at the elliptic point `i` -/

/-- The extension `λ` of the modular lambda function to the upper half plane takes the value
`1/2` at `i`: `λ(-1/z) = 1 - λ(z)` holds identically, and `-1/i = i`. -/
private lemma lamC_I : Work.Kernels.LogLambda.lamC Complex.I = 1 / 2 := by
  have h := Work.Rigidity.lamC_neg_inv Complex.I (by simp)
  have h' : (-1 : ℂ) / Complex.I = Complex.I := by
    rw [neg_div, one_div, Complex.inv_I, neg_neg]
  rw [h'] at h
  linear_combination (1 / 2 : ℂ) * h

/-- `λ(i) = 1/2`, the elliptic point `i` being the branch point of `λ` over `1/2`. -/
private lemma lambdaFun_I : Work.Kernels.lambdaFun UpperHalfPlane.I = 1 / 2 := by
  have h := Work.Rigidity.lamC_coe UpperHalfPlane.I
  rw [UpperHalfPlane.coe_I, lamC_I] at h
  exact h.symm

/-! ## `j` as the explicit degree-six rational function of `λ`

The classical identity `j = 256 (1 - λ + λ²)³ / (λ²(1-λ)²)` (which follows from
`E₄ = (U²+V²+W²)/2`, `Δ = U²V²W²/256` and `U = V + W` for the fourth powers of Jacobi's theta
functions) is rewritten in the variable `u = λ - 1/2`, where it becomes the *even* rational
function `Φ`. -/

private lemma alg_theta (a b c : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hq : a = c + b) :
    ((a ^ 2 + b ^ 2 + c ^ 2) / 2) ^ 3 / (a ^ 2 * b ^ 2 * c ^ 2 / 256)
      = 256 * ((b / a) ^ 2 - (b / a) + 1) ^ 3 / ((b / a) ^ 2 * (1 - b / a) ^ 2) := by
  subst hq
  have h1 : ((c + b) ^ 2 + b ^ 2 + c ^ 2) / 2 = (c + b) ^ 2 - (c + b) * b + b ^ 2 := by ring
  have h2 : (b / (c + b)) ^ 2 - b / (c + b) + 1
      = ((c + b) ^ 2 - (c + b) * b + b ^ 2) / (c + b) ^ 2 := by
    field_simp
    ring
  have h3 : 1 - b / (c + b) = c / (c + b) := by
    field_simp
    ring
  rw [h1, h2, h3]
  field_simp

/-- `j = 256 (1 - λ + λ²)³ / (λ²(1-λ)²)` on `ℍ`. -/
private lemma jInvariantFun_eq_lambda (τ : UpperHalfPlane) :
    Work.Kernels.jInvariantFun τ =
      256 * (Work.Kernels.lambdaFun τ ^ 2 - Work.Kernels.lambdaFun τ + 1) ^ 3 /
        (Work.Kernels.lambdaFun τ ^ 2 * (1 - Work.Kernels.lambdaFun τ) ^ 2) := by
  have hE4 := Work.Residues.KMinusT_E4Fun_eq_theta τ
  have hD := Work.Residues.KMinusT_DeltaFun_eq_theta τ
  have hq := Work.Kernels.TildeFacts.theta_quartic τ
  have ha : Work.Kernels.UFun τ ≠ 0 := Work.Rigidity.UFun_ne_zero τ
  have hb : Work.Kernels.VFun τ ≠ 0 := Work.Rigidity.VFun_ne_zero τ
  have hc : Work.Kernels.WFun τ ≠ 0 := Work.Rigidity.WFun_ne_zero τ
  have hmain := alg_theta (Work.Kernels.UFun τ) (Work.Kernels.VFun τ) (Work.Kernels.WFun τ)
    ha hb hc hq
  rw [show Work.Kernels.jInvariantFun τ
      = ((Work.Kernels.UFun τ ^ 2 + Work.Kernels.VFun τ ^ 2 + Work.Kernels.WFun τ ^ 2) / 2) ^ 3
        / (Work.Kernels.UFun τ ^ 2 * Work.Kernels.VFun τ ^ 2 * Work.Kernels.WFun τ ^ 2 / 256) by
    rw [Work.Kernels.jInvariantFun, hE4, hD]]
  rw [hmain]

/-- The even rational function `Φ u = 256 (3/4 + u²)³/(1/4 - u²)²` with `j = Φ (λ - 1/2)`. -/
private def PhiJ (u : ℂ) : ℂ := 256 * (3 / 4 + u ^ 2) ^ 3 / (1 / 4 - u ^ 2) ^ 2

private lemma PhiJ_zero : PhiJ 0 = 1728 := by unfold PhiJ; norm_num

/-- `j = Φ ∘ (λ - 1/2)`: the form of the previous identity adapted to the critical point
`λ = 1/2`. -/
private lemma jInvariantFun_eq_PhiJ (τ : UpperHalfPlane) :
    Work.Kernels.jInvariantFun τ = PhiJ (Work.Kernels.lambdaFun τ - 1 / 2) := by
  rw [jInvariantFun_eq_lambda τ]
  unfold PhiJ
  rw [show Work.Kernels.lambdaFun τ ^ 2 - Work.Kernels.lambdaFun τ + 1
        = 3 / 4 + (Work.Kernels.lambdaFun τ - 1 / 2) ^ 2 by ring,
      show Work.Kernels.lambdaFun τ ^ 2 * (1 - Work.Kernels.lambdaFun τ) ^ 2
        = (1 / 4 - (Work.Kernels.lambdaFun τ - 1 / 2) ^ 2) ^ 2 by ring]

/-! ## `Φ u - Φ 0 = u² ψ u` with `ψ 0 = 20736 ≠ 0` -/

/-- The divided difference of `Φ` by `u²`: `Φ u - 1728 = u² ψ u`. -/
private def psi (u : ℂ) : ℂ := 256 * (u ^ 4 - 9 / 2 * u ^ 2 + 81 / 16) / (1 / 4 - u ^ 2) ^ 2

/-- **The second-order vanishing of `Φ u - 1728`.**  This is the algebraic heart of the double
zero of `j - 1728` at `i`: the polynomial identity
`256 (3/4+u²)³ - 1728 (1/4-u²)² = u² · 256 (u⁴ - (9/2)u² + 81/16)`. -/
private lemma PhiJ_sub_zero (u : ℂ) (hu : 1 / 4 - u ^ 2 ≠ 0) :
    PhiJ u - 1728 = u ^ 2 * psi u := by
  have hD : ((1 : ℂ) / 4 - u ^ 2) ^ 2 ≠ 0 := pow_ne_zero 2 hu
  have hpoly : 256 * (3 / 4 + u ^ 2) ^ 3 - ((1 : ℂ) / 4 - u ^ 2) ^ 2 * 1728
      = u ^ 2 * (256 * (u ^ 4 - 9 / 2 * u ^ 2 + 81 / 16)) := by ring
  unfold PhiJ psi
  rw [← mul_div_cancel_left₀ (1728 : ℂ) hD, ← sub_div, hpoly, mul_div_assoc]

private lemma psi_zero : psi 0 = 20736 := by unfold psi; norm_num

private lemma continuousAt_psi : ContinuousAt psi 0 := by
  unfold psi
  refine ContinuousAt.div ?_ ?_ ?_
  · fun_prop
  · fun_prop
  · norm_num

/-- `ψ` is bounded above and below by positive constants near the origin. -/
private lemma psi_bounds :
    ∃ δ k K : ℝ, 0 < δ ∧ 0 < k ∧ 0 < K ∧
      ∀ u : ℂ, ‖u‖ < δ → k ≤ ‖psi u‖ ∧ ‖psi u‖ ≤ K := by
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.mp continuousAt_psi 10368 (by norm_num)
  refine ⟨δ, 10368, 41472, hδ, by norm_num, by norm_num, fun u hu => ?_⟩
  have h1 : dist (psi u) (psi 0) < 10368 :=
    hδ' (x := u) (by rw [dist_eq_norm, sub_zero]; exact hu)
  rw [psi_zero, dist_eq_norm, norm_sub_rev] at h1
  have h3 : ‖(20736 : ℂ)‖ = (20736 : ℝ) := by norm_num
  constructor
  · have h4 := norm_sub_norm_le (20736 : ℂ) (psi u)
    rw [h3] at h4
    linarith
  · have h5 : ‖psi u‖ ≤ ‖psi u - 20736‖ + ‖(20736 : ℂ)‖ := by
      have h6 := norm_add_le (psi u - 20736) (20736 : ℂ)
      rw [show psi u - 20736 + (20736 : ℂ) = psi u from by ring] at h6
      exact h6
    rw [norm_sub_rev (psi u) (20736 : ℂ), h3] at h5
    linarith

/-! ## `λ` is locally Lipschitz at `i`

A function strictly differentiable at a point is Lipschitz on a neighbourhood of it; here we
extract this in the form needed.  Applied to `λ` (analytic, hence strictly differentiable, at
`i`) this gives the upper comparison `‖λ z - 1/2‖ ≤ L ‖z - i‖`. -/

/-- **Strict differentiability gives a local Lipschitz upper bound.** -/
private lemma exists_lipschitz_upper_of_hasStrictDerivAt {f : ℂ → ℂ} {x f' : ℂ}
    (h : HasStrictDerivAt f f' x) :
    ∃ ρ L : ℝ, 0 < ρ ∧ 0 ≤ L ∧ ∀ y z : ℂ, ‖y - x‖ < ρ → ‖z - x‖ < ρ →
      ‖f y - f z‖ ≤ L * ‖y - z‖ := by
  have hlo := h.hasStrictFDerivAt.isLittleO
  obtain ⟨ρ, hρ, hb⟩ :=
    Metric.eventually_nhds_iff.mp (hlo.bound (by norm_num : (0 : ℝ) < 1 / 2))
  refine ⟨ρ, ‖f'‖ + 1 / 2, hρ, by positivity, fun y z hy hz => ?_⟩
  have hp : dist (y, z) (x, x) < ρ := by
    rw [Prod.dist_eq]
    exact max_lt (by rwa [dist_eq_norm]) (by rwa [dist_eq_norm])
  have h1 := hb hp
  have h2 : ‖(ContinuousLinearMap.toSpanSingleton ℂ f') (y - z)‖ = ‖f'‖ * ‖y - z‖ := by
    rw [ContinuousLinearMap.toSpanSingleton_apply, norm_smul, mul_comm]
  have h3 : ‖f y - f z‖ ≤ ‖f y - f z - (ContinuousLinearMap.toSpanSingleton ℂ f') (y - z)‖
      + ‖(ContinuousLinearMap.toSpanSingleton ℂ f') (y - z)‖ := by
    have h4 := norm_add_le (f y - f z - (ContinuousLinearMap.toSpanSingleton ℂ f') (y - z))
      ((ContinuousLinearMap.toSpanSingleton ℂ f') (y - z))
    rw [show f y - f z - (ContinuousLinearMap.toSpanSingleton ℂ f') (y - z)
        + (ContinuousLinearMap.toSpanSingleton ℂ f') (y - z) = f y - f z from by ring] at h4
    exact h4
  rw [h2] at h3
  linarith

/-- **Upper comparison of `λ` with `1/2` near `i`.** -/
private lemma lambdaFun_sub_half_upper :
    ∃ ρ L : ℝ, 0 < ρ ∧ 0 ≤ L ∧ ∀ z : UpperHalfPlane,
      ‖(z : ℂ) - Complex.I‖ < ρ →
      ‖Work.Kernels.lambdaFun z - 1 / 2‖ ≤ L * ‖(z : ℂ) - Complex.I‖ := by
  have hana : (0 : ℝ) < Complex.I.im := by simp
  have hAna : AnalyticAt ℂ Work.Kernels.LogLambda.lamC Complex.I :=
    Work.Kernels.LogLambda.differentiableOn_lamC.analyticAt
      (Work.Kernels.LogLambda.isOpen_U.mem_nhds hana)
  obtain ⟨ρ, L, hρ, hL, h⟩ := exists_lipschitz_upper_of_hasStrictDerivAt hAna.hasStrictDerivAt
  refine ⟨ρ, L, hρ, hL, fun z hz => ?_⟩
  have h1 := h (z : ℂ) Complex.I hz (by rw [sub_self, norm_zero]; exact hρ)
  rw [Work.Rigidity.lamC_coe z, lamC_I] at h1
  exact h1

/-- **Lower comparison of `λ` with `1/2` near `i`**: `λ` is a local bi-Lipschitz map at `i`
(`Work.Asymptotics.MiddleRange.exists_lambdaFun_lipschitz`, whose derivative `λ'` does not
vanish). -/
private lemma lambdaFun_sub_half_lower :
    ∃ ρ c : ℝ, 0 < ρ ∧ 0 < c ∧ ∀ z : UpperHalfPlane,
      ‖(z : ℂ) - Complex.I‖ < ρ →
      c * ‖(z : ℂ) - Complex.I‖ ≤ ‖Work.Kernels.lambdaFun z - 1 / 2‖ := by
  obtain ⟨ρ, hρ, c, hc, h⟩ :=
    Work.Asymptotics.MiddleRange.exists_lambdaFun_lipschitz UpperHalfPlane.I
  refine ⟨ρ, c, hρ, hc, fun z hz => ?_⟩
  have hI : ‖((UpperHalfPlane.I : UpperHalfPlane) : ℂ)
      - ((UpperHalfPlane.I : UpperHalfPlane) : ℂ)‖ < ρ := by
    rw [sub_self, norm_zero]; exact hρ
  have h1 := h z UpperHalfPlane.I hz hI
  simpa [UpperHalfPlane.coe_I, lambdaFun_I] using h1

/-! ## The quadratic two-sided bound -/

theorem j_sub_I_quadratic :
    ∃ ρ c C : ℝ, 0 < ρ ∧ 0 < c ∧ 0 < C ∧ ∀ z : UpperHalfPlane,
      ‖(z : ℂ) - Complex.I‖ < ρ →
        c * ‖(z : ℂ) - Complex.I‖ ^ 2
            ≤ ‖Work.Kernels.jInvariantFun z - Work.Kernels.jInvariantFun UpperHalfPlane.I‖
          ∧ ‖Work.Kernels.jInvariantFun z - Work.Kernels.jInvariantFun UpperHalfPlane.I‖
            ≤ C * ‖(z : ℂ) - Complex.I‖ ^ 2 := by
  obtain ⟨ρψ, k, K, hρψ, hk, hK, hψ⟩ := psi_bounds
  obtain ⟨ρu, Lu, hρu, hLu, hu⟩ := lambdaFun_sub_half_upper
  obtain ⟨ρl, cl, hρl, hcl, hl⟩ := lambdaFun_sub_half_lower
  have hLpos : (0 : ℝ) < max Lu 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hLuL : Lu ≤ max Lu 1 := le_max_left _ _
  have hρpos : 0 < min ρu (min ρl (ρψ / max Lu 1)) :=
    lt_min hρu (lt_min hρl (div_pos hρψ hLpos))
  refine ⟨min ρu (min ρl (ρψ / max Lu 1)), cl ^ 2 * k, (max Lu 1) ^ 2 * K, hρpos,
    by positivity, by positivity, fun z hz => ?_⟩
  have hzu : ‖(z : ℂ) - Complex.I‖ < ρu := lt_of_lt_of_le hz (min_le_left _ _)
  have hzl : ‖(z : ℂ) - Complex.I‖ < ρl :=
    lt_of_lt_of_le hz (le_trans (min_le_right _ _) (min_le_left _ _))
  have hzψ : max Lu 1 * ‖(z : ℂ) - Complex.I‖ < ρψ := by
    have h3 : ‖(z : ℂ) - Complex.I‖ < ρψ / max Lu 1 :=
      lt_of_lt_of_le hz (le_trans (min_le_right _ _) (min_le_right _ _))
    have h4 : ‖(z : ℂ) - Complex.I‖ * max Lu 1 < ρψ := (lt_div_iff₀ hLpos).mp h3
    rw [mul_comm]
    exact h4
  have hup : ‖Work.Kernels.lambdaFun z - 1 / 2‖ ≤ max Lu 1 * ‖(z : ℂ) - Complex.I‖ :=
    le_trans (hu z hzu) (mul_le_mul_of_nonneg_right hLuL (norm_nonneg _))
  have hlow : cl * ‖(z : ℂ) - Complex.I‖ ≤ ‖Work.Kernels.lambdaFun z - 1 / 2‖ := hl z hzl
  have hψ' := hψ (Work.Kernels.lambdaFun z - 1 / 2) (lt_of_le_of_lt hup hzψ)
  have hzero : (1 : ℂ) / 4 - (Work.Kernels.lambdaFun z - 1 / 2) ^ 2 ≠ 0 := by
    have hfac : (1 : ℂ) / 4 - (Work.Kernels.lambdaFun z - 1 / 2) ^ 2
        = Work.Kernels.lambdaFun z * (1 - Work.Kernels.lambdaFun z) := by ring
    rw [hfac]
    exact mul_ne_zero (Work.Rigidity.lambdaFun_ne_zero z)
      (sub_ne_zero.mpr (Work.Rigidity.lambdaFun_ne_one z).symm)
  have hJI : Work.Kernels.jInvariantFun UpperHalfPlane.I = 1728 := by
    rw [jInvariantFun_eq_PhiJ UpperHalfPlane.I, lambdaFun_I, sub_self, PhiJ_zero]
  have hfac2 : Work.Kernels.jInvariantFun z - Work.Kernels.jInvariantFun UpperHalfPlane.I
      = (Work.Kernels.lambdaFun z - 1 / 2) ^ 2 * psi (Work.Kernels.lambdaFun z - 1 / 2) := by
    rw [jInvariantFun_eq_PhiJ z, hJI, PhiJ_sub_zero _ hzero]
  rw [hfac2, norm_mul, norm_pow]
  constructor
  · have hA : (cl * ‖(z : ℂ) - Complex.I‖) ^ 2 ≤ ‖Work.Kernels.lambdaFun z - 1 / 2‖ ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hcl.le (norm_nonneg _)) hlow 2
    calc cl ^ 2 * k * ‖(z : ℂ) - Complex.I‖ ^ 2
        = (cl * ‖(z : ℂ) - Complex.I‖) ^ 2 * k := by ring
      _ ≤ ‖Work.Kernels.lambdaFun z - 1 / 2‖ ^ 2
            * ‖psi (Work.Kernels.lambdaFun z - 1 / 2)‖ :=
          mul_le_mul hA hψ'.1 hk.le (pow_nonneg (norm_nonneg _) 2)
  · have hA : ‖Work.Kernels.lambdaFun z - 1 / 2‖ ^ 2
        ≤ (max Lu 1 * ‖(z : ℂ) - Complex.I‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hup 2
    calc ‖Work.Kernels.lambdaFun z - 1 / 2‖ ^ 2 * ‖psi (Work.Kernels.lambdaFun z - 1 / 2)‖
        ≤ (max Lu 1 * ‖(z : ℂ) - Complex.I‖) ^ 2 * K :=
          mul_le_mul hA hψ'.2 (norm_nonneg _)
            (pow_nonneg (mul_nonneg hLpos.le (norm_nonneg _)) 2)
      _ = (max Lu 1) ^ 2 * K * ‖(z : ℂ) - Complex.I‖ ^ 2 := by ring

end

end Work.Asymptotics
