/-
# The kernel bound in terms of the divisor: from `𝒫`-bounds to a contour bound

CKMRV Theorem 4.9(4) says that the *cleared* kernels
`Δ(τ)Δ(z)^e (j(τ)-j(z))K^{(d)}(τ,z)` (with `e = 1` for `d = 8` and `e = 2` for `d = 24`) have
moderate growth.  In `Work.Asymptotics.ModerateGrowth2` that statement is upgraded to the
two-variable form with constants independent of both variables; here it is transferred to a
pointwise bound on the kernel along the contour `z = it`:

  `‖K(τ,it)‖ · ‖Δ(τ)Δ(it)^e(j(τ)-j(it))‖ ≤ α (scale τ)^N (scale(it))^M`.

Dividing by the divisor gives the dominator for the contour integral, once the divisor is
estimated from below along the contour.  The two ingredients of that estimate are already in the
area: `Work.Asymptotics.DeltaFun_imagAxis_atTop` (`Δ(it)` is comparable to `e^{-2πt}` at the
cusp, whence — by modularity — to `t^{-12}e^{-2π/t}` at the other cusp) and
`Work.Asymptotics.jInvariantFun_imagAxis_atTop` (`j(it)` blows up like `e^{2πt}`), together with
`Δ(τ)j(τ) = E₄(τ)³`.

## Main definitions

* `Work.Asymptotics.DivisorLower d τ₀ R D` : the lower bound `D t ≤ ‖Δ(τ)Δ(it)^e(j(τ)-j(it))‖`
  on a ball of `τ`'s and all `t > 0`.
* `Work.Asymptotics.ContourAsymptotic K τ₀ R` : the CKMRV Lemma 4.12 shape of the contour bound
  `‖K(τ,it)‖ ≤ G t` with `G(t)e^{-πr²t}` integrable for `r ≠ 0` (and, for `d = 24`, for
  `|r| > √2`).

## Main results

* `Work.Asymptotics.norm_Kaxis_Kfun_le`, `Work.Asymptotics.norm_Kaxis_Khat_le` : the contour
  bounds for `K^{(d)}` and `K̂^{(d)}` in terms of the divisor.
* `Work.Asymptotics.contour_kernel_bound_of_divisor` : the same with the divisor estimated by
  `DivisorLower`, producing the explicit dominator `G t = α (scale τ)^N (scale(it))^M / D t`.
-/
import Mathlib
import Submission.Work.Kernels.All
import Submission.Work.Asymptotics.ModerateGrowth2

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix MeasureTheory
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics

open Work.Kernels

/-! ## The cleared kernel bound -/

/-- **The point of Theorem 4.9(4)**: off the divisor, the kernel is bounded by the cleared
kernel divided by the divisor. -/
theorem norm_Kfun_mul_growthPrefactor_le {ℓ : LogLambdaData} {d : ℕ} (hd : d = 8 ∨ d = 24)
    (h : ModerateGrowth2 (fun τ z : ℍ => KfunClear ℓ d τ z)) :
    ∃ α N M : ℝ, 0 ≤ α ∧ 0 ≤ N ∧ 0 ≤ M ∧ ∀ τ z : ℍ,
      ‖Kfun ℓ d τ z‖ * ‖growthPrefactor d τ z‖
        ≤ α * (scale τ) ^ N * (scale z) ^ M := by
  obtain ⟨α, N, M, hα, hN, hM, h⟩ := h
  refine ⟨α, N, M, hα, hN, hM, fun τ z => ?_⟩
  by_cases hJ : jInvariantFun τ = jInvariantFun z
  · have hzero : growthPrefactor d τ z = 0 := by
      simp only [growthPrefactor, hJ, sub_self, mul_zero]
    rw [hzero, norm_zero, mul_zero]
    exact mul_nonneg (mul_nonneg hα (Real.rpow_nonneg (scale_pos τ).le N))
      (Real.rpow_nonneg (scale_pos z).le M)
  · have h1 := ClearLink.KPlusClear_eq_smul d hd τ z hJ
    have h2 := ClearLink.KMinusClear_eq_smul ℓ d hd τ z hJ
    have hK : KfunClear ℓ d τ z = growthPrefactor d τ z * Kfun ℓ d τ z := by
      simp only [KfunClear, h1, h2, Kfun]
      ring
    calc ‖Kfun ℓ d τ z‖ * ‖growthPrefactor d τ z‖
        = ‖growthPrefactor d τ z * Kfun ℓ d τ z‖ := by rw [norm_mul]; ring
      _ = ‖KfunClear ℓ d τ z‖ := by rw [← hK]
      _ ≤ α * (scale τ) ^ N * (scale z) ^ M := h τ z

/-- The same for `K̂^{(d)}`. -/
theorem norm_Khat_mul_growthPrefactor_le {ℓ : LogLambdaData} {d : ℕ} (hd : d = 8 ∨ d = 24)
    (h : ModerateGrowth2 (fun τ z : ℍ => KhatClear ℓ d τ z)) :
    ∃ α N M : ℝ, 0 ≤ α ∧ 0 ≤ N ∧ 0 ≤ M ∧ ∀ τ z : ℍ,
      ‖Khat ℓ d τ z‖ * ‖growthPrefactor d τ z‖
        ≤ α * (scale τ) ^ N * (scale z) ^ M := by
  obtain ⟨α, N, M, hα, hN, hM, h⟩ := h
  refine ⟨α, N, M, hα, hN, hM, fun τ z => ?_⟩
  by_cases hJ : jInvariantFun τ = jInvariantFun z
  · have hzero : growthPrefactor d τ z = 0 := by
      simp only [growthPrefactor, hJ, sub_self, mul_zero]
    rw [hzero, norm_zero, mul_zero]
    exact mul_nonneg (mul_nonneg hα (Real.rpow_nonneg (scale_pos τ).le N))
      (Real.rpow_nonneg (scale_pos z).le M)
  · have h1 := ClearLink.KPlusClear_eq_smul d hd τ z hJ
    have h2 := ClearLink.KMinusClear_eq_smul ℓ d hd τ z hJ
    have hK : KhatClear ℓ d τ z = growthPrefactor d τ z * Khat ℓ d τ z := by
      simp only [KhatClear, h1, h2, Khat]
      ring
    calc ‖Khat ℓ d τ z‖ * ‖growthPrefactor d τ z‖
        = ‖growthPrefactor d τ z * Khat ℓ d τ z‖ := by rw [norm_mul]; ring
      _ = ‖KhatClear ℓ d τ z‖ := by rw [← hK]
      _ ≤ α * (scale τ) ^ N * (scale z) ^ M := h τ z

/-! ## The contour form -/

/-- The contour bound for `K^{(d)}`: for `t > 0`, the product of `K(τ,it)` with the divisor is
bounded by the two-variable moderate growth scale. -/
theorem exists_contour_bound_Kfun {ℓ : LogLambdaData} {d : ℕ} (hd : d = 8 ∨ d = 24)
    (h : ModerateGrowth2 (fun τ z : ℍ => KfunClear ℓ d τ z)) :
    ∃ α N M : ℝ, 0 ≤ α ∧ 0 ≤ N ∧ 0 ≤ M ∧ ∀ (τ : ℍ) (t : ℝ) (ht : 0 < t),
      ‖Kaxis (Kfun ℓ d) τ t‖ * ‖growthPrefactor d τ (imagAxis t ht)‖
        ≤ α * (scale τ) ^ N * (scale (imagAxis t ht)) ^ M := by
  obtain ⟨α, N, M, hα, hN, hM, h⟩ := norm_Kfun_mul_growthPrefactor_le hd h
  refine ⟨α, N, M, hα, hN, hM, fun τ t ht => ?_⟩
  rw [Kaxis, dif_pos ht]
  exact h τ (imagAxis t ht)

/-- The contour bound for `K̂^{(d)}`. -/
theorem exists_contour_bound_Khat {ℓ : LogLambdaData} {d : ℕ} (hd : d = 8 ∨ d = 24)
    (h : ModerateGrowth2 (fun τ z : ℍ => KhatClear ℓ d τ z)) :
    ∃ α N M : ℝ, 0 ≤ α ∧ 0 ≤ N ∧ 0 ≤ M ∧ ∀ (τ : ℍ) (t : ℝ) (ht : 0 < t),
      ‖Kaxis (Khat ℓ d) τ t‖ * ‖growthPrefactor d τ (imagAxis t ht)‖
        ≤ α * (scale τ) ^ N * (scale (imagAxis t ht)) ^ M := by
  obtain ⟨α, N, M, hα, hN, hM, h⟩ := norm_Khat_mul_growthPrefactor_le hd h
  refine ⟨α, N, M, hα, hN, hM, fun τ t ht => ?_⟩
  rw [Kaxis, dif_pos ht]
  exact h τ (imagAxis t ht)

/-- **The lower bound on the divisor along the contour**, the remaining analytic input for the
dominator.  `DivisorLower d τ₀ R D` says that for `τ` in the ball of radius `R` around `τ₀` the
CKMRV divisor is bounded below by `D` on the contour.  Concretely the paper's estimates give
`D t = c · t^{12e} exp(-2π(e-1)/t)` for `t ≤ T` and `D t = c · exp(-2π(e-1)t)` for `t ≥ T`
(with `e = 1` for `d = 8`, `e = 2` for `d = 24`), the remaining compact range being handled by
continuity and the fact that the contour is pole-free there (see
`Work.Asymptotics.Obstruction`). -/
def DivisorLower (d : ℕ) (τ₀ : ℍ) (R : ℝ) (D : ℝ → ℝ) : Prop :=
  ∀ (τ : ℍ) (t : ℝ) (ht : 0 < t), dist τ τ₀ < R → D t ≤ ‖growthPrefactor d τ (imagAxis t ht)‖

/-- **The dominator from the divisor bound.**  Combining the contour bound (`α, N, M` from
`Work.Asymptotics.KClear_mg2`) with a lower bound `D` on the divisor gives the explicit
dominator `G t = α * (scale τ₀)^N * (scale(it))^M / D t` for the kernel on a ball of `τ`'s.
Its integrability against `e^{-πr²t}` is the remaining numerical input: `(scale(it))^M / D t` is
polynomial near `t = 0` and at most exponential (rate `2π(e-1)`) at `t = ∞`, so
`G(t)e^{-πr²t}` is integrable for `r ≠ 0` when `d = 8` and for `|r| > √2` when `d = 24` —
exactly the ranges of `r` in which CKMRV define `F₂` by the integral directly. -/
theorem contour_kernel_bound_of_divisor {ℓ : LogLambdaData} {d : ℕ} (hd : d = 8 ∨ d = 24)
    (h : ModerateGrowth2 (fun τ z : ℍ => KfunClear ℓ d τ z)) {τ₀ : ℍ} {R : ℝ} {D : ℝ → ℝ}
    (hD : DivisorLower d τ₀ R D) (hDpos : ∀ (τ : ℍ) (t : ℝ) (ht : 0 < t), dist τ τ₀ < R →
      0 < D t) :
    ∃ α N M : ℝ, 0 ≤ α ∧ 0 ≤ N ∧ 0 ≤ M ∧ ∀ (τ : ℍ) (t : ℝ) (ht : 0 < t),
      dist τ τ₀ < R →
      ‖Kaxis (Kfun ℓ d) τ t‖
        ≤ α * (scale τ) ^ N * (scale (imagAxis t ht)) ^ M / D t := by
  obtain ⟨α, N, M, hα, hN, hM, h⟩ := exists_contour_bound_Kfun hd h
  refine ⟨α, N, M, hα, hN, hM, fun τ t ht hτ => ?_⟩
  have hlt : ‖Kaxis (Kfun ℓ d) τ t‖ * D t
      ≤ α * (scale τ) ^ N * (scale (imagAxis t ht)) ^ M :=
    le_trans (mul_le_mul_of_nonneg_left (hD τ t ht hτ) (norm_nonneg _)) (h τ t ht)
  rw [le_div_iff₀ (hDpos τ t ht hτ)]
  exact hlt

end Work.Asymptotics
