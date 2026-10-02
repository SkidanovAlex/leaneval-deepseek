import Mathlib
import Submission.Work.FatouCoord.Setup
import Submission.Work.FatouCoord.Petal.repelling_defs
import Submission.Work.FatouCoord.Repelling.defect_bound
import Submission.Work.FatouCoord.Repelling.defect_lipschitz
import Submission.Work.FatouCoord.Repelling.wMap_injOn_large

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The corrected conjugacy `V (w + 1) = wMap f (V w)` on a left half-plane

The correction `Z` supplied by `Work.FatouCoord.Repelling.exists_correction` is a bounded
holomorphic solution of the difference equation

`Z (w + 1) - Z w = defect f a w (Z w)`

on a left half-plane `{Re w < -R₀}`.  Writing `V w = w + (1 - a) * Λ w + Z w`, where
`Λ w = log (-w) + π i` is the branch of the logarithm on the left half-plane, the defining
equation of `defect` turns *algebraically* into the conjugacy

`V (w + 1) = wMap f (V w)`.

The remaining properties are quantitative:

* `‖V w - w‖ ≤ ‖w‖ / 2` (and hence `V w ≠ 0`), because `Z` is bounded by `1/2` and `Λ` grows
  only logarithmically;
* `V` is injective on the half-plane.  This is *not* a consequence of the above estimates: the
  two half-planes on which `V` is defined are shifted, so that the two points of a hypothetical
  collision cannot be compared directly.  What makes the argument work is the conjugacy itself:
  from `V w₁ = V w₂` and the injectivity of `wMap f` near infinity one gets
  `V (w₁ - n) = V (w₂ - n)` for all `n`, and on the far left the mean value inequalities for `Λ`
  and for the *bounded* function `Z` (Cauchy's estimate) are strong enough to force
  `w₁ = w₂`.
-/

namespace Work.FatouCoord.Repelling

open Work.FatouCoord
open scoped Topology
open Set Filter Metric

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

noncomputable section

variable {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}

/-! ## The branch `Λ` of the logarithm on a left half-plane -/

/-- `Λ w = log (-w) + π i` is holomorphic on every left half-plane `{Re w < -R}` with `R ≥ 0`. -/
theorem differentiableOn_Lambda {R : ℝ} (hR : 0 ≤ R) :
    DifferentiableOn ℂ Petal.Lambda (Petal.LeftHalfPlane R) := by
  intro w hw
  rw [Petal.mem_LeftHalfPlane] at hw
  have hwr : 0 < (-w).re := by rw [Complex.neg_re]; linarith
  have h1 : DifferentiableAt ℂ (fun u : ℂ => Complex.log (-u)) w :=
    (Complex.differentiableAt_log (Or.inl hwr)).comp w (hasDerivAt_neg' w).differentiableAt
  have h2 : DifferentiableAt ℂ
      (fun u : ℂ => Complex.log (-u) + (Real.pi : ℂ) * Complex.I) w := h1.add_const _
  have hfun : Petal.Lambda = fun u : ℂ => Complex.log (-u) + (Real.pi : ℂ) * Complex.I := rfl
  rw [hfun]
  exact h2.differentiableWithinAt

/-- Left half-planes are convex. -/
theorem convex_leftHalfPlane (T : ℝ) : Convex ℝ (Petal.LeftHalfPlane T) := by
  have h : Petal.LeftHalfPlane T = Complex.reLm ⁻¹' (Set.Iio (-T)) := by
    ext z
    exact Iff.rfl
  rw [h]
  exact (convex_Iio (-T)).linear_preimage Complex.reLm

/-! ## Two thresholds -/

/-- A square-root-versus-linear threshold: past `T` the quantity `C (2 √t + 2π) + 1/2` is at
most `t / 2`.  This is the form in which `norm_Lambda_le` (from `defect_lipschitz`) is used: the
logarithmic growth of `Λ` is dominated by the linear factor `‖w‖`. -/
theorem exists_threshold_sqrt (C : ℝ) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ t : ℝ, T ≤ t → C * (2 * Real.sqrt t + 2 * Real.pi) + 1 / 2 ≤ t / 2 := by
  set M : ℝ := 16 * |C| + 8 * (|C| * (2 * Real.pi) + 1 / 2) + 4 with hMdef
  have hMpos : 0 < M := by
    rw [hMdef]
    have h1 := abs_nonneg C
    have h2 : 0 ≤ |C| * (2 * Real.pi) := by positivity
    linarith
  have hM16 : 16 * |C| ≤ M := by rw [hMdef]; nlinarith [abs_nonneg C, Real.pi_pos]
  have hM8 : 8 * (|C| * (2 * Real.pi) + 1 / 2) ≤ M := by
    rw [hMdef]; nlinarith [abs_nonneg C, Real.pi_pos]
  refine ⟨max 1 (M ^ 2), le_max_left _ _, ?_⟩
  intro t ht
  have h1 : (1 : ℝ) ≤ t := le_trans (le_max_left _ _) ht
  have hM2 : M ^ 2 ≤ t := le_trans (le_max_right _ _) ht
  have htpos : 0 < t := lt_of_lt_of_le one_pos h1
  have hM1 : (1 : ℝ) ≤ M := by rw [hMdef]; nlinarith [abs_nonneg C, Real.pi_pos]
  have hMt : M ≤ t := by
    have : M ≤ M ^ 2 := by nlinarith [hM1]
    linarith
  have hsqrt_le : Real.sqrt t ≤ t / M := by
    have hMe : M ≤ Real.sqrt t := by
      have h2 := Real.sqrt_le_sqrt hM2
      rwa [Real.sqrt_sq hMpos.le] at h2
    rw [le_div_iff₀ hMpos]
    calc Real.sqrt t * M ≤ Real.sqrt t * Real.sqrt t :=
          mul_le_mul_of_nonneg_left hMe (Real.sqrt_nonneg t)
      _ = t := Real.mul_self_sqrt (le_of_lt htpos)
  have h2AC : 2 * |C| * Real.sqrt t ≤ t / 8 := by
    have h3 : 2 * |C| * Real.sqrt t ≤ 2 * |C| * (t / M) :=
      mul_le_mul_of_nonneg_left hsqrt_le (by positivity)
    have h4 : 2 * |C| * (t / M) ≤ t / 8 := by
      rw [← mul_div_assoc, div_le_div_iff₀ hMpos (by norm_num : (0 : ℝ) < 8)]
      nlinarith [mul_le_mul_of_nonneg_right hM16 (le_of_lt htpos)]
    linarith
  have h5 : |C| * (2 * Real.pi) + 1 / 2 ≤ t / 8 := by
    have h6 : |C| * (2 * Real.pi) + 1 / 2 ≤ M / 8 := by nlinarith [hM8]
    have h7 : M / 8 ≤ t / 8 := by linarith [hMt]
    linarith
  have hC1 : C * (2 * Real.sqrt t) ≤ |C| * (2 * Real.sqrt t) :=
    mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
  have hC2 : C * (2 * Real.pi) ≤ |C| * (2 * Real.pi) :=
    mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
  have hsplit : C * (2 * Real.sqrt t + 2 * Real.pi) + 1 / 2
      = C * (2 * Real.sqrt t) + (C * (2 * Real.pi) + 1 / 2) := by ring
  have hexp : C * (2 * Real.sqrt t) + (C * (2 * Real.pi) + 1 / 2)
      ≤ 2 * |C| * Real.sqrt t + (|C| * (2 * Real.pi) + 1 / 2) := by
    have h: C * (2 * Real.sqrt t) = 2 * C * Real.sqrt t := by ring
    nlinarith [hC1, hC2]
  rw [hsplit]
  linarith

/-! ## A mean value estimate for a bounded holomorphic function on a half-plane -/

/-- If `Z` is holomorphic and bounded by `1/2` on `{Re w < -R}`, then on the smaller half-plane
`{Re w < -T}` (`T > R`) it is Lipschitz with constant `1/(T - R)`.  This is Cauchy's estimate
for the derivative on the ball of radius `(T - R)/2`, followed by the mean value inequality. -/
theorem norm_Z_sub_le {Z : ℂ → ℂ} {R T : ℝ} (hR : 0 < R)
    (hdiff : DifferentiableOn ℂ Z (Petal.LeftHalfPlane R))
    (hbd : ∀ w : ℂ, w ∈ Petal.LeftHalfPlane R → ‖Z w‖ ≤ 1 / 2) (hT : R < T)
    {x y : ℂ} (hx : x ∈ Petal.LeftHalfPlane T) (hy : y ∈ Petal.LeftHalfPlane T) :
    ‖Z x - Z y‖ ≤ (1 / (T - R)) * ‖x - y‖ := by
  have hTRpos : 0 < T - R := sub_pos.mpr hT
  have hsub : Petal.LeftHalfPlane T ⊆ Petal.LeftHalfPlane R := by
    intro w hw
    rw [Petal.mem_LeftHalfPlane] at hw ⊢
    linarith
  have hdiffT : DifferentiableOn ℂ Z (Petal.LeftHalfPlane T) := hdiff.mono hsub
  have hderiv : ∀ w ∈ Petal.LeftHalfPlane T, ‖deriv Z w‖ ≤ 1 / (T - R) := by
    intro w hw
    rw [Petal.mem_LeftHalfPlane] at hw
    set r : ℝ := (T - R) / 2 with hrdef
    have hrpos : 0 < r := by rw [hrdef]; linarith
    have hclosed : Metric.closedBall w r ⊆ Petal.LeftHalfPlane R := by
      intro z hz
      rw [Metric.mem_closedBall, dist_eq_norm] at hz
      rw [Petal.mem_LeftHalfPlane]
      have h1 : z.re ≤ w.re + ‖z - w‖ := by
        have := Complex.re_le_norm (z - w)
        rw [Complex.sub_re] at this
        linarith
      rw [hrdef] at hz
      linarith
    have hclsub : closure (Metric.ball w r) ⊆ Petal.LeftHalfPlane R := fun z hz =>
      hclosed (closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall hz)
    have hcont : DiffContOnCl ℂ Z (Metric.ball w r) := (hdiff.mono hclsub).diffContOnCl
    have hsphere : ∀ z ∈ Metric.sphere w r, ‖Z z‖ ≤ 1 / 2 := fun z hz =>
      hbd z (hclosed (Metric.sphere_subset_closedBall hz))
    have hcau := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hrpos hcont hsphere
    have heq : (1 / 2 : ℝ) / r = 1 / (T - R) := by
      rw [hrdef, div_div]
      norm_num
    rwa [heq] at hcau
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := Z) (s := Petal.LeftHalfPlane T) (C := 1 / (T - R))
    (fun z hz => hdiffT.differentiableAt ((Petal.IsOpen_leftHalfPlane T).mem_nhds hz))
    hderiv (convex_leftHalfPlane T) hx hy
  simpa only [norm_sub_rev] using hmvt

/-! ## The correction equation is algebraically the conjugacy -/

/-- The defining equation of `defect` is exactly what makes `V w = w + (1 - a) Λ w + Z w`
conjugate the shift to `wMap f`. -/
theorem self_conjugacy {Z : ℂ → ℂ} {R : ℝ}
    (hZeq : ∀ w : ℂ, w ∈ Petal.LeftHalfPlane R → Z (w + 1) - Z w = Petal.defect f a w (Z w)) :
    ∀ w : ℂ, w ∈ Petal.LeftHalfPlane R →
      (fun u : ℂ => u + (1 - a) * Petal.Lambda u + Z u) (w + 1)
        = wMap f ((fun u : ℂ => u + (1 - a) * Petal.Lambda u + Z u) w) := by
  intro w hw
  have h : Z (w + 1) = Z w + Petal.defect f a w (Z w) := by
    have := hZeq w hw
    rw [sub_eq_iff_eq_add] at this
    rw [this, add_comm]
  show (w + 1) + (1 - a) * Petal.Lambda (w + 1) + Z (w + 1)
      = wMap f (w + (1 - a) * Petal.Lambda w + Z w)
  rw [h, Petal.defect_apply, Petal.corr_apply]
  ring

/-! ## The Lipschitz estimate for `Λ` on a far left half-plane -/

/-- The derivative of the branch `Λ` on the left half-plane is `1/w`. -/
theorem hasDerivAt_Lambda {w : ℂ} (hw : w.re < 0) : HasDerivAt Petal.Lambda (1 / w) w := by
  have hwslit : (-w) ∈ Complex.slitPlane := Or.inl (by rw [Complex.neg_re]; linarith)
  have h1 : HasDerivAt (fun u : ℂ => Complex.log (-u)) (((-w)⁻¹) * (-1)) w :=
    (Complex.hasDerivAt_log hwslit).comp w (hasDerivAt_neg' w)
  have h2 : HasDerivAt (fun u : ℂ => Complex.log (-u) + (Real.pi : ℂ) * Complex.I)
      (((-w)⁻¹) * (-1)) w := h1.add_const _
  have hfun : Petal.Lambda = fun u : ℂ => Complex.log (-u) + (Real.pi : ℂ) * Complex.I := rfl
  rw [hfun]
  have hval : ((-w)⁻¹) * (-1) = 1 / w := by field_simp
  rwa [hval] at h2

/-- `Λ` is Lipschitz with constant `1/T` on the half-plane `{Re w < -T}`. -/
theorem norm_Lambda_sub_le_aux {x y : ℂ} {T : ℝ} (hT : 0 < T)
    (hx : Petal.LeftHalfPlane T x) (hy : Petal.LeftHalfPlane T y) :
    ‖Petal.Lambda x - Petal.Lambda y‖ ≤ ‖x - y‖ / T := by
  have hdiff : ∀ z ∈ Petal.LeftHalfPlane T, DifferentiableAt ℂ Petal.Lambda z := fun z hz =>
    (hasDerivAt_Lambda (by
      rw [Petal.mem_LeftHalfPlane] at hz
      linarith)).differentiableAt
  have hbound : ∀ z ∈ Petal.LeftHalfPlane T, ‖deriv Petal.Lambda z‖ ≤ 1 / T := by
    intro z hz
    rw [Petal.mem_LeftHalfPlane] at hz
    have hz0 : z ≠ 0 := by
      intro h
      rw [h] at hz
      simp at hz
      linarith
    have hderiv : deriv Petal.Lambda z = 1 / z :=
      (hasDerivAt_Lambda (by linarith)).deriv
    have hnorm : T ≤ ‖z‖ := by
      have h := Complex.re_le_norm (-z)
      rw [Complex.neg_re, norm_neg] at h
      linarith
    rw [hderiv, norm_div, norm_one]
    exact one_div_le_one_div_of_le hT hnorm
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := Petal.Lambda) (s := Petal.LeftHalfPlane T) (C := 1 / T)
    hdiff hbound (convex_leftHalfPlane T) hx hy
  have h1 : ‖Petal.Lambda y - Petal.Lambda x‖ ≤ (1 / T) * ‖y - x‖ := hmvt
  rw [norm_sub_rev (Petal.Lambda y) (Petal.Lambda x), norm_sub_rev y x, mul_comm] at h1
  simpa only [div_eq_mul_inv, one_mul] using h1

/-! ## Elementary summation estimates

The correction `Z` is constructed as the fixed point of the operator `Omega` on the space of
functions bounded by `1/2` on a left half-plane.  The two quantitative inputs are the pointwise
bound `‖defect f a w ζ‖ ≤ K_b (1 + log ‖w‖)/‖w‖²` and the Lipschitz bound
`‖defect f a w ζ - defect f a w ζ'‖ ≤ K_l/‖w‖² ‖ζ - ζ'‖` of the companion files; the point of
the estimates below is that both series are summable *uniformly* on the half-plane, with sums
that can be made as small as we like by moving the half-plane far enough to the left. -/

/-- Telescoping bound: `∑' n, 1/(N+n)² ≤ 2/N`. -/
private theorem tsum_inv_sq_le (N : ℝ) (hN : 1 ≤ N) :
    ∑' n : ℕ, 1 / (N + (n : ℝ)) ^ 2 ≤ 2 / N := by
  have hNpos : 0 < N := by linarith
  refine Real.tsum_le_of_sum_range_le (fun n => by positivity) (fun k => ?_)
  have h := Estimate.sum_range_inv_sq_le N hNpos k
  have h2 : 1 / N ^ 2 + 1 / N ≤ 2 / N := by
    have h3 : 1 / N ^ 2 ≤ 1 / N := by
      rw [div_le_div_iff₀ (by positivity) hNpos]
      nlinarith
    have h4 : (2 : ℝ) / N = 1 / N + 1 / N := by ring
    rw [h4]; linarith
  linarith [h]

/-- The logarithm grows at most like a square root: `1 + log t ≤ 3 √t` for `t ≥ 1`. -/
private theorem one_add_log_le_three_sqrt {t : ℝ} (h1 : 1 ≤ t) :
    1 + Real.log t ≤ 3 * Real.sqrt t := by
  have h2 : Real.log t ≤ 2 * Real.sqrt t := by
    have h := abs_log_le_two_sqrt h1
    linarith [le_abs_self (Real.log t)]
  have h3 : 1 ≤ Real.sqrt t := by
    have h := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_one] at h
  linarith

/-- `1/(t √t)` is antitone on the positive reals. -/
private theorem inv_mul_sqrt_antitone {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    1 / (t * Real.sqrt t) ≤ 1 / (s * Real.sqrt s) := by
  refine one_div_le_one_div_of_le (by positivity) ?_
  exact mul_le_mul hst (Real.sqrt_le_sqrt hst) (Real.sqrt_nonneg s) ((le_of_lt hs).trans hst)

/-- The terms of the defect series are dominated by `3K/(s√s)`, uniformly in the half-plane. -/
private theorem defect_term_le {K t s : ℝ} (hK : 0 ≤ K) (ht1 : 1 ≤ t) (hs : 0 < s) (hst : s ≤ t) :
    K * (1 + Real.log t) / t ^ 2 ≤ 3 * K / (s * Real.sqrt s) := by
  have ht0 : 0 < t := by linarith
  have hlog := one_add_log_le_three_sqrt ht1
  have h1 : K * (1 + Real.log t) / t ^ 2 ≤ K * (3 * Real.sqrt t) / t ^ 2 := by
    have h4 : (0 : ℝ) < t ^ 2 := by positivity
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlog hK) h4.le
  have h2 : K * (3 * Real.sqrt t) / t ^ 2 = 3 * K * (Real.sqrt t / t ^ 2) := by ring
  have h3 : Real.sqrt t / t ^ 2 = 1 / (t * Real.sqrt t) := by
    rw [div_eq_div_iff (by positivity) (by positivity)]
    rw [show Real.sqrt t * (t * Real.sqrt t) = t * (Real.sqrt t * Real.sqrt t) by ring,
      Real.mul_self_sqrt ht0.le]
    ring
  have h4 : 1 / (t * Real.sqrt t) ≤ 1 / (s * Real.sqrt s) := by
    refine one_div_le_one_div_of_le (by positivity) ?_
    exact mul_le_mul hst (Real.sqrt_le_sqrt hst) (Real.sqrt_nonneg s) ((le_of_lt hs).trans hst)
  have h5 : 3 * K * (1 / (s * Real.sqrt s)) = 3 * K / (s * Real.sqrt s) := by ring
  calc K * (1 + Real.log t) / t ^ 2
      ≤ K * (3 * Real.sqrt t) / t ^ 2 := h1
    _ = 3 * K * (Real.sqrt t / t ^ 2) := h2
    _ = 3 * K * (1 / (t * Real.sqrt t)) := by rw [h3]
    _ ≤ 3 * K * (1 / (s * Real.sqrt s)) := mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = 3 * K / (s * Real.sqrt s) := h5

/-- The telescoping sum bound `∑' n, 1/((N+n) √(N+n)) ≤ 2/√(N-1)`, with summability. -/
private theorem summable_tsum_inv_mul_sqrt_le (N : ℝ) (hN : 1 < N) :
    Summable (fun n : ℕ => 1 / ((N + (n : ℝ)) * Real.sqrt (N + (n : ℝ)))) ∧
      ∑' n : ℕ, 1 / ((N + (n : ℝ)) * Real.sqrt (N + (n : ℝ))) ≤ 2 / Real.sqrt (N - 1) := by
  have hterm : ∀ i : ℕ, 1 / ((N + (i : ℝ)) * Real.sqrt (N + (i : ℝ)))
      ≤ 2 * (1 / Real.sqrt (N + (i : ℝ) - 1) - 1 / Real.sqrt (N + (i : ℝ))) := by
    intro i
    have hs0 : 0 < N + (i : ℝ) := by
      have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
      linarith
    have hs1 : 0 < N + (i : ℝ) - 1 := by linarith
    have hB : 0 < Real.sqrt (N + (i : ℝ) - 1) := Real.sqrt_pos.mpr hs1
    have hsqA : Real.sqrt (N + (i : ℝ)) * Real.sqrt (N + (i : ℝ)) = N + (i : ℝ) :=
      Real.mul_self_sqrt hs0.le
    have hsqB : Real.sqrt (N + (i : ℝ) - 1) * Real.sqrt (N + (i : ℝ) - 1) = N + (i : ℝ) - 1 :=
      Real.mul_self_sqrt hs1.le
    have hkey : (2 * (N + (i : ℝ)) + 1) * Real.sqrt (N + (i : ℝ) - 1)
        ≤ 2 * (N + (i : ℝ)) * Real.sqrt (N + (i : ℝ)) := by
      have hsq : ((2 * (N + (i : ℝ)) + 1) * Real.sqrt (N + (i : ℝ) - 1))
            * ((2 * (N + (i : ℝ)) + 1) * Real.sqrt (N + (i : ℝ) - 1))
          ≤ (2 * (N + (i : ℝ)) * Real.sqrt (N + (i : ℝ)))
            * (2 * (N + (i : ℝ)) * Real.sqrt (N + (i : ℝ))) := by
        have hL : ((2 * (N + (i : ℝ)) + 1) * Real.sqrt (N + (i : ℝ) - 1))
              * ((2 * (N + (i : ℝ)) + 1) * Real.sqrt (N + (i : ℝ) - 1))
            = (2 * (N + (i : ℝ)) + 1) ^ 2 * (N + (i : ℝ) - 1) := by
          have e : ((2 * (N + (i : ℝ)) + 1) * Real.sqrt (N + (i : ℝ) - 1))
                * ((2 * (N + (i : ℝ)) + 1) * Real.sqrt (N + (i : ℝ) - 1))
              = (2 * (N + (i : ℝ)) + 1) ^ 2
                * (Real.sqrt (N + (i : ℝ) - 1) * Real.sqrt (N + (i : ℝ) - 1)) := by ring
          rw [e, hsqB]
        have hR : (2 * (N + (i : ℝ)) * Real.sqrt (N + (i : ℝ)))
              * (2 * (N + (i : ℝ)) * Real.sqrt (N + (i : ℝ)))
            = (2 * (N + (i : ℝ))) ^ 2 * (N + (i : ℝ)) := by
          have e : (2 * (N + (i : ℝ)) * Real.sqrt (N + (i : ℝ)))
                * (2 * (N + (i : ℝ)) * Real.sqrt (N + (i : ℝ)))
              = (2 * (N + (i : ℝ))) ^ 2
                * (Real.sqrt (N + (i : ℝ)) * Real.sqrt (N + (i : ℝ))) := by ring
          rw [e, hsqA]
        rw [hL, hR]
        nlinarith
      exact (mul_self_le_mul_self_iff
        (by positivity : (0 : ℝ) ≤ (2 * (N + (i : ℝ)) + 1) * Real.sqrt (N + (i : ℝ) - 1))
        (by positivity : (0 : ℝ) ≤ 2 * (N + (i : ℝ)) * Real.sqrt (N + (i : ℝ)))).mpr hsq
    have h2 : 2 * (1 / Real.sqrt (N + (i : ℝ) - 1) - 1 / Real.sqrt (N + (i : ℝ)))
          * ((N + (i : ℝ)) * Real.sqrt (N + (i : ℝ)))
        = 2 * (N + (i : ℝ)) * Real.sqrt (N + (i : ℝ)) / Real.sqrt (N + (i : ℝ) - 1)
          - 2 * (N + (i : ℝ)) := by
      field_simp
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (N + (i : ℝ)) * Real.sqrt (N + (i : ℝ)))]
    rw [h2, le_sub_iff_add_le, le_div_iff₀ hB]
    linarith [hkey]
  have hstep : ∀ k : ℕ, ∑ i ∈ Finset.range k, 1 / ((N + (i : ℝ)) * Real.sqrt (N + (i : ℝ)))
      ≤ 2 / Real.sqrt (N - 1) := by
    intro k
    calc ∑ i ∈ Finset.range k, 1 / ((N + (i : ℝ)) * Real.sqrt (N + (i : ℝ)))
        ≤ ∑ i ∈ Finset.range k,
            2 * (1 / Real.sqrt (N + (i : ℝ) - 1) - 1 / Real.sqrt (N + (i : ℝ))) :=
          Finset.sum_le_sum (fun i _ => hterm i)
      _ = ∑ i ∈ Finset.range k,
            (2 * (1 / Real.sqrt (N + (i : ℝ) - 1))
              - 2 * (1 / Real.sqrt (N + ((i + 1 : ℕ) : ℝ) - 1))) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          have h : N + (i : ℝ) = N + ((i + 1 : ℕ) : ℝ) - 1 := by push_cast; ring
          rw [h]; ring
      _ = 2 * (1 / Real.sqrt (N + ((0 : ℕ) : ℝ) - 1))
            - 2 * (1 / Real.sqrt (N + (k : ℝ) - 1)) := by
          rw [Finset.sum_range_sub' (fun j : ℕ => 2 * (1 / Real.sqrt (N + (j : ℝ) - 1)))]
      _ ≤ 2 / Real.sqrt (N - 1) := by
          have h1 : 0 ≤ 2 * (1 / Real.sqrt (N + (k : ℝ) - 1)) := by positivity
          have h2 : N + ((0 : ℕ) : ℝ) - 1 = N - 1 := by norm_num
          rw [h2]
          have h3 : 2 * (1 / Real.sqrt (N - 1)) = 2 / Real.sqrt (N - 1) := by ring
          rw [h3]
          linarith
  exact ⟨summable_of_sum_range_le (fun n => by positivity) hstep,
    Real.tsum_le_of_sum_range_le (fun n => by positivity) hstep⟩

/-- `w ↦ defect f a w (Z w)` is holomorphic on a left half-plane, provided the intermediate
point `w + (1 - a) Λ w + Z w` stays in the region where `wMap f` is holomorphic. -/
private lemma defect_comp_diffOn {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}
    (hb : ParabolicBounds f h a r A A') {Z : ℂ → ℂ} {L : ℝ} (hL : 1 ≤ L)
    (hgood : ∀ x ∈ Petal.LeftHalfPlane L,
      1 / r < ‖x + (1 - a) * Petal.Lambda x + Z x‖ ∧ 4 ≤ ‖x + (1 - a) * Petal.Lambda x + Z x‖)
    (hZ : DifferentiableOn ℂ Z (Petal.LeftHalfPlane L)) :
    DifferentiableOn ℂ (fun x => Petal.defect f a x (Z x)) (Petal.LeftHalfPlane L) := by
  intro x hx
  have hxlt : x.re < -L := hx
  have hxre : x.re < 0 := by linarith
  have hΛx : DifferentiableAt ℂ Petal.Lambda x := (hasDerivAt_Lambda hxre).differentiableAt
  have hΛx1 : DifferentiableAt ℂ (fun z : ℂ => Petal.Lambda (z + 1)) x := by
    have h1 : (x + 1).re < 0 := by
      simp only [Complex.add_re, Complex.one_re]; linarith
    exact (hasDerivAt_Lambda h1).differentiableAt.comp x (differentiableAt_id.add_const 1)
  have hZx : DifferentiableAt ℂ Z x :=
    hZ.differentiableAt ((Petal.IsOpen_leftHalfPlane L).mem_nhds hx)
  have hy : DifferentiableAt ℂ (fun z : ℂ => z + (1 - a) * Petal.Lambda z + Z z) x :=
    (differentiableAt_id.add (hΛx.const_mul (1 - a))).add hZx
  obtain ⟨hg1, hg4⟩ := hgood x hx
  have hW : DifferentiableAt ℂ (wMap f) (x + (1 - a) * Petal.Lambda x + Z x) :=
    Estimate.differentiableAt_wMap hb hg1 hg4
  have hcomp : DifferentiableAt ℂ
      (fun z : ℂ => wMap f (z + (1 - a) * Petal.Lambda z + Z z)) x :=
    DifferentiableAt.comp (f := fun z : ℂ => z + (1 - a) * Petal.Lambda z + Z z) (g := wMap f) x hW hy
  have hgoal : DifferentiableAt ℂ (fun z : ℂ => wMap f (z + (1 - a) * Petal.Lambda z + Z z)
      - (z + (1 - a) * Petal.Lambda z + Z z) - 1
      - (1 - a) * (Petal.Lambda (z + 1) - Petal.Lambda z)) x :=
    ((hcomp.sub hy).sub_const 1).sub ((hΛx1.sub hΛx).const_mul (1 - a))
  refine (hgoal.congr_of_eventuallyEq
    (Filter.EventuallyEq.of_eq (funext fun z => by rw [Petal.defect_apply, Petal.corr_apply]))).differentiableWithinAt

/-- **Existence of the bounded correction `Z`.**  On a far left half-plane the difference
equation `Z (w + 1) - Z w = defect f a w (Z w)` has a holomorphic solution bounded by `1/2`.

The solution is the fixed point of the contraction
`Omega Z w = ∑' n, defect f a (w - n - 1) (Z (w - n - 1))`, obtained as the limit of the
iterates started at `0`; both the pointwise bound and the contraction estimate come from
`defect_bound` and `defect_lipschitz`, and the summability of the geometric majorants from the
telescoping estimates above. -/
private theorem exists_correction_self {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}
    (hb : ParabolicBounds f h a r A A') :
    ∃ R : ℝ, 0 < R ∧ 1 / r < R ∧ ∃ Z : ℂ → ℂ, DifferentiableOn ℂ Z (Petal.LeftHalfPlane R) ∧
      (∀ w : ℂ, w ∈ Petal.LeftHalfPlane R → ‖Z w‖ ≤ 1 / 2) ∧
      (∀ w : ℂ, w ∈ Petal.LeftHalfPlane R → Z (w + 1) - Z w = Petal.defect f a w (Z w)) := by
  obtain ⟨R_b, K_b, hR_b_pos, hrR_b, hK_b, hbdD⟩ := defect_bound hb
  obtain ⟨R_l, K_l, hR_l_pos, hrR_l, hK_l, hlipD⟩ := defect_lipschitz hb
  obtain ⟨T₁, hT₁, hthr⟩ := exists_threshold_sqrt ‖1 - a‖
  set A₁ : ℝ := max (R_b + 1) (R_l + 1) with hA₁def
  set B₁ : ℝ := max (144 * K_b ^ 2 + 1) (4 * K_l + 1) with hB₁def
  set C₁ : ℝ := max (2 / r + 2) (max 9 (T₁ + 1)) with hC₁def
  set R : ℝ := max A₁ (max B₁ C₁) with hRdef
  have hA₁le : A₁ ≤ R := by rw [hRdef]; exact le_max_left _ _
  have hB₁C₁le : max B₁ C₁ ≤ R := by rw [hRdef]; exact le_max_right _ _
  have hB₁le : B₁ ≤ R := le_trans (le_max_left B₁ C₁) hB₁C₁le
  have hC₁le : C₁ ≤ R := le_trans (le_max_right B₁ C₁) hB₁C₁le
  have hRRb : R_b + 1 ≤ R := by
    have h1 : R_b + 1 ≤ A₁ := by rw [hA₁def]; exact le_max_left _ _
    linarith
  have hRRl : R_l + 1 ≤ R := by
    have h1 : R_l + 1 ≤ A₁ := by rw [hA₁def]; exact le_max_right _ _
    linarith
  have hRKb : 144 * K_b ^ 2 + 1 ≤ R := by
    have h1 : 144 * K_b ^ 2 + 1 ≤ B₁ := by rw [hB₁def]; exact le_max_left _ _
    linarith
  have hRKl : 4 * K_l + 1 ≤ R := by
    have h1 : 4 * K_l + 1 ≤ B₁ := by rw [hB₁def]; exact le_max_right _ _
    linarith
  have hRr : 2 / r + 2 ≤ R := by
    have h1 : 2 / r + 2 ≤ C₁ := by rw [hC₁def]; exact le_max_left _ _
    linarith
  have hR9 : 9 ≤ R := by
    have h1 : 9 ≤ max 9 (T₁ + 1) := le_max_left _ _
    have h2 : max 9 (T₁ + 1) ≤ C₁ := by rw [hC₁def]; exact le_max_right _ _
    linarith
  have hRT : T₁ + 1 ≤ R := by
    have h1 : T₁ + 1 ≤ max 9 (T₁ + 1) := le_max_right _ _
    have h2 : max 9 (T₁ + 1) ≤ C₁ := by rw [hC₁def]; exact le_max_right _ _
    linarith
  have hRpos : 0 < R := by linarith
  have hRr' : 1 / r < R := by linarith
  have hR1 : 1 < R := by linarith
  have hR2 : 2 < R := by linarith
  have hKb2 : 12 * K_b ≤ Real.sqrt (R - 1) := by
    have h5 : Real.sqrt (144 * K_b ^ 2) ≤ Real.sqrt (R - 1) := Real.sqrt_le_sqrt (by linarith)
    have h6 : Real.sqrt (144 * K_b ^ 2) = 12 * K_b := by
      rw [show (144 : ℝ) * K_b ^ 2 = (12 * K_b) ^ 2 by ring, Real.sqrt_sq_eq_abs,
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ 12 * K_b)]
    rwa [h6] at h5
  have hκ0 : 0 ≤ 2 * K_l / R := by positivity
  have hκ1 : 2 * K_l / R < 1 := by
    rw [div_lt_one hRpos]
    linarith
  -- the majorants of the defect series
  set ub : ℕ → ℝ := fun n => 3 * K_b / ((R + (n : ℝ)) * Real.sqrt (R + (n : ℝ))) with hubdef
  set ul : ℕ → ℝ := fun n => K_l / (R + (n : ℝ)) ^ 2 with huldef
  have hub_summ : Summable ub := by
    rw [hubdef]
    exact ((summable_tsum_inv_mul_sqrt_le R hR1).1.mul_left (3 * K_b)).congr
      (fun n => by rw [mul_one_div])
  have hub_le : ∑' n : ℕ, ub n ≤ 1 / 2 := by
    rw [hubdef]
    have h1 : (∑' n : ℕ, 3 * K_b / ((R + (n : ℝ)) * Real.sqrt (R + (n : ℝ))))
        = 3 * K_b * ∑' n : ℕ, 1 / ((R + (n : ℝ)) * Real.sqrt (R + (n : ℝ))) := by
      rw [← tsum_mul_left]
      exact tsum_congr (fun n => by rw [mul_one_div])
    rw [h1]
    have h2 := (summable_tsum_inv_mul_sqrt_le R hR1).2
    have h3 : 3 * K_b * (2 / Real.sqrt (R - 1)) ≤ 1 / 2 := by
      rw [show 3 * K_b * (2 / Real.sqrt (R - 1)) = 6 * K_b / Real.sqrt (R - 1) by ring]
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < Real.sqrt (R - 1))]
      linarith
    calc 3 * K_b * (∑' n : ℕ, 1 / ((R + (n : ℝ)) * Real.sqrt (R + (n : ℝ))))
        ≤ 3 * K_b * (2 / Real.sqrt (R - 1)) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ 1 / 2 := h3
  have hul_summ : Summable ul := by
    rw [huldef]
    have hbase : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
      have h := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
      simpa using (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) 1).mpr h
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (hbase.mul_left K_l)
    rw [mul_one_div]
    refine div_le_div_of_nonneg_left hK_l (by positivity) ?_
    have h1 : (n : ℝ) + 1 ≤ R + (n : ℝ) := by linarith
    have h2 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    nlinarith
  have hul_le : ∑' n : ℕ, ul n ≤ 2 * K_l / R := by
    rw [huldef]
    have h1 : (∑' n : ℕ, K_l / (R + (n : ℝ)) ^ 2)
        = K_l * ∑' n : ℕ, 1 / (R + (n : ℝ)) ^ 2 := by
      rw [← tsum_mul_left]
      exact tsum_congr (fun n => by rw [mul_one_div])
    rw [h1]
    have h2 := tsum_inv_sq_le R (by linarith : 1 ≤ R)
    calc K_l * (∑' n : ℕ, 1 / (R + (n : ℝ)) ^ 2) ≤ K_l * (2 / R) :=
          mul_le_mul_of_nonneg_left h2 hK_l
      _ = 2 * K_l / R := by ring
  -- the geometry of the working half-plane
  have hΓ_open : IsOpen (Petal.LeftHalfPlane (R - 1)) := Petal.IsOpen_leftHalfPlane _
  have hΓ_Rb : Petal.LeftHalfPlane (R - 1) ⊆ Petal.LeftHalfPlane R_b := by
    intro w hw
    rw [Petal.mem_LeftHalfPlane] at hw ⊢
    linarith
  have hΓ_Rl : Petal.LeftHalfPlane (R - 1) ⊆ Petal.LeftHalfPlane R_l := by
    intro w hw
    rw [Petal.mem_LeftHalfPlane] at hw ⊢
    linarith
  have hΓ_norm : ∀ w : ℂ, w ∈ Petal.LeftHalfPlane (R - 1) → R - 1 < ‖w‖ := by
    intro w hw
    rw [Petal.mem_LeftHalfPlane] at hw
    have h := Complex.re_le_norm (-w)
    rw [Complex.neg_re, norm_neg] at h
    linarith
  have hshift_mem : ∀ (n : ℕ) (w : ℂ), w ∈ Petal.LeftHalfPlane (R - 1) →
      w - (n : ℂ) ∈ Petal.LeftHalfPlane (R - 1) := by
    intro n w hw
    rw [Petal.mem_LeftHalfPlane] at hw ⊢
    simp only [Complex.sub_re, Complex.natCast_re]
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hshift_norm : ∀ (n : ℕ) (w : ℂ), w ∈ Petal.LeftHalfPlane (R - 1) →
      R - 1 + (n : ℝ) ≤ ‖w - (n : ℂ)‖ := by
    intro n w hw
    have h := Complex.re_le_norm (-(w - (n : ℂ)))
    rw [Complex.neg_re, norm_neg] at h
    rw [Petal.mem_LeftHalfPlane] at hw
    simp only [Complex.sub_re, Complex.natCast_re] at h
    push_cast
    linarith
  -- the per-term bounds for the defect series
  have hterm_gen : ∀ (n : ℕ) (Y : ℂ → ℂ),
      (∀ x : ℂ, x ∈ Petal.LeftHalfPlane (R - 1) → ‖Y x‖ ≤ 1 / 2) →
      ∀ w : ℂ, w ∈ Petal.LeftHalfPlane (R - 1) →
      ‖Petal.defect f a (w - (n : ℂ)) (Y (w - (n : ℂ)))‖
        ≤ 3 * K_b / ((R - 1 + (n : ℝ)) * Real.sqrt (R - 1 + (n : ℝ))) := by
    intro n Y hY w hw
    have hxΓ := hshift_mem n w hw
    have hxRb : w - (n : ℂ) ∈ Petal.LeftHalfPlane R_b := hΓ_Rb hxΓ
    have hYbd : ‖Y (w - (n : ℂ))‖ ≤ 1 := by
      have h := hY _ hxΓ
      linarith
    have hD := hbdD _ (Y (w - (n : ℂ))) hxRb hYbd
    have hxnorm := hshift_norm n w hw
    have hx1 : 1 ≤ ‖w - (n : ℂ)‖ := by linarith
    have hs : 0 < R - 1 + (n : ℝ) := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    exact le_trans hD (defect_term_le hK_b hx1 hs hxnorm)
  have hterm_b : ∀ (n : ℕ) (Y : ℂ → ℂ),
      (∀ x : ℂ, x ∈ Petal.LeftHalfPlane (R - 1) → ‖Y x‖ ≤ 1 / 2) →
      ∀ w : ℂ, w ∈ Petal.LeftHalfPlane (R - 1) →
      ‖Petal.defect f a (w - ((n : ℕ) + 1)) (Y (w - ((n : ℕ) + 1)))‖ ≤ ub n := by
    intro n Y hY w hw
    have h := hterm_gen (n + 1) Y hY w hw
    have hcast : (R - 1 + ((n + 1 : ℕ) : ℝ)) = R + (n : ℝ) := by push_cast; ring
    rw [hcast] at h
    have harg : w - (((n + 1 : ℕ)) : ℂ) = w - ((n : ℕ) + 1) := by push_cast; ring
    rw [harg] at h
    simpa only [hubdef] using h
  have hball : ∀ Y : ℂ → ℂ,
      (∀ x : ℂ, x ∈ Petal.LeftHalfPlane (R - 1) → ‖Y x‖ ≤ 1 / 2) →
      ∀ w : ℂ, w ∈ Petal.LeftHalfPlane (R - 1) → ‖Petal.Omega f a Y w‖ ≤ 1 / 2 := by
    intro Y hY w hw
    have hterm : ∀ n : ℕ,
        ‖Petal.defect f a (w - ((n : ℕ) + 1)) (Y (w - ((n : ℕ) + 1)))‖ ≤ ub n :=
      fun n => hterm_b n Y hY w hw
    have hsumm : Summable
        (fun n : ℕ => ‖Petal.defect f a (w - ((n : ℕ) + 1)) (Y (w - ((n : ℕ) + 1)))‖) :=
      Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hub_summ
    have h1 : ‖Petal.Omega f a Y w‖
        ≤ ∑' n : ℕ, ‖Petal.defect f a (w - ((n : ℕ) + 1)) (Y (w - ((n : ℕ) + 1)))‖ :=
      norm_tsum_le_tsum_norm hsumm
    have h2 : ∑' n : ℕ, ‖Petal.defect f a (w - ((n : ℕ) + 1)) (Y (w - ((n : ℕ) + 1)))‖
        ≤ ∑' n : ℕ, ub n := Summable.tsum_le_tsum hterm hsumm hub_summ
    linarith [h1, h2, hub_le]
  have hcontr : ∀ Y₁ Y₂ : ℂ → ℂ,
      (∀ x : ℂ, x ∈ Petal.LeftHalfPlane (R - 1) → ‖Y₁ x‖ ≤ 1 / 2) →
      (∀ x : ℂ, x ∈ Petal.LeftHalfPlane (R - 1) → ‖Y₂ x‖ ≤ 1 / 2) →
      ∀ δ : ℝ, (∀ x : ℂ, x ∈ Petal.LeftHalfPlane (R - 1) → ‖Y₁ x - Y₂ x‖ ≤ δ) →
      ∀ w : ℂ, w ∈ Petal.LeftHalfPlane (R - 1) →
        ‖Petal.Omega f a Y₁ w - Petal.Omega f a Y₂ w‖ ≤ (2 * K_l / R) * δ := by
    intro Y₁ Y₂ hY₁ hY₂ δ hδ w hw
    have hδnn : 0 ≤ δ := le_trans (norm_nonneg _) (hδ _ (hshift_mem 0 w hw))
    have hterm : ∀ n : ℕ,
        ‖Petal.defect f a (w - ((n : ℕ) + 1)) (Y₁ (w - ((n : ℕ) + 1)))
          - Petal.defect f a (w - ((n : ℕ) + 1)) (Y₂ (w - ((n : ℕ) + 1)))‖
        ≤ ul n * δ := by
      intro n
      have hxΓ : w - ((n : ℕ) + 1) ∈ Petal.LeftHalfPlane (R - 1) := by
        have h := hshift_mem (n + 1) w hw
        rwa [show (((n + 1 : ℕ)) : ℂ) = (n : ℂ) + 1 by push_cast; ring] at h
      have hxRl : w - ((n : ℕ) + 1) ∈ Petal.LeftHalfPlane R_l := hΓ_Rl hxΓ
      have hb₁ : ‖Y₁ (w - ((n : ℕ) + 1))‖ ≤ 1 := by
        have h := hY₁ _ hxΓ
        linarith
      have hb₂ : ‖Y₂ (w - ((n : ℕ) + 1))‖ ≤ 1 := by
        have h := hY₂ _ hxΓ
        linarith
      have hD := hlipD _ (Y₁ _) (Y₂ _) hxRl hb₁ hb₂
      have hxnorm : R + (n : ℝ) ≤ ‖w - ((n : ℕ) + 1)‖ := by
        have h := hshift_norm (n + 1) w hw
        have harg : w - (((n + 1 : ℕ)) : ℂ) = w - ((n : ℕ) + 1) := by push_cast; ring
        have hcast : R - 1 + (((n + 1 : ℕ)) : ℝ) = R + (n : ℝ) := by push_cast; ring
        rw [harg, hcast] at h
        exact h
      have hxpos : 0 < ‖w - ((n : ℕ) + 1)‖ := by linarith
      have h1 : K_l / ‖w - ((n : ℕ) + 1)‖ ^ 2 ≤ K_l / (R + (n : ℝ)) ^ 2 := by
        refine div_le_div_of_nonneg_left hK_l (by positivity) ?_
        nlinarith
      have h2 : K_l / ‖w - ((n : ℕ) + 1)‖ ^ 2 * ‖Y₁ (w - ((n : ℕ) + 1)) - Y₂ (w - ((n : ℕ) + 1))‖
          ≤ K_l / (R + (n : ℝ)) ^ 2 * δ :=
        mul_le_mul h1 (hδ _ hxΓ) (norm_nonneg _) (by positivity)
      calc ‖Petal.defect f a (w - ((n : ℕ) + 1)) (Y₁ (w - ((n : ℕ) + 1)))
            - Petal.defect f a (w - ((n : ℕ) + 1)) (Y₂ (w - ((n : ℕ) + 1)))‖
          ≤ K_l / ‖w - ((n : ℕ) + 1)‖ ^ 2
              * ‖Y₁ (w - ((n : ℕ) + 1)) - Y₂ (w - ((n : ℕ) + 1))‖ := hD
        _ ≤ K_l / (R + (n : ℝ)) ^ 2 * δ := h2
        _ = ul n * δ := by rw [huldef]
    have hsumm₁ : Summable (fun n : ℕ => Petal.defect f a (w - ((n : ℕ) + 1)) (Y₁ (w - ((n : ℕ) + 1)))) :=
      Summable.of_norm (Summable.of_nonneg_of_le (fun n => norm_nonneg _)
        (fun n => hterm_b n Y₁ hY₁ w hw) hub_summ)
    have hsumm₂ : Summable (fun n : ℕ => Petal.defect f a (w - ((n : ℕ) + 1)) (Y₂ (w - ((n : ℕ) + 1)))) :=
      Summable.of_norm (Summable.of_nonneg_of_le (fun n => norm_nonneg _)
        (fun n => hterm_b n Y₂ hY₂ w hw) hub_summ)
    have hsummD : Summable (fun n : ℕ =>
        ‖Petal.defect f a (w - ((n : ℕ) + 1)) (Y₁ (w - ((n : ℕ) + 1)))
          - Petal.defect f a (w - ((n : ℕ) + 1)) (Y₂ (w - ((n : ℕ) + 1)))‖) :=
      Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm (hul_summ.mul_right δ)
    have hsplit : Petal.Omega f a Y₁ w - Petal.Omega f a Y₂ w
        = ∑' n : ℕ, (Petal.defect f a (w - ((n : ℕ) + 1)) (Y₁ (w - ((n : ℕ) + 1)))
            - Petal.defect f a (w - ((n : ℕ) + 1)) (Y₂ (w - ((n : ℕ) + 1)))) := by
      rw [Petal.Omega_apply, Petal.Omega_apply, Summable.tsum_sub hsumm₁ hsumm₂]
    rw [hsplit]
    calc ‖∑' n : ℕ, (Petal.defect f a (w - ((n : ℕ) + 1)) (Y₁ (w - ((n : ℕ) + 1)))
            - Petal.defect f a (w - ((n : ℕ) + 1)) (Y₂ (w - ((n : ℕ) + 1))))‖
        ≤ ∑' n : ℕ, ‖Petal.defect f a (w - ((n : ℕ) + 1)) (Y₁ (w - ((n : ℕ) + 1)))
            - Petal.defect f a (w - ((n : ℕ) + 1)) (Y₂ (w - ((n : ℕ) + 1)))‖ :=
          norm_tsum_le_tsum_norm hsummD
      _ ≤ ∑' n : ℕ, ul n * δ := Summable.tsum_le_tsum hterm hsummD (hul_summ.mul_right δ)
      _ = (∑' n : ℕ, ul n) * δ := by rw [tsum_mul_right]
      _ ≤ (2 * K_l / R) * δ := mul_le_mul_of_nonneg_right hul_le hδnn
  have hgood : ∀ Y : ℂ → ℂ,
      (∀ x : ℂ, x ∈ Petal.LeftHalfPlane (R - 1) → ‖Y x‖ ≤ 1 / 2) →
      ∀ x : ℂ, x ∈ Petal.LeftHalfPlane (R - 1) →
      1 / r < ‖x + (1 - a) * Petal.Lambda x + Y x‖
        ∧ 4 ≤ ‖x + (1 - a) * Petal.Lambda x + Y x‖ := by
    intro Y hY x hx
    have hxnorm : R - 1 < ‖x‖ := hΓ_norm x hx
    have hx1 : 1 ≤ ‖x‖ := by linarith
    have hΛ := norm_Lambda_le x hx1
    have hYx : ‖Y x‖ ≤ 1 / 2 := hY x hx
    have hth := hthr ‖x‖ (by linarith)
    have hc : ‖(1 - a) * Petal.Lambda x‖ + ‖Y x‖ ≤ ‖x‖ / 2 := by
      calc ‖(1 - a) * Petal.Lambda x‖ + ‖Y x‖ = ‖1 - a‖ * ‖Petal.Lambda x‖ + ‖Y x‖ := by
            rw [norm_mul]
        _ ≤ ‖1 - a‖ * (2 * Real.sqrt ‖x‖ + 2 * Real.pi) + 1 / 2 := by
            have h1 : 0 ≤ ‖1 - a‖ := norm_nonneg _
            nlinarith
        _ ≤ ‖x‖ / 2 := hth
    have htri : ‖x‖ ≤ ‖x + (1 - a) * Petal.Lambda x + Y x‖
        + (‖(1 - a) * Petal.Lambda x‖ + ‖Y x‖) := by
      calc ‖x‖ = ‖(x + (1 - a) * Petal.Lambda x + Y x)
            - ((1 - a) * Petal.Lambda x + Y x)‖ := by ring_nf
        _ ≤ ‖x + (1 - a) * Petal.Lambda x + Y x‖
            + ‖(1 - a) * Petal.Lambda x + Y x‖ := norm_sub_le _ _
        _ ≤ ‖x + (1 - a) * Petal.Lambda x + Y x‖
            + (‖(1 - a) * Petal.Lambda x‖ + ‖Y x‖) := by
            have h := norm_add_le ((1 - a) * Petal.Lambda x) (Y x)
            linarith
    have h1 : 1 / r < ‖x‖ / 2 := by
      have h2 : 2 / r < ‖x‖ := by linarith
      have h3 : 1 / r = 2 / r / 2 := by ring
      rw [h3]
      linarith
    have h4 : 4 ≤ ‖x‖ / 2 := by
      have h2 : (8 : ℝ) ≤ ‖x‖ := by linarith
      linarith
    exact ⟨by linarith, by linarith⟩
  have hOmdiff : ∀ Y : ℂ → ℂ, DifferentiableOn ℂ Y (Petal.LeftHalfPlane (R - 1)) →
      (∀ x : ℂ, x ∈ Petal.LeftHalfPlane (R - 1) → ‖Y x‖ ≤ 1 / 2) →
      DifferentiableOn ℂ (Petal.Omega f a Y) (Petal.LeftHalfPlane (R - 1)) := by
    intro Y hY hYbd
    have hG := defect_comp_diffOn hb (by linarith : (1 : ℝ) ≤ R - 1) (hgood Y hYbd) hY
    refine Complex.differentiableOn_tsum_of_summable_norm hub_summ ?_ hΓ_open ?_
    · intro n
      have hmaps : Set.MapsTo (fun w : ℂ => w - ((n : ℕ) + 1)) (Petal.LeftHalfPlane (R - 1))
          (Petal.LeftHalfPlane (R - 1)) := by
        intro w hw
        have h := hshift_mem (n + 1) w hw
        rwa [show (((n + 1 : ℕ)) : ℂ) = (n : ℂ) + 1 by push_cast; ring] at h
      have hshiftDiff : DifferentiableOn ℂ (fun w : ℂ => w - ((n : ℕ) + 1))
          (Petal.LeftHalfPlane (R - 1)) := by
        have h1 : DifferentiableOn ℂ (fun w : ℂ => w - ((n : ℂ) + 1))
            (Petal.LeftHalfPlane (R - 1)) := differentiableOn_id.sub_const _
        convert h1 using 1
      have hcomp := hG.comp hshiftDiff hmaps
      convert hcomp using 1
      ext w
      simp only [Function.comp_apply]
    · intro n w hw
      exact hterm_b n Y hYbd w hw
  -- the iteration
  set Ωm : (ℂ → ℂ) → (ℂ → ℂ) := fun Y => Petal.Omega f a Y with hΩmdef
  set Zs : ℕ → ℂ → ℂ := fun n => Ωm^[n] (fun _ => (0 : ℂ)) with hZsdef
  have hZs_zero : Zs 0 = fun _ => (0 : ℂ) := by
    show Ωm^[0] (fun _ => (0 : ℂ)) = fun _ => (0 : ℂ)
    exact Function.iterate_zero_apply (f := Ωm) (x := fun _ => (0 : ℂ))
  have hZs_succ : ∀ n : ℕ, Zs (n + 1) = Ωm (Zs n) := by
    intro n
    show Ωm^[n + 1] (fun _ => (0 : ℂ)) = Ωm (Ωm^[n] (fun _ => (0 : ℂ)))
    exact Function.iterate_succ_apply' _ _ _
  have hZs_bd : ∀ n : ℕ, ∀ w : ℂ, w ∈ Petal.LeftHalfPlane (R - 1) → ‖Zs n w‖ ≤ 1 / 2 := by
    intro n
    induction n with
    | zero => intro w hw; rw [hZs_zero]; simp
    | succ n ih =>
        intro w hw
        rw [hZs_succ n]
        exact hball (Zs n) ih w hw
  have hZs_diff : ∀ n : ℕ, DifferentiableOn ℂ (Zs n) (Petal.LeftHalfPlane (R - 1)) := by
    intro n
    induction n with
    | zero => rw [hZs_zero]; exact differentiableOn_const 0
    | succ n ih =>
        rw [hZs_succ n]
        exact hOmdiff (Zs n) ih (hZs_bd n)
  have hΔ : ∀ n : ℕ, ∀ w : ℂ, w ∈ Petal.LeftHalfPlane (R - 1) →
      ‖Zs (n + 1) w - Zs n w‖ ≤ (1 / 2) * (2 * K_l / R) ^ n := by
    intro n
    induction n with
    | zero =>
        intro w hw
        rw [hZs_succ 0, hZs_zero]
        have h := hball (fun _ => (0 : ℂ)) (fun x hx => by simp) w hw
        simpa using h
    | succ n ih =>
        intro w hw
        have h := hcontr (Zs (n + 1)) (Zs n) (hZs_bd (n + 1)) (hZs_bd n)
          ((1 / 2) * (2 * K_l / R) ^ n) (fun x hx => ih x hx) w hw
        calc ‖Zs (n + 1 + 1) w - Zs (n + 1) w‖
            = ‖Ωm (Zs (n + 1)) w - Ωm (Zs n) w‖ := by rw [hZs_succ (n + 1), hZs_succ n]
          _ ≤ (2 * K_l / R) * ((1 / 2) * (2 * K_l / R) ^ n) := h
          _ = (1 / 2) * (2 * K_l / R) ^ (n + 1) := by rw [pow_succ]; ring
  set Δf : ℕ → ℂ → ℂ := fun n w => Zs (n + 1) w - Zs n w with hΔfdef
  have hu_summ : Summable (fun n : ℕ => (1 / 2) * (2 * K_l / R) ^ n) :=
    (summable_geometric_of_lt_one hκ0 hκ1).mul_left _
  set Z : ℂ → ℂ := fun w => ∑' n : ℕ, Δf n w with hZdef
  have hZ_diff : DifferentiableOn ℂ Z (Petal.LeftHalfPlane (R - 1)) := by
    rw [hZdef]
    refine Complex.differentiableOn_tsum_of_summable_norm hu_summ (fun n => ?_) hΓ_open
      (fun n w hw => hΔ n w hw)
    rw [hΔfdef]
    exact (hZs_diff (n + 1)).sub (hZs_diff n)
  have hZ_tel : ∀ N : ℕ, ∀ w : ℂ, Zs N w = ∑ n ∈ Finset.range N, Δf n w := by
    intro N
    induction N with
    | zero => intro w; rw [hZs_zero]; simp [hΔfdef]
    | succ N ih =>
        intro w
        have h1 := ih w
        calc Zs (N + 1) w = Ωm (Zs N) w := by rw [hZs_succ N]
          _ = ∑ n ∈ Finset.range (N + 1), Δf n w := by
              rw [Finset.sum_range_succ, ← h1]
              simp only [hΔfdef]
              rw [hZs_succ N]
              ring
  have hZ_tail : ∀ (N : ℕ) (w : ℂ), w ∈ Petal.LeftHalfPlane (R - 1) →
      ‖Z w - Zs N w‖ ≤ (1 / 2) * (2 * K_l / R) ^ N / (1 - 2 * K_l / R) := by
    intro N w hw
    have hsumm : Summable (fun n : ℕ => Δf n w) :=
      Summable.of_norm (Summable.of_nonneg_of_le (fun n => norm_nonneg _)
        (fun n => hΔ n w hw) hu_summ)
    have hsplit := hsumm.sum_add_tsum_nat_add N
    have hrepr : Z w - Zs N w = ∑' n : ℕ, Δf (n + N) w := by
      rw [hZdef, hZ_tel N w, sub_eq_iff_eq_add]
      simpa [add_comm] using hsplit.symm
    rw [hrepr]
    have hgs : Summable (fun n : ℕ => (1 / 2) * (2 * K_l / R) ^ (n + N)) := by
      have h := (summable_geometric_of_lt_one hκ0 hκ1).mul_left ((2 * K_l / R) ^ N)
      refine (h.mul_left (1 / 2)).congr (fun n => ?_)
      rw [pow_add]; ring
    have hsumm2 : Summable (fun n : ℕ => ‖Δf (n + N) w‖) :=
      Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => hΔ (n + N) w hw) hgs
    calc ‖∑' n : ℕ, Δf (n + N) w‖ ≤ ∑' n : ℕ, ‖Δf (n + N) w‖ :=
          norm_tsum_le_tsum_norm hsumm2
      _ ≤ ∑' n : ℕ, (1 / 2) * (2 * K_l / R) ^ (n + N) :=
          Summable.tsum_le_tsum (fun n => hΔ (n + N) w hw) hsumm2 hgs
      _ = (1 / 2) * (2 * K_l / R) ^ N / (1 - 2 * K_l / R) := by
          have h1 : (∑' n : ℕ, (1 / 2) * (2 * K_l / R) ^ (n + N))
              = (1 / 2) * (2 * K_l / R) ^ N * ∑' n : ℕ, (2 * K_l / R) ^ n := by
            rw [← tsum_mul_left]
            exact tsum_congr (fun n => by rw [pow_add]; ring)
          rw [h1, tsum_geometric_of_lt_one hκ0 hκ1]
          ring
  have hε_tend : Tendsto (fun N : ℕ => (1 / 2) * (2 * K_l / R) ^ N / (1 - 2 * K_l / R))
      atTop (nhds 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hκ0 hκ1).mul_const (1 / 2 / (1 - 2 * K_l / R))
    rw [zero_mul] at h
    refine h.congr (fun N => ?_)
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  have hZ_bd : ∀ w : ℂ, w ∈ Petal.LeftHalfPlane (R - 1) → ‖Z w‖ ≤ 1 / 2 := by
    intro w hw
    have htend : Tendsto (fun N : ℕ => (1 / 2) * (2 * K_l / R) ^ N / (1 - 2 * K_l / R) + 1 / 2)
        atTop (nhds (1 / 2)) := by
      have h : Tendsto (fun N : ℕ => (1 / 2) * (2 * K_l / R) ^ N / (1 - 2 * K_l / R) + 1 / 2)
          atTop (nhds ((0 : ℝ) + 1 / 2)) := hε_tend.add tendsto_const_nhds
      simpa using h
    refine le_of_tendsto_of_tendsto' tendsto_const_nhds htend (fun N => ?_)
    have h1 := hZ_tail N w hw
    have h2 := hZs_bd N w hw
    have h3 : Z w = (Z w - Zs N w) + Zs N w := by ring
    rw [h3]
    have h4 := norm_add_le (Z w - Zs N w) (Zs N w)
    linarith
  have hfix : ∀ w : ℂ, w ∈ Petal.LeftHalfPlane (R - 1) → Z w = Petal.Omega f a Z w := by
    intro w hw
    have hε2 : Tendsto (fun N : ℕ => 2 * (2 * K_l / R)
        * ((1 / 2) * (2 * K_l / R) ^ N / (1 - 2 * K_l / R))) atTop (nhds 0) := by
      have h := hε_tend.const_mul (2 * (2 * K_l / R))
      simpa using h
    have hnorm : ‖Z w - Petal.Omega f a Z w‖ ≤ 0 := by
      refine le_of_tendsto_of_tendsto' tendsto_const_nhds hε2 (fun N => ?_)
      have h1 := hZ_tail (N + 1) w hw
      have h1' : (1 / 2) * (2 * K_l / R) ^ (N + 1) / (1 - 2 * K_l / R)
          = (2 * K_l / R) * ((1 / 2) * (2 * K_l / R) ^ N / (1 - 2 * K_l / R)) := by
        rw [pow_succ]; ring
      rw [h1'] at h1
      have h2 := hcontr (Zs N) Z (hZs_bd N) hZ_bd
        ((1 / 2) * (2 * K_l / R) ^ N / (1 - 2 * K_l / R))
        (fun x hx => by
          have := hZ_tail N x hx
          rwa [norm_sub_rev] at this) w hw
      have hsucc : Zs (N + 1) w = Petal.Omega f a (Zs N) w := by rw [hZs_succ N]
      rw [hsucc] at h1
      have h4 : Z w - Petal.Omega f a Z w
          = (Z w - Petal.Omega f a (Zs N) w) + (Petal.Omega f a (Zs N) w - Petal.Omega f a Z w) := by
        ring
      rw [h4]
      have h5 := norm_add_le (Z w - Petal.Omega f a (Zs N) w)
        (Petal.Omega f a (Zs N) w - Petal.Omega f a Z w)
      have h6 : (2 : ℝ) * (2 * K_l / R) * ((1 / 2) * (2 * K_l / R) ^ N / (1 - 2 * K_l / R))
          = (2 * K_l / R) * ((1 / 2) * (2 * K_l / R) ^ N / (1 - 2 * K_l / R))
            + (2 * K_l / R) * ((1 / 2) * (2 * K_l / R) ^ N / (1 - 2 * K_l / R)) := by ring
      linarith [h1, h2, h5]
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _)))
  -- assemble
  refine ⟨R, hRpos, hRr', Z, ?_, ?_, ?_⟩
  · exact hZ_diff.mono (fun w hw => by
      rw [Petal.mem_LeftHalfPlane] at hw ⊢; linarith)
  · intro w hw
    exact hZ_bd w (by rw [Petal.mem_LeftHalfPlane] at hw ⊢; linarith)
  · intro w hw
    rw [Petal.mem_LeftHalfPlane] at hw
    have hwΓ : w ∈ Petal.LeftHalfPlane (R - 1) := by
      rw [Petal.mem_LeftHalfPlane]; linarith
    have hw1Γ : w + 1 ∈ Petal.LeftHalfPlane (R - 1) := by
      rw [Petal.mem_LeftHalfPlane]
      simp only [Complex.add_re, Complex.one_re]
      linarith
    have hfix1 := hfix (w + 1) hw1Γ
    have hfix2 := hfix w hwΓ
    have hsummF : Summable (fun n : ℕ => Petal.defect f a (w - (n : ℂ)) (Z (w - (n : ℂ)))) := by
      have h2 : Summable (fun n : ℕ =>
          3 * K_b / ((R - 1 + (n : ℝ)) * Real.sqrt (R - 1 + (n : ℝ)))) := by
        have h := (summable_tsum_inv_mul_sqrt_le (R - 1) (by linarith)).1
        exact (h.mul_left (3 * K_b)).congr (fun n => by rw [mul_one_div])
      exact Summable.of_norm (Summable.of_nonneg_of_le (fun n => norm_nonneg _)
        (fun n => hterm_gen n Z hZ_bd w hwΓ) h2)
    have e1 : Petal.Omega f a Z (w + 1)
        = ∑' n : ℕ, Petal.defect f a (w - (n : ℂ)) (Z (w - (n : ℂ))) := by
      rw [Petal.Omega_apply]
      refine tsum_congr (fun n => ?_)
      rw [show w + 1 - ((n : ℕ) + 1 : ℂ) = w - (n : ℂ) by push_cast; ring]
    have e2 : Petal.Omega f a Z w
        = ∑' n : ℕ, Petal.defect f a (w - (n : ℂ) - 1) (Z (w - (n : ℂ) - 1)) := by
      rw [Petal.Omega_apply]
      refine tsum_congr (fun n => ?_)
      rw [show w - ((n : ℕ) + 1 : ℂ) = w - (n : ℂ) - 1 by push_cast; ring]
    have hstep : (∑' n : ℕ, Petal.defect f a (w - (n : ℂ) - 1) (Z (w - (n : ℂ) - 1)))
        = ∑' n : ℕ, Petal.defect f a (w - ((n + 1 : ℕ) : ℂ)) (Z (w - ((n + 1 : ℕ) : ℂ))) := by
      refine tsum_congr (fun n => ?_)
      rw [show w - (n : ℂ) - 1 = w - ((n + 1 : ℕ) : ℂ) by push_cast; ring]
    have h0 : Petal.defect f a (w - ((0 : ℕ) : ℂ)) (Z (w - ((0 : ℕ) : ℂ)))
        = Petal.defect f a w (Z w) := by norm_num
    have hA : (∑' n : ℕ, Petal.defect f a (w - (n : ℂ)) (Z (w - (n : ℂ))))
        = Petal.defect f a w (Z w)
          + (∑' n : ℕ, Petal.defect f a (w - ((n + 1 : ℕ) : ℂ))
              (Z (w - ((n + 1 : ℕ) : ℂ)))) := by
      have h := hsummF.tsum_eq_zero_add
      simp only [h0] at h
      exact h
    calc Z (w + 1) - Z w
        = Petal.Omega f a Z (w + 1) - Petal.Omega f a Z w := by rw [hfix1, hfix2]
      _ = (∑' n : ℕ, Petal.defect f a (w - (n : ℂ)) (Z (w - (n : ℂ))))
          - (∑' n : ℕ, Petal.defect f a (w - (n : ℂ) - 1) (Z (w - (n : ℂ) - 1))) := by
            rw [e1, e2]
      _ = (∑' n : ℕ, Petal.defect f a (w - (n : ℂ)) (Z (w - (n : ℂ))))
          - (∑' n : ℕ, Petal.defect f a (w - ((n + 1 : ℕ) : ℂ))
              (Z (w - ((n + 1 : ℕ) : ℂ)))) := by rw [hstep]
      _ = Petal.defect f a w (Z w) := by rw [hA]; ring

/-! ## The main theorem -/

theorem exists_conjugacy {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ} (hb : ParabolicBounds f h a r A A') : ∃ R : ℝ, 0 < R ∧ 1 / r < R ∧ ∃ V : ℂ → ℂ, DifferentiableOn ℂ V (Work.FatouCoord.Petal.LeftHalfPlane R) ∧ (∀ w : ℂ, w ∈ Work.FatouCoord.Petal.LeftHalfPlane R → V (w + 1) = wMap f (V w)) ∧ (∀ w : ℂ, w ∈ Work.FatouCoord.Petal.LeftHalfPlane R → ‖V w - w‖ ≤ (1 / 2) * ‖w‖) ∧ (∀ w : ℂ, w ∈ Work.FatouCoord.Petal.LeftHalfPlane R → V w ≠ 0) ∧ Set.InjOn V (Work.FatouCoord.Petal.LeftHalfPlane R) := by
  obtain ⟨R₀, hR₀pos, hrR₀, Z, hZdiff, hZbd, hZeq⟩ := exists_correction_self hb
  obtain ⟨ρ, hρpos, hρinj⟩ := wMap_injOn_large (f := f) (h := h) (a := a) (r := r) hb
  obtain ⟨T₁, hT₁, hthresh⟩ := exists_threshold_sqrt ‖1 - a‖
  set R : ℝ := max (max R₀ (max T₁ 1)) (max (2 * ρ) 2) with hRdef
  have hR₀le : R₀ ≤ R := by
    rw [hRdef]
    exact le_trans (le_max_left R₀ (max T₁ 1)) (le_max_left (max R₀ (max T₁ 1)) (max (2 * ρ) 2))
  have hT₁le : T₁ ≤ R := by
    rw [hRdef]
    exact le_trans (le_trans (le_max_left T₁ 1) (le_max_right R₀ (max T₁ 1)))
      (le_max_left (max R₀ (max T₁ 1)) (max (2 * ρ) 2))
  have h1le : (1 : ℝ) ≤ R := by
    rw [hRdef]
    exact le_trans (le_trans (le_max_right T₁ 1) (le_max_right R₀ (max T₁ 1)))
      (le_max_left (max R₀ (max T₁ 1)) (max (2 * ρ) 2))
  have h2ρle : 2 * ρ ≤ R := by
    rw [hRdef]
    exact le_trans (le_max_left (2 * ρ) 2) (le_max_right (max R₀ (max T₁ 1)) (max (2 * ρ) 2))
  have hRpos : 0 < R := lt_of_lt_of_le one_pos h1le
  have hrR : 1 / r < R := lt_of_lt_of_le hrR₀ hR₀le
  have hsub₀ : Petal.LeftHalfPlane R ⊆ Petal.LeftHalfPlane R₀ := by
    intro w hw
    rw [Petal.mem_LeftHalfPlane] at hw ⊢
    linarith
  have hZdiffR : DifferentiableOn ℂ Z (Petal.LeftHalfPlane R) := hZdiff.mono hsub₀
  have hZbdR : ∀ w : ℂ, w ∈ Petal.LeftHalfPlane R → ‖Z w‖ ≤ 1 / 2 :=
    fun w hw => hZbd w (hsub₀ hw)
  have hZeqR : ∀ w : ℂ, w ∈ Petal.LeftHalfPlane R → Z (w + 1) - Z w = Petal.defect f a w (Z w) :=
    fun w hw => hZeq w (hsub₀ hw)
  set V : ℂ → ℂ := fun u => u + (1 - a) * Petal.Lambda u + Z u with hVdef
  have hnorm_w : ∀ w : ℂ, w ∈ Petal.LeftHalfPlane R → R ≤ ‖w‖ := by
    intro w hw
    rw [Petal.mem_LeftHalfPlane] at hw
    have h := Complex.re_le_norm (-w)
    rw [Complex.neg_re, norm_neg] at h
    linarith
  -- (1) differentiability
  have hVdiff : DifferentiableOn ℂ V (Petal.LeftHalfPlane R) := by
    rw [hVdef]
    exact (differentiableOn_id.add ((differentiableOn_Lambda hRpos.le).const_mul (1 - a))).add hZdiffR
  -- (2) the conjugacy
  have hVconj : ∀ w : ℂ, w ∈ Petal.LeftHalfPlane R → V (w + 1) = wMap f (V w) := by
    intro w hw
    rw [hVdef]
    exact self_conjugacy (f := f) (a := a) hZeqR w hw
  -- (3) the pointwise estimate
  have hVnorm : ∀ w : ℂ, w ∈ Petal.LeftHalfPlane R → ‖V w - w‖ ≤ (1 / 2) * ‖w‖ := by
    intro w hw
    have hwR : R ≤ ‖w‖ := hnorm_w w hw
    have hw1 : (1 : ℝ) ≤ ‖w‖ := le_trans h1le hwR
    have hZ := hZbdR w hw
    have hΛ := norm_Lambda_le w hw1
    have hthr := hthresh ‖w‖ (le_trans hT₁le hwR)
    have hVw : V w - w = (1 - a) * Petal.Lambda w + Z w := by rw [hVdef]; ring
    rw [hVw]
    calc ‖(1 - a) * Petal.Lambda w + Z w‖
        ≤ ‖(1 - a) * Petal.Lambda w‖ + ‖Z w‖ := norm_add_le _ _
      _ = ‖1 - a‖ * ‖Petal.Lambda w‖ + ‖Z w‖ := by rw [norm_mul]
      _ ≤ ‖1 - a‖ * (2 * Real.sqrt ‖w‖ + 2 * Real.pi) + 1 / 2 := by
            have h1 : 0 ≤ ‖1 - a‖ := norm_nonneg _
            nlinarith [hΛ, hZ, h1]
      _ ≤ (1 / 2) * ‖w‖ := by linarith
  -- (4) non-vanishing
  have hVne : ∀ w : ℂ, w ∈ Petal.LeftHalfPlane R → V w ≠ 0 := by
    intro w hw h0
    have hb := hVnorm w hw
    have hwR : R ≤ ‖w‖ := hnorm_w w hw
    have hwpos : 0 < ‖w‖ := lt_of_lt_of_le hRpos hwR
    have h1 : ‖w‖ ≤ ‖V w - w‖ + ‖V w‖ := by
      calc ‖w‖ = ‖(w - V w) + V w‖ := by ring_nf
        _ ≤ ‖w - V w‖ + ‖V w‖ := norm_add_le _ _
        _ = ‖V w - w‖ + ‖V w‖ := by rw [norm_sub_rev]
    have h2 : ‖V w‖ = 0 := by rw [h0, norm_zero]
    rw [h2, add_zero] at h1
    linarith only [h1, hb, hwpos]
  -- (5) injectivity on the half-plane
  have hVinj : Set.InjOn V (Petal.LeftHalfPlane R) := by
    have hnormV : ∀ u : ℂ, u ∈ Petal.LeftHalfPlane R → (1 / 2) * ‖u‖ ≤ ‖V u‖ := by
      intro u hu
      have h1 : ‖u‖ ≤ ‖V u - u‖ + ‖V u‖ := by
        calc ‖u‖ = ‖(u - V u) + V u‖ := by ring_nf
          _ ≤ ‖u - V u‖ + ‖V u‖ := norm_add_le _ _
          _ = ‖V u - u‖ + ‖V u‖ := by rw [norm_sub_rev]
      have h2 := hVnorm u hu
      linarith [norm_nonneg (V u)]
    have hmem : ∀ w : ℂ, w ∈ Petal.LeftHalfPlane R → ∀ n : ℕ,
        w - (n : ℂ) ∈ Petal.LeftHalfPlane R := by
      intro w hw n
      rw [Petal.mem_LeftHalfPlane] at hw ⊢
      simp only [Complex.sub_re, Complex.natCast_re]
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    -- the pointwise values of `V` far to the left are `V u ≈ u`
    have hsn : ∀ w : ℂ, w ∈ Petal.LeftHalfPlane R → ∀ n : ℕ, R ≤ ‖w - (n : ℂ)‖ := by
      intro w hw n
      have h := hnorm_w (w - (n : ℂ)) (hmem w hw n)
      exact h
    intro w₁ hw₁ w₂ hw₂ hVeq
    -- propagation of the equality to the left
    have hprop : ∀ n : ℕ, V (w₁ - (n : ℂ)) = V (w₂ - (n : ℂ)) := by
      intro n
      induction n with
      | zero => simpa using hVeq
      | succ n ih =>
        have h1 : w₁ - ((n + 1 : ℕ) : ℂ) ∈ Petal.LeftHalfPlane R := hmem w₁ hw₁ (n + 1)
        have h2 : w₂ - ((n + 1 : ℕ) : ℂ) ∈ Petal.LeftHalfPlane R := hmem w₂ hw₂ (n + 1)
        have hc1 := hVconj _ h1
        have hc2 := hVconj _ h2
        have e1 : w₁ - ((n + 1 : ℕ) : ℂ) + 1 = w₁ - (n : ℂ) := by push_cast; ring
        have e2 : w₂ - ((n + 1 : ℕ) : ℂ) + 1 = w₂ - (n : ℂ) := by push_cast; ring
        rw [e1] at hc1
        rw [e2] at hc2
        have hkey : wMap f (V (w₁ - ((n + 1 : ℕ) : ℂ)))
            = wMap f (V (w₂ - ((n + 1 : ℕ) : ℂ))) := by rw [← hc1, ← hc2, ih]
        have hb1 : ρ ≤ ‖V (w₁ - ((n + 1 : ℕ) : ℂ))‖ := by
          have h3 := hnormV _ h1
          have h4 : R / 2 ≤ (1 / 2) * ‖w₁ - ((n + 1 : ℕ) : ℂ)‖ := by
            have h5 := hsn w₁ hw₁ (n + 1)
            linarith
          linarith
        have hb2 : ρ ≤ ‖V (w₂ - ((n + 1 : ℕ) : ℂ))‖ := by
          have h3 := hnormV _ h2
          have h4 : R / 2 ≤ (1 / 2) * ‖w₂ - ((n + 1 : ℕ) : ℂ)‖ := by
            have h5 := hsn w₂ hw₂ (n + 1)
            linarith
          linarith
        exact hρinj hb1 hb2 hkey
    -- far to the left the two points have to be compared
    set m : ℝ := max w₁.re w₂.re with hmdef
    obtain ⟨n : ℕ, hn⟩ := exists_nat_gt (m + max (4 * ‖1 - a‖ + 2) (R + 5))
    set T : ℝ := (n : ℝ) - m - 1 with hTdef
    have hT4 : 4 * ‖1 - a‖ + 1 ≤ T := by
      rw [hTdef]
      have := le_max_left (4 * ‖1 - a‖ + 2) (R + 5)
      linarith
    have hTR4 : R + 4 ≤ T := by
      rw [hTdef]
      have := le_max_right (4 * ‖1 - a‖ + 2) (R + 5)
      linarith
    have hTpos : 0 < T := by
      have h1 : (0 : ℝ) ≤ ‖1 - a‖ := norm_nonneg _
      linarith
    have hTR : R < T := by linarith
    have hxT : w₁ - (n : ℂ) ∈ Petal.LeftHalfPlane T := by
      rw [Petal.mem_LeftHalfPlane, Complex.sub_re, Complex.natCast_re, hTdef]
      have hm : w₁.re ≤ m := by rw [hmdef]; exact le_max_left _ _
      linarith
    have hyT : w₂ - (n : ℂ) ∈ Petal.LeftHalfPlane T := by
      rw [Petal.mem_LeftHalfPlane, Complex.sub_re, Complex.natCast_re, hTdef]
      have hm : w₂.re ≤ m := by rw [hmdef]; exact le_max_right _ _
      linarith
    have heq := hprop n
    have hxy : w₁ - (n : ℂ) - (w₂ - (n : ℂ)) = w₁ - w₂ := by ring
    have hid : w₁ - w₂ + (1 - a) * (Petal.Lambda (w₁ - (n : ℂ)) - Petal.Lambda (w₂ - (n : ℂ)))
        + (Z (w₁ - (n : ℂ)) - Z (w₂ - (n : ℂ))) = 0 := by
      have hsub : V (w₁ - (n : ℂ)) - V (w₂ - (n : ℂ)) = 0 := by rw [heq]; ring
      have hstep : (w₁ - (n : ℂ)) - (w₂ - (n : ℂ))
            + (1 - a) * (Petal.Lambda (w₁ - (n : ℂ)) - Petal.Lambda (w₂ - (n : ℂ)))
            + (Z (w₁ - (n : ℂ)) - Z (w₂ - (n : ℂ)))
          = V (w₁ - (n : ℂ)) - V (w₂ - (n : ℂ)) := by rw [hVdef]; ring
      rw [← hxy, hstep]
      exact hsub
    have hL := norm_Lambda_sub_le_aux (x := w₁ - (n : ℂ)) (y := w₂ - (n : ℂ)) hTpos hxT hyT
    rw [hxy] at hL
    have hZb := norm_Z_sub_le hRpos hZdiffR hZbdR hTR hxT hyT
    rw [hxy] at hZb
    have htri : ‖w₁ - w₂‖ ≤ ‖1 - a‖ * ‖Petal.Lambda (w₁ - (n : ℂ)) - Petal.Lambda (w₂ - (n : ℂ))‖
        + ‖Z (w₁ - (n : ℂ)) - Z (w₂ - (n : ℂ))‖ := by
      have h1 : w₁ - w₂ = -((1 - a) * (Petal.Lambda (w₁ - (n : ℂ)) - Petal.Lambda (w₂ - (n : ℂ)))
          + (Z (w₁ - (n : ℂ)) - Z (w₂ - (n : ℂ)))) := by
        rw [eq_neg_iff_add_eq_zero]
        simpa only [add_assoc] using hid
      rw [h1]
      calc ‖-((1 - a) * (Petal.Lambda (w₁ - (n : ℂ)) - Petal.Lambda (w₂ - (n : ℂ)))
            + (Z (w₁ - (n : ℂ)) - Z (w₂ - (n : ℂ))))‖
          = ‖(1 - a) * (Petal.Lambda (w₁ - (n : ℂ)) - Petal.Lambda (w₂ - (n : ℂ)))
            + (Z (w₁ - (n : ℂ)) - Z (w₂ - (n : ℂ)))‖ := norm_neg _
        _ ≤ ‖(1 - a) * (Petal.Lambda (w₁ - (n : ℂ)) - Petal.Lambda (w₂ - (n : ℂ)))‖
            + ‖Z (w₁ - (n : ℂ)) - Z (w₂ - (n : ℂ))‖ := norm_add_le _ _
        _ = ‖1 - a‖ * ‖Petal.Lambda (w₁ - (n : ℂ)) - Petal.Lambda (w₂ - (n : ℂ))‖
            + ‖Z (w₁ - (n : ℂ)) - Z (w₂ - (n : ℂ))‖ := by rw [norm_mul]
    have hsum : ‖1 - a‖ / T + 1 / (T - R) ≤ 1 / 2 := by
      have hTRpos : 0 < T - R := by linarith
      have hterm1 : ‖1 - a‖ / T ≤ 1 / 4 := by
        rw [div_le_iff₀ hTpos]
        nlinarith [norm_nonneg (1 - a)]
      have hterm2 : 1 / (T - R) ≤ 1 / 4 := by
        rw [div_le_iff₀ hTRpos]
        linarith
      linarith
    have hfinal : ‖w₁ - w₂‖ ≤ (1 / 2) * ‖w₁ - w₂‖ := by
      calc ‖w₁ - w₂‖
          ≤ ‖1 - a‖ * (‖w₁ - w₂‖ / T) + (1 / (T - R)) * ‖w₁ - w₂‖ := by
            have := add_le_add (mul_le_mul_of_nonneg_left hL (norm_nonneg (1 - a))) hZb
            linarith
        _ = (‖1 - a‖ / T + 1 / (T - R)) * ‖w₁ - w₂‖ := by ring
        _ ≤ (1 / 2) * ‖w₁ - w₂‖ := mul_le_mul_of_nonneg_right hsum (norm_nonneg _)
    have hzero : ‖w₁ - w₂‖ = 0 := by nlinarith [norm_nonneg (w₁ - w₂)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hzero)
  exact ⟨R, hRpos, hrR, V, hVdiff, hVconj, hVnorm, hVne, hVinj⟩

end

end Work.FatouCoord.Repelling
