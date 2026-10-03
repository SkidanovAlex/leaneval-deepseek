import Mathlib
import Submission.Commons.NumberTheory.Linnik.logDeriv_circle_residue
import Submission.Commons.NumberTheory.Linnik.completedL_pf_identity_rect
import Submission.Commons.NumberTheory.Linnik.goodRadius_geometric
import Submission.Commons.NumberTheory.Linnik.divisor_eq_closedBall_subset
import Submission.Work.FIArea5.HeckeZFR.Hadm.log_norm_finprod_zpow_le
import Submission.Commons.Analysis.Complex.circleLogDerivContour_bound

namespace Work.FIArea5.HeckeZFR.Hadm

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## Helper lemmas for the cofactor bound

These are the analytic ingredients of `cofactorBound`, stated in the generality in which they are
used:

* `cof_finprod_log_ge` / `cof_finprod_ne_zero` — the canonical product
  `∏ᶠ u, (z - u) ^ (d u)` against a point `z` off its (finite) support;
* `cof_ball_log_le` — the maximum principle transfer from the circle `‖z‖ = T` to the ball;
* `cof_rawBound_le`, `cof_logT_mul_le` — the elementary real inequalities that absorb the divisor
  budget and the `log T` factor into `T (log (T+2) + K + 1)²`;
* `cof_sphere_log_le` — the Jensen/Borel–Carathéodory estimate for the cofactor on a good circle.
-/

/-- Lower bound for the log-norm of the canonical product `∏ᶠ u, (z-u)^{d u}`: if all exponents
`d u` are nonnegative and `B ≤ Real.log ‖z - u‖` for every `u` in the finite support of `d`, then
`(∑ᶠ u, d u) * B ≤ Real.log ‖∏ᶠ u, (z-u)^{d u}‖`. -/
lemma cof_finprod_log_ge {d : ℂ → ℤ} (hsupp : (Function.support d).Finite)
    (hdn : ∀ u : ℂ, 0 ≤ d u) {z : ℂ} {B : ℝ}
    (hz : ∀ u : ℂ, d u ≠ 0 → z ≠ u)
    (hB : ∀ u : ℂ, d u ≠ 0 → B ≤ Real.log ‖z - u‖) :
    (∑ᶠ u : ℂ, ((d u : ℤ) : ℝ)) * B ≤ Real.log ‖∏ᶠ u : ℂ, (z - u) ^ (d u)‖ := by
  classical
  have hmem : ∀ u : ℂ, u ∈ hsupp.toFinset ↔ d u ≠ 0 := by
    intro u; rw [hsupp.mem_toFinset, Function.mem_support]
  have hmul : Function.mulSupport (fun u : ℂ => (z - u) ^ (d u)) ⊆ Function.support d := by
    intro u hu
    rw [Function.mem_support]
    intro hdu
    rw [Function.mem_mulSupport] at hu
    exact hu (by simp [hdu])
  have hfne : ∀ u : ℂ, u ∈ hsupp.toFinset → (z - u) ^ (d u) ≠ 0 := by
    intro u hu
    exact zpow_ne_zero _ (sub_ne_zero.mpr (hz u ((hmem u).mp hu)))
  have hnorm_ne : ∀ u : ℂ, u ∈ hsupp.toFinset → ‖(z - u) ^ (d u)‖ ≠ 0 :=
    fun u hu => norm_ne_zero_iff.mpr (hfne u hu)
  have hsum : Function.support (fun u : ℂ => ((d u : ℤ) : ℝ)) ⊆ Function.support d := by
    intro u hu
    rw [Function.mem_support] at hu ⊢
    intro hdu
    exact hu (by simp [hdu])
  rw [finsum_eq_sum_of_support_subset_of_finite (fun u : ℂ => ((d u : ℤ) : ℝ)) hsum hsupp,
      finprod_eq_prod_of_mulSupport_subset_of_finite (fun u : ℂ => (z - u) ^ (d u)) hmul hsupp,
      norm_prod, Real.log_prod hnorm_ne]
  simp only [Complex.norm_zpow, Real.log_zpow]
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum
    (fun u hu => mul_le_mul_of_nonneg_left (hB u ((hmem u).mp hu)) (Int.cast_nonneg (hdn u)))

/-- The canonical product `∏ᶠ u, (z-u)^{d u}` does not vanish at a point `z` that avoids the finite
support of `d`. -/
lemma cof_finprod_ne_zero {d : ℂ → ℤ} (hsupp : (Function.support d).Finite)
    {z : ℂ} (hz : ∀ u : ℂ, d u ≠ 0 → z ≠ u) :
    (∏ᶠ u : ℂ, (z - u) ^ (d u)) ≠ 0 := by
  classical
  have hmul : Function.mulSupport (fun u : ℂ => (z - u) ^ (d u)) ⊆ Function.support d := by
    intro u hu
    rw [Function.mem_support]
    intro hdu
    rw [Function.mem_mulSupport] at hu
    exact hu (by simp [hdu])
  rw [finprod_eq_prod_of_mulSupport_subset_of_finite (fun u : ℂ => (z - u) ^ (d u)) hmul hsupp]
  refine Finset.prod_ne_zero_iff.mpr (fun u hu => zpow_ne_zero _ (sub_ne_zero.mpr ?_))
  have hdu : d u ≠ 0 := by
    have := hsupp.mem_toFinset.mp hu
    rwa [Function.mem_support] at this
  exact hz u hdu

/-- Maximum principle transfer: an analytic function on the ball of radius `T + ε` (`ε > 0`) whose
log-norm is bounded by `B ≥ 0` on the circle of radius `T` has log-norm bounded by `B` on the whole
open ball of radius `T`. -/
lemma cof_ball_log_le {g : ℂ → ℂ} {T ε B : ℝ} (hT : 0 < T) (hε : 0 < ε)
    (hg : AnalyticOnNhd ℂ g (Metric.ball 0 (T + ε))) (hB0 : 0 ≤ B)
    (hsphere : ∀ z : ℂ, ‖z‖ = T → Real.log ‖g z‖ ≤ B) :
    ∀ w : ℂ, w ∈ Metric.ball 0 T → Real.log ‖g w‖ ≤ B := by
  have hexp : ∀ z : ℂ, ‖z‖ = T → ‖g z‖ ≤ Real.exp B := by
    intro z hz
    rcases lt_or_eq_of_le (norm_nonneg (g z)) with h | h
    · exact (Real.log_le_iff_le_exp h).mp (hsphere z hz)
    · rw [← h]; exact (Real.exp_pos B).le
  have hsub : Metric.closedBall (0 : ℂ) T ⊆ Metric.ball 0 (T + ε) := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    rw [Metric.mem_ball, dist_eq_norm]
    linarith
  have hDiffBall : DifferentiableOn ℂ g (Metric.ball 0 T) :=
    hg.differentiableOn.mono (Metric.ball_subset_ball (by linarith))
  have hContCl : ContinuousOn g (Metric.closedBall 0 T) := hg.continuousOn.mono hsub
  have hDiffCl : DiffContOnCl ℂ g (Metric.ball 0 T) := DiffContOnCl.mk_ball hDiffBall hContCl
  intro w hw
  have hfront : ∀ z ∈ frontier (Metric.ball 0 T), ‖g z‖ ≤ Real.exp B := by
    intro z hz
    have hz' : ‖z‖ = T := by
      have h := hz
      rw [frontier_ball (0 : ℂ) (ne_of_gt hT), Metric.mem_sphere, dist_eq_norm] at h
      simpa using h
    exact hexp z hz'
  have hwcl : w ∈ closure (Metric.ball 0 T) := subset_closure hw
  have hnorm : ‖g w‖ ≤ Real.exp B :=
    Complex.norm_le_of_forall_mem_frontier_norm_le
      (Metric.isBounded_ball (x := (0 : ℂ)) (r := T)) hDiffCl hfront hwcl
  rcases lt_or_eq_of_le (norm_nonneg (g w)) with h | h
  · have h1 : Real.log ‖g w‖ ≤ Real.log (Real.exp B) := Real.log_le_log h hnorm
    rwa [Real.log_exp] at h1
  · rw [← h, Real.log_zero]; exact hB0

/-- Elementary real inequality absorbing the canonical-product factors into `(C + 2c) T L²`
with `L = log (T+2) + K + 1`. -/
lemma cof_rawBound_le (C K c A T : ℝ) (hC : 0 < C) (hc : 0 ≤ c) (hK : 0 ≤ K) (hA : 1 ≤ A)
    (hAT : A ≤ T) :
    C * T * (Real.log (T + 2) + K) +
        2 * Real.log (Real.log (A + 2) + K + 1) * (c * T * (Real.log (T + 2) + K)) ≤
      (C + 2 * c) * T * (Real.log (T + 2) + K + 1) ^ 2 := by
  have hT1 : 1 ≤ T := le_trans hA hAT
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT1
  set P : ℝ := Real.log (T + 2) + K with hP
  set Q : ℝ := Real.log (Real.log (A + 2) + K + 1) with hQ
  have hP0 : 0 ≤ P := by
    rw [hP]
    have : 0 ≤ Real.log (T + 2) := Real.log_nonneg (by linarith)
    linarith
  have hLpos : 0 < Real.log (A + 2) + K + 1 := by
    have : 0 ≤ Real.log (A + 2) := Real.log_nonneg (by linarith)
    linarith
  have hQle : Q ≤ P := by
    rw [hQ, hP]
    have h1 : Real.log (Real.log (A + 2) + K + 1) ≤ Real.log (Real.log (T + 2) + K + 1) := by
      apply Real.log_le_log hLpos
      have h2 : Real.log (A + 2) ≤ Real.log (T + 2) :=
        Real.log_le_log (by linarith) (by linarith)
      linarith
    have h3 : Real.log (Real.log (T + 2) + K + 1) ≤ Real.log (T + 2) + K := by
      have h4 : Real.log (Real.log (T + 2) + K + 1) ≤ (Real.log (T + 2) + K + 1) - 1 :=
        Real.log_le_sub_one_of_pos (by
          have : 0 ≤ Real.log (T + 2) := Real.log_nonneg (by linarith)
          linarith)
      linarith
    linarith
  have hTnn : 0 ≤ T := hTpos.le
  have hkey1 : C * T * P ≤ C * T * (P + 1) ^ 2 := by
    have h : P ≤ (P + 1) ^ 2 := by nlinarith
    have h2 := mul_le_mul_of_nonneg_left h (mul_nonneg hC.le hTnn)
    calc C * T * P = (C * T) * P := by ring
      _ ≤ (C * T) * (P + 1) ^ 2 := h2
      _ = C * T * (P + 1) ^ 2 := by ring
  have hkey2 : 2 * Q * (c * T * P) ≤ 2 * c * T * (P + 1) ^ 2 := by
    have hctp : 0 ≤ c * T * P := mul_nonneg (mul_nonneg hc hTnn) hP0
    have h1 : 2 * Q * (c * T * P) ≤ 2 * P * (c * T * P) := by
      have h2 : 0 ≤ 2 * (c * T * P) := by linarith
      nlinarith [mul_le_mul_of_nonneg_right hQle h2]
    have h3 : 2 * P * (c * T * P) ≤ 2 * c * T * (P + 1) ^ 2 := by
      have h4 : P * P ≤ (P + 1) ^ 2 := by nlinarith
      have h5 : 0 ≤ 2 * c * T := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h4 h5]
    linarith
  linarith [hkey1, hkey2]

/-- Elementary real inequality absorbing the `log T` factor coming from the canonical product at the
origin into `(C + 4c) T L²` with `L = log (T+2) + K + 1`. -/
lemma cof_logT_mul_le (C K c T : ℝ) (hC : 0 < C) (hc : 0 ≤ c) (hK : 0 ≤ K) (hT : 1 ≤ T) :
    c * T * (Real.log (T + 2) + K) * Real.log T ≤
      (C + 4 * c) * T * (Real.log (T + 2) + K + 1) ^ 2 := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg hT
  have hP0 : 0 ≤ Real.log (T + 2) + K := by
    have : 0 ≤ Real.log (T + 2) := Real.log_nonneg (by linarith)
    linarith
  have hP1 : 0 ≤ Real.log (T + 2) + K + 1 := by linarith
  have hlogT_le : Real.log T ≤ Real.log (T + 2) + K + 1 := by
    have h1 : Real.log T ≤ Real.log (T + 2) := Real.log_le_log hTpos (by linarith)
    linarith
  have hstep1 : (Real.log (T + 2) + K) * Real.log T ≤
      (Real.log (T + 2) + K + 1) * (Real.log (T + 2) + K + 1) :=
    mul_le_mul (by linarith) hlogT_le hlogT0 hP1
  have hct : 0 ≤ c * T := mul_nonneg hc hTpos.le
  have hstep2 : c * T * (Real.log (T + 2) + K) * Real.log T ≤
      c * T * ((Real.log (T + 2) + K + 1) * (Real.log (T + 2) + K + 1)) := by
    rw [show c * T * (Real.log (T + 2) + K) * Real.log T
        = (c * T) * ((Real.log (T + 2) + K) * Real.log T) by ring]
    exact mul_le_mul_of_nonneg_left hstep1 hct
  have hstep3 : c * T * ((Real.log (T + 2) + K + 1) * (Real.log (T + 2) + K + 1)) ≤
      (C + 4 * c) * T * (Real.log (T + 2) + K + 1) ^ 2 := by
    have hle : c * T ≤ (C + 4 * c) * T :=
      mul_le_mul_of_nonneg_right (by linarith) hTpos.le
    rw [show c * T * ((Real.log (T + 2) + K + 1) * (Real.log (T + 2) + K + 1))
        = (c * T) * (Real.log (T + 2) + K + 1) ^ 2 by ring]
    rw [show (C + 4 * c) * T * (Real.log (T + 2) + K + 1) ^ 2
        = ((C + 4 * c) * T) * (Real.log (T + 2) + K + 1) ^ 2 by ring]
    exact mul_le_mul_of_nonneg_right hle (by positivity)
  linarith [hstep2, hstep3]

/-- **Sphere bound for the cofactor.**  If `Λ` is entire with circle growth
`log ‖Λ z‖ ≤ C·T·(log (T+2) + K)` on the circle of radius `T` and divisor budget
`c·T·(log (T+2) + K)`, `T` is a good radius (`(log (A+2) + K + 1)^2 · |‖u‖ - T| ≥ 1` at every zero
`u` of `Λ`), `1 ≤ A ≤ T`, and `g` is the cofactor satisfying
`Λ z = (∏ᶠ u, (z-u)^{ord u}) · g z` at every `z` with `‖z‖ = T`, then
`log ‖g z‖ ≤ C·T·(log (T+2) + K) + 2·log (log (A+2) + K + 1) · Z` on that circle, where
`Z = ∑ᶠ u, ord u` is the total zero multiplicity in the closed ball of radius `T`. -/
lemma cof_sphere_log_le (Λ g : ℂ → ℂ) (C K c A T : ℝ)
    (hΛ : Differentiable ℂ Λ) (hC : 0 < C) (hK : 0 ≤ K) (hc : 0 ≤ c) (hA : 1 ≤ A) (hAT : A ≤ T)
    (hgrowth : ∀ z : ℂ, ‖z‖ = T → Real.log ‖Λ z‖ ≤ C * T * (Real.log (T + 2) + K))
    (hcount : (∑ᶠ u : ℂ, ((MeromorphicOn.divisor Λ (Metric.closedBall 0 T)) u : ℝ)) ≤
        c * T * (Real.log (T + 2) + K))
    (hgood : ∀ u : ℂ, Λ u = 0 → (Real.log (A + 2) + K + 1) ^ 2 * |‖u‖ - T| ≥ 1)
    (hfac : ∀ z : ℂ, ‖z‖ = T →
      Λ z = (∏ᶠ u : ℂ, (z - u) ^ (MeromorphicOn.divisor Λ (Metric.closedBall 0 T) u)) * g z) :
    ∀ z : ℂ, ‖z‖ = T →
      Real.log ‖g z‖ ≤ C * T * (Real.log (T + 2) + K) +
        2 * Real.log (Real.log (A + 2) + K + 1) *
          (∑ᶠ u : ℂ, ((MeromorphicOn.divisor Λ (Metric.closedBall 0 T)) u : ℝ)) := by
  intro z hz
  have hT1 : 1 ≤ T := le_trans hA hAT
  have hLpos : 0 < Real.log (A + 2) + K + 1 := by
    have h1 : 0 ≤ Real.log (A + 2) := Real.log_nonneg (by linarith)
    linarith
  have hL2pos : 0 < (Real.log (A + 2) + K + 1) ^ 2 := pow_pos hLpos 2
  have hΛz : Λ z ≠ 0 := by
    intro hz0
    have h := hgood z hz0
    simp only [hz, sub_self, abs_zero, mul_zero] at h
    norm_num at h
  have hΛan : AnalyticOnNhd ℂ Λ (Metric.closedBall 0 T) :=
    Commons.Analysis.Complex.analyticOnNhd_closedBall_of_differentiable hΛ _
  let d : ℂ → ℤ := fun u => MeromorphicOn.divisor Λ (Metric.closedBall 0 T) u
  have hdnn : ∀ u : ℂ, 0 ≤ d u := fun u => MeromorphicOn.AnalyticOnNhd.divisor_nonneg hΛan u
  have hsupp : (Function.support d).Finite :=
    MeromorphicOn.divisor_support_finite_of_subset hΛan.meromorphicOn
      (isCompact_closedBall (0 : ℂ) T) (by intro x hx; exact hx)
  have hdzero : ∀ u : ℂ, d u ≠ 0 → Λ u = 0 := fun u hdu =>
    Commons.Analysis.Complex.zero_of_divisor_ne_zero hΛan (by simpa [d] using hdu)
  have hz_ne : ∀ u : ℂ, d u ≠ 0 → z ≠ u := by
    intro u hdu hzu
    have h := hgood u (hdzero u hdu)
    simp only [← hzu, hz, sub_self, abs_zero, mul_zero] at h
    norm_num at h
  have hBfun : ∀ u : ℂ, d u ≠ 0 →
      -(2 * Real.log (Real.log (A + 2) + K + 1)) ≤ Real.log ‖z - u‖ := by
    intro u hdu
    have hdist : 1 / (Real.log (A + 2) + K + 1) ^ 2 ≤ ‖z - u‖ := by
      have hgoodu := hgood u (hdzero u hdu)
      have habs : |‖u‖ - T| ≤ ‖z - u‖ := by
        have h1 : |‖u‖ - T| = |‖u‖ - ‖z‖| := by rw [hz]
        rw [h1, abs_sub_comm]
        exact abs_norm_sub_norm_le z u
      have h2 : (1 : ℝ) ≤ (Real.log (A + 2) + K + 1) ^ 2 * ‖z - u‖ :=
        le_trans hgoodu (mul_le_mul_of_nonneg_left habs hL2pos.le)
      exact (div_le_iff₀ hL2pos).mpr (by rwa [mul_comm] at h2)
    have h3 : Real.log (1 / (Real.log (A + 2) + K + 1) ^ 2) ≤ Real.log ‖z - u‖ :=
      Real.log_le_log (by positivity) hdist
    have h4 : Real.log (1 / (Real.log (A + 2) + K + 1) ^ 2)
        = -(2 * Real.log (Real.log (A + 2) + K + 1)) := by
      rw [one_div, Real.log_inv, Real.log_pow]
      ring
    rwa [h4] at h3
  have hlow := cof_finprod_log_ge (d := d) hsupp hdnn (z := z)
    (B := -(2 * Real.log (Real.log (A + 2) + K + 1))) hz_ne hBfun
  have hlow' : -(2 * Real.log (Real.log (A + 2) + K + 1)) * (∑ᶠ u : ℂ, ((d u : ℤ) : ℝ)) ≤
      Real.log ‖∏ᶠ u : ℂ, (z - u) ^ (d u)‖ := by
    simpa [mul_comm] using hlow
  have hPne : (∏ᶠ u : ℂ, (z - u) ^ (d u)) ≠ 0 := cof_finprod_ne_zero hsupp hz_ne
  have hgne : g z ≠ 0 := by
    intro hgz
    have h := hfac z hz
    rw [hgz, mul_zero] at h
    exact hΛz h
  have hsplit : Real.log ‖Λ z‖ = Real.log ‖∏ᶠ u : ℂ, (z - u) ^ (d u)‖ + Real.log ‖g z‖ := by
    rw [hfac z hz, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hPne) (norm_ne_zero_iff.mpr hgne)]
  have hgrowth_z := hgrowth z hz
  have hfinal : Real.log ‖g z‖ ≤ C * T * (Real.log (T + 2) + K) +
      2 * Real.log (Real.log (A + 2) + K + 1) * (∑ᶠ u : ℂ, ((d u : ℤ) : ℝ)) := by
    nlinarith [hsplit, hgrowth_z, hlow']
  simpa [d] using hfinal

/-- **Cofactor bound at a good radius** (Jensen/Borel–Carathéodory).  With `Λ` entire, `Λ 0 ≠ 0`,
circle growth `C·R·(log (R+2) + K)` and divisor bound `c·R·(log (R+2) + K)`, at every good radius
`T` the canonical-product cofactor `g` (which satisfies `Λ = ∏_u (z-u)^{ord u} · g` on the ball of
radius `T + ε` and is zero-free there) admits a sup bound
`M0 ≤ (C + 4c)·T·(log (T+2) + K + 1)^2 + A₀`, together with `|log ‖g 0‖| ≤ M0`. -/
theorem cofactorBound (Λ : ℂ → ℂ) (hDiff : Differentiable ℂ Λ) (h0 : Λ 0 ≠ 0)
    (C K c : ℝ) (hC : 0 < C) (hK : 0 ≤ K) (hc : 0 ≤ c)
    (hgrowth : ∀ R : ℝ, 1 ≤ R → ∀ z : ℂ, ‖z‖ = R →
      Real.log ‖Λ z‖ ≤ C * R * (Real.log (R + 2) + K))
    (hcount : ∀ R : ℝ, 1 ≤ R →
      (∑ᶠ u : ℂ, ((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℝ)) ≤
        c * R * (Real.log (R + 2) + K)) :
    ∃ A₀ : ℝ, 0 ≤ A₀ ∧ ∀ A T : ℝ, 1 ≤ A → A ≤ T → T ≤ 2 * A →
      (∀ u : ℂ, Λ u = 0 → (Real.log (A + 2) + K + 1) ^ 2 * |‖u‖ - T| ≥ 1) →
      ∃ (g : ℂ → ℂ) (ε M0 : ℝ), 0 < ε ∧ 0 ≤ M0 ∧
        AnalyticOnNhd ℂ g (Metric.ball 0 (T + ε)) ∧
        (∀ w : ℂ, w ∈ Metric.ball 0 (T + ε) → g w ≠ 0) ∧
        (∀ z : ℂ, z ∈ Metric.ball 0 (T + ε) →
          Λ z = (∏ᶠ u : ℂ, (z - u) ^ (MeromorphicOn.divisor Λ (Metric.closedBall 0 T) u)) * g z) ∧
        (∀ w : ℂ, w ∈ Metric.ball 0 T → Real.log ‖g w‖ ≤ M0) ∧
        |Real.log ‖g 0‖| ≤ M0 ∧
        M0 ≤ (C + 4 * c) * T * (Real.log (T + 2) + K + 1) ^ 2 + A₀ := by
  set A₀ : ℝ := max 0 (-(Real.log ‖Λ 0‖)) with hA₀
  have hA₀nn : 0 ≤ A₀ := by rw [hA₀]; exact le_max_left 0 _
  refine ⟨A₀, hA₀nn, ?_⟩
  intro A T hA1 hAT hT2A hgood
  have hT1 : 1 ≤ T := le_trans hA1 hAT
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT1
  have hcirc : ∀ u : ℂ, ‖u‖ = T → Λ u ≠ 0 := by
    intro u hu hzu
    have h := hgood u hzu
    simp only [hu, sub_self, abs_zero, mul_zero] at h
    norm_num at h
  obtain ⟨g, ε, hε, hg_an, hg_nz, hfac⟩ :=
    Commons.NumberTheory.Linnik.factorization_open (f := Λ) (R := T) hTpos hDiff h0 hcirc
  have hΛan : AnalyticOnNhd ℂ Λ (Metric.closedBall 0 T) :=
    Commons.Analysis.Complex.analyticOnNhd_closedBall_of_differentiable hDiff _
  let d : ℂ → ℤ := fun u => MeromorphicOn.divisor Λ (Metric.closedBall 0 T) u
  have hdnn : ∀ u : ℂ, 0 ≤ d u := fun u => MeromorphicOn.AnalyticOnNhd.divisor_nonneg hΛan u
  have hsupp : (Function.support d).Finite :=
    MeromorphicOn.divisor_support_finite_of_subset hΛan.meromorphicOn
      (isCompact_closedBall (0 : ℂ) T) (by intro x hx; exact hx)
  have hdzero : ∀ u : ℂ, d u ≠ 0 → Λ u = 0 := fun u hdu =>
    Commons.Analysis.Complex.zero_of_divisor_ne_zero hΛan (by simpa [d] using hdu)
  set N : ℝ := ∑ᶠ u : ℂ, ((MeromorphicOn.divisor Λ (Metric.closedBall 0 T)) u : ℝ) with hN
  have hNsum : (∑ᶠ u : ℂ, ((d u : ℤ) : ℝ)) = N := by rw [hN]
  have hN_le : N ≤ c * T * (Real.log (T + 2) + K) := hcount T hT1
  have hN0 : 0 ≤ N := by
    rw [← hNsum]
    exact finsum_nonneg (fun u => by have := hdnn u; exact_mod_cast this)
  have hlogLnneg : 0 ≤ Real.log (Real.log (A + 2) + K + 1) := by
    apply Real.log_nonneg
    have : 0 ≤ Real.log (A + 2) := Real.log_nonneg (by linarith)
    linarith
  have hP2nn : 0 ≤ Real.log (T + 2) + K := by
    have : 0 ≤ Real.log (T + 2) := Real.log_nonneg (by linarith)
    linarith
  set B : ℝ := C * T * (Real.log (T + 2) + K) +
      2 * Real.log (Real.log (A + 2) + K + 1) * N with hB
  have hBnn : 0 ≤ B := by
    rw [hB]
    exact add_nonneg (mul_nonneg (mul_nonneg hC.le hTpos.le) hP2nn)
      (mul_nonneg (by linarith) hN0)
  -- sphere bound for the cofactor
  have hfac' : ∀ z : ℂ, ‖z‖ = T →
      Λ z = (∏ᶠ u : ℂ, (z - u) ^ (MeromorphicOn.divisor Λ (Metric.closedBall 0 T) u)) * g z := by
    intro z hz
    refine hfac z ?_
    rw [Metric.mem_ball, dist_eq_norm, sub_zero, hz]
    linarith
  have hsphere_raw := cof_sphere_log_le Λ g C K c A T hDiff hC hK hc hA1 hAT
    (fun z hz => hgrowth T hT1 z hz) (hcount T hT1) hgood hfac'
  have hsphere : ∀ z : ℂ, ‖z‖ = T → Real.log ‖g z‖ ≤ B := by
    intro z hz
    have h := hsphere_raw z hz
    rw [hB, hN]
    exact h
  -- the bound on the ball of radius T
  have hball : ∀ w : ℂ, w ∈ Metric.ball 0 T → Real.log ‖g w‖ ≤ B :=
    cof_ball_log_le hTpos hε hg_an hBnn hsphere
  -- the canonical product at the origin
  have hune : ∀ u : ℂ, d u ≠ 0 → u ≠ 0 := by
    intro u hdu hu0
    have hΛu : Λ u = 0 := hdzero u hdu
    rw [hu0] at hΛu
    exact h0 hΛu
  have hP0le : Real.log ‖∏ᶠ u : ℂ, ((0 : ℂ) - u) ^ (d u)‖ ≤
      (∑ᶠ u : ℂ, ((d u : ℤ) : ℝ)) * Real.log T := by
    refine log_norm_finprod_zpow_le hsupp hdnn (z := 0) (B := Real.log T) (Real.log_nonneg hT1)
      ?_ ?_
    · intro u hdu hzu
      exact hune u hdu hzu.symm
    · intro u hdu
      have hmem : u ∈ Metric.closedBall (0 : ℂ) T :=
        Commons.Analysis.Complex.divisor_mem_of_ne_zero (by simpa [d] using hdu)
      have hle : ‖u‖ ≤ T := by simpa [Metric.mem_closedBall, dist_eq_norm] using hmem
      have hpos : 0 < ‖u‖ := norm_pos_iff.mpr (hune u hdu)
      calc Real.log ‖(0 : ℂ) - u‖ = Real.log ‖u‖ := by rw [zero_sub, norm_neg]
        _ ≤ Real.log T := Real.log_le_log hpos hle
  have hP0ne : (∏ᶠ u : ℂ, ((0 : ℂ) - u) ^ (d u)) ≠ 0 :=
    cof_finprod_ne_zero hsupp (z := 0) (fun u hdu hzu => hune u hdu hzu.symm)
  have hg0ne : g 0 ≠ 0 :=
    hg_nz 0 (by rw [Metric.mem_ball, dist_self]; linarith)
  have hfac0 : Λ 0 = (∏ᶠ u : ℂ, ((0 : ℂ) - u) ^ (d u)) * g 0 := by
    have hmem : (0 : ℂ) ∈ Metric.ball 0 (T + ε) := by
      rw [Metric.mem_ball, dist_self]; linarith
    simpa [d] using hfac 0 hmem
  have hlog0 : Real.log ‖g 0‖ =
      Real.log ‖Λ 0‖ - Real.log ‖∏ᶠ u : ℂ, ((0 : ℂ) - u) ^ (d u)‖ := by
    have h : Real.log ‖Λ 0‖ = Real.log ‖∏ᶠ u : ℂ, ((0 : ℂ) - u) ^ (d u)‖ + Real.log ‖g 0‖ := by
      rw [hfac0, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hP0ne) (norm_ne_zero_iff.mpr hg0ne)]
    linarith
  have hminus : -(Real.log ‖g 0‖) ≤
      -(Real.log ‖Λ 0‖) + c * T * (Real.log (T + 2) + K) * Real.log T := by
    have h2 : N * Real.log T ≤ c * T * (Real.log (T + 2) + K) * Real.log T :=
      mul_le_mul_of_nonneg_right hN_le (Real.log_nonneg hT1)
    have h3 : Real.log ‖∏ᶠ u : ℂ, ((0 : ℂ) - u) ^ (d u)‖ ≤ N * Real.log T := by
      rw [← hNsum]; exact hP0le
    linarith
  -- bounds for M0
  have hBle : B ≤ (C + 2 * c) * T * (Real.log (T + 2) + K + 1) ^ 2 := by
    rw [hB]
    have hraw := cof_rawBound_le C K c A T hC hc hK hA1 hAT
    have hstep : 2 * Real.log (Real.log (A + 2) + K + 1) * N ≤
        2 * Real.log (Real.log (A + 2) + K + 1) * (c * T * (Real.log (T + 2) + K)) :=
      mul_le_mul_of_nonneg_left hN_le (by linarith)
    linarith [hraw, hstep]
  have hBle' : B ≤ (C + 4 * c) * T * (Real.log (T + 2) + K + 1) ^ 2 := by
    have hQ : 0 ≤ (Real.log (T + 2) + K + 1) ^ 2 := by positivity
    have hTQ : 0 ≤ T * (Real.log (T + 2) + K + 1) ^ 2 := mul_nonneg hTpos.le hQ
    have hle : C + 2 * c ≤ C + 4 * c := by linarith
    calc B ≤ (C + 2 * c) * T * (Real.log (T + 2) + K + 1) ^ 2 := hBle
      _ = (C + 2 * c) * (T * (Real.log (T + 2) + K + 1) ^ 2) := by ring
      _ ≤ (C + 4 * c) * (T * (Real.log (T + 2) + K + 1) ^ 2) :=
            mul_le_mul_of_nonneg_right hle hTQ
      _ = (C + 4 * c) * T * (Real.log (T + 2) + K + 1) ^ 2 := by ring
  have hA₀ge : -(Real.log ‖Λ 0‖) ≤ A₀ := by rw [hA₀]; exact le_max_right 0 _
  set M0 : ℝ := max B (max 0 (-(Real.log ‖g 0‖))) with hM0
  have hM0nn : 0 ≤ M0 := by
    rw [hM0]
    exact le_trans (le_max_left 0 (-(Real.log ‖g 0‖))) (le_max_right B _)
  refine ⟨g, ε, M0, hε, hM0nn, hg_an, hg_nz, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact hfac z hz
  · intro w hw
    exact le_trans (hball w hw) (le_max_left B _)
  · rw [abs_le]
    have h0mem : (0 : ℂ) ∈ Metric.ball 0 T := by
      rw [Metric.mem_ball, dist_self]; exact hTpos
    constructor
    · have h2 : -(Real.log ‖g 0‖) ≤ M0 := by
        rw [hM0]; exact le_trans (le_max_right 0 (-(Real.log ‖g 0‖))) (le_max_right B _)
      linarith
    · exact le_trans (hball 0 h0mem) (le_max_left B _)
  · rw [hM0]
    refine max_le ?_ (max_le ?_ ?_)
    · exact le_trans hBle' (le_add_of_nonneg_right hA₀nn)
    · have hQ : 0 ≤ (Real.log (T + 2) + K + 1) ^ 2 := by positivity
      have h1 : 0 ≤ (C + 4 * c) * T * (Real.log (T + 2) + K + 1) ^ 2 :=
        mul_nonneg (mul_nonneg (by linarith) hTpos.le) hQ
      linarith [hA₀nn, h1]
    · have harith := cof_logT_mul_le C K c T hC hc hK hT1
      linarith [hminus, hA₀ge, harith]

end Work.FIArea5.HeckeZFR.Hadm
