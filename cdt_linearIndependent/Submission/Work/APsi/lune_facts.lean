import Mathlib
import Submission.Work.APsi.defs
import Submission.Work.APsi.lune_branch
import Submission.Work.APsi.guide

/-!
# Area `Ψ_A`: the analytic facts on the lune map `lune c` for `c > 1`

`lune c z = (z(1+c²) - 1 - c² + √((1+c²)²(1+z)² - 16c²z))/(2(c²-1))` (principal square root) is
the section of the degree-two rational map `luneF c w = w(B + Cw)/(C + Bw)`, `B = 1+c²`,
`C = c²-1`, i.e. the conformal isomorphism from the open unit disc onto the lune `L(c) ⊂ 𝔻`
(Calegari--Dimitrov--Tang, arXiv:2408.15403, eq. `(firstgobble)`).

This module assembles the analytic facts:

* `lune c` is continuous on the closed unit disc and holomorphic on the open unit disc
  (the radicand `luneR c` avoids the branch cut `(-∞,0]` there; see `lune_branch`);
* `lune c 0 = 0` (`lune_zero` in `defs`);
* `‖lune c z‖ ≤ 1` on the closed disc and `‖lune c z‖ < 1` on the open disc, with equality only
  on the unit circle: `luneF c (lune c z) = z` and `‖luneF c w‖ = 1` for `‖w‖ = 1`, so
  `‖lune c z‖ = 1` forces `‖z‖ = 1`;
* `lune c` has the single zero `z = 0` (immediate from the quadratic relation `lune_quad`).
-/

namespace Work.APsi

open Submission.CDTPlan Metric
open scoped ComplexConjugate

noncomputable section

/-- `luneR c` is a polynomial, hence continuous. -/
theorem continuous_luneR (c : ℝ) : Continuous fun z : ℂ => luneR c z := by
  unfold luneR
  fun_prop

/-- `luneR c` is a polynomial, hence entire. -/
theorem differentiable_luneR (c : ℝ) : Differentiable ℂ fun z : ℂ => luneR c z := by
  unfold luneR
  fun_prop

/-- The principal square root of the radicand is continuous on the closed unit disc: on the open
disc `luneR c` avoids the branch cut, and at its zeros (`‖z‖ = 1`, where the values are `0`)
Mathlib's `continuousAt_cpow_const_of_re_pos` applies because `0 ≤ re 0`. -/
theorem continuousOn_luneR_cpow (c : ℝ) (hc : 1 < c) :
    ContinuousOn (fun z : ℂ => (luneR c z) ^ (1 / 2 : ℂ)) (closedBall 0 1) := by
  intro z hz
  have hz' : ‖z‖ ≤ 1 := by rwa [Metric.mem_closedBall, dist_zero_right] at hz
  have hcond : 0 ≤ (luneR c z).re ∨ (luneR c z).im ≠ 0 := by
    rcases eq_or_ne (luneR c z) 0 with h | h
    · left; rw [h]; simp
    · obtain h1 | h2 := luneR_slitPlane_of_le_of_ne hc hz' h
      · exact Or.inl (le_of_lt h1)
      · exact Or.inr h2
  exact (Complex.continuousAt_cpow_const_of_re_pos hcond
    (by norm_num : 0 < ((1 / 2 : ℂ)).re)).comp_continuousWithinAt
      ((continuous_luneR c).continuousAt.continuousWithinAt)

/-- `lune c` is continuous on the closed unit disc. -/
theorem lune_continuousOn_closedBall (c : ℝ) (hc : 1 < c) :
    ContinuousOn (lune c) (closedBall 0 1) := by
  have hsqrt := continuousOn_luneR_cpow c hc
  have hnum : ContinuousOn (fun z : ℂ => z * luneB c - luneB c + (luneR c z) ^ (1 / 2 : ℂ))
      (closedBall 0 1) :=
    ((continuousOn_id.mul continuousOn_const).sub continuousOn_const).add hsqrt
  have hfun : (lune c) = fun z : ℂ =>
      (z * luneB c - luneB c + (luneR c z) ^ (1 / 2 : ℂ)) / (2 * luneC c) :=
    funext fun z => lune_eq c z
  rw [hfun]
  exact hnum.div_const (2 * luneC c)

/-- `lune c` is holomorphic on the open unit disc. -/
theorem lune_differentiableOn_ball (c : ℝ) (hc : 1 < c) :
    DifferentiableOn ℂ (lune c) (ball 0 1) := by
  have hsqrt : DifferentiableOn ℂ (fun z : ℂ => (luneR c z) ^ (1 / 2 : ℂ)) (ball 0 1) :=
    DifferentiableOn.cpow_const (differentiable_luneR c).differentiableOn (fun z hz =>
      luneR_slitPlane_of_lt hc (by rwa [Metric.mem_ball, dist_zero_right] at hz))
  have hnum : DifferentiableOn ℂ (fun z : ℂ => z * luneB c - luneB c + (luneR c z) ^ (1 / 2 : ℂ))
      (ball 0 1) :=
    ((differentiableOn_id.mul (differentiableOn_const (luneB c))).sub
      (differentiableOn_const (luneB c))).add hsqrt
  have hfun : (lune c) = fun z : ℂ =>
      (z * luneB c - luneB c + (luneR c z) ^ (1 / 2 : ℂ)) / (2 * luneC c) :=
    funext fun z => lune_eq c z
  rw [hfun]
  exact hnum.div_const (2 * luneC c)

/-- `lune c` is continuous and holomorphic on the closed and open unit discs respectively. -/
theorem lune_cont_diff_ball (c : ℝ) (hc : 1 < c) :
    ContinuousOn (lune c) (closedBall 0 1) ∧ DifferentiableOn ℂ (lune c) (ball 0 1) :=
  ⟨lune_continuousOn_closedBall c hc, lune_differentiableOn_ball c hc⟩

/-- If `‖lune c z‖ = 1` then `‖z‖ = 1`: apply the inverse map, which preserves the unit circle. -/
theorem norm_eq_one_of_norm_lune_eq_one {c : ℝ} (hc : 1 < c) {z : ℂ}
    (h : ‖lune c z‖ = 1) : ‖z‖ = 1 := by
  have h1 : ‖luneF c (lune c z)‖ = 1 := norm_luneF c hc h
  rwa [luneF_lune c hc] at h1

/-- `‖lune c z‖ < 1` on the open unit disc.  Along the segment `t ↦ t z` the modulus profile is
continuous, starts at `0`, and never reaches `1` (that would force `‖t z‖ = 1`); by the
intermediate value theorem it stays below `1`. -/
theorem lune_norm_lt_one (c : ℝ) (hc : 1 < c) :
    ∀ z : ℂ, ‖z‖ < 1 → ‖lune c z‖ < 1 := by
  have hcont : ContinuousOn (fun w : ℂ => lune c w) (ball 0 1) :=
    (lune_continuousOn_closedBall c hc).mono ball_subset_closedBall
  intro z hz
  let F : ℝ → ℝ := fun t => ‖lune c ((t : ℂ) * z)‖
  have hlt_of : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖((t : ℂ) * z)‖ < 1 := by
    intro t ht
    have hn : ‖(t : ℂ)‖ = |t| := RCLike.norm_ofReal t
    rw [norm_mul, hn, abs_of_nonneg ht.1]
    calc t * ‖z‖ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg z)
      _ = ‖z‖ := one_mul _
      _ < 1 := hz
  have hmaps : Set.MapsTo (fun t : ℝ => ((t : ℂ) * z)) (Set.Icc (0 : ℝ) 1) (ball 0 1) := by
    intro t ht
    rw [Metric.mem_ball, dist_eq_norm]
    simpa using hlt_of t ht
  have hcontF : ContinuousOn F (Set.Icc (0 : ℝ) 1) := by
    have h1 : ContinuousOn (fun t : ℝ => ((t : ℂ) * z)) (Set.Icc (0 : ℝ) 1) :=
      (Complex.continuous_ofReal.mul continuous_const).continuousOn
    have h2 : ContinuousOn (fun t : ℝ => lune c ((t : ℂ) * z)) (Set.Icc (0 : ℝ) 1) :=
      hcont.comp h1 hmaps
    simpa only [F] using h2.norm
  have hF0 : F 0 = 0 := by
    simp only [F, Complex.ofReal_zero, zero_mul, lune_zero, norm_zero]
  have hne : ∀ t ∈ Set.Icc (0 : ℝ) 1, F t ≠ 1 := by
    intro t ht hFt
    have hw : ‖lune c ((t : ℂ) * z)‖ = 1 := by simpa only [F] using hFt
    have h1 : ‖((t : ℂ) * z)‖ = 1 := norm_eq_one_of_norm_lune_eq_one hc hw
    exact (ne_of_lt (hlt_of t ht)) h1
  rcases lt_or_gt_of_ne (hne 1 (by norm_num)) with h | h
  · simpa only [F, Complex.ofReal_one, one_mul] using h
  · exfalso
    have hmem : (1 : ℝ) ∈ Set.Icc (F 0) (F 1) := by
      rw [hF0]; exact ⟨zero_le_one, le_of_lt h⟩
    rcases (intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num) hcontF) hmem with
      ⟨t, ht, hFt⟩
    exact hne t ht hFt

/-- `lune c` maps the closed unit disc into the closed unit disc: it is `< 1` on the (dense) open
disc and continuous on the closed disc. -/
theorem lune_norm_le_one (c : ℝ) (hc : 1 < c) :
    ∀ z : ℂ, ‖z‖ ≤ 1 → ‖lune c z‖ ≤ 1 := by
  intro z hz
  have hcont : ContinuousOn (fun w : ℂ => ‖lune c w‖) (closedBall (0 : ℂ) 1) :=
    (lune_continuousOn_closedBall c hc).norm
  have hcl : IsClosed (closedBall (0 : ℂ) 1 ∩ {w : ℂ | ‖lune c w‖ ≤ 1}) :=
    hcont.preimage_isClosed_of_isClosed Metric.isClosed_closedBall isClosed_Iic
  have h1 : ball (0 : ℂ) 1 ⊆ closedBall (0 : ℂ) 1 ∩ {w : ℂ | ‖lune c w‖ ≤ 1} :=
    fun w hw =>
      ⟨ball_subset_closedBall hw,
        le_of_lt (lune_norm_lt_one c hc w (by rwa [Metric.mem_ball, dist_zero_right] at hw))⟩
  have h2 : closure (ball (0 : ℂ) 1) ⊆ closedBall (0 : ℂ) 1 ∩ {w : ℂ | ‖lune c w‖ ≤ 1} :=
    (closure_mono h1).trans (le_of_eq hcl.closure_eq)
  rw [closure_ball (0 : ℂ) one_ne_zero] at h2
  exact (h2 (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz)).2

/-- `lune c` has the single zero `0`: the quadratic relation `C w² + B(1-z) w - C z = 0` at
`w = lune c z = 0` reads `-C z = 0` and `C = c² - 1 ≠ 0`. -/
theorem lune_eq_zero_imp {c : ℝ} (hc : 1 < c) {z : ℂ} (h : lune c z = 0) : z = 0 := by
  have hq := lune_quad c hc z
  rw [h] at hq
  have hz : luneC c * z = 0 := by linear_combination -hq
  exact (mul_eq_zero.mp hz).resolve_left (luneC_ne_zero hc)

end

/-- **Analytic facts on the lune map** `lune c` for `c > 1`: continuity on the closed unit disc,
holomorphy on the open unit disc, `lune c 0 = 0`, the disc bounds `‖lune c z‖ ≤ 1` / `< 1`, and
the single zero `z = 0`. -/
theorem lune_facts (c : ℝ) (hc : 1 < c) :
    ContinuousOn (Submission.CDTPlan.lune c) (Metric.closedBall 0 1) ∧
      DifferentiableOn ℂ (Submission.CDTPlan.lune c) (Metric.ball 0 1) ∧
      Submission.CDTPlan.lune c 0 = 0 ∧
      (∀ z : ℂ, ‖z‖ ≤ 1 → ‖Submission.CDTPlan.lune c z‖ ≤ 1) ∧
      (∀ z : ℂ, ‖z‖ < 1 → ‖Submission.CDTPlan.lune c z‖ < 1) ∧
      (∀ z : ℂ, Submission.CDTPlan.lune c z = 0 → z = 0) := by
  exact ⟨lune_continuousOn_closedBall c hc, lune_differentiableOn_ball c hc, lune_zero c,
    lune_norm_le_one c hc, lune_norm_lt_one c hc, fun z hz => lune_eq_zero_imp hc hz⟩

end Work.APsi
