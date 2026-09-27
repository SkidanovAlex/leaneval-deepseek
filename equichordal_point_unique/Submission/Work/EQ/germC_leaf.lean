import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.fan_base
import Submission.Work.EQ.germC_apply_ne
import Submission.Work.EQ.germC_snd_deriv
import Submission.Work.EQ.germC_step_algebra
import Submission.Work.EQ.germC_diff_ne
import Submission.Work.EQ.germC_R_pos

/-! The stable germ is the principal invariant leaf of the equichordal relation: the germ point
`germC a h` is analytic at `0`, its second coordinate is a local coordinate there
(`y'(0) = (1-a)/2 ≠ 0`), and the *principal* backward branch `invBranch a true` inverts the germ
step `u ↦ λu` near the origin.  The algebra is `Work.EQ.germC_step_algebra`, fed with the
cleared functional equation `GermFE` at `λu` and the positivity of `Re R` supplied by
`Work.EQ.germC_R_pos`. -/

namespace Work.EQ

open Complex Filter _root_.Topology
open scoped Topology

/-- The principal backward branch at the fixed point `A₁ = (-1/2, 0)` fixes it:
`invBranch a true A₁ = A₁` for `a < 1` (the radial distance at `A₁` is `(1-a)/2`). -/
lemma invBranch_true_A1 {a : ℝ} (ha1 : a < 1) :
    invBranch a true ((-1 / 2 : ℂ), (0 : ℂ)) = ((-1 / 2 : ℂ), (0 : ℂ)) := by
  have h1a : (0 : ℝ) < (1 - a) / 2 := by linarith
  have hca : (-1 / 2 : ℂ) + ((a / 2 : ℝ) : ℂ) = ((-(1 - a) / 2 : ℝ) : ℂ) := by
    rw [show (-1/2 : ℂ) = ((-1/2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_add]
    congr 1
    ring
  -- the principal square root of the radial distance at `A₁` is `(1 - a)/2`
  have hρ : (((-1 / 2 : ℂ) + ((a / 2 : ℝ) : ℂ)) ^ 2 + (0 : ℂ) ^ 2) ^ (1 / 2 : ℂ)
      = (((1 - a) / 2 : ℝ) : ℂ) := by
    rw [hca, zero_pow (by norm_num), add_zero, ← Complex.ofReal_pow]
    rw [ofReal_cpow_half (x := (-(1 - a) / 2) ^ 2) (by positivity)]
    congr 1
    rw [Real.sqrt_sq_eq_abs, abs_of_nonpos (by linarith)]
    ring
  have hkeyR : (-(1 - a) / 2 : ℝ) / ((1 - a) / 2) = (-1 : ℝ) := by
    rw [neg_div, neg_div, div_self (ne_of_gt h1a)]
  have hkey : ((-1 / 2 : ℂ) + ((a / 2 : ℝ) : ℂ)) / (((1 - a) / 2 : ℝ) : ℂ) = (-1 : ℂ) := by
    rw [hca, ← Complex.ofReal_div, hkeyR]
    norm_num
  rw [invBranch]
  simp only [ite_true, one_mul]
  rw [hρ]
  refine Prod.ext ?_ ?_
  · rw [hkey]; ring
  · ring

/-- One germ step, backwards.  If `u ≠ 0` lies in the analyticity ball, the two successive
differences `h(λu) - h u`, `h(λ²u) - h(λu)` are nonzero and `Re R > 0` for
`R = -E S`, `E = a h(λ²u)/(h(λ²u) - h(λu))`, `S = (1 + h(λu)²)^{1/2}`, then
`invBranch a true (germC a h (λu)) = germC a h u`.  This is `germC_apply_ne` (to recognise the two
germ points as difference quotients) fed into `germC_step_algebra`, whose functional-equation
hypothesis is `GermFE a h (λu)`. -/
lemma germC_step_eq {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {u : ℂ} (hu_ball : u ∈ Metric.ball (0 : ℂ) r) (hu : u ≠ 0)
    (hBA : h ((eqLam a : ℂ) * u) - h u ≠ 0)
    (hCB : h ((eqLam a : ℂ) * ((eqLam a : ℂ) * u)) - h ((eqLam a : ℂ) * u) ≠ 0)
    (hRe : 0 < (-((a : ℂ) * h ((eqLam a : ℂ) * ((eqLam a : ℂ) * u)) /
              (h ((eqLam a : ℂ) * ((eqLam a : ℂ) * u)) - h ((eqLam a : ℂ) * u))) *
            (1 + h ((eqLam a : ℂ) * u) ^ 2) ^ (1 / 2 : ℂ)).re) :
    invBranch a true (germC a h ((eqLam a : ℂ) * u)) = germC a h u := by
  obtain ⟨hr, han, h0, hderiv, hreal, hfe⟩ := hh
  have hl0 : 0 < eqLam a := eqLam_pos' ha0 ha1
  have hlne : (eqLam a : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hl0)
  have hlu : (eqLam a : ℂ) * u ≠ 0 := mul_ne_zero hlne hu
  -- `λu` stays in the ball on which `GermFE` is assumed
  have hmem : (eqLam a : ℂ) * u ∈ Metric.ball (0 : ℂ) (eqLam a * r) := by
    rw [Metric.mem_ball, dist_zero_right] at hu_ball ⊢
    rw [norm_mul, Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self (le_of_lt hl0)]
    exact mul_lt_mul_of_pos_left hu_ball hl0
  have hdiv : ((eqLam a : ℂ) * u) / (eqLam a : ℂ) = u := by
    rw [mul_div_cancel_left₀ u hlne]
  -- the cleared germ equation at `λu`, in the shape requested by `germC_step_algebra`
  have hFE : (h ((eqLam a : ℂ) * u) - h u) *
      (h ((eqLam a : ℂ) * ((eqLam a : ℂ) * u)) - h ((eqLam a : ℂ) * u)) +
      (a : ℂ) * h ((eqLam a : ℂ) * u) * (h ((eqLam a : ℂ) * ((eqLam a : ℂ) * u)) - h u) *
        (1 + h ((eqLam a : ℂ) * u) ^ 2) ^ (1 / 2 : ℂ) = 0 := by
    simpa only [GermFE, hdiv] using hfe ((eqLam a : ℂ) * u) hmem
  have hS : ((1 + h ((eqLam a : ℂ) * u) ^ 2) ^ (1 / 2 : ℂ)) ^ 2
      = 1 + h ((eqLam a : ℂ) * u) ^ 2 := cpow_half_sq _
  have halg := germC_step_algebra (A := h u) (B := h ((eqLam a : ℂ) * u))
    (C := h ((eqLam a : ℂ) * ((eqLam a : ℂ) * u)))
    (S := (1 + h ((eqLam a : ℂ) * u) ^ 2) ^ (1 / 2 : ℂ))
    (E := (a : ℂ) * h ((eqLam a : ℂ) * ((eqLam a : ℂ) * u)) /
      (h ((eqLam a : ℂ) * ((eqLam a : ℂ) * u)) - h ((eqLam a : ℂ) * u)))
    (R := -((a : ℂ) * h ((eqLam a : ℂ) * ((eqLam a : ℂ) * u)) /
      (h ((eqLam a : ℂ) * ((eqLam a : ℂ) * u)) - h ((eqLam a : ℂ) * u))) *
      (1 + h ((eqLam a : ℂ) * u) ^ 2) ^ (1 / 2 : ℂ))
    hBA hCB hFE hS rfl rfl hRe
  -- recognise the two germ points, at `u` and at `λu`, with `germC_apply_ne`
  have hP : germC a h u =
      ((a : ℂ) * h ((eqLam a : ℂ) * u) / (h ((eqLam a : ℂ) * u) - h u) - ((a / 2 : ℝ) : ℂ),
       h u * ((a : ℂ) * h ((eqLam a : ℂ) * u) / (h ((eqLam a : ℂ) * u) - h u))) := by
    rw [germC_apply_ne h0 hu]
    exact Prod.ext rfl (by ring)
  have hQ : germC a h ((eqLam a : ℂ) * u) =
      ((a : ℂ) * h ((eqLam a : ℂ) * ((eqLam a : ℂ) * u)) /
          (h ((eqLam a : ℂ) * ((eqLam a : ℂ) * u)) - h ((eqLam a : ℂ) * u)) -
            ((a / 2 : ℝ) : ℂ),
       h ((eqLam a : ℂ) * u) * ((a : ℂ) * h ((eqLam a : ℂ) * ((eqLam a : ℂ) * u)) /
          (h ((eqLam a : ℂ) * ((eqLam a : ℂ) * u)) - h ((eqLam a : ℂ) * u)))) := by
    rw [germC_apply_ne h0 hlu]
    exact Prod.ext rfl (by ring)
  rw [hQ, hP]
  exact halg.2

/-- **The stable germ is the principal invariant leaf.** If `h` is the normalised linearised
stable germ of the equichordal half-map at `A₁ = -1/2` (`IsStableGerm a h r`), then the germ
point `germC a h` has differentiable coordinate functions at `0`, the second one has derivative
`(1-a)/2 ≠ 0` there, and near `0` the *principal* backward branch inverts the germ step:
`invBranch a true (germC a h (λu)) = germC a h u` for all `u` in some ball around `0`. The
branch is the one fixed by the real germ; this is the geometric content of the cleared
functional equation `GermFE`, and it says that the fan of the all-`true` word is `germC`.

Route. `germC a h 0 = A₁` is `Work.EQ.germC_value`, the `y`-derivative is
`Work.EQ.germC_snd_deriv`, and for `v ≠ 0` the germ point is the explicit quotient of
`Work.EQ.germC_apply_ne`. For `u ≠ 0` put `A = h u`, `B = h (λu)`, `C = h (λ²u)`,
`S = (1 + B²)^{1/2}`, `E = a C/(C - B)`, `R = -E S`; `GermFE` at `λu` is exactly the hypothesis
`hFE` of `Work.EQ.germC_step_algebra`, and `R.re > 0` holds near `0` because
`R → aλ/(1-λ) = (1-a)/2 > 0`. That result then gives
`invBranch a true (germC a h (λu)) = germC a h u` for `u ≠ 0` small; at `u = 0` both sides are
`A₁` since `invBranch a true A₁ = A₁`. -/
theorem germC_leaf {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    DifferentiableAt ℂ (fun u => (germC a h u).1) 0 ∧
    DifferentiableAt ℂ (fun u => (germC a h u).2) 0 ∧
    deriv (fun u => (germC a h u).2) 0 = (((1 - a) / 2 : ℝ) : ℂ) ∧
    (∃ δ : ℝ, 0 < δ ∧ ∀ u : ℂ, u ∈ Metric.ball 0 δ →
      invBranch a true (germC a h ((eqLam a : ℂ) * u)) = germC a h u) := by
  -- analyticity of the germ near `0` gives differentiability of both coordinates
  obtain ⟨ρ, hρ, hAnal⟩ := germC_analytic ha0 ha1 hh
  have hd : DifferentiableAt ℂ (germC a h) 0 :=
    (hAnal 0 (Metric.mem_ball_self hρ)).differentiableAt
  refine ⟨hd.fst, hd.snd, germC_snd_deriv ha0 ha1 hh, ?_⟩
  -- combine the two non-degeneracy neighbourhoods and shrink below the analyticity radius
  obtain ⟨δ₁, hδ₁, hne₁⟩ := germC_diff_ne ha0 ha1 hh
  obtain ⟨δ₂, hδ₂, hne₂⟩ := germC_R_pos ha0 ha1 hh
  refine ⟨min (min δ₁ δ₂) r, lt_min (lt_min hδ₁ hδ₂) hh.1, ?_⟩
  intro u hu
  rcases eq_or_ne u 0 with rfl | hu0
  · -- at the fixed point both sides are `A₁`
    rw [mul_zero, germC_value ha0 ha1 hh]
    exact invBranch_true_A1 ha1
  · have hlt : ‖u‖ < min (min δ₁ δ₂) r := by
      rwa [Metric.mem_ball, dist_zero_right] at hu
    have hu₁ : u ∈ Metric.ball (0 : ℂ) δ₁ := by
      rw [Metric.mem_ball, dist_zero_right]
      exact lt_of_lt_of_le hlt (le_trans (min_le_left _ _) (min_le_left _ _))
    have hu₂ : u ∈ Metric.ball (0 : ℂ) δ₂ := by
      rw [Metric.mem_ball, dist_zero_right]
      exact lt_of_lt_of_le hlt (le_trans (min_le_left _ _) (min_le_right _ _))
    have hur : u ∈ Metric.ball (0 : ℂ) r := by
      rw [Metric.mem_ball, dist_zero_right]
      exact lt_of_lt_of_le hlt (min_le_right _ _)
    obtain ⟨hBA, _⟩ := hne₁ u hu₁ hu0
    obtain ⟨hCB, hRe⟩ := hne₂ u hu₂ hu0
    exact germC_step_eq ha0 ha1 hh hur hu0 hBA hCB hRe

end Work.EQ
