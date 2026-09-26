import Mathlib
import Submission.Helpers
import Submission.Work.Drive.uniformCurveBounds

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-!
# The tangent-vs-chord estimate for a regular curve

For a `period`-periodic curve `v` (to be applied to `velocity r` of a smooth knot), we collect:

* `uniformContinuous_velocity` — a continuous periodic curve is uniformly continuous
  (its values on the compact fundamental domain `[-period, 2*period]` control everything),
* `inner_chord_bound_of_deriv` — the quantitative heart: if `f` has derivative `v u` at every
  `u`, `‖v u‖ ≥ m > 0` everywhere and `‖v u - v a‖ ≤ m/2` on `[a,b]`, then
  `(m^2/2) * (b - a) ≤ ⟪v a, f b - f a⟫`,

from which `knot_tangent_chord_bound` follows by taking `m` the minimal speed of the knot.
-/

/-- A continuous `period`-periodic curve is uniformly continuous.  Reduction to the compact
fundamental domain `[-period, 2*period]`: shift both arguments by the same integer multiple of
the period to bring the first into `[0, period)`. -/
lemma uniformContinuous_velocity {v : ℝ → Space} (hcont : Continuous v)
    (hper : Function.Periodic v period) : UniformContinuous v := by
  have hp : 0 < period := period_pos
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  obtain ⟨η, hηpos, hη⟩ :=
    (Metric.uniformContinuousOn_iff.mp
      ((isCompact_Icc (a := -period) (b := 2 * period)).uniformContinuousOn_of_continuous
        hcont.continuousOn)) ε hε
  refine ⟨min η period, lt_min hηpos hp, ?_⟩
  intro x y hxy
  rw [Real.dist_eq] at hxy
  have hltη : |x - y| < η := lt_of_lt_of_le hxy (min_le_left _ _)
  have hltp : |x - y| < period := lt_of_lt_of_le hxy (min_le_right _ _)
  set y' : ℝ := y - (⌊x / period⌋ : ℝ) * period with hy'def
  have hx_eq : v (resid x) = v x := by
    rw [resid]
    exact (hper.int_mul ⌊x / period⌋).sub_eq x
  have hy_eq : v y' = v y := by
    rw [hy'def]
    exact (hper.int_mul ⌊x / period⌋).sub_eq y
  obtain ⟨hx1, hx2⟩ := resid_mem x
  have hx_mem : resid x ∈ Set.Icc (-period) (2 * period) := ⟨by linarith, by linarith⟩
  have hy_mem : y' ∈ Set.Icc (-period) (2 * period) := by
    have hd : y' - resid x = y - x := by rw [hy'def, resid]; ring
    have hyx : |y' - resid x| < period := by rw [hd, abs_sub_comm]; exact hltp
    have hbd := abs_lt.mp hyx
    constructor
    · linarith [hbd.1, hx1]
    · linarith [hbd.2, hx2]
  have hdist : dist (resid x) y' < η := by
    rw [Real.dist_eq]
    have hd : resid x - y' = x - y := by rw [hy'def, resid]; ring
    rw [hd]
    exact hltη
  have hres := hη (resid x) hx_mem y' hy_mem hdist
  rw [dist_eq_norm, hx_eq, hy_eq] at hres
  rwa [dist_eq_norm]

/-- The quantitative tangent-vs-chord bound.  If `f` has derivative `v u` at every `u`, the
speed `‖v u‖` is bounded below by `m > 0` everywhere, and `‖v u - v a‖ ≤ m/2` on `[a,b]`, then
`(m^2/2) * (b - a) ≤ ⟪v a, f b - f a⟫`.

The proof linearises `f` at `a`: with `g u = f u - u • v a` one has
`f b - f a = (g b - g a) + (b - a) • v a` and `‖g b - g a‖ ≤ (m/2)(b - a)` by the mean value
inequality applied to `deriv g u = v u - v a`. -/
lemma inner_chord_bound_of_deriv {f v : ℝ → Space} {m a b : ℝ}
    (hm : 0 < m) (hab : a ≤ b)
    (hderiv : ∀ u, HasDerivAt f (v u) u)
    (hspd : ∀ u, m ≤ ‖v u‖)
    (hclose : ∀ u ∈ Set.Icc a b, ‖v u - v a‖ ≤ m / 2) :
    (m ^ 2 / 2) * (b - a) ≤ inner ℝ (v a) (f b - f a) := by
  set va : Space := v a with hva
  set g : ℝ → Space := fun u => f u - u • va with hg
  have hg_deriv : ∀ u, HasDerivAt g (v u - va) u := by
    intro u
    rw [hg]
    have h1 : HasDerivAt f (v u) u := hderiv u
    have h2 : HasDerivAt (fun u : ℝ => u • va) va u := by
      simpa using (hasDerivAt_id u).smul_const va
    have hfun : (fun u : ℝ => f u - u • va) = (f - fun u : ℝ => u • va) := by
      ext u; rfl
    rw [hfun]
    exact h1.sub h2
  have hdiff : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ g u := fun u _ => (hg_deriv u).differentiableAt
  have hbdd : ∀ u ∈ Set.Icc a b, ‖deriv g u‖ ≤ m / 2 := by
    intro u hu
    rw [(hg_deriv u).deriv]
    exact hclose u hu
  have hmvt : ‖g b - g a‖ ≤ (m / 2) * (b - a) := by
    have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := g) (s := Set.Icc a b)
      (x := a) (y := b) (C := m / 2) hdiff hbdd (convex_Icc a b)
      ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩
    rwa [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ b - a)] at h
  have hkey : f b - f a = (g b - g a) + (b - a) • va := by
    rw [hg]; module
  have hinner : inner ℝ va (f b - f a) = inner ℝ va (g b - g a) + (b - a) * ‖va‖ ^ 2 := by
    rw [hkey, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq]
  have h1 : -(‖va‖ * ‖g b - g a‖) ≤ inner ℝ va (g b - g a) := by
    have h2 := neg_abs_le (inner ℝ va (g b - g a))
    have h3 := abs_real_inner_le_norm va (g b - g a)
    linarith
  have hvan : m ≤ ‖va‖ := by rw [hva]; exact hspd a
  have hnn : 0 ≤ b - a := by linarith
  have hstep : (m ^ 2 / 2) * (b - a) ≤ (b - a) * ‖va‖ ^ 2 - ‖va‖ * ‖g b - g a‖ := by
    have hU0 : 0 ≤ ‖va‖ := le_trans hm.le hvan
    have hbase : (m ^ 2 / 2) * (b - a) ≤
        (b - a) * ‖va‖ ^ 2 - ‖va‖ * ((m / 2) * (b - a)) := by
      have h1 : m * (m / 2) ≤ ‖va‖ * (‖va‖ - m / 2) :=
        mul_le_mul hvan (by linarith) (by linarith) hU0
      nlinarith [h1, hnn]
    have h2 : ‖va‖ * ‖g b - g a‖ ≤ ‖va‖ * ((m / 2) * (b - a)) :=
      mul_le_mul_of_nonneg_left hmvt hU0
    nlinarith [hbase, h2]
  have hfinal : (m ^ 2 / 2) * (b - a) ≤ inner ℝ va (g b - g a) + (b - a) * ‖va‖ ^ 2 := by
    linarith [h1, hstep]
  rw [hinner]
  exact hfinal

theorem knot_tangent_chord_bound {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r) :
    ∃ δ c : ℝ, 0 < δ ∧ 0 < c ∧ ∀ θ θ' : ℝ, θ < θ' → θ' - θ ≤ δ →
      c * (θ' - θ) ≤ inner ℝ (LeanEval.KnotTheory.Quadrisecant.velocity r θ) (r θ' - r θ) := by
  have hp : 0 < period := period_pos
  have hcont : Continuous (velocity r) := hr.smooth.continuous_deriv (by simp)
  have hper : Function.Periodic (velocity r) period := fun t => hr.velocity_periodic t
  have huc : UniformContinuous (velocity r) := uniformContinuous_velocity hcont hper
  -- minimal speed
  obtain ⟨t0, _ht0, hmin⟩ :=
    (isCompact_Icc (a := (0:ℝ)) (b := period)).exists_isMinOn
      ⟨0, Set.mem_Icc.mpr ⟨le_rfl, hp.le⟩⟩ hcont.norm.continuousOn
  set m : ℝ := ‖velocity r t0‖ with hmdef
  have hmpos : 0 < m := by
    rw [hmdef]
    exact norm_pos_iff.mpr (hr.regular t0)
  have hmle : ∀ t : ℝ, m ≤ ‖velocity r t‖ := by
    intro t
    have h1 : ‖velocity r t‖ = ‖velocity r (resid t)‖ := by
      rw [resid]
      exact congrArg Norm.norm ((hper.int_mul ⌊t / period⌋).sub_eq t).symm
    rw [h1, hmdef]
    exact hmin ⟨(resid_mem t).1, (resid_mem t).2.le⟩
  -- uniform continuity at scale m/2
  rw [Metric.uniformContinuous_iff] at huc
  obtain ⟨η, hηpos, hη⟩ := huc (m / 2) (by linarith)
  have hucη : ∀ x y : ℝ, |x - y| < η → ‖velocity r x - velocity r y‖ < m / 2 := by
    intro x y hxy
    have hres := hη (a := x) (b := y) (by rwa [Real.dist_eq])
    rwa [dist_eq_norm] at hres
  refine ⟨min (η / 2) 1, m ^ 2 / 2, lt_min (by linarith) one_pos, by positivity, ?_⟩
  intro θ θ' hθ hδ
  have hδle : min (η / 2) 1 ≤ η / 2 := min_le_left _ _
  have hclose : ∀ u ∈ Set.Icc θ θ', ‖velocity r u - velocity r θ‖ ≤ m / 2 := by
    intro u hu
    have huθ : u - θ ≤ θ' - θ := by linarith [hu.2]
    have hlt : |u - θ| < η := by
      rw [abs_of_nonneg (by linarith [hu.1])]
      linarith
    exact le_of_lt (hucη u θ hlt)
  exact inner_chord_bound_of_deriv hmpos hθ.le
    (fun u => by
      have h := (hr.smooth.differentiable (by simp) u).hasDerivAt
      simpa [velocity] using h)
    hmle hclose

end Work.Drive
