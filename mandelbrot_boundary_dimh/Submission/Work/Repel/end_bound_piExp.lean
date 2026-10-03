import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Repel.periodic_strip_bound

/-!
# `Work.Repel.end_bound_piExp`: `π ∘ (Ẽ - id)` is bounded on the ends of the cylinder

For the §4.1 data `d` of a parabolic germ, the lifted horn map `E = d.E = Φ ∘ φ` is defined and
holomorphic on the `T`-invariant region `{w | η₀ < |Im w|}` (`ParabData.ends_sub`), and:

* `ParabData.E_upper` : `E w - w → 0` at the upper end (`Im w → +∞`),
* `ParabData.E_lower` : `E w - w → cl` at the lower end (`Im w → -∞`),

both uniformly in `Re w` (the ends are the filters `comap im atTop/atBot`).

`E w - w` is `1`-periodic on that region (`T`-equivariance of `E`, which is proved from
`φ_abel` + `Φ_abel`), so `π ∘ (Ẽ - id) = piExp ∘ (E - id)` is a `1`-periodic continuous function of
the strip, bounded above and below the strip.  Hence it is bounded on the whole region
`{y ≤ |Im w|}` for every `y > η₀`, which is what the §6 assembly (Step 2) needs: the constant `C`
controls `‖π(Ẽ(w) - w)‖` uniformly in the end regions, e.g. for the factor `e^{2π Im}` occurring in
the derivative estimates.

The generic periodic-strip statement is `Work.Repel.periodic_strip_bound`.
-/

namespace Work.Repel

open MandelDim Complex Set Filter Topology
open scoped Topology

/-- `‖π(w)‖ = exp (-2π Im w)` for `π w = exp (2πi w)`. -/
lemma norm_piExp (z : ℂ) : ‖MandelDim.piExp z‖ = Real.exp (-(2 * Real.pi * z.im)) := by
  rw [MandelDim.piExp, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re]

/-- `‖π(w)‖ ≤ exp (2π ‖w‖)`. -/
lemma norm_piExp_le_exp (z : ℂ) : ‖MandelDim.piExp z‖ ≤ Real.exp (2 * Real.pi * ‖z‖) := by
  rw [norm_piExp]
  apply Real.exp_le_exp.mpr
  have h1 : -z.im ≤ ‖z‖ := by
    have h2 := Complex.abs_im_le_norm z
    have h3 := neg_le_abs z.im
    linarith
  nlinarith [Real.pi_pos]

/-- `MandelDim.piExp` is continuous. -/
lemma continuous_piExp : Continuous MandelDim.piExp := by
  show Continuous fun w : ℂ => Complex.exp (2 * Real.pi * I * w)
  fun_prop

/-- `d.E - id` is continuous on the end regions `{η₀ < |Im w|}` (there `φ w` lies in the basin,
where `Φ` is holomorphic, and `φ` is holomorphic on `Dφ ⊇ {η₀ < |Im w|}`). -/
lemma continuousOn_E_sub {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : ParabData f₀ D₀) :
    ContinuousOn (fun w : ℂ => d.E w - w) {w : ℂ | d.η₀ < |w.im|} := by
  have hφ : ContinuousOn d.φ {w : ℂ | d.η₀ < |w.im|} :=
    d.φ_holo.continuousOn.mono (fun w hw => (d.ends_sub w hw).1)
  have hΦ : ContinuousOn d.Φ (ParabolicBasin f₀ D₀) := d.Φ_holo.continuousOn
  have h1 : ContinuousOn (fun w : ℂ => d.Φ (d.φ w)) {w : ℂ | d.η₀ < |w.im|} :=
    hΦ.comp hφ (fun w hw => (d.ends_sub w hw).2)
  have h2 : ContinuousOn (fun w : ℂ => w) {w : ℂ | d.η₀ < |w.im|} := continuousOn_id
  have hsub : ContinuousOn ((fun w : ℂ => d.Φ (d.φ w)) - (fun w : ℂ => w))
      {w : ℂ | d.η₀ < |w.im|} := h1.sub h2
  rw [show ((fun w : ℂ => d.Φ (d.φ w)) - (fun w : ℂ => w))
        = (fun w : ℂ => d.Φ (d.φ w) - w) from by funext w; rfl] at hsub
  simpa only [ParabData.E] using hsub

/-- `π ∘ (d.E - id)` is continuous on the end regions. -/
lemma continuousOn_piExp_E_sub {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : ParabData f₀ D₀) :
    ContinuousOn (fun w : ℂ => MandelDim.piExp (d.E w - w)) {w : ℂ | d.η₀ < |w.im|} :=
  continuous_piExp.comp_continuousOn (continuousOn_E_sub d)

/-- `T`-equivariance of the lifted horn map on the end regions (`φ(w+1) = f₀(φ w)` and
`Φ(f₀ z) = Φ z + 1`). -/
lemma E_add_one {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : ParabData f₀ D₀) {w : ℂ}
    (hw : d.η₀ < |w.im|) : d.E (w + 1) = d.E w + 1 := by
  have hw1 : d.η₀ < |(w + 1).im| := by simpa using hw
  obtain ⟨hwd, hφw⟩ := d.ends_sub w hw
  obtain ⟨hw1d, _⟩ := d.ends_sub (w + 1) hw1
  have habel := d.φ_abel w hwd hw1d
  show d.Φ (d.φ (w + 1)) = d.Φ (d.φ w) + 1
  rw [habel, d.Φ_abel (d.φ w) hφw]

/-- `π ∘ (d.E - id)` is `1`-periodic on the end regions (the `+1` of `d.E (w+1) = d.E w + 1`
cancels against the shift of `id`). -/
lemma piExp_E_sub_periodic {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : ParabData f₀ D₀) {w : ℂ}
    (hw : d.η₀ < |w.im|) :
    MandelDim.piExp (d.E (w + 1) - (w + 1)) = MandelDim.piExp (d.E w - w) := by
  rw [E_add_one d hw]
  congr 1
  ring

/-- Upper end: `‖d.E w - w‖ ≤ 1` for all `w` of sufficiently large imaginary part, uniformly in
`Re w` (`ParabData.E_upper`). -/
lemma E_sub_upper_bound {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : ParabData f₀ D₀) :
    ∃ T : ℝ, ∀ w : ℂ, T ≤ w.im → ‖d.E w - w‖ ≤ 1 := by
  have h : ∀ᶠ w in MandelDim.upperEnd, dist (d.E w - w) 0 < 1 := by
    simpa only [ParabData.E] using
      (d.E_upper.eventually (Metric.ball_mem_nhds (0 : ℂ) one_pos))
  rw [MandelDim.upperEnd, Filter.eventually_comap, Filter.eventually_atTop] at h
  obtain ⟨T, hT⟩ := h
  refine ⟨T, fun w hw => ?_⟩
  have h1 := hT w.im hw w rfl
  rw [dist_zero_right] at h1
  linarith

/-- Lower end: `‖d.E w - w‖ ≤ ‖cl‖ + 1` for all `w` of sufficiently negative imaginary part,
uniformly in `Re w`. -/
lemma E_sub_lower_bound {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : ParabData f₀ D₀) {cl : ℂ}
    (hcl : Tendsto (fun w => d.Φ (d.φ w) - w) MandelDim.lowerEnd (𝓝 cl)) :
    ∃ T : ℝ, ∀ w : ℂ, w.im ≤ T → ‖d.E w - w‖ ≤ ‖cl‖ + 1 := by
  have h : ∀ᶠ w in MandelDim.lowerEnd, dist (d.E w - w) cl < 1 := by
    simpa only [ParabData.E] using (hcl.eventually (Metric.ball_mem_nhds cl one_pos))
  rw [MandelDim.lowerEnd, Filter.eventually_comap, Filter.eventually_atBot] at h
  obtain ⟨T, hT⟩ := h
  refine ⟨T, fun w hw => ?_⟩
  have h1 := hT w.im hw w rfl
  rw [dist_eq_norm] at h1
  have h2 : ‖d.E w - w‖ ≤ ‖d.E w - w - cl‖ + ‖cl‖ := by
    have := norm_add_le (d.E w - w - cl) cl
    simpa using this
  linarith

theorem end_bound_piExp {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) {y : ℝ}
    (hy : MandelDim.ParabData.η₀ d < y) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, y ≤ |w.im| → ‖MandelDim.piExp (MandelDim.ParabData.E d w - w)‖ ≤ C := by
  obtain ⟨cl, hcl⟩ := d.E_lower
  refine periodic_strip_bound (F := fun w : ℂ => MandelDim.piExp (d.E w - w))
    (η := d.η₀) (y := y) (Cup := Real.exp (2 * Real.pi))
    (Cdn := Real.exp (2 * Real.pi * (‖cl‖ + 1))) hy (Real.exp_pos _).le (Real.exp_pos _).le
    (fun w hw => piExp_E_sub_periodic d hw) (continuousOn_piExp_E_sub d) ?_ ?_
  · obtain ⟨T, hT⟩ := E_sub_upper_bound d
    exact ⟨T, fun w hw => le_trans (norm_piExp_le_exp _)
      (Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, hT w hw]))⟩
  · obtain ⟨T, hT⟩ := E_sub_lower_bound d hcl
    exact ⟨T, fun w hw => le_trans (norm_piExp_le_exp _)
      (Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, hT w hw]))⟩

end Work.Repel
