import Mathlib
import Submission.Work.Whitney.CutPush.local_graph_data

/-!
# The parameter-smooth bump family (first rung of the parametric tower)

`CutPush/NOTES_STATE_S57.md` §4.  The parametric SLICE tower needs, for a *smooth family* of slices, a bump
that depends smoothly on the parameter and is `1` near the moving base point.  This file provides it in the
form the tower consumes: a smooth family `χ (t, ·)` of `[0,1]`-valued bumps, supported in the ball of radius
`ρ` around a smooth curve `u t` and equal to `1` on the ball of a *uniform* radius `δ`.

The construction is a translation of the single-point bump `exists_contDiffBump_near`:
`χ (t, v) = β (v - u t)`, with `β` a bump at `0` of support inside `ball 0 ρ`.  (The two clauses are
independent: the `= 1` clause controls the inner radius and the support clause the outer one, so no relation
between `δ` and `ρ` is needed.)  All the `t`-dependence sits
in the smooth curve `u`, so smoothness in `(t, v)` is composition with the smooth map `(t, v) ↦ v - u t`;
the support statement is the translation-invariance of the topological support,
`tsupport (β ∘ (· - u t)) ⊆ (· - u t) ⁻¹' tsupport β`.
-/

namespace Work.Whitney.CutPush

open scoped Topology ContDiff

set_option linter.unusedVariables false

/-- **The parameter-smooth bump family.**  Along a smooth curve `u : ℝ → E` and for a prescribed radius
`ρ > 0` there is a smooth family `χ` of bumps, with a *uniform* inner radius `δ ∈ (0, ρ)`: `χ t = 1` on the
`δ`-ball around `u t`, `tsupport (χ t) ⊆ ball (u t) ρ`, and `0 ≤ χ t ≤ 1`. -/
theorem exists_contDiffBump_family {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [HasContDiffBump E] (u : ℝ → E) (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ (χ : ℝ → E → ℝ) (δ : ℝ), 0 < δ ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × E => χ p.1 p.2) ∧
      (∀ t v, dist v (u t) ≤ δ → χ t v = 1) ∧
      (∀ t, tsupport (χ t) ⊆ Metric.ball (u t) ρ) ∧
      (∀ t v, 0 ≤ χ t v) := by
  classical
  -- the single-point bump at `0`, with support inside `ball 0 ρ`
  obtain ⟨β, r, hr, hβc, hβ1, hβnn, hβsupp⟩ :=
    exists_contDiffBump_near (E := E) Metric.isOpen_ball (c := (0 : E))
      (Metric.mem_ball_self hρ)
  refine ⟨fun t v => β (v - u t), r, hr, ?_, ?_, ?_, ?_⟩
  · have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × E => p.2 - u p.1) :=
      contDiff_snd.sub (hu.comp contDiff_fst)
    exact hβc.comp h1
  · intro t v hv
    refine hβ1 (v - u t) ?_
    simpa [dist_eq_norm] using hv
  · intro t
    have hA : closure ((fun v : E => v - u t) ⁻¹' Function.support β)
        ⊆ (fun v : E => v - u t) ⁻¹' tsupport β :=
      ((isClosed_tsupport β).preimage (continuous_id.sub continuous_const)).closure_subset_iff.mpr
        (fun v hv => subset_tsupport β hv)
    have hB : (fun v : E => v - u t) ⁻¹' tsupport β ⊆ Metric.ball (u t) ρ := by
      intro w hw
      have h2 : w - u t ∈ Metric.ball (0 : E) ρ := hβsupp hw
      rw [Metric.mem_ball, dist_zero_right] at h2
      rw [Metric.mem_ball, dist_eq_norm]
      exact h2
    show closure ((fun v : E => v - u t) ⁻¹' Function.support β) ⊆ Metric.ball (u t) ρ
    exact hA.trans hB
  · intro t v
    exact hβnn (v - u t)

end Work.Whitney.CutPush
