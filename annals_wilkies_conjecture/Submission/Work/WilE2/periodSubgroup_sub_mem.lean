import Mathlib
import Submission.Work.WilE2.period_subgroup

namespace Work.WilE2

/-- **Uniqueness of integral curves forces periodicity.**  If two points of an integral curve
`γ` of a `C¹` autonomous vector field `X` coincide, `γ t = γ t'`, then `t' - t` is a period of
`γ`: the time-shifted curve `v ↦ γ (v + (t' - t))` is again an integral curve of `X` (the chain
rule), and it agrees with `γ` at time `t`, so global uniqueness of integral curves
(`integral_curve_unique_global`) identifies the two. -/
theorem periodSubgroup_sub_mem {m : ℕ} {X : (Fin m → ℝ) → (Fin m → ℝ)} (hX : ContDiff ℝ 1 X)
    {γ : ℝ → Fin m → ℝ} (hγ : ∀ t, HasDerivAt γ (X (γ t)) t) {t t' : ℝ}
    (h : γ t = γ t') : t' - t ∈ periodSubgroup γ := by
  rw [mem_periodSubgroup]
  intro s
  set δ : ℝ → Fin m → ℝ := fun v => γ (v + (t' - t)) with hδdef
  -- The time-shifted curve is again an integral curve of `X`, by the chain rule.
  have hδ : ∀ u, HasDerivAt δ (X (δ u)) u := by
    intro u
    have hg : HasDerivAt (fun v : ℝ => v + (t' - t)) 1 u := (hasDerivAt_id u).add_const _
    have hc := HasDerivAt.scomp (x := u) (h := fun v : ℝ => v + (t' - t))
      (hγ (u + (t' - t))) hg
    rw [hδdef]
    simpa [Function.comp_def] using hc
  -- The two curves agree at time `t`.
  have hpt : γ t = δ t := by
    rw [hδdef]; simp [h]
  have heq := integral_curve_unique_global X hX hγ hδ hpt
  have := congrFun heq s
  simpa [hδdef] using this.symm

end Work.WilE2
