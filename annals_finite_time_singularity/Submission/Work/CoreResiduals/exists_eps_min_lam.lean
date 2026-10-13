import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.ConstructionInstance.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals

/-- **A local uniform positive lower bound for `λ̄` around any point of `preWindow T`.**

`preWindow T = Set.Ioo (-2) T` is *open*, so a point `t₀` of it has a symmetric neighbourhood
`Icc (t₀ - ε) (t₀ + ε)` still contained in `preWindow T`.  On `preWindow T` the modulation `λ̄` is
differentiable at every point, hence continuous at `t₀`, so `λ̄ s ≥ λ̄ t₀ / 2 > 0` on a small
symmetric neighbourhood of `t₀`.  Taking `ε` to be the smaller of the two radii gives a single
`ε > 0` with `Icc (t₀ - ε) (t₀ + ε) ⊆ preWindow T` and `λ̄ ≥ λ̄ t₀ / 2` throughout.

This is the *pointwise* companion of the global strip bounds `lam_pos_le_on_Icc` and
`exists_pos_le_lam_window`; it is used to localise the positivity of `λ̄` without a compactness
argument.  -/
theorem exists_eps_min_lam {T : ℝ} {lam : ℝ → ℝ}
    (hlam : ∀ t ∈ Work.ConstructionInstance.preWindow T, 0 < lam t)
    (hlamdif : ∀ t ∈ Work.ConstructionInstance.preWindow T, HasDerivAt lam (deriv lam t) t)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Work.ConstructionInstance.preWindow T) :
    ∃ ε : ℝ, 0 < ε ∧ Set.Icc (t₀ - ε) (t₀ + ε) ⊆ Work.ConstructionInstance.preWindow T ∧
      ∃ m : ℝ, 0 < m ∧ ∀ s ∈ Set.Icc (t₀ - ε) (t₀ + ε), m ≤ lam s := by
  have ht1 : -2 < t₀ := ht₀.1
  have ht2 : t₀ < T := ht₀.2
  have hpos : 0 < lam t₀ := hlam t₀ ht₀
  -- continuity of `λ̄` at `t₀` (from differentiability) gives a symmetric `δ`-neighbourhood
  -- on which `|λ̄ s - λ̄ t₀| < λ̄ t₀ / 2`.
  have hcont : ContinuousAt lam t₀ := (hlamdif t₀ ht₀).continuousAt
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ, hδpos, hδ⟩ := hcont (lam t₀ / 2) (by linarith)
  -- `ε` is the smaller of: half the distance to `-2`, half the distance to `T`, and `δ/2`.
  refine ⟨min (min ((t₀ + 2) / 2) ((T - t₀) / 2)) (δ / 2), ?_, ?_, lam t₀ / 2, by linarith, ?_⟩
  · exact lt_min (lt_min (by linarith) (by linarith)) (by linarith)
  · -- `Icc (t₀ - ε) (t₀ + ε) ⊆ Ioo (-2) T`
    intro s hs
    constructor
    · have hle : min (min ((t₀ + 2) / 2) ((T - t₀) / 2)) (δ / 2) ≤ (t₀ + 2) / 2 :=
        le_trans (min_le_left _ _) (min_le_left _ _)
      linarith [hs.1]
    · have hle : min (min ((t₀ + 2) / 2) ((T - t₀) / 2)) (δ / 2) ≤ (T - t₀) / 2 :=
        le_trans (min_le_left _ _) (min_le_right _ _)
      linarith [hs.2]
  · -- `λ̄ ≥ λ̄ t₀ / 2` throughout the interval
    intro s hs
    have hεle : min (min ((t₀ + 2) / 2) ((T - t₀) / 2)) (δ / 2) ≤ δ / 2 := min_le_right _ _
    have habs : |s - t₀| ≤ min (min ((t₀ + 2) / 2) ((T - t₀) / 2)) (δ / 2) := by
      rw [abs_le]; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hlt : |s - t₀| < δ := by
      have : |s - t₀| ≤ δ / 2 := le_trans habs hεle
      linarith
    have hd := hδ (x := s) (by rw [Real.dist_eq]; exact hlt)
    rw [Real.dist_eq] at hd
    have := (abs_lt.mp hd).1
    linarith

end Work.CoreResiduals
