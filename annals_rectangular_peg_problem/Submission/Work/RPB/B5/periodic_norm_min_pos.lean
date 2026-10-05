import Mathlib
import Submission.Work.RPA3.periodic_mem_Icc

/-!
# B5: a strict positive lower bound for a jointly continuous, `2π`-periodic-in-`t` function

If `g : ℝ × ℝ → ℂ` is continuous, `2π`-periodic in its second variable, and nowhere zero on the
slab `τ ∈ [0,1]`, `t ∈ ℝ`, then `‖g τ t‖` is bounded below by a strictly positive constant,
uniformly in `τ ∈ [0,1]` and `t ∈ ℝ`.

Proof: on the compact box `[0,1] × [0,2π]` the continuous function `‖g‖` is strictly positive, so
it has a strictly positive lower bound there (`IsCompact.exists_forall_le'`). Every `t ∈ ℝ` is
congruent mod `2π` to a point `t₀ ∈ [0,2π]` (`Work.RPA3.periodic_mem_Icc`), where the value of
`g τ ·` is unchanged, so the bound on the box is a global lower bound.
-/

namespace Work.RPB.B5

theorem periodic_norm_min_pos (g : ℝ → ℝ → ℂ)
    (hg : Continuous (fun p : ℝ × ℝ => g p.1 p.2))
    (hper : ∀ τ t, g τ (t + 2 * Real.pi) = g τ t)
    (hne : ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ t : ℝ, g τ t ≠ 0) :
    ∃ m : ℝ, 0 < m ∧ ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ t : ℝ, m ≤ ‖g τ t‖ := by
  -- `‖g‖` is continuous on the plane.
  have hcont : Continuous (fun p : ℝ × ℝ => ‖g p.1 p.2‖) := continuous_norm.comp hg
  -- The box `[0,1] × [0,2π]` is compact; on it `‖g‖` is strictly positive, hence bounded
  -- below by a strictly positive constant.
  have hK : IsCompact (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) (2 * Real.pi)) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨m, hmpos, hmin⟩ :=
    hK.exists_forall_le' hcont.continuousOn
      (fun b hb => norm_pos_iff.mpr (hne b.1 hb.1 b.2))
  refine ⟨m, hmpos, ?_⟩
  intro τ hτ t
  -- Reduce `t` modulo the period `2π` to a point `t₀ ∈ [0,2π]`.
  have hperf : Function.Periodic (fun u : ℝ => g τ u) (2 * Real.pi) := fun u => hper τ u
  obtain ⟨t₀, ht₀, heq⟩ :=
    Work.RPA3.periodic_mem_Icc Real.two_pi_pos (fun u : ℝ => g τ u) hperf t
  rw [heq]
  exact hmin (τ, t₀) ⟨hτ, ht₀⟩

end Work.RPB.B5
