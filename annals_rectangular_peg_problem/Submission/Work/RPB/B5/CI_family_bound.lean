import Mathlib
import Submission.Work.RPV.Defs
import Submission.Work.RPB.B5.deriv_bounds_family
import Submission.Work.RPB.B4.periodic_reduce
import Submission.Work.RPB.B4.periodic_deriv

open scoped ContDiff

namespace Work.RPB.B5

/-- **Uniform bound for a `CurveIsotopy`.**

For an isotopy `CI` of embedded area-`π` curves the uncurried map
`(τ, t) ↦ CI.c τ t : ℝ × ℝ → ℂ` is `C^∞` (in particular continuous), and the slice
derivative `(τ, t) ↦ deriv (CI.c τ) t` is continuous as well
(`Work.RPB.B5.continuous_deriv_family_one`).  Both are `2π`-periodic in `t`
(`CI.per` and `Work.RPB.B4.periodic_deriv`), so an arbitrary pair `(τ, t)` with
`τ ∈ [0,1]` is reduced by the periodicity to the compact box `[0,1] × [0, 2π]`, where
the norms of a continuous map are bounded (`IsCompact.exists_bound_of_continuousOn`). -/
theorem CI_family_bound (CI : Work.RPV.CurveIsotopy) :
    ∃ K : ℝ, 0 < K ∧ ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
      ‖CI.c τ t‖ ≤ K ∧ ‖deriv (CI.c τ) t‖ ≤ K := by
  let F : ℝ × ℝ → ℂ := fun z => CI.c z.1 z.2
  let G : ℝ × ℝ → ℂ := fun p => deriv (CI.c p.1) p.2
  -- the uncurried family is `C^∞`, hence continuous
  have hFcd : ContDiff ℝ ∞ F := CI.smooth
  have hFcd1 : ContDiff ℝ 1 F := hFcd.of_le (by norm_num)
  have hFcont : Continuous F := hFcd.continuous
  -- the slice derivative is continuous as well
  have hGcont : Continuous G := continuous_deriv_family_one CI.c hFcd1
  -- the compact box on which the uniform bounds are measured
  have hKc : IsCompact (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) (2 * Real.pi)) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨C1, hC1⟩ := hKc.exists_bound_of_continuousOn hFcont.continuousOn
  obtain ⟨C2, hC2⟩ := hKc.exists_bound_of_continuousOn hGcont.continuousOn
  refine ⟨|C1| + |C2| + 1, by positivity, ?_⟩
  intro τ hτ t
  -- reduce an arbitrary `t` to the fundamental domain using `2π`-periodicity
  obtain ⟨k, t', ht'mem, ht'eq, hft⟩ :=
    Work.RPB.B4.periodic_reduce (fun s => CI.c τ s) (fun s => CI.per τ s) t
  have ht'box : (τ, t') ∈ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) (2 * Real.pi) :=
    ⟨hτ, ⟨ht'mem.1, le_of_lt ht'mem.2⟩⟩
  -- the derivative is equally `2π`-periodic in `t`
  have hperD : Function.Periodic (deriv (CI.c τ)) (2 * Real.pi) :=
    Work.RPB.B4.periodic_deriv (CI.c τ) (2 * Real.pi) (CI.per τ)
  have hdeq : deriv (CI.c τ) t = deriv (CI.c τ) t' := by
    rw [ht'eq]
    exact hperD.zsmul k t'
  refine ⟨?_, ?_⟩
  · calc ‖CI.c τ t‖ ≤ C1 := by
          rw [hft]
          exact hC1 (τ, t') ht'box
      _ ≤ |C1| + |C2| + 1 := by
          have h1 : C1 ≤ |C1| := le_abs_self C1
          have h2 : (0:ℝ) ≤ |C2| := abs_nonneg C2
          linarith
  · calc ‖deriv (CI.c τ) t‖ ≤ C2 := by
          rw [hdeq]
          exact hC2 (τ, t') ht'box
      _ ≤ |C1| + |C2| + 1 := by
          have h1 : C2 ≤ |C2| := le_abs_self C2
          have h2 : (0:ℝ) ≤ |C1| := abs_nonneg C1
          linarith

end Work.RPB.B5
