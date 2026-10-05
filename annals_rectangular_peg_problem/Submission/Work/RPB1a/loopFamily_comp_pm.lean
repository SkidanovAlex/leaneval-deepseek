import Mathlib
import Submission.Work.RPB1a.Defs

namespace Work.RPB1a

open Complex Set Metric
open scoped ContDiff Real
open Work.RPB1a

/-- Pre-composing the *time* variable of a loop family with `t ↦ e * t`, where `e = 1` or
`e = -1`, again yields a loop family.

`e = 1` is the identity reparametrisation; `e = -1` reverses the time direction of every loop,
and all four fields of `IsLoopFamily` survive it:
joint smoothness is precomposition with the smooth (linear) map `(s,t) ↦ (s, -t)`;
`2π`-periodicity uses `c s (-1 * (t + 2π)) = c s (-1 * t - 2π) = c s (-1 * t)` (periodicity
applied backwards); injectivity mod `2π` turns a solution `-t' = -t + 2πm` into
`t' = t + 2π(-m)`; and the immersion condition uses
`deriv (fun t => c s (-t)) t = -deriv (c s) (-t)` (`deriv_comp_neg`). -/
theorem loopFamily_comp_pm {c : ℝ → ℝ → ℂ} (hc : IsLoopFamily c) {e : ℝ} (he : e = 1 ∨ e = -1) :
    IsLoopFamily (fun s t => c s (e * t)) := by
  rcases he with rfl | rfl
  · -- `e = 1`: identity reparametrisation (`1 * t = t`)
    simpa using hc
  · -- `e = -1`: time reversal of every loop
    obtain ⟨hcont, hper, hinj, himm⟩ := hc
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- joint smoothness: precomposition with the linear map `z ↦ (z.1, -z.2)`
      have hmap : ContDiff ℝ ∞ (fun z : ℝ × ℝ => (z.1, -1 * z.2)) := by fun_prop
      simpa [Function.comp_def] using hcont.comp hmap
    · -- `2π`-periodicity
      intro s t
      change c s (-1 * (t + 2 * π)) = c s (-1 * t)
      rw [show (-1 : ℝ) * (t + 2 * π) = -1 * t - 2 * π by ring]
      simpa using (hper s (-1 * t - 2 * π)).symm
    · -- injectivity mod `2π`
      intro s hs t t' h
      obtain ⟨m, hm⟩ := hinj s hs (-1 * t) (-1 * t') h
      exact ⟨-m, by push_cast; linarith⟩
    · -- immersed: the `t`-derivative picks up the factor `-1`
      intro s hs t
      have hd : deriv (fun t : ℝ => c s (-1 * t)) t = - deriv (c s) (-1 * t) := by
        simpa using deriv_comp_neg (c s) t
      rw [hd]
      exact neg_ne_zero.mpr (himm s hs (-1 * t))

end Work.RPB1a
