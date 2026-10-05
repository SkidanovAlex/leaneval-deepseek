import Mathlib
import Submission.Work.RPB1a.Defs

namespace Work.RPB1a

open Complex Set Metric
open scoped ContDiff Real
open Work.RPB1a

/-- `IsLoopFamily` is preserved by reversing the parameter direction `s ↦ 1 - s`. -/
theorem loopFamily_reverse {c : ℝ → ℝ → ℂ} (hc : IsLoopFamily c) :
    IsLoopFamily (fun s t => c (1 - s) t) := by
  obtain ⟨hcd, hper, hinj, himm⟩ := hc
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- joint smoothness of the reparametrised family
    have hmap : ContDiff ℝ ∞ (fun z : ℝ × ℝ => (1 - z.1, z.2)) := by fun_prop
    exact hcd.comp hmap
  · -- `2π`-periodicity in `t`
    intro s t
    exact hper (1 - s) t
  · -- injectivity mod `2π`, using `1 - s ∈ [0,1]` for `s ∈ [0,1]`
    intro s hs t t' h
    have hs' : (1 - s) ∈ Icc (0 : ℝ) 1 := by
      simp only [mem_Icc] at hs ⊢
      constructor <;> linarith [hs.1, hs.2]
    exact hinj (1 - s) hs' t t' h
  · -- non-vanishing `t`-derivative
    intro s hs t
    have hs' : (1 - s) ∈ Icc (0 : ℝ) 1 := by
      simp only [mem_Icc] at hs ⊢
      constructor <;> linarith [hs.1, hs.2]
    exact himm (1 - s) hs' t

end Work.RPB1a
