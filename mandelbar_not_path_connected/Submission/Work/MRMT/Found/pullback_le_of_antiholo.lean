import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Found.lintegral_comp_le_of_isCompact_disjoint
import Submission.Work.MRMT.Wirtinger.beltramiOf_comp_antiholo

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

open MeasureTheory Filter Topology Complex Function
open scoped Topology ENNReal

noncomputable section

/-- An anti-holomorphic map is `C¹` as a real map. -/
theorem contDiff_one_of_antiholo' {f : ℂ → ℂ} (hf : Differentiable ℂ (star ∘ f)) :
    ContDiff ℝ 1 f := by
  have hstar_contDiff : ContDiff ℝ 1 (star : ℂ → ℂ) := by
    have h1 : (star : ℂ → ℂ) = ⇑Complex.conjCLE := by funext w; simp
    rw [h1]; exact Complex.conjCLE.contDiff
  have h1 : f = star ∘ (star ∘ f) := by funext w; simp
  rw [h1]
  exact hstar_contDiff.comp ((hf.contDiff (n := 1)).restrict_scalars ℝ)

theorem pullback_le_of_antiholo {f : ℂ → ℂ} (hf : Differentiable ℂ (star ∘ f))
    {K : Set ℂ} (hK : IsCompact K) (hdzb : ∀ z ∈ K, Work.MRMT.dzbar f z ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℂ → ENNReal,
      ∫⁻ z in K, H (f z) ≤ ENNReal.ofReal C * ∫⁻ w in f '' K, H w := by
  have hcd : ContDiff ℝ 1 f := contDiff_one_of_antiholo' hf
  have hdz : ∀ z, Work.MRMT.dz f z = 0 := fun z => Work.MRMT.Wirtinger.dz_of_antiholo (hf z)
  refine lintegral_comp_le_of_isCompact_disjoint (S := {z | Work.MRMT.dzbar f z = 0}) hcd ?_ hK ?_
  · intro z hz
    have hz' : Work.MRMT.dzbar f z ≠ 0 := hz
    rw [hdz z]
    simp only [norm_zero]
    exact norm_pos_iff.mpr hz'
  · rw [Set.disjoint_left]
    intro z hzK hzS
    exact hdzb z hzK hzS

end

end Work.MRMT.Found
