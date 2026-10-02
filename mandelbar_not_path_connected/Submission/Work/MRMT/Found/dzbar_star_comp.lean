import Mathlib
import Submission.Work.MRMT.Basic
import Submission.Work.MRMT.Wirtinger.dz_comp
import Submission.Work.MRMT.Wirtinger.dzbar_comp
import Submission.Work.MRMT.Wirtinger.beltramiOf_comp_antiholo

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

/-- `∂(conj ∘ F) = conj (∂̄F)`: conjugating an `ℝ`-differentiable map interchanges its
two Wirtinger derivatives. -/
theorem dz_star_conj {F : ℂ → ℂ} {z : ℂ} (hF : DifferentiableAt ℝ F z) :
    Work.MRMT.dz ((star : ℂ → ℂ) ∘ F) z = star (Work.MRMT.dzbar F z) := by
  have h := Work.MRMT.Wirtinger.dz_comp (f := F) (g := (star : ℂ → ℂ))
    (Work.MRMT.Wirtinger.differentiableAt_star (F z)) hF
  simp only [Work.MRMT.Wirtinger.dz_star, Work.MRMT.Wirtinger.dzbar_star, zero_mul,
    one_mul, zero_add] at h
  exact h

/-- `∂̄(conj ∘ F) = conj (∂F)`. -/
theorem dzbar_star_conj {F : ℂ → ℂ} {z : ℂ} (hF : DifferentiableAt ℝ F z) :
    Work.MRMT.dzbar ((star : ℂ → ℂ) ∘ F) z = star (Work.MRMT.dz F z) := by
  have h := Work.MRMT.Wirtinger.dzbar_comp (f := F) (g := (star : ℂ → ℂ))
    (Work.MRMT.Wirtinger.differentiableAt_star (F z)) hF
  simp only [Work.MRMT.Wirtinger.dz_star, Work.MRMT.Wirtinger.dzbar_star, zero_mul,
    one_mul, zero_add] at h
  exact h

theorem dzbar_star_comp {F f μF : ℂ → ℂ} {z : ℂ}
    (hF : DifferentiableAt ℝ F (f z)) (hf : DifferentiableAt ℝ f z)
    (hrel : Work.MRMT.dzbar F (f z) = μF (f z) * Work.MRMT.dz F (f z)) :
    Work.MRMT.dzbar (star ∘ F ∘ f) z
      = star (Work.MRMT.dz F (f z)) * (star (Work.MRMT.dz f z) + star (μF (f z)) * Work.MRMT.dzbar f z) := by
  have hG : DifferentiableAt ℝ ((star : ℂ → ℂ) ∘ F) (f z) :=
    DifferentiableAt.comp (f z) (Work.MRMT.Wirtinger.differentiableAt_star (F (f z))) hF
  have hchain := Work.MRMT.Wirtinger.dzbar_comp (f := f) (g := (star : ℂ → ℂ) ∘ F) hG hf
  have hst : star (Work.MRMT.dzbar F (f z)) = star (Work.MRMT.dz F (f z)) * star (μF (f z)) := by
    rw [hrel, star_mul]
  rw [← Function.comp_assoc (star : ℂ → ℂ) F f, hchain, dz_star_conj hF, dzbar_star_conj hF, hst]
  ring

end Work.MRMT.Found
