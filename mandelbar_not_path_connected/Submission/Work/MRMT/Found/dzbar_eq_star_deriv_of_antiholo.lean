import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Wirtinger.dzbar_comp
import Submission.Work.MRMT.Wirtinger.beltramiOf_comp_antiholo
import Submission.Work.MRMT.QC.CompHolo.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

/-- Conjugating an `ℝ`-differentiable map interchanges the two Wirtinger derivatives:
`∂̄(conj ∘ g) = conj (∂g)`. -/
lemma dzbar_star_comp_anti {g : ℂ → ℂ} {w : ℂ} (hg : DifferentiableAt ℝ g w) :
    Work.MRMT.dzbar ((star : ℂ → ℂ) ∘ g) w = star (Work.MRMT.dz g w) := by
  have h := Work.MRMT.Wirtinger.dzbar_comp (f := g) (g := (star : ℂ → ℂ))
    (Work.MRMT.Wirtinger.differentiableAt_star (g w)) hg
  simp only [Work.MRMT.Wirtinger.dz_star, Work.MRMT.Wirtinger.dzbar_star, zero_mul,
    one_mul, zero_add] at h
  exact h

/-- For an anti-holomorphic `f` (i.e. `star ∘ f` complex differentiable), the Wirtinger
derivative `∂̄ f` equals `conj ∘ deriv (star ∘ f)`. -/
theorem dzbar_eq_star_deriv_of_antiholo {f : ℂ → ℂ} (hf : Differentiable ℂ (star ∘ f)) (z : ℂ) :
    Work.MRMT.dzbar f z = star (deriv (star ∘ f) z) := by
  have h1 : f = (star : ℂ → ℂ) ∘ (star ∘ f) := by funext w; simp
  have h2 : DifferentiableAt ℝ (star ∘ f) z := (hf z).restrictScalars ℝ
  conv_lhs => rw [h1]
  rw [dzbar_star_comp_anti h2, Work.MRMT.QC.dz_holo (hf z)]

end Work.MRMT.Found
