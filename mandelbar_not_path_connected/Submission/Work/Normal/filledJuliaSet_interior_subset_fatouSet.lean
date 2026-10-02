import Mathlib
import Submission.Work.Normal.Basic
import Submission.Work.Normal.escapeRadius
import Submission.Work.Normal.montel_locallyBounded

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Normal

/-- The interior of the filled Julia set of a polynomial map of degree at least two consists of
Fatou points: the iterates are locally bounded there (with the escape radius as a uniform bound),
hence normal by Montel's locally bounded principle. -/
theorem filledJuliaSet_interior_subset_fatouSet {d : ℕ} {f : ℂ → ℂ} (hd : 2 ≤ d)
    (hf : IsPolynomialMapOfDegree d f) : interior (FilledJuliaSet f) ⊆ FatouSet f := by
  obtain ⟨R, hR2, hRgrow, hKform, -⟩ := escapeRadius hd hf
  obtain ⟨P, hPd, hPeval⟩ := hf
  have hdiff : Differentiable ℂ f := by
    rw [show f = fun z => Polynomial.eval z P from funext hPeval]
    exact P.differentiable
  intro z hz
  refine ⟨interior (FilledJuliaSet f), isOpen_interior.mem_nhds hz, isOpen_interior, ?_⟩
  refine montel_locallyBounded isOpen_interior ?_ ?_
  · rintro g ⟨n, rfl⟩
    exact (hdiff.iterate n).differentiableOn
  · intro K hKU hK
    refine ⟨R, fun g hg w hw => ?_⟩
    obtain ⟨n, rfl⟩ := hg
    have hw' : w ∈ FilledJuliaSet f := interior_subset (hKU hw)
    rw [hKform] at hw'
    exact hw' n

end Work.Normal
