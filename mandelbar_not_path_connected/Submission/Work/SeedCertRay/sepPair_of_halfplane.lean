import Mathlib
import Submission.Work.SeedCertRay.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCertRay

/-- If both boxes `B` and `B'` lie in the open half-plane `{z | 0 < p * z.re + q * z.im}`, then
`B` is disjoint from the reflection `-B'` of the second box: a point `z` cannot be in `B` while
`-z` lies in `B'`, since the defining linear functional `z ↦ p * z.re + q * z.im` changes sign
under `z ↦ -z`. -/
theorem sepPair_of_halfplane (B B' : Work.SeedCertRay.Box) (p q : ℚ) (hB : ∀ z : ℂ, B.mem z → 0 < (p : ℝ) * z.re + (q : ℝ) * z.im) (hB' : ∀ z : ℂ, B'.mem z → 0 < (p : ℝ) * z.re + (q : ℝ) * z.im) : Work.SeedCertRay.SepPair B B' := by
  rw [SepPair, Set.disjoint_left]
  intro z hz hz'
  rw [Set.mem_neg] at hz'
  have h1 := hB z hz
  have h2 := hB' (-z) hz'
  simp only [Complex.neg_re, Complex.neg_im] at h2
  linarith

end Work.SeedCertRay
