import Mathlib
import Submission.Work.FQC.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FQC

open LeanEval.ComplexAnalysis (Tantibar)

/-- `0` is the unique point of the fibre of `T_c` over `T_c 0 = c`: the equation
`T_c y = T_c 0` forces `y = 0`. -/
private theorem Tantibar_eq_Tantibar_zero {c y : ℂ} (h : Tantibar c y = Tantibar c 0) :
    y = 0 := by
  have h' : (starRingEnd ℂ y) ^ 2 + c = (starRingEnd ℂ 0) ^ 2 + c := by
    simpa [Tantibar] using h
  have h2 : (starRingEnd ℂ y) ^ 2 = 0 := by
    simpa using add_right_cancel h'
  have h3 : starRingEnd ℂ y = 0 := sq_eq_zero_iff.mp h2
  simpa using congrArg (starRingEnd ℂ) h3

/-- If the fibre of `T_c` over `T_c w` is the singleton `{w}` (that is, no other point is mapped
to `T_c w`), then `w = 0`: for `w ≠ 0` the point `-w ≠ w` is mapped to the same value, because
`T_c(-w) = conj (-w)² + c = conj w² + c = T_c w`.  So `0` is the unique point whose image has a
singleton fibre — it is the critical point of the antiholomorphic map `T_c`. -/
private theorem eq_zero_of_singleton_fiber {c w : ℂ}
    (h : ∀ z : ℂ, Tantibar c z = Tantibar c w → z = w) : w = 0 := by
  by_contra hw
  have hne : -w ≠ w := neg_ne_self.mpr hw
  have heq : Tantibar c (-w) = Tantibar c w := by
    simp only [Tantibar, map_neg, neg_sq]
  exact hne (h (-w) heq)

theorem zero_of_conj {θ : ℂ → ℂ} {c c₂ : ℂ} (hθ : Function.Bijective θ) (hconj : ∀ z : ℂ, θ (LeanEval.ComplexAnalysis.Tantibar c z) = LeanEval.ComplexAnalysis.Tantibar c₂ (θ z)) : θ 0 = 0 := by
  -- The fibre of `T_{c₂}` over `T_{c₂} (θ 0)` is the singleton `{θ 0}`.
  have hfib : ∀ z : ℂ, Tantibar c₂ z = Tantibar c₂ (θ 0) → z = θ 0 := by
    intro z hz
    obtain ⟨y, rfl⟩ := hθ.2 z
    have hy : Tantibar c y = Tantibar c 0 := by
      apply hθ.1
      rw [hconj y, hconj 0]
      exact hz
    rw [Tantibar_eq_Tantibar_zero hy]
  by_contra hne
  have hne' : -θ 0 ≠ θ 0 := neg_ne_self.mpr hne
  exact hne' (hfib (-(θ 0)) (by simp only [Tantibar, map_neg, neg_sq]))

end Work.FQC
