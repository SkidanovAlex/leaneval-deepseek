import Mathlib
import Submission.Work.Top.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Top

/-- A point of the parameter ray of angle `β` is the point `rayPt hN β t` of that ray at level
`t = ‖Φ c‖` (equivalently, the ray is parametrised by the modulus of the Böttcher coordinate),
and its potential is `log ‖Φ c‖`. -/
theorem paramRay_rayPt_norm {Mb : Set ℂ} {Φ : ℂ → ℂ} (hN : Work.Top.NakaneData Mb Φ) {β : ℝ} {c : ℂ}
    (hc : c ∈ Work.Top.NakaneData.paramRay hN β) :
    c = Work.Top.NakaneData.rayPt hN β ‖Φ c‖ ∧
      Work.Top.potential Mb Φ c = Real.log ‖Φ c‖ := by
  obtain ⟨hcMb, t, ht, hΦ⟩ := hc
  have hnorm : ‖Φ c‖ = t := by
    rw [hΦ, NakaneData.norm_rayPoint, abs_of_pos (by linarith)]
  have h1 : c = NakaneData.rayPt hN β t :=
    hN.injOn_Phi hcMb (hN.rayPt_notMem ht) (by rw [hN.Phi_rayPt ht]; exact hΦ)
  refine ⟨?_, potential_of_not_mem hcMb⟩
  rw [hnorm]
  exact h1

end Work.Top
