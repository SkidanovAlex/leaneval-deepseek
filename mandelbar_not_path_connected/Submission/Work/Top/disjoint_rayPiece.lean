import Mathlib
import Submission.Work.Top.Defs
import Submission.Work.Top.rayPt_injOn
import Submission.Work.Top.paramRay_rayPt_norm

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Top

open Classical Filter Set
open scoped Topology

/-- The point of the parameter ray of angle `β` reached by `c` is the ray point of that angle
at level `‖Φ c‖`, so a common point of two ray pieces sits on both rays at the *same* level. -/
theorem disjoint_rayPiece {Mb : Set ℂ} {Φ : ℂ → ℂ} (hN : Work.Top.NakaneData Mb Φ)
    {β β' t t' R R' : ℝ} (hβ₀ : 0 ≤ β) (hβ₁ : β < 1) (hβ'₀ : 0 ≤ β') (hβ'₁ : β' < 1)
    (hne : β ≠ β') :
    Disjoint (Work.Top.NakaneData.rayPiece hN β t R)
      (Work.Top.NakaneData.rayPiece hN β' t' R') := by
  rw [Set.disjoint_left]
  intro c hc hc'
  -- Both pieces lie on the corresponding parameter rays.
  obtain ⟨hp, -, -⟩ := hc
  obtain ⟨hp', -, -⟩ := hc'
  -- `c` is off the connectedness locus, so its Böttcher coordinate has modulus `> 1`.
  have hcMb : c ∉ Mb := hp.1
  have hs : 1 < ‖Φ c‖ := hN.Phi_mem_exteriorDisc hcMb
  -- Hence `c` is the ray point of angle `β` (resp. `β'`) at the *same* level `‖Φ c‖`.
  have e1 := (Work.Top.paramRay_rayPt_norm hN hp).1
  have e2 := (Work.Top.paramRay_rayPt_norm hN hp').1
  -- Injectivity of `rayPt` in the angle on `[0,1)` forces `β = β'`.
  have h := Work.Top.rayPt_injOn hN hβ₀ hβ₁ hβ'₀ hβ'₁ hs hs (by rw [← e1, ← e2])
  exact hne h.1

end Work.Top
