import Mathlib
import Submission.Work.Top.Jordan
import Submission.Work.TopJordan.CurveModel
import Submission.Commons.Topology.Jordan.two_arcs_through

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

open Set

namespace Work.TopJordan

noncomputable section

/-- **A Jordan curve through `1` and `-1` splits into two arcs.**  A Jordan curve `C` containing
`1`, `-1` and a further point `l ∉ {1, -1}` is the union of two injective paths from `-1` to `1`
which meet exactly in the two endpoints; `l` lies on the first of them.  This is the converse of
`Work.TopJordan.isJordanCurve_of_two_paths`. -/
theorem exists_two_paths_of_isJordanCurve {C : Set ℂ} (hC : Work.Top.IsJordanCurve C)
    {l : ℂ} (hl : l ∈ C) (hl1 : l ≠ 1) (hlm1 : l ≠ -1)
    (h1 : (1 : ℂ) ∈ C) (hm1 : (-1 : ℂ) ∈ C) :
    ∃ P Q : Path (-1 : ℂ) 1,
      Set.range ⇑P ∪ Set.range ⇑Q = C ∧ Set.range ⇑P ∩ Set.range ⇑Q = {(1 : ℂ), -1} ∧
        Function.Injective ⇑P ∧ Function.Injective ⇑Q ∧ l ∈ Set.range ⇑P := by
  obtain ⟨γ, hγ, hrange⟩ := hC
  have := Commons.Topology.Jordan.two_arcs_through (toCircle γ) (toCircle_injective hγ) l
    (by rw [range_toCircle, hrange]; exact hl) hl1 hlm1
    (by rw [range_toCircle, hrange]; exact h1)
    (by rw [range_toCircle, hrange]; exact hm1)
  simpa only [range_toCircle, hrange] using this

end

end Work.TopJordan
