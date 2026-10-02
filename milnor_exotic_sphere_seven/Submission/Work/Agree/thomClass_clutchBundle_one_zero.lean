import Submission.Work.Agree.isOrientedOver_clutchBundle_one_zero
import Submission.Work.Thom.localThom_full

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The Thom class of `L¹R⁰ = clutchBundle 1 0`

`Work.Thom.nonempty_thomClass_of_charts` produces a Thom class from an oriented two-chart cover.
For `clutchBundle 1 0` the cover is `hemi0 = baseSet false`, `hemi1 = baseSet true` (so the three
subset obligations are definitional), the cover is `Work.Agree.hemi_cover'`, and the orientation is
`Work.Agree.isOrientedOver_clutchBundle_one_zero`.  This is the first ingredient of the `a = 1`
core `Work.Agree.bottHopfOne`: with the Thom class in hand the Gysin exactness of the sphere bundle
of `clutchBundle 1 0` computes its Euler class, `e(L¹R⁰) = ± (generator)`.
-/

namespace Work.Agree

open Work.TangentClasses

/-- The two hemispheres cover `S⁴`. -/
lemma hemi_cover' : hemi0 ∪ hemi1 = (Set.univ : Set S4) := by
  ext p
  by_cases h : p = OnePoint.infty
  · subst h
    simp [hemi1]
  · simp [hemi0, h]

/-- **`clutchBundle 1 0` carries a Thom class**: it is oriented over the two-chart cover
`{hemi0, hemi1}` by `isOrientedOver_clutchBundle_one_zero`. -/
theorem nonempty_thomClass_clutchBundle_one_zero :
    Nonempty (Work.Thom.ThomClass (clutchBundle 1 0) 4) :=
  Work.Thom.nonempty_thomClass_of_charts (n := 4) (by norm_num) Bool (clutchBundle 1 0)
    (U := hemi0) (V := hemi1) (i := false) (j := true) (k := false)
    isOpen_hemi0 isOpen_hemi1 hemi_cover'
    (fun x hx => hx) (fun x hx => hx) (fun x hx => hx.1)
    isOrientedOver_clutchBundle_one_zero

end Work.Agree
