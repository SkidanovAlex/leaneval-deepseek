import Mathlib
import Submission.Work.Thom.Glue
import Submission.Work.Cohomology.CupRing
import Submission.Work.Thom.MixedCup
import Submission.Work.Thom.localThomMap_cup_zero

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Thom

/-- H⁰-linearity of the local Thom map: the local Thom map is linear over the ring `H⁰(W;ℤ)`
acting by cup product.  This is the statement `Work.Thom.localThomMap_cup_zero`, recorded here
under the requested name. -/
theorem localThomMap_cupH0 {B : Type} [TopologicalSpace B] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type}
    (Z : Work.TangentClasses.RealBundle B F ι) (n : ℕ) (W : Set B)
    (τ : Work.Thom.PieceCoh Z W n) (x c : Work.Thom.Coh ℤ 0 ↥W) :
    Work.Thom.localThomMap Z n W
        ((Nat.zero_add n) ▸ (Work.Thom.localThomMap Z n W τ 0 c)) 0 x =
      Work.Thom.localThomMap Z n W τ 0
        (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥W)) 0 0 x c) :=
  Work.Thom.localThomMap_cup_zero Z n W τ x c

end Work.Thom
