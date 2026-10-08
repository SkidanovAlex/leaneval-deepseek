import Mathlib
import Submission.Work.ThompsonFrobenius.BlueprintZJ
import Submission.Work.GlaubermanZJ.ZJ_eq
import Submission.Work.PGroup.All

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Area `ThompsonFrobenius`: `ZJ` is natural under automorphisms (Z6 of the design note)

`ZJ (α P) = α (ZJ P)` for every automorphism `α`, hence (with `IsInv α P`) `ZJ P` is
`α`-invariant.  Obtained from the delivered `Work.PGroup.ZJ_map_of_ker_inf_eq_bot` through the
bridge `Work.GlaubermanZJ.ZJ_eq`.
-/

set_option autoImplicit false

namespace Work.ThompsonFrobenius

theorem ZJ_map_mulAut {G : Type*} [Group G] [Finite G] (α : MulAut G) (P : Subgroup G) :
    (Submission.Blueprint.ZJ P).map α.toMonoidHom =
      Submission.Blueprint.ZJ (P.map α.toMonoidHom) := by
  have hker : P ⊓ (α.toMonoidHom).ker = ⊥ := by
    refine le_antisymm (fun x hx => ?_) bot_le
    rw [Subgroup.mem_bot]
    have hxmem : x ∈ (α.toMonoidHom).ker := by simpa using hx.2
    have hx1 : α x = 1 := MonoidHom.mem_ker.mp hxmem
    exact α.injective (by rw [hx1, map_one])
  have h3 := Work.PGroup.ZJ_map_of_ker_inf_eq_bot α.toMonoidHom P hker
  rw [Work.GlaubermanZJ.ZJ_eq P, Work.GlaubermanZJ.ZJ_eq (P.map α.toMonoidHom), h3]

end Work.ThompsonFrobenius
