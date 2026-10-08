import Submission.Work.CharLib.CFun
import Submission.Work.CharCore.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.CharCore` versus `Work.CharLib`

The seed module `Submission.Work.CharLib` (the in-house character-theory seed, which is only
stated for groups in the universe `Type`) defines `cfInner`, `IsClassFun` and `indFun` with the
same formulas as this area, but universe-monomorphically.  This file records that the two
notions are *definitionally* the same on groups in `Type`, so results proved with either can be
transported freely.
-/

noncomputable section

open Classical

namespace Work.CharCore

variable {G : Type} [Group G] [Fintype G]

theorem cfInner_eq_charLib (f g : G → ℂ) : cfInner f g = Work.CharLib.cfInner f g := rfl

@[simp] theorem charLib_cfInner_eq (f g : G → ℂ) : Work.CharLib.cfInner f g = cfInner f g := rfl

theorem IsClassFun_iff_charLib (f : G → ℂ) : IsClassFun f ↔ Work.CharLib.IsClassFun f := Iff.rfl

theorem indFun_eq_charLib (H : Subgroup G) (f : H → ℂ) : indFun H f = Work.CharLib.indFun H f := rfl

end Work.CharCore
