import Submission.Work.CharLib.CFun
import Submission.Work.Coherence.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Compatibility of `Work.Coherence.cfInner` with `Work.CharLib.cfInner`

`Work.CharLib.cfInner` (the inner product used by the `A5` character-theory area) is declared for
`G : Type`, i.e. it is monomorphic in the universe of `G`.  The coherence area uses its own
universe-polymorphic copy `Work.Coherence.cfInner` (see `Work.Coherence.Inner`), defined by exactly
the same formula.  This file records that the two are the same function, so that a caller holding a
result phrased with `CharLib` vocabulary can use it here and conversely.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Classical

namespace Work.Coherence

/-- `Work.Coherence.cfInner` and `Work.CharLib.cfInner` are the same function. -/
theorem charLib_cfInner {G : Type} [Fintype G] (f g : G → ℂ) :
    Work.CharLib.cfInner f g = cfInner f g := rfl

/-- `Work.Coherence.IsClassFun` and `Work.CharLib.IsClassFun` are the same predicate. -/
theorem charLib_isClassFun {G : Type} [Group G] (f : G → ℂ) :
    Work.CharLib.IsClassFun f ↔ IsClassFun f := Iff.rfl

/-- Irreducible characters are class functions in the sense of `Work.CharLib`. -/
theorem charLib_isClassFun_of_mem_Irr {G : Type} [Group G] [Fintype G] {χ : G → ℂ}
    (hχ : χ ∈ Irr G) : Work.CharLib.IsClassFun χ :=
  (charLib_isClassFun χ).mpr (isClassFun_of_mem_Irr hχ)

end Work.Coherence
