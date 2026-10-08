import Mathlib
import Submission.Work.CharCore.Basic
import Submission.Work.CharCore.isChar_iff
import Submission.Work.CharCore.cfInner_character_nat

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.CharCore

/-- The character of any finite dimensional complex representation of a finite group is a
character (a non-negative integral combination of irreducible characters).

This is the `mpr` direction of `Work.CharCore.isChar_iff`: `isChar_iff` reduces the claim to
the statement that the multiplicity `cfInner ρ.character χ` of each irreducible character
`χ ∈ Irr G` in `ρ.character` is a natural number, which is
`Work.CharCore.cfInner_character_nat`. -/
theorem isChar_character {G : Type*} [Group G] [Fintype G] {V : Type*} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) :
    IsChar ρ.character :=
  (isChar_iff (isClassFun_character ρ)).mpr fun χ hχ => cfInner_character_nat (χ := χ) ρ hχ

end Work.CharCore
