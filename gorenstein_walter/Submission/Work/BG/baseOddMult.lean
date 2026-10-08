import Mathlib
import Submission.Work.BG.Glauberman
import Submission.Work.BG.glauberman_two

namespace Work.BG

open OddOrder.RepresentationTheory

-- `letI`/`haveI` are essential here: the `Fintype`/`Invertible` instances they bind must be
-- visible to typeclass search for `glauberman_two`; the linter's suggested `let`/`have` would
-- not be.
set_option linter.style.haveILetI false in

/-- **BG-L7(a)** in instance-free form: `BaseOddMultProp` is the `|S| = 2` case of
Glauberman's character correspondence (`glauberman_two`), restated in the `OddMultUnique`
vocabulary of area `BG`.  The only work is the instance bookkeeping: `BaseOddMultProp` lives
in the `[Finite U]`-world used by `IsOddMult`/`OddMultUnique` (which manufacture their own
`Fintype`/`Invertible` instances from finiteness), while `glauberman_two` takes those
instances as arguments; `OddMultBridgeProp` (`oddMultBridge`, proved in `Glauberman.lean`)
relates the two forms of "odd multiplicity". -/
theorem baseOddMult : Work.BG.BaseOddMultProp := by
  intro U _ _ hU σ hσ α hα
  letI : Fintype U := Fintype.ofFinite U
  haveI hcardU : Invertible (Nat.card U : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Fintype ↥(fixedSubgroup σ) := Fintype.ofFinite _
  haveI hcardK : Invertible (Nat.card ↥(fixedSubgroup σ) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  obtain ⟨β, hβ, huniq⟩ := glauberman_two hU σ hσ α hα
  refine ⟨β, ?_, ?_⟩
  · exact (oddMultBridge (fixedSubgroup σ) (α : ClassFunction U ℂ)
      (β : ClassFunction ↥(fixedSubgroup σ) ℂ)).mpr hβ
  · intro β' hβ'
    exact huniq β' ((oddMultBridge (fixedSubgroup σ) (α : ClassFunction U ℂ)
      (β' : ClassFunction ↥(fixedSubgroup σ) ℂ)).mp hβ')

end Work.BG
