import Submission.Work.MotAS.AsT.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Auxiliary lemmas for the group steps of the AS transport

The exponent `(l : ℕ)` of `w ^ (l : ℕ)` for `l : Fin 5` has to be reduced to a numeral before
`ring` can compare the expanded sums with the (`w`-free) reduced forms.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.MotAS.AsT

@[simp] lemma finVal0 : ((0 : Fin 5) : ℕ) = 0 := rfl
@[simp] lemma finVal1 : ((1 : Fin 5) : ℕ) = 1 := rfl
@[simp] lemma finVal2 : ((2 : Fin 5) : ℕ) = 2 := rfl
@[simp] lemma finVal3 : ((3 : Fin 5) : ℕ) = 3 := rfl
@[simp] lemma finVal4 : ((4 : Fin 5) : ℕ) = 4 := rfl

end Work.MotAS.AsT
