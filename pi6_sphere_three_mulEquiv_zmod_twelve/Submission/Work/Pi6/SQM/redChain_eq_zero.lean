import Mathlib
import Submission.Work.Pi6.SQM.SqOneDefs
import Submission.Work.Pi6.SQM.redChainKernel
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# `Pi6/SQM/redChain_eq_zero`

The kernel of the coefficientwise reduction of integral chains mod `2`: an integral `n`-chain of a
simplicial set whose mod-2 reduction vanishes is twice an integral chain.

This is the first component of `Work.Pi6.SQM.redChainKernel` (`Pi6/SQM/redChainKernel`), restated
for the chain complex `X.chainComplex (ModuleCat.of ℤ ℤ)` in place of the abbreviation
`Work.Cohomology.chainC ℤ X`, which is definitionally the same object.
-/

namespace Work.Pi6.SQM

theorem redChain_eq_zero (X : SSet) (n : ℕ)
    (c : ↥((X.chainComplex (ModuleCat.of ℤ ℤ)).X n))
    (h : Work.Pi6.SQM.redChain X n c = 0) : ∃ c', c = (2 : ℤ) • c' := by
  obtain ⟨c', hc'⟩ := (redChainKernel (Y := X) n).1 c h
  exact ⟨c', hc'.symm⟩

end Work.Pi6.SQM
