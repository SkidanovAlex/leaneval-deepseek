import Mathlib
import Submission.Work.Induction.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Induction

open Classical
open scoped Pointwise

-- For a *self-normalizing* subgroup the two standard forms of the TI condition agree:
-- `H ⊓ Hˣ = 1` for all `x ∉ N_G(H)` is equivalent to `H ⊓ Hˣ = 1` for all `x ∉ H` when
-- `N_G(H) = H`.  (`⟸` holds for every `H` since `H ≤ N_G(H)`; `⟹` needs `N_G(H) = H`, because
-- for `x ∈ N_G(H) \ H` and `H ≠ ⊥` we have `H ⊓ Hˣ = H ≠ ⊥`.)
theorem isTI_iff_forall_notMem {G : Type*} [Group G] {H : Subgroup G}
    (hN : Work.Induction.normalizer H = H) :
    Work.Induction.IsTI H ↔ ∀ x : G, x ∉ H → H ⊓ (MulAut.conj x • H) = ⊥ := by
  rw [IsTI, hN]

end Work.Induction
