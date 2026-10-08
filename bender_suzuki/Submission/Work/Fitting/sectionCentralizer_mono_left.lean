import Mathlib
import Submission.Work.Fitting.Defs
import Submission.Work.Fitting.mem_sectionCentralizer_iff_commutator

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Fitting

/-- `C_G(K/H)` is monotone in `H`: passing to a larger normal subgroup `H ≤ H'`
shrinks the section `K/H'` to a quotient of `K/H`, so anything centralizing `K/H`
also centralizes `K/H'`. -/
theorem sectionCentralizer_mono_left {G : Type*} [Group G] {H H' K : Subgroup G}
    [H.Normal] [H'.Normal] (h : H ≤ H') :
    Work.Fitting.sectionCentralizer H K ≤ Work.Fitting.sectionCentralizer H' K := by
  intro x hx
  rw [Work.Fitting.mem_sectionCentralizer_iff_commutator] at hx ⊢
  exact fun k hk => h (hx k hk)

end Work.Fitting
