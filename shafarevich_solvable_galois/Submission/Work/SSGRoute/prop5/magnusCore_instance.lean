import Mathlib
import Submission.Work.SSGRoute.prop5.magnus_mem_one_add
import Submission.Work.SSGRoute.prop5.magnusGroupPart
import Submission.Work.SSGRoute.prop5.core.Assembly
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Magnus core statement, instance form

This file proves the statement requested as `Work.SSGRoute.prop5.magnusCore_instance`: the "hard
half" of the Magnus embedding theorem, in the form in which it is used by the
Schmidt–Wingberg development of Shafarevich's theorem.

If `y` lies in `γ_{n+1}` (Mathlib: `lowerCentralSeries n`) and the Magnus image of `y` is congruent
to `1` modulo the degree `n+2` part of the truncated free associative algebra
`FreeAssoc X ⧸ fil X N` (for some `N ≥ n+2`), then `y ∈ γ_{n+2}`.

The proof is in `core/Assembly.lean`: it reduces the truncation to `N = n+2`
(`core.magLead_eq_zero_of_mem`), writes the class of `y` in `γ_{n+1}/γ_{n+2}` as a combination of
commutator monomials of weight `n+1` (`core.gen_span`), uses the additivity of the Magnus leading
term and the identification of the leading term of a commutator monomial with the corresponding
bracketed monomial (`core.magLead_monGrp_sub_mem`), applies Witt's theorem (the injectivity of the
free Lie ring into the free associative ring, proved from the Hall-set inputs in `witt/`), and
finally the well-definedness of the comparison map into the graded Lie ring
(`core.relations_zero`).
-/

noncomputable section

open scoped commutatorElement

namespace Work.SSGRoute.prop5

/-- **The Magnus core statement** (instance form). -/
theorem magnusCore_instance (X : Type) (N n : ℕ) (hn : n + 2 ≤ N) (y : FreeGroup X)
    (hy : y ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries n)
    (h : ((magnus X N y : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N) - 1 ∈
      filq X N (n + 2)) :
    y ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (n + 1) := by
  have hk : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
  have hy' : y ∈ core.Gam X (n + 1 - 1) := by simpa using (core.mem_Gam_iff.mpr hy)
  have hzero : magLead (n + 1 + 1) y = 0 :=
    core.magLead_eq_zero_of_mem (X := X) N n hn y (by simpa [magLead] using h)
  have hmem := core.magnusCore_aux X (n + 1) hk y hy' (by simpa using hzero)
  exact core.mem_Gam_iff.mp hmem

end Work.SSGRoute.prop5
