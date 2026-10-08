import Mathlib
import Submission.Work.PGroup.Basic
import Submission.Work.PGroup.frattini_eq_agemo_sup_commutator
import Submission.Work.PGroup.pow_mem_frattiniIn

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The Frattini quotient of a finite `p`-group is elementary abelian

For a finite `p`-group `P`, the quotient `P / Φ(P)` by the Frattini subgroup is commutative and
has exponent dividing `p`: it is the largest elementary abelian quotient of `P`.

Both halves are immediate consequences of the structure of `Φ(P) = ℧¹(P) · ⁅P, P⁆`
(`Work.PGroup.frattini_eq_powClosure_sup_commutator`):

* the derived subgroup lies in `Φ(P)`, so `P / Φ(P)` is commutative
  (`Subgroup.Normal.quotient_commutative_iff_commutator_le`);
* every `p`-th power lies in `Φ(P)` (`Work.PGroup.pow_mem_frattini`), so every element of the
  quotient has order dividing `p`
  (`Monoid.exponent_dvd_iff_forall_pow_eq_one`).
-/

namespace Work.PGroup

open scoped Classical Pointwise
open Subgroup

/-- For a finite `p`-group `H`, the derived subgroup is contained in the Frattini subgroup. -/
theorem commutator_le_frattini {H : Type*} [Group H] [Finite H] {p : ℕ} (hp : p.Prime)
    (hH : IsPGroup p H) : commutator H ≤ frattini H := by
  rw [frattini_eq_powClosure_sup_commutator hp hH]
  exact le_sup_right

theorem frattini_quotient_elementary {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    (P : Subgroup G) [Finite P] (hP : IsPGroup p P) :
    IsMulCommutative (P ⧸ frattini P) ∧ Monoid.exponent (P ⧸ frattini P) ∣ p := by
  constructor
  · exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
      (commutator_le_frattini hp hP)
  · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (frattini P) q
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact pow_mem_frattini hp hP x

end Work.PGroup
