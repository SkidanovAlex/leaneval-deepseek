import Mathlib
import Submission.Work.ORHughesFree.Rat.Orbit
import Submission.Work.ORHughesFree.Rat.SourceCore
import Submission.Work.ORHughesFree.Rat.mem_A_mul_ofGroup_iff

/-!
# `Rat.F` as the family of subgroups for which the orbit set of tails is non-empty

The tail bridge `mem_A_mul_ofGroup_iff` and the orbit set `Orbit.T` combine to identify the family
`Rat.F x = {V | x ∈ Rat(V)·U}` with the family of subgroups `V` for which `Orbit.T (supp (Psi x)) V`
is non-empty:

  `V ∈ Rat.F x  ↔  ∃ u : U, ∀ p ∈ supp (Psi x), p * Ugen u ∈ Orbit.NUV V`.

This is the form in which step 3 (the tail analysis: `Orbit.T` grows only by right multiplication by
`V`) feeds the induction of step 4.
-/

namespace Work.ORHughesFree.Rat
namespace Orbit

open Work.ORHughesFree
open Work.ORHughesFree.Rat.WordModel
open Work.ORHughesFree.Rat.FreeProduct

variable {U : Type} [Group U]

/-- **The orbit form of `Rat.F`.** -/
theorem mem_F_iff_T_nonempty (x : RatU U) (V : Subgroup U) :
    V ∈ Rat.F x ↔ (T ((Psi x).coeff.support) V).Nonempty := by
  rw [Work.ORHughesFree.Rat.mem_F_iff']
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u, (mem_A_mul_ofGroup_iff V x u).mp hu⟩
  · rintro ⟨u, hu⟩
    exact ⟨u, (mem_A_mul_ofGroup_iff V x u).mpr hu⟩

end Orbit
end Work.ORHughesFree.Rat
