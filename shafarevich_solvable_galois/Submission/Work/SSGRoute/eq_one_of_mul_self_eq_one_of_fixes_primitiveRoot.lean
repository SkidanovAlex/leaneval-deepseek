import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.TwoTorsion.add_mem_normSet
import Submission.Work.SSGRoute.TwoTorsion.neg_one_notMem_normSet
import Submission.Work.SSGRoute.TwoTorsion.rootOfUnity_eq_pm_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- **An order-two ring automorphism of an algebraically closed field of characteristic `0` cannot fix
a primitive `p`-th root of unity for an odd prime `p`.**  Consequence (used by the `z`-construction of
Schmidt--Wingberg §4): for a number field `k`, an algebraic closure `Ω`, and any intermediate field
`K ⊆ Ω` containing a primitive `p`-th root of unity with `p` odd, the Galois group `Gal(Ω/K)` has no
element of order two -- so the "vanishing on the involutions" clause
(`∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → z c = 0`) of `Work.SSGRoute.shafarevich_z_construction` and of
`Work.SSGRoute.HasZData` is *automatic* for odd `p` (it reduces to `z 1 = 0`).

The proof is the Artin--Schreier argument already carried out in the workspace
(`Submission/Work/SSGRoute/TwoTorsion/`, applied to `ℚ̄` with `μ_{p^{i+1}} ⊆ K`, `i ≥ 1`, in
`Work.SSGRoute.no_two_torsion_fixingSubgroup`): the norm set of the involution gives an ordering of
the fixed field under which every root of unity fixed by the involution is `±1`; and `ζ = ±1` is
excluded because `IsPrimitiveRoot ζ p` with `p` odd rules out both `1` and `-1`.  Note
`neg_one_notMem_normSet` needs `c ≠ 1`, so the proof is a `by_contra`. -/
theorem eq_one_of_mul_self_eq_one_of_fixes_primitiveRoot {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    [CharZero Ω] (c : Ω ≃+* Ω) (hc : c * c = 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : Ω} (hζ : IsPrimitiveRoot ζ p) (hfix : c ζ = ζ) :
    c = 1 := by
  by_contra hc1
  -- If `c` is a non-trivial involution, `-1` is not a norm for it ...
  have hneg : (-1 : Ω) ∉ TwoTorsion.normSet c :=
    TwoTorsion.neg_one_notMem_normSet c hc hc1
  -- ... so the norm set is closed under addition and provides an ordering of the fixed field.
  have hadd : ∀ w ∈ TwoTorsion.normSet c, ∀ w' ∈ TwoTorsion.normSet c,
      w + w' ∈ TwoTorsion.normSet c :=
    fun w hw w' hw' => TwoTorsion.add_mem_normSet c hc hneg hw hw'
  -- Hence every root of unity fixed by `c` is `±1`.
  have hres : ζ = 1 ∨ ζ = -1 :=
    TwoTorsion.rootOfUnity_eq_pm_one c hneg hadd hp.one_le hfix hζ.pow_eq_one
  rcases hres with h | h
  · -- `ζ = 1` contradicts primitivity, as `p ≠ 1`.
    exact hζ.ne_one hp.one_lt h
  · -- `ζ = -1` would force `p = orderOf (-1) = 2`, contradicting `p ≠ 2`.
    rw [h] at hζ
    have hord : p = orderOf (-1 : Ω) := hζ.eq_orderOf
    rw [orderOf_neg_one, ringChar.eq_zero] at hord
    norm_num at hord
    exact hp2 hord

end Work.SSGRoute
