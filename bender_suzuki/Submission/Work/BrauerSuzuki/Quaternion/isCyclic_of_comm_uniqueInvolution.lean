import Mathlib
import Submission.Work.BrauerSuzuki.Defs
import Submission.Work.BrauerSuzuki.Quaternion.two_involutions_of_two_factors
import Submission.Work.BrauerSuzuki.Quaternion.isCyclic_pi_of_subsingleton
import Submission.Work.BrauerSuzuki.Quaternion.even_of_dvd_two_pow

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BrauerSuzuki.Quaternion

open scoped IsMulCommutative

/-- A finite commutative `2`-group with a unique involution is cyclic.

By the structure theorem for finite abelian groups, `P` is a product of cyclic
groups `Multiplicative (ZMod (n i))` with `1 < n i`.  Since `P` is a `2`-group,
each `n i` is a divisor of a power of `2`, hence even.  If there were at least two
factors, taking an element of order `2` in two distinct coordinates would give two
distinct involutions, contradicting uniqueness.  Hence the index type is a
subsingleton and the product of the `ZMod (n i)` is cyclic. -/
theorem isCyclic_of_comm_uniqueInvolution {P : Type*} [Group P] [Finite P]
    (hcomm : IsMulCommutative P) (hP : IsPGroup 2 P)
    (hu : Work.BrauerSuzuki.HasUniqueInvolution P) : IsCyclic P := by
  classical
  letI : IsMulCommutative P := hcomm
  letI : CommGroup P := inferInstance
  obtain ⟨ι, hι, n, hn, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite P
  letI := hι
  have hprod : Nat.card ((i : ι) → Multiplicative (ZMod (n i))) = ∏ i, n i := by
    rw [Nat.card_pi]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Nat.card_congr (Multiplicative.toAdd (α := ZMod (n i))), Nat.card_zmod]
  have hEven : ∀ i, Even (n i) := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hP
    have hcard : Nat.card ((i : ι) → Multiplicative (ZMod (n i))) = 2 ^ m :=
      (Nat.card_congr e.toEquiv).symm.trans hm
    intro i
    refine even_of_dvd_two_pow (m := m) ?_ (hn i)
    rw [← hcard, hprod]
    exact Finset.dvd_prod_of_mem n (Finset.mem_univ i)
  have huniq : ∀ x y : ((i : ι) → Multiplicative (ZMod (n i))),
      orderOf x = 2 → orderOf y = 2 → x = y := by
    obtain ⟨z, _hz2, hzu⟩ := hu
    intro x y hx hy
    have hx' : orderOf (e.symm x) = 2 := by rw [MulEquiv.orderOf_eq]; exact hx
    have hy' : orderOf (e.symm y) = 2 := by rw [MulEquiv.orderOf_eq]; exact hy
    have h1 : e.symm x = e.symm y := (hzu _ hx').trans (hzu _ hy').symm
    exact e.symm.injective h1
  have hsub : Subsingleton ι := by
    by_contra h
    rw [not_subsingleton_iff_nontrivial] at h
    obtain ⟨x, y, hxy, hx, hy⟩ := two_involutions_of_two_factors n hn hEven h
    exact hxy (huniq x y hx hy)
  exact (MulEquiv.isCyclic e).mpr (isCyclic_pi_of_subsingleton n hsub)

end Work.BrauerSuzuki.Quaternion
