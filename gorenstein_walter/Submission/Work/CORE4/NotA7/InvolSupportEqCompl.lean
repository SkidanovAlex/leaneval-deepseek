import Mathlib
import Submission.Work.AUTA7.A7.EvenInvolutionCycleType

namespace Work.CORE4.NotA7

/-- An even involution of `A₇` which is not the identity, viewed as a permutation of `Fin 7`,
has support of cardinality `4`.

Indeed `Z * Z = 1` forces every cycle of `Z` to have length dividing `2`, so `Z` is a product of
disjoint transpositions; the number `k` of them is `cycleType.card`, and `sign Z = (-1)^k`.  Since
`Z ∈ A₇` the sign is `1`, so `k` is even, while `k ≥ 1` (`Z ≠ 1`) and `2 * k = cycleType.sum =
support.card ≤ 7` give `k ≤ 3`; hence `k = 2` and `support.card = 4`.  (This is
`Work.AUTA7.A7.EvenInvolutionCycleType` together with `Equiv.Perm.sum_cycleType`.) -/
theorem involSupportCardFour (z : alternatingGroup (Fin 7)) (hz : z * z = 1) (hz1 : z ≠ 1) :
    (z : Equiv.Perm (Fin 7)).support.card = 4 := by
  have hZZ : (z : Equiv.Perm (Fin 7)) * (z : Equiv.Perm (Fin 7)) = 1 := by
    have h := congrArg (fun x : alternatingGroup (Fin 7) => (x : Equiv.Perm (Fin 7))) hz
    simpa using h
  have hZ1 : (z : Equiv.Perm (Fin 7)) ≠ 1 := fun h => hz1 (Subtype.coe_injective h)
  have hsign : Equiv.Perm.sign (z : Equiv.Perm (Fin 7)) = 1 :=
    Equiv.Perm.mem_alternatingGroup.mp z.2
  have hct : (z : Equiv.Perm (Fin 7)).cycleType = ({2, 2} : Multiset ℕ) :=
    Work.AUTA7.A7.EvenInvolutionCycleType hZZ hZ1 hsign
  have hsum := Equiv.Perm.sum_cycleType (z : Equiv.Perm (Fin 7))
  rw [hct] at hsum
  simpa using hsum.symm

/-- **Support of an involution complementary to the support of a `3`-cycle of `A₇`.**

Let `x ∈ A₇` have support of cardinality `3` (so `x` is a `3`-cycle, or a product of a `3`-cycle
with three fixed points), and let `y ∈ A₇` be an involution (`orderOf y = 2`) fixing every point
of `supp x`.  Then `y` moves exactly the complementary four points:
`supp y = univ \ supp x`.

The point is that `y` is a non-identity even involution, hence a double transposition with
`|supp y| = 4`; as `y` fixes `supp x` pointwise, `supp y` is contained in the complement
`univ \ supp x`, which also has cardinality `7 - 3 = 4`, so the two are equal. -/
theorem InvolSupportEqCompl {x y : alternatingGroup (Fin 7)}
    (hsupp : (x : Equiv.Perm (Fin 7)).support.card = 3)
    (hfix : ∀ a ∈ (x : Equiv.Perm (Fin 7)).support, (y : Equiv.Perm (Fin 7)) a = a)
    (hy : orderOf y = 2) :
    (y : Equiv.Perm (Fin 7)).support = Finset.univ \ (x : Equiv.Perm (Fin 7)).support := by
  -- `y` is a non-identity involution of `A₇`
  have hyy : y * y = 1 := by
    rw [← pow_two, ← hy]
    exact pow_orderOf_eq_one y
  have hy1 : y ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hy
    exact absurd hy (by norm_num)
  -- hence `|supp y| = 4`
  have hsupp4 : (y : Equiv.Perm (Fin 7)).support.card = 4 := involSupportCardFour y hyy hy1
  -- `y` fixes the support of `x`, so `supp y ⊆ univ \ supp x`
  have hsub : (y : Equiv.Perm (Fin 7)).support ⊆
      Finset.univ \ (x : Equiv.Perm (Fin 7)).support := by
    intro a ha
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_univ a, ?_⟩
    intro hax
    exact (Equiv.Perm.mem_support.mp ha) (hfix a hax)
  -- and the complement has cardinality `7 - 3 = 4`
  have hcard : (Finset.univ \ (x : Equiv.Perm (Fin 7)).support).card = 4 := by
    have hcompl : Finset.univ \ (x : Equiv.Perm (Fin 7)).support =
        (x : Equiv.Perm (Fin 7)).supportᶜ := by
      ext a; simp
    rw [hcompl, Finset.card_compl, Fintype.card_fin, hsupp]
  exact Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hsupp4])

end Work.CORE4.NotA7
