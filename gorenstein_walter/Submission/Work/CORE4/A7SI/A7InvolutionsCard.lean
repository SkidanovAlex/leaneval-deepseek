import Mathlib
import Submission.Work.A7.Defs
import Submission.Work.CORE4.A7M.Defs

/-!
# The `105` involutions of `A₇`

The set of elements of order `2` in `A₇` has exactly `105` elements (`= 7!/(4!·2·2)`).

The count is obtained from the classification of involutions of `S₇` by cycle type.  An element
`t` of the alternating group is of order `2` iff it is a nonidentity involution of `S₇`, and being
even its cycle type is neither `{2}` (transposition, odd) nor `{2,2,2}` (product of three
transpositions, odd); hence its cycle type is `{2,2}`, the double transpositions.  Conversely every
double transposition is a nonidentity even involution.  So the elements of order `2` in `A₇` are
exactly the elements of `A₇` of `cycleType` `{2,2}`, and Mathlib's
`AlternatingGroup.card_of_cycleType` gives their number as

`7! / ((7 - 4)! · (2 · 2) · 2!) = 5040 / 48 = 105`.
-/

namespace Work.CORE4.A7SI

open Equiv

/-! ### The classification of even nonidentity involutions of `S₇` -/

/-- An even nonidentity involution of `S₇` is a double transposition, i.e. has cycle type `{2,2}`.

Since `t ^ 2 = 1` every cycle of `t` has length dividing `2`, so `cycleType t` consists only of
`2`'s: `cycleType t = Multiset.replicate k 2` with `k = t.cycleType.card`.  As `t ≠ 1` we have
`k ≥ 1`, and `2 * k = cycleType.sum ≤ 7` gives `k ≤ 3`; the sign formula
`sign t = (-1) ^ (cycleType.sum + cycleType.card) = (-1) ^ (3 * k)` together with `sign t = 1`
forces `k` even, hence `k = 2`. -/
theorem cycleType_eq_two_two_of_even_involution {t : Perm (Fin 7)}
    (ht : t * t = 1) (hne : t ≠ 1) (hsign : Perm.sign t = 1) :
    t.cycleType = ({2,2} : Multiset ℕ) := by
  have h2 : t ^ 2 = 1 := by rw [pow_two]; exact ht
  have hrep : t.cycleType = Multiset.replicate t.cycleType.card 2 :=
    Equiv.Perm.cycleType_of_pow_prime_eq_one (p := 2) h2
  have hpos : 0 < t.cycleType.card := (Equiv.Perm.card_cycleType_pos (σ := t)).mpr hne
  have hsum_le : t.cycleType.sum ≤ 7 := by
    have h := Equiv.Perm.sum_cycleType_le t
    simpa using h
  have hsum_eq : t.cycleType.sum = t.cycleType.card * 2 := by
    rw [hrep, Multiset.sum_replicate, Multiset.card_replicate, nsmul_eq_mul]
    simp
  have hle : t.cycleType.card ≤ 3 := by
    rw [hsum_eq] at hsum_le
    omega
  have hs : (-1 : ℤˣ) ^ (t.cycleType.card * 2 + t.cycleType.card) = 1 := by
    have h := Equiv.Perm.sign_of_cycleType t
    rw [hsign, hsum_eq] at h
    exact h.symm
  have hz : (-1 : ℤ) ^ (t.cycleType.card * 2 + t.cycleType.card) = 1 := by
    simpa using congrArg (Units.val) hs
  have heven' : Even (t.cycleType.card * 2 + t.cycleType.card) :=
    (neg_one_pow_eq_one_iff_even (R := ℤ) (by norm_num)).mp hz
  have heven : Even t.cycleType.card := by
    rw [Nat.even_add] at heven'
    exact heven'.mp ⟨t.cycleType.card, by ring⟩
  obtain ⟨m, hm⟩ := heven
  have hk2 : t.cycleType.card = 2 := by omega
  rw [hrep, hk2]
  rfl

/-- A permutation of `S₇` of cycle type `{2,2}` (a double transposition) is an involution. -/
theorem sq_eq_one_of_cycleType_two_two {g : Perm (Fin 7)}
    (hg : g.cycleType = ({2,2} : Multiset ℕ)) : g * g = 1 := by
  rw [← pow_two, Equiv.Perm.pow_prime_eq_one_iff (σ := g) (p := 2)]
  intro c hc
  rw [hg] at hc
  simpa using hc

/-- A permutation of `S₇` of cycle type `{2,2}` is not the identity. -/
theorem ne_one_of_cycleType_two_two {g : Perm (Fin 7)}
    (hg : g.cycleType = ({2,2} : Multiset ℕ)) : g ≠ 1 := by
  intro h
  rw [h, Equiv.Perm.cycleType_one] at hg
  exact absurd hg (by decide)

/-- A permutation of `S₇` of cycle type `{2,2}` is even. -/
theorem sign_eq_one_of_cycleType_two_two {g : Perm (Fin 7)}
    (hg : g.cycleType = ({2,2} : Multiset ℕ)) : Perm.sign g = 1 := by
  rw [Equiv.Perm.sign_of_cycleType, hg]
  norm_num

/-- An element of `A₇` has order `2` if and only if its cycle type is `{2,2}`
(a double transposition). -/
theorem orderOf_eq_two_iff_cycleType (x : alternatingGroup (Fin 7)) :
    orderOf x = 2 ↔ (x : Perm (Fin 7)).cycleType = ({2,2} : Multiset ℕ) := by
  constructor
  · intro hx
    have hord : orderOf (x : Perm (Fin 7)) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
    have ht : (x : Perm (Fin 7)) * (x : Perm (Fin 7)) = 1 := by
      rw [← pow_two, ← hord, pow_orderOf_eq_one]
    have hne : (x : Perm (Fin 7)) ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hord
      omega
    have hsign : Perm.sign (x : Perm (Fin 7)) = 1 := Equiv.Perm.mem_alternatingGroup.mp x.2
    exact cycleType_eq_two_two_of_even_involution ht hne hsign
  · intro hg
    have hord : orderOf (x : Perm (Fin 7)) = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact sq_eq_one_of_cycleType_two_two hg)
        (ne_one_of_cycleType_two_two hg)
    rw [← Subgroup.orderOf_coe, hord]

/-! ### The count -/

/-- **The alternating group `A₇` has exactly `105` elements of order `2`.** -/
theorem A7InvolutionsCard :
    ({x : alternatingGroup (Fin 7) | orderOf x = 2} : Set (alternatingGroup (Fin 7))).ncard = 105 := by
  show Nat.card {x : alternatingGroup (Fin 7) // orderOf x = 2} = 105
  rw [Nat.card_congr (Equiv.subtypeEquivRight orderOf_eq_two_iff_cycleType)]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [AlternatingGroup.card_of_cycleType (Fin 7) ({2,2} : Multiset ℕ)]
  norm_num

end Work.CORE4.A7SI
