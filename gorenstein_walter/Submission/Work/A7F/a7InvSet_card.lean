/-
Area A7F: the number of nonidentity involutions of `A₇` is `105`.

The count is obtained from the classification of involutions in `S₇` by cycle type:
a nonidentity permutation `t` with `t ^ 2 = 1` is a product of disjoint transpositions, so its
`cycleType` is a multiset of `2`'s; being even forces the number of transpositions to be even,
hence exactly `2`, i.e. `t` is a double transposition.  Conversely every permutation of cycle
type `{2,2}` is an even involution distinct from `1`.  Thus the nonidentity involutions of `A₇`
are in bijection with the permutations of `S₇` of cycle type `{2,2}`, whose cardinality is
Mathlib's `Equiv.Perm.card_of_cycleType`:
`7! / ((7 - 4)! · (2 · 2) · 2!) = 5040 / 48 = 105`.
-/
import Mathlib
import Submission.Work.A7F.Defs

open scoped MatrixGroups

namespace Work.A7F

open Equiv

/-- An even involution of `S₇` that is not the identity is a double transposition.

Since `t ^ 2 = 1`, every cycle of `t` has length dividing `2`, so `cycleType t` consists only of
`2`'s: `cycleType t = Multiset.replicate k 2` where `k = Multiset.card t.cycleType`.  Because
`t ≠ 1` we have `k ≥ 1`, and `2 * k = cycleType.sum ≤ 7` gives `k ≤ 3`; the sign formula
`sign t = (-1) ^ (cycleType.sum + cycleType.card) = (-1) ^ (3 * k)` together with `sign t = 1`
forces `k` even.  Hence `k = 2`. -/
theorem a7InvSet_cycleType_eq_two_two {t : Perm (Fin 7)} (ht : t * t = 1) (hne : t ≠ 1)
    (hsign : Perm.sign t = 1) : t.cycleType = ({2,2} : Multiset ℕ) := by
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
theorem a7InvSet_sq_eq_one {g : Perm (Fin 7)} (hg : g.cycleType = ({2,2} : Multiset ℕ)) :
    g * g = 1 := by
  rw [← pow_two, Equiv.Perm.pow_prime_eq_one_iff (σ := g) (p := 2)]
  intro c hc
  rw [hg] at hc
  simpa using hc

/-- A permutation of `S₇` of cycle type `{2,2}` is not the identity. -/
theorem a7InvSet_ne_one {g : Perm (Fin 7)} (hg : g.cycleType = ({2,2} : Multiset ℕ)) :
    g ≠ 1 := by
  intro h
  rw [h, Equiv.Perm.cycleType_one] at hg
  exact absurd hg (by decide)

/-- A permutation of `S₇` of cycle type `{2,2}` is even. -/
theorem a7InvSet_sign_eq_one {g : Perm (Fin 7)} (hg : g.cycleType = ({2,2} : Multiset ℕ)) :
    Perm.sign g = 1 := by
  rw [Equiv.Perm.sign_of_cycleType, hg]
  norm_num

/-- The nonidentity involutions of `A₇` are in bijection with the permutations of `S₇` of
cycle type `{2,2}` (the double transpositions). -/
def a7InvSet_equiv :
    {t : alternatingGroup (Fin 7) // t ≠ 1 ∧ t * t = 1} ≃
      {g : Perm (Fin 7) // g.cycleType = ({2,2} : Multiset ℕ)} where
  toFun t := ⟨(t.1 : Perm (Fin 7)),
    a7InvSet_cycleType_eq_two_two
      (by simpa using congrArg (Subtype.val) t.2.2)
      (fun h => t.2.1 (Subtype.ext h))
      ((Equiv.Perm.mem_alternatingGroup (f := (t.1 : Perm (Fin 7)))).mp t.1.2)⟩
  invFun g :=
    ⟨⟨g.1, (Equiv.Perm.mem_alternatingGroup (f := g.1)).mpr
        (a7InvSet_sign_eq_one g.2)⟩,
      ⟨fun h => a7InvSet_ne_one g.2 (by simpa using congrArg (Subtype.val) h),
       by apply Subtype.ext; simpa using a7InvSet_sq_eq_one g.2⟩⟩
  left_inv t := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv g := by
    apply Subtype.ext
    rfl

/-- **The alternating group `A₇` has exactly `105` nonidentity involutions.** -/
theorem a7InvSet_card : a7InvSet.card = 105 := by
  have hA : a7InvSet.card =
      Nat.card {t : alternatingGroup (Fin 7) // t ≠ 1 ∧ t * t = 1} := by
    rw [a7InvSet]
    rw [← Fintype.card_subtype (fun t : alternatingGroup (Fin 7) => t ≠ 1 ∧ t * t = 1)]
    rw [Nat.card_eq_fintype_card]
  rw [hA, Nat.card_congr a7InvSet_equiv]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Equiv.Perm.card_of_cycleType]
  norm_num

end Work.A7F
