import Mathlib
import Submission.Work.A7.Defs

namespace Work.AUTA7.A7

open Equiv

/-- A non-identity involution of `A₇` has cycle type `{2, 2}`: a product of two disjoint
transpositions.  Indeed its cycle type consists only of cycles of length `2` (the order divides
`2`, so every cycle length divides `2`, and cycle lengths are at least `2`), and since the
permutation is even the number of `2`-cycles is even, while the support has at most `7` points. -/
theorem cycleType_eq_of_invol (σ : Equiv.Perm (Fin 7)) (hσ : σ * σ = 1) (hσ1 : σ ≠ 1)
    (hsign : Equiv.Perm.sign σ = 1) : σ.cycleType = {2, 2} := by
  have hord : orderOf σ ∣ 2 := by
    rw [orderOf_dvd_iff_pow_eq_one, pow_two]
    exact hσ
  have hall : ∀ n ∈ σ.cycleType, n = 2 := by
    intro n hn
    have h1 : n ∣ orderOf σ := Equiv.Perm.dvd_of_mem_cycleType hn
    have h2 : 2 ≤ n := Equiv.Perm.two_le_of_mem_cycleType hn
    have h3 : n ≤ 2 := Nat.le_of_dvd (by norm_num) (h1.trans hord)
    omega
  have hrep : σ.cycleType = Multiset.replicate σ.cycleType.card 2 :=
    Multiset.eq_replicate_card.mpr hall
  have hsum : σ.cycleType.sum = 2 * σ.cycleType.card := by
    rw [hrep]
    simp [Multiset.sum_replicate, Nat.mul_comm]
  have hcard_le : σ.cycleType.card ≤ 3 := by
    have h := Equiv.Perm.sum_cycleType_le σ
    rw [hsum, Fintype.card_fin] at h
    omega
  have hcard_pos : 0 < σ.cycleType.card := by
    rw [Multiset.card_pos]
    exact fun h => hσ1 (Equiv.Perm.cycleType_eq_zero.mp h)
  have hcard_even : Even σ.cycleType.card := by
    have hpow : (-1 : ℤˣ) ^ (σ.cycleType.sum + σ.cycleType.card) = 1 := by
      rw [← Equiv.Perm.sign_of_cycleType, hsign]
    have h3 : σ.cycleType.sum + σ.cycleType.card = 3 * σ.cycleType.card := by
      rw [hsum]; ring
    rw [h3] at hpow
    rcases Nat.even_mul.mp
      ((neg_one_pow_eq_one_iff_even (R := ℤˣ) (by decide)).mp hpow) with h | h
    · exact absurd h (by decide)
    · exact h
  have hcard : σ.cycleType.card = 2 := by
    obtain ⟨j, hj⟩ := hcard_even
    omega
  rw [hrep, hcard]
  rfl

/-- The alternating group `A₇` acts transitively on its non-identity involutions. -/
theorem InvolutionsConjugate {x y : alternatingGroup (Fin 7)} (hx : x * x = 1)
    (hy : y * y = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1) : IsConj x y := by
  have hxσ : (x : Equiv.Perm (Fin 7)) * (x : Equiv.Perm (Fin 7)) = 1 := by
    have := congrArg (fun z : alternatingGroup (Fin 7) => (z : Equiv.Perm (Fin 7))) hx
    simpa using this
  have hyσ : (y : Equiv.Perm (Fin 7)) * (y : Equiv.Perm (Fin 7)) = 1 := by
    have := congrArg (fun z : alternatingGroup (Fin 7) => (z : Equiv.Perm (Fin 7))) hy
    simpa using this
  have hx1σ : (x : Equiv.Perm (Fin 7)) ≠ 1 := fun h => hx1 (Subtype.ext (by simpa using h))
  have hy1σ : (y : Equiv.Perm (Fin 7)) ≠ 1 := fun h => hy1 (Subtype.ext (by simpa using h))
  have hxsign : Equiv.Perm.sign (x : Equiv.Perm (Fin 7)) = 1 :=
    Equiv.Perm.mem_alternatingGroup.mp x.2
  have hysign : Equiv.Perm.sign (y : Equiv.Perm (Fin 7)) = 1 :=
    Equiv.Perm.mem_alternatingGroup.mp y.2
  have hxcyc := cycleType_eq_of_invol (x : Equiv.Perm (Fin 7)) hxσ hx1σ hxsign
  have hycyc := cycleType_eq_of_invol (y : Equiv.Perm (Fin 7)) hyσ hy1σ hysign
  have hxsupp : (x : Equiv.Perm (Fin 7)).support.card = 4 := by
    rw [← Equiv.Perm.sum_cycleType, hxcyc]
    decide
  refine alternatingGroup.isConj_of ?_ ?_
  · rw [Equiv.Perm.isConj_iff_cycleType_eq, hxcyc, hycyc]
  · rw [hxsupp]
    decide

end Work.AUTA7.A7
