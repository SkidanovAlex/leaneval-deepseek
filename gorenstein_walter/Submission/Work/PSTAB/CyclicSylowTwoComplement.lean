/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PSTAB area (fundmath3-gorenstein_walter)
-/
import Mathlib
import Submission.Work.PSTAB.Defs

/-!
# The normal `2`-complement of a finite group with cyclic Sylow `2`-subgroups

This file proves `Work.PSTAB.CyclicSylowTwoComplement`: a finite group `D` whose Sylow
`2`-subgroup `P` is cyclic has a normal subgroup `N` of odd order containing every element of
odd order (`N` is the normal `2`-complement, i.e. the set of elements of odd order).

The mathematics is Burnside's normal `p`-complement theorem.  If `|D|` is odd we take
`N = ⊤`.  Otherwise `2` is the smallest prime factor of `|D|`, and a cyclic Sylow subgroup of
the *smallest* prime lies in the centre of its normalizer, so Burnside's transfer theorem gives
a normal complement.  This is available in Mathlib as `IsCyclic.isComplement'`
(`Mathlib.GroupTheory.Transfer`), which produces the kernel `N` of the transfer map `D →* P`
together with `N.IsComplement' P`.  From that we read off:
* `N` is normal (a kernel);
* `Nat.card N = P.index` is odd (`P` is a Sylow `2`-subgroup);
* the quotient `D ⧸ N ≃* P` is a `2`-group, so an element `x` of odd order has trivial image.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.PSTAB

/-- **Existence of the normal `2`-complement.**  Every finite group with a cyclic Sylow
`2`-subgroup has a normal subgroup `N` of odd order which contains every element of odd order.

For odd `|D|` take `N = ⊤`.  For even `|D|`, `2 = (Nat.card D).minFac` and Mathlib's
`IsCyclic.isComplement'` (Burnside's transfer theorem for a cyclic Sylow subgroup of the
smallest prime, `Mathlib/GroupTheory/Transfer.lean`) exhibits the transfer kernel
`N = (transferSylow P _).ker` as a complement of `P`; being a kernel it is normal, its order is
`P.index` (odd), and the quotient `D ⧸ N ≃* P` is a `2`-group, so any odd order element maps
to `1`. -/
theorem CyclicSylowTwoComplement {D : Type*} [Group D] [Finite D] (P : Sylow 2 D)
    (hP : IsCyclic ↥(P : Subgroup D)) :
    ∃ N : Subgroup D, N.Normal ∧ Odd (Nat.card N) ∧ (∀ x : D, ¬ 2 ∣ orderOf x → x ∈ N) := by
  by_cases hodd : Odd (Nat.card D)
  · -- Odd order: the whole group is the normal `2`-complement.
    exact ⟨⊤, inferInstance, by simpa using hodd, fun x _ => Subgroup.mem_top x⟩
  · -- Even order: `2` is the smallest prime factor of `|D|`.
    have h2dvd : 2 ∣ Nat.card D := by
      rw [← even_iff_two_dvd, ← Nat.not_odd_iff_even]
      exact hodd
    have hmin : (Nat.card D).minFac = 2 := (Nat.minFac_eq_two_iff _).mpr h2dvd
    let N : Subgroup D := (MonoidHom.transferSylow P (hP.normalizer_le_centralizer hmin)).ker
    have hcomp : N.IsComplement' (P : Subgroup D) :=
      IsCyclic.isComplement' (G := D) (p := 2) hmin hP
    haveI hNnorm : N.Normal := MonoidHom.normal_ker _
    -- `Nat.card N = P.index`, which is odd because `P` is a Sylow `2`-subgroup.
    have hOddN : Odd (Nat.card N) := by
      rw [← Subgroup.IsComplement'.index_eq_card hcomp]
      exact Nat.not_even_iff_odd.mp (by rw [even_iff_two_dvd]; exact P.not_dvd_index)
    -- `D ⧸ N ≃* P` is a `2`-group.
    have hiso : D ⧸ N ≃* ↥(P : Subgroup D) :=
      Subgroup.IsComplement'.QuotientMulEquiv hcomp.symm
    obtain ⟨k, hk⟩ := P.2.exists_card_eq
    have hcard : Nat.card (D ⧸ N) = 2 ^ k := by
      rw [Nat.card_congr hiso.toEquiv, hk]
    refine ⟨N, hNnorm, hOddN, ?_⟩
    intro x hx
    -- The image of `x` in `D ⧸ N ≃* P` has odd order dividing `2 ^ k`, hence is trivial.
    have h1 : orderOf (QuotientGroup.mk' N x) ∣ orderOf x := orderOf_map_dvd _ x
    have h2 : orderOf (QuotientGroup.mk' N x) ∣ Nat.card (D ⧸ N) := orderOf_dvd_natCard _
    have h2k : orderOf (QuotientGroup.mk' N x) ∣ 2 ^ k := hcard ▸ h2
    have hcop2 : (2 ^ k).Coprime (orderOf x) := by
      have h : (2 : ℕ).Coprime (orderOf x) :=
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hx
      exact h.pow_left k
    have hcop : (orderOf (QuotientGroup.mk' N x)).Coprime (orderOf x) :=
      Nat.Coprime.coprime_dvd_left h2k hcop2
    have hone : orderOf (QuotientGroup.mk' N x) = 1 := Nat.Coprime.eq_one_of_dvd hcop h1
    have heq : QuotientGroup.mk' N x = 1 := orderOf_eq_one_iff.mp hone
    rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker]
    exact heq

end Work.PSTAB
