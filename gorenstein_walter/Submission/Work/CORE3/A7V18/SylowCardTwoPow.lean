import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.ASM.oddCore_odd

/-!
# The `2`-part of `M / O(M)` for `M ⊇ S`

Let `B : BenderSetup G`, so that `S = B.S` is a Sylow `2`-subgroup of `G`, and let `M ≤ G`
contain `S`.  Then `S` is a Sylow `2`-subgroup of `M`, and since `O(M)` has odd order,

  `|S| = 2 ^ v₂(|M / O(M)|)`.

The proof only compares the exponent of `2`:
* `|S| = 2 ^ v₂(|S|)` because `S` is a `2`-group;
* `|M| = |M / O(M)| · |O(M)|` with `O(M)` of odd order, so `v₂(|M|) = v₂(|M / O(M)|)`;
* `|M| = [M : S] · |S|` and `[M : S] ∣ [G : S]` is odd, so `v₂(|M|) = v₂(|S|)`.
-/

namespace Work.CORE3.A7V18

open Subgroup in
theorem SylowCardTwoPow {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G) (M : Subgroup G) (hSM : (B.S : Subgroup G) ≤ M) : Nat.card (B.S : Subgroup G) = 2 ^ (Nat.card (↥M ⧸ Work.GW2.oddCore ↥M)).factorization 2 := by
  -- `|S|` is a power of `2`
  obtain ⟨n, hn⟩ := B.S.isPGroup'.exists_card_eq
  have hsne : Nat.card (B.S : Subgroup G) ≠ 0 :=
    Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩
  have hqne : Nat.card (↥M ⧸ Work.GW2.oddCore ↥M) ≠ 0 :=
    Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩
  have hone : Nat.card (Work.GW2.oddCore ↥M) ≠ 0 :=
    Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩
  -- `[M : S] = S.relIndex M` divides `[G : S]`, which is odd
  have hdvd : (B.S : Subgroup G).relIndex M ∣ (B.S : Subgroup G).index :=
    Subgroup.relIndex_dvd_index_of_le hSM
  have hnot2 : ¬ 2 ∣ (B.S : Subgroup G).relIndex M :=
    fun h => B.S.not_dvd_index (h.trans hdvd)
  have hine : (B.S : Subgroup G).relIndex M ≠ 0 := by
    intro h; rw [h] at hnot2; exact hnot2 (dvd_zero 2)
  -- the two factorizations of `|M|`
  have h1 : Nat.card M
      = Nat.card (↥M ⧸ Work.GW2.oddCore ↥M) * Nat.card (Work.GW2.oddCore ↥M) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (Work.GW2.oddCore ↥M)
  have h2 : Nat.card M = (B.S : Subgroup G).relIndex M * Nat.card (B.S : Subgroup G) := by
    rw [← Subgroup.relIndex_mul_card (B.S : Subgroup G) M, inf_eq_left.mpr hSM]
  have hMfac1 : (Nat.card M).factorization 2
      = (Nat.card (↥M ⧸ Work.GW2.oddCore ↥M)).factorization 2 := by
    rw [h1, Nat.factorization_mul hqne hone, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (Work.ASM.oddCore_odd ↥M).not_two_dvd_nat, add_zero]
  have hMfac2 : (Nat.card M).factorization 2
      = (Nat.card (B.S : Subgroup G)).factorization 2 := by
    rw [h2, Nat.factorization_mul hine hsne, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hnot2, zero_add]
  have key : (Nat.card (↥M ⧸ Work.GW2.oddCore ↥M)).factorization 2
      = (Nat.card (B.S : Subgroup G)).factorization 2 := by
    rw [← hMfac1, hMfac2]
  rw [key, hn, Nat.factorization_pow_self Nat.prime_two]

end Work.CORE3.A7V18
