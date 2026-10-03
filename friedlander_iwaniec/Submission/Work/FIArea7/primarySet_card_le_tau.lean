import Mathlib
import Submission.Work.FIArea7.prop232Defs
import Submission.Commons.NumberTheory.GaussianInt.two_squares_repr_count
import Submission.Commons.NumberTheory.GaussianInt.two_squares_repr_count_le_tau_of_pos
import Submission.Commons.NumberTheory.GaussianInt.primary_associate_exists_unique
import Submission.Work.FIArea7.mk_injOn_primarySet

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## The count of primary elements of norm `M`

`primarySet M` is a set of pairwise **non-associate** Gaussian integers
(`mk_injOn_primarySet`), so its cardinality is at most the number `A M` of associate classes of
elements of norm `M` (`Commons.NumberTheory.GaussianInt.A`, the `ncard` of `Xset M`), and
`A M ≤ τ(M)` by the classical two-squares/divisor bound (`A_le_card_divisors`). -/

/-- `A M ≤ τ(M) = M.divisors.card` for `M ≥ 1`: the number of *ordered* representations
`M = x² + y²` is `4 · A M` (`targetF_card_eq_four_mul_A`) and at most `4 · τ(M)`
(`two_squares_repr_count_le_tau_of_pos`), so the factor `4` cancels. -/
lemma A_le_card_divisors (M : ℕ) (hM : 1 ≤ M) :
    Commons.NumberTheory.GaussianInt.A M ≤ M.divisors.card := by
  have h1 : (Commons.NumberTheory.GaussianInt.targetF M).card
      = 4 * Commons.NumberTheory.GaussianInt.A M :=
    Commons.NumberTheory.GaussianInt.targetF_card_eq_four_mul_A M hM
  have h2 : ((Commons.NumberTheory.GaussianInt.targetF M).card : ℤ)
      ≤ 4 * (M.divisors.card : ℤ) :=
    Commons.NumberTheory.GaussianInt.two_squares_repr_count_le_tau_of_pos M hM
  have h3 : 4 * Commons.NumberTheory.GaussianInt.A M ≤ 4 * M.divisors.card := by
    rw [← h1]
    exact_mod_cast h2
  exact Nat.le_of_mul_le_mul_left h3 (by norm_num)

/-- There is no primary Gaussian integer of norm `0` (`0` is not primary: its real part is even),
so `primarySet 0` is empty. -/
lemma primarySet_zero_card : (primarySet 0).card = 0 := by
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro z hz
  obtain ⟨hp, hg⟩ := mem_primarySet.mp hz
  have hodd := odd_gnorm_of_isPrimary hp
  rw [hg] at hodd
  obtain ⟨k, hk⟩ := hodd
  omega

/-- `(primarySet M).card ≤ A M`: two distinct primary elements of the same norm are
non-associate, so `Associates.mk` is injective on `primarySet M` and its image lies in the set
`Xset M` of associate classes of norm `M`. -/
lemma primarySet_card_le_A (M : ℕ) :
    (primarySet M).card ≤ Commons.NumberTheory.GaussianInt.A M := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM
    rw [primarySet_zero_card]
    exact Nat.zero_le _
  · have hsub : (Associates.mk '' ((primarySet M) : Set GaussianInt))
        ⊆ Commons.NumberTheory.GaussianInt.Xset M := by
      rintro κ ⟨z, hz, rfl⟩
      show Commons.NumberTheory.GaussianInt.nc (Associates.mk z) = M
      rw [Commons.NumberTheory.GaussianInt.nc_mk]
      exact gnorm_of_mem_primarySet hz
    have hcard : (primarySet M).card
        = (Associates.mk '' ((primarySet M) : Set GaussianInt)).ncard := by
      rw [Set.InjOn.ncard_image (mk_injOn_primarySet M), Set.ncard_coe_finset]
    have hfin : (Commons.NumberTheory.GaussianInt.Xset M).Finite := by
      rw [Commons.NumberTheory.GaussianInt.Xset_eq_image M hM]
      exact Set.Finite.image _ (Commons.NumberTheory.GaussianInt.elemF M).finite_toSet
    rw [hcard]
    calc (Associates.mk '' ((primarySet M) : Set GaussianInt)).ncard
        ≤ (Commons.NumberTheory.GaussianInt.Xset M).ncard := Set.ncard_le_ncard hsub hfin
      _ = Commons.NumberTheory.GaussianInt.A M :=
          Commons.NumberTheory.GaussianInt.Xset_ncard M hM

/-- The number of primary Gaussian integers of norm `M` is at most `τ(M) = M.divisors.card`.

Proof route: distinct primary elements of the same norm are non-associate
(`Commons.NumberTheory.GaussianInt.unit_eq_one_of_primary`), so `(primarySet M).card` is at most
the number `A M` of associate classes of Gaussian integers of norm `M`
(`Commons.NumberTheory.GaussianInt.A`), which is multiplicative on coprime arguments
(`...A_mul_of_coprime`) with `A (p^a) = a+1`, `1`, `1`/`0` for `p ≡ 1 (mod 4)`, `p = 2`,
`p ≡ 3 (mod 4)` (`...A_prime_pow`); hence `A M ≤ Π_p (v_p M + 1) = τ(M)`.  (Alternatively bound
`(primarySet M).card ≤ A M` via `Associates.mk` and `Set.ncard`.) -/
theorem primarySet_card_le_tau (M : ℕ) :
    (Work.FIArea7.primarySet M).card ≤ M.divisors.card := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM
    rw [primarySet_zero_card]
    exact Nat.zero_le _
  · exact (primarySet_card_le_A M).trans (A_le_card_divisors M hM)

end

end Work.FIArea7
