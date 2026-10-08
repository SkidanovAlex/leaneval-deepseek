/-
**All involutions of `SU(3, 2ⁿ)` are conjugate.**

The centralizer of every involution of `SU(3, q)` (`q = 2ⁿ`) is `U · T₁`, of order `q³(q+1)`
(`Submission/PSU3/Centralizer.lean`).  Since `|SU(3,q)| = q³(q²-1)(q³+1)` and the number of
involutions is `(q³+1)(q-1)`, the conjugacy class of a fixed involution has cardinality

  `|SU(3,q)| / q³(q+1) = (q-1)(q³+1)`,

i.e. it exhausts the set of involutions.  Hence the involutions of `SU(3,q)` form a single
conjugacy class --- the fusion of involutions, one of the standard `2`-local data of the
Bender--Suzuki analysis.
-/
import Mathlib
import ChallengeDeps
import Submission.Work.Models.Port.PSU3.Centralizer
import Submission.Work.Models.Port.PSU3.Involutions
import Submission.Work.Models.Port.PSU3.Order
import Submission.Work.Models.Port.Commons.GroupTheory.Conjugation.card_conjClass_eq_index_centralizer
import Submission.Work.Models.Port.Commons.GroupTheory.Conjugation.exists_conj_eq_of_card_conjClass_eq_of_orderOf_eq_two

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

open Matrix LeanEval.GroupTheory.Defs

namespace Submission.PSU3

/-- The arithmetic identity `2^(2n) - 1 = (2^n - 1)(2^n + 1)`. -/
private lemma two_pow_mul_two_sub_one (n : ℕ) :
    (2 : ℕ) ^ (2 * n) - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
  have h : (2 : ℕ) ^ (2 * n) = 2 ^ n * 2 ^ n := by rw [show 2 * n = n + n by ring, pow_add]
  have hkey : (2 ^ n - 1) * (2 ^ n + 1) + 1 = 2 ^ n * 2 ^ n := by
    obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le (Nat.one_le_two_pow (n := n))
    rw [hb]
    have : 1 + b - 1 = b := by omega
    rw [this]; ring
  rw [h, ← Nat.eq_sub_of_add_eq hkey]

/-- **All involutions of `SU(3, 2ⁿ)` are conjugate.** -/
theorem su3_involutions_conj (n : ℕ) (hn : 1 ≤ n) (t s : ↥(SU3 n))
    (ht : orderOf t = 2) (hs : orderOf s = 2) : ∃ z : ↥(SU3 n), z * t * z⁻¹ = s := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set u : ↥(SU3 n) := ⟨suUg n 0 1, suU_le_SU3 n (suUg_zero_mem n 1 (by rw [one_pow]))⟩ with hudef
  have hu : orderOf u = 2 := by
    refine (orderOf_eq_prime_iff (p := 2)).mpr ⟨?_, ?_⟩
    · rw [hudef]
      apply Subtype.ext
      rw [pow_two]
      show suUg n 0 1 * suUg n 0 1 = (1 : GL (Fin 3) (F n))
      rw [suUg_mul_self, zero_pow (show 2 ^ n + 1 ≠ 0 by positivity), suUg_zero]
    · intro h
      have h1 : suUg n 0 1 = (1 : GL (Fin 3) (F n)) := by
        have := congrArg (fun z : ↥(SU3 n) => (z : GL (Fin 3) (F n))) h
        simpa [hudef] using this
      have h2 : ((0 : F n), (1 : F n)) = ((0 : F n), (0 : F n)) :=
        suUg_injective n (h1.trans (suUg_zero n).symm)
      exact one_ne_zero (Prod.ext_iff.mp h2).2
  have hC : Nat.card ↥(Subgroup.centralizer ({u} : Set (↥(SU3 n)))) = 2 ^ (3 * n) * (2 ^ n + 1) := by
    rw [hudef, card_centralizer_suUg_zero n hn (by rw [one_pow]) one_ne_zero]
  have hindex : (Subgroup.centralizer ({u} : Set (↥(SU3 n)))).index =
      (2 ^ n - 1) * (2 ^ (3 * n) + 1) := by
    have h := Subgroup.card_mul_index (Subgroup.centralizer ({u} : Set (↥(SU3 n))))
    rw [hC, card_SU3 n hn] at h
    have hfac : (2 ^ n - 1) * (2 ^ n + 1) = 2 ^ (2 * n) - 1 := (two_pow_mul_two_sub_one n).symm
    have hh : 2 ^ (3 * n) * ((2 ^ n + 1) * (Subgroup.centralizer {u}).index) =
        2 ^ (3 * n) * ((2 ^ (2 * n) - 1) * (2 ^ (3 * n) + 1)) := by
      rw [← mul_assoc, ← mul_assoc]; exact h
    have hkey : 2 ^ (3 * n) * ((2 ^ n + 1) * (Subgroup.centralizer {u}).index) =
        2 ^ (3 * n) * ((2 ^ n + 1) * ((2 ^ n - 1) * (2 ^ (3 * n) + 1))) := by
      rw [hh, ← hfac]; ring
    exact Nat.mul_left_cancel (by positivity : 0 < 2 ^ n + 1)
      (Nat.mul_left_cancel (pow_pos (by norm_num : (0 : ℕ) < 2) (3 * n)) hkey)
  have hcard : Nat.card (ConjClasses.mk u).carrier =
      Nat.card {t : ↥(SU3 n) // orderOf t = 2} := by
    rw [Commons.GroupTheory.Conjugation.card_conjClass_eq_index_centralizer u, hindex,
      card_involutions_SU3 n hn]
    ring
  have hconj : ∀ t : ↥(SU3 n), orderOf t = 2 → ∃ z : ↥(SU3 n), z * u * z⁻¹ = t :=
    Commons.GroupTheory.Conjugation.exists_conj_eq_of_card_conjClass_eq_of_orderOf_eq_two u hu hcard
  obtain ⟨z₁, hz₁⟩ := hconj t ht
  obtain ⟨z₂, hz₂⟩ := hconj s hs
  refine ⟨z₂ * z₁⁻¹, ?_⟩
  rw [← hz₁, ← hz₂]
  group

/-- The involutions of `SU(3, 2ⁿ)` form a single conjugacy class. -/
theorem su3_involutions_single_class (n : ℕ) (hn : 1 ≤ n) {t s : ↥(SU3 n)}
    (ht : orderOf t = 2) (hs : orderOf s = 2) : IsConj t s :=
  isConj_iff.mpr (su3_involutions_conj n hn t s ht hs)

end Submission.PSU3
