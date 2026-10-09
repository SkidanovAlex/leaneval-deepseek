/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `G_1` is pro-`p` and `G_0/G_1` has order prime to `p`

Two consequences of the embeddings of `NK.RamificationDeep.QuotientEmbed` and
`NK.RamificationDeep.UnitMap`:

* `#(G_i/G_{i+1}) ∣ q` for `i ≥ 1`, where `q = #(A/𝔪_A)`; hence if `q = p^f` and the filtration
  terminates (`G_N = ⊥` for some `N`) then `#G_1` is a power of `p`, i.e. `G_1` is a pro-`p`
  group (`isProP_ramificationSubgroup_one`);
* `#(G_0/G_1) ∣ q - 1`, hence `p ∤ #(G_0/G_1)` (`coprime_quotient_zero`).

Together these are precisely the two inputs of
`NK.Ramification.isWildInertia_ramificationSubgroup_one`, so that theorem can now be invoked
with no hypotheses beyond `q = p^f`, `p` prime and the termination of the filtration: see
`isWildInertia_ramificationSubgroup_one_of_residue` below.  For a finite Galois extension of
`p`-adic fields the filtration always terminates (`NK.Ramification.exists_ramificationSubgroup_eq_bot`)
and the residue field has `p^f` elements, so in that setting `G_1` *is* the wild inertia.
-/
import Mathlib
import Submission.NK.RamificationDeep.UnitMap
import Submission.NK.Ramification.isWildInertia_ramificationSubgroup_one
import Submission.NK.Ramification.isProP_of_natCard_eq_prime_pow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

open scoped Pointwise

namespace NK.RamificationDeep

universe u

noncomputable section

variable {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]
variable {A : ValuationSubring L} [IsDiscreteValuationRing A] {π : A} {E : IntermediateField K L}

/-! ## `#G_k ∣ q^N` when `G_{k+N} = ⊥` -/

/-- **The order of `G_k` is a power of the residue cardinality** as soon as the filtration has
become trivial: if `G_{k+N} = ⊥` then `#G_k ∣ q^N`, where `q = #(A/𝔪_A)`.

This is the induction along the filtration using `#(G_i/G_{i+1}) ∣ q` for `i ≥ 1`
(`NK.RamificationDeep.natCard_quotient_dvd_residue`). -/
theorem natCard_ramificationSubgroup_dvd_pow (D : UniformizerData (K := K) A π E) :
    ∀ (N k : ℕ), 1 ≤ k →
      NK.Ramification.ramificationSubgroup (K := K) A (k + N) = ⊥ →
      Nat.card ↥(NK.Ramification.ramificationSubgroup (K := K) A k) ∣
        (Nat.card (A ⧸ IsLocalRing.maximalIdeal A)) ^ N := by
  intro N
  induction N with
  | zero =>
      intro k _ hbot
      rw [Nat.add_zero] at hbot
      rw [hbot, pow_zero]
      have : Nat.card ↥(⊥ : Subgroup (A.decompositionSubgroup K)) = 1 := Nat.card_unique
      rw [this]
  | succ N ih =>
      intro k hk hbot
      -- `G_k ⊵ G_{k+1}`, `#G_k = #G_{k+1} · #(G_k/G_{k+1})` and both factors divide.
      have hle : NK.Ramification.ramificationSubgroup (K := K) A (k + 1) ≤
          NK.Ramification.ramificationSubgroup (K := K) A k :=
        NK.Ramification.ramificationSubgroup_antitone (K := K) A (Nat.le_succ k)
      have hcard : Nat.card ↥((NK.Ramification.ramificationSubgroup (K := K) A
            (k + 1)).subgroupOf (NK.Ramification.ramificationSubgroup (K := K) A k)) =
          Nat.card ↥(NK.Ramification.ramificationSubgroup (K := K) A (k + 1)) :=
        Nat.card_congr
          { toFun := fun x => ⟨x.1.1, x.2⟩
            invFun := fun y => ⟨⟨y.1, hle y.2⟩, y.2⟩
            left_inv := fun x => by ext; rfl
            right_inv := fun y => by ext; rfl }
      have hrec := Subgroup.card_mul_index
        ((NK.Ramification.ramificationSubgroup (K := K) A (k + 1)).subgroupOf
          (NK.Ramification.ramificationSubgroup (K := K) A k))
      rw [hcard, Subgroup.index_eq_card] at hrec
      have hdvd : Nat.card (↥(NK.Ramification.ramificationSubgroup (K := K) A k) ⧸
            (NK.Ramification.ramificationSubgroup (K := K) A (k + 1)).subgroupOf
              (NK.Ramification.ramificationSubgroup (K := K) A k)) ∣
          Nat.card (A ⧸ IsLocalRing.maximalIdeal A) :=
        natCard_quotient_dvd_residue (K := K) D hk
      have hIH := ih (k + 1) (by omega) (by rw [show k + 1 + N = k + (N + 1) by omega]; exact hbot)
      rw [pow_succ]
      rw [← hrec]
      exact mul_dvd_mul hIH hdvd

/-- **`#G_1` is a power of `p`** when the residue field has `p^f` elements. -/
theorem exists_natCard_one_eq_prime_pow (D : UniformizerData (K := K) A π E) {p f N : ℕ}
    (hp : p.Prime) (hq : Nat.card (A ⧸ IsLocalRing.maximalIdeal A) = p ^ f)
    (hbot : NK.Ramification.ramificationSubgroup (K := K) A (1 + N) = ⊥) :
    ∃ j : ℕ, Nat.card ↥(NK.Ramification.ramificationSubgroup (K := K) A 1) = p ^ j := by
  have hdvd := natCard_ramificationSubgroup_dvd_pow (K := K) D N 1 le_rfl hbot
  rw [hq, ← pow_mul] at hdvd
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  exact ⟨j, hj⟩

/-- **`G_1` is a pro-`p` group** once the residue field has `p^f` elements (`f` arbitrary) and the
ramification filtration terminates. -/
theorem isProP_ramificationSubgroup_one (D : UniformizerData (K := K) A π E) [Finite ↥(A.decompositionSubgroup K)]
    {p f N : ℕ} (hp : p.Prime) (hq : Nat.card (A ⧸ IsLocalRing.maximalIdeal A) = p ^ f)
    (hbot : NK.Ramification.ramificationSubgroup (K := K) A (1 + N) = ⊥) :
    NK.LocalTame.IsProP p ↥(NK.Ramification.ramificationSubgroup (K := K) A 1) :=
  NK.Ramification.isProP_of_natCard_eq_prime_pow hp
    (exists_natCard_one_eq_prime_pow (K := K) D hp hq hbot)

/-! ## `G_0/G_1` has order prime to `p` -/

/-- `p` does not divide `p^f - 1`. -/
theorem prime_not_dvd_pow_sub_one {p f : ℕ} (hp : p.Prime) (hf : 0 < f) : ¬ p ∣ p ^ f - 1 := by
  intro h
  have hle : 1 ≤ p ^ f := Nat.one_le_pow f p (le_of_lt hp.one_lt)
  have hpf : p ∣ p ^ f := dvd_pow_self p (Nat.pos_iff_ne_zero.mp hf)
  have h1 : p ∣ p ^ f - (p ^ f - 1) := Nat.dvd_sub hpf h
  rw [show p ^ f - (p ^ f - 1) = 1 from by omega] at h1
  exact hp.not_dvd_one h1

/-- **`p` is coprime to `#(G_0/G_1)`** when the residue field has `p^f` elements: this is the
embedding `G_0/G_1 ↪ (A/𝔪_A)^×` and `#(A/𝔪_A)^× = p^f - 1`. -/
theorem coprime_natCard_quotient_zero (D : UniformizerData (K := K) A π E) {p f : ℕ}
    (hp : p.Prime) (hf : 0 < f)
    (hunits : Nat.card ((A ⧸ IsLocalRing.maximalIdeal A)ˣ) = p ^ f - 1) :
    Nat.Coprime p
      (Nat.card (↥(NK.Ramification.ramificationSubgroup (K := K) A 0) ⧸
        (NK.Ramification.ramificationSubgroup (K := K) A 1).subgroupOf
          (NK.Ramification.ramificationSubgroup (K := K) A 0))) := by
  have hdvd := natCard_quotient_zero_dvd_units (K := K) D
  rw [hunits] at hdvd
  exact (hp.coprime_iff_not_dvd).mpr fun h =>
    prime_not_dvd_pow_sub_one hp hf (h.trans hdvd)

/-! ## The wild inertia -/

/-- **`G_1` is the wild inertia subgroup of `G_0`** in the sense of `NK.LocalTame.IsWildInertia`,
under the sole additional hypotheses that the residue field has `p^f` elements and that the
filtration terminates.

(For a finite Galois extension of `p`-adic fields the latter is
`NK.Ramification.exists_ramificationSubgroup_eq_bot` and the former is a computation of the
residue field; in that setting this theorem is unconditional.) -/
theorem isWildInertia_ramificationSubgroup_one_of_residue (D : UniformizerData (K := K) A π E)
    [Finite ↥(A.decompositionSubgroup K)] {p f N : ℕ} (hp : p.Prime) (hf : 0 < f)
    (hq : Nat.card (A ⧸ IsLocalRing.maximalIdeal A) = p ^ f)
    (hunits : Nat.card ((A ⧸ IsLocalRing.maximalIdeal A)ˣ) = p ^ f - 1)
    (hbot : NK.Ramification.ramificationSubgroup (K := K) A (1 + N) = ⊥) :
    NK.LocalTame.IsWildInertia p
      ↥(NK.Ramification.ramificationSubgroup (K := K) A 0)
      ((NK.Ramification.ramificationSubgroup (K := K) A 1).subgroupOf
        (NK.Ramification.ramificationSubgroup (K := K) A 0)) := by
  have hpro : NK.LocalTame.IsProP p
      ↥((NK.Ramification.ramificationSubgroup (K := K) A 1).subgroupOf
        (NK.Ramification.ramificationSubgroup (K := K) A 0)) :=
    (NK.LocalTame.isProP_congr
      (Subgroup.subgroupOfEquivOfLe
        (NK.Ramification.ramificationSubgroup_antitone (K := K) A (Nat.zero_le 1))) p).mpr
      (isProP_ramificationSubgroup_one (K := K) D hp hq hbot)
  exact NK.Ramification.isWildInertia_ramificationSubgroup_one A hp hpro
    (coprime_natCard_quotient_zero (K := K) D hp hf hunits)

end

end NK.RamificationDeep
