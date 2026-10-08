/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area BSW, `Work.BSW`)

# Area BSW, Bender §2: the involution-pair class function `i`

`Work.BSW.invPairCount G x` is Bender's `i(x)`: the number of ordered pairs `(u, v)` of
involutions with `u * v = x` (`REFS/bender1974_bsw.txt`, p. 229).  This file packages it as a
complex class function (`Work.BSW.Order.invPairCF`), defined through the character formula
`i(x) = |G| / |C_G(t)|² · Σ_χ χ(t)² χ(x) / χ(1)` (`Work.BSW.Char.invPairCount_eq_sum_characters`,
Gorenstein 9.4.21) so that it is manifestly a class function, and proves that it agrees with the
counting definition (`invPairCF_apply`), together with the values on `K` used by Bender's §2
(p. 231):

* `i(1) = |G : C_G(t)|` (the number of involutions),
* `i(t) = k` (the pair count; the involution count `iFn G t` is `k + 1`),
* `i(x) = k` for `x ∈ K ∖ {1, t}`.
-/
import Mathlib
import Submission.Work.BSW.Vocab
import Submission.Work.BSW.Basic
import Submission.Work.BSW.Api.card_sup_zpowers
import Submission.Work.BSW.Api.normalizer_K_eq
import Submission.Work.BSW.Api.mem_centralizer_iff
import Submission.Work.BSW.Api.ncard_involutions_eq_index
import Submission.Work.BSW.Char.Alpha
import Submission.Work.BSW.Char.isTISubset_Kdiff
import Submission.Work.BSW.Char.iFn_eq_invPairCount
import Submission.Work.BSW.Char.iFn_eq_card_of_mem_K
import Submission.Work.BSW.Char.iFn_t
import Submission.Work.BSW.Char.invPairCount_eq_sum_characters
import Submission.OddOrder.GroupTheory.RepresentationTheory.CharacterProduct

namespace Work.BSW.Order

open Subgroup Work.GW2 OddOrder.RepresentationTheory

variable {G : Type} [Group G] [Finite G]

section InvPairCF

/-- Bender's `i` as a complex class function, defined through the character formula: the number
of ordered pairs of involutions with product `x`. -/
noncomputable def invPairCF (G : Type) [Group G] [Finite G] (t : G) : ClassFunction G ℂ :=
  ((Nat.card G : ℂ) / (Nat.card (Subgroup.centralizer ({t} : Set G)) : ℂ) ^ 2) •
    (∑ χ : IrreducibleCharacter G,
      (((χ : ClassFunction G ℂ) t) ^ 2 / (χ : ClassFunction G ℂ) 1) •
        (χ : ClassFunction G ℂ))

@[simp] theorem invPairCF_apply_def (t : G) (x : G) :
    invPairCF G t x =
      ((Nat.card G : ℂ) / (Nat.card (Subgroup.centralizer ({t} : Set G)) : ℂ) ^ 2) *
        (∑ χ : IrreducibleCharacter G,
          (((χ : ClassFunction G ℂ) t) ^ 2 / (χ : ClassFunction G ℂ) 1) *
            (χ : ClassFunction G ℂ) x) := by
  rw [invPairCF, ClassFunction.smul_apply, ClassFunction.sum_apply]
  refine congrArg _ (Finset.sum_congr rfl (fun χ _ => ?_))
  rw [ClassFunction.smul_apply]

/-- `invPairCF` computes `Work.BSW.invPairCount`. -/
theorem invPairCF_apply {t : G} (ht : orderOf t = 2)
    (hconj : ∀ x : G, orderOf x = 2 → IsConj x t) (x : G) :
    invPairCF G t x = (Work.BSW.invPairCount G x : ℂ) := by
  letI : Fintype G := Fintype.ofFinite G
  rw [invPairCF_apply_def,
    Work.BSW.Char.invPairCount_eq_sum_characters (G := G) ht hconj x]
  congr 1
  exact Finset.sum_congr rfl fun χ _ => by rw [div_mul_eq_mul_div]

end InvPairCF

section Values

variable {t s : G} {K : Subgroup G}

/-- The involutions inverting `t` are exactly `{t} ∪ Ks`. -/
theorem involutions_inverting_t (h : BSWHyps2 G t s K) :
    {u : G | orderOf u = 2 ∧ u⁻¹ * t * u = t⁻¹}
      = {t} ∪ {x : G | ∃ k ∈ K, x = k * s} := by
  ext u
  constructor
  · rintro ⟨hu2, hu⟩
    rcases Work.BSW.Char.inv_inverting_t_mem_coset h hu2 hu with heq | hmem
    · exact Or.inl heq
    · exact Or.inr hmem
  · rintro (rfl | ⟨k, hk, rfl⟩)
    · refine ⟨Work.BSW.orderOf_t h, ?_⟩
      rw [Work.BSW.t_inv h, Work.BSW.t_mul_self h, one_mul]
    · exact (Work.BSW.Char.coset_sK_involutions h).1 k hk

/-- **`i(t) = k`** in the pair-count normalization: the involution count `iFn G t = k + 1` counts
the coset `Ks` together with `t` itself, but the pair `(u, v) = (t, 1)` is excluded from the
pair count. -/
theorem invPairCount_t (h : BSWHyps2 G t s K) :
    Work.BSW.invPairCount G t = Nat.card ↥K := by
  have ht2 : t * t = 1 := Work.BSW.t_mul_self h
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  obtain ⟨hcard, htnot⟩ := Work.BSW.Char.ncard_coset_sK h
  have key : {p : G × G | orderOf p.1 = 2 ∧ orderOf p.2 = 2 ∧ p.1 * p.2 = t}.ncard
      = {x : G | ∃ k ∈ K, x = k * s}.ncard := by
    refine Set.ncard_congr (fun p _ => p.1) ?_ ?_ ?_
    · rintro p ⟨hp1, hp2, hp3⟩
      obtain ⟨u, v⟩ := p
      simp only at hp1 hp2 hp3
      have hut : u⁻¹ * t * u = t⁻¹ := by
        have h1 : u⁻¹ * (u * v) * u = v * u := by group
        have h2 : v * u = (u * v)⁻¹ := by
          rw [mul_inv_rev,
            inv_eq_of_mul_eq_one_left (Work.BSW.mul_self_eq_one_of_orderOf_eq_two hp2),
            inv_eq_of_mul_eq_one_left (Work.BSW.mul_self_eq_one_of_orderOf_eq_two hp1)]
        rw [← hp3, h1, h2]
      have hune : u ≠ t := by
        intro heq
        have hv1 : v = 1 := by
          have hc := congrArg (fun z => t⁻¹ * z) hp3
          rw [heq, ← mul_assoc, inv_mul_cancel, one_mul] at hc
          simpa [htinv, ht2] using hc
        rw [hv1, orderOf_one] at hp2
        exact absurd hp2 (by norm_num)
      rcases Work.BSW.Char.inv_inverting_t_mem_coset h hp1 hut with heq | hmem
      · exact absurd heq hune
      · exact hmem
    · intro a b ha hb hf
      obtain ⟨u₁, v₁⟩ := a
      obtain ⟨u₂, v₂⟩ := b
      simp only at ha hb hf
      have hu : u₁ = u₂ := hf
      subst hu
      have hv₁ : v₁ = u₁⁻¹ * t := by
        have hc := congrArg (fun z => u₁⁻¹ * z) ha.2.2
        rw [← mul_assoc, inv_mul_cancel, one_mul] at hc
        exact hc
      have hv₂ : v₂ = u₁⁻¹ * t := by
        have hc := congrArg (fun z => u₁⁻¹ * z) hb.2.2
        rw [← mul_assoc, inv_mul_cancel, one_mul] at hc
        exact hc
      rw [hv₁, hv₂]
    · intro b hb
      obtain ⟨k, hk, rfl⟩ := hb
      obtain ⟨hu2, hut⟩ := (Work.BSW.Char.coset_sK_involutions h).1 k hk
      have hu_inv : (k * s)⁻¹ = k * s :=
        inv_eq_of_mul_eq_one_left (Work.BSW.mul_self_eq_one_of_orderOf_eq_two hu2)
      have hsq : (k * s) * (k * s) = 1 := Work.BSW.mul_self_eq_one_of_orderOf_eq_two hu2
      have ht_sq : t * t = 1 := Work.BSW.mul_self_eq_one_of_orderOf_eq_two (Work.BSW.orderOf_t h)
      have hcomm : t * (k * s) = (k * s) * t := by
        have hc := congrArg (fun z => (k * s) * z) hut
        rw [show (k * s) * ((k * s)⁻¹ * t * (k * s)) = t * (k * s) from by group,
          Work.BSW.t_inv h] at hc
        exact hc
      have hv2 : ((k * s)⁻¹ * t) * ((k * s)⁻¹ * t) = 1 := by
        rw [hu_inv]
        calc ((k * s) * t) * ((k * s) * t) = (k * s) * (t * (k * s)) * t := by group
          _ = (k * s) * ((k * s) * t) * t := by rw [hcomm]
          _ = ((k * s) * (k * s)) * (t * t) := by group
          _ = 1 := by rw [hsq, ht_sq, mul_one]
      have hvne : (k * s)⁻¹ * t ≠ 1 := by
        intro h1
        have hc := congrArg (fun z => (k * s) * z) h1
        rw [mul_one, ← mul_assoc, hu_inv, hsq, one_mul] at hc
        exact htnot ⟨k, hk, hc⟩
      refine ⟨(k * s, (k * s)⁻¹ * t), ⟨hu2, ?_, ?_⟩, rfl⟩
      · exact orderOf_eq_prime (p := 2) (by rw [pow_two]; exact hv2) hvne
      · show (k * s) * ((k * s)⁻¹ * t) = t
        rw [mul_inv_cancel_left]
  rw [Work.BSW.invPairCount, key, hcard]

/-- **`i(x) = k`** for `x ∈ K ∖ {1, t}`: the involutions inverting such an `x` are exactly the
`k` elements of the coset `Ks` (`Work.BSW.Char.iFn_eq_card_of_mem_K`), and for `x ≠ t` the
involution count and the pair count agree (`Work.BSW.Char.iFn_eq_invPairCount`). -/
theorem invPairCount_mem_K (h : BSWHyps2 G t s K) {x : G} (hxK : x ∈ K) (hx1 : x ≠ 1)
    (hxt : x ≠ t) : Work.BSW.invPairCount G x = Nat.card ↥K := by
  have hx : x * x ≠ 1 := by
    intro hxx
    rcases Work.BSW.involution_mem_K h hxK hxx with h1 | h1
    · exact hx1 h1
    · exact hxt h1
  rw [← Work.BSW.Char.iFn_eq_invPairCount hx,
    Work.BSW.Char.iFn_eq_card_of_mem_K h hxK hx1 hxt]

end Values

end Work.BSW.Order
