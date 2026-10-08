import Mathlib
import Submission.Work.BSW.Char.Setup
import Submission.Work.BSW.Char.invPairCount_eq_sum_characters
import Submission.Work.BSW.Char.iFn_t
import Submission.Work.BSW.Api.card_centralizer_of_card_K_two
import Submission.Work.BSW.Vocab

namespace Work.BSW.Char

open OddOrder.RepresentationTheory

/-- For an involution `x`, Bender's count `i(x)` of the involutions inverting `x` exceeds the
number `invPairCount G x` of ordered pairs `(u, v)` of involutions with `u * v = x` by exactly one:
the extra solution is `u = x`, `v = 1`, whose second component is not an involution.

Proof: the map `u ↦ (u, u * x)` is injective on the set `A` of involutions inverting `x` and its
image is `B ∪ {(x, 1)}`, where `B` is the pair-counting set: the second component `u * x` is
always an involution, and it is trivial exactly when `u = x`.  Since `x ∈ A` maps to `(x, 1)` and
`(x, 1) ∉ B`, the two cardinalities differ by one. -/
theorem iFn_eq_invPairCount_add_one {G : Type} [Group G] [Finite G] {x : G}
    (hx : orderOf x = 2) : Work.BSW.iFn G x = Work.BSW.invPairCount G x + 1 := by
  have hx2 : x * x = 1 := Work.BSW.mul_self_eq_one_of_orderOf_eq_two hx
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_left hx2
  set A : Set G := {u : G | orderOf u = 2 ∧ u⁻¹ * x * u = x⁻¹} with hA
  set B : Set (G × G) :=
    {p : G × G | orderOf p.1 = 2 ∧ orderOf p.2 = 2 ∧ p.1 * p.2 = x} with hB
  have hxA : x ∈ A := by
    rw [hA]
    exact ⟨hx, by rw [hxinv, mul_assoc, hx2, mul_one]⟩
  -- ### the map `u ↦ (u, u * x)` lands in `B ∪ {(x, 1)}`
  have hφmem : ∀ u ∈ A, (u, u * x) ∈ B ∪ {((x, 1) : G × G)} := by
    intro u hu
    rw [hA] at hu
    obtain ⟨hu2, hu⟩ := hu
    have hu2' : u * u = 1 := Work.BSW.mul_self_eq_one_of_orderOf_eq_two hu2
    have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_left hu2'
    have huxu : u * x * u = x⁻¹ := by rw [huinv] at hu; exact hu
    have hvv : (u * x) * (u * x) = 1 := by rw [← mul_assoc, huxu, inv_mul_cancel]
    have hdiv : orderOf (u * x) ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hvv)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with h1 | h2
    · -- `u * x = 1`, i.e. `u = x`, so the image is `(x, 1)`
      right
      have hux1 : u * x = 1 := orderOf_eq_one_iff.mp h1
      have hux : u = x := by
        have h := eq_inv_of_mul_eq_one_right hux1
        rw [huinv] at h
        exact h.symm
      rw [Set.mem_singleton_iff]
      exact Prod.ext hux hux1
    · left
      rw [hB]
      exact ⟨hu2, h2, by rw [← mul_assoc, hu2', one_mul]⟩
  -- ### the image of `A \ {x}` is exactly `B`
  have hAB : ∀ u ∈ A \ {x}, (u, u * x) ∈ B := by
    intro u hu
    rcases hφmem u hu.1 with h | h
    · exact h
    · rw [Set.mem_singleton_iff] at h
      exact absurd (Prod.mk.inj h).1 (fun hux => hu.2 (Set.mem_singleton_iff.mpr hux))
  have hBA : ∀ p ∈ B, ∃ u ∈ A \ {x}, (u, u * x) = p := by
    intro p hp
    rw [hB] at hp
    obtain ⟨hu2, hv2, huv⟩ := hp
    have hu2' : p.1 * p.1 = 1 := Work.BSW.mul_self_eq_one_of_orderOf_eq_two hu2
    have huinv : p.1⁻¹ = p.1 := inv_eq_of_mul_eq_one_left hu2'
    have hv2' : p.2 * p.2 = 1 := Work.BSW.mul_self_eq_one_of_orderOf_eq_two hv2
    have hvinv : p.2⁻¹ = p.2 := inv_eq_of_mul_eq_one_left hv2'
    have hmemA : p.1 ∈ A := by
      rw [hA]
      refine ⟨hu2, ?_⟩
      rw [huinv]
      have hLHS : p.1 * x * p.1 = p.2 * p.1 := by
        rw [← huv]
        calc p.1 * (p.1 * p.2) * p.1 = (p.1 * p.1) * (p.2 * p.1) := by group
          _ = p.2 * p.1 := by rw [hu2', one_mul]
      have hRHS : x⁻¹ = p.2 * p.1 := by rw [← huv, mul_inv_rev, huinv, hvinv]
      rw [hLHS, hRHS]
    have hne : p.1 ∉ ({x} : Set G) := by
      rw [Set.mem_singleton_iff]
      intro hpx
      have hp21 : p.2 = 1 :=
        mul_left_cancel (a := p.1) (by rw [huv, hpx, mul_one])
      rw [hp21, orderOf_one] at hv2
      exact absurd hv2 (by norm_num)
    have hcomp : p.1 * x = p.2 := by rw [← huv, ← mul_assoc, hu2', one_mul]
    exact ⟨p.1, ⟨hmemA, hne⟩, Prod.ext rfl hcomp⟩
  have hcard : (A \ {x}).ncard = B.ncard :=
    Set.ncard_congr (fun u _ => (u, u * x)) hAB (fun u1 _ u2 _ h => congrArg Prod.fst h)
      (fun p hp => by obtain ⟨u, hu, hup⟩ := hBA p hp; exact ⟨u, hu, hup⟩)
  -- ### `x ∈ A` contributes the single extra element
  have hAcard : A.ncard = (A \ {x}).ncard + 1 := by
    have hthis := Set.ncard_insert_of_notMem (s := A \ {x}) (a := x) (by simp : x ∉ A \ {x})
    rwa [Set.insert_sdiff_singleton, Set.insert_eq_of_mem hxA] at hthis
  rw [Work.BSW.iFn, Work.BSW.invPairCount, ← hA, ← hB, hAcard, hcard]

/-- **Bender 1974, §2** for `|K| = 2`: the character-theoretic identity
`∑_χ χ(t)³ / χ(1) = 32 / |G|`.

Route: the involution-product formula `Work.BSW.Char.invPairCount_eq_sum_characters` at `x = t`
reads `invPairCount G t = |G| / |C_G(t)|² * ∑_χ χ(t)³/χ(1)`.  In the `|K| = 2` case
`|C_G(t)| = 4` (`Work.BSW.Api.card_centralizer_of_card_K_two`), and `invPairCount G t = 2`:
`i(t) = |K| + 1 = 3` (`Work.BSW.Char.iFn_t`) and `i(t) = invPairCount G t + 1` because `t` is an
involution (`Work.BSW.Char.iFn_eq_invPairCount_add_one`).  Solving `2 = |G|/16 * S` gives
`S = 32/|G|`. -/
theorem sum_chi_t_cube_div {G : Type} [Group G] [Fintype G] {t s : G} {K : Subgroup G}
    (h : Work.GW2.BSWHyps2 G t s K) (hk : Nat.card ↥K = 2) :
    ∑ χ : OddOrder.RepresentationTheory.IrreducibleCharacter G,
      ((χ : OddOrder.RepresentationTheory.ClassFunction G ℂ) t) ^ 3 /
        (χ : OddOrder.RepresentationTheory.ClassFunction G ℂ) 1 =
      32 / (Nat.card G : ℂ) := by
  have ht : orderOf t = 2 := Work.BSW.orderOf_t h
  have hconj : ∀ x : G, orderOf x = 2 → IsConj x t := Work.BSW.involutions_conj h
  -- the involution-product formula at `x = t`
  have hsum := invPairCount_eq_sum_characters (G := G) (t := t) ht hconj t
  have hC : Nat.card ↥(Subgroup.centralizer ({t} : Set G)) = 4 :=
    Work.BSW.Api.card_centralizer_of_card_K_two h hk
  -- `invPairCount G t = 2`
  have hpc : Work.BSW.invPairCount G t = 2 := by
    have h1 := iFn_eq_invPairCount_add_one (G := G) ht
    rw [Work.BSW.Char.iFn_t h, hk] at h1
    omega
  set S : ℂ := ∑ χ : IrreducibleCharacter G,
      (((χ : ClassFunction G ℂ) t) ^ 2 * (χ : ClassFunction G ℂ) t) /
        (χ : ClassFunction G ℂ) 1 with hS
  have hsumS : (2 : ℂ) = (Nat.card G : ℂ) / 16 * S := by
    have h' := hsum
    rw [hpc, hC] at h'
    norm_num at h'
    rw [← Nat.card_eq_fintype_card] at h'
    exact h'
  have hG : (Nat.card G : ℂ) ≠ 0 := by
    have := Nat.card_pos (α := G)
    exact_mod_cast this.ne'
  have hScube : S = 32 / (Nat.card G : ℂ) := by
    rw [eq_div_iff hG, mul_comm S (Nat.card G : ℂ)]
    have h1 : ((Nat.card G : ℂ) / 16) * 16 = (Nat.card G : ℂ) := by ring
    calc (Nat.card G : ℂ) * S = (((Nat.card G : ℂ) / 16) * 16) * S := by rw [h1]
      _ = (((Nat.card G : ℂ) / 16) * S) * 16 := by ring
      _ = 2 * 16 := by rw [← hsumS]
      _ = 32 := by norm_num
  rw [← hScube, hS]
  refine Finset.sum_congr rfl (fun χ _ => ?_)
  ring

end Work.BSW.Char
