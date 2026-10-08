import Mathlib
import Submission.Work.CORE4.EightIdxDefs

open scoped commutatorElement

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.CORE4

/-- Key structural lemma: a normal subgroup of order `p ^ 2` of a finite `p`-group lies in the
second centre, i.e. every triple commutator `⁅⁅x, y⁆, z⁆` with `x ∈ N` vanishes.

Proof.  Let `Z = N ⊓ Z(H)`.  Since `H` is nilpotent, `Z ≠ ⊥`.  If `Z = N` then `N` is central and
there is nothing to prove.  Otherwise `Z` is a nontrivial proper subgroup of `N`, so `|Z| = p`
(as `|N| = p²`).  Then `N/Z` is a normal subgroup of prime order of the `p`-group `H/Z`, hence
central in `H/Z`; consequently `[N, H] ≤ Z ≤ Z(H)`. -/
theorem z2Set_of_normal_card_prime_sq {H : Type} [Group H] [Finite H] {p : ℕ} (hp : p.Prime)
    (hH : IsPGroup p H) (N : Subgroup H) (hN : N.Normal) (hcard : Nat.card ↥N = p ^ 2) :
    ∀ x ∈ N, ∀ y z : H, ⁅⁅x, y⁆, z⁆ = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hNil : Group.IsNilpotent H := hH.isNilpotent
  haveI hNnorm : N.Normal := hN
  have hNne : N ≠ ⊥ := by
    rw [← Subgroup.one_lt_card_iff_ne_bot N, hcard]
    nlinarith [hp.two_le]
  by_cases hNc : N ≤ Subgroup.center H
  · -- `N` is central
    intro x hx y z
    have hxy : ⁅x, y⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp (hNc hx) y).symm
    rw [hxy]
    simp
  · -- `Z = N ⊓ Z(H)` has order `p`
    set Z : Subgroup H := N ⊓ Subgroup.center H with hZdef
    haveI hZn : Z.Normal := by rw [hZdef]; infer_instance
    have hZN : Z ≤ N := by rw [hZdef]; exact inf_le_left
    have hZc : Z ≤ Subgroup.center H := by rw [hZdef]; exact inf_le_right
    have hZne : Z ≠ ⊥ := by
      rw [hZdef]; exact Group.IsNilpotent.inf_center_ne_bot_of_normal hNne
    have hZlt : Z < N := lt_of_le_of_ne hZN (fun heq => hNc (heq ▸ hZc))
    have hZcard : Nat.card ↥Z = p := by
      have hdvd : Nat.card ↥Z ∣ p ^ 2 := hcard ▸ Subgroup.card_dvd_of_le hZN
      obtain ⟨k, hk2, hkeq⟩ := (Nat.dvd_prime_pow hp (m := 2)).mp hdvd
      have h1 : 1 < Nat.card ↥Z := (Subgroup.one_lt_card_iff_ne_bot Z).mpr hZne
      have h2 : Nat.card ↥Z < p ^ 2 := hcard ▸ Subgroup.card_lt_of_lt hZlt
      interval_cases k
      · rw [pow_zero] at hkeq; omega
      · rw [pow_one] at hkeq; exact hkeq
      · rw [hkeq] at h2; exact absurd h2 (lt_irrefl _)
    -- The image of `N` in `H ⧸ Z` has order `p`, hence is central.
    have hNqN : (N.map (QuotientGroup.mk' Z)).Normal :=
      hN.map (QuotientGroup.mk' Z) QuotientGroup.mk_surjective
    haveI : (N.map (QuotientGroup.mk' Z)).Normal := hNqN
    have hker : ((QuotientGroup.mk' Z).comp N.subtype).ker = Z.subgroupOf N := by
      ext g
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.comp_apply,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      rfl
    have hrange : ((QuotientGroup.mk' Z).comp N.subtype).range = N.map (QuotientGroup.mk' Z) := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have hcardker : Nat.card ↥(((QuotientGroup.mk' Z).comp N.subtype).ker) = p := by
      rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZN).toEquiv, hZcard]
    have hcardNq : Nat.card ↥(N.map (QuotientGroup.mk' Z)) = p := by
      have key : Nat.card (↥N ⧸ ((QuotientGroup.mk' Z).comp N.subtype).ker) =
          Nat.card ↥(((QuotientGroup.mk' Z).comp N.subtype).range) :=
        Nat.card_congr
          (QuotientGroup.quotientKerEquivRange ((QuotientGroup.mk' Z).comp N.subtype)).toEquiv
      have hq : Nat.card (↥N ⧸ ((QuotientGroup.mk' Z).comp N.subtype).ker) = p := by
        have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
          (((QuotientGroup.mk' Z).comp N.subtype).ker)
        rw [hcard, hcardker] at h
        rw [pow_two] at h
        exact Nat.mul_right_cancel hp.pos h.symm
      rw [← hrange, ← key]
      exact hq
    have hNqne : N.map (QuotientGroup.mk' Z) ≠ ⊥ :=
      (Subgroup.one_lt_card_iff_ne_bot _).mp (by rw [hcardNq]; exact hp.one_lt)
    have hNqcenter : N.map (QuotientGroup.mk' Z) ≤ Subgroup.center (H ⧸ Z) := by
      have hne : N.map (QuotientGroup.mk' Z) ⊓ Subgroup.center (H ⧸ Z) ≠ ⊥ :=
        Group.IsNilpotent.inf_center_ne_bot_of_normal hNqne
      by_contra hcon
      have hlt : N.map (QuotientGroup.mk' Z) ⊓ Subgroup.center (H ⧸ Z) <
          N.map (QuotientGroup.mk' Z) :=
        lt_of_le_of_ne inf_le_left (fun heq => hcon (heq ▸ inf_le_right))
      have hcardlt : Nat.card ↥(N.map (QuotientGroup.mk' Z) ⊓ Subgroup.center (H ⧸ Z)) <
          Nat.card ↥(N.map (QuotientGroup.mk' Z)) := Subgroup.card_lt_of_lt hlt
      have hcardgt : 1 < Nat.card ↥(N.map (QuotientGroup.mk' Z) ⊓ Subgroup.center (H ⧸ Z)) :=
        (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
      have hdv : Nat.card ↥(N.map (QuotientGroup.mk' Z) ⊓ Subgroup.center (H ⧸ Z)) ∣
          Nat.card ↥(N.map (QuotientGroup.mk' Z)) := Subgroup.card_dvd_of_le inf_le_left
      rw [hcardNq] at hcardlt hdv
      rcases (Nat.dvd_prime hp).mp hdv with h1 | h1 <;> omega
    -- Conclusion: `[N, H] ≤ Z ≤ Z(H)`.
    intro x hx y z
    have hxNq : (QuotientGroup.mk' Z x) ∈ N.map (QuotientGroup.mk' Z) :=
      Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    have hcx : (QuotientGroup.mk' Z x) ∈ Subgroup.center (H ⧸ Z) := hNqcenter hxNq
    have h1 : ⁅QuotientGroup.mk' Z x, QuotientGroup.mk' Z y⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr
        ((Subgroup.mem_center_iff.mp hcx (QuotientGroup.mk' Z y)).symm)
    have h2 : (QuotientGroup.mk' Z) ⁅x, y⁆ = 1 := by
      rw [map_commutatorElement]
      exact h1
    have hxy : ⁅x, y⁆ ∈ Z := by
      have hmem : ⁅x, y⁆ ∈ (QuotientGroup.mk' Z).ker := MonoidHom.mem_ker.mpr h2
      rwa [QuotientGroup.ker_mk' Z] at hmem
    have hxyc : ⁅x, y⁆ ∈ Subgroup.center H := hZc hxy
    exact commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hxyc z).symm

theorem E2Z2le {G : Type} [Group G] [Finite G] (p : ℕ) (hp : p.Prime) (P A : Subgroup G) (hP : IsPGroup p ↥P) (hAle : A ≤ P) (hAn : (A.subgroupOf P).Normal) (hcard : Nat.card ↥A = p ^ 2) (hexp : ∀ x ∈ A, x ^ p = 1) : A ≤ Work.CORE4.z2 P := by
  intro x hx
  have hxP : x ∈ P := hAle hx
  rw [z2]
  refine Subgroup.subset_closure ⟨hxP, ?_⟩
  intro y hy z hz
  have hcardN : Nat.card ↥(A.subgroupOf P) = p ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAle).toEquiv, hcard]
  have hcomm := z2Set_of_normal_card_prime_sq hp hP (A.subgroupOf P) hAn hcardN
      (⟨x, hxP⟩ : ↥P) (by rw [Subgroup.mem_subgroupOf]; exact hx)
      (⟨y, hy⟩ : ↥P) (⟨z, hz⟩ : ↥P)
  simpa using congrArg P.subtype hcomm

end Work.CORE4
