import Mathlib
import Submission.Work.ThompsonFrobenius.GTDefs
import Submission.Work.ThompsonFrobenius.npc_quotient
import Submission.Work.ThompsonFrobenius.pCore_lt
import Submission.Work.ThompsonFrobenius.commutator_le
import Submission.Work.HallHigman.ModRep

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# GT-7b: the Sylow `2`-subgroups of the minimal counterexample are abelian (area `ThompsonFrobenius`)

Step GT-7b of `NOTES_LEAD_bs_thompson.md`.  With `H = O_p(G)` and `K` the preimage of the normal
`p`-complement of `G/H`:

* `G/K` is a `p`-group with `p ≠ 2`, so the image in `G/K` of a `2`-subgroup is both a `2`-group
  and a `p`-group, hence trivial: `S ≤ K`.
* `⁅S,S⁆ ≤ ⁅K,K⁆ ≤ O_p(G)` (GT-6) and `S ⊓ O_p(G) = 1` (coprime orders, `p` odd), so `S` is
  abelian.
-/

set_option autoImplicit false

open scoped Pointwise commutatorElement

namespace Work.ThompsonFrobenius

theorem abelianSylowTwo {p : ℕ} {G : Type} [Group G] [Finite G] {P : Sylow p G}
    (h : GTMinimal p G P) :
    ∀ S : Sylow 2 G, Submission.Blueprint.IsAbelianSubgroup (S : Subgroup G) := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro S
  let H : Subgroup G := Work.HallHigman.pCore p G
  haveI hHnormal : H.Normal := inferInstance
  have hHpg : IsPGroup p H := Work.HallHigman.isPGroup_pCore
  obtain ⟨Mbar, hMbar⟩ := npc_quotient h
  haveI hMbarnormal : Mbar.Normal := hMbar.normal
  let K : Subgroup G := Mbar.comap (QuotientGroup.mk' H)
  haveI hKnormal : K.Normal := Subgroup.normal_comap _
  have hHK : H ≤ K := by
    intro x hx
    show (QuotientGroup.mk' H) x ∈ Mbar
    have h1 : (QuotientGroup.mk' H) x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    simpa [h1] using Mbar.one_mem
  have hKmap : Subgroup.map (QuotientGroup.mk' H) K = Mbar := by
    show Subgroup.map (QuotientGroup.mk' H) (Mbar.comap (QuotientGroup.mk' H)) = Mbar
    rw [Subgroup.map_comap_eq, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective H),
      top_inf_eq]
  have hGKpg : IsPGroup p (G ⧸ K) := by
    have hiso : (G ⧸ H) ⧸ Mbar ≃* G ⧸ K :=
      (QuotientGroup.quotientMulEquivOfEq hKmap).symm.trans
        (QuotientGroup.quotientQuotientEquivQuotient H K hHK)
    exact IsPGroup.of_equiv hMbar.isPGroup_quotient hiso
  -- `S ≤ K`
  have hSK : (S : Subgroup G) ≤ K := by
    have htriv : S.map (QuotientGroup.mk' K) = ⊥ := by
      have hd : Disjoint (S.map (QuotientGroup.mk' K)) (S.map (QuotientGroup.mk' K)) :=
        IsPGroup.disjoint_of_ne 2 p (fun h2p => h.ne_two h2p.symm)
          (S.map (QuotientGroup.mk' K)) (S.map (QuotientGroup.mk' K))
          (S.isPGroup'.map (QuotientGroup.mk' K))
          (IsPGroup.to_le (IsPGroup.of_equiv hGKpg (Subgroup.topEquiv (G := G ⧸ K)).symm)
            (le_top : S.map (QuotientGroup.mk' K) ≤ ⊤))
      have h1 : (S.map (QuotientGroup.mk' K)) ⊓ (S.map (QuotientGroup.mk' K)) = ⊥ :=
        disjoint_iff.mp hd
      rwa [inf_idem] at h1
    have h1 : (S : Subgroup G) ≤ (QuotientGroup.mk' K).ker :=
      (Subgroup.map_eq_bot_iff (S : Subgroup G)).mp htriv
    rwa [QuotientGroup.ker_mk'] at h1
  -- `⁅S,S⁆ ≤ O_p(G)`
  have hcomm : ⁅(S : Subgroup G), (S : Subgroup G)⁆ ≤ H :=
    (Subgroup.commutator_mono hSK hSK).trans
      (commutator_le h (show Work.NPC.IsNormalPComplement p (K.map (QuotientGroup.mk' H))
        from hKmap.symm ▸ hMbar) hHK)
  -- `S ⊓ O_p(G) = 1`
  have hinf : (S : Subgroup G) ⊓ H = ⊥ := by
    refine Subgroup.inf_eq_bot_of_coprime ?_
    obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
    obtain ⟨m, hm⟩ := hHpg.exists_card_eq
    rw [hk, hm]
    have hcop2 : Nat.Coprime 2 p := by
      rw [Nat.prime_two.coprime_iff_not_dvd]
      intro h2dvd
      exact h.ne_two ((Nat.prime_dvd_prime_iff_eq Nat.prime_two h.prime).mp h2dvd).symm
    exact (hcop2.pow_left k).pow_right m
  have hbot : ⁅(S : Subgroup G), (S : Subgroup G)⁆ = ⊥ := by
    have h1 : ⁅(S : Subgroup G), (S : Subgroup G)⁆ ≤ H ⊓ (S : Subgroup G) :=
      le_inf hcomm (Subgroup.commutator_le_self (S : Subgroup G))
    rw [inf_comm] at h1
    exact le_bot_iff.mp (h1.trans (le_of_eq hinf))
  have hcent : (S : Subgroup G) ≤ Subgroup.centralizer (S : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
  intro x hx y hy
  exact (Subgroup.mem_centralizer_iff.mp (hcent hx) y hy).symm

end Work.ThompsonFrobenius
