import Mathlib
import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.L27Hyp_of_L28MHyp
import Submission.Work.CORE2B.t_central_in_S
import Submission.Work.CORE2B.API
import Submission.Work.CORE2B.dihedral_index_two
import Submission.Work.CORE2B.L27_fourGroup_in_C_M_t
import Submission.Work.CORE2B.sylow_not_cyclic_of_sub
import Submission.Work.CORE2B.L29_callSite_nonvacuous
import Submission.Work.CORE2B.L29_tower_normcond

namespace Work.CORE2B

open Subgroup

set_option linter.style.haveILetI false

-- GW design pass 18, item A′, leaf H3 (copied from `Core18L27HypOfPairNormalizer.lean`): Bender
-- applies Lemma 2.7 to `M ⊇ N_G(X) ⊇ N_S(⟨t,s⟩)`, *not* to an `M ⊇ S`; this leaf supplies
-- `L27Hyp B M` from the pair-normalizer hypothesis.
-- Sketch: `V = ⟨t,s⟩` is a four-group (`t ∈ Z(S)`, `s ∉ S₀` an involution `≠ t`).
-- * `t ∈ M`: `t ∈ S` normalizes `V`.
-- * `sylow_nc`: `V ≤ M`, and any `P ∈ Syl₂(M)` contains an `M`-conjugate of `V`, a four-group;
--   a cyclic group has a unique involution.
-- * `size`: if `|S| = 4` take the middle disjunct; otherwise `|S| ≥ 8` and, in the nilpotent
--   group `S`, `N_S(V) > V` (`normalizer condition`), so `|N_S(V)| ≥ 8` and
--   `N_S(V) = S ⊓ N(V) ≤ S ⊓ M`, giving `8 ≤ |S ⊓ M|`.
-- GAP (`gw18_A.g`, A2): `|N_S(⟨t,s⟩)| = 8` for dihedral `S` of order 8…128.
theorem C18L27HypOfPairNormalizer_proved {G : Type} [Group G] [Finite G]
    (hCtx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (s : G)
    (hs : s ∈ (B.S : Subgroup G)) (hs0 : s ∉ B.S0) (M : Subgroup G) (hMne : M ≠ ⊤)
    (hrel : Work.GW2.BRel B.Hhat M) (hnle : ¬ M ≤ B.Hhat) (htl : B.t ∉ Work.GW2.layerIn M)
    (hN : (B.S : Subgroup G) ⊓
      Subgroup.normalizer ((Subgroup.closure ({B.t, s} : Set G) : Subgroup G) : Set G) ≤ M) :
    Work.CORE2B.L27Hyp B M := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- ### `t` is an involution of `S`
  have htS : B.t ∈ (B.S : Subgroup G) := B.S0_le B.t_mem
  have ht2 : B.t ^ 2 = 1 := by rw [← B.t_order]; exact pow_orderOf_eq_one B.t
  have ht1 : B.t ≠ 1 := by
    intro h
    have hord := B.t_order
    rw [h, orderOf_one] at hord
    exact absurd hord (by norm_num)
  -- ### `|S₀| ≥ 2` and `|S| = 2|S₀|`
  have hS0card : 2 ≤ Nat.card B.S0 := by
    have hle : Subgroup.zpowers B.t ≤ B.S0 := Subgroup.zpowers_le.mpr B.t_mem
    have h : Nat.card ↥(Subgroup.zpowers B.t) ≤ Nat.card ↥B.S0 :=
      Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hle)
    rw [Nat.card_zpowers, B.t_order] at h
    exact h
  have hcardS : Nat.card (B.S : Subgroup G) = 2 * Nat.card B.S0 := by
    have h := Subgroup.relIndex_mul_card B.S0 (B.S : Subgroup G)
    rw [B.S0_index, inf_eq_left.mpr B.S0_le] at h
    exact h.symm
  -- ### `S` is dihedral of order `2n`, `n ≥ 2`, so `s ∈ S \ S₀` is an involution
  obtain ⟨n, hn2, hndih⟩ : ∃ n : ℕ, 2 ≤ n ∧ Nonempty ((B.S : Subgroup G) ≃* DihedralGroup n) := by
    rcases hCtx.sylow B.S with hcyc | ⟨n, hn⟩
    · exact absurd hcyc (Work.CORE2B.BenderCtx_sylow_not_cyclic hCtx B.S)
    · obtain ⟨e⟩ := hn
      have hcard : Nat.card (B.S : Subgroup G) = 2 * n := by
        rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
      exact ⟨n, by omega, ⟨e⟩⟩
  have hso : orderOf s = 2 :=
    dihedral_index_two n hn2 (B.S : Subgroup G) B.S0 hndih B.S0_le B.S0_cyclic B.S0_index s hs hs0
  have hs2 : s ^ 2 = 1 := by rw [← hso]; exact pow_orderOf_eq_one s
  have hs1 : s ≠ 1 := fun h => hs0 (h ▸ B.S0.one_mem)
  have hnes : s ≠ B.t := fun h => hs0 (h.symm ▸ B.t_mem)
  have hcomm : s * B.t = B.t * s := t_central_in_S B s hs
  -- ### the Klein four-group `V = ⟨t,s⟩`
  set V : Subgroup G := Subgroup.closure ({B.t, s} : Set G) with hVdef
  have hfour := fourGroup_closure_pair ht2 hs2 ht1 hs1 hnes hcomm
  have hV4 : Work.GW2.IsFourGroup V := by rw [hVdef]; exact hfour.1
  have hVcard : Nat.card ↥V = 4 := hV4.1
  have htV : B.t ∈ V := by rw [hVdef]; exact hfour.2.1
  have hsV : s ∈ V := by
    rw [hVdef]; exact Subgroup.subset_closure (by simp)
  have hVS : V ≤ (B.S : Subgroup G) := by
    rw [hVdef, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact htS
    · exact hs
  -- ### `V ≤ M` and `t ∈ M`, from the pair-normalizer hypothesis
  have hSinfN : (B.S : Subgroup G) ⊓ Subgroup.normalizer (V : Set G) ≤ M := by
    simpa only [hVdef] using hN
  have htM : B.t ∈ M := hSinfN ⟨htS, Subgroup.le_normalizer htV⟩
  have hsM : s ∈ M := hSinfN ⟨hs, Subgroup.le_normalizer hsV⟩
  have hVM : V ≤ M := by
    rw [hVdef, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact htM
    · exact hsM
  refine ⟨hMne, hrel, hnle, htM, htl, ?_, ?_⟩
  · -- ### a Sylow `2`-subgroup of `M` contains a conjugate of the non-cyclic `V`
    intro P
    obtain ⟨hVpg, hVnc⟩ := subgroupOf_four_not_cyclic V M hV4 hVM
    exact sylow_not_cyclic_of_sub (V.subgroupOf M) hVpg hVnc P
  · -- ### the size condition
    by_cases h4 : Nat.card (B.S : Subgroup G) = 4
    · exact Or.inr (Or.inl h4)
    · refine Or.inl ?_
      -- `V` is a proper subgroup of `S`, and `S` is nilpotent, so `N_S(V) = S ⊓ N(V)` grows:
      -- `V < S ⊓ N(V)`; since moreover `4 = |V| ∣ |S ⊓ N(V)|`, this gives `|S ⊓ N(V)| ≥ 8`.
      have hVneS : V ≠ (B.S : Subgroup G) := fun heq => h4 (by rw [← heq]; exact hVcard)
      have hnil : Group.IsNilpotent ↥(B.S : Subgroup G) :=
        IsPGroup.isNilpotent (Sylow.isPGroup' B.S)
      have hlt : V < (B.S : Subgroup G) ⊓ Subgroup.normalizer (V : Set G) :=
        L29_tower_normcond (B.S : Subgroup G) V hnil hVS hVneS
      have hcardlt : Nat.card ↥V <
          Nat.card ↥((B.S : Subgroup G) ⊓ Subgroup.normalizer (V : Set G)) :=
        Subgroup.card_lt_of_lt hlt
      have hdvd : 4 ∣ Nat.card ↥((B.S : Subgroup G) ⊓ Subgroup.normalizer (V : Set G)) := by
        have h := Subgroup.card_dvd_of_le (le_inf hVS Subgroup.le_normalizer :
          V ≤ (B.S : Subgroup G) ⊓ Subgroup.normalizer (V : Set G))
        rwa [hVcard] at h
      have hcardle : Nat.card ↥((B.S : Subgroup G) ⊓ Subgroup.normalizer (V : Set G)) ≤
          Nat.card ↥((B.S : Subgroup G) ⊓ M) :=
        Subgroup.card_le_of_le (le_inf inf_le_left hSinfN)
      obtain ⟨k, hk⟩ := hdvd
      omega

end Work.CORE2B
