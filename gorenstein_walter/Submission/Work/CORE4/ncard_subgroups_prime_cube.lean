import Mathlib
import Submission.Work.CORE4.EightIdxDefs
import Submission.Work.CORE4.NcardSubgroupsCardPrimeSq

namespace Work.CORE4

/-- If `N` is a normal subgroup of `G` and `K ≤ G ⧸ N`, the preimage of `K` under the quotient
map has cardinality `|N| * |K|`. -/
theorem ncard_comap_quotientMk {G : Type} [Group G] (N : Subgroup G) [N.Normal]
    (K : Subgroup (G ⧸ N)) :
    Nat.card ↥(K.comap (QuotientGroup.mk' N)) = Nat.card ↥N * Nat.card ↥K :=
  (Nat.card_congr (show ↥(K.comap (QuotientGroup.mk' N)) ≃ ↥N × ↥K from
      QuotientGroup.preimageMkEquivSubgroupProdSet N (K : Set (G ⧸ N)))).trans
    (Nat.card_prod _ _)

/-- Counting lemma: a finite group of exponent `p`, of order `p ^ 3`, whose centre has order `p`,
has exactly `p + 1` subgroups of order `p ^ 2` containing the centre.

Such a group is the nonabelian group of order `p ^ 3` and exponent `p`; subgroups of order `p ^ 2`
containing the centre correspond to the subgroups of order `p` of the elementary abelian quotient
`G ⧸ Z(G)` of order `p ^ 2`, of which there are `p + 1`. -/
theorem ncard_subgroups_prime_cube_center {G : Type} [Group G] [Finite G] (p : ℕ) (hp : p.Prime)
    (hexp : ∀ x : G, x ^ p = 1) (hcard : Nat.card G = p ^ 3)
    (hZ : Nat.card ↥(Subgroup.center G) = p) :
    {H : Subgroup G | Nat.card ↥H = p ^ 2 ∧ Subgroup.center G ≤ H}.ncard = p + 1 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hp0 : 0 < p := hp.pos
  -- The quotient by the centre has order `p ^ 2`.
  have hquot : Nat.card (G ⧸ Subgroup.center G) = p ^ 2 := by
    have h1 : Nat.card G
        = Nat.card (G ⧸ Subgroup.center G) * Nat.card ↥(Subgroup.center G) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup _
    rw [hcard, hZ] at h1
    have h2 : Nat.card (G ⧸ Subgroup.center G) * p = p ^ 2 * p := h1.symm.trans (by ring)
    exact Nat.mul_right_cancel hp0 h2
  -- The quotient by the centre has exponent dividing `p`.
  have hexpq : ∀ y : G ⧸ Subgroup.center G, y ^ p = 1 := by
    intro y
    induction y using QuotientGroup.induction_on with
    | H x =>
      show QuotientGroup.mk' (Subgroup.center G) x ^ p = 1
      rw [← map_pow (QuotientGroup.mk' (Subgroup.center G)) x p, hexp x, map_one]
  -- The quotient by the centre of a group of order `p ^ 2` is abelian.
  haveI : IsMulCommutative (G ⧸ Subgroup.center G) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := p) hquot
  have hcomm : ∀ a b : G ⧸ Subgroup.center G, a * b = b * a := fun a b => mul_comm' a b
  have hK : {K : Subgroup (G ⧸ Subgroup.center G) | Nat.card ↥K = p}.ncard = p + 1 :=
    NcardSubgroupsCardPrimeSq p (G ⧸ Subgroup.center G) hquot hexpq hcomm
  -- Correspondence between subgroups of order `p ^ 2` containing the centre and subgroups of
  -- order `p` of the quotient.
  have hbij : {H : Subgroup G | Nat.card ↥H = p ^ 2 ∧ Subgroup.center G ≤ H}.ncard
      = {K : Subgroup (G ⧸ Subgroup.center G) | Nat.card ↥K = p}.ncard := by
    refine Set.ncard_congr' ?_
    refine
      { toFun := fun H => ⟨H.1.map (QuotientGroup.mk' (Subgroup.center G)), ?_⟩
        invFun := fun K => ⟨K.1.comap (QuotientGroup.mk' (Subgroup.center G)), ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · show Nat.card ↥(H.1.map (QuotientGroup.mk' (Subgroup.center G))) = p
      have hc : (H.1.map (QuotientGroup.mk' (Subgroup.center G))).comap
            (QuotientGroup.mk' (Subgroup.center G)) = H.1 := by
        rw [QuotientGroup.comap_map_mk' (Subgroup.center G) H.1, sup_eq_right.mpr H.2.2]
      have h2 := ncard_comap_quotientMk (Subgroup.center G)
        (H.1.map (QuotientGroup.mk' (Subgroup.center G)))
      rw [hc, hZ, H.2.1] at h2
      have h3 : p * Nat.card ↥(H.1.map (QuotientGroup.mk' (Subgroup.center G))) = p * p :=
        h2.symm.trans (by ring)
      exact Nat.mul_left_cancel hp0 h3
    · refine ⟨?_, QuotientGroup.le_comap_mk' (Subgroup.center G) K.1⟩
      rw [ncard_comap_quotientMk, hZ, K.2]
      ring
    · intro H
      exact Subtype.ext (by
        show (H.1.map (QuotientGroup.mk' (Subgroup.center G))).comap
            (QuotientGroup.mk' (Subgroup.center G)) = H.1
        rw [QuotientGroup.comap_map_mk' (Subgroup.center G) H.1, sup_eq_right.mpr H.2.2])
    · intro K
      exact Subtype.ext (by
        show (K.1.comap (QuotientGroup.mk' (Subgroup.center G))).map
            (QuotientGroup.mk' (Subgroup.center G)) = K.1
        exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) K.1)
  rw [hbij, hK]

theorem ncard_subgroups_prime_cube {X : Type} [Group X] [Finite X] (p : ℕ) (hp : p.Prime) (Q : Subgroup X) (hQexp : ∀ x ∈ Q, x ^ p = 1) (hQcard : Nat.card ↥Q = p ^ 3) (hZcard : Nat.card ↥(Work.CORE4.centerIn Q) = p) : {H : Subgroup X | H ≤ Q ∧ Nat.card ↥H = p ^ 2 ∧ Work.CORE4.centerIn Q ≤ H}.ncard = p + 1 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  -- The hypotheses transfer to the abstract group `↥Q`.
  have hexpQ : ∀ x : ↥Q, x ^ p = 1 := by
    intro x
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    exact hQexp x x.2
  have hZQ : Nat.card ↥(Subgroup.center ↥Q) = p := by
    rw [← hZcard]
    exact (Subgroup.card_map_of_injective (Subgroup.subtype_injective Q)).symm
  have hcount := ncard_subgroups_prime_cube_center (G := ↥Q) p hp hexpQ hQcard hZQ
  -- Transfer the count from `↥Q` to `X` along the injective map `K ↦ K.map Q.subtype`.
  have hA : {H : Subgroup X | H ≤ Q ∧ Nat.card ↥H = p ^ 2 ∧ Work.CORE4.centerIn Q ≤ H}.ncard
      ≤ {K : Subgroup ↥Q | Nat.card ↥K = p ^ 2 ∧ Subgroup.center ↥Q ≤ K}.ncard := by
    refine Set.ncard_le_ncard_of_injOn (fun H : Subgroup X => H.subgroupOf Q) ?_ ?_
    · intro H hH
      rw [Set.mem_ofPred_eq] at hH ⊢
      obtain ⟨hHQ, hHcard, hHcent⟩ := hH
      refine ⟨?_, ?_⟩
      · have hcard' : Nat.card ↥H = Nat.card ↥(H.subgroupOf Q) :=
          calc Nat.card ↥H = Nat.card ↥((H.subgroupOf Q).map Q.subtype) := by
                rw [Subgroup.map_subgroupOf_eq_of_le hHQ]
            _ = Nat.card ↥(H.subgroupOf Q) :=
                Subgroup.card_map_of_injective (Subgroup.subtype_injective Q)
        rw [← hHcard]
        exact hcard'.symm
      · have h1 : (Subgroup.center ↥Q).map Q.subtype ≤ (H.subgroupOf Q).map Q.subtype := by
          rw [Subgroup.map_subgroupOf_eq_of_le hHQ]
          exact hHcent
        exact (Subgroup.map_le_map_iff_of_injective (Subgroup.subtype_injective Q)).mp h1
    · intro H hH H' hH' heq
      rw [Set.mem_ofPred_eq] at hH hH'
      have heq' : H.subgroupOf Q = H'.subgroupOf Q := heq
      rw [← Subgroup.map_subgroupOf_eq_of_le hH.1, heq',
        Subgroup.map_subgroupOf_eq_of_le hH'.1]
  have hB : {K : Subgroup ↥Q | Nat.card ↥K = p ^ 2 ∧ Subgroup.center ↥Q ≤ K}.ncard
      ≤ {H : Subgroup X | H ≤ Q ∧ Nat.card ↥H = p ^ 2 ∧ Work.CORE4.centerIn Q ≤ H}.ncard := by
    refine Set.ncard_le_ncard_of_injOn (fun K : Subgroup ↥Q => K.map Q.subtype) ?_ ?_
    · intro K hK
      rw [Set.mem_ofPred_eq] at hK ⊢
      obtain ⟨hKcard, hKcent⟩ := hK
      exact ⟨Subgroup.map_subtype_le K,
        by rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective Q), hKcard],
        by
          show Work.CORE4.centerIn Q ≤ K.map Q.subtype
          rw [show Work.CORE4.centerIn Q = (Subgroup.center ↥Q).map Q.subtype from rfl]
          exact Subgroup.map_mono hKcent⟩
    · exact (Subgroup.map_injective (Subgroup.subtype_injective Q)).injOn
  rw [le_antisymm hA hB, hcount]

end Work.CORE4
