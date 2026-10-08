import Mathlib
import Submission.Work.RED.Basic
import Submission.Work.RED.OddCoreFacts

namespace Work.RED

open Subgroup

/-- **`Work.RED.CyclicSylowQuotient`**: a finite group whose Sylow `2`-subgroup is cyclic has
`2`-group quotient `G / O(G)`.

This is Burnside's normal `2`-complement theorem in the cyclic Sylow case.  Since `2 = |G|.minFac`
and a cyclic Sylow `p`-subgroup `P` with `p = |G|.minFac` satisfies `P ≤ Z(N_G(P))`, the transfer
`G →* P` is defined; its kernel `K` is a normal `2`-complement of `P`, hence of odd order
(`[G : K] = |P|` is a power of `2`), so `K ≤ O(G)`.  Therefore `|G/O(G)|` divides `[G : K] = |P|`,
a power of `2`.  When `|G|` is odd, `O(G) = ⊤` and the quotient is trivial. -/
theorem CyclicSylowQuotient (G : Type) [Group G] [Finite G] (P : Sylow 2 G)
    (hP : IsCyclic ↥(P : Subgroup G)) : IsPGroup 2 (G ⧸ Work.RED.GW2.oddCore G) := by
  by_cases h2 : 2 ∣ Nat.card G
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hminfac : (Nat.card G).minFac = 2 := Nat.minFac_eq_two_iff _ |>.mpr h2
    -- The transfer `G →* P`; the hypothesis `P ≤ Z(N_G(P))` comes from cyclicity of `P`.
    let K : Subgroup G := (MonoidHom.transferSylow P (hP.normalizer_le_centralizer hminfac)).ker
    have hKcompl : K.IsComplement' (P : Subgroup G) := hP.isComplement' hminfac
    have hKn : K.Normal := MonoidHom.normal_ker _
    -- `K` has odd order, because `[G : K] = |P|` is a power of `2`.
    have hKodd : Odd (Nat.card K) := by
      rw [← hKcompl.index_eq_card]
      exact Nat.not_even_iff_odd.mp fun he => P.not_dvd_index (even_iff_two_dvd.mp he)
    -- hence `K ≤ O(G)`, so `|G/O(G)|` divides `|G/K| = |P| = 2 ^ n`.
    have hKle : K ≤ GW2.oddCore G := GW2.le_oddCore_of_odd_normal hKn hKodd
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (P.isPGroup' : IsPGroup 2 ↥(P : Subgroup G))
    refine IsPGroup.of_card_dvd_pow (n := n) ?_
    calc Nat.card (G ⧸ Work.RED.GW2.oddCore G)
        = (GW2.oddCore G).index := (Subgroup.index_eq_card (GW2.oddCore G)).symm
      _ ∣ K.index := Subgroup.index_dvd_of_le hKle
      _ = Nat.card ↥(P : Subgroup G) := hKcompl.symm.index_eq_card
      _ = 2 ^ n := hn
  · -- `|G|` odd: `O(G) = ⊤` and `G/O(G)` is trivial.
    have hodd : Odd (Nat.card G) := Nat.not_even_iff_odd.mp fun he => h2 (even_iff_two_dvd.mp he)
    have htop : Work.RED.GW2.oddCore G = ⊤ := GW2.eq_top_of_odd hodd
    have hcard : Nat.card (G ⧸ Work.RED.GW2.oddCore G) = 1 := by
      rw [htop, ← Subgroup.index_eq_card (⊤ : Subgroup G), Subgroup.index_top]
    refine IsPGroup.of_card (p := 2) (n := 0) ?_
    rw [hcard]
    norm_num

end Work.RED
