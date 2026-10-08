import Mathlib
import Submission.Work.RED.Defs

/-!
# `O(G) = 1` and cyclic Sylow 2-subgroups imply solvability

Use Burnside's normal `p`-complement theorem in its cyclic-Sylow form (Mathlib's
`IsCyclic.isComplement'`, which is Isaacs' Corollary 5.14: a Sylow `p`-subgroup `P` with
`p = |G|.minFac` cyclic has a normal complement): if all Sylow 2-subgroups of a finite group
`G` are cyclic, then `G` has a normal `2`-complement `K`, necessarily of odd order.  If in
addition `O(G) = 1`, then `K ≤ O(G) = 1`, so the Sylow 2-subgroup is all of `G`, `G` is a
`2`-group, and `G` is solvable.

Note that `O(G) = 1` with `G ≠ 1` forces `|G|` to be even, so the smallest-prime hypothesis
of the transfer theorem is automatic.
-/

namespace Work.RED

/-- **Universal property of the odd core.** A normal subgroup of odd order is contained in
`O(G) = O_{2'}(G)`, the largest normal subgroup of odd order. -/
theorem le_oddCore_of_odd_normal {G : Type*} [Group G] {N : Subgroup G} [N.Normal]
    (hN : Odd (Nat.card N)) : N ≤ GW2.oddCore G :=
  Subgroup.normal_le_normalCore.mpr (le_sSup ⟨‹N.Normal›, hN⟩)

theorem isSolvable_of_forall_sylow_two_isCyclic
    {N : Type*} [Group N] [Finite N]
    (hO : Work.RED.GW2.oddCore N = ⊥)
    (hcyc : ∀ P : Sylow 2 N, IsCyclic ↥(P : Subgroup N)) :
    Group.IsSolvable N := by
  by_cases htriv : Nat.card N = 1
  · haveI : Subsingleton N := (Nat.card_eq_one_iff_unique.mp htriv).1
    infer_instance
  · -- `O(N) = ⊥` and `N ≠ 1` force `|N|` even: otherwise `⊤` is a normal odd subgroup.
    have h2dvd : 2 ∣ Nat.card N := by
      by_contra h2
      have hodd : Odd (Nat.card N) :=
        Nat.not_even_iff_odd.mp fun he => h2 (even_iff_two_dvd.mp he)
      have htop : (⊤ : Subgroup N) ≤ GW2.oddCore N :=
        le_oddCore_of_odd_normal (N := ⊤) (by rw [Subgroup.card_top]; exact hodd)
      rw [hO, le_bot_iff] at htop
      exact htriv (by rw [← Subgroup.card_top (G := N), htop, Subgroup.card_bot])
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hminfac : (Nat.card N).minFac = 2 := Nat.minFac_eq_two_iff _ |>.mpr h2dvd
    obtain ⟨P⟩ := Sylow.nonempty (p := 2) (G := N)
    -- Burnside's transfer: the kernel `K` of the transfer is a normal complement of `P`.
    let K : Subgroup N :=
      (MonoidHom.transferSylow P ((hcyc P).normalizer_le_centralizer hminfac)).ker
    have hKcompl : K.IsComplement' (P : Subgroup N) :=
      IsCyclic.isComplement' hminfac (hcyc P)
    -- `K` has odd order ...
    have hKodd : Odd (Nat.card K) := by
      rw [← hKcompl.index_eq_card]
      exact Nat.not_even_iff_odd.mp fun he => P.not_dvd_index (even_iff_two_dvd.mp he)
    -- ... hence `K ≤ O(N) = ⊥` ...
    have hKbot : K = ⊥ := by
      haveI : K.Normal := MonoidHom.normal_ker _
      exact le_bot_iff.mp (hO ▸ le_oddCore_of_odd_normal hKodd)
    -- ... so `P = ⊤`, and `N` is a 2-group, hence nilpotent and solvable.
    have hPtop : (P : Subgroup N) = ⊤ := by
      have h := hKcompl.sup_eq_top
      rwa [hKbot, bot_sup_eq] at h
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp P.isPGroup'
    have hcard : Nat.card N = 2 ^ k := by
      rw [← Subgroup.card_top (G := N), ← hPtop]
      exact hk
    haveI : Group.IsNilpotent N := IsPGroup.isNilpotent (IsPGroup.of_card hcard)
    exact IsNilpotent.to_isSolvable

end Work.RED
