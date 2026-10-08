import Mathlib
import Submission.Work.CORE2A.Defs
import Submission.Work.CORE2A.Basic

namespace Work.CORE2A

/-- The Sylow `2`-subgroup `S` of a minimal counterexample has order `2n ≥ 4`, hence `|G| ≥ 4`;
in particular `|G| ≠ 2`. -/
private theorem card_G_ne_two {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G)
    (n : ℕ) (hn : 2 ≤ n) (hdih : Nonempty ((B.S : Subgroup G) ≃* DihedralGroup n)) :
    Nat.card G ≠ 2 := by
  obtain ⟨e⟩ := hdih
  have hcardS : Nat.card (B.S : Subgroup G) = 2 * n := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hle : Nat.card (B.S : Subgroup G) ≤ Nat.card G := Subgroup.card_le_card_group _
  rw [hcardS] at hle
  omega

/-- A simple group of order `≠ 2` has no normal subgroup of index `2`. -/
private theorem no_normal_index_two {G : Type} [Group G] [Finite G] (hsimple : IsSimpleGroup G)
    (hcard : Nat.card G ≠ 2) : ∀ N : Subgroup G, N.Normal → N.index ≠ 2 := by
  intro N hN hIdx
  have hbot : N ≠ ⊥ := by
    intro h
    rw [h, Subgroup.index_bot] at hIdx
    exact hcard hIdx
  have htop : N ≠ ⊤ := by
    intro h
    rw [h, Subgroup.index_top] at hIdx
    omega
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal G _ hsimple N hN with h | h
  · exact hbot h
  · exact htop h

theorem ncard_involutions_eq_index (T : Work.GW2.LocalToolkit) {G : Type} [Group G] [Finite G]
    (hctx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (n : ℕ) (hn : 2 ≤ n)
    (hdih : Nonempty ((B.S : Subgroup G) ≃* DihedralGroup n)) :
    {x : G | orderOf x = 2}.ncard = B.H.index := by
  classical
  -- `G` is simple of order `≥ 4`, so it has no normal subgroup of index `2`.
  have hNoIndex2 := no_normal_index_two hctx.simple (card_G_ne_two B n hn hdih)
  -- Bender's fusion result: all involutions of `G` are conjugate.
  have hfus : ∀ x y : G, orderOf x = 2 → orderOf y = 2 → IsConj x y :=
    (T.fus G B.S n hn hdih hNoIndex2).1
  -- The set of involutions is exactly the conjugacy class of `t`.
  have hset : {x : G | orderOf x = 2} = conjugatesOf B.t := by
    ext x
    constructor
    · intro hx
      exact (hfus x B.t hx B.t_order).symm
    · intro hx
      change IsConj B.t x at hx
      rw [isConj_iff] at hx
      obtain ⟨c, hc⟩ := hx
      change orderOf x = 2
      rw [← hc, ← MulAut.conj_apply c B.t, MulEquiv.orderOf_eq (MulAut.conj c) B.t, B.t_order]
  rw [hset, ← Subgroup.index_centralizer_eq_ncard B.t]

end Work.CORE2A
