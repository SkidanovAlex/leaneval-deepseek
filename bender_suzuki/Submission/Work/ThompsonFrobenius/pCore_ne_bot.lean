import Mathlib
import Submission.Work.ThompsonFrobenius.GTDefs
import Submission.Work.ThompsonFrobenius.npc_of_le
import Submission.Work.ThompsonFrobenius.npc_normalizer_of_not_normal
import Submission.Work.ThompsonFrobenius.Prelim
import Submission.Work.ThompsonFrobenius.ZJ_subgroupOf
import Submission.Work.ThompsonFrobenius.ZJ_ne_bot
import Submission.Work.ThompsonFrobenius.normalizer_le_normalizer_ZJ
import Submission.Work.ThompsonFrobenius.hasNormalPComplement_normalizer_subgroupOf

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# GT-1 (Thompson's Step One): `O_p(G) ≠ 1` (area `ThompsonFrobenius`)

Step GT-1 of `NOTES_LEAD_bs_thompson.md`, following Farris §3.4 Step One but with GT-d replacing
the second maximality.

Let `G` be a minimal counterexample to the Glauberman–Thompson theorem with Sylow `p`-subgroup `P`.

1. By the contrapositive of Frobenius' criterion (`Work.NPC.Frobenius.npc_of_normalizer_npc`) there
   is a `p`-subgroup `H ≠ 1` whose normalizer has no normal `p`-complement ("bad").
2. Choose a pair `(H, R)` with `H` bad and `R` a `p`-subgroup of `N_G(H)`, maximising `|R|`
   (`Nat.findGreatest` over the bounded set of possible orders).  Conjugating the pair
   (`exists_map_conj_le_sylow`), we may assume `R ≤ P`; badness is conjugacy-invariant
   (`hasNormalPComplement_normalizer_map_conj_iff`).
3. If `R = P`, then `P ≤ N_G(H)` and GT-d (`npc_normalizer_of_not_normal`) shows that `H` is
   normal, whence `H ≤ O_p(G) ≠ 1`.
4. If `R < P`, then `N_P(R)` is a strictly larger `p`-subgroup of `N_G(ZJ(R))`
   (`lt_normalizer_of_lt_of_isPGroup`, `normalizer_le_normalizer_ZJ`); maximality forces
   `N_G(ZJ(R))` to have a normal `p`-complement, hence so does `N_{N_G(H)}(ZJ(R))`.  Also `R` has
   the order of a Sylow `p`-subgroup of `N_G(H)` (compare with any Sylow by maximality), so the
   induction hypothesis `h.ih` applied to `↥N_G(H)` gives a normal `p`-complement of `N_G(H)`,
   contradicting its badness.  If instead `N_G(H) = G`, then `H ⊴ G` and we are done directly.
-/

set_option autoImplicit false

open scoped Pointwise

namespace Work.ThompsonFrobenius

theorem pCore_ne_bot {p : ℕ} {G : Type} [Group G] [Finite G] {P : Sylow p G}
    (h : GTMinimal p G P) : Work.HallHigman.pCore p G ≠ ⊥ := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  classical
  -- Step 1: Frobenius' criterion produces a "bad" `p`-subgroup.
  have hex : ∃ H : Subgroup G, IsPGroup p H ∧ H ≠ ⊥ ∧
      ¬ Work.NPC.HasNormalPComplement p ↥(Subgroup.normalizer (H : Set G)) := by
    by_contra hcon
    refine h.not_npc (Work.NPC.Frobenius.npc_of_normalizer_npc h.prime ?_)
    intro Q hQ hQne
    by_contra hbad
    exact hcon ⟨Q, hQ, hQne, hbad⟩
  -- Step 2: choose a pair `(H, R)` maximising `|R|`.
  let Sset : ℕ → Prop := fun n => ∃ (W R : Subgroup G), IsPGroup p W ∧ W ≠ ⊥ ∧
      ¬ Work.NPC.HasNormalPComplement p ↥(Subgroup.normalizer (W : Set G)) ∧
      IsPGroup p R ∧ R ≤ Subgroup.normalizer (W : Set G) ∧ Nat.card ↥R = n
  have hSne : ∃ n, n ≤ Nat.card G ∧ Sset n := by
    obtain ⟨H, hHp, hHne, hHbad⟩ := hex
    exact ⟨Nat.card ↥H, Subgroup.card_le_card_group H, H, H, hHp, hHne, hHbad, hHp,
      Subgroup.le_normalizer, rfl⟩
  obtain ⟨m, hmle, hSm⟩ := hSne
  obtain ⟨H, R, hHp, hHne, hHbad, hRp, hRle, hRcardEq⟩ := Nat.findGreatest_spec hmle hSm
  -- maximality of `|R|`
  have hmax : ∀ (W R' : Subgroup G), IsPGroup p W → W ≠ ⊥ →
      ¬ Work.NPC.HasNormalPComplement p ↥(Subgroup.normalizer (W : Set G)) →
      IsPGroup p R' → R' ≤ Subgroup.normalizer (W : Set G) →
      Nat.card ↥R' ≤ Nat.card ↥R := by
    intro W R' hWp hWne hWbad hR'p hR'le
    rw [hRcardEq]
    exact Nat.le_findGreatest (Subgroup.card_le_card_group R')
      ⟨W, R', hWp, hWne, hWbad, hR'p, hR'le, rfl⟩
  -- Step 3: conjugate the pair so that `R ≤ P`.
  obtain ⟨k, hk⟩ := exists_map_conj_le_sylow hRp P
  set H' : Subgroup G := H.map (MulAut.conj k).toMonoidHom with hH'def
  set R' : Subgroup G := R.map (MulAut.conj k).toMonoidHom with hR'def
  have hinj : Function.Injective (MulAut.conj k).toMonoidHom := (MulAut.conj k).injective
  have hH'p : IsPGroup p H' := by rw [hH'def]; exact IsPGroup.map hHp _
  have hH'ne : H' ≠ ⊥ := by
    rw [hH'def]
    intro hbot
    rw [Subgroup.map_eq_bot_iff] at hbot
    exact hHne (le_bot_iff.mp
      (hbot.trans (le_of_eq ((MonoidHom.ker_eq_bot_iff _).mpr hinj))))
  have hH'bad : ¬ Work.NPC.HasNormalPComplement p ↥(Subgroup.normalizer (H' : Set G)) := by
    rw [hH'def]
    exact fun hc => hHbad ((hasNormalPComplement_normalizer_map_conj_iff k).mp hc)
  have hR'p : IsPGroup p R' := by rw [hR'def]; exact IsPGroup.map hRp _
  have hR'le : R' ≤ Subgroup.normalizer (H' : Set G) := by
    rw [hH'def, hR'def]
    refine (Subgroup.map_mono (f := (MulAut.conj k).toMonoidHom) hRle).trans ?_
    rw [Subgroup.map_equiv_normalizer_eq H (MulAut.conj k)]
  have hR'leP : R' ≤ (P : Subgroup G) := hk
  have hR'card : Nat.card ↥R' = Nat.card ↥R := by
    rw [hR'def]; exact Subgroup.card_map_of_injective hinj
  have hmax' : ∀ (W R'' : Subgroup G), IsPGroup p W → W ≠ ⊥ →
      ¬ Work.NPC.HasNormalPComplement p ↥(Subgroup.normalizer (W : Set G)) →
      IsPGroup p R'' → R'' ≤ Subgroup.normalizer (W : Set G) →
      Nat.card ↥R'' ≤ Nat.card ↥R' := by
    intro W R'' hWp hWne hWbad hR''p hR''le
    rw [hR'card]
    exact hmax W R'' hWp hWne hWbad hR''p hR''le
  -- Step 4: `R'` has the order of a Sylow `p`-subgroup of `N_G(H')`.
  let N' : Subgroup G := Subgroup.normalizer (H' : Set G)
  let H'L : Subgroup ↥N' := H'.subgroupOf N'
  let R'L : Subgroup ↥N' := R'.subgroupOf N'
  have hH'leN' : H' ≤ N' := Subgroup.le_normalizer
  have hH'Lp : IsPGroup p H'L :=
    IsPGroup.of_equiv hH'p (Subgroup.subgroupOfEquivOfLe hH'leN').symm
  have hR'Lp : IsPGroup p R'L :=
    IsPGroup.of_equiv hR'p (Subgroup.subgroupOfEquivOfLe hR'le).symm
  obtain ⟨S, hSle⟩ := hR'Lp.exists_le_sylow
  have hSGp : IsPGroup p (S.map N'.subtype) := S.isPGroup'.map N'.subtype
  have hSGle : S.map N'.subtype ≤ N' := Subgroup.map_subtype_le _
  have hSGcard : Nat.card ↥(S.map N'.subtype) ≤ Nat.card ↥R' :=
    hmax' H' (S.map N'.subtype) hH'p hH'ne hH'bad hSGp hSGle
  have hScard : Nat.card ↥(S : Subgroup ↥N') = Nat.card ↥(S.map N'.subtype) :=
    (Subgroup.card_map_of_injective (f := N'.subtype) (K := (S : Subgroup ↥N'))
      N'.subtype_injective).symm
  have hH'Lcard : Nat.card ↥H' = Nat.card ↥H'L :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH'leN').toEquiv).symm
  have hH'Lcard_le : Nat.card ↥H'L ≤ Nat.card ↥S :=
    card_le_card_sylow_of_isPGroup hH'Lp S
  have hH'card_le : Nat.card ↥H' ≤ Nat.card ↥R' :=
    calc Nat.card ↥H' = Nat.card ↥H'L := hH'Lcard
      _ ≤ Nat.card ↥S := hH'Lcard_le
      _ = Nat.card ↥(S.map N'.subtype) := hScard
      _ ≤ Nat.card ↥R' := hSGcard
  -- `R'` is nontrivial, because it is at least as large as `H' ≠ ⊥`.
  have hR'ne : R' ≠ ⊥ := by
    intro hbot
    rw [hbot] at hH'card_le
    have hb : Nat.card ↥(⊥ : Subgroup G) = 1 := Subgroup.card_eq_one.mpr rfl
    rw [hb] at hH'card_le
    have hlt : 1 < Nat.card ↥H' := (Subgroup.one_lt_card_iff_ne_bot H').mpr hH'ne
    omega
  have hR'Lcard : Nat.card ↥R'L = Nat.card ↥R' :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR'le).toEquiv
  have hSeq : R'L = (S : Subgroup ↥N') := by
    refine Subgroup.eq_of_le_of_card_ge hSle ?_
    rw [hR'Lcard, hScard]
    exact hSGcard
  -- Step 5: the conclusion.
  by_cases hRP : R' = (P : Subgroup G)
  · have hPN : (P : Subgroup G) ≤ Subgroup.normalizer (H' : Set G) := hRP ▸ hR'le
    by_cases hHnorm : H'.Normal
    · intro hbot
      exact hH'ne (le_bot_iff.mp (hbot ▸ Work.HallHigman.le_pCore hHnorm
        (isPiNat_card_of_isPGroup hH'p)))
    · exact absurd (npc_normalizer_of_not_normal h hH'p hPN hHnorm) hH'bad
  · -- `R' < P`: `ZJ(R')` has `p`-nilpotent normalizer by maximality.
    have hR'ltP : R' < (P : Subgroup G) := lt_of_le_of_ne hR'leP hRP
    have hltN : R' < Subgroup.normalizer (R' : Set G) ⊓ (P : Subgroup G) :=
      Work.NPC.Frobenius.lt_normalizer_of_lt_of_isPGroup (P := (P : Subgroup G))
        (A := R') P.isPGroup' hR'ltP
    let W : Subgroup G := Submission.Blueprint.ZJ R'
    have hWp : IsPGroup p W := isPGroup_of_le hR'p (ZJ_le R')
    have hWne : W ≠ ⊥ := ZJ_ne_bot hR'p hR'ne
    have hWnotbad : Work.NPC.HasNormalPComplement p ↥(Subgroup.normalizer (W : Set G)) := by
      by_contra hbad
      have hNPRp : IsPGroup p ↥(Subgroup.normalizer (R' : Set G) ⊓ (P : Subgroup G)) :=
        isPGroup_of_le P.isPGroup'
          (show Subgroup.normalizer (R' : Set G) ⊓ (P : Subgroup G) ≤ (P : Subgroup G)
            from inf_le_right)
      have hNPRle : Subgroup.normalizer (R' : Set G) ⊓ (P : Subgroup G) ≤
          Subgroup.normalizer (W : Set G) :=
        le_trans inf_le_left (normalizer_le_normalizer_ZJ R')
      have hcard := hmax' W _ hWp hWne hbad hNPRp hNPRle
      have hlt := Subgroup.card_lt_of_lt hltN
      omega
    have hinner : Work.NPC.HasNormalPComplement p
        ↥(Subgroup.normalizer (Submission.Blueprint.ZJ R'L : Set ↥N')) := by
      rw [ZJ_subgroupOf hR'le]
      exact hasNormalPComplement_normalizer_subgroupOf (le_trans (ZJ_le R') hR'le) hWnotbad
    by_cases hN'top : N' = ⊤
    · have hHnorm : H'.Normal := Subgroup.normalizer_eq_top_iff.mp hN'top
      intro hbot
      exact hH'ne (le_bot_iff.mp (hbot ▸ Work.HallHigman.le_pCore hHnorm
        (isPiNat_card_of_isPGroup hH'p)))
    · have hcard : Nat.card ↥N' < Nat.card G := by
        have hlt : N' < ⊤ := lt_top_iff_ne_top.mpr hN'top
        have hc := Subgroup.card_lt_of_lt (H := N') (K := ⊤) hlt
        rwa [Subgroup.card_top] at hc
      refine absurd (h.ih ↥N' hcard S ?_) hH'bad
      rw [← hSeq]
      exact hinner

end Work.ThompsonFrobenius
