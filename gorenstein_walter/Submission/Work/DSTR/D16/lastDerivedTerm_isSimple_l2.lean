import Mathlib
import Submission.Work.ASM.Defs

/-!
# The last term of the derived series of `Ḡ` in the `L₂(q)`-case of Bender 1.6

This module proves `Work.DSTR.D16.lastDerivedTerm_isSimple_l2`, the group-theoretic input
used in `Submission/Work/DSTR/D16/case34.lean` (Bender 1.6, cases `X/O(X) ≅ A₇` and the
`L₂(q)`/`PGL₂(q)` case).

## Setting and statement

`Q` is a finite group, `Ġ ◁ Q` is a nontrivial, non-solvable normal subgroup, and `L ◁ Q`
is a normal subgroup of odd index admitting a simple, perfect subgroup `P = ⁅L, L⁆` of
index at most two in `L`.  Writing `S := (derivedSeries ↥Ġ m).map Ġ.subtype` for the image in
`Q` of the `m`-th derived subgroup of `Ġ`, with `m ≥ |Q|`, the claim is that `S` is simple.

## Proof

Since the derived series of a finite group of order `≤ m` has stabilised by index `m`, the
subgroup `S` is *perfect*, `⁅S, S⁆ = S`, and `S` is nontrivial (as `Ġ` is not solvable).

* `S ≤ L`.  `Q ⧸ L` has odd order, hence is solvable by Feit–Thompson; the image of the
  perfect group `S` in the solvable group `Q ⧸ L` is perfect and solvable, hence trivial.
* `S ≤ P`.  By `P = ⁅L, L⁆` and `S = ⁅S, S⁆ ≤ ⁅L, L⁆`.
* `P ≤ Ġ`.  `Ġ ⊓ P ◁ P` is either `⊥` or `P`; if it were `⊥` then
  `S ≤ Ġ ⊓ P = ⊥`, contradicting `S ≠ ⊥`.  Hence `P ≤ Ġ`.
* `P ≤ S`.  Every subgroup `R ≤ Ġ` with `⁅R, R⁆ = R` is contained in every term of the
  derived series of `Ġ`, in particular in `S`; apply this to `P`.

Thus `S = P` is simple.

Note: the hypotheses `hne`, `hPL` and `hidx` are not needed for the argument, but they are
part of the requested statement and are kept verbatim.
-/

namespace Work.DSTR.D16

open Subgroup

/-- A group that is both perfect and solvable is trivial. -/
theorem subsingleton_of_isPerfect_of_isSolvable {G : Type} [Group G]
    [Group.IsPerfect G] [Group.IsSolvable G] : Subsingleton G := by
  by_contra h
  haveI : Nontrivial G := not_subsingleton_iff_nontrivial.mp h
  exact (Group.IsPerfect.not_isSolvable G) inferInstance

/-- If `N ◁ G` has solvable quotient `G ⧸ N` and `S ≤ G` is perfect (`⁅S, S⁆ = S`), then
`S ≤ N`: the image of `S` in `G ⧸ N` is perfect (quotient of a perfect group) and solvable
(subgroup of a solvable group), hence trivial. -/
theorem subgroup_le_of_isPerfect_of_isSolvable_quotient {G : Type} [Group G]
    {N S : Subgroup G} [N.Normal] [Group.IsSolvable (G ⧸ N)] (hS : ⁅S, S⁆ = S) : S ≤ N := by
  haveI : Group.IsPerfect ↥(S.map (QuotientGroup.mk' N)) := by
    rw [Subgroup.isPerfect_iff, ← Subgroup.map_commutator, hS]
  haveI : Group.IsSolvable ↥(S.map (QuotientGroup.mk' N)) := inferInstance
  haveI : Subsingleton ↥(S.map (QuotientGroup.mk' N)) := subsingleton_of_isPerfect_of_isSolvable
  have hbot : S.map (QuotientGroup.mk' N) = ⊥ := Subgroup.eq_bot_of_subsingleton _
  rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot

/-- The derived series of a finite group of order at most `m` has stabilised by index `m`:
`derivedSeries G m = derivedSeries G (m+1)`. -/
theorem derivedSeries_eq_succ_of_card_le (G : Type) [Group G] [Finite G] (m : ℕ)
    (hm : Nat.card G ≤ m) : derivedSeries G m = derivedSeries G (m + 1) := by
  by_contra hne
  have hstrict : ∀ n, n ≤ m → derivedSeries G (n + 1) < derivedSeries G n := by
    intro n hn
    refine lt_of_le_of_ne (derivedSeries_antitone G (Nat.le_succ n)) ?_
    intro heq
    have hconst : ∀ j, n + 1 ≤ j → derivedSeries G j = derivedSeries G (n + 1) := by
      intro j hj
      induction j, hj using Nat.le_induction with
      | base => rfl
      | succ j hj ih =>
        calc derivedSeries G (j + 1) = ⁅derivedSeries G j, derivedSeries G j⁆ :=
              derivedSeries_succ G j
          _ = ⁅derivedSeries G (n + 1), derivedSeries G (n + 1)⁆ := by rw [ih]
          _ = ⁅derivedSeries G n, derivedSeries G n⁆ := by rw [← heq]
          _ = derivedSeries G (n + 1) := (derivedSeries_succ G n).symm
    rcases lt_or_eq_of_le hn with hlt | heqnm
    · exact hne ((hconst m (by omega)).trans (hconst (m + 1) (by omega)).symm)
    · exact hne (Eq.symm (heqnm ▸ heq))
  have hcard : ∀ n, n ≤ m → Nat.card (derivedSeries G (n + 1)) < Nat.card (derivedSeries G n) :=
    fun n hn => Subgroup.card_lt_of_lt (hstrict n hn)
  have hiter : ∀ k, k ≤ m + 1 →
      Nat.card (derivedSeries G k) + k ≤ Nat.card (derivedSeries G 0) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have h2 := hcard k (by omega)
      omega
  have hpos : 1 ≤ Nat.card (derivedSeries G (m + 1)) :=
    Nat.card_pos_iff.mpr ⟨⟨1, (derivedSeries G (m + 1)).one_mem⟩, inferInstance⟩
  have hfin := hiter (m + 1) le_rfl
  have h0 : Nat.card (derivedSeries G 0) = Nat.card G := by
    rw [derivedSeries_zero G, Subgroup.card_top]
  omega

/-- If `P ≤ H` and `P` is perfect (`⁅P, P⁆ = P`), then `P` lies in every term of the derived
series of `H` (mapped into the ambient group). -/
theorem le_map_derivedSeries_of_commutator_eq_self {Q : Type} [Group Q] {H P : Subgroup Q}
    (hPH : P ≤ H) (hP : ⁅P, P⁆ = P) (n : ℕ) :
    P ≤ (derivedSeries ↥H n).map H.subtype := by
  induction n with
  | zero =>
    rw [derivedSeries_zero, Subgroup.map_top, Subgroup.range_subtype]
    exact hPH
  | succ n ih =>
    rw [derivedSeries_succ, Subgroup.map_commutator]
    exact le_trans (le_of_eq hP.symm) (Subgroup.commutator_mono ih ih)

set_option linter.unusedVariables false in
/-- **The last term of the derived series of `Ḡ` is simple** (the `L₂(q)`/`PGL₂(q)` case of
Bender 1.6).  See the module docstring for the proof. -/
theorem lastDerivedTerm_isSimple_l2 (Q : Type) [Group Q] [Finite Q] {Ġ : Subgroup Q} [Ġ.Normal] (hne : Ġ ≠ ⊥) (hns : ¬ Group.IsSolvable ↥Ġ) (hFT : Work.GW2.FeitThompsonProp) {L P : Subgroup Q} (hL : L.Normal) (hodd : Odd L.index) (hPL : P ≤ L) (hPeq : P = ⁅L, L⁆) (hidx : (P.subgroupOf L).index ≤ 2) (hPsimple : IsSimpleGroup ↥P) (hPperf : Group.IsPerfect ↥P) (m : ℕ) (hm : Nat.card Q ≤ m) : IsSimpleGroup ↥((derivedSeries ↥Ġ m).map Ġ.subtype) := by
  haveI := hL
  -- `P = ⁅L, L⁆` is normal in `Q`.
  have hPnormal : P.Normal := by rw [hPeq]; exact Subgroup.commutator_normal L L
  haveI := hPnormal
  -- `Q ⧸ L` has odd order, hence is solvable by Feit–Thompson.
  have hsolL : Group.IsSolvable (Q ⧸ L) :=
    hFT (Q ⧸ L) (Subgroup.index_eq_card L ▸ hodd)
  haveI := hsolL
  -- `S` is the image in `Q` of the `m`-th derived subgroup of `Ġ`.
  set S : Subgroup Q := (derivedSeries ↥Ġ m).map Ġ.subtype with hSdef
  have hSleĠ : S ≤ Ġ := Subgroup.map_subtype_le _
  -- `S` is nontrivial, since `Ġ` is not solvable.
  have hSne : S ≠ ⊥ := by
    intro hSbot
    apply hns
    rw [Group.isSolvable_def]
    refine ⟨m, ?_⟩
    have hinj := Subgroup.map_injective (f := Ġ.subtype) (Subgroup.subtype_injective Ġ)
    refine hinj ?_
    rw [← hSdef, hSbot, Subgroup.map_bot]
  -- The derived series of `Ġ` has stabilised, so `S` is perfect.
  have hstab : derivedSeries ↥Ġ m = derivedSeries ↥Ġ (m + 1) :=
    derivedSeries_eq_succ_of_card_le ↥Ġ m (le_trans (Subgroup.card_le_card_group Ġ) hm)
  have hSperf : ⁅S, S⁆ = S := by
    rw [hSdef, ← Subgroup.map_commutator, ← derivedSeries_succ, ← hstab]
  -- `S ≤ L`, because the image of the perfect group `S` in the solvable group `Q ⧸ L` is
  -- perfect and solvable, hence trivial.
  have hSleL : S ≤ L := subgroup_le_of_isPerfect_of_isSolvable_quotient hSperf
  -- `S ≤ P = ⁅L, L⁆`.
  have hSleP : S ≤ P := by
    rw [hPeq]
    exact le_trans (le_of_eq hSperf.symm) (Subgroup.commutator_mono hSleL hSleL)
  -- `P ≤ Ġ`, because `Ġ ⊓ P ◁ P` is `⊥` or `P`, and `⊥` is impossible as `S ≤ Ġ ⊓ P`.
  have hPleĠ : P ≤ Ġ := by
    haveI : (Ġ.subgroupOf P).Normal := (inferInstance : Ġ.Normal).subgroupOf P
    rcases hPsimple.eq_bot_or_eq_top_of_normal (Ġ.subgroupOf P) with h | h
    · exfalso
      have hd : Disjoint (Ġ : Subgroup Q) P := Subgroup.subgroupOf_eq_bot.mp h
      have hle : S ≤ (⊥ : Subgroup Q) :=
        le_trans (le_inf hSleĠ hSleP) (le_of_eq (disjoint_iff.mp hd))
      exact hSne (le_bot_iff.mp hle)
    · exact Subgroup.subgroupOf_eq_top.mp h
  -- `P ≤ S`, since `P` is perfect.
  have hPleS : P ≤ S := by
    rw [hSdef]
    exact le_map_derivedSeries_of_commutator_eq_self hPleĠ (Subgroup.isPerfect_iff.mp hPperf) m
  have hSP : S = P := le_antisymm hSleP hPleS
  rw [hSP]
  exact hPsimple

end Work.DSTR.D16
