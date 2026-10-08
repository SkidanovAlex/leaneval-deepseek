import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.StageA.coarseFrame_exists
import Submission.Work.ThmF.ChV12.lemma6
import Submission.Work.PSU3.StageA.caseC_W_semireg
import Submission.Work.PSU3.StageA.caseC_data

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageB.StepB

/-!
# `Work.PSU3.StageB.StepB.exists_generating_frame` — Peterfalvi II, Ch. VII §2: a frame whose
`ζ` generates `W`

Peterfalvi's Ch. VII §2 (p. 270) fixes `ζ` to be a **generator** of `W = C_V(K)` and uses
`m = |W| = o(ζ)` throughout.  A given `CoarseFrame` may carry a non-generating `ζ`, so every
consumer that needs `o(ζ) = |W|` (or `W ≤ KW`) must be allowed to *replace* the frame.

This file proves exactly that: from the case-c data of Peterfalvi II, Ch. VI §1
(`|Q| = |Q₀|³`, `o(s t) = 3`, `s, r` as in Ch. V §2 Lemma 1 b)) `W` is cyclic
(`Work.ThmF.ChV12.lemma6`), so it has a generator `ζ₀` with `⟨ζ₀⟩ = W` and `o(ζ₀) = |W|`;
`Work.PSU3.StageA.coarseFrame_exists` applied to `ζ₀` builds a frame `fr'` with `fr'.ζ = ζ₀`
at some `n'`, and `n' = n` because both `2 ^ n` and `2 ^ n'` are the cardinality of `Q₀`.
The conclusion `W ≤ fr'.KW` is then immediate from `W = ⟨ζ₀⟩ = ⟨fr'.ζ⟩ ≤ fr'.KW`.
-/

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

/-- **A nontrivial cyclic group has a generator of maximal order.**  If `N ≤ G` is cyclic and
`N ≠ ⊥`, there is `g ∈ N` with `⟨g⟩ = N`, `g ≠ 1` and `orderOf g = |N|`. -/
lemma exists_zpowers_eq_of_isCyclic {G : Type} [Group G] {N : Subgroup G} (hne : N ≠ ⊥)
    (hcyc : IsCyclic ↥N) :
    ∃ g : G, g ∈ N ∧ Subgroup.zpowers g = N ∧ g ≠ 1 ∧ orderOf g = Nat.card ↥N := by
  classical
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hgen : Subgroup.zpowers (g : G) = N := by
    refine le_antisymm (Subgroup.zpowers_le.mpr g.2) ?_
    intro y hy
    have hy' : (⟨y, hy⟩ : ↥N) ∈ Subgroup.zpowers g := hg _
    rw [Subgroup.mem_zpowers_iff] at hy' ⊢
    obtain ⟨k, hk⟩ := hy'
    exact ⟨k, by simpa using congrArg (fun z : ↥N => (z : G)) hk⟩
  have hord : orderOf (g : G) = Nat.card ↥N := by
    simpa using orderOf_eq_card_of_forall_mem_zpowers (α := ↥N) (g := g) hg
  refine ⟨(g : G), g.2, hgen, ?_, hord⟩
  intro h1
  exact hne (by rw [← hgen, h1, Subgroup.zpowers_eq_bot])

/-- A `CoarseFrame` carries a nontrivial element of `W = C_V(K)` (`fr.ζ`), so `W ≠ ⊥`. -/
lemma W_ne_bot_of_frame {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}
    (fr : Work.PSU3.CoarseFrame H Q t n) : Work.ThmF.W H t ≠ ⊥ := by
  intro hbot
  have hmem : (fr.ζ : G) ∈ (⊥ : Subgroup G) := hbot ▸ fr.ζ_mem_W
  exact fr.ζ_ne_one (Subtype.ext (Subgroup.mem_bot.mp hmem))

theorem exists_generating_frame {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hHig : Submission.Blueprint.HigmanProp) (fr : Work.PSU3.CoarseFrame H Q t n)
    (hcard3 : Nat.card ↥Q = Nat.card ↥(Work.ThmF.Q0sub H) ^ 3)
    (hQ0pow : Nat.card ↥(Work.ThmF.Q0sub H) = 2 ^ n)
    {s r : G} (hs : s ∈ Q) (hs2 : orderOf s = 2) (hr : r ∈ Q) (hsr : t * s * t = r⁻¹ * t * r)
    (h3 : orderOf (s * t) = 3) :
    ∃ fr' : Work.PSU3.CoarseFrame H Q t n,
      orderOf (fr'.ζ : G) = Nat.card ↥(Work.ThmF.W H t) ∧ Work.ThmF.W H t ≤ fr'.KW := by
  classical
  -- ## Step 1: the data of Ch. V §2 Lemma 1 b) give the hypotheses of Lemma 5, hence the
  -- structure identity `t s t = s t s`.
  have h5 : Work.ThmF.Lemma5.Hyp5 H Q t s := ⟨hS.situation, hS.split, hs, hs2, h3⟩
  have hst : t * s * t = s * t * s := Work.ThmF.Lemma5.tst_eq_sts h5
  -- ## Step 2: `W ≠ ⊥`, because the frame carries the nontrivial element `fr.ζ ∈ W`.
  have hWne : Work.ThmF.W H t ≠ ⊥ := W_ne_bot_of_frame fr
  -- ## Step 3: `Q` is a Suzuki 2-group.  `W ≠ ⊥` forces `Q` to be non-abelian, and then the
  -- Suzuki structure is `caseC_isSuzuki2Grp` (Higman's notion, `Submission.Blueprint`).
  have hnab : ¬ Submission.Blueprint.IsAbelianSubgroup Q :=
    Work.PSU3.StageA.not_abelian_of_W_ne_bot hS hC4 hWne
  have hZ : ∀ x : ↥Q, (x : G) ∈ Work.ThmF.Q0sub H ↔ x * x = 1 :=
    Work.PSU3.StageA.caseC_Q0sub_subgroupOf_iff_sq hS hC4
  have hSuz2 : Work.Higman.IsSuzuki2Grp ↥Q :=
    Work.PSU3.StageA.caseC_isSuzuki2Grp hS hC4 hnab hZ hWne
  have hSuz : Submission.Blueprint.IsSuzukiTwoGroup ↥Q :=
    Work.Higman.isSuzukiTwoGroup_iff_nonempty_isSuzuki2Grp.mpr ⟨hSuz2⟩
  -- ## Step 4: `W` is cyclic (Peterfalvi II, Ch. V §2 Lemma 6).
  have hcyc : IsCyclic ↥(Work.ThmF.W H t) :=
    (Work.ThmF.ChV12.lemma6 hC4 hHig h5 hSuz hcard3).1
  -- ## Step 5: choose a generator `ζ₀` of `W`.
  obtain ⟨ζ₀, hζ₀W, hζ₀gen, hζ₀ne, hζ₀ord⟩ := exists_zpowers_eq_of_isCyclic hWne hcyc
  -- ## Step 6: a frame whose `ζ` is `ζ₀` (Stage A's construction, at some `n'`).
  obtain ⟨n', -, hcardn', fr', -, hζ'⟩ :=
    Work.PSU3.StageA.coarseFrame_exists hS hC4 hHig hs hs2 hr hsr hst hcard3 hζ₀W hζ₀ne
  -- ## Step 7: `n' = n`, since both `2 ^ n'` and `2 ^ n` are `|Q₀|`.
  have hn : n' = n :=
    Nat.pow_right_injective (le_refl 2) (hcardn'.symm.trans hQ0pow)
  subst hn
  -- ## Step 8: the conclusions.
  refine ⟨fr', ?_, ?_⟩
  · rw [hζ', hζ₀ord]
  · rw [← hζ₀gen, Subgroup.zpowers_le, ← hζ']
    exact fr'.ζ.2

end Work.PSU3.StageB.StepB
