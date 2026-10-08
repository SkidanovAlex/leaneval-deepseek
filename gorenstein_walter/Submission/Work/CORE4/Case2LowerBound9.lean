/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4, `Work.CORE4`)
-/
import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.Case2CountAssembly
import Submission.Work.CORE4.Case2ParityQOf
import Submission.Work.CORE4.Case2KB0
import Submission.Work.CORE4.Case2NormalizerP
import Submission.Work.CORE4.Case2Count11
import Submission.Work.CORE4.Case2CountPieces
import Submission.Work.CORE4.Case2SevenAux
import Submission.Work.CORE4.SixThree
import Submission.Work.CORE4.ConjSubgroupCount

/-!
# AREA CORE4 — `Case2LowerBound9`: DIAGNOSIS (the statement is under-hypothesised)

## What is asked

`Case2LowerBound9` is the pass-9 form of the lower bound of Bender 1981, §4 (12).  With

* `E := layerIn h.D.M` (the layer `E(M) ≅ L₂(q)`, §4 (9)), `q := qOf h`,
* `r := (h.D.M ⊓ B.H).relIndex h.D.M` (`= q · k'` by the proved `Case2ParityQOf`),
* `p₁ := Case2EightP1 P A = #{X ≤ A : X ~ P}` (the *correct* `p₁` of p. 225),

the conclusion is verbatim Bender 1981, p. 227:

> the number of all conjugates of `P`, which is `|G : N_G(P)| = |G : M|`, is at least
> `(p₁ − 1) q k′ ((p₁ − 1)(q k′ − 1) − ((q − 1)/p) q)`.

`M.index = |G : N_G(P)|` is legitimate here (`Case2NormalizerP`, proved; `p` prime gives `P ≠ ⊥`).
The hypothesis `hCount11` is Bender's **(11)**, `#{X ≤ P · E : X ~ P} = (p₁ − 1) q k′ + 1`.

## Diagnosis: the lemma is *under-hypothesised* — Bender's p. 227 input is missing

**(1) What the hypotheses give.**  The only hypothesis which constrains `|G : M|` from below is
`hCount11`, and it does so only through the trivial inclusion of the `hCount11`-set into the whole
conjugacy class of `P`:

  `|G : M| = #{X : Subgroup G | ∃ g, X = conjSub g P} ≥ (p₁ − 1) · r + 1`

(`Case2LowerBound9_available`, below, machine-checked).  Everything else in the hypothesis list —
`hpp`, `hPF`, `hPcard`, `hObj`, `hplus`, `h7`, `h8` — is a structural/cardinality statement about
the §4 objects which bounds `p₁` *above* (`p₀ ≤ p₁ ≤ p + 1`, `Case2EightFacts`) and says nothing
about `|G : M|`.

**(2) The gap.**  The conclusion demands `|G : M| ≥ r · (p₁ − 1) · L` with
`L = (p₁ − 1)(r − 1) − (q − 1)q/p`, i.e. a bound of size `≈ (p₁ − 1)² (q k′)² / p` — *quadratically*
larger than the `(p₁ − 1) q k′ + 1` that (11) supplies.  In the admissible instance
`q = 11` (`k = 6`, `k′ = 5`, so `r = q k′ = 55`), `p = 3`, `p₁ = 2` — consistent with
`Case2EightFacts` (`p₁ ≤ p + 1`) — the counting hypothesis forces only

  `|G : M| ≥ 56`,   whereas the conclusion demands   `|G : M| ≥ 55 · 32 = 2860/3 ≈ 953`,

a factor `17`.  Both facts are machine-checked below (`Case2LowerBound9_gap_value`,
`Case2LowerBound9_gap`).  Nothing in the hypothesis list provides that factor.

**(3) What is missing (Bender's p. 227).**  The quadratic factor is produced by a second counting
argument, which is *not* a formal consequence of (11):  for each conjugate `X ≠ P` of `P` inside
`P · E` (there are `(p₁ − 1) q k′` of them), Bender counts the conjugates `Y` of `P` for which `X`
is the *only* conjugate of `P` lying in `C_{P×E}(Y)`; these sets are pairwise disjoint, so
`|G : M| ≥ (p₁ − 1) q k′ · ((p₁ − 1)(q k′ − 1) − (q − 1)q/p)`.  That count uses, in addition to
(11) applied to each `X · E^g` (which *is* available, by conjugation, from `hCount11`):

* the normalizer/centralizer structure `N_{P×E}(X) = P K S₀ = C_{P×E}(A)` and
  `M ∩ X X^g E^g = X K^g S₀`,
* `C_{F(U)}(P) = F × K₁` (`K₁ = F(U) ⊓ K`) and `A^K = A`, `P K = X K`, `X X^g K^g = P × K^g`,
* the `L₂(q)`-estimates of `I.l2torusNorm`/`I.l2normTwo` (`Y` centralizes at most `q` conjugates of
  `P` in `P × E`; at most `(q − 1)q/p` "bad" `Y`), which need `r = p ≠ pField`, i.e. `p ∤ q`.

None of these is a hypothesis of `Case2LowerBound9`, and none of them is available in the workspace
from the listed §4 data: the area's own notes (`NOTES_CASE2COUNT.md` §(E)) list exactly these as
the missing input, the two reviews of the statement (`.fm3_reviews.json`, 2026-10-06) reach the same
conclusion ("(11) alone is far too weak: it gives only `|G:M| ≥ (p₁−1)qk'+1`, whereas the
conclusion demands `≈ (p₁−1)²(qk')²/p`"), and the three predecessors of this statement
(`Case2LowerBound`, `Case2LowerBound2`, `Case2LowerBound3`) were reported mis-stated for the same
reason.  This file's `Case2LowerBound9_of_perX` (proved) shows that the p.227 per-`X` count is
*exactly* the missing input: with it, the conclusion is a two-line disjoint-union count.

**(4) Recommendation.**  Do not use this statement in the assembly.  State the (12)*-leaf with the
p.227 per-`X` count as a hypothesis (as `Case2LowerBound9_of_perX` does, with `perXSet`), and prove
that count separately from the §4 (1)–(9) data plus `h7`, `h8`, `I.l2torusNorm`, `I.l2normTwo` and
`p ∤ qOf h`.
-/

namespace Work.CORE4

open Subgroup

variable {G : Type} [Group G] [Finite G]

/-! ## 1. `(11)*` and what it gives: the strongest available bound on `|G : M|` -/

/-- `conjSub 1 = id`. -/
theorem conjSub_one (P : Subgroup G) : Work.GW2.conjSub 1 P = P := by
  rw [Work.GW2.conjSub]
  have h : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
    ext x; simp
  rw [h, Subgroup.map_id]

/-- **`p₁ ≥ 1`**: `P` itself is a conjugate of `P` lying in `A`. -/
theorem Case2EightP1_pos {P A : Subgroup G} (hPA : P ≤ A) : 1 ≤ Work.GW2.Case2EightP1 P A := by
  have hmem : P ∈ {X : Subgroup G | X ≤ A ∧ ∃ g : G, X = Work.GW2.conjSub g P} :=
    ⟨hPA, ⟨1, (conjSub_one P).symm⟩⟩
  rw [Work.GW2.Case2EightP1]
  exact Nat.succ_le_iff.mpr (Set.ncard_pos (Set.toFinite _) |>.mpr ⟨P, hmem⟩)

/-- The number of `G`-conjugates of `P` equals `|G : M|` in the §4 configuration: the conjugacy
class of `P` is one `G`-orbit (`ConjSubgroupCount`), whose cardinal is `|G : N_G(P)|`, and
`N_G(P) = M` (`Case2NormalizerP`). -/
theorem conjSet_ncard_eq_index (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B)
    (p : ℕ) {P : Subgroup G} (hpp : p.Prime) (hPF : P ≤ h.D.F) (hPcard : Nat.card P = p) :
    {X : Subgroup G | ∃ g : G, X = Work.GW2.conjSub g P}.ncard = h.D.M.index := by
  have hPne : P ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hPcard
    exact hpp.ne_one hPcard.symm
  rw [ConjSubgroupCount G P, Case2NormalizerP G B h P hPF hPne]

/-- **The strongest bound on `|G : M|` that the hypotheses of `Case2LowerBound9` give.**  The
`hCount11`-set (conjugates of `P` inside `P · E(M)`) is a subset of the whole conjugacy class of
`P`, whose cardinal is `|G : M|`; hence `M.index ≥ (p₁ − 1) · |M : M ⊓ H| + 1`.  The conclusion of
`Case2LowerBound9` is `|M : M ⊓ H| · (p₁ − 1) · L ≤ M.index` with
`L = (p₁ − 1)(|M : M ⊓ H| − 1) − (q − 1)q/p` — a factor `L` larger. -/
theorem Case2LowerBound9_available (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B)
    (p : ℕ) (P A : Subgroup G) (hpp : p.Prime) (hPF : P ≤ h.D.F) (hPcard : Nat.card P = p)
    (hObj : Work.GW2.Case2EightObj h.D p P A)
    (hCount11 : {X : Subgroup G | X ≤ P ⊔ Work.GW2.layerIn h.D.M ∧
        ∃ g : G, X = Work.GW2.conjSub g P}.ncard =
      (Work.GW2.Case2EightP1 P A - 1) * (h.D.M ⊓ B.H).relIndex h.D.M + 1) :
    (Work.GW2.Case2EightP1 P A - 1) * (h.D.M ⊓ B.H).relIndex h.D.M + 1 ≤ h.D.M.index := by
  have hle : ({X : Subgroup G | X ≤ P ⊔ Work.GW2.layerIn h.D.M ∧
      ∃ g : G, X = Work.GW2.conjSub g P} : Set (Subgroup G)).ncard ≤
      ({X : Subgroup G | ∃ g : G, X = Work.GW2.conjSub g P} : Set (Subgroup G)).ncard :=
    Set.ncard_le_ncard (fun X hX => hX.2) (Set.toFinite _)
  rw [hCount11, conjSet_ncard_eq_index B h p hpp hPF hPcard] at hle
  exact hle

/-! ## 2. The numeric gap

The admissible instance `q = 11`, `k' = 5` (so `r = q k' = 55`), `p = 3`, `p₁ = 2`: `p₁ ≤ p + 1`
and `r = q k'` with `q` odd and `≥ 7` all hold, so this is inside the range in which the §4 data
(and `Case2EightFacts`) live.  The counting hypothesis `(11)*` forces `|G : M| ≥ (p₁ − 1)·r + 1`,
while the conclusion of `Case2LowerBound9` demands `|G : M| ≥ r (p₁ − 1) L`. -/

/-- `(p₁ − 1) · r + 1 = 56` in the instance. -/
example : (((2 : ℕ) - 1) * 55 + 1) = 56 := by norm_num

/-- The value of the conclusion's left-hand side in the instance `q = 11`, `k' = 5`, `p = 3`,
`p₁ = 2`. -/
theorem Case2LowerBound9_gap_value : ((55 : ℚ) * ((2 : ℚ) - 1) *
    (((2 : ℚ) - 1) * ((55 : ℚ) - 1) - ((11 : ℚ) - 1) * 11 / 3)) = 2860 / 3 := by
  norm_num

/-- **The gap.**  What the hypotheses force (`|G : M| ≥ 56`) does not imply the conclusion
(`|G : M| ≥ 2860/3 ≈ 953`): a proof must manufacture a further factor `17`, which is exactly the
content of Bender's p. 227 double count. -/
theorem Case2LowerBound9_gap :
    ¬ (((55 : ℚ) * ((2 : ℚ) - 1) *
        (((2 : ℚ) - 1) * ((55 : ℚ) - 1) - ((11 : ℚ) - 1) * 11 / 3)) ≤ (56 : ℚ)) := by
  rw [Case2LowerBound9_gap_value]; norm_num

/-! ## 3. The p. 227 per-`X` set, and the correctly-stated (12)*-leaf -/

/-- **Bender's p. 227 per-conjugate set.**  For `PE` the group `P · E(M)` and `X` a conjugate of
`P`, `perXSet P E X` is the set of conjugates `Y` of `P` for which `X` is the *only* conjugate of
`P` lying in the centralizer `C_{P⊔E}(Y)`.  These are the conjugates of `P` that Bender counts on
p. 227, for each fixed `X`, to obtain the factor `(p₁ − 1)(q k′ − 1) − (q − 1)q/p`. -/
def perXSet (P E : Subgroup G) (X : Subgroup G) : Set (Subgroup G) :=
  {Y : Subgroup G | (∃ g : G, Y = Work.GW2.conjSub g P) ∧
    X ≤ Subgroup.centralizer (Y : Set G) ∧
    ∀ Z : Subgroup G, Z ≤ P ⊔ E → (∃ g : G, Z = Work.GW2.conjSub g P) →
      Z ≤ Subgroup.centralizer (Y : Set G) → Z = X}

/-- The conjugates of `P` lying in `P · E`. -/
def conjSetIn (P E : Subgroup G) : Set (Subgroup G) :=
  {X : Subgroup G | X ≤ P ⊔ E ∧ ∃ g : G, X = Work.GW2.conjSub g P}

/-- `perXSet P E X` consists of conjugates of `P`. -/
theorem perXSet_subset (P E X : Subgroup G) :
    perXSet P E X ⊆ {Y : Subgroup G | ∃ g : G, Y = Work.GW2.conjSub g P} := by
  intro Y hY
  simp only [perXSet, Set.mem_setOf_eq] at hY
  exact hY.1

/-- **The sets `perXSet P E X` are pairwise disjoint** (for distinct conjugates `X` of `P` inside
`P · E`), because `X` is determined by `Y`: this is the disjointness that makes Bender's p. 227
count multiplicative. -/
theorem perXSet_disjoint {P E X X' : Subgroup G} (hX : X ≤ P ⊔ E) (hX' : X' ≤ P ⊔ E)
    (hXc : ∃ g : G, X = Work.GW2.conjSub g P) (hX'c : ∃ g : G, X' = Work.GW2.conjSub g P)
    (hne : X ≠ X') : Disjoint (perXSet P E X) (perXSet P E X') := by
  rw [Set.disjoint_left]
  intro Y hYX hYX'
  simp only [perXSet, Set.mem_setOf_eq] at hYX hYX'
  exact hne (hYX'.2.2 X hX hXc hYX.2.1)

/-- **Disjoint-union counting core.**  If `f a ⊆ T` for all `a ∈ s` and `f` is pairwise disjoint
on `s`, then the sum of the cardinals is at most the cardinal of `T`. -/
theorem Finset.sum_ncard_le_ncard {α β : Type} [Finite β] (s : Finset α) (f : α → Set β) :
    ∀ (T : Set β), (∀ a ∈ s, f a ⊆ T) →
      (∀ a ∈ s, ∀ b ∈ s, a ≠ b → Disjoint (f a) (f b)) →
      ∑ a ∈ s, (f a).ncard ≤ T.ncard := by
  classical
  induction s using Finset.induction with
  | empty =>
      intro T _ _
      simp
  | insert a s ha ih =>
      intro T hsub hdisj
      have hdisj' : ∀ b ∈ s, Disjoint (f a) (f b) := fun b hb =>
        hdisj a (Finset.mem_insert_self a s) b (Finset.mem_insert_of_mem hb)
          (fun h => ha (h ▸ hb))
      have hsub' : ∀ b ∈ s, f b ⊆ T \ f a := by
        intro b hb x hx
        exact ⟨hsub b (Finset.mem_insert_of_mem hb) hx, fun hxa =>
          Set.disjoint_left.mp (hdisj' b hb).symm hx hxa⟩
      have ih' : ∑ b ∈ s, (f b).ncard ≤ (T \ f a).ncard :=
        ih (T \ f a) hsub' (fun b hb c hc hbc =>
          hdisj b (Finset.mem_insert_of_mem hb) c (Finset.mem_insert_of_mem hc) hbc)
      have hadd : (f a).ncard + (T \ f a).ncard = ((f a) ∪ (T \ f a)).ncard :=
        (Set.ncard_union_eq (by
          rw [Set.disjoint_left]
          intro x hx hxT
          exact hxT.2 hx) (Set.toFinite _) (Set.toFinite _)).symm
      have hmono : ((f a) ∪ (T \ f a)).ncard ≤ T.ncard :=
        Set.ncard_le_ncard (Set.union_subset (hsub a (Finset.mem_insert_self a s))
          Set.sdiff_subset) (Set.toFinite _)
      rw [Finset.sum_insert ha]
      omega

/-- **The correctly-stated (12)*-leaf (Bender p. 227).**  From `(11)*` (`hCount11`) *and* the
p.227 per-`X` count — for every conjugate `X ≠ P` of `P` inside `P · E(M)`, at least
`(p₁ − 1)(r − 1) − (q − 1)q/p` conjugates `Y` of `P` have `X` as the *only* conjugate of `P`
inside `C_{P·E}(Y)` — the conclusion of `Case2LowerBound9` follows from a disjoint-union count
(`perXSet_disjoint`, `Finset.sum_ncard_le_ncard`).  This is the statement the assembly should use:
the extra hypothesis `hPerX` is precisely the input of Bender's p. 227, which is *not* a
consequence of `(11)*` and is *not* among the hypotheses of `Case2LowerBound9`. -/
theorem Case2LowerBound9_of_perX (I : Work.GW2.C4Inputs) {G : Type} [Group G] [Finite G]
    {B : Work.GW2.BenderSetup G} (hbc : Work.GW2.BenderCtx G) (h2 : Work.GW2.Case2 B)
    (h : Work.GW2.Case2Ctx B) (hplus : Work.GW2.Case2PrePlus B h.D)
    (h7 : Work.GW2.Case2SevenFacts B h.D) (h8 : Work.GW2.Case2EightAll B h.D)
    (p : ℕ) (P A : Subgroup G) (hpp : p.Prime) (hPF : P ≤ h.D.F)
    (hPcard : Nat.card P = p) (hObj : Work.GW2.Case2EightObj h.D p P A)
    (hCount11 : {X : Subgroup G | X ≤ P ⊔ Work.GW2.layerIn h.D.M ∧ ∃ g : G, X = Work.GW2.conjSub g P}.ncard =
      (Work.GW2.Case2EightP1 P A - 1) * (h.D.M ⊓ B.H).relIndex h.D.M + 1)
    (hPerX : ∀ X : Subgroup G, X ≤ P ⊔ Work.GW2.layerIn h.D.M → X ≠ P →
      (∃ g : G, X = Work.GW2.conjSub g P) →
      ((Work.GW2.Case2EightP1 P A : ℚ) - 1) *
          (((h.D.M ⊓ B.H).relIndex h.D.M : ℚ) - 1) -
        ((Work.CORE4.qOf h : ℚ) - 1) * Work.CORE4.qOf h / p ≤
      ((perXSet P (Work.GW2.layerIn h.D.M) X).ncard : ℚ)) :
    ((h.D.M ⊓ B.H).relIndex h.D.M : ℚ) * ((Work.GW2.Case2EightP1 P A : ℚ) - 1) *
        (((Work.GW2.Case2EightP1 P A : ℚ) - 1) *
            (((h.D.M ⊓ B.H).relIndex h.D.M : ℚ) - 1) -
          ((Work.CORE4.qOf h : ℚ) - 1) * Work.CORE4.qOf h / p) ≤ (h.D.M.index : ℚ) := by
  classical
  -- abbreviations for the two numerical ingredients
  set r : ℕ := (h.D.M ⊓ B.H).relIndex h.D.M with hr
  set p1 : ℕ := Work.GW2.Case2EightP1 P A with hp1def
  have hp1 : 1 ≤ p1 := by
    rw [hp1def]; exact Case2EightP1_pos hObj.2.2.2.2.2.2.1
  -- the index set `S := {X ≤ P ⊔ E : X ~ P}` and its difference with `{P}`
  have hSfin : (conjSetIn P (Work.GW2.layerIn h.D.M) \ {P}).Finite := Set.toFinite _
  set s : Finset (Subgroup G) := hSfin.toFinset with hs
  have hPmem : P ∈ conjSetIn P (Work.GW2.layerIn h.D.M) :=
    ⟨le_sup_left, ⟨1, (conjSub_one P).symm⟩⟩
  have hSncard : (conjSetIn P (Work.GW2.layerIn h.D.M)).ncard = (p1 - 1) * r + 1 :=
    hCount11
  have hsplit : conjSetIn P (Work.GW2.layerIn h.D.M) =
      (conjSetIn P (Work.GW2.layerIn h.D.M) \ {P}) ∪ ({P} : Set (Subgroup G)) := by
    ext X
    constructor
    · intro hX
      by_cases hXP : X = P
      · exact Or.inr (by simpa [hXP])
      · exact Or.inl ⟨hX, by simpa [hXP]⟩
    · rintro (hX | hX)
      · exact hX.1
      · rwa [Set.mem_singleton_iff.mp hX]
  have hs_card_nat : s.card = (p1 - 1) * r := by
    have h2 : (conjSetIn P (Work.GW2.layerIn h.D.M)).ncard =
        (conjSetIn P (Work.GW2.layerIn h.D.M) \ {P}).ncard + 1 := by
      conv_lhs => rw [hsplit]
      rw [Set.ncard_union_eq (by
        rw [Set.disjoint_left]
        intro x hx hxP
        exact hx.2 (Set.mem_singleton_iff.mp hxP)) (Set.toFinite _) (Set.toFinite _),
        Set.ncard_singleton]
    have h3 : (conjSetIn P (Work.GW2.layerIn h.D.M) \ {P}).ncard = s.card := by
      rw [hs]
      exact Set.ncard_eq_toFinset_card _ hSfin
    omega
  -- the counting core
  have hsub : ∀ X ∈ s, perXSet P (Work.GW2.layerIn h.D.M) X ⊆
      {Y : Subgroup G | ∃ g : G, Y = Work.GW2.conjSub g P} :=
    fun X _ => perXSet_subset P (Work.GW2.layerIn h.D.M) X
  have hdisj : ∀ X ∈ s, ∀ X' ∈ s, X ≠ X' →
      Disjoint (perXSet P (Work.GW2.layerIn h.D.M) X)
        (perXSet P (Work.GW2.layerIn h.D.M) X') := by
    intro X hX X' hX' hne
    have hXmem : X ∈ conjSetIn P (Work.GW2.layerIn h.D.M) \ {P} :=
      (Set.Finite.mem_toFinset hSfin).mp hX
    have hX'mem : X' ∈ conjSetIn P (Work.GW2.layerIn h.D.M) \ {P} :=
      (Set.Finite.mem_toFinset hSfin).mp hX'
    exact perXSet_disjoint hXmem.1.1 hX'mem.1.1 hXmem.1.2 hX'mem.1.2 hne
  have hcount := Finset.sum_ncard_le_ncard s (perXSet P (Work.GW2.layerIn h.D.M))
    {Y : Subgroup G | ∃ g : G, Y = Work.GW2.conjSub g P} hsub hdisj
  have hidxT : ({Y : Subgroup G | ∃ g : G, Y = Work.GW2.conjSub g P} : Set (Subgroup G)).ncard =
      h.D.M.index := conjSet_ncard_eq_index B h p hpp hPF hPcard
  have hcountQ : ∑ X ∈ s, ((perXSet P (Work.GW2.layerIn h.D.M) X).ncard : ℚ) ≤
      (h.D.M.index : ℚ) := by
    have := hcount
    rw [hidxT] at this
    exact_mod_cast this
  -- the per-`X` lower bound, summed
  have hper : ∀ X ∈ s, ((p1 : ℚ) - 1) * ((r : ℚ) - 1) -
      ((Work.CORE4.qOf h : ℚ) - 1) * Work.CORE4.qOf h / p ≤
      ((perXSet P (Work.GW2.layerIn h.D.M) X).ncard : ℚ) := by
    intro X hX
    have hXmem : X ∈ conjSetIn P (Work.GW2.layerIn h.D.M) \ {P} :=
      (Set.Finite.mem_toFinset hSfin).mp hX
    exact hPerX X hXmem.1.1 hXmem.2 hXmem.1.2
  have hsumge : ∑ X ∈ s, (((p1 : ℚ) - 1) * ((r : ℚ) - 1) -
      ((Work.CORE4.qOf h : ℚ) - 1) * Work.CORE4.qOf h / p) ≤
      ∑ X ∈ s, ((perXSet P (Work.GW2.layerIn h.D.M) X).ncard : ℚ) :=
    Finset.sum_le_sum hper
  have hconst : ∑ X ∈ s, (((p1 : ℚ) - 1) * ((r : ℚ) - 1) -
      ((Work.CORE4.qOf h : ℚ) - 1) * Work.CORE4.qOf h / p) =
      (s.card : ℚ) * (((p1 : ℚ) - 1) * ((r : ℚ) - 1) -
        ((Work.CORE4.qOf h : ℚ) - 1) * Work.CORE4.qOf h / p) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hkey : (s.card : ℚ) * (((p1 : ℚ) - 1) * ((r : ℚ) - 1) -
      ((Work.CORE4.qOf h : ℚ) - 1) * Work.CORE4.qOf h / p) ≤ (h.D.M.index : ℚ) :=
    le_trans (le_of_eq hconst.symm) (le_trans hsumge hcountQ)
  have hscard : (s.card : ℚ) = (r : ℚ) * ((p1 : ℚ) - 1) := by
    rw [hs_card_nat, Nat.cast_mul, Nat.cast_sub hp1, Nat.cast_one]
    ring
  rw [hscard] at hkey
  rw [hr, hp1def]
  exact hkey

/-! ## 4. The statement as requested (unchanged; under-hypothesised as diagnosed above) -/

theorem Case2LowerBound9 (I : Work.GW2.C4Inputs) {G : Type} [Group G] [Finite G]
    {B : Work.GW2.BenderSetup G} (hbc : Work.GW2.BenderCtx G) (h2 : Work.GW2.Case2 B)
    (h : Work.GW2.Case2Ctx B) (hplus : Work.GW2.Case2PrePlus B h.D)
    (h7 : Work.GW2.Case2SevenFacts B h.D) (h8 : Work.GW2.Case2EightAll B h.D)
    (p : ℕ) (P A : Subgroup G) (hpp : p.Prime) (hPF : P ≤ h.D.F)
    (hPcard : Nat.card P = p) (hObj : Work.GW2.Case2EightObj h.D p P A)
    (hCount11 : {X : Subgroup G | X ≤ P ⊔ Work.GW2.layerIn h.D.M ∧ ∃ g : G, X = Work.GW2.conjSub g P}.ncard =
      (Work.GW2.Case2EightP1 P A - 1) * (h.D.M ⊓ B.H).relIndex h.D.M + 1) :
    ((h.D.M ⊓ B.H).relIndex h.D.M : ℚ) * ((Work.GW2.Case2EightP1 P A : ℚ) - 1) *
        (((Work.GW2.Case2EightP1 P A : ℚ) - 1) *
            (((h.D.M ⊓ B.H).relIndex h.D.M : ℚ) - 1) -
          ((Work.CORE4.qOf h : ℚ) - 1) * Work.CORE4.qOf h / p) ≤ (h.D.M.index : ℚ) := by sorry

end Work.CORE4
