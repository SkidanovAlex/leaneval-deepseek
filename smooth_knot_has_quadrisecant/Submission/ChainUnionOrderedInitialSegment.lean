import Mathlib
import Submission.OneManifold
import Submission.RealIntervalShape
import Submission.Commons.Topology.Exhaustion.chain_initialSegments_union_homeo

open Set
open scoped Topology

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

/-!
# S217 — ordered initial-segment chains: the data format of the
exhaustion-to-interval assembly (module
Submission/ChainUnionOrderedInitialSegment.lean)

Per the S216 analysis (Finding A), the exhaustion-to-interval assembly of
the interval side needs its data in the CANONICAL LENGTH FORM: an
exhaustion of `X` by nested open sets `range (i n)` where each
`i n : (0, L n) → X` is an injective continuous open embedding of the
real interval `(0, L n)` with `0 < L n ≤ L (n+1) ≤ 1`, the embeddings
AGREE on the common coordinate value (`i n t = i (n+1) t` as real
coordinates — each `range (i n)` sits in `range (i (n+1))` as the
initial segment `(0, L n)` of its coordinate), and the ranges cover `X`.
(S216 showed the naive "same coordinate `(0,1)` for every level" is
impossible under strict growth; the growing intervals are the fix.)

This module is the verified data-format layer of that assembly:

1. **real ordered initial segments**: `Ioo0_subset_of_le` /
   `Ioo0_mem_of_le` — `(0,L) ⊆ (0,L')` for `L ≤ L'`; `reEmbedIoo0` — the
   subtype re-embedding `(0,L) ↪ (0,L')` (identity on the real value);
   `L_mono_of_le` — a stepwise-monotone length family is monotone;
   `agree_chain` — consecutive coordinate agreement implies agreement
   across any `n ≤ m` (`i n = i m ∘ reEmbed` — the well-definedness
   spine of the assembly);
2. **the limit interval**: `sSup_rangeL_pos` / `sSup_rangeL_le_one`
   (`0 < sSup (range L) ≤ 1` from `0 < L n ≤ 1`),
   `union_Ioo_zero_range_eq` — `⋃ n, Ioo 0 (L n) = Ioo 0 (sSup (range L))`
   (a monotone chain of initial segments fills the limit interval),
   `exists_lt_of_mem_Ioo_zero_sSup` — membership gives the witnessing
   index;
3. **T1 (real model of the one-sided terminal attachment)** — the
   terminal-extension arithmetic that the per-level growth step uses:
   `terminalStrip_inter` (`Ioo 0 1 ∩ Ioo a b = Ioo a 1` for
   `0 < a < 1 ≤ b`: the new arc's overlap with the prefix is exactly the
   terminal strip `(a,1)` of the prefix coordinate),
   `terminalStrip_union` (`Ioo 0 1 ∪ Ioo a b = Ioo 0 b`: the union is
   the extended interval — the `P ∪ V` real model),
   `terminalStrip_subset` / `beyond_end_nonempty` (the new arc reaches
   beyond the terminal end: `(Ioo a b) ∖ Ioo 0 1 ≠ ∅` for `1 < b`),
   `terminalStrip_arc` (the new interval is `≃ₜ (0,1)`); the ABSTRACT
   glue that consumes exactly this data is already verified:
   `OverlapConn.terminalTwoChart_union_is_openInterval` (S207) and
   `OverlapConn.chain_step_prefix_interval_of_terminal` (S208);
4. **the assembly** (PROVED by the fleet as the commons theorem
   `Commons.Topology.Exhaustion.chain_initialSegments_union_homeo`,
   L35, committed this session; imported here): `X` as in (1) is
   `≃ₜ (0, sSup (range L))`; the corollary
   **`chain_initialSegments_union_homeo_openUnit`** composes that with
   `RealIntervalShape.homeo_Ioo_openUnit` to `X ≃ₜ OpenRealInterval 0 1`
   — the exact conclusion the S206 gate needs.

Honest status (S106 discipline): the genuinely open part of the interval
side is unchanged — PRODUCING such ordered-initial-segment data for the
trisecant components (the ordering / per-level terminal attachment
analysis, T1-abstract/T2 of ROADMAP S216/S217); this module makes the
data format precise, verifies its real-coordinate content, and provides
the final assembly hop that consumes the data (verified here: section
4, `chain_initialSegments_union_homeo_openUnit`).  No `sorry` in this
module.
-/

/-! ## 1. Real ordered initial segments and the agreement chain -/

/-- `(0,L) ⊆ (0,L')` for `L ≤ L'`. -/
lemma Ioo0_subset_of_le {L L' : ℝ} (h : L ≤ L') : Set.Ioo 0 L ⊆ Set.Ioo 0 L' := by
  intro t ht
  exact ⟨ht.1, lt_of_lt_of_le ht.2 h⟩

/-- Membership transfer `t ∈ (0,L) → t ∈ (0,L')` for `L ≤ L'`. -/
lemma Ioo0_mem_of_le {L L' : ℝ} (h : L ≤ L') {t : ℝ} (ht : t ∈ Set.Ioo 0 L) :
    t ∈ Set.Ioo 0 L' :=
  Ioo0_subset_of_le h ht

/-- The subtype re-embedding `(0,L) ↪ (0,L')` for `L ≤ L'` (identity on the
real value) — how a point of the `L`-level interval sits in the `L'`-level
interval as an initial segment. -/
def reEmbedIoo0 {L L' : ℝ} (h : L ≤ L') : {t : ℝ // t ∈ Set.Ioo 0 L} →
    {t : ℝ // t ∈ Set.Ioo 0 L'} :=
  fun t => ⟨t.1, Ioo0_mem_of_le h t.2⟩

/-- The value of a re-embedding is the same real. -/
lemma reEmbedIoo0_val {L L' : ℝ} (h : L ≤ L') (t : {t : ℝ // t ∈ Set.Ioo 0 L}) :
    (reEmbedIoo0 h t : ℝ) = t.1 := rfl

/-- A stepwise monotone length family is monotone. -/
lemma L_mono_of_le {L : ℕ → ℝ} (hmono : ∀ n, L n ≤ L (n + 1)) : Monotone L :=
  monotone_nat_of_le_succ hmono

/-- **The agreement chain**: if the level-`n` coordinate embedding agrees with
the level-`(n+1)` one on the common real value (consecutive agreement), then it
agrees across any `n ≤ m` (`i n t = i m (reEmbed t)`) — the well-definedness
spine of the assembly: any point of the `n`-level range has the same real
coordinate at every later level. -/
lemma agree_chain {X : Type*} {L : ℕ → ℝ} (hmono : ∀ n, L n ≤ L (n + 1))
    (i : ∀ n, {t : ℝ // t ∈ Set.Ioo 0 (L n)} → X)
    (hagree : ∀ n, ∀ t : {t : ℝ // t ∈ Set.Ioo 0 (L n)},
      i n t = i (n + 1) (reEmbedIoo0 (hmono n) t)) :
    ∀ {n m : ℕ} (hnm : n ≤ m), ∀ t : {t : ℝ // t ∈ Set.Ioo 0 (L n)},
      i n t = i m (reEmbedIoo0 (L_mono_of_le hmono hnm) t) := by
  classical
  intro n m hnm t
  -- the re-embedding across `hnm` is value-identity: strip it by congrArg+Subtype.ext
  induction m with
  | zero =>
      have hnm' : n = 0 := by omega
      subst hnm'
      symm
      apply congrArg (i 0)
      apply Subtype.ext
      rfl
  | succ m ih =>
      by_cases hnm' : n ≤ m
      · calc
          i n t = i m (reEmbedIoo0 (L_mono_of_le hmono hnm') t) := ih hnm'
          _ = i (m + 1) (reEmbedIoo0 (hmono m) (reEmbedIoo0 (L_mono_of_le hmono hnm') t)) :=
              hagree m (reEmbedIoo0 (L_mono_of_le hmono hnm') t)
          _ = i (m + 1) (reEmbedIoo0 (L_mono_of_le hmono hnm) t) := by
              apply congrArg (i (m + 1))
              apply Subtype.ext
              rfl
      · have hEq : n = m + 1 := by omega
        subst hEq
        symm
        apply congrArg (i (m + 1))
        apply Subtype.ext
        rfl

/-! ## 2. The limit interval `(0, sSup (range L))` -/

/-- `0 < sSup (range L)` when every `L n > 0` and `L` is bounded above. -/
lemma sSup_rangeL_pos {L : ℕ → ℝ} (hpos : ∀ n, 0 < L n) (hbdd : BddAbove (Set.range L)) :
    0 < sSup (Set.range L) := by
  have hsge : L 0 ≤ sSup (Set.range L) := le_csSup hbdd ⟨0, rfl⟩
  exact lt_of_lt_of_le (hpos 0) hsge

/-- `sSup (range L) ≤ 1` when every `L n ≤ 1`. -/
lemma sSup_rangeL_le_one {L : ℕ → ℝ} (hle : ∀ n, L n ≤ 1)
    (hbdd : BddAbove (Set.range L)) : sSup (Set.range L) ≤ 1 :=
  csSup_le ⟨L 0, ⟨0, rfl⟩⟩ (by rintro y ⟨n, rfl⟩; exact hle n)

/-- `BddAbove (range L)` from the uniform bound `L n ≤ 1`. -/
lemma sSup_rangeL_bdd {L : ℕ → ℝ} (hle : ∀ n, L n ≤ 1) : BddAbove (Set.range L) :=
  ⟨1, by rintro y ⟨n, rfl⟩; exact hle n⟩

/-- **The monotone chain of initial segments fills the limit interval**:
`⋃ n, (0, L n) = (0, sSup (range L))` for a positive bounded chain.
(Monotonicity is not needed for the set equality — only positivity and
boundedness.) -/
lemma union_Ioo_zero_range_eq {L : ℕ → ℝ} (hpos : ∀ n, 0 < L n)
    (hbdd : BddAbove (Set.range L)) :
    (⋃ n : ℕ, Set.Ioo 0 (L n)) = Set.Ioo 0 (sSup (Set.range L)) := by
  ext t
  constructor
  · intro ht
    rcases Set.mem_iUnion.mp ht with ⟨n, htn⟩
    have hsge : L n ≤ sSup (Set.range L) := le_csSup hbdd ⟨n, rfl⟩
    exact ⟨htn.1, lt_of_lt_of_le htn.2 hsge⟩
  · intro ht
    have hne : (Set.range L).Nonempty := ⟨L 0, ⟨0, rfl⟩⟩
    rcases exists_lt_of_lt_csSup hne ht.2 with ⟨v, ⟨n, rfl⟩, hlt⟩
    exact Set.mem_iUnion.mpr ⟨n, ht.1, hlt⟩

/-- Membership of `t` in the limit interval gives a witnessing level
(`∃ n, t.1 < L n`). -/
lemma exists_lt_of_mem_Ioo_zero_sSup {L : ℕ → ℝ} (hpos : ∀ n, 0 < L n)
    (hbdd : BddAbove (Set.range L)) {t : ℝ} (ht : t ∈ Set.Ioo 0 (sSup (Set.range L))) :
    ∃ n : ℕ, t < L n := by
  have hne : (Set.range L).Nonempty := ⟨L 0, ⟨0, rfl⟩⟩
  rcases exists_lt_of_lt_csSup hne ht.2 with ⟨v, ⟨n, rfl⟩, hlt⟩
  exact ⟨n, hlt⟩

/-! ## 3. T1 (real model): the one-sided terminal attachment step -/

/-- **Terminal strip identity**: an arc `(a,b)` with `0 < a < 1 ≤ b` meets the
unit-interval prefix `(0,1)` in exactly the terminal strip `(a,1)` of its
coordinate — the real model of `hVend` (`V ∩ P =` terminal interval of `P`). -/
lemma terminalStrip_inter {a b : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hb1 : 1 ≤ b) :
    Set.Ioo 0 1 ∩ Set.Ioo a b = Set.Ioo a 1 := by
  ext t
  constructor
  · rintro ⟨ht1, htb⟩
    exact ⟨htb.1, ht1.2⟩
  · intro hta
    constructor
    · exact ⟨ha0.trans hta.1, hta.2⟩
    · exact ⟨hta.1, lt_of_lt_of_le hta.2 hb1⟩

/-- **Terminal extension union**: prefix `(0,1)` and the beyond-the-end arc
`(a,b)` (`0 < a < 1 ≤ b`) glue to the extended interval `(0,b)` — the real
model of `P ∪ V` after a one-sided terminal attachment. -/
lemma terminalStrip_union {a b : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hb1 : 1 ≤ b) :
    Set.Ioo 0 1 ∪ Set.Ioo a b = Set.Ioo 0 b := by
  ext t
  constructor
  · rintro (ht1 | htb)
    · exact ⟨ht1.1, lt_of_lt_of_le ht1.2 hb1⟩
    · exact ⟨lt_trans ha0 htb.1, htb.2⟩
  · intro htb
    by_cases ht1 : t < 1
    · exact Or.inl ⟨htb.1, ht1⟩
    · right
      exact ⟨lt_of_lt_of_le ha1 (le_of_not_gt ht1), htb.2⟩

/-- The terminal strip `(a,1)` sits inside the prefix `(0,1)` (for `0 < a`). -/
lemma terminalStrip_subset {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    Set.Ioo a 1 ⊆ Set.Ioo 0 1 := by
  intro t ht
  exact ⟨lt_trans ha0 ht.1, ht.2⟩

/-- The beyond-the-end part is nonempty for a genuine extension (`1 < b`). -/
lemma beyond_end_nonempty {a b : ℝ} (ha1 : a < 1) (h1b : 1 < b) :
    (Set.Ioo a b \ Set.Ioo 0 1).Nonempty := by
  refine ⟨(1 + b) / 2, ?_, ?_⟩
  · constructor
    · linarith
    · linarith
  · intro hb1
    have hb' : b < 1 := by nlinarith [hb1.2]
    linarith

/-- The new arc `(a,b)` (`0 < a`, `a < b`) is homeomorphic to the open unit
interval — it is itself an arc. -/
lemma terminalStrip_arc {a b : ℝ} (ha0 : 0 < a) (hab : a < b) :
    Nonempty ({t : ℝ // t ∈ Set.Ioo a b} ≃ₜ OpenRealInterval 0 1) :=
  homeo_Ioo_openUnit a b hab

/-- The extended prefix `(0,b)` (`1 < b`) is homeomorphic to the open unit
interval. -/
lemma extendedPrefix_arc {b : ℝ} (h0b : 0 < b) :
    Nonempty ({t : ℝ // t ∈ Set.Ioo 0 b} ≃ₜ OpenRealInterval 0 1) :=
  homeo_Ioo_openUnit 0 b h0b



/-! ## 4. The assembly corollary (consumes the commons theorem) -/

/-- **The exhaustion-to-interval assembly in ORI form**: if `X` is
exhausted by the nested agreeing open images of the `(0, L n)`-embeddings
`i n` (canonical length-form data of the S216 Finding-A format), then
`X ≃ₜ OpenRealInterval 0 1` — the exact conclusion the S206 interval-side
gate `TrisecantComponentIntervalSide` needs.  Proof: the commons
assembly `Commons.Topology.Exhaustion.chain_initialSegments_union_homeo`
(L35) gives `X ≃ₜ (0, sSup (range L))`; composing with
`RealIntervalShape.homeo_Ioo_openUnit 0 (sSup (range L))`
(`0 < sSup` by `sSup_rangeL_pos`) yields `X ≃ₜ (0,1)`. -/
theorem chain_initialSegments_union_homeo_openUnit {X : Type*} [TopologicalSpace X]
    [Nonempty X]
    (L : ℕ → ℝ) (hLpos : ∀ n, 0 < L n) (hLmono : ∀ n, L n ≤ L (n + 1))
    (hLle1 : ∀ n, L n ≤ 1)
    (i : ∀ n, {t : ℝ // t ∈ Set.Ioo 0 (L n)} → X)
    (hiCont : ∀ n, Continuous (i n))
    (hiInj : ∀ n, Function.Injective (i n))
    (hiOpenMap : ∀ n, ∀ U : Set {t : ℝ // t ∈ Set.Ioo 0 (L n)}, IsOpen U →
      IsOpen (i n '' U))
    (hiAgree : ∀ n, ∀ t : {t : ℝ // t ∈ Set.Ioo 0 (L n)},
      i n t = i (n + 1) ⟨t.1, ⟨t.2.1, lt_of_lt_of_le t.2.2 (hLmono n)⟩⟩)
    (hiCover : ∀ x : X, ∃ n, ∃ t : {t : ℝ // t ∈ Set.Ioo 0 (L n)}, i n t = x) :
    Nonempty (OpenRealInterval 0 1 ≃ₜ X) := by
  let S : ℝ := sSup (Set.range L)
  have hSpos : 0 < S := sSup_rangeL_pos hLpos (sSup_rangeL_bdd hLle1)
  rcases Commons.Topology.Exhaustion.chain_initialSegments_union_homeo
      (X := X) L hLpos hLmono hLle1 i hiCont hiInj hiOpenMap hiAgree hiCover with ⟨e⟩
  rcases homeo_Ioo_openUnit 0 S hSpos with ⟨f⟩
  exact ⟨f.symm.trans e⟩


