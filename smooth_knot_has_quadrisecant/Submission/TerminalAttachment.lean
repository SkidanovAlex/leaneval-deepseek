import Mathlib
import Submission.OneManifold
import Submission.OverlapConn
import Submission.RealIntervalShape

open Set
open scoped Topology

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

/-!
# S218 — T1-abstract: the one-step attaching-arc construction (module
Submission/TerminalAttachment.lean) — statement + verified core

Per the ROADMAP S216/S217 status, the remaining real content of the
interval side is PRODUCING the ordered-initial-segment data for a
trisecant component: the ordering / per-level one-sided terminal
attachment.  This module opens the T1-abstract slice: the ONE-STEP
attaching-arc construction at the ends of a proper arc prefix, and the
observation that the obstruction (the two-sided wrap closing into a
circle) is excluded in a non-compact ambient.

**Target statements (records; the geometric proof is the open content —
no `sorry` here).**

1. **`TerminalAttach P V κ s`** — the attaching DATA: `V` meets the open
   arc prefix `P` (chart `κ : (0,1) ≃ P`) exactly over the TERMINAL
   interval `(s,1)` of the prefix coordinate (`0 < s < 1` and the
   membership iff of the engine's `hVend`).  With this data the verified
   S207 glue applies: **`glue_of_TerminalAttach`** — open arcs `P`, `V`
   with interval charts and `TerminalAttach` data glue to an interval
   arc (restatement of
   `OverlapConn.terminalTwoChart_union_is_openInterval`).  So the whole
   one-step extension is reduced to PRODUCING an open arc `V` with the
   `TerminalAttach` data (and `V ∖ P ≠ ∅`);

2. **`OneStepTerminalExtension P κ`** — the one-step OUTPUT: for a
   PROPER open arc prefix `P` (`IsOpen P`, `P ≠ univ`) there is an open
   arc `V` attaching over a terminal interval and genuinely extending
   (`V ∖ P ≠ ∅`).  The ambient theorem — "every proper open arc prefix
   of a connected non-compact 1-manifold admits a one-step terminal
   extension" (the T1-abstract content; `S209.TerminalExtensionExists`
   is its O-side avatar) — is the next goal;

3. **`TwoSidedStripCover P V κ`** — the two-sided WRAP data: `V`
   contains both the initial strip `(0,a)` and the terminal strip
   `(b,1)` of `P`'s coordinate (`0 < a < b < 1`) — the necessary form
   of an overlap meeting `P` at BOTH ends (a genuine two-sided overlap
   of an arc prefix by an arc; a connected one-sided attachment only
   ever covers one end strip);

4. **`TwoSidedClosedWrap P κ`** — the wrap CLOSES: `V` is an open arc
   with `TwoSidedStripCover` data AND `P ∪ V = univ` (the prefix and the
   attaching arc jointly cover the whole ambient, as when an arc closes
   around a circle).

**Verified core (the real-coordinate model of why the wrap is excluded
in the line).**

- **`preconnected_overlap_with_unit`** — every open arc of the REAL
  LINE meets the unit prefix `(0,1)` in a connected set (whatever its
  position): shape-classify the arc (`Ioo`/`Ioi`/`Iio`/`univ`), rewrite
  the intersection to an open interval via `max_lt_iff`/`lt_min_iff`,
  and read off `isPreconnected_Ioo`.  I.e. a genuine two-sided
  (disconnected, both-end) overlap can never occur between intervals of
  ℝ — it is intrinsically a CIRCULAR phenomenon;
- **`twoSidedStrip_forces_cover_unit`** — the punchline: if the real
  arc `V` contains BOTH end strips of the unit prefix
  (`(0,a) ∪ (b,1) ⊆ V`, `0 < a < b < 1`), then `V` must contain the
  WHOLE prefix `(0,1) ⊆ V` (its two-sided strip cover "closes" over the
  middle): in the real line the only two-sided strip covers are the ones
  that already contain the prefix, so the overlap `V ∩ (0,1)` is the
  whole connected prefix — never two disjoint strips.  Corollary:
  `overlap_eq_unit_of_twoSidedStrip`.

The step beyond this module (recorded, open): transport this to the
abstract 1-manifold — a closed two-sided wrap `TwoSidedClosedWrap P κ`
in a CONNECTED Hausdorff ambient makes the ambient compact (the union of
two arcs wrapping around both ways is a circle: compact, open, nonempty
in a connected space, hence the whole space), contradicting
non-compactness; and the no-infinite-oscillation T2 (an overlap cannot
accumulate at a boundary point through infinitely many components) which
is what guarantees the local overlap data near the chosen boundary point
is a finite union of strips to which the above applies.  Both are
genuine one-dimensional analysis, documented in ROADMAP S218.

Everything in this module is verified (no axioms, no `sorry`).
-/

/-! ## 1. The attaching data and the verified glue -/

/-- **Terminal-attach data**: the open arc `V` meets the open arc prefix
`P` (chart `κ : (0,1) ≃ₜ P`) exactly over the TERMINAL interval `(s,1)`
of the prefix coordinate — the engine's `hVend` as a bundled Prop. -/
def TerminalAttach {X : Type*} [TopologicalSpace X] (P V : Set X)
    (κ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ P}) (s : ℝ) : Prop :=
  0 < s ∧ s < 1 ∧ ∀ t : OpenRealInterval 0 1,
    (((κ t : {x : X // x ∈ P}) : X)) ∈ V ↔ (t : ℝ) ∈ Set.Ioo s 1

/-- **The verified attach-glue step**: open arcs `P`, `V` of a Hausdorff
space with interval charts and `TerminalAttach` data glue to an open
interval arc — the restatement of S207
(`OverlapConn.terminalTwoChart_union_is_openInterval`) in
`TerminalAttach` language.  This is the "attachment succeeds" half of
the one-step extension; the open content is producing the `V` and the
data. -/
theorem glue_of_TerminalAttach {X : Type*} [TopologicalSpace X] [T2Space X]
    {P V : Set X} (hPopen : IsOpen P) (hVopen : IsOpen V)
    (κ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ P})
    (η : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    {s : ℝ} (hT : TerminalAttach P V κ s) :
    Nonempty ({x : X // x ∈ P ∪ V} ≃ₜ OpenRealInterval 0 1) := by
  rcases hT with ⟨hs0, hs1, hVend⟩
  exact terminalTwoChart_union_is_openInterval hPopen hVopen κ η hs0 hs1 hVend

/-- **One-step terminal extension (target record)**: from a PROPER open
arc prefix `P` (chart `κ`) the construction must produce an open arc `V`
attaching over a terminal interval of the prefix coordinate and
genuinely extending `P` (`V ∖ P ≠ ∅`).  Proving this in a connected
non-compact 1-manifold ambient is the T1-abstract content (the S209
`TerminalExtensionExists` avatar); the module doc records the route. -/
def OneStepTerminalExtension {X : Type*} [TopologicalSpace X] (P : Set X)
    (κ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ P}) : Prop :=
  IsOpen P → P ≠ Set.univ →
    ∃ V : Set X, IsOpen V ∧ Nonempty (OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V}) ∧
      ∃ s : ℝ, TerminalAttach P V κ s ∧ (V \ P).Nonempty

/-- **Two-sided strip-cover (wrap data)**: the set `V` contains BOTH the
initial strip `(0,a)` and the terminal strip `(b,1)` of the prefix
coordinate (`0 < a < b < 1`) — the necessary form of an overlap meeting
the arc prefix `P` at both ends. -/
def TwoSidedStripCover {X : Type*} [TopologicalSpace X] (P V : Set X)
    (κ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ P}) : Prop :=
  ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < 1 ∧
    (∀ t : OpenRealInterval 0 1, (t : ℝ) < a →
      (((κ t : {x : X // x ∈ P}) : X)) ∈ V) ∧
    (∀ t : OpenRealInterval 0 1, b < (t : ℝ) →
      (((κ t : {x : X // x ∈ P}) : X)) ∈ V)

/-- **Closed two-sided wrap (target record)**: an open arc `V` with
two-sided strip-cover data over the prefix whose union with `P` covers
the whole ambient — the shape an attaching arc takes when it closes
around (the S¹ picture: `P = X ∖ {y}`, `V` a small arc through `y`).
The claim to prove (next goal): in a connected non-compact Hausdorff
1-manifold no proper open arc prefix admits a closed two-sided wrap —
such a wrap makes the ambient compact (circle). -/
def TwoSidedClosedWrap {X : Type*} [TopologicalSpace X] (P : Set X)
    (κ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ P}) : Prop :=
  ∃ V : Set X, IsOpen V ∧ Nonempty (OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V}) ∧
    TwoSidedStripCover P V κ ∧ P ∪ V = Set.univ

/-! ## 2. The real-coordinate model: no two-sided overlap in the line -/

/-- **The real line has no two-sided overlaps**: every open arc of ℝ
(open preconnected nonempty set) meets the unit prefix `(0,1)` in a
preconnected set, whatever its position — a genuine two-sided
(disconnected, both-end) overlap can never occur between intervals of
ℝ; it is intrinsically a circular phenomenon. -/
theorem preconnected_overlap_with_unit {V : Set ℝ} (hV : IsOpen V)
    (hpc : IsPreconnected V) (hne : V.Nonempty) :
    IsPreconnected (V ∩ Set.Ioo 0 1) := by
  rcases open_preconnected_nonempty_ℝ_shape hV hpc hne with h | h | h | h
  · rcases h with ⟨p, q, hpq⟩
    have hint : Set.Ioo p q ∩ Set.Ioo 0 1 = Set.Ioo (max p 0) (min q 1) := by
      ext x
      constructor
      · rintro ⟨⟨hp, hq⟩, ⟨h0, h1⟩⟩
        exact ⟨max_lt_iff.mpr ⟨hp, h0⟩, lt_min_iff.mpr ⟨hq, h1⟩⟩
      · rintro ⟨hmax, hmin⟩
        exact ⟨⟨(max_lt_iff.mp hmax).1, (lt_min_iff.mp hmin).1⟩,
          ⟨(max_lt_iff.mp hmax).2, (lt_min_iff.mp hmin).2⟩⟩
    rw [hpq, hint]
    exact isPreconnected_Ioo
  · rcases h with ⟨p, hVp⟩
    have hint : Set.Ioi p ∩ Set.Ioo 0 1 = Set.Ioo (max p 0) 1 := by
      ext x
      constructor
      · rintro ⟨hp, ⟨h0, h1⟩⟩
        exact ⟨max_lt_iff.mpr ⟨hp, h0⟩, h1⟩
      · rintro ⟨hmax, h1⟩
        exact ⟨(max_lt_iff.mp hmax).1, (max_lt_iff.mp hmax).2, h1⟩
    rw [hVp, hint]
    exact isPreconnected_Ioo
  · rcases h with ⟨q, hVq⟩
    have hint : Set.Iio q ∩ Set.Ioo 0 1 = Set.Ioo 0 (min q 1) := by
      ext x
      constructor
      · rintro ⟨hq, ⟨h0, h1⟩⟩
        exact ⟨h0, lt_min_iff.mpr ⟨hq, h1⟩⟩
      · rintro ⟨h0, hmin⟩
        exact ⟨(lt_min_iff.mp hmin).1, ⟨h0, (lt_min_iff.mp hmin).2⟩⟩
    rw [hVq, hint]
    exact isPreconnected_Ioo
  · rw [h]
    simp
    exact isPreconnected_Ioo

/-- **The two-sided strip cover forces full containment in the real
line**: if the real arc `V` contains BOTH end strips of the unit prefix
(`(0,a) ∪ (b,1) ⊆ V`, `0 < a < b < 1`), then `V` contains the whole
prefix `(0,1) ⊆ V` — its two-sided cover "closes over the middle", so
in ℝ it can never leave the prefix in two disjoint end pieces. -/
theorem twoSidedStrip_forces_cover_unit {V : Set ℝ} (hV : IsOpen V)
    (hpc : IsPreconnected V) (hne : V.Nonempty)
    {a b : ℝ} (ha0 : 0 < a) (hab : a < b) (hb1 : b < 1)
    (hinit : Set.Ioo 0 a ⊆ V) (hterm : Set.Ioo b 1 ⊆ V) :
    Set.Ioo 0 1 ⊆ V := by
  intro x hx
  rcases open_preconnected_nonempty_ℝ_shape hV hpc hne with h | h | h | h
  · rcases h with ⟨p, q, hpq⟩
    have hp_le0 : p ≤ 0 := by
      by_contra hp0
      have h0p : (0 : ℝ) < p := lt_of_not_ge hp0
      have hpa : p < a := by
        have hw : a / 2 ∈ V := hinit (by constructor <;> nlinarith)
        have hw' : a / 2 ∈ Set.Ioo p q := by simpa [hpq] using hw
        nlinarith [hw'.1, ha0]
      have hbad : p / 2 ∈ V := hinit (by constructor <;> nlinarith [h0p, hpa])
      have hbad' : p / 2 ∈ Set.Ioo p q := by simpa [hpq] using hbad
      nlinarith [hbad'.1]
    have hq_ge1 : 1 ≤ q := by
      by_contra hq1
      have h1q : q < 1 := lt_of_not_ge hq1
      have hbq : b < q := by
        have hw : (1 + b) / 2 ∈ V := hterm (by constructor <;> nlinarith [hb1])
        have hw' : (1 + b) / 2 ∈ Set.Ioo p q := by simpa [hpq] using hw
        nlinarith [hw'.2, hb1]
      have hbad : (q + 1) / 2 ∈ V := hterm (by constructor <;> nlinarith [hbq, h1q])
      have hbad' : (q + 1) / 2 ∈ Set.Ioo p q := by simpa [hpq] using hbad
      nlinarith [hbad'.2]
    rw [hpq]
    exact ⟨lt_of_le_of_lt hp_le0 hx.1, lt_of_lt_of_le hx.2 hq_ge1⟩
  · rcases h with ⟨p, hVp⟩
    have hp_le0 : p ≤ 0 := by
      by_contra hp0
      have h0p : (0 : ℝ) < p := lt_of_not_ge hp0
      have hpa : p < a := by
        have hw : a / 2 ∈ V := hinit (by constructor <;> nlinarith)
        have hwI : a / 2 ∈ Set.Ioi p := by simpa [hVp] using hw
        have hw' : p < a / 2 := Set.mem_Ioi.mp hwI
        nlinarith [hw', ha0]
      have hbad : p / 2 ∈ V := hinit (by constructor <;> nlinarith [h0p, hpa])
      have hbadI : p / 2 ∈ Set.Ioi p := by simpa [hVp] using hbad
      have hbad' : p < p / 2 := Set.mem_Ioi.mp hbadI
      nlinarith [hbad']
    rw [hVp]
    exact lt_of_le_of_lt hp_le0 hx.1
  · rcases h with ⟨q, hVq⟩
    have hq_ge1 : 1 ≤ q := by
      by_contra hq1
      have h1q : q < 1 := lt_of_not_ge hq1
      have hbq : b < q := by
        have hw : (1 + b) / 2 ∈ V := hterm (by constructor <;> nlinarith [hb1])
        have hwI : (1 + b) / 2 ∈ Set.Iio q := by simpa [hVq] using hw
        have hw' : (1 + b) / 2 < q := Set.mem_Iio.mp hwI
        nlinarith [hw', hb1]
      have hbad : (q + 1) / 2 ∈ V := hterm (by constructor <;> nlinarith [hbq, h1q])
      have hbadI : (q + 1) / 2 ∈ Set.Iio q := by simpa [hVq] using hbad
      have hbad' : (q + 1) / 2 < q := Set.mem_Iio.mp hbadI
      nlinarith [hbad']
    rw [hVq]
    exact lt_of_lt_of_le hx.2 hq_ge1
  · rw [h]
    trivial

/-- **Corollary**: with two-sided strip-cover data, the real arc's
overlap with the unit prefix is the whole (connected) prefix — never two
disjoint end strips. -/
theorem overlap_eq_unit_of_twoSidedStrip {V : Set ℝ} (hV : IsOpen V)
    (hpc : IsPreconnected V) (hne : V.Nonempty)
    {a b : ℝ} (ha0 : 0 < a) (hab : a < b) (hb1 : b < 1)
    (hinit : Set.Ioo 0 a ⊆ V) (hterm : Set.Ioo b 1 ⊆ V) :
    V ∩ Set.Ioo 0 1 = Set.Ioo 0 1 := by
  ext x
  constructor
  · intro hx
    exact hx.2
  · intro hx
    exact ⟨twoSidedStrip_forces_cover_unit hV hpc hne ha0 hab hb1 hinit hterm hx, hx⟩

end LeanEval.KnotTheory.Quadrisecant
