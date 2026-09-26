import Mathlib
import Submission.OneManifold
import Submission.TerminalAttachment
import Submission.T1Abstract
import Submission.Commons.Analysis.RealIntervals.left_strip_of_finiteIntervals_accumulation
import Submission.Commons.Topology.Compactness.closedInterval_inside_unit_open
import Submission.Commons.Analysis.RealIntervals.mem_closure_left_interval
import Submission.Commons.Analysis.RealIntervals.open_preconnected_untrapped_unit_end_strip
import Submission.Commons.Topology.Charts.chartArc_isOpen
import Submission.Commons.Topology.Charts.chartArc_intervalChart
import Submission.Commons.Topology.Charts.coordSet_open_preconnected_nonempty

open Set
open scoped Topology

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

/-!
# S221 — the one-sided attachment: side condition from L36 + strip cut
(module Submission/OneSidedAttach.lean)

Per the S220 status the next sub-goal is the one-sided attachment lemma:
the bridge `c ∈ closure S` (S220) plus the one-sidedness side condition,
through the L36 strip core
(`Commons.Analysis.RealIntervals.left_strip_of_finiteIntervals_accumulation`),
produces the end strip from which the attaching arc `V` with
`TerminalAttach` data is cut (S218 `glue_of_TerminalAttach` then charts
`P ∪ V`).  This module fixes the real-coordinate side-condition core
(VERIFIED, sorry-free) and frames the geometric one-sided-attach target
precisely.

**Real-coordinate core (VERIFIED).**  Let `S ⊆ (0,1)` be the
U-chart-coordinate set of the overlap `P ∩ U` at the boundary point
`y` (`c = c₀` its coordinate; S220 proved `c ∈ closure S`, `c ∉ S`).

1. **`RightFreeAt S c`** — the one-sidedness side condition: `S` has no
   points in some right-neighbourhood `(c, c+δ)` of `c` (all overlap
   points near `c` lie to the left);
2. **`closure_left_accumulation_of_rightFree`** — right-free +
   `c ∈ closure S` + `c ∉ S` ⇒ left accumulation (`hacc` of L36: every
   left interval `(c−ε, c)` meets `S`): closure forces points of `S`
   arbitrarily close to `c`, right-freeness rules out the right side,
   `c ∉ S` rules out `c` itself;
3. **`left_strip_of_rightFree`** — THE side-condition glue: right-free +
   closure + `c ∉ S` + the T2 FINITE local structure
   (`S ∩ Iio c = ⋃ p ∈ F, Ioo p.1 p.2` with `p.2 ≤ c` — the hypothesis
   the T2 geometric no-oscillation claim will supply) ⇒ by L36 there is
   an end strip `(p, c) ⊆ S` reaching `c` from the left;
4. **`strip_cut_left`** — the cut: given the strip `(p,c) ⊆ S`,
   right-freeness (`hfree`), and a cut point `p' ∈ (p, c)`, the overlap
   of `S` with the cut interval `(p', c+δ)` is EXACTLY the strip
   `(p', c)` — the real-coordinate avatar of `V ∩ P ∩ U` being a clean
   strip in the U-chart.

**Geometric target (record).**  **`OneSidedBoundaryAttach`** — the
theorem-shaped statement: at a boundary point `y ∈ P̄ ∖ P` of the open
arc prefix `P` (chart `κ`), in an open arc chart `ψ : (0,1) ≃ₜ U` of
`U ∋ y` whose overlap-coordinate set `Sℝ = val '' {t | (ψ t : X) ∈ P}`
is one-sided from the left at `c₀ = ψ.symm ⟨y,·⟩` (`RightFreeAt Sℝ c₀`)
and has the finite local structure (`hF`), there is an open arc `V`
attaching over an END strip of the current prefix chart `κ` —
`TerminalAttach P V κ s` (terminal; an initial-strip attach is converted
to terminal by reversing the prefix chart with the interval involution
`t ↦ 1 − t`) — with `V ∖ P ≠ ∅`.  Proof
obligations (documented; the verified pieces above are the real-coordinate
half): (i) transport `Sℝ`/`RightFreeAt`/`hF` through the S220 bridge to
the strip `(p,c₀) ⊆ Sℝ` (`left_strip_of_rightFree` + the bridge), (ii)
cut the attaching arc `V` from the U-chart so that `V ∩ P` is the strip
(`strip_cut_left` at the real level + the homeo `ψ`), (iii) the
transition/end sub-lemma T1b — the end strip of the U-chart maps under
the transition `κ⁻¹ ∘ ψ` to an end strip of the prefix chart `κ` (the
accumulating end of `P` at `y` lies eventually in `U` — needs the T2
geometric no-oscillation input — and its coordinate reaches an end of
`(0,1)`; this gives an end strip of `κ`, terminal up to the reversal
involution `t ↦ 1 − t`), giving
`TerminalAttach` against `κ` (or its reversal).  (i)–(ii) are
real-coordinate; (iii) is the one-dimensional transition analysis,
recorded OPEN with T2.

**T1b — the transition/end sub-lemma (section 3, VERIFIED).**
**`end_coords_reach_prefix_end`** — the core of the transition: in a
Hausdorff space, if `A ⊆ P` is a strip of the arc prefix `P` (chart
`κ`) with a boundary point `y ∈ closure A`, `y ∉ P`, then the set of
κ-coordinates of `A` is NOT contained in any strict sub-interval
`(ε, 1−ε)` of the prefix coordinate — it reaches an end of `(0,1)`
(compactness of the closed interval `{ε ≤ r ≤ 1−ε}` in `(0,1)` by the
commons L37, continuous-image compactness, closedness in the Hausdorff
ambient, complement-neighbourhood vs `y ∈ closure A`).  Whatever the
U-chart side looks like, the κ-coordinates of the overlap points
accumulating at the boundary point approach an end of the prefix
coordinate; the attaching arc is then cut from the prefix end so reached
(initial-end reach converted by `t ↦ 1 − t`), completing T1b's role in
`OneSidedBoundaryAttach`.

**Step (i)/(ii) — strip → point-set transport and the end-reaches
application (section 4, VERIFIED, S223).**  With the U-side end strip
`{t | p < t < c₀}` (`c₀` the coordinate of the boundary point `y`), its
ambient point set **`stripPoints U ψ p c₀`** is defined and verified to
carry the bridge onward: `strip_coord_mem_closure` (the endpoint `c₀` is
in the closure of the coordinate strip — real closure L38 through
`closure_subtype`), **`stripPoints_mem_closure`** (THE transport: `y` is
in the closure of `stripPoints` — the continuous chart coercion plus
`image_closure_subset_closure_image`), `stripPoints_subset` (`⊆ P` from
the overlap hypothesis), and **`boundaryStrip_coords_reach_prefix_end`**
(the application: the κ-coordinates of the strip point set reach a prefix
end — T1b core applied with `A := stripPoints`).  This closes proof
obligations (i) and (ii) of `OneSidedBoundaryAttach`; the attach cutting
(iii) and the T2 geometric no-oscillation input are recorded in the
ROADMAP.

**Step (iii) — the attach cutting (section 5, S224): statement pinned,
first subgoal VERIFIED.**  `InitialAttach` / `EndStripAttach` (the
orientation-neutral end-strip attach data) and
**`AttachCuttingStatement`** (the theorem-shaped target: boundary point +
one-sided right-freeness + T2 finite structure + bridge ⇒ an open arc `V`
with an END-STRIP attach over `κ` and `V ∖ P ≠ ∅`) are pinned; the first
subgoal **`right_free_beyond_arc`** is VERIFIED (from the right-freeness
there is a NONEMPTY beyond-arc `beyondArc U ψ c₀ δ` DISJOINT from `P` —
the `V ∖ P` ingredient of the attaching arc exists; `δ` shrunk to
`min δ₀ ((1−c₀)/2)` to stay inside the chart).  The assembly (prefix-end
strip from steps (i)/(ii) + beyond-arc + the arc through `y`, with the
transition/end monotone-limit sub-analysis and the reversal
normalization) is recorded in the ROADMAP with the T2 geometric input.

**Step (iii-a) — the clean prefix-end strip (section 6, VERIFIED,
S225).**  `boundaryStripCoordSet P U κ ψ p c₀` (the κ-coordinate set of
the strip point set) and **`boundaryStrip_coords_end_strip`** — the
payoff: given the strip point set (`A ⊆ P`, boundary point `y ∉ P` with
`y ∈ closure A`) whose κ-coordinate set `T` is open, preconnected and
nonempty (the bridge outputs), `T` is a clean END STRIP `(a,1)` or
`(0,b)` of the prefix coordinate — via the untrapped fact
(`end_coords_reach_prefix_end`) and the fleet L39
`open_preconnected_untrapped_unit_end_strip`.  (No monotone-limit
argument is needed: openness + preconnectedness + untrapped suffice.)
The remaining iii-a bridge (T open/preconnected/nonempty from the
openness/connectedness of `stripPoints` through the chart homeos),
iii-b (the cutting assembly) and iii-c (the T2 input) are recorded in
the ROADMAP.

**Step (iii-b) — the cutting assembly (section 7, S226): statement
pinned; first real-coordinate sublemma VERIFIED.**  The terminal-subcase
construction is recorded (the attaching arc `V := ψArc U ψ p (c₀+δ)` —
the ψ-arc through the boundary point beyond the strip — with the four
proof obligations: `V∩P` real cut, `A = κ((a,1))` prefix-end identity,
openness/arc-charting of `V`, `V ∖ P ≠ ∅` via the beyond bit);
**`overlapStrip_rightFree_cut_at_left`** is VERIFIED (the `V ∩ P` real
half: `S ∩ (p, c₀+δ) = (p,c₀)` from the strip, `c₀ ∉ S` and
right-freeness); `ψArc` (the ψ-coordinate arc) and
`AttachCuttingTerminalAssembled` (the terminal-subcase target record)
are pinned.  The initial subcase (`T = (0,b)`) is the mirror with the
reversal normalization; obligations 2–4 are the next sub-lemmas.

**Step (iii-b-2) — the prefix-end identity (section 8, VERIFIED,
S227).**  `stripPoints_mem_iff_of_coordSet` — the pointwise identity
`((κ r : X) ∈ A) ↔ (r : ℝ) ∈ (a,1)` from the coordinate-set identity
`T = (a,1)` (iii-a's payoff; the `TerminalAttach`-shaped membership iff),
and `stripPoints_eq_prefixEnd_of_coordSet` — the set identity
`A = κ((a,1))` (with `A ⊆ P`): obligation 2 of the cutting assembly,
which with `V ∩ P = A` gives the `TerminalAttach P V κ a` data.

**Step (iii-b-3) — openness and interval-charting of `ψArc` (section 9,
VERIFIED, S228).**  `ψArc_isOpen` (the chart-arc over `(lo,hi)` is open
when `U` is open — commons L40 `chartArc_isOpen`), `ψArc_intervalChart`
(`ORI ≃ₜ ↑(ψArc U ψ lo hi)` when the interval meets `(0,1)` — commons L41
`chartArc_intervalChart`, via `e.symm`), and
`interval_meets_unit_of_nonneg_bounds` (the `hne` source for the attach
interval `(p, c₀+δ)`).  Obligation 3 of the cutting assembly.

**Step (iii-b-4) — the attaching arc extends `P` (section 10, VERIFIED,
S229).**  `ψArc_diff_P_nonempty` — `(ψArc U ψ p (c₀+δ) \ P).Nonempty`
from `p ≤ c₀`, `0 < δ`, the beyond arc nonempty, and its disjointness
from `P` (`hbdP` from `right_free_beyond_arc`): the beyond point lies in
the attach arc and outside `P`.  With this, ALL FOUR obligations of the
cutting assembly are VERIFIED (real cut + prefix-end identity +
openness/interval-charting + genuine extension) — the terminal-subcase
assembly theorem `AttachCuttingTerminalAssembled` is one composition
away from the boundary data.

**The terminal-subcase cutting assembly (section 11, VERIFIED, S230).**
  `chart_mem_P_iff_coord` (chart-point-in-`P` iff coordinate in the real
  overlap set) and `P_inter_ψArc_eq_stripPoints` (from the real cut:
  `P ∩ ψArc U ψ p (c₀+δ) = stripPoints U ψ p c₀`) are the plumbing, and
  **`attach_cutting_terminal`** closes the assembly: from the boundary
  data (strip `p < c₀`, `c₀ ∈ (0,1)`, `0 < δ`, the clean terminal end
  `0 < a < 1` with the prefix-end identity `hiff`, the real cut `hcut`,
  and the beyond arc `hbd`/`hbdP`) the arc `V := ψArc U ψ p (c₀+δ)` is
  open, interval-charted, satisfies `TerminalAttach P V κ a`, and
  `V \ P ≠ ∅` — the terminal half of `AttachCuttingTerminalAssembled`,
  produced by assembling the four verified obligations.

**The initial-subcase cutting assembly (section 12, VERIFIED, S231).**
  **`attach_cutting_initial`** mirrors `attach_cutting_terminal` over the
  INITIAL strip `(0,b)` (`0 < b < 1`): the arc `V := ψArc U ψ p (c₀+δ)`
  is open, interval-charted, satisfies `InitialAttach P V κ b` (the
  pointwise membership `(κ t : X) ∈ V ↔ (t : ℝ) ∈ (0,b)`), and
  `V \ P ≠ ∅`.  Both halves of the attach cutting (terminal and initial)
  are now in hand; the reversal normalization (InitialAttach →
  TerminalAttach against the reversed chart `t ↦ 1 − t`) is delegated as
  commons L42 `unitInterval_revHomeo` and will be applied next.

**The reversal normalization (section 13, VERIFIED, S231).**
  `revORI` (the self-inverse interval reversal `t ↦ 1 − t`, built with
  the standalone-`F` + named-membership pattern), `revORI_val`, and
  **`initialAttach_to_terminal_rev`** — from `InitialAttach P V κ b` the
  reversed prefix chart `revORI.trans κ` satisfies
  `TerminalAttach P V (revORI.trans κ) (1 − b)` (initial strip `(0,b)`
  becomes the terminal strip `(1−b,1)`).  With sections 11–13 BOTH
  halves of the attach cutting are closed and the initial half
  normalizes to the `TerminalAttach` form the chain consumes.

**The attach-cutting disjunction realized (section 14, VERIFIED,
S232).**  **`attach_cutting_endStrip`** — from the boundary data and the
clean END-STRIP disjunction (`hend`: the κ-coordinate set of the strip
point set is `(a,1)`, `0 < a < 1`, or `(0,b)`, `0 < b < 1`) plus the
real cut and the beyond arc, the arc `V := ψArc U ψ p (c₀+δ)` is open,
interval-charted, attaches over an end strip (`EndStripAttach P V κ`),
and `V \ P ≠ ∅` — case-split on `hend`, apply the terminal or the
initial half.  The remaining instantiation (producing `hend` and the
transport inputs from the raw boundary data) needs the iii-a bridge,
recorded in the ROADMAP.

Everything in this module is verified (no axioms, no `sorry`); the
geometric targets `OneSidedBoundaryAttach`, `AttachCuttingStatement` and
`AttachCuttingTerminalAssembled` are records.
-/

/-! ## 1. The real-coordinate side-condition core -/

/-- **One-sidedness side condition**: the real set `S` has no points in
some right-neighbourhood `(c, c+δ)` of `c` (near `c`, all points of `S`
lie to the left — "one-sided from the left"). -/
def RightFreeAt (S : Set ℝ) (c : ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ S ∩ Set.Ioo c (c + δ) = ∅

/-- **Right-free + closure + not-a-member ⇒ left accumulation**: if `c ∈
closure S`, `c ∉ S`, and `S` is free of points just to the right of `c`,
then every left interval `(c−ε, c)` meets `S` — the `hacc` hypothesis of
the L36 strip core. -/
theorem closure_left_accumulation_of_rightFree {S : Set ℝ} {c : ℝ}
    (hfree : RightFreeAt S c) (hcl : c ∈ closure S) (hcS : c ∉ S) :
    ∀ ε : ℝ, 0 < ε → (S ∩ Set.Ioo (c - ε) c).Nonempty := by
  rcases hfree with ⟨δ, hδ0, hδ⟩
  intro ε hε
  let ε' : ℝ := min ε δ / 2
  have hε'0 : 0 < ε' := by
    dsimp [ε']
    have hmin : 0 < min ε δ := lt_min hε hδ0
    positivity
  have hε'ε : ε' ≤ ε := by
    dsimp [ε']
    nlinarith [min_le_left ε δ]
  have hε'δ : ε' ≤ δ := by
    dsimp [ε']
    nlinarith [min_le_right ε δ]
  have hopen : IsOpen (Set.Ioo (c - ε') (c + ε')) := isOpen_Ioo
  have hcI : c ∈ Set.Ioo (c - ε') (c + ε') := by constructor <;> linarith
  rcases (mem_closure_iff.mp hcl) (Set.Ioo (c - ε') (c + ε')) hopen hcI with ⟨x, hx, hxS⟩
  have hxclt : x < c := by
    by_contra hxge
    have hxc_ne : x ≠ c := by
      intro hxc
      exact hcS (by simpa [hxc] using hxS)
    have hxgt : c < x := lt_of_le_of_ne (le_of_not_gt hxge) hxc_ne.symm
    have hxδ : x ∈ Set.Ioo c (c + δ) := ⟨hxgt, by linarith [hx.2, hε'δ]⟩
    exact (eq_empty_iff_forall_notMem.mp hδ) x ⟨hxS, hxδ⟩
  refine ⟨x, ⟨hxS, ?_⟩⟩
  exact ⟨by linarith [hx.1, hε'ε], hxclt⟩

/-- **THE side-condition glue**: right-free + closure + not-a-member + the
T2 FINITE local structure (`S ∩ Iio c` is a finite union of open
intervals with upper endpoints `≤ c` — the hypothesis the T2 geometric
no-oscillation claim supplies) ⇒ an end strip `(p,c) ⊆ S` reaching `c`
from the left (the L36 strip core
`Commons.Analysis.RealIntervals.left_strip_of_finiteIntervals_accumulation`
fed by `closure_left_accumulation_of_rightFree`). -/
theorem left_strip_of_rightFree {S : Set ℝ} {c : ℝ} (F : Finset (ℝ × ℝ))
    (hF : S ∩ Set.Iio c = ⋃ p ∈ F, Set.Ioo p.1 p.2)
    (hvle : ∀ p ∈ F, p.2 ≤ c)
    (hfree : RightFreeAt S c) (hcl : c ∈ closure S) (hcS : c ∉ S) :
    ∃ p : ℝ, p < c ∧ Set.Ioo p c ⊆ S := by
  have hacc : ∀ ε : ℝ, 0 < ε → (S ∩ Set.Ioo (c - ε) c).Nonempty :=
    closure_left_accumulation_of_rightFree hfree hcl hcS
  exact Commons.Analysis.RealIntervals.left_strip_of_finiteIntervals_accumulation
    S c F hF hvle hacc

/-- **The strip cut**: given the end strip `(p,c) ⊆ S` (from L36) and a
cut point `p' ∈ (p,c)`, the overlap of `S` with the cut interval
`(p', c+δ)` is EXACTLY the strip `(p', c)` — right-freeness (`hfree`)
kills everything to the right of `c`, `c ∉ S` kills `c`, and the strip
fills `(p', c)`.  (The real-coordinate avatar of `V ∩ P ∩ U` being a
clean strip in the U-chart, with `V = ψ((p', c+δ))`.) -/
theorem strip_cut_left {S : Set ℝ} {c p : ℝ} (hcS : c ∉ S)
    (hstrip : Set.Ioo p c ⊆ S) {p' δ : ℝ} (hpp' : p < p') (hp'c : p' < c)
    (hδ0 : 0 < δ) (hfree : S ∩ Set.Ioo c (c + δ) = ∅) :
    S ∩ Set.Ioo p' (c + δ) = Set.Ioo p' c := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hxS, hxI⟩
    rcases hxI with ⟨hp'x, hxcδ⟩
    constructor
    · exact hp'x
    · by_contra hxge
      have hxc_ne : x ≠ c := by
        intro hxc
        exact hcS (by simpa [hxc] using hxS)
      have hxgt : c < x := lt_of_le_of_ne (le_of_not_gt hxge) hxc_ne.symm
      have hxδ : x ∈ Set.Ioo c (c + δ) := ⟨hxgt, hxcδ⟩
      exact (eq_empty_iff_forall_notMem.mp hfree) x ⟨hxS, hxδ⟩
  · intro hx
    rcases hx with ⟨hp'x, hxc⟩
    refine ⟨?_, ⟨hp'x, by linarith⟩⟩
    exact hstrip ⟨lt_trans hpp' hp'x, hxc⟩

/-! ## 2. The geometric target (record) -/

/-- The existential output of a one-step attach: an open arc `V` with an
interval chart, `TerminalAttach` data over the prefix `P` at some
`s ∈ (0,1)`, and a genuine extension `V ∖ P ≠ ∅`.  (This is exactly the
existential content of `TerminalAttachment.OneStepTerminalExtension P κ`
after its `IsOpen P`/`P ≠ univ` antecedents.) -/
def AttachingArcOutput {X : Type*} [TopologicalSpace X] (P : Set X)
    (κ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ P}) : Prop :=
  ∃ V : Set X, IsOpen V ∧ Nonempty (OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V}) ∧
    ∃ s : ℝ, TerminalAttach P V κ s ∧ (V \ P).Nonempty

/-- **The geometric one-sided-attach target (record)**: at a boundary
point `y ∈ P̄ ∖ P` of the open arc prefix `P` (chart `κ`), in an open arc
chart `ψ : (0,1) ≃ₜ U` of `U ∋ y` whose overlap-coordinate real set
`Sℝ = val '' {t | (ψ t : X) ∈ P}` is one-sided from the left at
`c₀ = (ψ.symm ⟨y, ·⟩ : ℝ)` (`RightFreeAt Sℝ c₀`) and has the T2 FINITE
local structure (`hF`: `Sℝ ∩ Iio c₀` a finite union of intervals with
upper endpoints `≤ c₀`), there is an open arc `V` attaching over an END
strip of the current prefix chart — `TerminalAttach P V κ s` (terminal)
— with `V ∖ P ≠ ∅`.  Proof obligations: (i) the S220 bridge +
`left_strip_of_rightFree` give the end strip `(p, c₀) ⊆ Sℝ`; (ii)
`strip_cut_left` + the homeo `ψ` cut the arc `V` so that `V ∩ P` is the
strip; (iii) the transition/end sub-lemma T1b (OPEN): the accumulating
end of `P` at `y` lies eventually in `U` and its coordinate reaches an
end of `(0,1)` (needs the T2 geometric no-oscillation input and the
transition `κ⁻¹ ∘ ψ` analysis), so the strip is an end strip of `κ`
(terminal up to the reversal involution). -/
def OneSidedBoundaryAttach {X : Type*} [TopologicalSpace X] (P U : Set X)
    (κ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ P})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U}) {y : X} (hyU : y ∈ U) : Prop :=
  let Sℝ : Set ℝ := ((↑) : OpenRealInterval 0 1 → ℝ) ''
    {t : OpenRealInterval 0 1 | ((ψ t : {x : X // x ∈ U}) : X) ∈ P}
  let c₀ : ℝ := ((ψ.symm ⟨y, hyU⟩ : OpenRealInterval 0 1) : ℝ)
  IsOpen U → y ∈ closure P → y ∉ P → RightFreeAt Sℝ c₀ →
    (∃ F : Finset (ℝ × ℝ),
      Sℝ ∩ Set.Iio c₀ = ⋃ p ∈ F, Set.Ioo p.1 p.2 ∧ ∀ p ∈ F, p.2 ≤ c₀) →
    ∃ V : Set X, IsOpen V ∧ Nonempty (OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V}) ∧
      ∃ s : ℝ, 0 < s ∧ s < 1 ∧ (V \ P).Nonempty ∧ TerminalAttach P V κ s



/-! ## 3. T1b — the transition/end sub-lemma (crystallized core, VERIFIED)

Per the S221 proof obligations, T1b is the transition step that turns the
U-chart end strip into an END STRIP OF THE PREFIX CHART `κ`: the
κ-coordinate image of a boundary strip of `P` (points of `P ∩ U`
approaching the boundary point `y ∈ P̄ ∖ P`) cannot be trapped strictly
inside the prefix coordinate `(0,1)` — it reaches an end (the coordinate
`1` or `0`), and from there the attaching arc is cut (an initial-end
reach is converted to terminal by the reversal involution `t ↦ 1 − t`).

**`end_coords_reach_prefix_end`** (VERIFIED — the core of T1b): in a
Hausdorff space, let `A ⊆ P` be a strip of the arc prefix `P` (chart
`κ : (0,1) ≃ₜ P`) with a boundary point `y ∈ closure A`, `y ∉ P`.  Then
the set of κ-coordinates of `A` is NOT contained in any strict
sub-interval `(ε, 1−ε)` of the prefix coordinate — it reaches an end of
`(0,1)`.  Proof: if the coordinates were trapped in `(ε, 1−ε)`, then
`A ⊆ f '' C` where `C := {r | ε ≤ r ≤ 1−ε}` (the closed interval inside
`(0,1)`, compact by the commons L37
`Commons.Topology.Compactness.closedInterval_inside_unit_open`) and
`f := κ`-value coercion; `f '' C` is compact (continuous image), hence
closed in the Hausdorff `X`, and avoids `y` (its points lie in `P`);
its open complement is a neighbourhood of `y` disjoint from `A` —
contradicting `y ∈ closure A`.

This is the analytic heart of the transition: whatever the U-chart side
looks like, the κ-coordinates of the overlap points that accumulate at
the boundary point `y` must approach an end of the prefix coordinate.
The assembly that follows (recorded in the S221 proof obligations and
the `OneSidedBoundaryAttach` target) chooses the attaching arc from the
prefix end so reached; the U-chart data enters by defining `A` as the
point set of the U-side end strip (whose κ-coordinate set is exactly the
set tested here).  Everything here is verified (no axioms, no `sorry`).
-/

/-- **T1b core**: the κ-coordinate set of a boundary strip `A` of the arc
prefix `P` (`A ⊆ P`, `y ∈ closure A`, `y ∉ P`) cannot be trapped strictly
inside `(0,1)` — it reaches an end of the prefix coordinate. -/
theorem end_coords_reach_prefix_end {X : Type*} [TopologicalSpace X] [T2Space X]
    (P : Set X) (κ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ P})
    {A : Set X} (hAP : A ⊆ P) {y : X} (hyPc : y ∉ P) (hyA : y ∈ closure A) :
    ¬ ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 2 ∧
      (((↑) : OpenRealInterval 0 1 → ℝ) ''
        {r : OpenRealInterval 0 1 | ((κ r : {x : X // x ∈ P}) : X) ∈ A}) ⊆ Set.Ioo ε (1 - ε) := by
  intro hbad
  rcases hbad with ⟨ε, hε0, hε12, hsub⟩
  let C : Set (OpenRealInterval 0 1) :=
    {r : OpenRealInterval 0 1 | ε ≤ (r : ℝ) ∧ (r : ℝ) ≤ 1 - ε}
  let f : OpenRealInterval 0 1 → X := fun r => ((κ r : {x : X // x ∈ P}) : X)
  let K : Set X := f '' C
  have hAκ : A ⊆ K := by
    intro x hx
    let r₀ : OpenRealInterval 0 1 := κ.symm ⟨x, hAP hx⟩
    have hrC : r₀ ∈ C := by
      have hmem : r₀ ∈ {r : OpenRealInterval 0 1 |
          ((κ r : {x : X // x ∈ P}) : X) ∈ A} := by
        dsimp [r₀]
        rw [κ.apply_symm_apply ⟨x, hAP hx⟩]
        exact hx
      have hval : (r₀ : ℝ) ∈ Set.Ioo ε (1 - ε) := hsub ⟨_, hmem, rfl⟩
      dsimp [C]
      exact ⟨le_of_lt hval.1, le_of_lt hval.2⟩
    have hxeq : f r₀ = x := by
      dsimp [f, r₀]
      simp
    rw [← hxeq]
    exact Set.mem_image_of_mem f hrC
  have hCcomp : IsCompact C := by
    dsimp [C]
    simpa using (Commons.Topology.Compactness.closedInterval_inside_unit_open
      (ε := ε) hε0 hε12)
  have hcont : Continuous f := by
    dsimp [f]
    exact continuous_subtype_val.comp κ.continuous
  have hKcomp : IsCompact K := hCcomp.image hcont
  have hKcl : IsClosed K := hKcomp.isClosed
  have hyK : y ∉ K := by
    intro hyK'
    rcases hyK' with ⟨r, hrC, hrf⟩
    have hκry : ((κ r : {x : X // x ∈ P}) : X) = y := by
      simpa [f] using hrf
    have hmem : ((κ r : {x : X // x ∈ P}) : X) ∈ P := (κ r : {x : X // x ∈ P}).2
    exact hyPc (by rwa [hκry] at hmem)
  let O : Set X := Kᶜ
  have hOopen : IsOpen O := hKcl.isOpen_compl
  have hyO : y ∈ O := hyK
  have hOA : O ∩ A = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    rcases hx with ⟨hxO, hxA⟩
    exact hxO (hAκ hxA)
  have hmeet : (O ∩ A).Nonempty := by
    exact (mem_closure_iff.mp hyA) O hOopen hyO
  rcases hmeet with ⟨x, hxO, hxA⟩
  have hxK : x ∈ K := hAκ hxA
  exact hxO hxK




/-! ## 4. Step (i)/(ii) — strip → point-set transport and the
end-reaches application (VERIFIED)

Per the S222 proof-obligation list, step (i) is the transport that turns
the U-chart coordinate strip into the ambient POINT SET the
end-reaches theorem consumes, and step (ii) is the direct application.
This section verifies both.

**Step (i) — the transport.**  Let the U-side end strip be the set of
U-coordinates `{t : (0,1) | p < (t:ℝ) < c₀}` (`c₀ := (ψ.symm ⟨y,·⟩ : ℝ)`
the coordinate of the boundary point `y`, `p < c₀`), known to lie in
the overlap set (`hstrip`: every such `t` satisfies `(ψ t : X) ∈ P`).
The corresponding ambient point set is
**`stripPoints U ψ p c₀ := ψ-coercion '' {t | p < t < c₀}`**.  The three
lemmas assemble the bridge:

- **`strip_coord_mem_closure`** — `c₀` lies in the closure (in the chart
  interval) of the coordinate strip (the real closure fact
  `Commons.Analysis.RealIntervals.mem_closure_left_interval`, fleet L38,
  transported through `closure_subtype`);
- **`stripPoints_mem_closure`** — THE transport: the boundary point `y`
  lies in the closure of `stripPoints U ψ p c₀` (the chart coercion
  `f : t ↦ (ψ t : X)` is continuous, `y = f c₀`, and
  `image_closure_subset_closure_image` pushes the coordinate closure
  through);
- **`stripPoints_subset`** — `stripPoints U ψ p c₀ ⊆ P` whenever the
  strip lies in the overlap (`hstrip`).

**Step (ii) — the application.**  **`boundaryStrip_coords_reach_prefix_end`**:
with `P` (chart `κ`), `U` (chart `ψ`), the boundary point `y` (`y ∉ P`,
`hyU`), the strip `(p, c₀)` inside the overlap (`hstrip`), the ambient
space Hausdorff, the κ-coordinate set of `stripPoints U ψ p c₀` is NOT
contained in any strict `(ε, 1−ε)` of the prefix coordinate — it reaches
an end of `(0,1)`: exactly
`end_coords_reach_prefix_end` (S222, T1b core) applied to
`A := stripPoints U ψ p c₀` with `A ⊆ P` (`stripPoints_subset`),
`y ∉ P`, `y ∈ closure A` (`stripPoints_mem_closure`).

This closes proof obligations (i) and (ii) of `OneSidedBoundaryAttach`
(end-strip point set with `y` in its closure, and its κ-coordinates
reaching a prefix end).  The remaining assembly step (iii) — cutting the
attaching arc `V` with `TerminalAttach P V κ s` from the prefix end so
reached (`V ∖ P ≠ ∅`; initial-end reach converted by `t ↦ 1 − t`) — and
the T2 geometric no-oscillation input supplying the finite local
structure are recorded in the ROADMAP.  Everything here is verified (no
axioms, no `sorry`).
-/

/-- The ambient point set of the U-chart coordinate strip `(p, c₀)`: the
ψ-images of all chart coordinates strictly between `p` and `c₀`. -/
def stripPoints {X : Type*} [TopologicalSpace X] (U : Set X)
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U}) (p c₀ : ℝ) : Set X :=
  (fun t : OpenRealInterval 0 1 => ((ψ t : {x : X // x ∈ U}) : X)) ''
    {t : OpenRealInterval 0 1 | (t : ℝ) ∈ Set.Ioo p c₀}

/-- **Step (i)-a**: the strip-end coordinate `c₀` lies in the closure (in
the chart interval) of the coordinate strip `{t | p < t < c₀}` — the real
closure fact L38 transported through `closure_subtype`. -/
lemma strip_coord_mem_closure {c₀ p : ℝ} (hpc : p < c₀) (hc0 : 0 < c₀)
    (hc1 : c₀ < 1) :
    (⟨c₀, ⟨hc0, hc1⟩⟩ : OpenRealInterval 0 1) ∈
      closure {t : OpenRealInterval 0 1 | (t : ℝ) ∈ Set.Ioo p c₀} := by
  rw [closure_subtype]
  have himg : ((↑) : OpenRealInterval 0 1 → ℝ) ''
      {t : OpenRealInterval 0 1 | (t : ℝ) ∈ Set.Ioo p c₀} =
      Set.Ioo p c₀ ∩ Set.Ioo 0 1 := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨ht, t.2⟩
    · intro hx
      refine ⟨⟨x, hx.2⟩, ?_, rfl⟩
      change p < x ∧ x < c₀
      exact ⟨hx.1.1, hx.1.2⟩
  rw [himg]
  exact Commons.Analysis.RealIntervals.mem_closure_left_interval hpc hc0 hc1

/-- **Step (i)-b — THE transport**: the boundary point `y` lies in the
closure of the ambient point set `stripPoints U ψ p c₀` of the
U-coordinate strip (the chart coercion is continuous, `y` is the image of
`c₀`, and the coordinate closure is pushed through by
`image_closure_subset_closure_image`). -/
lemma stripPoints_mem_closure {X : Type*} [TopologicalSpace X]
    (U : Set X) (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    {y : X} (hyU : y ∈ U) {p : ℝ}
    (hpc : p < ((ψ.symm ⟨y, hyU⟩ : OpenRealInterval 0 1) : ℝ)) :
    y ∈ closure (stripPoints U ψ p ((ψ.symm ⟨y, hyU⟩ : OpenRealInterval 0 1) : ℝ)) := by
  let c₀ : ℝ := ((ψ.symm ⟨y, hyU⟩ : OpenRealInterval 0 1) : ℝ)
  have hc₀mem : c₀ ∈ Set.Ioo (0 : ℝ) 1 := (ψ.symm ⟨y, hyU⟩ : OpenRealInterval 0 1).2
  let f : OpenRealInterval 0 1 → X := fun t => ((ψ t : {x : X // x ∈ U}) : X)
  have hfcont : Continuous f := by
    dsimp [f]
    exact continuous_subtype_val.comp ψ.continuous
  have hce : (⟨c₀, hc₀mem⟩ : OpenRealInterval 0 1) ∈
      closure {t : OpenRealInterval 0 1 | (t : ℝ) ∈ Set.Ioo p c₀} :=
    strip_coord_mem_closure hpc hc₀mem.1 hc₀mem.2
  have hyeq : y = f ⟨c₀, hc₀mem⟩ := by
    dsimp [f, c₀]
    rw [ψ.apply_symm_apply ⟨y, hyU⟩]
  have hinc : f '' closure {t : OpenRealInterval 0 1 | (t : ℝ) ∈ Set.Ioo p c₀} ⊆
      closure (f '' {t : OpenRealInterval 0 1 | (t : ℝ) ∈ Set.Ioo p c₀}) :=
    image_closure_subset_closure_image hfcont
  have hmem : y ∈ f '' closure {t : OpenRealInterval 0 1 | (t : ℝ) ∈ Set.Ioo p c₀} := by
    rw [hyeq]
    exact Set.mem_image_of_mem f hce
  have hfinal : y ∈ closure (f '' {t : OpenRealInterval 0 1 | (t : ℝ) ∈ Set.Ioo p c₀}) :=
    hinc hmem
  simpa [stripPoints, f, c₀] using hfinal

/-- **Step (i)-c**: the ambient point set of the strip lies in `P`
whenever the strip lies in the overlap (coordinate-wise hypothesis
`hstrip`). -/
lemma stripPoints_subset {X : Type*} [TopologicalSpace X] (P U : Set X)
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U}) (p c₀ : ℝ)
    (hstrip : ∀ t : OpenRealInterval 0 1, (t : ℝ) ∈ Set.Ioo p c₀ →
      ((ψ t : {x : X // x ∈ U}) : X) ∈ P) :
    stripPoints U ψ p c₀ ⊆ P := by
  intro x hx
  rcases hx with ⟨t, ht, rfl⟩
  exact hstrip t ht

/-- **Step (ii) — the application**: for a boundary point `y` (`y ∉ P`) of
the arc prefix `P` (chart `κ`) with a U-side strip `(p, c₀)` inside the
overlap (`hstrip`, `c₀ := (ψ.symm ⟨y,·⟩ : ℝ)` the coordinate of `y`),
the κ-coordinate set of the strip POINT SET `stripPoints U ψ p c₀` is NOT
contained in any strict `(ε, 1−ε)` — it reaches an end of the prefix
coordinate (T1b core `end_coords_reach_prefix_end` applied with
`A := stripPoints …` through `stripPoints_subset` and
`stripPoints_mem_closure`). -/
theorem boundaryStrip_coords_reach_prefix_end {X : Type*} [TopologicalSpace X] [T2Space X]
    (P U : Set X) (κ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ P})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    {y : X} (hyU : y ∈ U) (hyPc : y ∉ P) {p : ℝ}
    (hpc : p < ((ψ.symm ⟨y, hyU⟩ : OpenRealInterval 0 1) : ℝ))
    (hstrip : ∀ t : OpenRealInterval 0 1, (t : ℝ) ∈
        Set.Ioo p ((ψ.symm ⟨y, hyU⟩ : OpenRealInterval 0 1) : ℝ) →
      ((ψ t : {x : X // x ∈ U}) : X) ∈ P) :
    ¬ ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 2 ∧
      (((↑) : OpenRealInterval 0 1 → ℝ) ''
        {r : OpenRealInterval 0 1 | ((κ r : {x : X // x ∈ P}) : X) ∈
          stripPoints U ψ p ((ψ.symm ⟨y, hyU⟩ : OpenRealInterval 0 1) : ℝ)})
        ⊆ Set.Ioo ε (1 - ε) := by
  let A : Set X := stripPoints U ψ p ((ψ.symm ⟨y, hyU⟩ : OpenRealInterval 0 1) : ℝ)
  have hAsub : A ⊆ P := by
    dsimp [A]
    exact stripPoints_subset P U ψ p ((ψ.symm ⟨y, hyU⟩ : OpenRealInterval 0 1) : ℝ) hstrip
  have hyA : y ∈ closure A := by
    dsimp [A]
    exact stripPoints_mem_closure U ψ hyU hpc
  have hres := end_coords_reach_prefix_end P κ hAsub hyPc hyA
  simpa [A] using hres




/-! ## 5. Step (iii) — the attach cutting from the prefix end (statement
pinned; first subgoal VERIFIED)

Per the S223 proof-obligation list, step (iii) is the attach cutting: from
the post-(ii) data (the U-side strip point set whose κ-coordinates reach
an end of the prefix coordinate) cut the open arc `V` with
`TerminalAttach P V κ s` (the chain step's `hVend` data against the
prefix chart `κ`) and `V ∖ P ≠ ∅`.  This section pins the precise
statement and verifies the first subgoal (the beyond-arc).

**Target definitions.**

- **`InitialAttach P V κ s`** — the INITIAL-strip attach: `V` meets `P`
  exactly over the initial interval `(0,s)` of the prefix coordinate
  (an attach at the `0`-end of the prefix; converted to a terminal
  `TerminalAttach` by reversing the prefix chart with the involution
  `t ↦ 1 − t`);
- **`EndStripAttach P V κ`** — `V` attaches over an END strip of the
  prefix chart (initial or terminal) — the orientation-neutral output of
  the cutting before the reversal normalization;
- **`AttachCuttingStatement P U κ ψ y`** — the theorem-shaped statement
  (record): with the open arc-chart `ψ : (0,1) ≃ₜ U` of the boundary
  point `y` (`y ∈ U`, `y ∉ P`), the overlap-coordinate real set `Sℝ`
  right-free at `c₀` (one-sided: the far side of `y` in `U` is free of
  `P` — supplies the beyond-arc), the T2 finite local structure (`hF`:
  the input the T2 geometric no-oscillation claim supplies), and the
  bridge input `y ∈ closure P` (S220), there is an open arc `V` with an
  interval chart, an END-STRIP attach over `κ` (`EndStripAttach P V κ`)
  and a genuine extension `V ∖ P ≠ ∅`.  The construction (recorded):
  cut the beyond-arc `B` from the right-free side of `y` in `U`
  (`right_free_beyond_arc` below: `B` nonempty and disjoint from `P` —
  the `V ∖ P` ingredient), take the prefix-end strip whose κ-coordinates
  the strip reaches (steps (i)/(ii): `boundaryStrip_coords_reach_prefix_end`),
  and assemble `V := κ((s,1)) ∪ B ∪ {small arc through y}` (or the
  initial-end mirror) with `V ∩ P = κ((s,1))` exactly — the assembly
  needs the transition/end sub-analysis (monotone limit of the chart
  transition at the strip end, so the κ-coordinate end strip is clean)
  and the reversal normalization, recorded with the T2 input.

**Verified first subgoal.**  **`right_free_beyond_arc`** — from the
right-freeness of the overlap set at `c₀` there is `δ > 0` such that the
beyond-arc `beyondArc U ψ c₀ δ` (the ψ-images of the chart coordinates
`(c₀, c₀+δ)`) is NONEMPTY and DISJOINT from `P`: the far side of the
boundary point in the arc chart is genuinely free of the prefix — the
`V ∖ P` ingredient of the attaching arc exists.  (The `δ` is shrunk to
`min δ₀ ((1−c₀)/2)` so the beyond interval stays inside the chart
`(0,1)`.)  Everything here is verified (no axioms, no `sorry`); the
`AttachCuttingStatement` record and the assembly above are the open
continuation (ROADMAP S224).
-/

/-- The INITIAL-strip attach: `V` meets `P` exactly over the initial
interval `(0,s)` of the prefix chart `κ`'s coordinate — an attach at the
`0`-end of the prefix (converted to a terminal `TerminalAttach` by
reversing the prefix chart). -/
def InitialAttach {X : Type*} [TopologicalSpace X] (P V : Set X)
    (κ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ P}) (s : ℝ) : Prop :=
  0 < s ∧ s < 1 ∧ ∀ t : OpenRealInterval 0 1,
    (((κ t : {x : X // x ∈ P}) : X)) ∈ V ↔ (t : ℝ) ∈ Set.Ioo 0 s

/-- The END-STRIP attach: `V` attaches over an end strip of the prefix
chart `κ` — terminal (`TerminalAttach P V κ s`) or initial
(`InitialAttach P V κ s`) — the orientation-neutral output of the attach
cutting before the reversal normalization. -/
def EndStripAttach {X : Type*} [TopologicalSpace X] (P V : Set X)
    (κ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ P}) : Prop :=
  (∃ s : ℝ, TerminalAttach P V κ s) ∨ (∃ s : ℝ, InitialAttach P V κ s)

/-- **The attach-cutting target (record)**: at a boundary point `y` of
the arc prefix `P` (`y ∈ U`, `y ∉ P`), in the open arc chart
`ψ : (0,1) ≃ₜ U` whose overlap-coordinate real set `Sℝ` is right-free at
`c₀` (one-sided: the far side of `y` in `U` is free of `P`) and has the
T2 finite local structure (`hF`), with the bridge input `y ∈ closure P`
(S220), there is an open arc `V` with an interval chart attaching over an
END STRIP of the prefix chart `κ` (`EndStripAttach P V κ`) and genuinely
extending `P` (`V ∖ P ≠ ∅`).  The construction (recorded in the module
doc): beyond-arc from `right_free_beyond_arc` + the prefix-end strip of
steps (i)/(ii) + the assembly through `y` (open in ROADMAP S224). -/
def AttachCuttingStatement {X : Type*} [TopologicalSpace X] (P U : Set X)
    (κ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ P})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U}) {y : X} (hyU : y ∈ U)
    (hyPc : y ∉ P) : Prop :=
  let Sℝ : Set ℝ := ((↑) : OpenRealInterval 0 1 → ℝ) ''
    {t : OpenRealInterval 0 1 | ((ψ t : {x : X // x ∈ U}) : X) ∈ P}
  let c₀ : ℝ := ((ψ.symm ⟨y, hyU⟩ : OpenRealInterval 0 1) : ℝ)
  IsOpen U → RightFreeAt Sℝ c₀ →
    (∃ F : Finset (ℝ × ℝ),
      Sℝ ∩ Set.Iio c₀ = ⋃ p ∈ F, Set.Ioo p.1 p.2 ∧ ∀ p ∈ F, p.2 ≤ c₀) →
    y ∈ closure P →
    ∃ V : Set X, IsOpen V ∧ Nonempty (OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V}) ∧
      EndStripAttach P V κ ∧ (V \ P).Nonempty

/-- The beyond-arc on the far side of the boundary coordinate: the
ψ-images of the chart coordinates `(c₀, c₀+δ)`. -/
def beyondArc {X : Type*} [TopologicalSpace X] (U : Set X)
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U}) (c₀ δ : ℝ) : Set X :=
  (fun t : OpenRealInterval 0 1 => ((ψ t : {x : X // x ∈ U}) : X)) ''
    {t : OpenRealInterval 0 1 | (t : ℝ) ∈ Set.Ioo c₀ (c₀ + δ)}

/-- **First subgoal of the attach cutting (VERIFIED)**: from the
right-freeness of the overlap-coordinate set at `c₀` there is `δ > 0`
such that the beyond-arc `beyondArc U ψ c₀ δ` is NONEMPTY and DISJOINT
from `P` — the far side of the boundary point in the arc chart is
genuinely free of the prefix (the `V ∖ P` ingredient of the attaching
arc exists).  The `δ` is shrunk to `min δ₀ ((1−c₀)/2)` so the beyond
interval stays inside the chart `(0,1)`. -/
theorem right_free_beyond_arc {X : Type*} [TopologicalSpace X]
    (P U : Set X) (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    {y : X} (hyU : y ∈ U)
    (hfree : RightFreeAt (((↑) : OpenRealInterval 0 1 → ℝ) ''
      {t : OpenRealInterval 0 1 | ((ψ t : {x : X // x ∈ U}) : X) ∈ P})
      ((ψ.symm ⟨y, hyU⟩ : OpenRealInterval 0 1) : ℝ)) :
    let c₀ : ℝ := ((ψ.symm ⟨y, hyU⟩ : OpenRealInterval 0 1) : ℝ)
    ∃ δ : ℝ, 0 < δ ∧ (beyondArc U ψ c₀ δ).Nonempty ∧ beyondArc U ψ c₀ δ ∩ P = ∅ := by
  let c₀ : ℝ := ((ψ.symm ⟨y, hyU⟩ : OpenRealInterval 0 1) : ℝ)
  let S : Set ℝ := ((↑) : OpenRealInterval 0 1 → ℝ) ''
    {t : OpenRealInterval 0 1 | ((ψ t : {x : X // x ∈ U}) : X) ∈ P}
  rcases hfree with ⟨δ₀, hδ₀0, hδ₀⟩
  let δ : ℝ := min δ₀ ((1 - c₀) / 2)
  have hδ0 : 0 < δ := by
    dsimp [δ]
    have h1 : 0 < (1 - c₀) / 2 := by
      have hc₀lt : c₀ < 1 := (ψ.symm ⟨y, hyU⟩ : OpenRealInterval 0 1).2.2
      positivity
    exact lt_min hδ₀0 h1
  have hδδ₀ : δ ≤ δ₀ := by dsimp [δ]; exact min_le_left δ₀ ((1 - c₀) / 2)
  have hc₀ : c₀ ∈ Set.Ioo (0 : ℝ) 1 := (ψ.symm ⟨y, hyU⟩ : OpenRealInterval 0 1).2
  have hδbd : c₀ + δ < 1 := by
    have hδle : δ ≤ (1 - c₀) / 2 := by dsimp [δ]; exact min_le_right δ₀ ((1 - c₀) / 2)
    nlinarith [hc₀.2]
  refine ⟨δ, hδ0, ?_, ?_⟩
  · have hmid : c₀ + δ / 2 ∈ Set.Ioo c₀ (c₀ + δ) := by constructor <;> linarith
    have hmid01 : c₀ + δ / 2 ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> nlinarith [hc₀.1, hδbd]
    refine ⟨(ψ ⟨c₀ + δ / 2, hmid01⟩ : {x : X // x ∈ U}), ?_⟩
    dsimp [beyondArc, δ]
    exact Set.mem_image_of_mem
      (fun t : OpenRealInterval 0 1 => ((ψ t : {x : X // x ∈ U}) : X)) hmid
  · rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    rcases hx with ⟨hxB, hxP⟩
    rcases hxB with ⟨t, ht, rfl⟩
    have htS : ((ψ t : {x : X // x ∈ U}) : X) ∈ P := hxP
    have htS' : t.1 ∈ S := by
      dsimp [S]
      exact Set.mem_image_of_mem (fun u : OpenRealInterval 0 1 => (u : ℝ)) htS
    have hδsub : Set.Ioo c₀ (c₀ + δ) ⊆ Set.Ioo c₀ (c₀ + δ₀) := by
      intro z hz
      exact ⟨hz.1, by linarith [hz.2, hδδ₀]⟩
    have hmem : (t.1 : ℝ) ∈ S ∩ Set.Ioo c₀ (c₀ + δ₀) := ⟨htS', hδsub ht⟩
    exact (eq_empty_iff_forall_notMem.mp hδ₀) t.1 hmem




/-! ## 6. Step (iii-a) — the clean prefix-end strip (payoff VERIFIED)

Per the S224 proof-obligation list, iii-a makes the prefix-end strip
clean: the κ-coordinate set of the U-side strip point set (reaching an
end of the prefix coordinate by steps (i)/(ii)) is shown to be EXACTLY a
terminal strip `(a,1)` or an initial strip `(0,b)` of the prefix
coordinate, from which the attaching arc is cut.  The analysis is
cleaner than a monotone-limit argument: the coordinate set is OPEN and
PRECONNECTED (a connected image of the chart-open strip — the bridge
outputs `hTopen`/`hTpc`/`hTne`, to be verified in the next lemma) and
UNTRAPPED (the T1b core `end_coords_reach_prefix_end`); the real model
of `(0,1)` says an open preconnected nonempty untrapped subset is
exactly `(a,1)` or `(0,b)` — the fleet L39
`Commons.Analysis.RealIntervals.open_preconnected_untrapped_unit_end_strip`
(open preconnected nonempty `⊆ (0,1)`, not trapped in any `(ε,1−ε)` ⇒
terminal or initial strip).

**`boundaryStrip_coords_end_strip`** (VERIFIED — the payoff): with the
arc prefix `P` (chart `κ`), the strip point set `stripPoints U ψ p c₀`
(`A ⊆ P` by `hAsub`, boundary point `y` with `y ∉ P` and
`y ∈ closure A` by `hyA`), and the bridge outputs (the coordinate set
`T := boundaryStripCoordSet P U κ ψ p c₀` open, preconnected, nonempty),
the coordinate set is a clean END STRIP of the prefix coordinate:
`T = (a,1)` (`0 ≤ a < 1`) or `T = (0,b)` (`0 < b ≤ 1`).  Proof: the
untrapped fact from `end_coords_reach_prefix_end` (`T ⊆ (0,1)` since
each element is the value of an ORI coordinate) + L39.

The remaining iii-a bridge (T open + preconnected + nonempty from the
openness/connectedness of `stripPoints` through the chart homeomorphisms)
is the next lemma; iii-b (the cutting assembly from the clean end strip)
and iii-c (the T2 input) follow.  Everything here is verified (no axioms,
no `sorry`).
-/

/-- The κ-coordinate set of the U-side strip point set: the values in the
prefix coordinate `(0,1)` of the points of `stripPoints U ψ p c₀`. -/
def boundaryStripCoordSet {X : Type*} [TopologicalSpace X] (P U : Set X)
    (κ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ P})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U}) (p c₀ : ℝ) : Set ℝ :=
  ((↑) : OpenRealInterval 0 1 → ℝ) ''
    {r : OpenRealInterval 0 1 | ((κ r : {x : X // x ∈ P}) : X) ∈ stripPoints U ψ p c₀}

/-- **Step (iii-a) payoff (VERIFIED)**: for a strip point set
`A := stripPoints U ψ p c₀` of the arc prefix `P` (`A ⊆ P` by `hAsub`,
boundary point `y` with `y ∉ P` and `y ∈ closure A` by `hyA`), whose
κ-coordinate set `T := boundaryStripCoordSet P U κ ψ p c₀` is OPEN,
PRECONNECTED and NONEMPTY (the bridge outputs), `T` is a clean END STRIP
of the prefix coordinate: `T = (a,1)` (`0 ≤ a < 1`, terminal) or
`T = (0,b)` (`0 < b ≤ 1`, initial) — via the untrapped fact
(`end_coords_reach_prefix_end`, T1b core) and the fleet L39
`open_preconnected_untrapped_unit_end_strip`. -/
theorem boundaryStrip_coords_end_strip {X : Type*} [TopologicalSpace X] [T2Space X]
    (P U : Set X) (κ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ P})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    {y : X} (hyPc : y ∉ P) (p c₀ : ℝ)
    (hAsub : stripPoints U ψ p c₀ ⊆ P)
    (hyA : y ∈ closure (stripPoints U ψ p c₀))
    (hTopen : IsOpen (boundaryStripCoordSet P U κ ψ p c₀))
    (hTpc : IsPreconnected (boundaryStripCoordSet P U κ ψ p c₀))
    (hTne : (boundaryStripCoordSet P U κ ψ p c₀).Nonempty) :
    (∃ a : ℝ, 0 ≤ a ∧ a < 1 ∧ boundaryStripCoordSet P U κ ψ p c₀ = Set.Ioo a 1) ∨
      (∃ b : ℝ, 0 < b ∧ b ≤ 1 ∧ boundaryStripCoordSet P U κ ψ p c₀ = Set.Ioo 0 b) := by
  let T : Set ℝ := boundaryStripCoordSet P U κ ψ p c₀
  have hunt : ¬ ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 2 ∧ T ⊆ Set.Ioo ε (1 - ε) := by
    dsimp [T]
    exact end_coords_reach_prefix_end P κ hAsub hyPc hyA
  have hT01 : T ⊆ Set.Ioo (0 : ℝ) 1 := by
    intro r hr
    dsimp [T, boundaryStripCoordSet] at hr
    rcases hr with ⟨t, ht, rfl⟩
    exact t.2
  exact Commons.Analysis.RealIntervals.open_preconnected_untrapped_unit_end_strip
    hT01 hTopen hTpc hTne hunt




/-! ## 7. Step (iii-b) — the cutting assembly (statement pinned; first
real-coordinate sublemma VERIFIED)

Per the S225 status, iii-b is the cutting assembly: from the clean end
strip (iii-a: the κ-coordinate set `T` of the strip point set is `(a,1)`
or `(0,b)`) cut the attaching arc `V` with `TerminalAttach P V κ s` and
`V ∖ P ≠ ∅`.

**The construction (terminal subcase, recorded).**  Let the strip be the
set of U-coordinates `(p, c₀)` inside the overlap (`S ⊇ (p,c₀)`, from
L36), right-free beyond `c₀` (`S ∩ (c₀, c₀+δ) = ∅`), and let its
κ-coordinate set be the terminal strip `(a,1)` (iii-a).  Then the
attaching arc is the ψ-arc through the boundary point `y` beyond it:
`V := ψArc U ψ p (c₀+δ)` (the ψ-images of the coordinates `(p, c₀+δ)`).
The four proof obligations (the next sub-lemmas):
1. `V ∩ P ∩ U` has U-coordinates exactly `(p,c₀)` — the real cut
   `S ∩ Ioo p (c₀+δ) = Ioo p c₀` (VERIFIED below as
   **`overlapStrip_rightFree_cut_at_left`**: the strip fills `(p,c₀)`,
   right-freeness kills `(c₀,c₀+δ)`, `c₀ ∉ S` kills `c₀`), transported
   by `ψ`; hence `V ∩ P = A := stripPoints U ψ p c₀`;
2. `A = κ((a,1))` (the pointwise coordinate identity
   `(κ r : X) ∈ A ↔ (r : ℝ) ∈ (a,1)`, from `T = (a,1)` + `A ⊆ P` +
   `T = val '' {r | κ r ∈ A}`), giving `V ∩ P = κ((a,1))` — the
   `TerminalAttach P V κ a` data (`s := a`, `0 < a < 1`);
3. `V` is open and interval-charted (`ψ` is a homeo onto the open set
   `U`, the coordinate interval `(p, c₀+δ)` is open and `≃ₜ (0,1)`);
4. `V ∖ P ≠ ∅` (the beyond bit `ψArc U ψ c₀ (c₀+δ) ⊆ V ∖ P` — the
   `right_free_beyond_arc` content of S224).

The initial subcase (`T = (0,b)`) is the mirror: attach at the `0`-end,
then reverse the prefix chart with `t ↦ 1 − t` to normalize to
`TerminalAttach`.  The target record
**`AttachCuttingTerminalAssembled`** fixes the terminal-subcase statement.
Everything here is verified (no axioms, no `sorry`); obligations 2–4 are
the next sub-lemmas.
-/

/-- The ψ-arc over a real coordinate interval `(lo, hi)`: the ψ-images of
the chart coordinates strictly between `lo` and `hi` (an open arc of the
chart; `beyondArc` is the special case `(c₀, c₀+δ)`). -/
def ψArc {X : Type*} [TopologicalSpace X] (U : Set X)
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U}) (lo hi : ℝ) : Set X :=
  (fun t : OpenRealInterval 0 1 => ((ψ t : {x : X // x ∈ U}) : X)) ''
    {t : OpenRealInterval 0 1 | (t : ℝ) ∈ Set.Ioo lo hi}

/-- **Step (iii-b) first real-coordinate sublemma (VERIFIED)**: given the
strip `(p,c₀) ⊆ S` (from L36), `c₀ ∉ S` and right-freeness beyond `c₀`
(`S ∩ (c₀, c₀+δ) = ∅`), the overlap of `S` with the attaching interval
`(p, c₀+δ)` is EXACTLY the strip `(p,c₀)` — the strip fills the left
part, right-freeness kills `(c₀,c₀+δ)`, `c₀ ∉ S` kills `c₀`.  (The
`V ∩ P` half of the attach, at the real-coordinate level.) -/
theorem overlapStrip_rightFree_cut_at_left {S : Set ℝ} {c₀ p : ℝ} (hcS : c₀ ∉ S)
    (hstrip : Set.Ioo p c₀ ⊆ S) {δ : ℝ} (hδ0 : 0 < δ)
    (hfree : S ∩ Set.Ioo c₀ (c₀ + δ) = ∅) :
    S ∩ Set.Ioo p (c₀ + δ) = Set.Ioo p c₀ := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hxS, hxI⟩
    rcases hxI with ⟨hpx, hxcδ⟩
    constructor
    · exact hpx
    · by_contra hxge
      have hxc_ne : x ≠ c₀ := by
        intro hxc
        exact hcS (by simpa [hxc] using hxS)
      have hxgt : c₀ < x := lt_of_le_of_ne (le_of_not_gt hxge) hxc_ne.symm
      have hxδ : x ∈ Set.Ioo c₀ (c₀ + δ) := ⟨hxgt, hxcδ⟩
      exact (eq_empty_iff_forall_notMem.mp hfree) x ⟨hxS, hxδ⟩
  · intro hx
    rcases hx with ⟨hpx, hxc₀⟩
    refine ⟨hstrip ⟨hpx, hxc₀⟩, ⟨hpx, by linarith⟩⟩

/-- **The terminal-subcase cutting statement (record)**: from the strip
`(p,c₀)` inside the overlap, the right-freeness beyond `c₀`, the
coordinate-interval containment `(p, c₀+δ) ⊆ (0,1)`, the prefix-end
identity `A = κ((a,1))` (`0 < a < 1`), and the openness/arc-charting of
`U`, the ψ-arc `V := ψArc U ψ p (c₀+δ)` is the attaching arc:
`TerminalAttach P V κ a` with `V ∖ P ≠ ∅`.  Proof obligations 1–4 in the
module doc; obligation 1's real half is
`overlapStrip_rightFree_cut_at_left`. -/
def AttachCuttingTerminalAssembled {X : Type*} [TopologicalSpace X]
    (P U : Set X) (κ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ P})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U}) (p c₀ a : ℝ) : Prop :=
  IsOpen U → IsOpen P → P ≠ Set.univ → 0 < a → a < 1 →
  (∃ δ : ℝ, 0 < δ ∧ c₀ + δ < 1 ∧ Set.Ioo p (c₀ + δ) ⊆ Set.Ioo 0 1 ∧
    Set.Ioo p c₀ ⊆ Set.Ioo 0 1) →
  (∀ r : OpenRealInterval 0 1,
    ((κ r : {x : X // x ∈ P}) : X) ∈ stripPoints U ψ p c₀ ↔ (r : ℝ) ∈ Set.Ioo a 1) →
  ∃ V : Set X, IsOpen V ∧ Nonempty (OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V}) ∧
    TerminalAttach P V κ a ∧ (V \ P).Nonempty




/-! ## 8. Step (iii-b-2) — the prefix-end identity (VERIFIED)

Per the S226 sub-lemma list, iii-b-2 is the bridge from the
real-coordinate interval cut to the `TerminalAttach` boundary condition:
the strip point set `A := stripPoints U ψ p c₀` equals the prefix-end
point set `κ((a,1))` (the points of `P` whose κ-coordinate lies in the
terminal strip `(a,1)`) whenever the κ-coordinate set of `A` IS the
terminal strip `(a,1)` (iii-a's payoff).

- **`stripPoints_mem_iff_of_coordSet`** — the pointwise identity: from
  `T := boundaryStripCoordSet P U κ ψ p c₀ = Ioo a 1` (iii-a),
  `((κ r : X) ∈ A) ↔ (r : ℝ) ∈ Ioo a 1` for every chart coordinate `r` —
  the exact shape the `TerminalAttach` membership-iff needs.  Proof:
  `(κ r : X) ∈ A ⟺ r ∈ {r' | (κ r' : X) ∈ A} ⟺ (r : ℝ) ∈ val '' {…} =
  (a,1)` — the forward direction by `mem_image_of_mem`, the reverse by
  the injectivity of the coordinate value map (`Subtype.ext` on the
  witness `r′` with equal values);
- **`stripPoints_eq_prefixEnd_of_coordSet`** — the SET identity
  `A = κ((a,1))`: `stripPoints U ψ p c₀` equals
  `(val∘κ) '' {r | (r : ℝ) ∈ Ioo a 1}` — from the pointwise identity and
  `A ⊆ P` (`hAsub`: each `x ∈ A` has the κ-coordinate
  `r := κ⁻¹⟨x, hAsub hx⟩`, whose value lies in `(a,1)` by the iff).

This is exactly obligation 2 of the S226 cutting assembly: with
`V ∩ P = A` (obligation 1, real cut transported by `ψ`) the set identity
gives `V ∩ P = κ((a,1))`, i.e. the `TerminalAttach P V κ a` data
(`s := a`, `0 < a < 1` from iii-a).  Everything here is verified (no
axioms, no `sorry`).
-/

/-- **iii-b-2 (pointwise)**: from the κ-coordinate set identity
`boundaryStripCoordSet P U κ ψ p c₀ = (a,1)` (iii-a's payoff), a point
of `P` with chart coordinate `r` lies in the strip point set `A` iff its
coordinate lies in the terminal strip `(a,1)` — the exact shape the
`TerminalAttach` membership-iff needs. -/
theorem stripPoints_mem_iff_of_coordSet {X : Type*} [TopologicalSpace X]
    (P U : Set X) (κ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ P})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U}) (p c₀ a : ℝ)
    (hT : boundaryStripCoordSet P U κ ψ p c₀ = Set.Ioo a 1) :
    ∀ r : OpenRealInterval 0 1,
      ((κ r : {x : X // x ∈ P}) : X) ∈ stripPoints U ψ p c₀ ↔ (r : ℝ) ∈ Set.Ioo a 1 := by
  intro r
  constructor
  · intro hr
    have hval : (r : ℝ) ∈ boundaryStripCoordSet P U κ ψ p c₀ := by
      dsimp [boundaryStripCoordSet]
      exact Set.mem_image_of_mem (fun t : OpenRealInterval 0 1 => (t : ℝ)) hr
    rwa [hT] at hval
  · intro hr
    have hmem : (r : ℝ) ∈ boundaryStripCoordSet P U κ ψ p c₀ := by
      rwa [hT]
    rcases hmem with ⟨r', hr', hval⟩
    have hr'eq : r' = r := by
      apply Subtype.ext
      exact hval
    simpa [hr'eq] using hr'

/-- **iii-b-2 (set identity)**: the strip point set equals the
prefix-end point set `κ((a,1))` (the points of `P` with coordinate in
`(a,1)`), from the coordinate-set identity and `A ⊆ P` — with
`V ∩ P = A` this gives `V ∩ P = κ((a,1))`, the `TerminalAttach` boundary
condition. -/
theorem stripPoints_eq_prefixEnd_of_coordSet {X : Type*} [TopologicalSpace X]
    (P U : Set X) (κ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ P})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U}) (p c₀ a : ℝ)
    (hAsub : stripPoints U ψ p c₀ ⊆ P)
    (hT : boundaryStripCoordSet P U κ ψ p c₀ = Set.Ioo a 1) :
    stripPoints U ψ p c₀ =
      (fun r : OpenRealInterval 0 1 => ((κ r : {x : X // x ∈ P}) : X)) ''
        {r : OpenRealInterval 0 1 | (r : ℝ) ∈ Set.Ioo a 1} := by
  have hiff := stripPoints_mem_iff_of_coordSet P U κ ψ p c₀ a hT
  ext x
  constructor
  · intro hx
    let r : OpenRealInterval 0 1 := κ.symm ⟨x, hAsub hx⟩
    have hκr : ((κ r : {x : X // x ∈ P}) : X) = x := by
      dsimp [r]
      simp
    have hra : (r : ℝ) ∈ Set.Ioo a 1 := (hiff r).1 (by simpa [hκr] using hx)
    refine ⟨r, hra, ?_⟩
    exact hκr
  · intro hx
    rcases hx with ⟨r, hr, rfl⟩
    exact (hiff r).2 hr




/-! ## 9. Step (iii-b-3) — openness and interval-charting of `ψArc`
(VERIFIED)

Per the S227 sub-lemma list, iii-b-3 certifies that the attaching arc
`V := ψArc U ψ p (c₀+δ)` is an OPEN interval-charted arc: `ψArc_isOpen`
(the chart-arc over any real coordinate interval `(lo,hi)` is open in
`X` when `U` is open — the commons L40 `chartArc_isOpen`: coordinate
strip open in the unit interval, `ψ` a homeo, and the subtype embedding
of the OPEN set `U` is an open map), and `ψArc_intervalChart` (if the
coordinate interval meets `(0,1)`, the chart-arc is interval-charted:
`ORI ≃ₜ ↑(ψArc U ψ lo hi)` — the commons L41 `chartArc_intervalChart`,
transported by `e.symm`).  The helper
`interval_meets_unit_of_nonneg_bounds` supplies the `hne` hypothesis for
the attach interval `(p, c₀+δ)` from `0 ≤ p`, `c₀+δ ≤ 1`, `p < c₀+δ`.
Everything here is verified (no axioms, no `sorry`).
-/

/-- **iii-b-3 (openness)**: the chart-arc over the real coordinate
interval `(lo,hi)` is open in `X` whenever the chart carrier `U` is open
(the commons L40: coordinate strip open in the unit interval, `ψ` a
homeo, subtype embedding of the open set `U` is an open map). -/
theorem ψArc_isOpen {X : Type*} [TopologicalSpace X] (U : Set X) (hUopen : IsOpen U)
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U}) (lo hi : ℝ) :
    IsOpen (ψArc U ψ lo hi) := by
  simpa [ψArc] using (Commons.Topology.Charts.chartArc_isOpen (X := X) U hUopen ψ lo hi)

/-- **iii-b-3 (interval-charting)**: if the coordinate interval meets the
open unit interval, the chart-arc `ψArc U ψ lo hi` is interval-charted
(`ORI ≃ₜ ↑(ψArc …)`) — the commons L41 transported by `e.symm`. -/
theorem ψArc_intervalChart {X : Type*} [TopologicalSpace X] (U : Set X)
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U}) (lo hi : ℝ)
    (hne : (Set.Ioo lo hi ∩ Set.Ioo 0 1).Nonempty) :
    Nonempty (OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ ψArc U ψ lo hi}) := by
  rcases Commons.Topology.Charts.chartArc_intervalChart (X := X) U ψ lo hi hne with ⟨e⟩
  exact ⟨e.symm⟩

/-- The coordinate interval `(lo,hi)` meets the open unit interval when it
is nonempty and lies within it (`0 ≤ lo`, `hi ≤ 1`, `lo < hi`) — the
`hne` source for the attach interval `(p, c₀+δ)`. -/
lemma interval_meets_unit_of_nonneg_bounds {lo hi : ℝ} (hlo0 : 0 ≤ lo) (hhi1 : hi ≤ 1)
    (hlo : lo < hi) : (Set.Ioo lo hi ∩ Set.Ioo 0 1).Nonempty := by
  refine ⟨(lo + hi) / 2, ?_, ?_⟩
  · constructor <;> linarith
  · constructor <;> linarith




/-! ## 10. Step (iii-b-4) — the attaching arc genuinely extends `P`
(VERIFIED)

Per the S228 sub-lemma list, iii-b-4 closes the last obligation of the
cutting assembly: `V ∖ P ≠ ∅` for the attaching arc
`V := ψArc U ψ p (c₀+δ)`.  The beyond bit does the work:
`beyondArc U ψ c₀ δ` (the ψ-images of the coordinates `(c₀, c₀+δ)`)
sits inside `V` (its coordinate interval is contained in `(p, c₀+δ)`
when `p ≤ c₀`), is nonempty, and is disjoint from `P`
(`right_free_beyond_arc`, S224, from the one-sided right-freeness).
Picking the beyond point gives the witness: it lies in `V` and outside
`P`.

**`ψArc_diff_P_nonempty`** (VERIFIED): from `p ≤ c₀`, `0 < δ`, a
NONEMPTY beyond arc, and its disjointness from `P` (`hbdP`),
`(ψArc U ψ p (c₀ + δ) \ P).Nonempty`.  Proof: the beyond point `x`
(= `(ψ t : X)` for `t` with `c₀ < t.1 < c₀ + δ`) lies in `ψArc U ψ p
(c₀+δ)` (its coordinate satisfies `p < t.1` since `p ≤ c₀ < t.1`) and is
outside `P` by `hbdP`.

With this, all four obligations of the cutting assembly (S226 module
doc) are VERIFIED: (1) the real cut `overlapStrip_rightFree_cut_at_left`
+ the `ψ` transport give `V ∩ P = A`; (2) the prefix-end identity
`stripPoints_eq_prefixEnd_of_coordSet` (S227) gives
`V ∩ P = κ((a,1))` — the `TerminalAttach P V κ a` data; (3)
`ψArc_isOpen`/`ψArc_intervalChart` (S228) give `V` an open
interval-charted arc; (4) `ψArc_diff_P_nonempty` (this section) gives
`V ∖ P ≠ ∅`.  The terminal-subcase assembly theorem
(`AttachCuttingTerminalAssembled`) is one composition away (the remaining
plumbing: assembling the hypotheses from the boundary data — the S220
bridge + S221 strip + iii-a payoff).  Everything here is verified (no
axioms, no `sorry`).
-/

/-- **iii-b-4 (VERIFIED)**: the attaching arc `ψArc U ψ p (c₀+δ)`
genuinely extends `P` — it contains the beyond point (`p ≤ c₀` puts the
beyond bit's coordinates inside the attach interval), which is outside
`P` by the beyond arc's disjointness. -/
theorem ψArc_diff_P_nonempty {X : Type*} [TopologicalSpace X]
    (P U : Set X) (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    {p c₀ δ : ℝ} (hpc₀ : p ≤ c₀) (hδ0 : 0 < δ)
    (hbd : (beyondArc U ψ c₀ δ).Nonempty)
    (hbdP : beyondArc U ψ c₀ δ ∩ P = ∅) :
    (ψArc U ψ p (c₀ + δ) \ P).Nonempty := by
  rcases hbd with ⟨x, hxB⟩
  refine ⟨x, ?_, ?_⟩
  · rcases hxB with ⟨t, ht, rfl⟩
    apply Set.mem_image_of_mem
    constructor
    · exact lt_of_le_of_lt hpc₀ ht.1
    · exact ht.2
  · intro hxP
    have hxmem : x ∈ beyondArc U ψ c₀ δ ∩ P := ⟨hxB, hxP⟩
    exact (eq_empty_iff_forall_notMem.mp hbdP) x hxmem




/-! ## 11. The terminal-subcase cutting assembly (VERIFIED)

Per the S229 status, the cutting assembly's four obligations are each
verified; this section closes the assembly itself: the terminal-subcase
theorem **`attach_cutting_terminal`** produces the attaching arc
`V := ψArc U ψ p (c₀+δ)` with all four clauses, from the boundary data
(the real cut, the prefix-end identity, the openness/arc-charting, the
beyond arc).  Two helper identities make the composition clean:

- **`chart_mem_P_iff_coord`** — a chart point `(ψ t : X)` lies in `P`
  iff its coordinate lies in the real overlap set `Sℝ` (value-injectivity
  of the coordinate map);
- **`P_inter_ψArc_eq_stripPoints`** — from the real cut
  (`hcut : Sℝ ∩ (p, c₀+δ) = (p, c₀)`) the prefix-overlap of the attach
  arc is exactly the strip point set: `P ∩ ψArc U ψ p (c₀+δ) =
  stripPoints U ψ p c₀`.

**`attach_cutting_terminal`** (VERIFIED): with `U` open, the strip data
(`p < c₀`, `c₀ ∈ (0,1)`, `0 < δ`), the clean terminal end (`0 < a < 1`,
the prefix-end identity `hiff`), the real cut `hcut`, and the beyond arc
(`hbd`, `hbdP`), the arc `V := ψArc U ψ p (c₀+δ)` satisfies:
`IsOpen V` (obligation 3a), `ORI ≃ₜ ↑V` (obligation 3b),
`TerminalAttach P V κ a` (obligations 1+2: `(κ t : X) ∈ V` iff
`t ∈ (a,1)` via `P ∩ V = A` and `hiff`), and `V \ P ≠ ∅` (obligation
4).  Proof: `refine ⟨V, …⟩` with the four clauses, each from its
section's theorem.  This is the terminal half of
`AttachCuttingTerminalAssembled` (the def's `∃ V` conclusion, assembled
from the boundary data).  Everything here is verified (no axioms, no
`sorry`).
-/

/-- A chart point `(ψ t : X)` lies in `P` iff its coordinate lies in the
real overlap-coordinate set `Sℝ` (the value map of the unit interval is
injective). -/
theorem chart_mem_P_iff_coord {X : Type*} [TopologicalSpace X] (P U : Set X)
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U}) :
    let Sℝ : Set ℝ := ((↑) : OpenRealInterval 0 1 → ℝ) ''
      {t : OpenRealInterval 0 1 | ((ψ t : {x : X // x ∈ U}) : X) ∈ P}
    ∀ t : OpenRealInterval 0 1, ((ψ t : {x : X // x ∈ U}) : X) ∈ P ↔ (t : ℝ) ∈ Sℝ := by
  intro Sℝ t
  constructor
  · intro ht
    dsimp [Sℝ]
    exact Set.mem_image_of_mem (fun u : OpenRealInterval 0 1 => (u : ℝ)) ht
  · intro hts
    dsimp [Sℝ] at hts
    rcases hts with ⟨t', ht', hval⟩
    have ht'eq : t' = t := by
      apply Subtype.ext
      exact hval
    simpa [ht'eq] using ht'

/-- From the real cut `Sℝ ∩ (p, c₀+δ) = (p,c₀)` the prefix-overlap of
the attach arc is exactly the strip point set:
`P ∩ ψArc U ψ p (c₀+δ) = stripPoints U ψ p c₀`. -/
theorem P_inter_ψArc_eq_stripPoints {X : Type*} [TopologicalSpace X] (P U : Set X)
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U}) (p c₀ δ : ℝ)
    (hδ0 : 0 < δ)
    (hcut : (((↑) : OpenRealInterval 0 1 → ℝ) ''
      {t : OpenRealInterval 0 1 | ((ψ t : {x : X // x ∈ U}) : X) ∈ P}) ∩ Set.Ioo p (c₀ + δ)
        = Set.Ioo p c₀) :
    P ∩ ψArc U ψ p (c₀ + δ) = stripPoints U ψ p c₀ := by
  let Sℝ : Set ℝ := ((↑) : OpenRealInterval 0 1 → ℝ) ''
    {t : OpenRealInterval 0 1 | ((ψ t : {x : X // x ∈ U}) : X) ∈ P}
  have hiff := chart_mem_P_iff_coord P U ψ
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hxP, hxV⟩
    rcases hxV with ⟨t, ht, rfl⟩
    have htS : (t : ℝ) ∈ Sℝ := (hiff t).1 hxP
    have htin : (t : ℝ) ∈ Sℝ ∩ Set.Ioo p (c₀ + δ) := ⟨htS, ht⟩
    have htpc : (t : ℝ) ∈ Set.Ioo p c₀ := by
      rwa [hcut] at htin
    exact Set.mem_image_of_mem (fun u : OpenRealInterval 0 1 => ((ψ u : {x : X // x ∈ U}) : X))
      htpc
  · intro hxA
    rcases hxA with ⟨t, htpc, rfl⟩
    constructor
    · have htS : (t : ℝ) ∈ Sℝ := by
        have hin : (t : ℝ) ∈ Sℝ ∩ Set.Ioo p (c₀ + δ) := by
          rw [hcut]
          exact htpc
        exact hin.1
      exact (hiff t).2 htS
    · apply Set.mem_image_of_mem
      constructor
      · exact htpc.1
      · linarith [htpc.2, hδ0]

/-- **The terminal-subcase cutting assembly (VERIFIED)**: from the
boundary data (strip `p < c₀`, `c₀ ∈ (0,1)`, `0 < δ`; the clean terminal
end `0 < a < 1` with prefix-end identity `hiff`; the real cut `hcut`; the
beyond arc `hbd`/`hbdP`), the arc `V := ψArc U ψ p (c₀+δ)` is the
attaching arc: open, interval-charted, `TerminalAttach P V κ a`, and
`V \ P ≠ ∅`. -/
theorem attach_cutting_terminal {X : Type*} [TopologicalSpace X] [T2Space X]
    (P U : Set X) (κ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ P})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U}) (p c₀ δ a : ℝ)
    (hUopen : IsOpen U) (hpc₀ : p < c₀) (hc₀I : c₀ ∈ Set.Ioo 0 1) (hδ0 : 0 < δ)
    (ha0 : 0 < a) (ha1 : a < 1)
    (hcut : (((↑) : OpenRealInterval 0 1 → ℝ) ''
      {t : OpenRealInterval 0 1 | ((ψ t : {x : X // x ∈ U}) : X) ∈ P}) ∩ Set.Ioo p (c₀ + δ)
        = Set.Ioo p c₀)
    (hiff : ∀ r : OpenRealInterval 0 1,
      ((κ r : {x : X // x ∈ P}) : X) ∈ stripPoints U ψ p c₀ ↔ (r : ℝ) ∈ Set.Ioo a 1)
    (hbd : (beyondArc U ψ c₀ δ).Nonempty)
    (hbdP : beyondArc U ψ c₀ δ ∩ P = ∅) :
    ∃ V : Set X, IsOpen V ∧ Nonempty (OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V}) ∧
      TerminalAttach P V κ a ∧ (V \ P).Nonempty := by
  let V : Set X := ψArc U ψ p (c₀ + δ)
  have hVopen : IsOpen V := by
    dsimp [V]
    exact ψArc_isOpen U hUopen ψ p (c₀ + δ)
  have hVchart : Nonempty (OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V}) := by
    dsimp [V]
    refine ψArc_intervalChart U ψ p (c₀ + δ) ?_
    refine ⟨c₀, ?_, hc₀I⟩
    exact ⟨hpc₀, by linarith⟩
  have hVP : P ∩ V = stripPoints U ψ p c₀ := by
    dsimp [V]
    exact P_inter_ψArc_eq_stripPoints P U ψ p c₀ δ hδ0 hcut
  have hattach : TerminalAttach P V κ a := by
    constructor
    · exact ha0
    constructor
    · exact ha1
    intro t
    constructor
    · intro htV
      have hκtP : ((κ t : {x : X // x ∈ P}) : X) ∈ P := (κ t : {x : X // x ∈ P}).2
      have hκtVP : ((κ t : {x : X // x ∈ P}) : X) ∈ P ∩ V := ⟨hκtP, htV⟩
      have hκtA : ((κ t : {x : X // x ∈ P}) : X) ∈ stripPoints U ψ p c₀ := by
        simpa [hVP] using hκtVP
      exact (hiff t).1 hκtA
    · intro htI
      have hκtA : ((κ t : {x : X // x ∈ P}) : X) ∈ stripPoints U ψ p c₀ := (hiff t).2 htI
      have hκtVP : ((κ t : {x : X // x ∈ P}) : X) ∈ P ∩ V := by
        simpa [hVP] using hκtA
      exact hκtVP.2
  have hVdiff : (V \ P).Nonempty := by
    dsimp [V]
    exact ψArc_diff_P_nonempty P U ψ (le_of_lt hpc₀) hδ0 hbd hbdP
  refine ⟨V, hVopen, hVchart, hattach, hVdiff⟩




/-! ## 12. The initial-subcase cutting assembly (VERIFIED)

The mirror of section 11: when the κ-coordinate set of the strip point
set is the INITIAL strip `(0,b)` (iii-a's second disjunct), the attach
happens at the `0`-end of the prefix: the arc `V := ψArc U ψ p (c₀+δ)`
satisfies `InitialAttach P V κ b` (the pointwise membership
`(κ t : X) ∈ V ↔ (t : ℝ) ∈ (0,b)`) together with the other three clauses
(open, interval-charted, `V \ P ≠ ∅`).  **`attach_cutting_initial`**
(VERIFIED) mirrors `attach_cutting_terminal` with `0 < b < 1` and the
`(0,b)` interval.  The reversal normalization (turning `InitialAttach`
into a `TerminalAttach` against the reversed prefix chart `t ↦ 1 − t`)
is delegated as the standalone commons L42 `unitInterval_revHomeo` and
will be applied in a later step.  Everything here is verified (no axioms,
no `sorry`).
-/


theorem attach_cutting_initial {X : Type*} [TopologicalSpace X] [T2Space X]
    (P U : Set X) (κ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ P})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U}) (p c₀ δ b : ℝ)
    (hUopen : IsOpen U) (hpc₀ : p < c₀) (hc₀I : c₀ ∈ Set.Ioo 0 1) (hδ0 : 0 < δ)
    (hb0 : 0 < b) (hb1 : b < 1)
    (hcut : (((↑) : OpenRealInterval 0 1 → ℝ) ''
      {t : OpenRealInterval 0 1 | ((ψ t : {x : X // x ∈ U}) : X) ∈ P}) ∩ Set.Ioo p (c₀ + δ)
        = Set.Ioo p c₀)
    (hiff : ∀ r : OpenRealInterval 0 1,
      ((κ r : {x : X // x ∈ P}) : X) ∈ stripPoints U ψ p c₀ ↔ (r : ℝ) ∈ Set.Ioo 0 b)
    (hbd : (beyondArc U ψ c₀ δ).Nonempty)
    (hbdP : beyondArc U ψ c₀ δ ∩ P = ∅) :
    ∃ V : Set X, IsOpen V ∧ Nonempty (OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V}) ∧
      InitialAttach P V κ b ∧ (V \ P).Nonempty := by
  let V : Set X := ψArc U ψ p (c₀ + δ)
  have hVopen : IsOpen V := by
    dsimp [V]
    exact ψArc_isOpen U hUopen ψ p (c₀ + δ)
  have hVchart : Nonempty (OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V}) := by
    dsimp [V]
    refine ψArc_intervalChart U ψ p (c₀ + δ) ?_
    refine ⟨c₀, ?_, hc₀I⟩
    exact ⟨hpc₀, by linarith⟩
  have hVP : P ∩ V = stripPoints U ψ p c₀ := by
    dsimp [V]
    exact P_inter_ψArc_eq_stripPoints P U ψ p c₀ δ hδ0 hcut
  have hattach : InitialAttach P V κ b := by
    constructor
    · exact hb0
    constructor
    · exact hb1
    intro t
    constructor
    · intro htV
      have hκtP : ((κ t : {x : X // x ∈ P}) : X) ∈ P := (κ t : {x : X // x ∈ P}).2
      have hκtVP : ((κ t : {x : X // x ∈ P}) : X) ∈ P ∩ V := ⟨hκtP, htV⟩
      have hκtA : ((κ t : {x : X // x ∈ P}) : X) ∈ stripPoints U ψ p c₀ := by
        simpa [hVP] using hκtVP
      exact (hiff t).1 hκtA
    · intro htI
      have hκtA : ((κ t : {x : X // x ∈ P}) : X) ∈ stripPoints U ψ p c₀ := (hiff t).2 htI
      have hκtVP : ((κ t : {x : X // x ∈ P}) : X) ∈ P ∩ V := by
        simpa [hVP] using hκtA
      exact hκtVP.2
  have hVdiff : (V \ P).Nonempty := by
    dsimp [V]
    exact ψArc_diff_P_nonempty P U ψ (le_of_lt hpc₀) hδ0 hbd hbdP
  refine ⟨V, hVopen, hVchart, hattach, hVdiff⟩


/-! ## 13. The reversal normalization (VERIFIED)

The initial subcase of the attach cutting produces `InitialAttach P V κ b`
(section 12); the chain step (`OneStepTerminalExtension`) consumes
`TerminalAttach` data.  The reversal normalization converts one into the
other: reversing the prefix chart by the interval involution `t ↦ 1 − t`
turns the initial strip `(0,b)` into the terminal strip `(1−b, 1)` of the
reversed chart.

- **`revORI`** — the interval reversal `t ↦ 1 − t` of the open unit
  interval, a self-inverse homeomorphism (built with the standalone-`F`
  pattern: named membership function `memRev`, `Continuous.subtype_mk`
  with `f := fun t => 1 − (t:ℝ)`, `Function.LeftInverse` by
  `Subtype.ext` + `ring`); `revORI_val` — `(revORI t : ℝ) = 1 − (t:ℝ)`;
- **`initialAttach_to_terminal_rev`** — from `InitialAttach P V κ b`
  (`0 < b < 1`) the reversed prefix chart `revORI.trans κ` satisfies
  `TerminalAttach P V (revORI.trans κ) (1 − b)` (the membership
  `(κ (revORI t) : X) ∈ V` iff `(1 − (t:ℝ)) ∈ (0,b)` iff
  `(t : ℝ) ∈ (1−b, 1)`; the trans-application reduces by the `@[simp]`
  `Homeomorph.trans_apply` — use plain `simpa`, never
  `simpa [Homeomorph.trans]` which unfolds the def instead).

Everything here is verified (no axioms, no `sorry`).
-/

/-- The interval reversal `t ↦ 1 − t` of the open unit interval
(self-inverse homeomorphism). -/
def revORI : OpenRealInterval 0 1 ≃ₜ OpenRealInterval 0 1 := by
  have memRev : ∀ t : OpenRealInterval 0 1, 1 - (t : ℝ) ∈ Set.Ioo (0 : ℝ) 1 :=
    fun t => by constructor <;> linarith [t.2.1, t.2.2]
  let F : OpenRealInterval 0 1 → OpenRealInterval 0 1 := fun t => ⟨1 - (t : ℝ), memRev t⟩
  have hFcont : Continuous F :=
    Continuous.subtype_mk (f := fun t : OpenRealInterval 0 1 => 1 - (t : ℝ))
      (continuous_const.sub continuous_subtype_val) memRev
  have hF2 : Function.LeftInverse F F := by
    intro t
    apply Subtype.ext
    ring
  exact { toFun := F, invFun := F, left_inv := hF2, right_inv := hF2,
          continuous_toFun := hFcont, continuous_invFun := hFcont }

/-- The value of the reversal at `t` is `1 − t`. -/
lemma revORI_val (t : OpenRealInterval 0 1) : (revORI t : ℝ) = 1 - (t : ℝ) := by
  rfl

/-- **The reversal normalization**: an `InitialAttach` against the prefix
chart `κ` is a `TerminalAttach` against the reversed chart
`revORI.trans κ` (the initial strip `(0,b)` becomes the terminal strip
`(1−b, 1)`). -/
theorem initialAttach_to_terminal_rev {X : Type*} [TopologicalSpace X]
    (P V : Set X) (κ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ P}) {b : ℝ}
    (hInit : InitialAttach P V κ b) :
    TerminalAttach P V (revORI.trans κ) (1 - b) := by
  rcases hInit with ⟨hb0, hb1, hiff⟩
  constructor
  · linarith
  constructor
  · linarith
  intro t
  constructor
  · intro htV
    have hmem : ((κ (revORI t) : {x : X // x ∈ P}) : X) ∈ V := by
      simpa using htV
    have hr : ((revORI t : OpenRealInterval 0 1) : ℝ) ∈ Set.Ioo 0 b := (hiff (revORI t)).1 hmem
    rw [revORI_val] at hr
    constructor <;> linarith [hr.1, hr.2]
  · intro htI
    rcases htI with ⟨h1b, ht1⟩
    have hr : (1 - (t : ℝ)) ∈ Set.Ioo 0 b := by
      constructor <;> linarith
    have hmem : ((κ (revORI t : OpenRealInterval 0 1) : {x : X // x ∈ P}) : X) ∈ V :=
      (hiff (revORI t)).2 (by simpa [revORI_val] using hr)
    simpa using hmem




/-! ## 14. The attach-cutting disjunction realized (VERIFIED)

Per the S231 status, both halves of the attach cutting exist
(`attach_cutting_terminal`, `attach_cutting_initial`) and the initial
half normalizes to the `TerminalAttach` form
(`initialAttach_to_terminal_rev`).  This section realizes the
`EndStripAttach` disjunction of `AttachCuttingStatement` from the clean
end data: **`attach_cutting_endStrip`** — from the boundary data (open
`U`, the strip `p < c₀`, `c₀ ∈ (0,1)`, `0 < δ`, the real cut `hcut`),
the prefix-end identity as a disjunction over the terminal `(a,1)`
(`0 < a < 1`) or the initial `(0,b)` (`0 < b < 1`) interval
(`hend`), and the beyond arc (`hbd`, `hbdP`), the arc
`V := ψArc U ψ p (c₀+δ)` (the SAME arc in both cases) is open,
interval-charted, attaches over an END STRIP of the prefix chart
(`EndStripAttach P V κ`: `TerminalAttach` in the first case,
`InitialAttach` in the second), and `V \ P ≠ ∅`.  Proof: case-split on
`hend` and apply the corresponding half (rcases the output, provide
`Or.inl ⟨a, hTA⟩` / `Or.inr ⟨b, hIA⟩` for the `EndStripAttach`
disjunction).

The remaining instantiation — producing `hend` (and the `hcut`, `hbd`,
`hbdP`, `hpc₀` inputs) from the raw boundary data — needs the iii-a
bridge (the openness/preconnectedness/nonemptiness of the coordinate set
`T`, from which `boundaryStrip_coords_end_strip` produces the clean-end
disjunction) and the S220/S221/L36 transport, recorded in the ROADMAP.
Everything here is verified (no axioms, no `sorry`).
-/

/-- **The attach-cutting disjunction realized (VERIFIED)**: from the
boundary data and the clean END-STRIP disjunction (`hend`: the
κ-coordinate set of the strip point set is `(a,1)` with `0 < a < 1` or
`(0,b)` with `0 < b < 1`), the arc `V := ψArc U ψ p (c₀+δ)` attaches
over an end strip of the prefix chart (`EndStripAttach P V κ`), is open
and interval-charted, and genuinely extends `P`. -/
theorem attach_cutting_endStrip {X : Type*} [TopologicalSpace X] [T2Space X]
    (P U : Set X) (κ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ P})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U}) (p c₀ δ : ℝ)
    (hUopen : IsOpen U) (hpc₀ : p < c₀) (hc₀I : c₀ ∈ Set.Ioo 0 1) (hδ0 : 0 < δ)
    (hcut : (((↑) : OpenRealInterval 0 1 → ℝ) ''
      {t : OpenRealInterval 0 1 | ((ψ t : {x : X // x ∈ U}) : X) ∈ P}) ∩ Set.Ioo p (c₀ + δ)
        = Set.Ioo p c₀)
    (hend : (∃ a : ℝ, 0 < a ∧ a < 1 ∧
        ∀ r : OpenRealInterval 0 1,
          ((κ r : {x : X // x ∈ P}) : X) ∈ stripPoints U ψ p c₀ ↔ (r : ℝ) ∈ Set.Ioo a 1) ∨
      (∃ b : ℝ, 0 < b ∧ b < 1 ∧
        ∀ r : OpenRealInterval 0 1,
          ((κ r : {x : X // x ∈ P}) : X) ∈ stripPoints U ψ p c₀ ↔ (r : ℝ) ∈ Set.Ioo 0 b))
    (hbd : (beyondArc U ψ c₀ δ).Nonempty)
    (hbdP : beyondArc U ψ c₀ δ ∩ P = ∅) :
    ∃ V : Set X, IsOpen V ∧ Nonempty (OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V}) ∧
      EndStripAttach P V κ ∧ (V \ P).Nonempty := by
  rcases hend with hterm | hinit
  · rcases hterm with ⟨a, ha0, ha1, hiff⟩
    rcases attach_cutting_terminal P U κ ψ p c₀ δ a hUopen hpc₀ hc₀I hδ0 ha0 ha1 hcut hiff
        hbd hbdP with ⟨V, hVopen, hVchart, hTA, hVdiff⟩
    refine ⟨V, hVopen, hVchart, ?_, hVdiff⟩
    exact Or.inl ⟨a, hTA⟩
  · rcases hinit with ⟨b, hb0, hb1, hiff⟩
    rcases attach_cutting_initial P U κ ψ p c₀ δ b hUopen hpc₀ hc₀I hδ0 hb0 hb1 hcut hiff
        hbd hbdP with ⟨V, hVopen, hVchart, hIA, hVdiff⟩
    refine ⟨V, hVopen, hVchart, ?_, hVdiff⟩
    exact Or.inr ⟨b, hIA⟩



/-! ## 15. The iii-a bridge and the raw-data instantiation (VERIFIED, S233)

Per the S232 status the remaining instantiation needs two pieces: the
iii-a bridge (the coordinate set `boundaryStripCoordSet P U κ ψ p c₀` of
the strip point set is OPEN/PRECONNECTED/NONEMPTY — the commons L43
`coordSet_open_preconnected_nonempty` transported through the chart
homeomorphisms), and the raw-data assembly (from the `AttachCuttingStatement`
boundary data — `IsOpen U`, right-freeness, the finite local structure
`hF`, `y ∈ closure P` — produce the attaching arc).  This section closes
both:

- **`boundaryStripCoordSet_open_preconnected_nonempty`** — the iii-a
  bridge: `hAsub : stripPoints U ψ p c₀ ⊆ P` + the strip meets the unit
  interval (`hne`) + `U` open ⇒ `boundaryStripCoordSet` open,
  preconnected, nonempty (the `hTopen`/`hTpc`/`hTne` inputs of
  `boundaryStrip_coords_end_strip`; direct `simpa` transport of L43, the
  raw subtype `{t : ℝ // t ∈ Ioo 0 1}` being defeq `OpenRealInterval 0 1`);
- **`coordSet_full_implies_all_members`** (Fact A) — `T = (0,1)` ⇒ every
  prefix point `κ r` lies in the strip (value-injectivity of the
  coordinate map);
- **`exists_P_not_mem_stripPoints_cut`** (Fact B) — cutting the strip at
  `p₀ ∈ (p, c₀)` leaves a point of `P` out (the ψ-coordinate
  `(p+p₀)/2` is in the overlap `P` but below the cut);
- **`stripPoints_mem_iff_of_coordSet_initial`** — the `(0,b)` mirror of
  the terminal membership-iff `stripPoints_mem_iff_of_coordSet` (S227);
- **`attach_cutting_realized`** — THE raw-data instantiation: realizes
  `AttachCuttingStatement P U κ ψ hyU hyPc`.  Proof: (i) `c₀ ∈ closure
  Sℝ` (`chart_real_coord_mem_closure`, S220) and `c₀ ∉ Sℝ`
  (value-injectivity over `chart_coord_not_mem`) feed the L36 strip core
  `left_strip_of_rightFree` (S221) giving the strip `(p, c₀) ⊆ Sℝ`; (ii)
  cut at the midpoint `p₀ := (p+c₀)/2` — the cut strictness (Facts A+B)
  forces the clean end strip of `boundaryStrip_coords_end_strip` (S225,
  fed by the iii-a bridge) to be NON-degenerate (`0 < a` terminal /
  `b < 1` initial), giving `hend` in the membership-iff form; (iii) the
  shrunk right-free radius `δ := min δ₀ ((1−c₀)/2)` gives the real cut
  (`overlapStrip_rightFree_cut_at_left`, S221) and the beyond arc
  (`hbd`/`hbdP`, the `right_free_beyond_arc` argument of S224); (iv)
  `attach_cutting_endStrip` (S232) assembles `V` — open,
  interval-charted, `EndStripAttach P V κ`, `V \ P ≠ ∅`.

Everything here is verified (no axioms, no `sorry`).  The remaining
steps of the interval side: iii-c (the T2 geometric no-oscillation input
supplying `hF`), the strict-terminal normalization to `OneSidedBoundaryAttach`
and the chain/glue bookkeeping, the ordered chain + alignment, the S206
extraction, the H2 compact side, and Layer-C winding.
-/

/-- **iii-a bridge (L43 instantiation)**: the κ-coordinate set
`boundaryStripCoordSet P U κ ψ p c₀` of the strip point set is open,
preconnected, nonempty in ℝ — the commons
`coordSet_open_preconnected_nonempty` transport through the chart
homeomorphisms (`ORI` is the raw subtype `{t : ℝ // t ∈ Ioo 0 1}`). -/
theorem boundaryStripCoordSet_open_preconnected_nonempty {X : Type*} [TopologicalSpace X]
    (P U : Set X) (hUopen : IsOpen U)
    (κ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ P})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (p c₀ : ℝ) (hne : (Set.Ioo p c₀ ∩ Set.Ioo 0 1).Nonempty)
    (hAsub : stripPoints U ψ p c₀ ⊆ P) :
    IsOpen (boundaryStripCoordSet P U κ ψ p c₀) ∧
      IsPreconnected (boundaryStripCoordSet P U κ ψ p c₀) ∧
      (boundaryStripCoordSet P U κ ψ p c₀).Nonempty := by
  have hA : (fun t : {t : ℝ // t ∈ Set.Ioo 0 1} => ((ψ t : {x : X // x ∈ U}) : X)) ''
      {t : {t : ℝ // t ∈ Set.Ioo 0 1} | (t : ℝ) ∈ Set.Ioo p c₀} ⊆ P := by
    simpa [stripPoints] using hAsub
  have hres := Commons.Topology.Charts.coordSet_open_preconnected_nonempty
    (X := X) P U hUopen κ ψ p c₀ hne hA
  simpa [boundaryStripCoordSet, stripPoints] using hres

/-- Fact A: if the κ-coordinate set of the strip point set is the full
open unit interval, then EVERY prefix point `κ r` lies in the strip. -/
lemma coordSet_full_implies_all_members {X : Type*} [TopologicalSpace X]
    (P U : Set X) (κ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ P})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U}) (p c₀ : ℝ)
    (hT : boundaryStripCoordSet P U κ ψ p c₀ = Set.Ioo 0 1) :
    ∀ r : OpenRealInterval 0 1,
      ((κ r : {x : X // x ∈ P}) : X) ∈ stripPoints U ψ p c₀ := by
  intro r
  have hrT : (r : ℝ) ∈ boundaryStripCoordSet P U κ ψ p c₀ := by
    rw [hT]
    exact r.2
  rcases hrT with ⟨r', hr'κ, hr'val⟩
  have hr'eq : r' = r := by
    apply Subtype.ext
    exact hr'val
  simpa [hr'eq] using hr'κ

/-- Fact B: cutting the strip at `p₀` strictly inside `(p, c₀)` leaves a
point of `P` out (the ψ-coordinate `(p+p₀)/2` is a member of `P` — the
strip `(p,c₀) ⊆ Sℝ` lies in the overlap — but not of the cut strip). -/
lemma exists_P_not_mem_stripPoints_cut {X : Type*} [TopologicalSpace X]
    (P U : Set X) (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (p p₀ c₀ : ℝ) (hpp₀ : p < p₀) (hp₀c : p₀ < c₀)
    (hstrip : Set.Ioo p c₀ ⊆
      ((↑) : OpenRealInterval 0 1 → ℝ) ''
        {t : OpenRealInterval 0 1 | ((ψ t : {x : X // x ∈ U}) : X) ∈ P}) :
    ∃ x : X, x ∈ P ∧ x ∉ stripPoints U ψ p₀ c₀ := by
  let Sℝ : Set ℝ := ((↑) : OpenRealInterval 0 1 → ℝ) ''
    {t : OpenRealInterval 0 1 | ((ψ t : {x : X // x ∈ U}) : X) ∈ P}
  have hS01 : Sℝ ⊆ Set.Ioo (0 : ℝ) 1 := by
    intro r hr
    rcases hr with ⟨t, ht, rfl⟩
    exact t.2
  let m : ℝ := (p + p₀) / 2
  have hmp : p < m := by dsimp [m]; linarith
  have hmp₀ : m < p₀ := by dsimp [m]; linarith
  have hmc : m < c₀ := lt_trans hmp₀ hp₀c
  have hmS : m ∈ Sℝ := hstrip ⟨hmp, hmc⟩
  have hm01 : m ∈ Set.Ioo (0 : ℝ) 1 := hS01 hmS
  let t : OpenRealInterval 0 1 := ⟨m, hm01⟩
  refine ⟨((ψ t : {x : X // x ∈ U}) : X), ?_, ?_⟩
  · have hiff := chart_mem_P_iff_coord P U ψ
    exact (hiff t).2 hmS
  · intro hxA
    rcases hxA with ⟨t', ht', hteq⟩
    have hψeq : ψ t' = ψ t := by
      apply Subtype.ext
      exact hteq
    have ht'eq : t' = t := ψ.injective hψeq
    have hval' : (t' : ℝ) = m := by
      rw [ht'eq]
    exact (not_lt_of_ge (le_of_lt hmp₀)) (by simpa [hval'] using ht'.1)

/-- **iii-b-2 (initial mirror)**: from the κ-coordinate set identity
`boundaryStripCoordSet P U κ ψ p c₀ = (0,b)`, a point of `P` with chart
coordinate `r` lies in the strip point set iff its coordinate lies in the
INITIAL strip `(0,b)` — the `InitialAttach`-half of the membership-iff
(identical proof to the terminal version: value-injectivity). -/
theorem stripPoints_mem_iff_of_coordSet_initial {X : Type*} [TopologicalSpace X]
    (P U : Set X) (κ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ P})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U}) (p c₀ b : ℝ)
    (hT : boundaryStripCoordSet P U κ ψ p c₀ = Set.Ioo 0 b) :
    ∀ r : OpenRealInterval 0 1,
      ((κ r : {x : X // x ∈ P}) : X) ∈ stripPoints U ψ p c₀ ↔ (r : ℝ) ∈ Set.Ioo 0 b := by
  intro r
  constructor
  · intro hr
    have hval : (r : ℝ) ∈ boundaryStripCoordSet P U κ ψ p c₀ := by
      dsimp [boundaryStripCoordSet]
      exact Set.mem_image_of_mem (fun t : OpenRealInterval 0 1 => (t : ℝ)) hr
    rwa [hT] at hval
  · intro hr
    have hmem : (r : ℝ) ∈ boundaryStripCoordSet P U κ ψ p c₀ := by
      rwa [hT]
    rcases hmem with ⟨r', hr', hval⟩
    have hr'eq : r' = r := by
      apply Subtype.ext
      exact hval
    simpa [hr'eq] using hr'

/-- **The raw-data instantiation (attach cutting realized)**: at a
boundary point `y` of `P` in the open arc-chart `U` (chart `ψ`), whose
overlap-coordinate set `Sℝ` is right-free at `c₀` and has the finite
local structure `hF`, with `y ∈ closure P`, the attaching arc exists:
`V` open, interval-charted, `EndStripAttach P V κ`, `V \ P ≠ ∅`.
Proof: (i) `c₀ ∈ closure Sℝ` (T1Abstract.chart_real_coord_mem_closure)
and `c₀ ∉ Sℝ` (value-injectivity over `chart_coord_not_mem`) feed L36
(`left_strip_of_rightFree`) giving the strip `(p, c₀) ⊆ Sℝ`; (ii) cut at
`p₀ ∈ (p, c₀)` (midpoint) to force strictness of the clean end below;
(iii) the iii-a bridge makes `boundaryStripCoordSet … p₀ c₀` open
preconnected nonempty, `boundaryStrip_coords_end_strip` makes it a clean
end strip, and the cut strictness (Facts A/B) rules out the degenerate
`(0,1)`; (iv) `overlapStrip_rightFree_cut_at_left` with the shrunk
`δ ≤ δ₀` gives the real cut, `right_free_beyond_arc`-style gives the
beyond arc; (v) `attach_cutting_endStrip` assembles `V`. -/
theorem attach_cutting_realized {X : Type*} [TopologicalSpace X] [T2Space X]
    (P U : Set X) (κ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ P})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U}) {y : X} (hyU : y ∈ U)
    (hyPc : y ∉ P) : AttachCuttingStatement P U κ ψ hyU hyPc := by
  intro hUopen hfree hF hclP
  let Sℝ : Set ℝ := ((↑) : OpenRealInterval 0 1 → ℝ) ''
    {t : OpenRealInterval 0 1 | ((ψ t : {x : X // x ∈ U}) : X) ∈ P}
  let c₀ : ℝ := ((ψ.symm ⟨y, hyU⟩ : OpenRealInterval 0 1) : ℝ)
  have hc₀I : c₀ ∈ Set.Ioo (0 : ℝ) 1 := (ψ.symm ⟨y, hyU⟩ : OpenRealInterval 0 1).2
  have hS01 : Sℝ ⊆ Set.Ioo (0 : ℝ) 1 := by
    intro r hr
    rcases hr with ⟨t, ht, rfl⟩
    exact t.2
  -- (i) closure and non-membership of c₀ in Sℝ
  have hclS : c₀ ∈ closure Sℝ := by
    exact chart_real_coord_mem_closure P U hUopen ψ hyU hclP
  have hcS : c₀ ∉ Sℝ := by
    intro hc₀S
    rcases hc₀S with ⟨t, ht, hval⟩
    have htEq : t = ψ.symm ⟨y, hyU⟩ := by
      apply Subtype.ext
      dsimp [c₀] at hval
      exact hval
    have hyeq : y = ((ψ t : {x : X // x ∈ U}) : X) := by
      rw [htEq]
      rw [ψ.apply_symm_apply ⟨y, hyU⟩]
    exact hyPc (by simpa [hyeq] using ht)
  -- (i') the strip from L36
  rcases hF with ⟨F, hF1, hF2⟩
  rcases left_strip_of_rightFree F hF1 hF2 hfree hclS hcS with ⟨p, hpc, hstrip⟩
  -- (ii) cut at the midpoint p₀
  let p₀ : ℝ := (p + c₀) / 2
  have hpp₀ : p < p₀ := by dsimp [p₀]; linarith
  have hp₀c : p₀ < c₀ := by dsimp [p₀]; linarith
  have hstrip₀ : Set.Ioo p₀ c₀ ⊆ Sℝ := by
    intro x hx
    exact hstrip ⟨by linarith [hx.1, hpp₀], hx.2⟩
  have hiffP := chart_mem_P_iff_coord P U ψ
  have hstrip₀' : ∀ t : OpenRealInterval 0 1, (t : ℝ) ∈ Set.Ioo p₀ c₀ →
      ((ψ t : {x : X // x ∈ U}) : X) ∈ P := fun t ht => (hiffP t).2 (hstrip₀ ht)
  have hAsub₀ : stripPoints U ψ p₀ c₀ ⊆ P := stripPoints_subset P U ψ p₀ c₀ hstrip₀'
  have hyA₀ : y ∈ closure (stripPoints U ψ p₀ c₀) := stripPoints_mem_closure U ψ hyU hp₀c
  -- (iii) open/preconnected/nonempty of the coordinate set
  have hne₀ : (Set.Ioo p₀ c₀ ∩ Set.Ioo 0 1).Nonempty := by
    let m : ℝ := (p₀ + c₀) / 2
    have hm₁ : m ∈ Set.Ioo p₀ c₀ := by dsimp [m]; constructor <;> linarith
    have hmS : m ∈ Sℝ := hstrip₀ hm₁
    exact ⟨m, hm₁, hS01 hmS⟩
  have hT₀ := boundaryStripCoordSet_open_preconnected_nonempty P U hUopen κ ψ p₀ c₀ hne₀ hAsub₀
  rcases hT₀ with ⟨hTopen, hTpc, hTne⟩
  have hend₀ := boundaryStrip_coords_end_strip P U κ ψ hyPc p₀ c₀ hAsub₀ hyA₀ hTopen hTpc hTne
  -- δ: shrunk right-free radius
  rcases hfree with ⟨δ₀, hδ₀0, hδ₀⟩
  let δ : ℝ := min δ₀ ((1 - c₀) / 2)
  have hδ0 : 0 < δ := by
    dsimp [δ]
    have h1 : 0 < (1 - c₀) / 2 := by nlinarith [hc₀I.2]
    exact lt_min hδ₀0 h1
  have hδle₀ : δ ≤ δ₀ := by dsimp [δ]; exact min_le_left δ₀ ((1 - c₀) / 2)
  have hδbd : c₀ + δ < 1 := by
    have hδle1 : δ ≤ (1 - c₀) / 2 := by dsimp [δ]; exact min_le_right δ₀ ((1 - c₀) / 2)
    nlinarith [hc₀I.2, hδle1]
  have hfreeδ : Sℝ ∩ Set.Ioo c₀ (c₀ + δ) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    have hx₂ : x ∈ Sℝ ∩ Set.Ioo c₀ (c₀ + δ₀) := ⟨hx.1, ⟨hx.2.1, by linarith [hx.2.2, hδle₀]⟩⟩
    exact (Set.eq_empty_iff_forall_notMem.mp hδ₀) x hx₂
  -- beyond arc
  have hbd : (beyondArc U ψ c₀ δ).Nonempty := by
    have hmid₁ : c₀ + δ / 2 ∈ Set.Ioo c₀ (c₀ + δ) := by constructor <;> linarith
    have hmid₂ : c₀ + δ / 2 ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> nlinarith [hc₀I.1, hδbd]
    refine ⟨(ψ ⟨c₀ + δ / 2, hmid₂⟩ : {x : X // x ∈ U}), ?_⟩
    dsimp [beyondArc]
    exact Set.mem_image_of_mem
      (fun t : OpenRealInterval 0 1 => ((ψ t : {x : X // x ∈ U}) : X)) hmid₁
  have hbdP : beyondArc U ψ c₀ δ ∩ P = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    rcases hx with ⟨hxB, hxP⟩
    rcases hxB with ⟨t, ht, rfl⟩
    have htS : (t : ℝ) ∈ Sℝ := (hiffP t).1 hxP
    have htx : (t : ℝ) ∈ Sℝ ∩ Set.Ioo c₀ (c₀ + δ₀) := ⟨htS, ⟨ht.1, by linarith [ht.2, hδle₀]⟩⟩
    exact (Set.eq_empty_iff_forall_notMem.mp hδ₀) (t : ℝ) htx
  -- the clean end (strict)
  have hend : (∃ a : ℝ, 0 < a ∧ a < 1 ∧
      ∀ r : OpenRealInterval 0 1,
        ((κ r : {x : X // x ∈ P}) : X) ∈ stripPoints U ψ p₀ c₀ ↔ (r : ℝ) ∈ Set.Ioo a 1) ∨
      (∃ b : ℝ, 0 < b ∧ b < 1 ∧
        ∀ r : OpenRealInterval 0 1,
          ((κ r : {x : X // x ∈ P}) : X) ∈ stripPoints U ψ p₀ c₀ ↔ (r : ℝ) ∈ Set.Ioo 0 b) := by
    rcases hend₀ with hterm | hinit
    · rcases hterm with ⟨a, ha0ge, ha1, hTeq⟩
      have ha0 : 0 < a := by
        by_contra ha0not
        have ha0z : a = 0 := le_antisymm (le_of_not_gt ha0not) ha0ge
        have hfull : boundaryStripCoordSet P U κ ψ p₀ c₀ = Set.Ioo (0 : ℝ) 1 := by
          simpa [ha0z] using hTeq
        have hall := coordSet_full_implies_all_members P U κ ψ p₀ c₀ hfull
        rcases (exists_P_not_mem_stripPoints_cut P U ψ p p₀ c₀ hpp₀ hp₀c hstrip) with
          ⟨x, hxP, hxA₀c⟩
        have hκx : ((κ (κ.symm ⟨x, hxP⟩) : {x : X // x ∈ P}) : X) ∈ stripPoints U ψ p₀ c₀ :=
          hall (κ.symm ⟨x, hxP⟩)
        exact hxA₀c (by simpa using hκx)
      exact Or.inl ⟨a, ha0, ha1, stripPoints_mem_iff_of_coordSet P U κ ψ p₀ c₀ a hTeq⟩
    · rcases hinit with ⟨b, hb0gt, hb1le, hTeq⟩
      have hb1 : b < 1 := by
        by_contra hb1not
        have hb1z : b = 1 := le_antisymm hb1le (le_of_not_gt hb1not)
        have hfull : boundaryStripCoordSet P U κ ψ p₀ c₀ = Set.Ioo (0 : ℝ) 1 := by
          simpa [hb1z] using hTeq
        have hall := coordSet_full_implies_all_members P U κ ψ p₀ c₀ hfull
        rcases (exists_P_not_mem_stripPoints_cut P U ψ p p₀ c₀ hpp₀ hp₀c hstrip) with
          ⟨x, hxP, hxA₀c⟩
        have hκx : ((κ (κ.symm ⟨x, hxP⟩) : {x : X // x ∈ P}) : X) ∈ stripPoints U ψ p₀ c₀ :=
          hall (κ.symm ⟨x, hxP⟩)
        exact hxA₀c (by simpa using hκx)
      exact Or.inr ⟨b, hb0gt, hb1, stripPoints_mem_iff_of_coordSet_initial P U κ ψ p₀ c₀ b hTeq⟩
  -- the real cut
  have hcut : (((↑) : OpenRealInterval 0 1 → ℝ) ''
      {t : OpenRealInterval 0 1 | ((ψ t : {x : X // x ∈ U}) : X) ∈ P}) ∩
        Set.Ioo p₀ (c₀ + δ) = Set.Ioo p₀ c₀ := by
    exact overlapStrip_rightFree_cut_at_left hcS hstrip₀ hδ0 hfreeδ
  -- assemble
  exact attach_cutting_endStrip P U κ ψ p₀ c₀ δ hUopen hp₀c hc₀I hδ0 hcut hend hbd hbdP
end LeanEval.KnotTheory.Quadrisecant
