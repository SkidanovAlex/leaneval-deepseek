import Mathlib
import Submission.OneManifold
import Submission.T1Abstract
import Submission.OneSidedAttach
import Submission.ComponentIntervalSide
import Submission.Commons.Topology.OneManifold.psi_coord_set_single_or_empty
import Submission.Commons.Topology.OneManifold.noncompact_connected_oneManifold_interval

open LeanEval.KnotTheory.Quadrisecant
open Set
open scoped Topology

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false

noncomputable section
namespace LeanEval.KnotTheory.Quadrisecant

/-!
# S236 — iii-c PINNED: the T2 geometric no-oscillation input
(module Submission/NoOscillation.lean)

Per the S233/S234 records the attach cutting (`attach_cutting_realized`,
`endStripExtension_of_rawBoundary`) is realized from the raw boundary
data EXCEPT for one hypothesis — the finite local structure `hF` of the
overlap-coordinate set at the boundary point — which is supplied by the
T2 geometric no-oscillation claim (iii-c).  This module PINS iii-c as a
Lean statement (full local context), records its decomposition into the
one-dimensional lemmas it needs, and verifies the transport that shows
iii-c's output plugs into the attach (the end strip).  It also fixes the
delegation decision: `iii_c_finite_structure` is stated against the
generic connected Hausdorff second-countable locally-interval-charted
ambient (`LocallyIntervalChart`), so the 1-manifold content needed for
its proof is exactly the connected-1-manifold classification
(`noncompact_connected_oneManifold_interval`, ComponentIntervalSide.lean
:210, for the interval side; the circle side is excluded by
`RightFreeAt`, see below) — i.e. the S206 extraction IS the right child
to dispatch for the 1-manifold content, and once it is proved iii-c
follows in a short argument (the coordinate pullback of an interval
prefix in `(0,1)` is a single interval).

**The geometric content of iii-c.**  At a boundary point `y` of an open
arc prefix `P ≃ (0,1)` of a 1-manifold, in an arc chart `ψ : (0,1) ≃ U`
of `y`, the overlap-coordinate set
`Sℝ := val '' {t : (0,1) | (ψ t : X) ∈ P}` records where `P` meets `U`.
`RightFreeAt Sℝ c₀` is the one-sidedness: no point of `P` in `U` lies
just to the right of `y` (in `ψ`'s coordinate).  The claim: `Sℝ`'s part
to the LEFT of `c₀` is a FINITE union of open intervals with upper
endpoints `≤ c₀` — the no-infinite-oscillation content: an open arc
prefix cannot oscillate infinitely often near its own boundary point in
a genuine 1-manifold (T2, second-countable, locally interval-charted:
connected components are `(0,1)` or the circle; in either, with
one-sidedness, the overlap is a single end strip — see the TRUTH
ANALYSIS below).

**Why `hF` is genuinely one-dimensional (and not a bare-T2 formality).**
The TRUTH ANALYSIS of S233/S235: an arbitrary open set `S ⊆ (0,1)` with
`c₀ ∈ closure S`, `c₀ ∉ S`, right-free, can oscillate infinitely often
(left components `(aₙ,bₙ)` with `bₙ ↑ c₀`) and then NO end strip
exists — `hF` fails.  Such `S` CANNOT arise as the overlap-coordinate
set of an arc prefix `P ≃ (0,1)` in a 1-manifold: `P` open connected
`≃ (0,1)` embedded in a Hausdorff 1-manifold meets an arc chart
finitely (the components of `P ∩ U` correspond to visits of the single
interval `(0,1)` to `U`; infinite oscillation would make `P`'s chart
`κ : (0,1) ≃ P` accumulate visits at an interior parameter or at an
end, contradicting injectivity or the one-sidedness).  The clean proof
goes through the classification (component `≃ (0,1)` or the circle):
then `P` is an open interval (or the punctured circle, whose overlap is
two intervals — the right one excluded by `RightFreeAt`), and the
coordinate set is a single interval.  That is why the delegation target
is the connected-1-manifold classification and NOT a bare
`LocallyIntervalChart`-plus-`RightFreeAt` statement.

**Decomposition of iii-c (the sub-lemmas it needs).**

1. **(α) the coordinate set is open.**  `S := {t : (0,1) | (ψ t : X) ∈
   P}` is open in `(0,1)` (the continuous preimage of the open set
   `P`); `Sℝ = val '' S` is open in `(0,1)` (open subsets of the open
   subtype `(0,1) ⊆ ℝ` have open value-images).  [VERIFIED below:
   `overlapCoordSet_isOpen`; the value-image half recorded.]
2. **(β) the one-dimensional core (the content).**  Under
   `[T2Space X] [SecondCountableTopology X]`, `LocallyIntervalChart X`,
   `ConnectedSpace X` and the boundary data (`κ`-chart of `P`, `y ∈
   closure P ∖ P`, `RightFreeAt`), the open set `Sℝ ∩ Iio c₀` is a
   finite union of open intervals with upper endpoints `≤ c₀` — i.e.
   `iii_c_finite_structure` itself.  Route: (i) by the component
   classification (`noncompact_connected_oneManifold_interval` on the
   non-compact side; on the compact/circle side `RightFreeAt` excludes
   the two-interval punctured-circle overlap — or handle the circle
   directly), pull `P` and `U` back to the model `(0,1)`/circle, where
   `P` is an open interval and `P ∩ U` is a single interval; or (ii) a
   direct local monotonicity development of embeddings of intervals
   into Hausdorff 1-manifolds (recorded, longer).  The delegation
   decision (see below): route (i) — the classification child is the
   right one to dispatch.
3. **(γ) the transport: iii-c ⟹ the attach works.**  From `hF` +
   `RightFreeAt` + `c₀ ∈ closure Sℝ` + `c₀ ∉ Sℝ` the L36 strip core
   (`left_strip_of_rightFree`, S221) gives the end strip
   `∃ p < c₀, Ioo p c₀ ⊆ Sℝ`, which is what `attach_cutting_realized`
   actually consumes.  [VERIFIED below: `left_strip_of_boundary`
   packages the geometry (the two closure/non-membership facts are the
   S220 bridge `chart_real_coord_mem_closure` / `chart_coord_not_mem`)
   with `hF` into the end strip — sorry-free.]

**Delegation decision (recorded).**  `noncompact_connected_oneManifold_interval`
(ComponentIntervalSide.lean:210) IS the right child for the 1-manifold
content of iii-c: it supplies the model `X ≃ (0,1)` on the interval
side; iii-c is then a corollary (`P`'s pullback is an open interval,
`P ∩ U` one interval).  The dependency note: iii-c is NOT needed to
STATEMENT of the S206 extraction; it is needed by the per-level
boundary-attach route to S206 — so the recommended order is to close the
S206 extraction first (independent route), then iii-c follows; if iii-c
is needed before S206, only route (ii) (local monotonicity) breaks the
circularity, and that is a larger development.  (This module does NOT
resolve the ordering; it pins the statement so the fleet can work.)

Content (all sorry-free EXCEPT the single pinned placeholder
`iii_c_finite_structure`, documented below): the two definitions
`overlapCoordReal`/`boundaryCoord` (the `hF`-statement's coordinate
objects, shared with `attach_cutting_realized`'s inline form),
`overlapCoordSet_isOpen` ((α) half), and `left_strip_of_boundary` ((γ),
verified).
-/

/-- The overlap-coordinate REAL set of `P ∩ U` in the `U`-chart `ψ`:
the value-image (in ℝ) of the chart parameters whose `ψ`-image lies in
`P`.  (The `Sℝ` of the attach-cutting statements, factored so that
iii-c and its consumers share one name.) -/
def overlapCoordReal {X : Type*} [TopologicalSpace X] {U : Set X}
    (P : Set X) (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U}) : Set ℝ :=
  ((↑) : OpenRealInterval 0 1 → ℝ) ''
    {t : OpenRealInterval 0 1 | ((ψ t : {x : X // x ∈ U}) : X) ∈ P}

/-- The chart coordinate of the boundary point `y ∈ U`: `c₀ = (ψ.symm
⟨y, hyU⟩ : ℝ)`.  (The `c₀` of the attach-cutting statements, factored
for shared use.) -/
noncomputable def boundaryCoord {X : Type*} [TopologicalSpace X] {U : Set X}
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U}) {y : X} (hyU : y ∈ U) : ℝ :=
  ((ψ.symm ⟨y, hyU⟩ : OpenRealInterval 0 1) : ℝ)



/-- **(α) the coordinate set is open**: `S := {t : (0,1) | (ψ t : X) ∈
P}` is open in the chart interval — the continuous preimage (under
`t ↦ (ψ t : X)`) of the open set `P`.  (Its value-image `Sℝ` is then
open in `(0,1)`, since open subsets of the open subtype `(0,1) ⊆ ℝ`
have open value-images — recorded, not yet formalised.) -/
theorem overlapCoordSet_isOpen {X : Type*} [TopologicalSpace X]
    {U P : Set X} (hPopen : IsOpen P)
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U}) :
    IsOpen {t : OpenRealInterval 0 1 | ((ψ t : {x : X // x ∈ U}) : X) ∈ P} := by
  have hg : Continuous (fun t : OpenRealInterval 0 1 => ((ψ t : {x : X // x ∈ U}) : X)) :=
    continuous_subtype_val.comp ψ.continuous
  exact hg.isOpen_preimage P hPopen

/-- **(γ) the transport: iii-c's output plugs into the attach.**  From
the finite local structure `hF` together with the boundary geometry
(`RightFreeAt`, `y ∈ closure P`, `y ∉ P`, chart `ψ` of `y`) the L36
strip core gives the END STRIP `∃ p < c₀, Ioo p c₀ ⊆ Sℝ` — the form
`attach_cutting_realized` actually consumes.  The two non-obvious facts
are the S220 bridge: `c₀ ∈ closure Sℝ` (`chart_real_coord_mem_closure`)
and `c₀ ∉ Sℝ` (value-injectivity over `chart_coord_not_mem`, `y ∉ P`).
Verified (sorry-free). -/
theorem left_strip_of_boundary {X : Type*} [TopologicalSpace X]
    {P U : Set X} (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    {y : X} (hyU : y ∈ U) (hyPc : y ∉ P)
    (hUopen : IsOpen U) (hclP : y ∈ closure P)
    (hfree : RightFreeAt (overlapCoordReal P ψ) (boundaryCoord ψ hyU))
    (hF : ∃ F : Finset (ℝ × ℝ),
      overlapCoordReal P ψ ∩ Set.Iio (boundaryCoord ψ hyU) =
        ⋃ p ∈ F, Set.Ioo p.1 p.2 ∧
      ∀ p ∈ F, p.2 ≤ boundaryCoord ψ hyU) :
    ∃ p : ℝ, p < boundaryCoord ψ hyU ∧
      Set.Ioo p (boundaryCoord ψ hyU) ⊆ overlapCoordReal P ψ := by
  let Sℝ : Set ℝ := overlapCoordReal P ψ
  let c₀ : ℝ := boundaryCoord ψ hyU
  -- c₀ ∈ closure Sℝ (S220 bridge)
  have hclS : c₀ ∈ closure Sℝ := by
    dsimp [Sℝ, c₀, overlapCoordReal, boundaryCoord]
    exact chart_real_coord_mem_closure P U hUopen ψ hyU hclP
  -- c₀ ∉ Sℝ (y ∉ P and value-injectivity of the coordinate map)
  have hcS : c₀ ∉ Sℝ := by
    intro hc₀S
    dsimp [Sℝ, c₀, boundaryCoord] at hc₀S
    rcases hc₀S with ⟨t, ht, hval⟩
    have htEq : t = ψ.symm ⟨y, hyU⟩ := by
      apply Subtype.ext
      exact hval
    have hyeq : y = ((ψ t : {x : X // x ∈ U}) : X) := by
      rw [htEq]
      rw [ψ.apply_symm_apply ⟨y, hyU⟩]
    exact hyPc (by simpa [hyeq] using ht)
  rcases hF with ⟨F, hF1, hF2⟩
  have hacc : ∀ ε : ℝ, 0 < ε → (Sℝ ∩ Set.Ioo (c₀ - ε) c₀).Nonempty :=
    closure_left_accumulation_of_rightFree hfree hclS hcS
  have hres := left_strip_of_rightFree (S := Sℝ) (c := c₀) F hF1 hF2 hfree hclS hcS
  simpa [Sℝ, c₀] using hres

/-! ## S240 — the iii-c corollary on the interval side, canonical chart
form (VERIFIED, sorry-free)

Once the component admits the interval chart `e : (0,1) ≃ₜ X` (the S206
output — fleet L46 IN FLIGHT), iii-c's `hF` is a short corollary with no
oscillation analysis: `prefix_coord_interval` (S237) puts every open arc
prefix over a single interval `Ioo a b` of the chart, and
`singleInterval_finiteStructure` (S239) packs `Ioo a b ∩ Iio c₀` as one
(possibly empty) interval with upper endpoint `≤ c₀`.  This section
verifies:

1. **`hF_prefix_in_interval_chart`** — `chartPrefixCoord e P ∩ Iio c₀`
   has the finite local structure for ANY cut point `c₀` (the `hF` of
   the attach statements in the whole-space chart);
2. **`canonicalChart_overlapCoord_eq`** — the canonical boundary chart
   at any point (the whole space `U := univ` with chart
   `ψe := e.trans (subtypeUnivHomeo X).symm`) has overlap-coordinate set
   `overlapCoordReal P ψe` equal to the prefix-coordinate set
   `chartPrefixCoord e P` (values coincide: `(ψe t : X) = e t`) — so on
   the interval side the attach's `hF` input is
   `hF_prefix_in_interval_chart` in the canonical chart, and iii-c
   (`iii_c_finite_structure`, NoOscillation) is the composition of these
   with `L46`'s chart, plus the circle-side case (compact components are
   excluded on the interval side by the S206 hypothesis; the circle
   itself is handled by the same one-interval argument after the compact
   classification, recorded for the H2 side).

Everything here is verified (no axioms, no `sorry`); the general-chart
version (`ψ` an arbitrary arc chart of an arbitrary open `U` at the
boundary point) needs the chart-transition plumbing of S237/S239 and is
recorded as the next step after L46.
-/

/-- **The hF corollary on the interval side (canonical chart form)**: in
the whole-space interval chart `e : (0,1) ≃ₜ X` (the S206 output, fleet
L46), every open arc prefix `P` (chart `κ`) has its coordinate set with
FINITE local structure at any cut point `c₀`: `chartPrefixCoord e P ∩
Iio c₀` is a finite union of open intervals with upper endpoints `≤ c₀`
— `prefix_coord_interval` (S237) gives `chartPrefixCoord e P = Ioo a b`
and `singleInterval_finiteStructure` (S239) packs the single interval.
This is exactly the `hF` of `attach_cutting_realized` in the canonical
boundary chart `U := X`, `ψ := e`. -/
theorem hF_prefix_in_interval_chart {X : Type*} [TopologicalSpace X]
    (e : OpenRealInterval 0 1 ≃ₜ X) (P : Set X)
    (hPopen : IsOpen P) (hPne : P.Nonempty)
    (κ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ P}) (c₀ : ℝ) :
    ∃ F : Finset (ℝ × ℝ),
      chartPrefixCoord e P ∩ Set.Iio c₀ = ⋃ p ∈ F, Set.Ioo p.1 p.2 ∧
      ∀ p ∈ F, p.2 ≤ c₀ := by
  rcases prefix_coord_interval e P hPopen hPne κ with ⟨a, b, hab, h⟩
  rw [h]
  exact singleInterval_finiteStructure a b c₀

/-- **The canonical boundary chart equals the whole-space chart on
values**: with `ψe := e.trans (subtypeUnivHomeo X).symm` the chart of
the open set `univ` (the whole space), the overlap-coordinate set of the
attach statements (`overlapCoordReal P ψe`) is the prefix-coordinate set
(`chartPrefixCoord e P`) of the interval chart.  (So on the interval
side the boundary chart at any point can be taken as the canonical whole
-space chart and the `hF` input of the attach is
`hF_prefix_in_interval_chart`.) -/
lemma canonicalChart_overlapCoord_eq {X : Type*} [TopologicalSpace X]
    (e : OpenRealInterval 0 1 ≃ₜ X) (P : Set X) :
    overlapCoordReal P (e.trans (subtypeUnivHomeo X).symm) = chartPrefixCoord e P := by
  let ψe : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ (univ : Set X)} :=
    e.trans (subtypeUnivHomeo X).symm
  have hval : ∀ t : OpenRealInterval 0 1,
      ((ψe t : {x : X // x ∈ (univ : Set X)}) : X) = e t := by
    intro t
    rfl
  have hset : {t : OpenRealInterval 0 1 |
        ((ψe t : {x : X // x ∈ (univ : Set X)}) : X) ∈ P} =
      {t : OpenRealInterval 0 1 | e t ∈ P} := by
    ext t
    constructor
    · intro ht
      change ((ψe t : {x : X // x ∈ (univ : Set X)}) : X) ∈ P at ht
      rw [hval] at ht
      change e t ∈ P
      exact ht
    · intro ht
      change e t ∈ P at ht
      rw [← hval] at ht
      change ((ψe t : {x : X // x ∈ (univ : Set X)}) : X) ∈ P
      exact ht
  unfold overlapCoordReal chartPrefixCoord
  rw [hset]

/-! ## S241 — the arbitrary-`ψ` hF target on the interval side and its
reduction (VERIFIED, sorry-free statement + reduction; residual
delegated)

The full-generality version of the iii-c interval-side corollary (with
ANY boundary arc chart `ψ` of an open `U` at the boundary point — the
form the circle-side/H2 route will need, and the one that isolates the
remaining dependency from L46 entirely):

1. **`hF_of_interval_chart`** — PINNED target (a `def Prop`, no `sorry`):
   in the whole-space interval chart `e : (0,1) ≃ₜ X`, for an open arc
   prefix `P` (chart `κ`) and an open arc `U` (chart `ψ`), both nonempty
   open, the overlap-coordinate real set `overlapCoordReal P ψ` of the
   prefix in the boundary chart has the finite local structure at every
   cut point `c₀` (the `hF` of `attach_cutting_realized`);
2. **`hF_of_interval_chart_of_coord_shape`** — the REDUCTION (VERIFIED,
   sorry-free): from the residual chart-transition shape — `overlapCoordReal
   P ψ` is EMPTY or a SINGLE open interval — the `hF` follows with no
   further analysis (empty case: the empty Finset; single interval:
   `singleInterval_finiteStructure`, S239 — one interval cannot
   oscillate).

The residual (the chart-transition lemma) has been DELEGATED to the
fleet as commons L55 (`Commons.Topology.OneManifold.psi_coord_set_single_or_empty`,
pure form, IN FLIGHT): once it lands, `hF_of_interval_chart` is the
two-line composition `hF_of_interval_chart_of_coord_shape` +
`psi_coord_set_single_or_empty` (whose proof uses the already-landed
`Commons.Topology.OneManifold.chart_pullback_interval_shape` + the
connectivity of the overlap in the charted space).  The canonical-chart
case (S240) remains the shortcut when the boundary analysis takes
`U := univ`, `ψ := e`.
-/

/-- **The arbitrary-`ψ` target on the interval side (PINNED STATEMENT,
a `def Prop` — the finite local structure `hF` of the attach for ANY
boundary arc chart `ψ` of an open `U` at the boundary point, in the
whole-space interval chart `e : (0,1) ≃ₜ X`).**  Once the component
admits the interval chart (S206 / fleet L46), the overlap-coordinate
real set `overlapCoordReal P ψ` of the prefix `P` in the boundary chart
`ψ` has the finite local structure at every cut point `c₀`:
`∃ F : Finset (ℝ × ℝ), overlapCoordReal P ψ ∩ Iio c₀ = ⋃p∈F Ioo p.1
p.2 ∧ ∀ p ∈ F, p.2 ≤ c₀`.  Proof = the residual chart-transition
lemma (the ψ-coordinate set of the overlap is empty or a single open
interval — delegated as commons L55
`Commons.Topology.OneManifold.psi_coord_set_single_or_empty`, IN
FLIGHT) + `hF_of_interval_chart_of_coord_shape` (VERIFIED below) +
`singleInterval_finiteStructure` (S239). -/
def hF_of_interval_chart {X : Type*} [TopologicalSpace X]
    (e : OpenRealInterval 0 1 ≃ₜ X)
    (P U : Set X) (κ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ P})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (hPopen : IsOpen P) (hUopen : IsOpen U)
    (hPne : P.Nonempty) (hUne : U.Nonempty) (c₀ : ℝ) : Prop :=
  ∃ F : Finset (ℝ × ℝ),
    overlapCoordReal P ψ ∩ Set.Iio c₀ = ⋃ p ∈ F, Set.Ioo p.1 p.2 ∧
    ∀ p ∈ F, p.2 ≤ c₀

/-- **The reduction (VERIFIED, sorry-free)**: from the residual
chart-transition shape — the overlap-coordinate real set of the prefix
in the boundary chart is EMPTY or a SINGLE open interval — the `hF`
finite structure follows with no further analysis: the empty case is the
empty Finset, the single-interval case is
`singleInterval_finiteStructure` (S239: one interval cannot oscillate). -/
theorem hF_of_interval_chart_of_coord_shape {X : Type*} [TopologicalSpace X]
    (e : OpenRealInterval 0 1 ≃ₜ X)
    (P U : Set X) (κ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ P})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (hPopen : IsOpen P) (hUopen : IsOpen U)
    (hPne : P.Nonempty) (hUne : U.Nonempty) (c₀ : ℝ)
    (hshape : overlapCoordReal P ψ = ∅ ∨
      ∃ a b : ℝ, a < b ∧ overlapCoordReal P ψ = Set.Ioo a b) :
    hF_of_interval_chart e P U κ ψ hPopen hUopen hPne hUne c₀ := by
  unfold hF_of_interval_chart
  rcases hshape with hEmpty | ⟨a, b, hab, h⟩
  · refine ⟨∅, ?_, ?_⟩
    · rw [hEmpty]
      simp
    · intro p hp
      simp at hp
  · rw [h]
    exact singleInterval_finiteStructure a b c₀

/-! ## S240 (completion) — the canonical boundary `hF` composition
(VERIFIED, sorry-free)

The canonical-chart branch of the interval-side iii-c bridge is now
closed END-TO-END: with the whole-space chart `e : (0,1) ≃ₜ X` and the
canonical boundary chart `ψe := e.trans (subtypeUnivHomeo X).symm`
(`U := univ`) at any boundary point, the attach's `hF` input is
supplied by a single composition:

- **`hF_canonical_boundary_of_interval`** — `overlapCoordReal P ψe ∩
  Iio c₀` has the finite local structure at EVERY cut `c₀` (hence at
  `c₀ = boundaryCoord ψe hyU` for any point `y`).  Proof: `rw
  [canonicalChart_overlapCoord_eq e P]` (S240: `ψ := e` makes the
  ψ-coordinate set literally the e-coordinate set) + `hF_prefix_in_interval_chart`
  (S240), whose single-interval shape is `prefix_coord_interval` (S237).
  Where `ψ := e` makes the shape lemma easier: NO chart-transition /
  connectivity plumbing is needed in the canonical branch — the
  residual L55 (arbitrary `ψ`) and the L46-child
  `chart_pullback_interval_shape` are bypassed entirely here.

When L46 lands, the interval-side proof of `iii_c_finite_structure` in
the canonical boundary chart is: rcases L46's chart `e`; instantiate
`hF_canonical_boundary_of_interval` at `c₀ = boundaryCoord ψe hyU`.
-/

/-- **S240 completion — the canonical boundary `hF` on the interval side
(VERIFIED, sorry-free)**: in the whole-space interval chart
`e : (0,1) ≃ₜ X`, for an open arc prefix `P` (chart `κ`, nonempty), the
overlap-coordinate real set of the prefix in the CANONICAL boundary
chart `ψe := e.trans (subtypeUnivHomeo X).symm` (the chart of the whole
space `U := univ`) has the finite local structure at EVERY cut point
`c₀` — so in particular at the boundary coordinate
`c₀ = boundaryCoord ψe hyU` of any point `y`.  Where `ψ := e` makes the
shape lemma easier: `canonicalChart_overlapCoord_eq` (S240) identifies
`overlapCoordReal P ψe = chartPrefixCoord e P`, and
`prefix_coord_interval` (S237) gives that single interval directly —
NO chart-transition/connectivity plumbing (the L55 / L46-child
`chart_pullback_interval_shape` route) is needed in the canonical
branch.  Composition: `rw [canonicalChart_overlapCoord_eq]` +
`hF_prefix_in_interval_chart`. -/
theorem hF_canonical_boundary_of_interval {X : Type*} [TopologicalSpace X]
    (e : OpenRealInterval 0 1 ≃ₜ X)
    (P : Set X) (hPopen : IsOpen P) (hPne : P.Nonempty)
    (κ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ P}) (c₀ : ℝ) :
    ∃ F : Finset (ℝ × ℝ),
      overlapCoordReal P (e.trans (subtypeUnivHomeo X).symm) ∩ Set.Iio c₀ =
          ⋃ p ∈ F, Set.Ioo p.1 p.2 ∧
      ∀ p ∈ F, p.2 ≤ c₀ := by
  rw [canonicalChart_overlapCoord_eq e P]
  exact hF_prefix_in_interval_chart e P hPopen hPne κ c₀

/-! ## S241 (completion) — L55 landed: the arbitrary-`ψ` hF composition
(VERIFIED, sorry-free)

The L55 residual (`Commons.Topology.OneManifold.psi_coord_set_single_or_empty`)
LANDED: in the whole-space interval chart, the ψ-coordinate set of the
overlap is empty or a single open interval.  This section closes the
arbitrary-`ψ` target of S241:

- **`hF_of_interval_chart_obtain`** — `hF_of_interval_chart` (the pinned
  `def Prop`) holds: the two-line composition of the L55 residual with
  the verified reduction `hF_of_interval_chart_of_coord_shape` (S241).
  This is the full-generality interval-side content of iii-c's `hF`
  (any boundary chart `ψ` of an open `U` at the boundary point; cut at
  `c₀ = boundaryCoord ψ hyU`), consumed by the eventual proof of
  `iii_c_finite_structure` on the interval side and by the
  circle-side/H2 route.

Together with the canonical branch (S240-completion,
`hF_canonical_boundary_of_interval`) every interval-side `hF` input is
now VERIFIED; the remaining interval-side dependency is the
classification chart itself (L46).
-/

/-- **S241 completion — the arbitrary-`ψ` hF on the interval side
(VERIFIED, sorry-free)**: in the whole-space interval chart
`e : (0,1) ≃ₜ X`, for an open arc prefix `P` (chart `κ`, nonempty) and
an open arc `U` (chart `ψ`, nonempty), the overlap-coordinate real set
of the prefix in the boundary chart `ψ` has the finite local structure
at every cut point `c₀`.  Composition of the L55 residual
(`Commons.Topology.OneManifold.psi_coord_set_single_or_empty`: the
ψ-coordinate set is empty or a single open interval) with the verified
reduction `hF_of_interval_chart_of_coord_shape` (S241).  This is the
full-generality interval-side content of iii-c's `hF` — the version the
circle-side/H2 route and the eventual proof of `iii_c_finite_structure`
consume (with `c₀ = boundaryCoord ψ hyU`). -/
theorem hF_of_interval_chart_obtain {X : Type*} [TopologicalSpace X]
    (e : OpenRealInterval 0 1 ≃ₜ X)
    (P U : Set X) (κ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ P})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (hPopen : IsOpen P) (hUopen : IsOpen U)
    (hPne : P.Nonempty) (hUne : U.Nonempty) (c₀ : ℝ) :
    hF_of_interval_chart e P U κ ψ hPopen hUopen hPne hUne c₀ := by
  exact hF_of_interval_chart_of_coord_shape e P U κ ψ hPopen hUopen hPne hUne c₀
    (Commons.Topology.OneManifold.psi_coord_set_single_or_empty
      e P U κ ψ hPopen hUopen hPne hUne)

/-- **iii-c — the T2 geometric no-oscillation input (DONE on the
non-compact side — fleet L46 + L55 landed; recorded).**  In a connected
Hausdorff second-countable locally-interval-charted NON-COMPACT space (a
connected non-compact topological 1-manifold — the interval-side
ambient where the attach machinery is consumed), at a one-sided
boundary point `y` of an open arc prefix `P` (chart `κ`) with arc chart
`ψ : (0,1) ≃ U` of `y` (`y ∈ U`, `y ∉ P`, `y ∈ closure P`), the
overlap-coordinate real set `Sℝ := overlapCoordReal P ψ` is RIGHT-FREE
at `c₀ := boundaryCoord ψ hyU`; then the part of `Sℝ` to the left of
`c₀` is a FINITE union of open intervals with upper endpoints `≤ c₀`:
`∃ F : Finset (ℝ × ℝ), Sℝ ∩ Iio c₀ = ⋃ p ∈ F, Ioo p.1 p.2 ∧ ∀ p ∈ F,
p.2 ≤ c₀`.

This is exactly the `hF` hypothesis of
`attach_cutting_realized`/`endStripExtension_of_rawBoundary` (S233/S234)
— the last raw input of the one-sided attach, consumed only on the
non-compact (interval) side of the component dichotomy (compact/circle
components take the winding route and never attach).  PROOF (verified,
sorry-free): the `¬ CompactSpace` hypothesis feeds the classification
(fleet L46, `Commons.Topology.OneManifold.
noncompact_connected_oneManifold_interval`: `X ≃ₜ (0,1)`); in the
interval chart, the L55 residual
(`Commons.Topology.OneManifold.psi_coord_set_single_or_empty`: the
ψ-coordinate set of the overlap is empty or one open interval) plus the
S241 reduction give `hF_of_interval_chart_obtain`, instantiated at
`c₀ = boundaryCoord ψ hyU`.  NOTE (recorded): the circle-side (compact
ambient) generalization of this statement is deferred with the H2
compact classification — the pin now carries `hnc` because its only
consumer is the non-compact side.
-/

theorem iii_c_finite_structure {X : Type*} [TopologicalSpace X] [T2Space X]
    [SecondCountableTopology X] [Nonempty X]
    (hLoc : LocallyIntervalChart X) (hconn : ConnectedSpace X) (hnc : ¬ CompactSpace X)
    (P U : Set X) (κ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ P})
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    {y : X} (hyU : y ∈ U) (hyPc : y ∉ P)
    (hPopen : IsOpen P) (hUopen : IsOpen U) (hclP : y ∈ closure P)
    (hfree : RightFreeAt (overlapCoordReal P ψ) (boundaryCoord ψ hyU)) :
    ∃ F : Finset (ℝ × ℝ),
      overlapCoordReal P ψ ∩ Set.Iio (boundaryCoord ψ hyU) =
        ⋃ p ∈ F, Set.Ioo p.1 p.2 ∧
      ∀ p ∈ F, p.2 ≤ boundaryCoord ψ hyU := by
  classical
  rcases (Commons.Topology.OneManifold.noncompact_connected_oneManifold_interval
      (X := X) hLoc hconn hnc) with ⟨e⟩
  have hPne : P.Nonempty := arc_prefix_nonempty P κ
  have hF : hF_of_interval_chart e P U κ ψ hPopen hUopen hPne ⟨y, hyU⟩
      (boundaryCoord ψ hyU) := by
    exact hF_of_interval_chart_obtain e P U κ ψ hPopen hUopen hPne ⟨y, hyU⟩
      (boundaryCoord ψ hyU)
  simpa [hF_of_interval_chart] using hF

end LeanEval.KnotTheory.Quadrisecant
