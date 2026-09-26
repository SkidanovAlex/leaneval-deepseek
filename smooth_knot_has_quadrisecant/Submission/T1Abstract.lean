import Mathlib
import Submission.OneManifold
import Submission.TerminalAttachment

open Set
open scoped Topology

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

/-!
# S219 — T1-abstract, ambient statement: the one-step terminal extension
of a proper arc prefix in a connected non-compact 1-manifold (module
Submission/T1Abstract.lean) — statement + first verified peel

Per the ROADMAP S218 status the remaining content of the interval side is
the ORDERING: at each step, a proper open arc prefix `P ≃ (0,1)` of a
trisecant component (a connected non-compact Hausdorff topological
1-manifold) must admit a one-step terminal extension — an open arc `V`
attaching over a terminal interval of the prefix coordinate
(`TerminalAttach`, S218) and genuinely extending `P`.  `glue_of_TerminalAttach`
(S218, restating S207) already turns such data into the interval chart of
`P ∪ V`; so the ambient theorem is a DATA-PRODUCTION statement.  This
module fixes that ambient statement precisely and peels its first
topological layer.

**The ambient target (record; the proof is the open content — no `sorry`
here).**

1. **`AmbientOneStepTerminalExtension X`** — the theorem-shaped Prop: for
   a Hausdorff (`T2Space`) locally-interval-charted (`LocallyIntervalChart`,
   S153) connected (`ConnectedSpace`) NON-compact topological space `X`,
   every open arc prefix `P` (`κ : (0,1) ≃ₜ P`, `IsOpen P`,
   `P ≠ univ`) admits `OneStepTerminalExtension P κ` (S218): an open arc
   `V` with `TerminalAttach` data and `V ∖ P ≠ ∅`.  Instantiated on
   `TrisecantComponent r c₀` (the S205 component type: T2, second
   countable, locally interval-charted, connected, and non-compact in the
   interval-side branch) this is the per-level step of the ordered chain
   that produces the length-form data consumed by
   `ChainUnionOrderedInitialSegment.chain_initialSegments_union_homeo_openUnit`
   (S217) — whose output `C ≃ₜ (0,1)` closes the S206 gate.

2. **`proper_arc_prefix_has_boundary`** (VERIFIED — the first peel): in a
   CONNECTED space a proper open arc prefix always has a boundary point:
   `(closure P \ P).Nonempty`.  Proof: if `P` were also closed it would
   be clopen, nonempty (the arc chart makes `P` nonempty — `κ` provides
   the witness through the nonempty coordinate interval), and not all of
   `X` — separating the preconnected `univ` into the two disjoint
   nonempty open sets `P`, `Pᶜ`, a contradiction.  This is the entry
   point of the T1-abstract construction: the attaching arc is built at a
   boundary point `y ∈ P̄ ∖ P` via a local interval chart of `y`
   (`LocallyIntervalChart`), where the overlap-coordinate set
   `S = ψ(P ∩ U) ⊆ (0,1)` has `c = ψ(y)` in its closure; the local
   one-sided/two-sided strip analysis (S218 real model + the T2
   finite-component core, delegated as commons L36
   `left_strip_of_finiteIntervals_accumulation`) then produces the
   `TerminalAttach` data.  (The continuation of the peel — chart-setup
   at `y`, one-sided ⇒ end strip ⇒ attach, two-sided ⇒
   `TwoSidedClosedWrap` ⇒ compact contradiction — is recorded in ROADMAP
   S219.)

3. **`arc_prefix_nonempty`** (VERIFIED) — an interval-charted set is
   nonempty (the coordinate interval `(0,1)` is nonempty; the homeo
   transports the witness);

4. **the chart-setup bridge `c ∈ closure S`** (VERIFIED — S220): for a
   boundary point `y ∈ P̄` with an arc chart `ψ : (0,1) ≃ₜ U` of an open
   neighbourhood `U ∋ y`,
   **`chart_coord_mem_closure`** — the chart coordinate
   `c₀ := ψ.symm ⟨y, hyU⟩` of `y` lies in the closure of the coordinate
   set `S = {t | (ψ t : X) ∈ P}` of the overlap `P ∩ U` (via
   `y ∈ closure P` + `U` open ⇒ `y ∈ closure (P ∩ U)`, the subtype
   `closure_subtype`, and `ψ.symm.image_closure`);
   **`chart_coord_not_mem`** — `c₀ ∉ S` (the boundary point itself is
   not in `P`); **`chart_real_coord_mem_closure`** — the real-coordinate
   form `c := (c₀ : ℝ) ∈ closure (val '' S)` consumed by the L36 strip
   core (supplying the accumulation hypothesis of the one-sided
   attachment).  This is the bridge from the boundary point to the
   strip-hypothesis input of `TerminalAttach`.

Everything here is verified (no axioms, no `sorry`).
-/

/-- An open interval-charted set is nonempty: the coordinate interval
`(0,1)` is nonempty and the chart homeomorphism transports the witness. -/
lemma arc_prefix_nonempty {X : Type*} [TopologicalSpace X] (P : Set X)
    (κ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ P}) : P.Nonempty := by
  have hw : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by constructor <;> norm_num
  let t : OpenRealInterval 0 1 := ⟨1 / 2, hw⟩
  refine ⟨((κ t : {x : X // x ∈ P}) : X), (κ t : {x : X // x ∈ P}).2⟩

/-- **The complement of a proper open set is nonempty.** -/
lemma complement_nonempty_of_ne_univ {X : Type*} (P : Set X) (hPneU : P ≠ Set.univ) :
    (Pᶜ : Set X).Nonempty := by
  by_contra hc
  have hc' : Pᶜ = ∅ := eq_empty_iff_forall_notMem.mpr (by
    intro x hx
    exact hc ⟨x, hx⟩)
  have huniv : P = Set.univ := by
    ext x
    constructor
    · intro hx
      trivial
    · intro hx
      by_contra hxp
      have hxmem : x ∈ Pᶜ := hxp
      rw [hc'] at hxmem
      exact hxmem
  exact hPneU huniv

/-- **A proper open nonempty subset of a connected space has a boundary
point** (`(closure P \ P).Nonempty`): if it were also closed it would be
clopen, separating the preconnected `univ` into the two disjoint nonempty
open sets `P` and `Pᶜ`. -/
lemma boundary_point_nonempty_of_proper_open {X : Type*} [TopologicalSpace X]
    [ConnectedSpace X] (P : Set X) (hPopen : IsOpen P) (hPne : P.Nonempty)
    (hPneU : P ≠ Set.univ) : (closure P \ P).Nonempty := by
  by_contra hb
  have hsub : closure P ⊆ P := by
    intro x hx
    by_contra hxP
    have hxmem : x ∈ closure P \ P := ⟨hx, hxP⟩
    exact hb ⟨x, hxmem⟩
  have hPcl : IsClosed P := isClosed_of_closure_subset hsub
  have hPc : (Pᶜ : Set X).Nonempty := complement_nonempty_of_ne_univ P hPneU
  have hpc : IsPreconnected (univ : Set X) := isPreconnected_univ
  have hcov : (univ : Set X) ⊆ P ∪ Pᶜ := by intro x hx; simp
  have hxP : ((univ : Set X) ∩ P).Nonempty := by
    rcases hPne with ⟨x, hx⟩
    exact ⟨x, ⟨trivial, hx⟩⟩
  have hxPc : ((univ : Set X) ∩ Pᶜ).Nonempty := by
    rcases hPc with ⟨x, hx⟩
    exact ⟨x, ⟨trivial, hx⟩⟩
  rcases hpc P Pᶜ hPopen hPcl.isOpen_compl hcov hxP hxPc with ⟨x, hx, hxP, hxPc⟩
  exact hxPc hxP

/-- **The first peel**: a proper open arc prefix of a connected space has
a boundary point (the arc chart `κ` supplies the nonemptiness). -/
theorem proper_arc_prefix_has_boundary {X : Type*} [TopologicalSpace X] [ConnectedSpace X]
    (P : Set X) (κ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ P})
    (hPopen : IsOpen P) (hPneU : P ≠ Set.univ) : (closure P \ P).Nonempty :=
  boundary_point_nonempty_of_proper_open P hPopen (arc_prefix_nonempty P κ) hPneU

/-- **The ambient T1-abstract target (record)** — for a Hausdorff
locally-interval-charted connected NON-compact space `X`, every open arc
prefix `P` (chart `κ`) admits a one-step terminal extension
(`OneStepTerminalExtension P κ` — S218: an open arc `V` attaching over a
terminal interval of the prefix coordinate with `V ∖ P ≠ ∅`).  The proof
is the ordering content of the interval side (construction at a boundary
point `y ∈ P̄ ∖ P` from `proper_arc_prefix_has_boundary`, via the local
chart and the one-sided/two-sided strip analysis; see the module doc and
ROADMAP S219).  The instantiation on the trisecant component closes the
per-level step of the interval-side chain. -/
def AmbientOneStepTerminalExtension (X : Type*) [TopologicalSpace X] : Prop :=
  T2Space X → LocallyIntervalChart X → ConnectedSpace X → ¬ CompactSpace X →
    ∀ P : Set X, ∀ κ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ P},
      OneStepTerminalExtension P κ


/-! ## The chart-setup bridge: `c ∈ closure S` at the boundary point -/

/-- **Chart-setup bridge**: let `y ∈ P̄` be a boundary point of the open
arc `P` and `ψ : (0,1) ≃ₜ U` an arc chart of an open neighbourhood `U ∋ y`.
Then the chart coordinate `c₀ := ψ.symm ⟨y, hyU⟩` of `y` lies in the
closure (in the chart interval) of the coordinate set
`S = {t | (ψ t : X) ∈ P}` of the overlap `P ∩ U`.  Proof: `y ∈ closure P`
with `U` open gives `y ∈ closure (P ∩ U)`; the subtype-embedding closure
lemma `closure_subtype` transfers this to the closure of
`S_U := {z : U | z ∈ P}` inside the chart-carrier subtype; the homeo
`ψ.symm` transfers it back to the chart interval through
`ψ.symm.image_closure`.  This is the bridge from the boundary point to
the strip hypothesis (`hacc` of the T2 core L36) of the one-sided
attachment. -/
theorem chart_coord_mem_closure {X : Type*} [TopologicalSpace X]
    (P U : Set X) (hUopen : IsOpen U)
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    {y : X} (hyU : y ∈ U) (hyP : y ∈ closure P) :
    (ψ.symm ⟨y, hyU⟩ : OpenRealInterval 0 1) ∈
      closure {t : OpenRealInterval 0 1 | ((ψ t : {x : X // x ∈ U}) : X) ∈ P} := by
  let S_U : Set {x : X // x ∈ U} := {z : {x : X // x ∈ U} | (z : X) ∈ P}
  let y' : {x : X // x ∈ U} := ⟨y, hyU⟩
  have himgU : ((↑) : {x : X // x ∈ U} → X) '' S_U = P ∩ U := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨hz, z.2⟩
    · intro hx
      exact ⟨⟨x, hx.2⟩, hx.1, rfl⟩
  have hyclU : y' ∈ closure S_U := by
    dsimp [y', S_U]
    rw [closure_subtype]
    rw [himgU]
    rw [mem_closure_iff]
    intro V hVopen hxV
    have hVUopen : IsOpen (V ∩ U) := hVopen.inter hUopen
    have hxVU : y ∈ V ∩ U := ⟨hxV, hyU⟩
    rcases (mem_closure_iff.mp hyP) (V ∩ U) hVUopen hxVU with ⟨x, hxVU', hxP⟩
    refine ⟨x, ?_⟩
    exact ⟨hxVU'.1, hxP, hxVU'.2⟩
  have hmem2 : (ψ.symm y' : OpenRealInterval 0 1) ∈ closure (ψ.symm '' S_U) := by
    have him : (ψ.symm '' closure S_U) = closure (ψ.symm '' S_U) := ψ.symm.image_closure S_U
    rw [← him]
    exact ⟨y', hyclU, rfl⟩
  have himg : (ψ.symm '' S_U) =
      {t : OpenRealInterval 0 1 | ((ψ t : {x : X // x ∈ U}) : X) ∈ P} := by
    ext t
    constructor
    · rintro ⟨z, hz, rfl⟩
      dsimp [S_U] at hz ⊢
      have heq : ((ψ (ψ.symm z) : {x : X // x ∈ U}) : X) = (z : X) := by
        rw [ψ.apply_symm_apply z]
      rwa [heq]
    · intro ht
      refine ⟨(ψ t : {x : X // x ∈ U}), ?_, ?_⟩
      · dsimp [S_U]
        exact ht
      · exact ψ.symm_apply_apply t
  rwa [himg] at hmem2

/-- **The boundary point's coordinate is not in the overlap set** (the
boundary point itself is not in `P`, so its coordinate has no witness in
`S`). -/
lemma chart_coord_not_mem {X : Type*} [TopologicalSpace X]
    (P U : Set X) (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    {y : X} (hyU : y ∈ U) (hyPc : y ∉ P) :
    ¬ (ψ.symm ⟨y, hyU⟩ : OpenRealInterval 0 1) ∈
      {t : OpenRealInterval 0 1 | ((ψ t : {x : X // x ∈ U}) : X) ∈ P} := by
  intro ht
  have heq : (((ψ (ψ.symm ⟨y, hyU⟩) : {x : X // x ∈ U}) : X)) = y := by
    rw [ψ.apply_symm_apply ⟨y, hyU⟩]
  exact hyPc (by simpa [heq] using ht)

/-- **The real-coordinate bridge**: with `c := (ψ.symm ⟨y, hyU⟩ : ℝ)` the
coordinate value of `y`, the real coordinate set
`Sℝ = {r | r ∈ (0,1) ∧ ((ψ ⟨r, ·⟩ : X) ∈ P)}`-image of the overlap has `c`
in its closure — the form consumed by the L36 strip core
(`left_strip_of_finiteIntervals_accumulation`): it supplies the
`hacc`-type accumulation hypothesis once the left/right side is fixed. -/
theorem chart_real_coord_mem_closure {X : Type*} [TopologicalSpace X]
    (P U : Set X) (hUopen : IsOpen U)
    (ψ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    {y : X} (hyU : y ∈ U) (hyP : y ∈ closure P) :
    (((ψ.symm ⟨y, hyU⟩ : OpenRealInterval 0 1) : ℝ)) ∈
      closure (((↑) : OpenRealInterval 0 1 → ℝ) ''
        {t : OpenRealInterval 0 1 | ((ψ t : {x : X // x ∈ U}) : X) ∈ P}) := by
  have hmem := chart_coord_mem_closure P U hUopen ψ hyU hyP
  have hinc : ((↑) : OpenRealInterval 0 1 → ℝ) '' closure
      {t : OpenRealInterval 0 1 | ((ψ t : {x : X // x ∈ U}) : X) ∈ P} ⊆
      closure (((↑) : OpenRealInterval 0 1 → ℝ) ''
        {t : OpenRealInterval 0 1 | ((ψ t : {x : X // x ∈ U}) : X) ∈ P}) :=
    image_closure_subset_closure_image (f := ((↑) : OpenRealInterval 0 1 → ℝ))
      continuous_subtype_val
  exact hinc (Set.mem_image_of_mem (fun t : OpenRealInterval 0 1 => (t : ℝ)) hmem)


end LeanEval.KnotTheory.Quadrisecant
