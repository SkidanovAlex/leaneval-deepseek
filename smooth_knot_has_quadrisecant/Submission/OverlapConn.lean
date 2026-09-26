import Mathlib
import Submission.TwoArcUnion

open Set
open scoped Real Topology

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false

noncomputable section
namespace LeanEval.KnotTheory.Quadrisecant

/-!
# S200 — the prefix-overlap connectedness certificate (the hconn of the
S183 engine at one level; module Submission/OverlapConn.lean)

The S183 finite-chain engine (`finite_chain_union_interval`,
TwoArcUnion.lean) glues a chain of open arcs into one interval PROVIDED
every prefix meets the next trace in a CONNECTED overlap
(`hconn : ∀ k, ConnectedSpace {x : X // x ∈ P_k ∩ T (k+1)}`).  The
TwoChartGlue chain-step data (S154–S160) supplies, at each level, the
FACING-TERMINAL attachment of the next trace: the prefix chart `κk` has
`hVend` (the next trace meets the prefix exactly over the terminal
interval `(s,1)` of the prefix coordinate).  This module proves the
missing link — the OVERLAP-CONNECTIVITY CERTIFICATE: the facing-terminal
data implies the S183 `hconn` at that level:

**`prefixOverlap_connected_of_terminal`**: if the `k`-prefix `P_k`
carries an interval chart `κk : ORI 0 1 ≃ₜ ↑P_k` and the next trace
`T (k+1)` attaches over the terminal interval `(s,1)` of the prefix
coordinate (`hVend`, with `0 < s < 1`), then the prefix-overlap
`P_k ∩ T (k+1)` is connected (indeed it is the `κk`-image of the
terminal interval, hence an arc).  Proof: the overlap is the range of
the continuous map `t ↦ (κk (emb t) : X)` from the connected interval
`{t // t ∈ Ioo s 1}` (the embedding `emb : Ioo s 1 ↪ Ioo 0 1` from
`s > 0`); the range equality with `P_k ∩ T (k+1)` is the two inclusions
given by `hVend`; `IsConnected` of the range (`isConnected_range`) then
gives `IsConnected (P_k ∩ T (k+1))` and `Subtype.connectedSpace` the
`ConnectedSpace` of the overlap subtype — exactly the S183 `hconn k`
hypothesis.  This is the overlap-connectivity piece for one `P'_k`; the
chaining (each level's `hconn` from its `hVend`/`hUend` data, and the
supply of that data by the walk ordering) is the recorded remainder.

Everything here is verified (no axioms, no `sorry`).
-/

/-- **S200 — prefix-overlap connectedness from the facing-terminal data
(the hconn certificate of the S183 engine at one level).**  If the
`k`-prefix `P_k` carries an interval chart `κk` and the next trace
`T (k+1)` attaches over the TERMINAL interval `(s,1)` of the prefix
coordinate (`hVend`, the chain-step data of TwoChartGlue), then the
prefix-overlap `P_k ∩ T (k+1)` is connected — the `hconn k` hypothesis of
the S183 finite-chain engine. -/
lemma prefixOverlap_connected_of_terminal {X : Type*} [TopologicalSpace X]
    (T : ℕ → Set X) (k : ℕ)
    (κk : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ ⋃ j ∈ Finset.range (k + 1), T j})
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hVend : ∀ t : OpenRealInterval 0 1,
      (((κk t : {x : X // x ∈ ⋃ j ∈ Finset.range (k + 1), T j}) : X)) ∈ T (k + 1) ↔
        (t : ℝ) ∈ Set.Ioo s 1) :
    ConnectedSpace {x : X // x ∈ (⋃ j ∈ Finset.range (k + 1), T j) ∩ T (k + 1)} := by
  let P : Set X := ⋃ j ∈ Finset.range (k + 1), T j
  have hsub01 : Set.Ioo s 1 ⊆ Set.Ioo (0 : ℝ) 1 := by
    intro r hr
    rcases hr with ⟨hsr, hr1⟩
    exact ⟨lt_trans hs0 hsr, hr1⟩
  let emb : {t : ℝ // t ∈ Set.Ioo s 1} → OpenRealInterval 0 1 := fun t =>
    ⟨(t : ℝ), hsub01 t.2⟩
  have hemb_cont : Continuous emb := by
    dsimp [emb]
    exact Continuous.subtype_mk continuous_subtype_val (fun t => hsub01 t.2)
  let g : {t : ℝ // t ∈ Set.Ioo s 1} → X := fun t => ((κk (emb t) :
    {x : X // x ∈ P}) : X)
  have hg_cont : Continuous g := by
    dsimp [g]
    exact continuous_subtype_val.comp (κk.continuous.comp hemb_cont)
  letI : ConnectedSpace {t : ℝ // t ∈ Set.Ioo s 1} :=
    Subtype.connectedSpace (isConnected_Ioo hs1)
  have hconnRange : IsConnected (Set.range g) := isConnected_range hg_cont
  have hrange : Set.range g = P ∩ T (k + 1) := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      constructor
      · exact (κk (emb t) : {x : X // x ∈ P}).2
      · have ht : ((emb t : OpenRealInterval 0 1) : ℝ) ∈ Set.Ioo s 1 := by
          change (t : ℝ) ∈ Set.Ioo s 1
          exact t.2
        exact (hVend (emb t)).mpr ht
    · intro hx
      rcases hx with ⟨hxP, hxV⟩
      let t0 : OpenRealInterval 0 1 := κk.symm ⟨x, hxP⟩
      have ht0V : ((κk t0 : {x : X // x ∈ ⋃ j ∈ Finset.range (k + 1), T j}) : X) ∈
          T (k + 1) := by
        have hk := κk.apply_symm_apply ⟨x, hxP⟩
        have hv : (((κk t0 : {x : X // x ∈ P}) : X)) = x := by
          simpa [P, t0] using congrArg (fun z : {x : X // x ∈ P} => (z : X)) hk
        simpa [hv] using hxV
      have ht0s : (t0 : ℝ) ∈ Set.Ioo s 1 := (hVend t0).mp ht0V
      refine ⟨⟨(t0 : ℝ), ht0s⟩, ?_⟩
      dsimp [g]
      have hemb_eq : emb ⟨(t0 : ℝ), ht0s⟩ = t0 := by
        apply Subtype.ext
        rfl
      have hk2 := κk.apply_symm_apply ⟨x, hxP⟩
      have hval : ((κk (emb ⟨(t0 : ℝ), ht0s⟩) : {x : X // x ∈ P}) : X) = x := by
        rw [hemb_eq]
        simpa [P, t0] using congrArg (fun z : {x : X // x ∈ P} => (z : X)) hk2
      simpa [hval]
  have hconnSet : IsConnected (P ∩ T (k + 1)) := by
    rw [← hrange]
    exact hconnRange
  exact Subtype.connectedSpace hconnSet

/-! ## S207 — the abstract two-chart prefix gluing with the terminal
certificate (two-set level)

The S200 certificate is indexed over traces (`prefixOverlap_connected_of_terminal`);
this section restates it at the bare TWO-SET level and composes it with
the S182 ambient two-arc theorem into the abstract two-chart prefix
gluing step — the per-level step of the prefix exhaustion that both the
S183 engine (via its `hconn`) and the S160 engine (via the glued chart)
consume:

1. **`overlap_connected_of_terminal`** — the two-set certificate: an
   open arc `U` with interval chart `κ`, and `V` attaching over the
   terminal interval `(s,1)` of `U`'s coordinate (`hVend`), make the
   overlap `U ∩ V` connected (`ConnectedSpace {x // x ∈ U ∩ V}`) — the
   S200 proof at two-set level (the overlap is the range of
   `t ↦ (κ (emb t) : X)` on the connected interval `Ioo s 1`);
2. **`terminalTwoChart_union_is_openInterval`** — the ABSTRACT TWO-CHART
   PREFIX GLUING: open arcs `U`, `V` with interval charts and `V`
   attaching terminally over `U` (`hVend`) glue to an open interval arc:
   the certificate (1) supplies the connected-overlap hypothesis of the
   S182 `two_open_arcs_union_is_openInterval`, whose glued chart is the
   output.  This is the first load-bearing step under the generic
   dichotomy extraction `noncompact_connected_oneManifold_interval`
   (S206): each two-chart gluing of the exhaustion is certified from
   facing-terminal data and yields the next prefix arc.

Everything here is verified (no axioms, no `sorry`).
-/

/-- **S207(i) — the two-set terminal-overlap certificate.**  If an open
arc `U` carries an interval chart `κ` and the arc `V` attaches over the
TERMINAL interval `(s,1)` of `U`'s coordinate (`hVend`), then the
overlap `U ∩ V` is connected — the two-set form of the S200
`prefixOverlap_connected_of_terminal` certificate (no trace indexing). -/
lemma overlap_connected_of_terminal {X : Type*} [TopologicalSpace X]
    {U V : Set X} (κ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hVend : ∀ t : OpenRealInterval 0 1,
      (((κ t : {x : X // x ∈ U}) : X)) ∈ V ↔ (t : ℝ) ∈ Set.Ioo s 1) :
    ConnectedSpace {x : X // x ∈ U ∩ V} := by
  have hsub01 : Set.Ioo s 1 ⊆ Set.Ioo (0 : ℝ) 1 := by
    intro r hr
    rcases hr with ⟨hsr, hr1⟩
    exact ⟨lt_trans hs0 hsr, hr1⟩
  let emb : {t : ℝ // t ∈ Set.Ioo s 1} → OpenRealInterval 0 1 := fun t =>
    ⟨(t : ℝ), hsub01 t.2⟩
  have hemb_cont : Continuous emb := by
    dsimp [emb]
    exact Continuous.subtype_mk continuous_subtype_val (fun t => hsub01 t.2)
  let g : {t : ℝ // t ∈ Set.Ioo s 1} → X := fun t => ((κ (emb t) : {x : X // x ∈ U}) : X)
  have hg_cont : Continuous g := by
    dsimp [g]
    exact continuous_subtype_val.comp (κ.continuous.comp hemb_cont)
  letI : ConnectedSpace {t : ℝ // t ∈ Set.Ioo s 1} :=
    Subtype.connectedSpace (isConnected_Ioo hs1)
  have hconnRange : IsConnected (Set.range g) := isConnected_range hg_cont
  have hrange : Set.range g = U ∩ V := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      constructor
      · exact (κ (emb t) : {x : X // x ∈ U}).2
      · have ht : ((emb t : OpenRealInterval 0 1) : ℝ) ∈ Set.Ioo s 1 := by
          change (t : ℝ) ∈ Set.Ioo s 1
          exact t.2
        exact (hVend (emb t)).mpr ht
    · intro hx
      rcases hx with ⟨hxU, hxV⟩
      let t0 : OpenRealInterval 0 1 := κ.symm ⟨x, hxU⟩
      have ht0V : (((κ t0 : {x : X // x ∈ U}) : X)) ∈ V := by
        have hk := κ.apply_symm_apply ⟨x, hxU⟩
        have hv : (((κ t0 : {x : X // x ∈ U}) : X)) = x := by
          simpa [t0] using congrArg (fun z : {x : X // x ∈ U} => (z : X)) hk
        simpa [hv] using hxV
      have ht0s : (t0 : ℝ) ∈ Set.Ioo s 1 := (hVend t0).mp ht0V
      refine ⟨⟨(t0 : ℝ), ht0s⟩, ?_⟩
      dsimp [g]
      have hemb_eq : emb ⟨(t0 : ℝ), ht0s⟩ = t0 := by
        apply Subtype.ext
        rfl
      have hk2 := κ.apply_symm_apply ⟨x, hxU⟩
      have hval : ((κ (emb ⟨(t0 : ℝ), ht0s⟩) : {x : X // x ∈ U}) : X) = x := by
        rw [hemb_eq]
        simpa [t0] using congrArg (fun z : {x : X // x ∈ U} => (z : X)) hk2
      simpa [hval]
  have hconnSet : IsConnected (U ∩ V) := by
    rw [← hrange]
    exact hconnRange
  exact Subtype.connectedSpace (s := U ∩ V) hconnSet

/-- **S207(ii) — the abstract two-chart prefix gluing with the
certificate.**  If the open arcs `U`, `V` carry interval charts and `V`
attaches over the TERMINAL interval `(s,1)` of `U`'s coordinate
(`hVend`), then the union `U ∪ V` is again an open interval arc: the
S200-style certificate (i) supplies the connected-overlap hypothesis of
the S182 ambient two-arc theorem, whose glued chart is the output.  This
is the per-level gluing step of the prefix exhaustion in either engine
(S183 via hconn, S160 via the glued chart). -/
theorem terminalTwoChart_union_is_openInterval {X : Type*} [TopologicalSpace X] [T2Space X]
    {U V : Set X} (hUopen : IsOpen U) (hVopen : IsOpen V)
    (κ : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ U})
    (η : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ V})
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hVend : ∀ t : OpenRealInterval 0 1,
      (((κ t : {x : X // x ∈ U}) : X)) ∈ V ↔ (t : ℝ) ∈ Set.Ioo s 1) :
    Nonempty ({x : X // x ∈ U ∪ V} ≃ₜ OpenRealInterval 0 1) := by
  exact two_open_arcs_union_is_openInterval hUopen hVopen κ η
    (overlap_connected_of_terminal κ hs0 hs1 hVend)

/-! ## S208 — the chain step: the `(k+1)`-prefix chart from the
interval-charted `k`-prefix and the terminal-attaching next trace

The S207 two-set gluing is the level-0 step; this section adds the
INDUCTIVE step of the prefix exhaustion, abstracted from the S203 walk
pattern to generic `X`: an interval-charted `k`-prefix `P_k` with the
next trace attaching over the terminal interval of its coordinate glues
to the interval-charted `(k+1)`-prefix `P_{k+1}`.  **`chain_step_prefix_interval_of_terminal`**
composes the S200 certificate (`prefixOverlap_connected_of_terminal` —
the indexed form, supplying the S183 `hconn k`) with the S182 two-arc
gluing and the `union_range_succ` set identity.  With per-trace
openness/charts and terminal-attachment data at every level, iterating
this step (via the S183 `finite_chain_union_interval` or the S160
`finite_prefix_interval` induction, both verified) yields the interval
charts of all prefixes — the chain side of the exhaustion assembly under
`noncompact_connected_oneManifold_interval` (S206).  Everything here is
verified (no axioms, no `sorry`).
-/

/-- **S208 — the chain step: the `(k+1)`-prefix chart from the
interval-charted `k`-prefix and the terminal-attaching next trace.**  If
the `k`-prefix `P_k := ⋃ j ∈ range (k+1), T j` is open and
interval-charted by `eP` and the next trace `T (k+1)` is open and
interval-charted by `eT` and attaches over the TERMINAL interval `(s,1)`
of the prefix coordinate (`hVend`), then the `(k+1)`-prefix
`P_{k+1} = P_k ∪ T (k+1)` is again interval-charted: the S200
certificate (`prefixOverlap_connected_of_terminal`) supplies the
`hconn k` of the S183 induction step, whose two-arc gluing
(`two_open_arcs_union_is_openInterval`) produces the glued chart
(set-identity `union_range_succ`).  This is the per-level step of the
prefix exhaustion, abstracted from the S203 walk pattern to generic `X`. -/
theorem chain_step_prefix_interval_of_terminal {X : Type*} [TopologicalSpace X] [T2Space X]
    (T : ℕ → Set X) (k : ℕ)
    (hPopen : IsOpen (⋃ j ∈ Finset.range (k + 1), T j))
    (hTopen : IsOpen (T (k + 1)))
    (eP : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ ⋃ j ∈ Finset.range (k + 1), T j})
    (eT : OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ T (k + 1)})
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hVend : ∀ t : OpenRealInterval 0 1,
      (((eP t : {x : X // x ∈ ⋃ j ∈ Finset.range (k + 1), T j}) : X)) ∈ T (k + 1) ↔
        (t : ℝ) ∈ Set.Ioo s 1) :
    Nonempty (OpenRealInterval 0 1 ≃ₜ {x : X // x ∈ ⋃ j ∈ Finset.range (k + 2), T j}) := by
  have hconn : ConnectedSpace
      {x : X // x ∈ (⋃ j ∈ Finset.range (k + 1), T j) ∩ T (k + 1)} :=
    prefixOverlap_connected_of_terminal T k eP hs0 hs1 hVend
  rcases two_open_arcs_union_is_openInterval hPopen hTopen eP eT hconn with ⟨eU⟩
  have hset : (⋃ j ∈ Finset.range (k + 2), T j) =
      (⋃ j ∈ Finset.range (k + 1), T j) ∪ T (k + 1) := union_range_succ T k
  have hfin : ({x : X // x ∈ ⋃ j ∈ Finset.range (k + 2), T j}) ≃ₜ
      ({x : X // x ∈ (⋃ j ∈ Finset.range (k + 1), T j) ∪ T (k + 1)}) :=
    setEqSubtypeHomeoX hset
  exact ⟨(hfin.trans eU).symm⟩

end LeanEval.KnotTheory.Quadrisecant
