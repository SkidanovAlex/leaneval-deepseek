import Mathlib
import Submission.OSubChart
import Submission.ChartTracePath
import Submission.OChartComponent
import Submission.OLocalStructure
import Submission.ComponentPath
import Submission.OneManifold

open LeanEval.KnotTheory.Quadrisecant
open Set
open scoped Real Topology

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

set_option maxHeartbeats 800000

/-!
# Milestone-2 (iv) brick (b) — components of the trisecant set are
topological 1-manifolds (the local-interval interface for the
interval/circle classification)

The OChart machinery verified `osub1Chart_at_class` (S97: under
`QuadrisecantFree` + `TorusGeneralPositionTransverse` every trisecant
class carries an `OSub1Chart` — an open real interval homeomorphic to an
open trace `{c : OSub r | c ∈ W}` of the band) and `ChartTracePath`
verified that every trace is open, path-connected and contained in the
connected component of its centre (`chartTrace_subset_connectedComponent`).
This module assembles the *component-level* interface those results give
for free:

1. **`osub_local_interval`** — at every trisecant class `x`, there is an
   open neighbourhood `U` of `x` in `O = trisecantSet r` contained in the
   connected component of `x`, homeomorphic to an open real interval
   `ChartInterval lo hi` (the interval-chart neighbourhood restricted to
   the component): every point of `O` is an interior point of a
   1-dimensional chart of its own component;
2. **`TrisecantComponent r c₀`** — the type of trisecant classes in the
   connected component of `c₀` (the component as a topological space);
3. **`compSubtypeHomeo`** — the reassociation homeo between a subset
   `U ⊆ connectedComponent c₀` read as a subtype of the ambient
   trisecant set and as a subtype of the component (used to transport the
   chart homeo to the component type);
4. **`component_local_interval`** — the interface theorem of the
   classification route: **every connected component of `O` is locally
   homeomorphic to an open real interval at each of its points**: each
   `x ∈ C` has an open neighbourhood in `C` (the chart trace restricted
   to the component) with an `OSub1Chart`-interval homeomorphism.

Together with the automatic facts that the component (a subspace of the
second-countable Hausdorff band `OpenMobius`) is Hausdorff, second
countable, and (ComponentPath) path-connected, this is precisely the
input the interval/circle classification of the components
("compact component ⇒ circle; non-compact ⇒ open interval") will consume
(the next gluing stage, per ROADMAP S147/S152: the classification of
connected topological 1-manifolds without boundary, instantiated on the
`OSub1Chart`-atlas of `O`).

Everything here is elementary and verified (no axioms, no `sorry`).
-/

/-- **The interval-chart neighbourhood of a trisecant class, inside its
component.**  Every trisecant class `x` of `O` has an open neighbourhood
`U` in the subspace `O = trisecantSet r` with `x ∈ U`, `U` contained in
the connected component of `x`, and `U` homeomorphic to an open real
interval `ChartInterval lo hi` — the trace of the `OSub1Chart` at `x`
(open by `isOpen_chartTrace`, inside the component by
`chartTrace_subset_connectedComponent`, parametrised by
`chartTraceHomeo`). -/
theorem osub_local_interval {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r) (x : OSub r) :
    ∃ U : Set (OSub r), IsOpen U ∧ x ∈ U ∧ U ⊆ connectedComponent x ∧
      ∃ lo hi : ℝ, Nonempty (ChartInterval lo hi ≃ₜ {c : OSub r // c ∈ U}) := by
  classical
  let ch : OSub1Chart r x := Classical.choice (osub1Chart_at_class h hqf hgp x)
  let U : Set (OSub r) := chartTrace ch
  refine ⟨U, ?_, ?_, ?_, ch.lo, ch.hi, ?_⟩
  · exact isOpen_chartTrace ch
  · simpa [U, chartTrace] using (ch.c₀_mem)
  · simpa [U] using (chartTrace_subset_connectedComponent ch)
  · exact ⟨chartTraceHomeo ch⟩

/-- A connected component of the trisecant set, as a type: the trisecant
classes lying in the connected component of `c₀`. -/
abbrev TrisecantComponent (r : ℝ → Space) (c₀ : OSub r) : Type :=
  {c : OSub r // c ∈ connectedComponent c₀}

/-- **Reassociation homeo.**  For `U ⊆ connectedComponent c₀`, the
elements of `U` read as a subtype of the component and as a subtype of the
ambient trisecant set are the same topological space (the identity on the
underlying classes); this transports chart homeos onto the component. -/
noncomputable def compSubtypeHomeo {r : ℝ → Space} (c₀ : OSub r) {U : Set (OSub r)}
    (hU : U ⊆ connectedComponent c₀) :
    {c : OSub r // c ∈ U} ≃ₜ {c : TrisecantComponent r c₀ // (c : OSub r) ∈ U} where
  toFun := fun y => ⟨⟨(y : OSub r), hU y.2⟩, y.2⟩
  invFun := fun w => ⟨(w.1 : OSub r), w.2⟩
  left_inv := by intro y; rfl
  right_inv := by intro w; rfl
  continuous_toFun := by
    fun_prop
  continuous_invFun := by
    fun_prop

/-- **Components of `O` are locally homeomorphic to open real intervals.**
  For every component `C = connectedComponent c₀` of the trisecant set and
  every `x ∈ C`, there is an open neighbourhood of `x` in `C`
  homeomorphic to an open real interval `ChartInterval lo hi` (the trace
  of the interval chart at `x` restricted to the component).  This is the
  local-1-manifold interface of the interval/circle classification: with
  the component Hausdorff, second countable and path-connected, each
  component is a connected topological 1-manifold without boundary. -/
theorem component_local_interval {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r) (c₀ : OSub r) :
    ∀ x : TrisecantComponent r c₀,
      ∃ U : Set (TrisecantComponent r c₀), IsOpen U ∧ x ∈ U ∧
        ∃ lo hi : ℝ, Nonempty (ChartInterval lo hi ≃ₜ U) := by
  intro x
  rcases osub_local_interval h hqf hgp (x : OSub r) with
    ⟨U, hUopen, hxU, hUcc, lo, hi, hhomeo⟩
  have hcc₀ : connectedComponent (x : OSub r) = connectedComponent c₀ :=
    (connectedComponent_eq (x := c₀) (y := (x : OSub r)) x.2).symm
  have hUC : U ⊆ connectedComponent c₀ := by
    intro c hc
    exact (hcc₀ ▸ hUcc hc)
  let W : Set (TrisecantComponent r c₀) :=
    {c : TrisecantComponent r c₀ | (c : OSub r) ∈ U}
  refine ⟨W, ?_, ?_, lo, hi, ?_⟩
  · dsimp [W]
    have hcont : Continuous (fun c : TrisecantComponent r c₀ => (c : OSub r)) :=
      continuous_subtype_val
    exact hUopen.preimage hcont
  · dsimp [W]
    exact hxU
  · rcases hhomeo with ⟨e⟩
    exact ⟨e.trans (compSubtypeHomeo c₀ hUC)⟩

/-- The component is a Hausdorff topological space (a subspace of the
Hausdorff band `OpenMobius`). -/
theorem component_t2Space {r : ℝ → Space} (c₀ : OSub r) :
    T2Space (TrisecantComponent r c₀) := by
  infer_instance

/-- The component is second countable (a subspace of the second-countable
band `OpenMobius`, `OpenMapPackaging`). -/
theorem component_secondCountableTopology {r : ℝ → Space} (c₀ : OSub r) :
    SecondCountableTopology (TrisecantComponent r c₀) := by
  infer_instance

/-! ## 5. The S153 bridge: components are generic topological 1-manifolds -/

/-- **The component satisfies the generic `IsOneManifold` predicate**
(Hausdorff + second countable + locally interval-charted) — the
instantiation of the S153 classification engine on the trisecant set. -/
theorem trisecantComponent_isOneManifold {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r) (c₀ : OSub r) :
    IsOneManifold (TrisecantComponent r c₀) := by
  dsimp [IsOneManifold, LocallyIntervalChart]
  constructor
  · infer_instance
  · constructor
    · infer_instance
    · intro x
      exact component_local_interval h hqf hgp c₀ x

/-- **Every component of `O` is covered by countably many open arcs** —
the S153 exhaustion-engine existence theorem instantiated on the
trisecant-set components (`countable_open_arc_cover` + the S152 local
interval charts). -/
theorem trisecantComponent_countable_open_arc_cover {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r) (c₀ : OSub r) :
    ∃ A : ℕ → Set (TrisecantComponent r c₀),
      (∀ n, IsOpen (A n)) ∧
      (∀ n, ∃ lo hi : ℝ, Nonempty (OpenRealInterval lo hi ≃ₜ A n)) ∧
      (⋃ n, A n = univ) := by
  classical
  exact @countable_open_arc_cover (TrisecantComponent r c₀) _ _ _
    ⟨⟨c₀, mem_connectedComponent⟩⟩ (fun x => component_local_interval h hqf hgp c₀ x)

end LeanEval.KnotTheory.Quadrisecant
