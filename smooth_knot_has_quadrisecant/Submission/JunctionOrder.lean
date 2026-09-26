import Mathlib
import Submission.NestedFamily

open LeanEval.KnotTheory.Quadrisecant
open Set
open scoped Real Topology

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

noncomputable section
namespace LeanEval.KnotTheory.Quadrisecant

/-!
# S199 — the single-junction class-order transition (the H1 step of the
S147-T chaining; module Submission/JunctionOrder.lean)

The S150-WI theorem (`walk_junction_transition_monotone`,
NestedFamily.lean) proves that at a walk junction `m` the real
relabelling `oChartTransitionReal (walkChart m) (walkChart (m+1))` is
strictly monotone-or-antitone on the connected component of the
transition domain containing the coordinate of the walk-overlap class.
That is the coordinate-level H1 fact; THIS module reads it at CLASS
level — the form in which the prefix-union coordinate (a real function
of classes) is glued at a junction:

1. **`chParam`** — the inverse-coordinate map: the chart parameter of a
   trace class (`ch.homeo.symm`), with `chParam_lift` (lifting the
   parameter gives the class back) — the class-coordinate vocabulary of
   the junction order;
2. **`chParam_transition_real`** — the coordinate-change identification
   at real-value level: the real value of the transition of the
   `ch₁`-parameter of a shared class equals the real value of its
   `ch₂`-parameter (corollary of the S98 `oChart_param_transition`
   parameter equality);
3. **`transitionDomain` / `junctionComponent`** — the transition-domain
   set of `ch₁` towards `ch₂` and the connected component of the walk
   junction (short names for the statements);
4. **`junctionClassOrder_of_monotone`** — the generic H1 transfer: if
   the real transition is strictly monotone-or-antitone on the junction
   component `C`, then two overlap classes whose `ch₁`-coordinates both
   lie in `C` keep their `ch₁`-order in their `ch₂`-coordinates, in the
   same direction;
5. **`walk_junction_classOrder`** — the S199 headline: the walk
   instance at junction `m` (the classes of the overlap of the walk
   traces `T_m`/`T_{m+1}` with `ch m`-coordinates in the junction
   component of the walk-overlap class are consistently ordered by the
   two trace coordinates) — WI read at class level, the H1 step the
   prefix-union chaining composes (with the S198 cell interlock
   certifying the coordinates along the per-length cells).

Everything here is verified (no axioms, no `sorry`).
-/

/-- The parameter of a trace class: `ch.homeo.symm` re-read as the
inverse coordinate map from a class of the trace to its chart parameter. -/
def chParam {r : ℝ → Space} {c₀ : OSub r} (ch : OSub1Chart r c₀) (c : OSub r)
    (hc : (c : OpenMobius) ∈ ch.W) : ChartInterval ch.lo ch.hi :=
  ch.homeo.symm ⟨c, hc⟩

/-- The parameter of a class is the inverse lift: lifting `chParam` back
gives the class. -/
lemma chParam_lift {r : ℝ → Space} {c₀ : OSub r} (ch : OSub1Chart r c₀) {c : OSub r}
    (hc : (c : OpenMobius) ∈ ch.W) : oChartLift ch (chParam ch c hc) = c := by
  dsimp [chParam]
  simpa using oChartLift_eq_of_homeo ch (z := ⟨c, hc⟩)

/-- The real value of the transition of the `ch₁`-parameter of a shared
class is the real value of its `ch₂`-parameter (the coordinate-change
identification at the level of real values, with an arbitrary transition-
domain proof — corollary of the S98 `oChart_param_transition` parameter
equality). -/
lemma chParam_transition_real {r : ℝ → Space} {c₀ c₁ : OSub r}
    (ch₁ : OSub1Chart r c₀) (ch₂ : OSub1Chart r c₁)
    {g : OSub r} (hg₁ : (g : OpenMobius) ∈ ch₁.W) (hg₂ : (g : OpenMobius) ∈ ch₂.W)
    (hdom : (oChartLift ch₁ (chParam ch₁ g hg₁) : OpenMobius) ∈ ch₂.W) :
    oChartTransitionReal ch₁ ch₂ ⟨chParam ch₁ g hg₁, hdom⟩ = (chParam ch₂ g hg₂ : ℝ) := by
  have hp := oChart_param_transition ch₁ ch₂ hg₁ hg₂
  have hval := congrArg (fun w : ChartInterval ch₂.lo ch₂.hi => (w : ℝ)) hp
  dsimp [oChartTransitionReal] at hval ⊢
  have heq : (⟨chParam ch₁ g hg₁, hdom⟩ : OChartTransitionDomain ch₁ ch₂) =
      ⟨chParam ch₁ g hg₁, oChart_class_of_symm_mem ch₁ hg₁ hg₂⟩ := by
    apply Subtype.ext
    rfl
  rw [heq]
  simpa [chParam] using hval

/-- The transition-domain set of `ch₁` towards `ch₂`: the `ch₁`-parameters
whose classes lie in the trace of `ch₂` (the chart-parameter form of the
trace overlap). -/
def transitionDomain {r : ℝ → Space} {c₀ c₁ : OSub r} (ch₁ : OSub1Chart r c₀)
    (ch₂ : OSub1Chart r c₁) : Set (ChartInterval ch₁.lo ch₁.hi) :=
  {x | (oChartLift ch₁ x : OpenMobius) ∈ ch₂.W}

/-- The junction component: the connected component of the transition
domain containing the transition parameter `t₀` (the component on which
the S150-WI relabelling is monotone-or-antitone). -/
abbrev junctionComponent {r : ℝ → Space} {c₀ c₁ : OSub r} (ch₁ : OSub1Chart r c₀)
    (ch₂ : OSub1Chart r c₁) (t₀ : OChartTransitionDomain ch₁ ch₂) :
    Set (ChartInterval ch₁.lo ch₁.hi) :=
  connectedComponentIn (transitionDomain ch₁ ch₂) t₀.1

/-- **Generic class-order transfer across a junction (H1 single-step).**
If the real transition `oChartTransitionReal ch₁ ch₂` is strictly
monotone-or-antitone on the junction component `C`, then the
`ch₂`-coordinate order of two overlap classes (whose `ch₁`-coordinates
both lie in `C`) is consistent with their `ch₁`-coordinate order, in the
same direction. -/
lemma junctionClassOrder_of_monotone {r : ℝ → Space} {c₀ c₁ : OSub r}
    (ch₁ : OSub1Chart r c₀) (ch₂ : OSub1Chart r c₁) (t₀ : OChartTransitionDomain ch₁ ch₂)
    (htrans :
      (∀ ⦃a b : ChartInterval ch₁.lo ch₁.hi⦄,
          (ha : a ∈ junctionComponent ch₁ ch₂ t₀) → (hb : b ∈ junctionComponent ch₁ ch₂ t₀) →
          (a : ℝ) < (b : ℝ) →
          oChartTransitionReal ch₁ ch₂ ⟨a, connectedComponentIn_subset
            (transitionDomain ch₁ ch₂) t₀.1 ha⟩ <
          oChartTransitionReal ch₁ ch₂ ⟨b, connectedComponentIn_subset
            (transitionDomain ch₁ ch₂) t₀.1 hb⟩) ∨
      (∀ ⦃a b : ChartInterval ch₁.lo ch₁.hi⦄,
          (ha : a ∈ junctionComponent ch₁ ch₂ t₀) → (hb : b ∈ junctionComponent ch₁ ch₂ t₀) →
          (a : ℝ) < (b : ℝ) →
          oChartTransitionReal ch₁ ch₂ ⟨b, connectedComponentIn_subset
            (transitionDomain ch₁ ch₂) t₀.1 hb⟩ <
          oChartTransitionReal ch₁ ch₂ ⟨a, connectedComponentIn_subset
            (transitionDomain ch₁ ch₂) t₀.1 ha⟩)) :
    (∀ ⦃x y : OSub r⦄ (hx₁ : (x : OpenMobius) ∈ ch₁.W) (hx₂ : (x : OpenMobius) ∈ ch₂.W)
        (hy₁ : (y : OpenMobius) ∈ ch₁.W) (hy₂ : (y : OpenMobius) ∈ ch₂.W),
        chParam ch₁ x hx₁ ∈ junctionComponent ch₁ ch₂ t₀ →
        chParam ch₁ y hy₁ ∈ junctionComponent ch₁ ch₂ t₀ →
        (chParam ch₁ x hx₁ : ℝ) < (chParam ch₁ y hy₁ : ℝ) →
        (chParam ch₂ x hx₂ : ℝ) < (chParam ch₂ y hy₂ : ℝ)) ∨
    (∀ ⦃x y : OSub r⦄ (hx₁ : (x : OpenMobius) ∈ ch₁.W) (hx₂ : (x : OpenMobius) ∈ ch₂.W)
        (hy₁ : (y : OpenMobius) ∈ ch₁.W) (hy₂ : (y : OpenMobius) ∈ ch₂.W),
        chParam ch₁ x hx₁ ∈ junctionComponent ch₁ ch₂ t₀ →
        chParam ch₁ y hy₁ ∈ junctionComponent ch₁ ch₂ t₀ →
        (chParam ch₁ x hx₁ : ℝ) < (chParam ch₁ y hy₁ : ℝ) →
        (chParam ch₂ y hy₂ : ℝ) < (chParam ch₂ x hx₂ : ℝ)) := by
  rcases htrans with hinc | hdec
  · left
    intro x y hx₁ hx₂ hy₁ hy₂ hCx hCy hxy
    have htx : oChartTransitionReal ch₁ ch₂
          ⟨chParam ch₁ x hx₁, connectedComponentIn_subset (transitionDomain ch₁ ch₂) t₀.1 hCx⟩ <
        oChartTransitionReal ch₁ ch₂
          ⟨chParam ch₁ y hy₁, connectedComponentIn_subset (transitionDomain ch₁ ch₂) t₀.1 hCy⟩ :=
      hinc (a := chParam ch₁ x hx₁) (b := chParam ch₁ y hy₁) hCx hCy hxy
    have hxeq : (⟨chParam ch₁ x hx₁, connectedComponentIn_subset (transitionDomain ch₁ ch₂) t₀.1 hCx⟩ :
        OChartTransitionDomain ch₁ ch₂) =
        ⟨chParam ch₁ x hx₁, oChart_class_of_symm_mem ch₁ hx₁ hx₂⟩ := by
      apply Subtype.ext
      rfl
    have hyeq : (⟨chParam ch₁ y hy₁, connectedComponentIn_subset (transitionDomain ch₁ ch₂) t₀.1 hCy⟩ :
        OChartTransitionDomain ch₁ ch₂) =
        ⟨chParam ch₁ y hy₁, oChart_class_of_symm_mem ch₁ hy₁ hy₂⟩ := by
      apply Subtype.ext
      rfl
    rw [hxeq, hyeq] at htx
    rw [chParam_transition_real ch₁ ch₂ hx₁ hx₂ (oChart_class_of_symm_mem ch₁ hx₁ hx₂),
        chParam_transition_real ch₁ ch₂ hy₁ hy₂ (oChart_class_of_symm_mem ch₁ hy₁ hy₂)] at htx
    exact htx
  · right
    intro x y hx₁ hx₂ hy₁ hy₂ hCx hCy hxy
    have htx : oChartTransitionReal ch₁ ch₂
          ⟨chParam ch₁ y hy₁, connectedComponentIn_subset (transitionDomain ch₁ ch₂) t₀.1 hCy⟩ <
        oChartTransitionReal ch₁ ch₂
          ⟨chParam ch₁ x hx₁, connectedComponentIn_subset (transitionDomain ch₁ ch₂) t₀.1 hCx⟩ :=
      hdec (a := chParam ch₁ x hx₁) (b := chParam ch₁ y hy₁) hCx hCy hxy
    have hxeq : (⟨chParam ch₁ x hx₁, connectedComponentIn_subset (transitionDomain ch₁ ch₂) t₀.1 hCx⟩ :
        OChartTransitionDomain ch₁ ch₂) =
        ⟨chParam ch₁ x hx₁, oChart_class_of_symm_mem ch₁ hx₁ hx₂⟩ := by
      apply Subtype.ext
      rfl
    have hyeq : (⟨chParam ch₁ y hy₁, connectedComponentIn_subset (transitionDomain ch₁ ch₂) t₀.1 hCy⟩ :
        OChartTransitionDomain ch₁ ch₂) =
        ⟨chParam ch₁ y hy₁, oChart_class_of_symm_mem ch₁ hy₁ hy₂⟩ := by
      apply Subtype.ext
      rfl
    rw [hxeq, hyeq] at htx
    rw [chParam_transition_real ch₁ ch₂ hx₁ hx₂ (oChart_class_of_symm_mem ch₁ hx₁ hx₂),
        chParam_transition_real ch₁ ch₂ hy₁ hy₂ (oChart_class_of_symm_mem ch₁ hy₁ hy₂)] at htx
    exact htx

/-- **The walk-junction class-order consistency (the H1 single-step at
the junction `m`).**  Two classes in the overlap of the walk traces `m`
and `m+1`, whose `ch m`-coordinates both lie in the junction component
of the walk-overlap class, keep their `ch m`-order in their
`ch (m+1)`-coordinates — consistently in one direction (the S150-WI
monotone transition read at class level, via
`transition_monotone_on_connected_open` + the generic transfer). -/
theorem walk_junction_classOrder {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty)
    (m : ℕ) :
    let ch₁ := walkChart h hqf hgp cl e m
    let ch₂ := walkChart h hqf hgp cl e (m + 1)
    let t₀ : OChartTransitionDomain ch₁ ch₂ :=
      oChartTraceOverlapParam ch₁ ch₂ (walkOverlapClass h hqf hgp cl e hoverlap m)
        (walkOverlapClass_mem_left h hqf hgp cl e hoverlap m)
        (walkOverlapClass_mem_right h hqf hgp cl e hoverlap m)
    (∀ ⦃x y : OSub r⦄ (hx₁ : (x : OpenMobius) ∈ ch₁.W) (hx₂ : (x : OpenMobius) ∈ ch₂.W)
        (hy₁ : (y : OpenMobius) ∈ ch₁.W) (hy₂ : (y : OpenMobius) ∈ ch₂.W),
        chParam ch₁ x hx₁ ∈ junctionComponent ch₁ ch₂ t₀ →
        chParam ch₁ y hy₁ ∈ junctionComponent ch₁ ch₂ t₀ →
        (chParam ch₁ x hx₁ : ℝ) < (chParam ch₁ y hy₁ : ℝ) →
        (chParam ch₂ x hx₂ : ℝ) < (chParam ch₂ y hy₂ : ℝ)) ∨
    (∀ ⦃x y : OSub r⦄ (hx₁ : (x : OpenMobius) ∈ ch₁.W) (hx₂ : (x : OpenMobius) ∈ ch₂.W)
        (hy₁ : (y : OpenMobius) ∈ ch₁.W) (hy₂ : (y : OpenMobius) ∈ ch₂.W),
        chParam ch₁ x hx₁ ∈ junctionComponent ch₁ ch₂ t₀ →
        chParam ch₁ y hy₁ ∈ junctionComponent ch₁ ch₂ t₀ →
        (chParam ch₁ x hx₁ : ℝ) < (chParam ch₁ y hy₁ : ℝ) →
        (chParam ch₂ y hy₂ : ℝ) < (chParam ch₂ x hx₂ : ℝ)) := by
  classical
  dsimp
  let ch₁ := walkChart h hqf hgp cl e m
  let ch₂ := walkChart h hqf hgp cl e (m + 1)
  let t₀ : OChartTransitionDomain ch₁ ch₂ :=
    oChartTraceOverlapParam ch₁ ch₂ (walkOverlapClass h hqf hgp cl e hoverlap m)
      (walkOverlapClass_mem_left h hqf hgp cl e hoverlap m)
      (walkOverlapClass_mem_right h hqf hgp cl e hoverlap m)
  have htrans := transition_monotone_on_connected_open ch₁ ch₂
    (isOpen_connectedComponentIn_transitionDomain ch₁ ch₂ t₀)
    (isPreconnected_connectedComponentIn)
    (connectedComponentIn_subset (transitionDomain ch₁ ch₂) t₀.1)
  exact junctionClassOrder_of_monotone ch₁ ch₂ t₀ htrans

end LeanEval.KnotTheory.Quadrisecant
