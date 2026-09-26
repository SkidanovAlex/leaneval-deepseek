import Mathlib
import ChallengeDeps
import Submission.OChartChain
import Submission.OSubChart
import Submission.ComponentPath

open LeanEval.KnotTheory.Quadrisecant
open Filter
open scoped Real Topology unitInterval

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

/-!
# Milestone-2 (iv) step 6, brick (b) — ordering along a chain: the
well-definedness half and component chainability

`OSubChart.lean` (S97/S98) gave every trisecant class an interval chart
whose overlapping charts change parameters by homeomorphisms of open
interval domains preserving the class, and `OChartChain.lean` (S99) showed
that every path of trisecant classes is covered by a finite chart chain
with inhabited consecutive transition domains.  This module takes the
first step of the ordering argument of the component classification: the
parameter transported along a chain is **well-defined** (depends only on
the trisecant class, not on the parameter chosen to represent it), each
chart is an **injective parametrisation of its trace** by its open real
interval (so the classes of a chart trace carry a well-defined linear order
via their unique parameters), and any two classes of one connected
component of `O` are **chain-connected**: joined by a path inside the
component that is covered by a finite chart chain with inhabited
consecutive transition domains.

1. `oChartLift_injective` — the chart lift is injective: two parameters
   with the same class are equal (the chart homeo is a bijection and the
   class recovers the codomain point);
2. `oChartLift_surjOn_trace` — the lift is surjective onto the chart trace
   (every class of the trace is the lift of its unique parameter);
3. `oChartTransitionTo_depends_on_class` / `_Back` — the forward and
   backward transition parameters depend only on the class: the
   interval-coordinates of overlapping charts are coherent, so gluing
   along a chain of overlaps is unambiguous;
4. `exists_oChart_chain_between_component_classes` — any two classes of a
   connected component of `O` are chain-connected inside the component
   (the chain theorem of S99 applied to the component path of
   `ComponentPath.exists_path_in_component_in_O`).

This is the "the chains bite" keystone of brick (b): with well-defined,
class-mediated transport, the dichotomy "compact component ⇒ circular;
non-compact ⇒ open interval" reduces to gluing the interval coordinates of
a chain (the monotone-coordinate step: any homeomorphism of real-interval
pieces is order-preserving or order-reversing, so consecutive overlaps
fix a coherent linear order on the union; a chain that closes up gives a
circle, one that does not gives an open interval).  The next steps are
recorded in the ROADMAP session log.

Everything here is elementary and verified (no axioms, no `sorry`).
-/

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

/-- Each interval chart of `O` is injectively parametrised by its open real
interval: the chart homeo recovers the parameter from the class.  This is
the well-definedness of the *order within a chart trace* (the ordering of
classes by their unique parameters). -/
lemma oChartLift_injective {r : ℝ → Space} {c₀ : OSub r} (ch : OSub1Chart r c₀) :
    Function.Injective (oChartLift ch) := by
  intro x₁ x₂ h
  have h1 : (ch.homeo x₁ : {c : OSub r // (c : OpenMobius) ∈ ch.W}) = ch.homeo x₂ := by
    rw [oChartHomeo_eq_lift ch x₁, oChartHomeo_eq_lift ch x₂]
    apply Subtype.ext
    exact h
  exact ch.homeo.injective h1

/-- The chart lift is surjective onto the chart trace: every class in the
trace of the chart is the lift of its (unique) parameter. -/
lemma oChartLift_surjOn_trace {r : ℝ → Space} {c₀ : OSub r} (ch : OSub1Chart r c₀)
    {c : OSub r} (hcW : (c : OpenMobius) ∈ ch.W) :
    ∃ x : ChartInterval ch.lo ch.hi, oChartLift ch x = c := by
  refine ⟨ch.homeo.symm ⟨c, hcW⟩, ?_⟩
  simpa using oChartLift_eq_of_homeo ch (z := ⟨c, hcW⟩)

/-- **The transition parameter depends only on the class.**  Two parameters
of `ch₁` in the transition domain `ch₁ → ch₂` that describe the same class
are transported to the same parameter of `ch₂`: the change of charts along
a chain is a well-defined function of the trisecant class, so the
interval-coordinates of the overlapping charts are coherent (the basis of
the ordering along a chart chain). -/
lemma oChartTransitionTo_depends_on_class {r : ℝ → Space} {c₀ c₁ : OSub r}
    (ch₁ : OSub1Chart r c₀) (ch₂ : OSub1Chart r c₁)
    {x₁ x₂ : OChartTransitionDomain ch₁ ch₂}
    (hcl : oChartLift ch₁ x₁.1 = oChartLift ch₁ x₂.1) :
    oChartTransitionTo ch₁ ch₂ x₁ = oChartTransitionTo ch₁ ch₂ x₂ := by
  apply Subtype.ext
  calc
    (oChartTransitionTo ch₁ ch₂ x₁ : OChartTransitionDomain ch₂ ch₁).1
        = ch₂.homeo.symm ⟨oChartLift ch₁ x₁.1, x₁.2⟩ := oChartTransitionTo_val ch₁ ch₂ x₁
    _ = ch₂.homeo.symm ⟨oChartLift ch₁ x₂.1, x₂.2⟩ := by
      apply congrArg ch₂.homeo.symm
      apply Subtype.ext
      exact hcl
    _ = (oChartTransitionTo ch₁ ch₂ x₂ : OChartTransitionDomain ch₂ ch₁).1 :=
      (oChartTransitionTo_val ch₁ ch₂ x₂).symm

/-- The backward transition also depends only on the class. -/
lemma oChartTransitionBack_depends_on_class {r : ℝ → Space} {c₀ c₁ : OSub r}
    (ch₁ : OSub1Chart r c₀) (ch₂ : OSub1Chart r c₁)
    {y₁ y₂ : OChartTransitionDomain ch₂ ch₁}
    (hcl : oChartLift ch₂ y₁.1 = oChartLift ch₂ y₂.1) :
    oChartTransitionBack ch₁ ch₂ y₁ = oChartTransitionBack ch₁ ch₂ y₂ := by
  dsimp [oChartTransitionBack]
  exact oChartTransitionTo_depends_on_class ch₂ ch₁ hcl



/-! ## Component chainability -/

/-- **Chaining between classes of a connected component.**  Two trisecant
classes of one connected component of `O` are joined by a path that stays
inside the component and is covered by a finite chart chain whose
consecutive charts have inhabited transition domains — the chains of
`OChartChain.exists_oChartTransition_chain_along_path` applied to the
component path of `ComponentPath.exists_path_in_component_in_O`. -/
theorem exists_oChart_chain_between_component_classes {r : ℝ → Space} {c₀ x y : OSub r}
    (h : IsSmoothKnot r) (hqf : QuadrisecantFree r)
    (hgp : TorusGeneralPositionTransverse r) (hx : x ∈ connectedComponent c₀)
    (hy : y ∈ connectedComponent c₀) :
    ∃ γ : Path x y, (∀ t : I, γ t ∈ connectedComponent c₀) ∧
      ∃ (N : ℕ) (_hN : 0 < N) (τ : Fin N → I)
        (ch : (i : Fin N) → OSub1Chart r (γ (τ i))),
        ∀ i : Fin N, ∀ hi : i.1 + 1 < N,
          let j : Fin N := ⟨i.1 + 1, hi⟩
          Nonempty (OChartTransitionDomain (ch i) (ch j)) := by
  rcases exists_path_in_component_in_O h hqf hgp (c₀ := c₀) (x := x) (y := y) hx hy with
    ⟨γ, hγin⟩
  rcases exists_oChartTransition_chain_along_path h hqf hgp γ with
    ⟨N, hN, τ, ch, hstart, hend, hover⟩
  refine ⟨γ, hγin, N, hN, τ, ch, ?_⟩
  exact hover

end LeanEval.KnotTheory.Quadrisecant
