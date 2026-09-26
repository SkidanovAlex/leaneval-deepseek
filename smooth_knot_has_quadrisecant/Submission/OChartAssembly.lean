import Mathlib
import Submission.OChartChain
import Submission.OChartOrder
import Submission.OSubChart

open LeanEval.KnotTheory.Quadrisecant
open Filter
open scoped Real Topology unitInterval

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

/-!
# Milestone-2 (iv) step 6, brick (b) — the chain assembly: well-defined
class coordinates

`OChartOrder.lean` (S100) showed that each interval chart of `O`
parametrises its trace injectively (unique parameter per class) and that
transition parameters depend only on the class; `OChartChain.lean` (S99)
covered every path of classes by finite chart chains with consecutive
overlapping traces; `OChartGlue.lean` (S102) showed the coordinate
relabelling is locally strictly monotone.  This module starts the
**chain assembly**: it packages the *well-definedness* of the transported
coordinate along a chain — the class-coordinate layer on top of which the
ordering (monotone global coordinate) of a component is built.

1. **the class coordinate is a function** — `oChart_class_of_symm_mem`
   (a class `g` of a trace, read at its parameter, still has class `g`:
   the membership transport used when packaging coordinates into
   transition domains), `oChart_param_unique` (a class of a chart trace
   is the lift of exactly one parameter: the chart homeo is a bijection
   and `oChartLift_injective` (S100) makes the coordinate well-defined)
   and `oChart_param_of_class_eq` (two parameters with the same class
   are equal);
2. **transitions relabel class coordinates** —
   `oChart_transition_class_mem` (the class of a transition result lies
   in any trace containing the class of the source parameter) and
   `oChart_param_transition` (if a class `g` lies in the traces of both
   charts, the transition of the `ch₁`-coordinate of `g` is the
   `ch₂`-coordinate of the same `g`: the change of parameters along an
   overlap is the relabelling of well-defined class coordinates);
3. **the cocycle** — `oChart_param_transition_trans`: transporting the
   coordinate of `g` from `ch₁` through `ch₂` to `ch₃` lands on the
   `ch₃`-coordinate of `g` — the composition of transitions is the direct
   transition, so the coordinate reached at the end of a chain is a
   function of the endpoint class only (the assembly along a chain is
   unambiguous);
4. **junction coherence of the S99 chains** —
   `oChart_chain_junction_coherent`: at every shared boundary class of an
   S99 chart chain (`OChartChain.exists_oChart_chain_along_path`), the
   transition of the left chart's coordinate of the boundary class is the
   right chart's coordinate of the same class — the assembled coordinates
   agree across the junctions of the chain.

This is the well-definedness half of the chain assembly: the monotonicity
of the assembled coordinate falls out of the local monotone patches
(`OChartGlue`, S102) once the coordinate is transported as a
class-coordinate function along the chain.

Everything here is elementary and verified (no axioms, no `sorry`).
-/

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

/-- The trace class `g` (in `W₁`) has its class equal to `g` — the
membership transport used to package parameters whose class is `g` into a
transition domain of another chart (with trace `V`). -/
lemma oChart_class_of_symm_mem {r : ℝ → Space} {c₀ : OSub r} (ch₁ : OSub1Chart r c₀)
    {g : OSub r} (hg₁ : (g : OpenMobius) ∈ ch₁.W) {V : Set OpenMobius}
    (hg₂ : (g : OpenMobius) ∈ V) :
    (oChartLift ch₁ (ch₁.homeo.symm ⟨g, hg₁⟩) : OpenMobius) ∈ V := by
  have hcl : oChartLift ch₁ (ch₁.homeo.symm ⟨g, hg₁⟩) = g := by
    simpa using oChartLift_eq_of_homeo ch₁ (z := ⟨g, hg₁⟩)
  rw [hcl]
  exact hg₂

/-- **The parameter of a class is unique (the class coordinate is
well-defined).**  A trisecant class of a chart trace is the lift of exactly
one parameter: the chart homeo is a bijection and the lift is injective
(S100 `oChartLift_injective`), so the ordering within a chart by the
unique parameters is well-defined. -/
lemma oChart_param_unique {r : ℝ → Space} {c₀ : OSub r} (ch : OSub1Chart r c₀)
    {c : OSub r} (hc : (c : OpenMobius) ∈ ch.W) :
    ∃! x : ChartInterval ch.lo ch.hi, oChartLift ch x = c := by
  refine ⟨ch.homeo.symm ⟨c, hc⟩, ?_, ?_⟩
  · simpa using oChartLift_eq_of_homeo ch (z := ⟨c, hc⟩)
  · intro y hy
    apply oChartLift_injective ch
    rw [hy]
    exact (oChartLift_eq_of_homeo ch (z := ⟨c, hc⟩)).symm

/-- Two parameters of one chart with equal classes are equal (the
coordinate is a function of the class). -/
lemma oChart_param_of_class_eq {r : ℝ → Space} {c₀ : OSub r} (ch : OSub1Chart r c₀)
    {x y : ChartInterval ch.lo ch.hi} (h : oChartLift ch x = oChartLift ch y) : x = y :=
  oChartLift_injective ch h

/-- **The transition of the coordinate of a shared class is the
coordinate in the other chart.**  If a class `g` lies in the traces of both
charts, then the transition of the `ch₁`-parameter describing `g` is the
`ch₂`-parameter describing the same class `g` — the change of parameters
along an overlap is the relabelling of the well-defined class coordinates
(the elementary well-definedness of the chain assembly at a junction). -/
lemma oChart_param_transition {r : ℝ → Space} {c₀ c₁ : OSub r}
    (ch₁ : OSub1Chart r c₀) (ch₂ : OSub1Chart r c₁)
    {g : OSub r} (hg₁ : (g : OpenMobius) ∈ ch₁.W) (hg₂ : (g : OpenMobius) ∈ ch₂.W) :
    ((oChartTransitionTo ch₁ ch₂
        ⟨ch₁.homeo.symm ⟨g, hg₁⟩, oChart_class_of_symm_mem ch₁ hg₁ hg₂⟩ :
          OChartTransitionDomain ch₂ ch₁) : ChartInterval ch₂.lo ch₂.hi) =
      ch₂.homeo.symm ⟨g, hg₂⟩ := by
  rw [oChartTransitionTo_val]
  apply congrArg ch₂.homeo.symm
  apply Subtype.ext
  simpa using oChartLift_eq_of_homeo ch₁ (z := ⟨g, hg₁⟩)



/-- The class of a transition result is transported into any trace: if the
parameter `x` describes the class `g`, then the class of the transported
parameter of `ch₂` lies in any trace `V` containing `g`. -/
lemma oChart_transition_class_mem {r : ℝ → Space} {a₁ a₂ : OSub r}
    (ch₁ : OSub1Chart r a₁) (ch₂ : OSub1Chart r a₂)
    {x : OChartTransitionDomain ch₁ ch₂} {g : OSub r} {V : Set OpenMobius}
    (hgx : oChartLift ch₁ x.1 = g) (hg : (g : OpenMobius) ∈ V) :
    (oChartLift ch₂ ((oChartTransitionTo ch₁ ch₂ x : OChartTransitionDomain ch₂ ch₁) :
        ChartInterval ch₂.lo ch₂.hi) : OpenMobius) ∈ V := by
  have hp := oChartTransition_preserves ch₁ ch₂ x
  rw [hp, hgx]
  exact hg

/-- **The cocycle at the class level.**  Transporting the coordinate of a
class `g` from `ch₁` through `ch₂` to `ch₃` gives the `ch₃`-coordinate of
the same class: the composition of transitions on the well-defined class
coordinates is the direct transition, so the assembly along a chain of
overlapping charts is unambiguous (the coordinate reached at the end of a
chain is a function of the endpoint class only). -/
lemma oChart_param_transition_trans {r : ℝ → Space} {a₁ a₂ a₃ : OSub r}
    (ch₁ : OSub1Chart r a₁) (ch₂ : OSub1Chart r a₂) (ch₃ : OSub1Chart r a₃)
    {g : OSub r} (hg₁ : (g : OpenMobius) ∈ ch₁.W) (hg₂ : (g : OpenMobius) ∈ ch₂.W)
    (hg₃ : (g : OpenMobius) ∈ ch₃.W) :
    ((oChartTransitionTo ch₂ ch₃
        ⟨((oChartTransitionTo ch₁ ch₂
            ⟨ch₁.homeo.symm ⟨g, hg₁⟩, oChart_class_of_symm_mem ch₁ hg₁ hg₂⟩ :
              OChartTransitionDomain ch₂ ch₁) : ChartInterval ch₂.lo ch₂.hi),
          oChart_transition_class_mem ch₁ ch₂
            (by simpa using oChartLift_eq_of_homeo ch₁ (z := ⟨g, hg₁⟩)) hg₃⟩ :
            OChartTransitionDomain ch₃ ch₂) : ChartInterval ch₃.lo ch₃.hi) =
      ch₃.homeo.symm ⟨g, hg₃⟩ := by
  rw [oChartTransitionTo_val]
  have hc2 : oChartLift ch₂ (((oChartTransitionTo ch₁ ch₂
        ⟨ch₁.homeo.symm ⟨g, hg₁⟩, oChart_class_of_symm_mem ch₁ hg₁ hg₂⟩ :
          OChartTransitionDomain ch₂ ch₁) : ChartInterval ch₂.lo ch₂.hi)) = g := by
    have hp := oChartTransition_preserves ch₁ ch₂
      ⟨ch₁.homeo.symm ⟨g, hg₁⟩, oChart_class_of_symm_mem ch₁ hg₁ hg₂⟩
    simpa using hp.trans (oChartLift_eq_of_homeo ch₁ (z := ⟨g, hg₁⟩))
  apply congrArg ch₃.homeo.symm
  apply Subtype.ext
  exact hc2



/-- **The junction coherence of an S99 chart chain.**  At every shared
boundary class of a chain of interval charts (as produced by
`OChartChain.exists_oChart_chain_along_path`: consecutive charts `ch i` and
`ch (i+1)` both contain the boundary class
`γ (realTime (gridReal_mem_Icc hN (i.1+1) ·))`), the transition of the left
chart's coordinate of the boundary class is the right chart's coordinate of
the same class — the assembled class coordinates agree across the junctions
of the chain (an instance of `oChart_param_transition` on the boundary
class). -/
lemma oChart_chain_junction_coherent {r : ℝ → Space} {a b : OSub r}
    (γ : Path a b) (N : ℕ) (hN : 0 < N) (τ : Fin N → I)
    (ch : (i : Fin N) → OSub1Chart r (γ (τ i)))
    (hover : ∀ i : Fin N, ∀ hi : i.1 + 1 < N,
        let j : Fin N := ⟨i.1 + 1, hi⟩
        (γ (realTime (gridReal_mem_Icc hN (i.1 + 1) (by omega))) : OpenMobius) ∈ (ch i).W ∧
        (γ (realTime (gridReal_mem_Icc hN (i.1 + 1) (by omega))) : OpenMobius) ∈ (ch j).W)
    (i : Fin N) (hi : i.1 + 1 < N) :
    ((oChartTransitionTo (ch i) (ch ⟨i.1 + 1, hi⟩)
        ⟨(ch i).homeo.symm
            ⟨γ (realTime (gridReal_mem_Icc hN (i.1 + 1) (by omega))), (hover i hi).1⟩,
          oChart_class_of_symm_mem (ch i) (hover i hi).1 (hover i hi).2⟩ :
          OChartTransitionDomain (ch ⟨i.1 + 1, hi⟩) (ch i)) :
        ChartInterval (ch ⟨i.1 + 1, hi⟩).lo (ch ⟨i.1 + 1, hi⟩).hi) =
      (ch ⟨i.1 + 1, hi⟩).homeo.symm
        ⟨γ (realTime (gridReal_mem_Icc hN (i.1 + 1) (by omega))), (hover i hi).2⟩ := by
  exact oChart_param_transition (ch i) (ch ⟨i.1 + 1, hi⟩) (hover i hi).1 (hover i hi).2

end LeanEval.KnotTheory.Quadrisecant
