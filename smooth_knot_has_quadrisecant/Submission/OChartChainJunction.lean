import Mathlib
import Submission.OChartAssemblyMonotone
import Submission.OChartAssembly
import Submission.OChartGlue
import Submission.OChartChain

open LeanEval.KnotTheory.Quadrisecant
open Filter
open scoped Real Topology unitInterval

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

/-!
# Milestone-2 (iv) step 6, brick (b) — the chain assembly: the S102
patches instantiated at the junctions of an S99 chain

`OChartGlue.lean` (S102) proved that every transition parameter carries a
monotone interval neighbourhood (`OChartMonotoneNbhd`,
`exists_oChartMonotoneNbhd`); `OChartAssemblyMonotone.lean` (S104) packaged
the monotone patches and their composition (`MonotoneOnPiece`,
`composite_monotone_direction`, the two-junction transport instance);
`OChartAssembly.lean` (S103) gave the well-defined class coordinates and
the junction coherence of the S99 chains.  This module instantiates the
S102 patches **at the junctions of an
`OChartChain.exists_oChart_chain_along_path` chain** and states the
resulting `TransportStepDomain` conditions.

1. **the junction parameter** — `oChartChainJunctionParam`: the
   transition-domain element at a junction (charts `ch i`, `ch (i+1)`,
   shared boundary class `γ (realTime (gridReal_mem_Icc hN (i.1+1) ·))`,
   memberships `(hover i hi).1/.2`): the `ch i`-coordinate of the boundary
   class packaged into `OChartTransitionDomain (ch i) (ch (i+1))`;
   `oChartChainJunctionParam_class` — it describes the boundary class
   (`oChartLift_eq_of_homeo`);
2. **the S102 patch at the junction** —
   `oChart_chain_junction_monotoneNbhd` (the monotone neighbourhood
   exists at every junction), `oChartChainJunctionNbhd` (the chosen one),
   `oChart_chain_junction_piece_monotone` (its piece map is
   `MonotoneOnPiece`) and
   `oChart_chain_junction_piece_coordinate` (on the piece, the values are
   the `ch (i+1)`-coordinates of the same classes as the `ch i`-
   parameters — the monotonicity direction compares the two charts'
   orders of the same classes);
3. **the step-domain condition** — `oChartChainStepDomain` (the
   parameters of the first junction patch whose transport lands in the
   second junction patch) and
   `oChart_chain_two_junction_step_monotone` (the composite transport
   `ch i → ch (i+2)` is monotone in one direction on the step domain —
   the composition engine applied to two consecutive instantiated
   junction patches).

This is the junction-instantiation slice of the monotone chain assembly;
the shrinking slice (ensure each junction patch's transport lands in the
next patch's piece, via openness/continuity) and the `Fin (N-1)` iteration
are recorded next in the ROADMAP session log.

Everything here is elementary and verified (no axioms, no `sorry`).
-/

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

/-- The transition-domain parameter at a junction of an S99 chart chain:
the `ch i`-coordinate of the shared boundary class (with the memberships
of `hover`), packaged into the transition domain `ch i → ch (i+1)`. -/
noncomputable def oChartChainJunctionParam {r : ℝ → Space} {a b : OSub r}
    (γ : Path a b) (N : ℕ) (hN : 0 < N) (τ : Fin N → I)
    (ch : (i : Fin N) → OSub1Chart r (γ (τ i)))
    (hover : ∀ i : Fin N, ∀ hi : i.1 + 1 < N,
        let j : Fin N := ⟨i.1 + 1, hi⟩
        (γ (realTime (gridReal_mem_Icc hN (i.1 + 1) (by omega))) : OpenMobius) ∈ (ch i).W ∧
        (γ (realTime (gridReal_mem_Icc hN (i.1 + 1) (by omega))) : OpenMobius) ∈ (ch j).W)
    (i : Fin N) (hi : i.1 + 1 < N) :
    OChartTransitionDomain (ch i) (ch ⟨i.1 + 1, hi⟩) :=
  ⟨(ch i).homeo.symm
      ⟨γ (realTime (gridReal_mem_Icc hN (i.1 + 1) (by omega))), (hover i hi).1⟩,
    oChart_class_of_symm_mem (ch i) (hover i hi).1 (hover i hi).2⟩

/-- The junction parameter describes the shared boundary class of the two
adjacent charts. -/
lemma oChartChainJunctionParam_class {r : ℝ → Space} {a b : OSub r}
    (γ : Path a b) (N : ℕ) (hN : 0 < N) (τ : Fin N → I)
    (ch : (i : Fin N) → OSub1Chart r (γ (τ i)))
    (hover : ∀ i : Fin N, ∀ hi : i.1 + 1 < N,
        let j : Fin N := ⟨i.1 + 1, hi⟩
        (γ (realTime (gridReal_mem_Icc hN (i.1 + 1) (by omega))) : OpenMobius) ∈ (ch i).W ∧
        (γ (realTime (gridReal_mem_Icc hN (i.1 + 1) (by omega))) : OpenMobius) ∈ (ch j).W)
    (i : Fin N) (hi : i.1 + 1 < N) :
    oChartLift (ch i) (((oChartChainJunctionParam γ N hN τ ch hover i hi) :
        OChartTransitionDomain (ch i) (ch ⟨i.1 + 1, hi⟩)) :
        ChartInterval (ch i).lo (ch i).hi) =
      γ (realTime (gridReal_mem_Icc hN (i.1 + 1) (by omega))) := by
  simpa [oChartChainJunctionParam] using
    (oChartLift_eq_of_homeo (ch i)
      (z := ⟨γ (realTime (gridReal_mem_Icc hN (i.1 + 1) (by omega))), (hover i hi).1⟩))

/-- **The S102 monotone neighbourhood exists at every junction of an S99
chain.**  The coordinate relabelling between the adjacent charts of a
chain junction is strictly monotone on an interval neighbourhood of the
boundary class's parameter. -/
theorem oChart_chain_junction_monotoneNbhd {r : ℝ → Space} {a b : OSub r}
    (γ : Path a b) (N : ℕ) (hN : 0 < N) (τ : Fin N → I)
    (ch : (i : Fin N) → OSub1Chart r (γ (τ i)))
    (hover : ∀ i : Fin N, ∀ hi : i.1 + 1 < N,
        let j : Fin N := ⟨i.1 + 1, hi⟩
        (γ (realTime (gridReal_mem_Icc hN (i.1 + 1) (by omega))) : OpenMobius) ∈ (ch i).W ∧
        (γ (realTime (gridReal_mem_Icc hN (i.1 + 1) (by omega))) : OpenMobius) ∈ (ch j).W)
    (i : Fin N) (hi : i.1 + 1 < N) :
    Nonempty (OChartMonotoneNbhd (ch i) (ch ⟨i.1 + 1, hi⟩)
      (oChartChainJunctionParam γ N hN τ ch hover i hi)) := by
  exact exists_oChartMonotoneNbhd (ch i) (ch ⟨i.1 + 1, hi⟩)
    (oChartChainJunctionParam γ N hN τ ch hover i hi)

/-- The chosen monotone neighbourhood at a junction of an S99 chain. -/
noncomputable def oChartChainJunctionNbhd {r : ℝ → Space} {a b : OSub r}
    (γ : Path a b) (N : ℕ) (hN : 0 < N) (τ : Fin N → I)
    (ch : (i : Fin N) → OSub1Chart r (γ (τ i)))
    (hover : ∀ i : Fin N, ∀ hi : i.1 + 1 < N,
        let j : Fin N := ⟨i.1 + 1, hi⟩
        (γ (realTime (gridReal_mem_Icc hN (i.1 + 1) (by omega))) : OpenMobius) ∈ (ch i).W ∧
        (γ (realTime (gridReal_mem_Icc hN (i.1 + 1) (by omega))) : OpenMobius) ∈ (ch j).W)
    (i : Fin N) (hi : i.1 + 1 < N) :
    OChartMonotoneNbhd (ch i) (ch ⟨i.1 + 1, hi⟩)
      (oChartChainJunctionParam γ N hN τ ch hover i hi) :=
  Classical.choice (oChart_chain_junction_monotoneNbhd γ N hN τ ch hover i hi)

/-- The instantiated junction patch is monotone in one direction on its
piece: the coordinate transport `ch i → ch (i+1)` of the S99 chain is
strictly monotone on the neighbourhood of the boundary class parameter. -/
lemma oChart_chain_junction_piece_monotone {r : ℝ → Space} {a b : OSub r}
    (γ : Path a b) (N : ℕ) (hN : 0 < N) (τ : Fin N → I)
    (ch : (i : Fin N) → OSub1Chart r (γ (τ i)))
    (hover : ∀ i : Fin N, ∀ hi : i.1 + 1 < N,
        let j : Fin N := ⟨i.1 + 1, hi⟩
        (γ (realTime (gridReal_mem_Icc hN (i.1 + 1) (by omega))) : OpenMobius) ∈ (ch i).W ∧
        (γ (realTime (gridReal_mem_Icc hN (i.1 + 1) (by omega))) : OpenMobius) ∈ (ch j).W)
    (i : Fin N) (hi : i.1 + 1 < N) :
    MonotoneOnPiece (oChartTransitionOnInterval (ch i) (ch ⟨i.1 + 1, hi⟩)
      (oChartChainJunctionNbhd γ N hN τ ch hover i hi).subset
      (oChartChainJunctionNbhd γ N hN τ ch hover i hi).dom) :=
  (oChartChainJunctionNbhd γ N hN τ ch hover i hi).monotone




/-- **The junction patch values are the `ch (i+1)`-coordinates of the same
classes.**  For a parameter of the monotone neighbourhood at a chain
junction, the piece value is the coordinate of the adjacent chart
describing the same trisecant class as the corresponding parameter of
`ch i` (the S102 `oChartNbhd_piece_coordinate` reading, instantiated at
the junction): the monotonicity direction of the patch compares the
`ch i`-order and the `ch (i+1)`-order of the same classes. -/
lemma oChart_chain_junction_piece_coordinate {r : ℝ → Space} {a b : OSub r}
    (γ : Path a b) (N : ℕ) (hN : 0 < N) (τ : Fin N → I)
    (ch : (i : Fin N) → OSub1Chart r (γ (τ i)))
    (hover : ∀ i : Fin N, ∀ hi : i.1 + 1 < N,
        let j : Fin N := ⟨i.1 + 1, hi⟩
        (γ (realTime (gridReal_mem_Icc hN (i.1 + 1) (by omega))) : OpenMobius) ∈ (ch i).W ∧
        (γ (realTime (gridReal_mem_Icc hN (i.1 + 1) (by omega))) : OpenMobius) ∈ (ch j).W)
    (i : Fin N) (hi : i.1 + 1 < N)
    (a : ChartInterval (oChartChainJunctionNbhd γ N hN τ ch hover i hi).lo
      (oChartChainJunctionNbhd γ N hN τ ch hover i hi).hi) :
    ∃ y : OChartTransitionDomain (ch ⟨i.1 + 1, hi⟩) (ch i),
      oChartLift (ch ⟨i.1 + 1, hi⟩)
          (((y : OChartTransitionDomain (ch ⟨i.1 + 1, hi⟩) (ch i)) :
            ChartInterval (ch ⟨i.1 + 1, hi⟩).lo (ch ⟨i.1 + 1, hi⟩).hi)) =
        oChartLift (ch i)
          (⟨(a : ℝ), (oChartChainJunctionNbhd γ N hN τ ch hover i hi).subset a.2⟩ :
            ChartInterval (ch i).lo (ch i).hi) ∧
      (((y : OChartTransitionDomain (ch ⟨i.1 + 1, hi⟩) (ch i)) :
          ChartInterval (ch ⟨i.1 + 1, hi⟩).lo (ch ⟨i.1 + 1, hi⟩).hi) : ℝ) =
        oChartTransitionOnInterval (ch i) (ch ⟨i.1 + 1, hi⟩)
          (oChartChainJunctionNbhd γ N hN τ ch hover i hi).subset
          (oChartChainJunctionNbhd γ N hN τ ch hover i hi).dom a := by
  exact oChartNbhd_piece_coordinate (ch i) (ch ⟨i.1 + 1, hi⟩)
    (oChartChainJunctionParam γ N hN τ ch hover i hi)
    (oChartChainJunctionNbhd γ N hN τ ch hover i hi) a

/-- **The step domain between two consecutive junctions.**  The parameters
of the first junction patch whose transport lands inside the second
junction patch's piece — the `TransportStepDomain` condition on which the
composite transport `ch i → ch (i+2)` is defined. -/
noncomputable def oChartChainStepDomain {r : ℝ → Space} {c₀ c₁ c₂ : OSub r}
    (ch₁ : OSub1Chart r c₀) (ch₂ : OSub1Chart r c₁) (ch₃ : OSub1Chart r c₂)
    (x₁ : OChartTransitionDomain ch₁ ch₂) (x₂ : OChartTransitionDomain ch₂ ch₃)
    (nb₁ : OChartMonotoneNbhd ch₁ ch₂ x₁) (nb₂ : OChartMonotoneNbhd ch₂ ch₃ x₂) :
    Type :=
  TransportStepDomain (oChartTransitionOnInterval ch₁ ch₂ nb₁.subset nb₁.dom)
    nb₂.lo nb₂.hi

/-- **The composite transport over two consecutive junctions is monotone
on the step domain.**  On the parameters whose first-junction transport
lands in the second-junction patch, the transported coordinate from the
first to the third chart of the S99 chain (through the middle chart) is
monotone in one direction — the composition engine applied to the two
instantiated junction patches. -/
lemma oChart_chain_two_junction_step_monotone {r : ℝ → Space} {a b : OSub r}
    (γ : Path a b) (N : ℕ) (hN : 0 < N) (τ : Fin N → I)
    (ch : (i : Fin N) → OSub1Chart r (γ (τ i)))
    (hover : ∀ i : Fin N, ∀ hi : i.1 + 1 < N,
        let j : Fin N := ⟨i.1 + 1, hi⟩
        (γ (realTime (gridReal_mem_Icc hN (i.1 + 1) (by omega))) : OpenMobius) ∈ (ch i).W ∧
        (γ (realTime (gridReal_mem_Icc hN (i.1 + 1) (by omega))) : OpenMobius) ∈ (ch j).W)
    (i : Fin N) (hij : i.1 + 1 < N) (hjk : i.1 + 2 < N) :
    let j : Fin N := ⟨i.1 + 1, hij⟩
    let k : Fin N := ⟨i.1 + 2, hjk⟩
    let step : Type := oChartChainStepDomain (ch i) (ch j) (ch k)
      (oChartChainJunctionParam γ N hN τ ch hover i hij)
      (oChartChainJunctionParam γ N hN τ ch hover j hjk)
      (oChartChainJunctionNbhd γ N hN τ ch hover i hij)
      (oChartChainJunctionNbhd γ N hN τ ch hover j hjk)
    (∀ u v : step, (u.1 : ℝ) < (v.1 : ℝ) →
        (oChartTransitionOnInterval (ch j) (ch k)
            (oChartChainJunctionNbhd γ N hN τ ch hover j hjk).subset
            (oChartChainJunctionNbhd γ N hN τ ch hover j hjk).dom)
              ⟨(oChartTransitionOnInterval (ch i) (ch j)
                  (oChartChainJunctionNbhd γ N hN τ ch hover i hij).subset
                  (oChartChainJunctionNbhd γ N hN τ ch hover i hij).dom) u.1, u.2⟩ <
          (oChartTransitionOnInterval (ch j) (ch k)
            (oChartChainJunctionNbhd γ N hN τ ch hover j hjk).subset
            (oChartChainJunctionNbhd γ N hN τ ch hover j hjk).dom)
              ⟨(oChartTransitionOnInterval (ch i) (ch j)
                  (oChartChainJunctionNbhd γ N hN τ ch hover i hij).subset
                  (oChartChainJunctionNbhd γ N hN τ ch hover i hij).dom) v.1, v.2⟩) ∨
    (∀ u v : step, (u.1 : ℝ) < (v.1 : ℝ) →
        (oChartTransitionOnInterval (ch j) (ch k)
            (oChartChainJunctionNbhd γ N hN τ ch hover j hjk).subset
            (oChartChainJunctionNbhd γ N hN τ ch hover j hjk).dom)
              ⟨(oChartTransitionOnInterval (ch i) (ch j)
                  (oChartChainJunctionNbhd γ N hN τ ch hover i hij).subset
                  (oChartChainJunctionNbhd γ N hN τ ch hover i hij).dom) v.1, v.2⟩ <
          (oChartTransitionOnInterval (ch j) (ch k)
            (oChartChainJunctionNbhd γ N hN τ ch hover j hjk).subset
            (oChartChainJunctionNbhd γ N hN τ ch hover j hjk).dom)
              ⟨(oChartTransitionOnInterval (ch i) (ch j)
                  (oChartChainJunctionNbhd γ N hN τ ch hover i hij).subset
                  (oChartChainJunctionNbhd γ N hN τ ch hover i hij).dom) u.1, u.2⟩) := by
  exact composite_monotone_direction
    (oChartMonotoneNbhd_piece_monotone (ch i) (ch ⟨i.1 + 1, hij⟩)
      (oChartChainJunctionParam γ N hN τ ch hover i hij)
      (oChartChainJunctionNbhd γ N hN τ ch hover i hij))
    (oChartMonotoneNbhd_piece_monotone (ch ⟨i.1 + 1, hij⟩) (ch ⟨i.1 + 2, hjk⟩)
      (oChartChainJunctionParam γ N hN τ ch hover ⟨i.1 + 1, hij⟩ hjk)
      (oChartChainJunctionNbhd γ N hN τ ch hover ⟨i.1 + 1, hij⟩ hjk))



/-! ## The shrinking slice: transports land in the next patch on whole
sub-pieces

`exists_interval_preimage_piece` is the elementary continuity/openness
shrink: a continuous real map on an open interval that sends a point into
an open target interval sends a whole interval neighbourhood of the point
into the target (the preimage of the target is open, so it contains a
metric ball, hence an interval).  `exists_oChart_step_subpiece` applies it
to the interval-piece transition maps of two consecutive monotone
neighbourhoods: whenever the first patch's transport of a base parameter
lands in the second patch's piece, the step-domain condition holds on a
whole open interval sub-piece around the base parameter (so the composite
transport of the composition engine is defined and monotone there).  Note
that the alignment hypothesis `hx` is genuinely needed — consecutive
junction patches sit at the coordinates of *different* boundary classes
along the path, so a transport lands in the next patch only when the data
are aligned (see the ROADMAP session log for the honest discussion of the
global chain-transport framing). -/

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

/-- **Shrinking: continuous maps land inside an open target interval on a
whole sub-piece.**  If a continuous real map on an open interval takes a
point into an open target interval, then it takes a whole interval
neighbourhood of the point (a sub-piece of the domain) into the target:
the preimage of the target interval is open (continuity), so it contains a
metric ball around the point, hence an open interval around it. -/
lemma exists_interval_preimage_piece {lo hi : ℝ} (φ : ChartInterval lo hi → ℝ)
    (hφ : Continuous φ) (x₀ : ChartInterval lo hi) {c d : ℝ}
    (hx : φ x₀ ∈ Set.Ioo c d) :
    ∃ a b : ℝ, a < b ∧ (x₀ : ℝ) ∈ Set.Ioo a b ∧
      (∀ u : ChartInterval lo hi, (u : ℝ) ∈ Set.Ioo a b → φ u ∈ Set.Ioo c d) := by
  let S : Set (ChartInterval lo hi) := {u | φ u ∈ Set.Ioo c d}
  have hSopen : IsOpen S := isOpen_Ioo.preimage hφ
  have hxS : x₀ ∈ S := hx
  have hnhd : S ∈ 𝓝 x₀ := hSopen.mem_nhds hxS
  rcases (Metric.mem_nhds_iff.mp hnhd) with ⟨ε, hεpos, hball⟩
  let a : ℝ := (x₀ : ℝ) - ε / 2
  let b : ℝ := (x₀ : ℝ) + ε / 2
  refine ⟨a, b, ?_, ?_, ?_⟩
  · dsimp [a, b]
    linarith [hεpos]
  · dsimp [a, b]
    constructor <;> linarith [hεpos]
  · intro u hu
    have hb : u ∈ Metric.ball x₀ ε := by
      rw [Metric.mem_ball]
      have hdist : dist u x₀ < ε := by
        change dist (u : ℝ) (x₀ : ℝ) < ε
        rw [Real.dist_eq, abs_lt]
        dsimp [a, b] at hu
        constructor <;> linarith [hu.1, hu.2, hεpos]
      exact hdist
    simpa [S] using hball hb

/-- **Shrinking at a chain step: the transport lands in the next patch on
a whole sub-piece.**  If the transport of the first junction patch takes a
base parameter into the second patch's piece, then it takes a whole
interval sub-piece around the base parameter into the second patch's piece
— the step-domain condition holds on a genuine open interval around any
transport-aligned base parameter (the continuity of the interval-piece
transition map, S102). -/
lemma exists_oChart_step_subpiece {r : ℝ → Space} {c₀ c₁ c₂ : OSub r}
    (ch₁ : OSub1Chart r c₀) (ch₂ : OSub1Chart r c₁) (ch₃ : OSub1Chart r c₂)
    (x₁ : OChartTransitionDomain ch₁ ch₂) (x₂ : OChartTransitionDomain ch₂ ch₃)
    (nb₁ : OChartMonotoneNbhd ch₁ ch₂ x₁) (nb₂ : OChartMonotoneNbhd ch₂ ch₃ x₂)
    (x₀ : ChartInterval nb₁.lo nb₁.hi)
    (hx : oChartTransitionOnInterval ch₁ ch₂ nb₁.subset nb₁.dom x₀ ∈
      Set.Ioo nb₂.lo nb₂.hi) :
    ∃ a b : ℝ, a < b ∧ (x₀ : ℝ) ∈ Set.Ioo a b ∧
      ∀ u : ChartInterval nb₁.lo nb₁.hi, (u : ℝ) ∈ Set.Ioo a b →
        oChartTransitionOnInterval ch₁ ch₂ nb₁.subset nb₁.dom u ∈
          Set.Ioo nb₂.lo nb₂.hi :=
  exists_interval_preimage_piece
    (oChartTransitionOnInterval ch₁ ch₂ nb₁.subset nb₁.dom)
    (continuous_oChartTransitionOnInterval ch₁ ch₂ nb₁.subset nb₁.dom) x₀ hx

end LeanEval.KnotTheory.Quadrisecant
