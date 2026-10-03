import Mathlib
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.GreenSetupReg
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.globalizedBarrierAux
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.globalizedBarrierBuild

/-!
# The globalized barrier: from a local barrier at a frontier point to a global one

Let `Ω` be an open subset of a Riemann surface `X` and `p ∈ frontier Ω`.  Suppose `p` carries a
*local barrier*: a function `u` that is superharmonic on `Ω ∩ V` for some neighbourhood `V ∋ p`,
strictly positive on `Ω ∩ V`, continuous on `V`, with `u p = 0`.

The theorem `globalizedBarrier_dev` produces a *global* barrier: a function `β` superharmonic on
all of `Ω`, nonnegative, with `β p = 0`, continuous on `Ω`, strictly positive on `Ω \ {p}`, and
tending to `0` at `p` along `Ω`.

This is the classical statement that a local barrier at a boundary point implies the existence of a
global barrier there (equivalently: that a local barrier forces the point to be Dirichlet-regular),
in the form used by the region-Perrron (limsup envelope) comparison
`Submission.limEnvelope_le_smul_of_barrier`.

## Layout

The elementary superharmonic tooling used by the construction lives in
`Submission.Work.SimplyConnected.ABS.globalizedBarrierAux`:

* `Work.SimplyConnected.ABS.superharmonicOnX_const_dev` — constants are superharmonic;
* `Work.SimplyConnected.ABS.SuperharmonicOnX.inf_const_dev` — **the clamp lemma**: the pointwise
  minimum of a superharmonic function with a constant is superharmonic;
* `Work.SimplyConnected.ABS.superharmonicOnX_of_isOpen_cover_dev` — superharmonicity is local.

The globalization itself is the classical Bouligand argument, proved in
`Submission.Work.SimplyConnected.ABS.globalizedBarrierBuild`: writing `b := -u` one first builds,
for every neighbourhood `N'` of `p` and every `ε > 0`, a *subharmonic* `b_ε < 0` on `Ω` with
`liminf_{x→p} b_ε ≥ -ε` and `b_ε ≤ -1` off `N'` (Bouligand's lemma), using the Poisson extension of
a bounded measurable datum on a chart circle (`Submission.Work.SimplyConnected.ABS.bouligandDatum`);
coherence over shrinking chart discs gives a single subharmonic `b < 0` on `Ω` with `b → 0` at `p`,
and then `β := min (-b) 1` is the required barrier, with `β p := 0` prescribed by hand.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Work.SimplyConnected.ABS

/-- **The globalized barrier.**  A local barrier at a frontier point `p` of `Ω` yields a global
barrier on `Ω`: a nonnegative superharmonic function, continuous on `Ω`, vanishing at `p`, strictly
positive on `Ω \ {p}`, and tending to `0` at `p` along `Ω`. -/
theorem globalizedBarrier_dev {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {Ω : Set X} (hΩo : IsOpen Ω) {p : X} (hp : p ∈ frontier Ω)
    (hb : ∃ (u : X → ℝ) (V : Set X), IsOpen V ∧ p ∈ V ∧
      Submission.SuperharmonicOnX u (Ω ∩ V) ∧ (∀ x ∈ Ω ∩ V, 0 < u x) ∧
      ContinuousOn u V ∧ u p = 0) :
    ∃ β : X → ℝ, Submission.SuperharmonicOnX β Ω ∧ (∀ x ∈ Ω, 0 ≤ β x) ∧ β p = 0 ∧
      ContinuousOn β Ω ∧ (∀ x ∈ Ω, x ≠ p → 0 < β x) ∧
      (∀ ε : ℝ, 0 < ε → ∃ V : Set X, V ∈ nhds p ∧ ∀ x ∈ Ω ∩ V, β x < ε) :=
  Work.SimplyConnected.ABS.GBBuild.globalizedBarrier hΩo hp hb

end Work.SimplyConnected.ABS
