import Mathlib
import Submission.OChartChainJunction
import Submission.OChartChain

open LeanEval.KnotTheory.Quadrisecant
open Filter
open scoped Real Topology unitInterval

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

/-!
# Milestone-2 (iv) step 6, brick (b) — the correct global slice over
component objects: countable chart-trace covers of the components

S102–S106 verified the local well-definedness/monotonicity layers of the
interval-chart machinery, and the S106 scoping note recorded that the
"transport one coordinate along an arbitrary S99 path" reading is not
well-posed (consecutive junction patches sit at coordinates of different
boundary classes).  This module starts the *correct* global route over the
proper component objects: the components of `O = trisecantSet r` are open
(S95), path-connected (S96), locally interval-charted (S97), and each is a
subspace of the second-countable band `OpenMobius`, hence hereditarily
Lindelöf.

**First component lemma `component_countable_chart_cover`**: every
connected component `C = connectedComponent c₀` of `O` lies in the union
of the traces of the interval charts centred at countably many classes of
`C` itself — the trace sets `{y : OSub r | (y : OpenMobius) ∈
(oChartAtClass h hqf hgp x).W}` (open, each class in its own trace by the
chart `c₀_mem` field) cover `C`, and hereditarily Lindelöf
(`HereditarilyLindelofSpace.isLindelof` + `eq_open_union_nat` on the
second-countable `OSub r`) gives a countable subcover enumerated as
`cl : ℕ → OSub r` with every `cl n` in `C`.

This is the countable-exhaustion input of the arc/circle classification
route: with countably many chart traces covering a component, the next
slices (stated in the ROADMAP session log S107) build the exhaustion/
ordering of the component and conclude "compact component ⇒ circle;
non-compact ⇒ open interval", then brick (c).

Everything here is elementary and verified (no axioms, no `sorry`).
-/

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

/-- **Every component of `O` is covered by countably many interval-chart
traces.**  A connected component `C = connectedComponent c₀` of the
trisecant set lies in the union of the traces of the interval charts
(`OSub1Chart`, S97) centred at countably many classes of `C` itself: the
trace sets `U_x = {y : OSub r | (y : OpenMobius) ∈ (oChartAtClass h hqf hgp
x).W}` (open, each contains its own class by the chart `c₀_mem` field)
cover `C`, and the component (a subspace of the second-countable band
`OpenMobius`) is hereditarily Lindelöf, so the cover has a countable
subcover (`HereditarilyLindelofSpace.isLindelof` +
`IsLindelof.elim_countable_subcover`/`eq_open_union_nat`).  This is the
first global component lemma of the classification route: a countable
exhaustion of the component by chart traces. -/
theorem component_countable_chart_cover {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r) (c₀ : OSub r) :
    ∃ cl : ℕ → OSub r,
      (∀ n : ℕ, cl n ∈ connectedComponent c₀) ∧
      (∀ y : OSub r, y ∈ connectedComponent c₀ →
        ∃ n : ℕ, (y : OpenMobius) ∈ (oChartAtClass h hqf hgp (cl n)).W) := by
  classical
  let ι : Type := {x : OSub r // x ∈ connectedComponent c₀}
  have hι : Nonempty ι := ⟨⟨c₀, mem_connectedComponent⟩⟩
  let U : ι → Set (OSub r) := fun x => {y : OSub r | (y : OpenMobius) ∈ (oChartAtClass h hqf hgp x.1).W}
  have hUo : ∀ i : ι, IsOpen (U i) := by
    intro i
    dsimp [U]
    exact ((oChartAtClass h hqf hgp i.1).W_open).preimage continuous_subtype_val
  have hcov : (connectedComponent c₀ : Set (OSub r)) ⊆ ⋃ i : ι, U i := by
    intro y hy
    exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, (oChartAtClass h hqf hgp y).c₀_mem⟩
  rcases eq_open_union_nat (U := U) hUo with ⟨k, hk⟩
  let cl : ℕ → OSub r := fun n => (k n).1
  refine ⟨cl, ?_, ?_⟩
  · intro n
    dsimp [cl]
    exact (k n).2
  · intro y hy
    have hycov : y ∈ ⋃ i : ι, U i := by
      exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, (oChartAtClass h hqf hgp y).c₀_mem⟩
    rw [← hk] at hycov
    rcases Set.mem_iUnion.mp hycov with ⟨n, hyn⟩
    refine ⟨n, ?_⟩
    simpa [cl, U] using hyn

end LeanEval.KnotTheory.Quadrisecant
