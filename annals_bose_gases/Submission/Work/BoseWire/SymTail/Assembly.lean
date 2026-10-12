import ChallengeDeps
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.BoseSym.Bridge.tendsto_symBoxEnergyTrunc
import Submission.Work.BoseWire.SymTail.SphereInf
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseWire.SymTail.Assembly` — the bosonic reduction, clash-free

The assembly of the `BoseSym` chapter (`Submission/Work/BoseSym/Main.lean`), reproduced in this
namespace because `Work.BoseSym.Main` cannot be imported together with the `LHYBoxB` chain (see
the header of `Submission/Work/BoseWire/SymTail/Basic.lean` for the duplicate-name obstruction).

Delivered here (all names local to `Work.BoseWire.SymTail`):

* `symBoxEnergyTrunc_le_boxEnergyTrunc` — the bosonic reduction at each truncation level `M`,
  from the symmetric minimiser (`SphereInf.symBoxEnergyTrunc_le_sphereInf`);
* `symBoxE_le_boxE` — the same with the truncation removed, for an even potential;
* `symBoxEnergy_le_boxEnergy_of_radial` — the radial form, which is what the corpus
  `Work.BoseTop.symBoxReduction` names.

The proofs are those of the `BoseSym` chapter; only the a.e.-measurability input is taken from
this directory's own copy (`SymTail.aemeasurable_Vtrunc`) instead of
`Work.BoseSym.Form.aemeasurable_Vtrunc` (which drags in the incompatible
`Work.BoseSym.Form.qmp_pair_pi`).
-/

namespace Work.BoseWire.SymTail

open MeasureTheory Filter
open BoseGases
open Submission.BoseGases
open scoped Topology Real ContDiff ENNReal
open Work.BoseSym

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The truncated box energy dominates the symmetric one, at every truncation level. -/
theorem symBoxEnergyTrunc_le_boxEnergyTrunc {N : ℕ} {L : ℝ} (hL : 0 < L) {v : E3 → ℝ}
    (hv : 0 ≤ v) {M : ℝ} (hM : 0 ≤ M) (hv1 : IsL1 v)
    (heven : ∀ y : E3, v (-y) = v y) :
    symBoxEnergyTrunc N L v M ≤ boxEnergyTrunc N L v M := by
  rw [Bridge.boxEnergyTrunc_eq_iInf hL (C := M) (fun x => by
        rw [abs_of_nonneg (Vtrunc_nonneg hv hM x)]
        exact Vtrunc_le N v M x)
      (Work.BoseWire.SymTail.aemeasurable_Vtrunc (hv1.aestronglyMeasurable.aemeasurable) M)]
  exact symBoxEnergyTrunc_le_sphereInf hL hv hM hv1 heven

/-- The bosonic reduction at the level of the box energies, for an even potential. -/
theorem symBoxE_le_boxE {N : ℕ} {L : ℝ} (hL : 0 < L) {v : E3 → ℝ} (hv : 0 ≤ v)
    (hv1 : IsL1 v) (heven : ∀ y : E3, v (-y) = v y) : symBoxE N L v ≤ boxE N L v := by
  have hV : IntOnBox N L (Vpot N v) := Bridge.integrableOn_Vpot_box hv1
  have hbox : Filter.Tendsto (fun M : ℕ => boxEnergyTrunc N L v M) Filter.atTop
      (nhds (boxE N L v)) := Bridge.tendsto_boxEnergyTrunc hL hv hV
  have hsym : Filter.Tendsto (fun M : ℕ => symBoxEnergyTrunc N L v M) Filter.atTop
      (nhds (symBoxE N L v)) := Bridge.tendsto_symBoxEnergyTrunc hL hv hV
  refine le_of_tendsto_of_tendsto hsym hbox (Eventually.of_forall fun M => ?_)
  exact symBoxEnergyTrunc_le_boxEnergyTrunc hL hv (Nat.cast_nonneg M) hv1 heven

/-- **The bosonic reduction for a radial potential**: the infimum over all trial functions is at
least the bosonic infimum.  This is the statement the wire consumes (via
`Work.BoseWire.symBoxReduction_of_radial`). -/
theorem symBoxEnergy_le_boxEnergy_of_radial {N : ℕ} {L : ℝ} {v : E3 → ℝ} (hL : 0 < L)
    (hv : 0 ≤ v) (hv1 : IsL1 v) (hrad : IsRadial v) : symBoxE N L v ≤ boxE N L v :=
  symBoxE_le_boxE hL hv hv1 fun y => (hrad y (-y) (norm_neg y).symm).symm

end

end Work.BoseWire.SymTail
