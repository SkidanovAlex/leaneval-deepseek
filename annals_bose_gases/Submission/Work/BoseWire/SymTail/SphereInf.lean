import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseSym.Main.eventually_symTest_ne_zero
import Submission.Work.BoseSym.Main.symBoxEnergyTrunc_le_symTest_quot
import Submission.Work.BoseSym.Main.tendsto_symTest_quot
import Submission.Work.BoseSym.Minimiser.symMinimiser_exists
import Submission.Work.BoseSym.Perm.Vpot_tauPerm
import Submission.Work.BoseWire.SymTail.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# BoseSym — the bosonic reduction at the level of the truncated box energy

For `L > 0`, a nonnegative interaction `v` and `M ≥ 0`, the symmetric (bosonic)
truncated box energy is at most the infimum of the Dirichlet form of the
truncated potential `Vtrunc N v M` over the unit sphere of the Dirichlet energy
space `Hsub N L`.

The proof combines three ingredients:

* the Perron–Frobenius (symmetrisation) input `symMinimiser_exists`, which
  produces a *permutation invariant* unit minimiser `p` of the Dirichlet form;
* the density of the graph points of the test functions in `Hsub N L`
  (`exists_graphPoint_close`), which approximates `p` by `graphPoint N L (F n)`;
* the fact that the symmetrisation commutes with the graph point
  (`symAvgAmb_graphPoint`), so that the symmetrised approximants
  `graphPoint N L (symTest N L (F n)) = symAvgAmb N (graphPoint N L (F n))`
  converge back to `p` (because `symAvgAmb N p = p` for invariant `p`).

Each symmetrised approximant is a legitimate symmetric box trial state, so its
Rayleigh quotient bounds `symBoxEnergyTrunc` from above, and those quotients
converge to `dirForm (Vtrunc N v M) p`, the value of the infimum.
-/

namespace Work.BoseWire.SymTail

open MeasureTheory Filter
open Work.BoseSym
open Work.BoseSym.Main
open BoseGases
open Submission.BoseGases
open scoped Topology Real ContDiff ENNReal

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem symBoxEnergyTrunc_le_sphereInf {N : ℕ} {L : ℝ} (hL : 0 < L) {v : E3 → ℝ} (hv : 0 ≤ v)
    {M : ℝ} (hM : 0 ≤ M) (hv1 : IsL1 v) (heven : ∀ y : E3, v (-y) = v y) :
    symBoxEnergyTrunc N L v M ≤
      ⨅ p : {p : Hsub N L // l2Sq (p : Amb N) = 1}, dirForm (Vtrunc N v M) (p : Amb N) := by
  -- the truncated potential is a.e. nonnegative, bounded by `M`, a.e. measurable
  -- and permutation invariant
  have hnn : AENonneg N (Vtrunc N v M) :=
    Filter.Eventually.of_forall fun x => Vtrunc_nonneg hv hM x
  have hbb : BddBy N (Vtrunc N v M) M := fun x =>
    abs_le.2 ⟨by linarith [Vtrunc_nonneg hv hM x], Vtrunc_le N v M x⟩
  have hme : AEMeas N (Vtrunc N v M) :=
    Work.BoseWire.SymTail.aemeasurable_Vtrunc (hv1.aestronglyMeasurable.aemeasurable) M
  have hperm : ∀ σ x, Vtrunc N v M (tauPerm N σ x) = Vtrunc N v M x := fun σ x => by
    rw [Vtrunc, Vtrunc, Work.BoseSym.Perm.Vpot_tauPerm heven σ x]
  -- the Perron--Frobenius input: an invariant unit minimiser of the form
  obtain ⟨p, hpsym, hpmin⟩ :=
    Work.BoseSym.Minimiser.symMinimiser_exists (N := N) L hL (W := Vtrunc N v M) M hperm hbb hnn hme
  -- it suffices to bound `symBoxEnergyTrunc` by the form of that minimiser
  have key : symBoxEnergyTrunc N L v M ≤ dirForm (Vtrunc N v M) (p : Amb N) := by
    -- approximating test functions
    let F : ℕ → testSub N L := fun n =>
      Classical.choose (Work.BoseSym.Basic.exists_graphPoint_close (p : Hsub N L)
        (ε := 1 / ((n : ℝ) + 1)) (by positivity))
    have hFspec : ∀ n : ℕ,
        hSq (graphPoint N L (F n) - (p : Amb N)) ≤ 1 / ((n : ℝ) + 1) := fun n =>
      Classical.choose_spec (Work.BoseSym.Basic.exists_graphPoint_close (p : Hsub N L)
        (ε := 1 / ((n : ℝ) + 1)) (by positivity))
    have hbound : ∀ n : ℕ,
        ‖graphPoint N L (F n) - (p : Amb N)‖ ≤ Real.sqrt (1 / ((n : ℝ) + 1)) := by
      intro n
      calc ‖graphPoint N L (F n) - (p : Amb N)‖
          = Real.sqrt (‖graphPoint N L (F n) - (p : Amb N)‖ ^ 2) :=
            (Real.sqrt_sq (norm_nonneg _)).symm
        _ ≤ Real.sqrt (hSq (graphPoint N L (F n) - (p : Amb N))) :=
            Real.sqrt_le_sqrt (Work.BoseSym.Abs.norm_sq_le_hSq _)
        _ ≤ Real.sqrt (1 / ((n : ℝ) + 1)) := Real.sqrt_le_sqrt (hFspec n)
    have hlim : Tendsto (fun n => graphPoint N L (F n)) atTop (nhds (p : Amb N)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun n => norm_nonneg _) hbound ?_
      have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (nhds 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h1 := (Real.continuous_sqrt.tendsto 0).comp h0
      simpa [Function.comp_def] using h1
    -- the symmetrised quotients converge to the value of the infimum
    have hy : Tendsto (fun n =>
        dirForm (Vtrunc N v M) (graphPoint N L (symTest N L (F n)))
          / l2Sq (graphPoint N L (symTest N L (F n)))) atTop
        (nhds (dirForm (Vtrunc N v M) (p : Amb N))) :=
      tendsto_symTest_quot hbb hme p.2 hpsym hlim
    -- every symmetrised approximant is a symmetric trial state
    have hev : ∀ᶠ n in atTop, symBoxEnergyTrunc N L v M ≤
        dirForm (Vtrunc N v M) (graphPoint N L (symTest N L (F n)))
          / l2Sq (graphPoint N L (symTest N L (F n))) := by
      refine (eventually_symTest_ne_zero p.2 hpsym hlim).mono fun n hn => ?_
      exact symBoxEnergyTrunc_le_symTest_quot hv hM (F n)
        (ne_of_gt (Work.BoseSym.Bridge.pos_l2Sq_graphPoint (symTest N L (F n)) hn))
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hy hev
  exact key.trans_eq hpmin

end

end Work.BoseWire.SymTail
