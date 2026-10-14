import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS.StrongEps.Weights
import Submission.Work.FTS.StrongEps.mixed_Jeps
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6
import Submission.Work.FTS.StrongPersist.L3Aux.acoef_gamCoef_slots_le
import Submission.Work.FTS.StrongPersist.L3Rhs.CoupledVf
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.L3Rhs.L3RhsNstarBlock
import Submission.Work.FTS.StrongPersist.L3Rhs.N0gAuxDefs
import Submission.Work.FTS.StrongPersist.L3Rhs.N3ssPriced
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.SmainHon
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.leibnizRem6
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.Slots.v2_L12DzIterTendsto
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_RegExport.RXT.starVop
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.StrongEps.DiffAux.HkIntegrandSub =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.DiffAux

open Work.FTS.StrongEps (Quad zShift thShift Jker Jeps sin_two_pos)

set_option autoImplicit false
set_option maxHeartbeats 4000000

variable {ρ : ℝ × ℝ → ℝ} {ε c δ : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ}

/-! ## The level-`k` integrand of the mollifier difference -/

theorem HkIntegrand_sub_le {α : ℝ} (hα : α ∈ Set.Ioc 0 1) (hρ : IsMollKernel ρ) (hε : 0 < ε)
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad) {c : ℝ} (hc : 0 ≤ c)
    (hWη : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → ∀ q : ℝ × ℝ,
      wE z θ ≤ Real.exp (c * (|q.1| + |q.2|)) * wE (zShift z q.1) (thShift θ q.2))
    (hWγ : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → ∀ q : ℝ × ℝ,
      Work.Spaces.Wt α z θ ≤ Real.exp (c * (|q.1| + |q.2|)) * Work.Spaces.Wt α (zShift z q.1)
        (thShift θ q.2))
    {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    ENNReal.ofReal (Work.Spaces.HkIntegrand α k (fun z θ => Jeps ρ ε f z θ - f z θ) z θ)
      ≤ ENNReal.ofReal (2 * ε ^ 2 * Real.exp (4 * c * ε))
        * lintegral μY (fun y => ENNReal.ofReal (Jker ρ ε y.1)
            * ENNReal.ofReal (shadow α k f (zShift z (y.2 * y.1.1))
                (thShift θ (y.2 * y.1.2)))) := by
  by_cases hq : 0 < z ∧ θ ∈ Set.Ioo 0 (π / 2)
  · obtain ⟨hzpos, hθQ⟩ := hq
    have hZslot : ∀ i ∈ Finset.range (k + 1),
        ENNReal.ofReal ((Work.Spaces.DzIter i (fun z θ => Jeps ρ ε f z θ - f z θ) z θ
            * wE z θ) ^ 2)
          ≤ ENNReal.ofReal (2 * ε ^ 2 * Real.exp (4 * c * ε))
            * lintegral μY (fun y => ENNReal.ofReal (Jker ρ ε y.1)
                * ENNReal.ofReal (bracket (Work.Spaces.DzIter i f) wE z θ y.1 y.2)) := by
      intro i _
      have hslot := DzIter_sub_Jeps ρ hρ hε hf hzpos hθQ i
      have hsmQ : Work.FTS.StrongEps.SmQ (Work.Spaces.DzIter i f) :=
        (Work.FTS.StrongEps.smQ_of_forall_nat hf).DzIter i
      have hforall : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.Spaces.DzIter i f)) Quad :=
        fun n => contDiffOn_infty.mp hsmQ n
      have hDzc : ContinuousOn (fun q : ℝ × ℝ =>
          Work.Spaces.Dz (Work.Spaces.DzIter i f) q.1 q.2) Quad :=
        continuousOn_DzIter (f := Work.Spaces.DzIter i f) hforall 1
      have hDthc : ContinuousOn (fun q : ℝ × ℝ =>
          Work.Spaces.Dth (Work.Spaces.DzIter i f) q.1 q.2) Quad :=
        (continuousOn_mixed hf i 1).congr fun q hq' =>
          (Work.FTS.EllipticEst.ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen
            isOpen_Quad hf i 1 hq')
      have hpt := slot_ofReal_le (ρ := ρ) (ε := ε) (c := c) (g := Work.Spaces.DzIter i f)
        (W := wE) hρ hε hc hforall continuousOn_wE hDzc hDthc hzpos hθQ
        (wE_nonneg hθQ) (hWη z θ hzpos hθQ)
      have hgoal : ENNReal.ofReal ((Work.Spaces.DzIter i
            (fun z θ => Jeps ρ ε f z θ - f z θ) z θ * wE z θ) ^ 2)
          = ENNReal.ofReal ((wE z θ * (Jeps ρ ε (Work.Spaces.DzIter i f) z θ
              - Work.Spaces.DzIter i f z θ)) ^ 2) := by
        rw [hslot]
        congr 1
        ring
      rw [hgoal]
      exact hpt
    have hMslot : ∀ q ∈ slots k,
        ENNReal.ofReal ((Work.Spaces.mixed q.2 q.1
            (fun z θ => Jeps ρ ε f z θ - f z θ) z θ * Work.Spaces.Wt α z θ) ^ 2)
          ≤ ENNReal.ofReal (2 * ε ^ 2 * Real.exp (4 * c * ε))
            * lintegral μY (fun y => ENNReal.ofReal (Jker ρ ε y.1)
                * ENNReal.ofReal (bracket (Work.Spaces.mixed q.2 q.1 f) (Work.Spaces.Wt α)
                    z θ y.1 y.2)) := by
      intro q _
      have hslot := mixed_sub_Jeps ρ hρ hε hf hzpos hθQ q.2 q.1
      have hsmQ : Work.FTS.StrongEps.SmQ (Work.Spaces.mixed q.2 q.1 f) :=
        ((Work.FTS.StrongEps.smQ_of_forall_nat hf).DthIter q.1).DzIter q.2
      have hforall : ∀ n : ℕ,
          ContDiffOn ℝ n (Function.uncurry (Work.Spaces.mixed q.2 q.1 f)) Quad :=
        fun n => contDiffOn_infty.mp hsmQ n
      have hDzc : ContinuousOn (fun q' : ℝ × ℝ =>
          Work.Spaces.Dz (Work.Spaces.mixed q.2 q.1 f) q'.1 q'.2) Quad :=
        (continuousOn_mixed hf (q.2 + 1) q.1).congr fun q' hq' => rfl
      have hDthc : ContinuousOn (fun q' : ℝ × ℝ =>
          Work.Spaces.Dth (Work.Spaces.mixed q.2 q.1 f) q'.1 q'.2) Quad :=
        (continuousOn_mixed hf q.2 (q.1 + 1)).congr fun q' hq' =>
          (Work.FTS.EllipticEst.ThetaU.OpenSliceAux.Dth_DzIter_eqOn_of_smooth
            isOpen_Quad ((Work.FTS.StrongEps.smQ_of_forall_nat hf).DthIter q.1) q.2 hq')
      have hpt := slot_ofReal_le (ρ := ρ) (ε := ε) (c := c) (g := Work.Spaces.mixed q.2 q.1 f)
        (W := Work.Spaces.Wt α) hρ hε hc hforall continuousOn_Wt hDzc hDthc hzpos hθQ
        (Wt_nonneg ⟨le_of_lt hθQ.1, le_of_lt hθQ.2⟩) (hWγ z θ hzpos hθQ)
      have hgoal : ENNReal.ofReal ((Work.Spaces.mixed q.2 q.1
            (fun z θ => Jeps ρ ε f z θ - f z θ) z θ * Work.Spaces.Wt α z θ) ^ 2)
          = ENNReal.ofReal ((Work.Spaces.Wt α z θ * (Jeps ρ ε (Work.Spaces.mixed q.2 q.1 f) z θ
              - Work.Spaces.mixed q.2 q.1 f z θ)) ^ 2) := by
        rw [hslot]
        congr 1
        ring
      rw [hgoal]
      exact hpt
    have hZ := Finset.sum_le_sum hZslot
    have hM := Finset.sum_le_sum hMslot
    have hZ2 : (∑ i ∈ Finset.range (k + 1),
          ENNReal.ofReal ((Work.Spaces.DzIter i (fun z θ => Jeps ρ ε f z θ - f z θ) z θ
            * wE z θ) ^ 2))
        ≤ ENNReal.ofReal (2 * ε ^ 2 * Real.exp (4 * c * ε))
          * (∑ i ∈ Finset.range (k + 1), lintegral μY (fun y => ENNReal.ofReal (Jker ρ ε y.1)
              * ENNReal.ofReal (bracket (Work.Spaces.DzIter i f) wE z θ y.1 y.2))) :=
      hZ.trans_eq (Finset.mul_sum _ _ _).symm
    have hM2 : (∑ q ∈ slots k,
          ENNReal.ofReal ((Work.Spaces.mixed q.2 q.1 (fun z θ => Jeps ρ ε f z θ - f z θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2))
        ≤ ENNReal.ofReal (2 * ε ^ 2 * Real.exp (4 * c * ε))
          * (∑ q ∈ slots k, lintegral μY (fun y => ENNReal.ofReal (Jker ρ ε y.1)
              * ENNReal.ofReal (bracket (Work.Spaces.mixed q.2 q.1 f) (Work.Spaces.Wt α)
                  z θ y.1 y.2))) :=
      hM.trans_eq (Finset.mul_sum _ _ _).symm
    have hfinal : ENNReal.ofReal (2 * ε ^ 2 * Real.exp (4 * c * ε))
          * ((∑ i ∈ Finset.range (k + 1), lintegral μY (fun y => ENNReal.ofReal (Jker ρ ε y.1)
              * ENNReal.ofReal (bracket (Work.Spaces.DzIter i f) wE z θ y.1 y.2)))
            + (∑ q ∈ slots k, lintegral μY (fun y => ENNReal.ofReal (Jker ρ ε y.1)
              * ENNReal.ofReal (bracket (Work.Spaces.mixed q.2 q.1 f) (Work.Spaces.Wt α)
                  z θ y.1 y.2))))
        ≤ ENNReal.ofReal (2 * ε ^ 2 * Real.exp (4 * c * ε))
          * lintegral μY (fun y => ENNReal.ofReal (Jker ρ ε y.1)
              * ENNReal.ofReal (shadow α k f (zShift z (y.2 * y.1.1))
                  (thShift θ (y.2 * y.1.2)))) := by
      gcongr
      calc (∑ i ∈ Finset.range (k + 1), lintegral μY (fun y => ENNReal.ofReal (Jker ρ ε y.1)
              * ENNReal.ofReal (bracket (Work.Spaces.DzIter i f) wE z θ y.1 y.2)))
            + (∑ q ∈ slots k, lintegral μY (fun y => ENNReal.ofReal (Jker ρ ε y.1)
              * ENNReal.ofReal (bracket (Work.Spaces.mixed q.2 q.1 f) (Work.Spaces.Wt α)
                  z θ y.1 y.2)))
          ≤ lintegral μY (fun y => ∑ i ∈ Finset.range (k + 1), ENNReal.ofReal (Jker ρ ε y.1)
              * ENNReal.ofReal (bracket (Work.Spaces.DzIter i f) wE z θ y.1 y.2))
            + lintegral μY (fun y => ∑ q ∈ slots k, ENNReal.ofReal (Jker ρ ε y.1)
              * ENNReal.ofReal (bracket (Work.Spaces.mixed q.2 q.1 f) (Work.Spaces.Wt α)
                  z θ y.1 y.2)) :=
            add_le_add (lintegral_finsetSum_le μY _ _) (lintegral_finsetSum_le μY _ _)
        _ ≤ lintegral μY (fun y =>
              (∑ i ∈ Finset.range (k + 1), ENNReal.ofReal (Jker ρ ε y.1)
                * ENNReal.ofReal (bracket (Work.Spaces.DzIter i f) wE z θ y.1 y.2))
              + ∑ q ∈ slots k, ENNReal.ofReal (Jker ρ ε y.1)
                * ENNReal.ofReal (bracket (Work.Spaces.mixed q.2 q.1 f) (Work.Spaces.Wt α)
                    z θ y.1 y.2)) :=
            MeasureTheory.le_lintegral_add _ _
        _ ≤ lintegral μY (fun y => ENNReal.ofReal (Jker ρ ε y.1)
              * ENNReal.ofReal (shadow α k f (zShift z (y.2 * y.1.1))
                  (thShift θ (y.2 * y.1.2)))) := by
            refine lintegral_mono fun y => ?_
            have hbrack := sum_bracket_le_shadow (α := α) (k := k) hα hf y (f := f) (z := z)
              (θ := θ) hzpos hθQ
            have hnn1 : ∀ i ∈ Finset.range (k + 1),
                0 ≤ bracket (Work.Spaces.DzIter i f) wE z θ y.1 y.2 :=
              fun i _ => bracket_nonneg _ _ _ _ _ _
            have hnn2 : ∀ q ∈ slots k,
                0 ≤ bracket (Work.Spaces.mixed q.2 q.1 f) (Work.Spaces.Wt α) z θ y.1 y.2 :=
              fun q _ => bracket_nonneg _ _ _ _ _ _
            calc (∑ i ∈ Finset.range (k + 1), ENNReal.ofReal (Jker ρ ε y.1)
                  * ENNReal.ofReal (bracket (Work.Spaces.DzIter i f) wE z θ y.1 y.2))
                + ∑ q ∈ slots k, ENNReal.ofReal (Jker ρ ε y.1)
                  * ENNReal.ofReal (bracket (Work.Spaces.mixed q.2 q.1 f) (Work.Spaces.Wt α)
                      z θ y.1 y.2)
                = ENNReal.ofReal (Jker ρ ε y.1)
                  * (ENNReal.ofReal (∑ i ∈ Finset.range (k + 1),
                        bracket (Work.Spaces.DzIter i f) wE z θ y.1 y.2)
                    + ENNReal.ofReal (∑ q ∈ slots k,
                        bracket (Work.Spaces.mixed q.2 q.1 f) (Work.Spaces.Wt α)
                          z θ y.1 y.2)) := by
                  rw [← Finset.mul_sum, ← Finset.mul_sum,
                    ← ENNReal.ofReal_sum_of_nonneg hnn1, ← ENNReal.ofReal_sum_of_nonneg hnn2]
                  ring
              _ = ENNReal.ofReal (Jker ρ ε y.1)
                  * ENNReal.ofReal ((∑ i ∈ Finset.range (k + 1),
                        bracket (Work.Spaces.DzIter i f) wE z θ y.1 y.2)
                    + ∑ q ∈ slots k,
                        bracket (Work.Spaces.mixed q.2 q.1 f) (Work.Spaces.Wt α)
                          z θ y.1 y.2) := by
                  rw [ENNReal.ofReal_add (Finset.sum_nonneg hnn1) (Finset.sum_nonneg hnn2)]
              _ ≤ ENNReal.ofReal (Jker ρ ε y.1)
                  * ENNReal.ofReal (shadow α k f (zShift z (y.2 * y.1.1))
                      (thShift θ (y.2 * y.1.2))) := by
                  gcongr
    calc ENNReal.ofReal (Work.Spaces.HkIntegrand α k
            (fun z θ => Jeps ρ ε f z θ - f z θ) z θ)
        = (∑ i ∈ Finset.range (k + 1),
              ENNReal.ofReal ((Work.Spaces.DzIter i
                (fun z θ => Jeps ρ ε f z θ - f z θ) z θ * wE z θ) ^ 2))
            + (∑ q ∈ slots k, ENNReal.ofReal ((Work.Spaces.mixed q.2 q.1
                (fun z θ => Jeps ρ ε f z θ - f z θ) z θ * Work.Spaces.Wt α z θ) ^ 2)) := by
          rw [HkIntegrand_eq,
            ENNReal.ofReal_add (Finset.sum_nonneg fun i _ => sq_nonneg _)
              (Finset.sum_nonneg fun q _ => sq_nonneg _),
            ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _),
            ENNReal.ofReal_sum_of_nonneg (fun q _ => sq_nonneg _)]
      _ ≤ ENNReal.ofReal (2 * ε ^ 2 * Real.exp (4 * c * ε))
            * ((∑ i ∈ Finset.range (k + 1), lintegral μY (fun y =>
                ENNReal.ofReal (Jker ρ ε y.1)
                  * ENNReal.ofReal (bracket (Work.Spaces.DzIter i f) wE z θ y.1 y.2)))
              + (∑ q ∈ slots k, lintegral μY (fun y => ENNReal.ofReal (Jker ρ ε y.1)
                  * ENNReal.ofReal (bracket (Work.Spaces.mixed q.2 q.1 f) (Work.Spaces.Wt α)
                      z θ y.1 y.2)))) := by
            calc _ ≤ ENNReal.ofReal (2 * ε ^ 2 * Real.exp (4 * c * ε))
                    * (∑ i ∈ Finset.range (k + 1), lintegral μY (fun y =>
                        ENNReal.ofReal (Jker ρ ε y.1)
                          * ENNReal.ofReal (bracket (Work.Spaces.DzIter i f) wE z θ y.1 y.2)))
                  + ENNReal.ofReal (2 * ε ^ 2 * Real.exp (4 * c * ε))
                    * (∑ q ∈ slots k, lintegral μY (fun y => ENNReal.ofReal (Jker ρ ε y.1)
                      * ENNReal.ofReal (bracket (Work.Spaces.mixed q.2 q.1 f)
                          (Work.Spaces.Wt α) z θ y.1 y.2))) := add_le_add hZ2 hM2
              _ = _ := by ring
      _ ≤ _ := hfinal
  · rw [HkSqAux.HkIntegrand_boundary_zero hα hz hθ hq, ENNReal.ofReal_zero]
    exact bot_le


end Work.FTS.StrongEps.DiffAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.GlueParts.contDiffWithinAt_concat_halfslab =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.GlueParts

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam)
open Work.FTS.StrongGlobal (P3 concat uncurry3 concat_apply_of_le concat_apply_of_gt)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The main case `0 < t`

The proof is factored so that the two genuinely independent inputs are explicit hypotheses of the
private lemma `key`:

* `hjunc0` — the agreement of the two one-sided derivative fields at every junction point of the
  closed slab (the *boundary junction comparison*, proved in
  `GlueParts/junction_eq_fderivWithin.lean`);
* `hcontFact` — the continuity on the closed slab of the piecewise derivative field, as a function
  of that agreement (proved in `GlueParts/continuousOn_junctionStep.lean`).

This lets the body of `key` (the derivative field, the union over the two closed halves, and the
`C¹`-characterisation) be developed and checked independently of those two inputs. -/

/-- The main case (`0 < t`) of the boundary junction glue. -/
private theorem key {G H : Work.FTS.Galerkin.Fam} {t δ : ℝ}
    {R : Work.FTS.Galerkin.Fn} {q : Work.FTS.StrongGlobal.P3}
    (htpos : 0 < t) (hδ : 0 < δ)
    (hjunc0 : ∀ (p : Work.FTS.StrongGlobal.P3) (cG cH : Work.FTS.StrongGlobal.P3 →L[ℝ] ℝ),
        p ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 (t + δ) →
        p.2.2 = t →
        HasFDerivWithinAt
          (Work.FTS.StrongGlobal.uncurry3 (Work.FTS.StrongGlobal.concat G H t)) cG
          ((Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 (t + δ)) ∩
            {r : Work.FTS.StrongGlobal.P3 | r.2.2 ≤ t}) p →
        HasFDerivWithinAt
          (Work.FTS.StrongGlobal.uncurry3 (Work.FTS.StrongGlobal.concat G H t)) cH
          ((Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 (t + δ)) ∩
            {r : Work.FTS.StrongGlobal.P3 | t ≤ r.2.2}) p →
        cG = cH)
    (hcontFact : (∀ p ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 (t + δ), p.2.2 = t →
        fderivWithin ℝ (Work.FTS.StrongGlobal.uncurry3 G)
            (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 t) p =
        fderivWithin ℝ (Work.FTS.StrongGlobal.uncurry3 H)
            (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc t (t + δ)) p) →
      ContinuousOn (fun p : Work.FTS.StrongGlobal.P3 =>
          if p.2.2 ≤ t then
            fderivWithin ℝ (Work.FTS.StrongGlobal.uncurry3 G)
              (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 t) p
          else
            fderivWithin ℝ (Work.FTS.StrongGlobal.uncurry3 H)
              (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc t (t + δ)) p)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 (t + δ)))
    (hG : ContDiffOn ℝ 1 (Work.FTS.StrongGlobal.uncurry3 G)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 t))
    (hH : ContDiffOn ℝ 1 (Work.FTS.StrongGlobal.uncurry3 H)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc t (t + δ)))
    (hval : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → G z θ t = H z θ t)
    (hderG : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      HasDerivWithinAt (fun s => G z θ s) (R z θ) (Set.Icc 0 t) t)
    (hderH : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      HasDerivWithinAt (fun s => H z θ s) (R z θ) (Set.Icc t (t + δ)) t)
    (hq : q ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 (t + δ))
    (hqt : q.2.2 = t) :
    ContDiffWithinAt ℝ 1
      (Work.FTS.StrongGlobal.uncurry3 (Work.FTS.StrongGlobal.concat G H t))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 (t + δ)) q := by
  -- the two half-slabs
  let UG : Set P3 := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 t
  let UH : Set P3 := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc t (t + δ)
  let U : Set P3 := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 (t + δ)
  let Ψ : P3 → ℝ := uncurry3 (concat G H t)
  let f' : P3 → P3 →L[ℝ] ℝ := fun p : P3 =>
    if p.2.2 ≤ t then fderivWithin ℝ (uncurry3 G) UG p
    else fderivWithin ℝ (uncurry3 H) UH p
  -- differentiability of each piece on its own half-slab
  have hdG : ∀ p ∈ UG,
      HasFDerivWithinAt (uncurry3 G) (fderivWithin ℝ (uncurry3 G) UG p) UG p :=
    fun p hp => (hG.differentiableOn one_ne_zero p hp).hasFDerivWithinAt
  have hdH : ∀ p ∈ UH,
      HasFDerivWithinAt (uncurry3 H) (fderivWithin ℝ (uncurry3 H) UH p) UH p :=
    fun p hp => (hH.differentiableOn one_ne_zero p hp).hasFDerivWithinAt
  -- the agreement of the two one-sided derivative fields at the junction points of the slab
  have hjunc : ∀ p ∈ U, p.2.2 = t →
      fderivWithin ℝ (uncurry3 G) UG p = fderivWithin ℝ (uncurry3 H) UH p := by
    intro p hpU hp4
    have hpUG : p ∈ UG := ⟨hpU.1, hpU.2.1, ⟨hpU.2.2.1, le_of_eq hp4⟩⟩
    have hpUH : p ∈ UH := ⟨hpU.1, hpU.2.1, ⟨le_of_eq hp4.symm, hpU.2.2.2⟩⟩
    have hA : HasFDerivWithinAt Ψ (fderivWithin ℝ (uncurry3 G) UG p)
        (U ∩ {r : P3 | r.2.2 ≤ t}) p :=
      ((hdG p hpUG).mono (fun r hr => ⟨hr.1.1, hr.1.2.1, ⟨hr.1.2.2.1, hr.2⟩⟩)).congr
        (fun r hr => by
          show concat G H t r.1 r.2.1 r.2.2 = G r.1 r.2.1 r.2.2
          rw [concat_apply_of_le hr.2])
        (by
          show concat G H t p.1 p.2.1 p.2.2 = G p.1 p.2.1 p.2.2
          rw [concat_apply_of_le (le_of_eq hp4)])
    have hB : HasFDerivWithinAt Ψ (fderivWithin ℝ (uncurry3 H) UH p)
        (U ∩ {r : P3 | t ≤ r.2.2}) p :=
      ((hdH p hpUH).mono (fun r hr => ⟨hr.1.1, hr.1.2.1, ⟨hr.2, hr.1.2.2.2⟩⟩)).congr
        (fun r hr => by
          show concat G H t r.1 r.2.1 r.2.2 = H r.1 r.2.1 r.2.2
          have hr2 : t ≤ r.2.2 := by simpa using hr.2
          rcases lt_or_eq_of_le hr2 with hlt | hEq
          · rw [concat_apply_of_gt hlt]
          · rw [concat_apply_of_le (le_of_eq hEq.symm), hEq.symm]
            exact hval r.1 r.2.1 hr.1.1 hr.1.2.1.1 hr.1.2.1.2)
        (by
          show concat G H t p.1 p.2.1 p.2.2 = H p.1 p.2.1 p.2.2
          rw [concat_apply_of_le (le_of_eq hp4), hp4]
          exact hval p.1 p.2.1 hpU.1 hpU.2.1.1 hpU.2.1.2)
    exact hjunc0 p (fderivWithin ℝ (uncurry3 G) UG p) (fderivWithin ℝ (uncurry3 H) UH p)
      hpU hp4 hA hB
  -- continuity of the piecewise derivative field
  have hcont : ContinuousOn f' U := hcontFact hjunc
  -- the derivative of the concatenation at every point of the slab
  have hderiv : ∀ p ∈ U, HasFDerivWithinAt Ψ (f' p) U p := by
    intro p hpU
    rcases lt_trichotomy p.2.2 t with hlt | heq | hgt
    · -- strictly before the junction
      have hpUG : p ∈ UG := ⟨hpU.1, hpU.2.1, ⟨hpU.2.2.1, le_of_lt hlt⟩⟩
      have h1 : HasFDerivWithinAt Ψ (fderivWithin ℝ (uncurry3 G) UG p)
          (U ∩ {r : P3 | r.2.2 < t}) p :=
        ((hdG p hpUG).mono (fun r hr => ⟨hr.1.1, hr.1.2.1, ⟨hr.1.2.2.1, le_of_lt hr.2⟩⟩)).congr
          (fun r hr => by
            show concat G H t r.1 r.2.1 r.2.2 = G r.1 r.2.1 r.2.2
            rw [concat_apply_of_le (le_of_lt hr.2)])
          (by
            show concat G H t p.1 p.2.1 p.2.2 = G p.1 p.2.1 p.2.2
            rw [concat_apply_of_le (le_of_lt hlt)])
      have h2 : HasFDerivWithinAt Ψ (fderivWithin ℝ (uncurry3 G) UG p) U p :=
        h1.mono_of_mem_nhdsWithin (by
          rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
          exact ⟨{r : P3 | r.2.2 < t},
            (isOpen_lt (by fun_prop) continuous_const).mem_nhds hlt,
            fun r hr => ⟨hr.2, hr.1⟩⟩)
      have hfp : f' p = fderivWithin ℝ (uncurry3 G) UG p := by
        show (if p.2.2 ≤ t then fderivWithin ℝ (uncurry3 G) UG p
            else fderivWithin ℝ (uncurry3 H) UH p) = fderivWithin ℝ (uncurry3 G) UG p
        rw [if_pos (le_of_lt hlt)]
      rw [hfp]
      exact h2
    · -- on the junction hyperplane: glue the two one-sided derivatives
      have hpUG : p ∈ UG := ⟨hpU.1, hpU.2.1, ⟨hpU.2.2.1, le_of_eq heq⟩⟩
      have hpUH : p ∈ UH := ⟨hpU.1, hpU.2.1, ⟨le_of_eq heq.symm, hpU.2.2.2⟩⟩
      have h1 : HasFDerivWithinAt Ψ (fderivWithin ℝ (uncurry3 G) UG p)
          (U ∩ {r : P3 | r.2.2 ≤ t}) p :=
        ((hdG p hpUG).mono (fun r hr => ⟨hr.1.1, hr.1.2.1, ⟨hr.1.2.2.1, hr.2⟩⟩)).congr
          (fun r hr => by
            show concat G H t r.1 r.2.1 r.2.2 = G r.1 r.2.1 r.2.2
            rw [concat_apply_of_le hr.2])
          (by
            show concat G H t p.1 p.2.1 p.2.2 = G p.1 p.2.1 p.2.2
            rw [concat_apply_of_le (le_of_eq heq)])
      have h2 : HasFDerivWithinAt Ψ (fderivWithin ℝ (uncurry3 H) UH p)
          (U ∩ {r : P3 | t ≤ r.2.2}) p :=
        ((hdH p hpUH).mono (fun r hr => ⟨hr.1.1, hr.1.2.1, ⟨hr.2, hr.1.2.2.2⟩⟩)).congr
          (fun r hr => by
            show concat G H t r.1 r.2.1 r.2.2 = H r.1 r.2.1 r.2.2
            have hr2 : t ≤ r.2.2 := by simpa using hr.2
            rcases lt_or_eq_of_le hr2 with hlt | hEq
            · rw [concat_apply_of_gt hlt]
            · rw [concat_apply_of_le (le_of_eq hEq.symm), hEq.symm]
              exact hval r.1 r.2.1 hr.1.1 hr.1.2.1.1 hr.1.2.1.2)
          (by
            show concat G H t p.1 p.2.1 p.2.2 = H p.1 p.2.1 p.2.2
            rw [concat_apply_of_le (le_of_eq heq), heq]
            exact hval p.1 p.2.1 hpU.1 hpU.2.1.1 hpU.2.1.2)
      have h2' : HasFDerivWithinAt Ψ (fderivWithin ℝ (uncurry3 G) UG p)
          (U ∩ {r : P3 | t ≤ r.2.2}) p := by
        rw [hjunc p hpU heq]
        exact h2
      have hunion : HasFDerivWithinAt Ψ (fderivWithin ℝ (uncurry3 G) UG p)
          ((U ∩ {r : P3 | r.2.2 ≤ t}) ∪ (U ∩ {r : P3 | t ≤ r.2.2})) p :=
        h1.union h2'
      have hcov : (U ∩ {r : P3 | r.2.2 ≤ t}) ∪ (U ∩ {r : P3 | t ≤ r.2.2}) = U := by
        ext r
        constructor
        · rintro (hr | hr) <;> exact hr.1
        · intro hr
          rcases le_total r.2.2 t with h | h
          · exact Or.inl ⟨hr, h⟩
          · exact Or.inr ⟨hr, h⟩
      rw [hcov] at hunion
      have hfp : f' p = fderivWithin ℝ (uncurry3 G) UG p := by
        show (if p.2.2 ≤ t then fderivWithin ℝ (uncurry3 G) UG p
            else fderivWithin ℝ (uncurry3 H) UH p) = fderivWithin ℝ (uncurry3 G) UG p
        rw [if_pos (le_of_eq heq)]
      rw [hfp]
      exact hunion
    · -- strictly after the junction
      have hpUH : p ∈ UH := ⟨hpU.1, hpU.2.1, ⟨le_of_lt hgt, hpU.2.2.2⟩⟩
      have h1 : HasFDerivWithinAt Ψ (fderivWithin ℝ (uncurry3 H) UH p)
          (U ∩ {r : P3 | t < r.2.2}) p :=
        ((hdH p hpUH).mono (fun r hr => ⟨hr.1.1, hr.1.2.1, ⟨le_of_lt hr.2, hr.1.2.2.2⟩⟩)).congr
          (fun r hr => by
            show concat G H t r.1 r.2.1 r.2.2 = H r.1 r.2.1 r.2.2
            rw [concat_apply_of_gt hr.2])
          (by
            show concat G H t p.1 p.2.1 p.2.2 = H p.1 p.2.1 p.2.2
            rw [concat_apply_of_gt hgt])
      have h2 : HasFDerivWithinAt Ψ (fderivWithin ℝ (uncurry3 H) UH p) U p :=
        h1.mono_of_mem_nhdsWithin (by
          rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
          exact ⟨{r : P3 | t < r.2.2},
            (isOpen_lt continuous_const (by fun_prop)).mem_nhds hgt,
            fun r hr => ⟨hr.2, hr.1⟩⟩)
      have hfp : f' p = fderivWithin ℝ (uncurry3 H) UH p := by
        show (if p.2.2 ≤ t then fderivWithin ℝ (uncurry3 G) UG p
            else fderivWithin ℝ (uncurry3 H) UH p) = fderivWithin ℝ (uncurry3 H) UH p
        rw [if_neg (not_le.mpr hgt)]
      rw [hfp]
      exact h2
  -- the `C¹`-characterisation on the closed slab
  have hmain : ContDiffWithinAt ℝ ((0 : WithTop ℕ∞) + 1) (uncurry3 (concat G H t))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 (t + δ)) q := by
    rw [contDiffWithinAt_succ_iff_hasFDerivWithinAt (𝕜 := ℝ) (n := (0 : WithTop ℕ∞))
      (f := uncurry3 (concat G H t))
      (s := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 (t + δ))
      (x := q) (by norm_num)]
    refine ⟨U, ?_, ?_, f', hderiv, ?_⟩
    · rw [Set.insert_eq_of_mem hq]
      exact self_mem_nhdsWithin
    · intro h
      exact absurd h (by simp)
    · refine (contDiffWithinAt_zero hq).mpr ⟨U, self_mem_nhdsWithin, ?_⟩
      rwa [Set.inter_self]
  exact hmain

/-- **The junction glue for the joint `C¹`-regularity at a *boundary* junction.**

Two families `G`, `H` are jointly `C¹` on the two closed half-slabs `τ ≤ t` resp. `τ ≥ t` of fake
time (open quadrant in `(z,θ)`); they agree on the hyperplane `τ = t` over the open quadrant
(`hval`) and their fake-time one-sided derivatives there agree, both being `R` (`hderG`, `hderH`).
Then the concatenation `concat G H t` (`G` for `τ ≤ t`, `H` for `τ > t`) is jointly `C¹` *within*
the closed slab `τ ∈ [0, t+δ]` at every point `q` of that slab on the junction hyperplane `τ = t`.
This is the boundary-junction version of `Work.FTS.StrongGlobal.contDiffOn_concat_1` (which needs
the junction to be *interior* to both slabs, achieved there by one unit of slack).

Route.  Write `UG = Ioi 0 ×ˢ Ioo 0 (π/2) ×ˢ Icc 0 t`, `UH = Ioi 0 ×ˢ Ioo 0 (π/2) ×ˢ Icc t (t+δ)`,
`U = Ioi 0 ×ˢ Ioo 0 (π/2) ×ˢ Icc 0 (t+δ)`, `f = uncurry3 (concat G H t)`, and fix a junction point
`q = (x,y,t) ∈ U` (so `0 ≤ t`; the case `t = 0` is degenerate: then `f = H` on `U` by `hval`).
Use `contDiffWithinAt_succ_iff_hasFDerivWithinAt` with `n = 0` on the slab `U` itself (which is a
neighbourhood of `q` within `insert q U`).  On `U` take
`f' p = if p.2.2 ≤ t then fderivWithin ℝ (uncurry3 G) UG p else fderivWithin ℝ (uncurry3 H) UH p`.
(i) `HasFDerivWithinAt f (f' p) U p` for `p ∈ U`: off the junction this is the within-derivative of
the relevant piece on `U ∩ {τ < t}` (resp. `U ∩ {t < τ}`), upgraded to `U` by
`HasFDerivWithinAt.mono_of_mem_nhdsWithin`; at a junction point `p` glue the two one-sided
derivatives with `HasFDerivWithinAt.union` over `U ∩ {τ ≤ t}` and `U ∩ {τ ≥ t}`
(`Work.FTS.StrongEps.GlueParts.junction_eq_fderivWithin` supplies the agreement of the two
branches there).
(ii) `ContDiffWithinAt ℝ 0 f' U q` (`ContinuousOn f' U`), i.e. `f'` continuous on the slab: on
`U ∩ {τ ≤ t}` it is `fderivWithin ℝ (uncurry3 G) UG`, continuous on `UG` by
`ContDiffOn.continuousOn_fderivWithin` (`UniqueDiffOn` from `uniqueDiffOn_Ioi`, `uniqueDiffOn_Ioo`,
`uniqueDiffOn_Icc`, `UniqueDiffOn.prod`); likewise on the right half `U ∩ {τ ≥ t}`, which splits as
`{τ = t} ∪ {t < τ}`: on the first part `f'` is again the `G`-branch (its value at `p` included) and
on the second the `H`-branch, whose value at a junction point is identified with that of `f'` by
(i); combine with `ContinuousWithinAt.union`.  This is
`Work.FTS.StrongEps.GlueParts.continuousOn_junctionStep`. -/
theorem contDiffWithinAt_concat_halfslab {G H : Work.FTS.Galerkin.Fam} {t δ : ℝ}
    {R : Work.FTS.Galerkin.Fn} {q : Work.FTS.StrongGlobal.P3} (hδ : 0 < δ)
    (hG : ContDiffOn ℝ 1 (Work.FTS.StrongGlobal.uncurry3 G)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 t))
    (hH : ContDiffOn ℝ 1 (Work.FTS.StrongGlobal.uncurry3 H)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc t (t + δ)))
    (hval : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → G z θ t = H z θ t)
    (hderG : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      HasDerivWithinAt (fun s => G z θ s) (R z θ) (Set.Icc 0 t) t)
    (hderH : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      HasDerivWithinAt (fun s => H z θ s) (R z θ) (Set.Icc t (t + δ)) t)
    (hq : q ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 (t + δ))
    (hqt : q.2.2 = t) :
    ContDiffWithinAt ℝ 1 (Work.FTS.StrongGlobal.uncurry3 (Work.FTS.StrongGlobal.concat G H t))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 (t + δ)) q := by
  by_cases h0 : t = 0
  · -- degenerate case: on the slab the concatenation *is* `H` (by `hval` on the hyperplane `τ = 0`)
    subst h0
    have hEqOn : ∀ p ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 (0 + δ),
        uncurry3 (concat G H 0) p = uncurry3 H p := by
      intro p hp
      show concat G H 0 p.1 p.2.1 p.2.2 = H p.1 p.2.1 p.2.2
      rcases lt_or_ge (0 : ℝ) p.2.2 with h | h
      · rw [concat_apply_of_gt h]
      · have hp0 : p.2.2 = 0 := le_antisymm h hp.2.2.1
        rw [concat_apply_of_le h, hp0]
        exact hval p.1 p.2.1 hp.1 hp.2.1.1 hp.2.1.2
    exact (hH.contDiffWithinAt hq).congr hEqOn (hEqOn q hq)
  · -- main case
    have ht0 : 0 ≤ t := hqt ▸ hq.2.2.1
    have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm h0)
    refine key (G := G) (H := H) (t := t) (δ := δ) (R := R) (q := q) htpos hδ ?_ ?_
      hG hH hval hderG hderH hq hqt
    · -- the junction comparison of the two one-sided derivative fields
      intro p cG cH hpU hp4 hA hB
      exact junction_eq_fderivWithin (G := G) (H := H) (t := t) (δ := δ) (R := R) (p := p)
        (cG := cG) (cH := cH) htpos hδ hpU hp4 hA hB hval hderG hderH
    · -- continuity of the piecewise derivative field
      exact continuousOn_junctionStep (G := G) (H := H) (t := t) (δ := δ) htpos hδ hG hH

end Work.FTS.StrongEps.GlueParts
end
-- ===== merged: Submission.Work.FTS.StrongEps.TenOfEight.mslot_le_gain_all =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

open Work.FTS.StrongEps.EpsE4Thr

namespace Work.FTS.StrongEps.TenOfEight

set_option maxHeartbeats 1000000

/-! ## Auxiliary facts about the routed kernels `KdK ρ ε a b`

The routed kernels are smooth and compactly supported, hence supported in the closed ball of
radius `ε`; this gives both their integrability against any function which is continuous on that
ball, and a sharp bound of their mass by the level-`M` mass `Ksm`. -/

private lemma tsupport_KdK_subset_closedBall {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε) (a b : ℕ) :
    tsupport (KdK ρ ε a b) ⊆ Metric.closedBall (0 : ℝ × ℝ) ε := by
  have hS : ∀ {F : ℝ × ℝ → ℝ}, tsupport F ⊆ Metric.closedBall (0 : ℝ × ℝ) ε →
      tsupport (Work.FTS.StrongEps.partSnd F) ⊆ Metric.closedBall (0 : ℝ × ℝ) ε := by
    intro F hF
    refine closure_minimal (fun q hq => ?_) Metric.isClosed_closedBall
    exact hF (mem_tsupport_of_partSnd_ne_zero (Function.mem_support.mp hq))
  have hP : ∀ {F : ℝ × ℝ → ℝ}, tsupport F ⊆ Metric.closedBall (0 : ℝ × ℝ) ε →
      tsupport (Work.FTS.StrongEps.partFst F) ⊆ Metric.closedBall (0 : ℝ × ℝ) ε := by
    intro F hF
    refine closure_minimal (fun q hq => ?_) Metric.isClosed_closedBall
    exact hF (mem_tsupport_of_partFst_ne_zero (Function.mem_support.mp hq))
  have hbase : tsupport (Work.FTS.StrongEps.Jker ρ ε) ⊆ Metric.closedBall (0 : ℝ × ℝ) ε := by
    refine closure_minimal (fun q hq => ?_) Metric.isClosed_closedBall
    have h := Work.FTS.StrongEps.Jker_ne_zero_support hρ.moll hε (Function.mem_support.mp hq)
    have h1 : q.1 ^ 2 ≤ ε ^ 2 := by nlinarith [sq_nonneg q.2]
    have h2 : q.2 ^ 2 ≤ ε ^ 2 := by nlinarith [sq_nonneg q.1]
    have ha : |q.1| ≤ ε := by rw [sq_le_sq] at h1; rwa [abs_of_nonneg hε.le] at h1
    have hb : |q.2| ≤ ε := by rw [sq_le_sq] at h2; rwa [abs_of_nonneg hε.le] at h2
    rw [Metric.mem_closedBall, dist_zero_right]
    exact max_le ha hb
  induction a with
  | zero =>
    induction b with
    | zero =>
      simpa only [KdK, Work.FTS.StrongEps.Kd_zero_eq,
        Function.iterate_zero_apply] using hbase
    | succ b ih => simpa only [KdK, Work.FTS.StrongEps.Kd_zero_succ] using hS ih
  | succ a ih => simpa only [KdK, Work.FTS.StrongEps.Kd_succ_eq] using hP ih

private lemma KdK_eq_zero_of_notMem_closedBall {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε) (a b : ℕ) {p : ℝ × ℝ}
    (hp : p ∉ Metric.closedBall (0 : ℝ × ℝ) ε) : KdK ρ ε a b p = 0 := by
  by_contra hne
  refine hp (tsupport_KdK_subset_closedBall hρ hε a b ?_)
  exact subset_tsupport _ (Function.mem_support.mpr hne)

private lemma integrable_abs_KdK_mul {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {ε : ℝ} (hε : 0 < ε) (a b : ℕ) {B : ℝ × ℝ → ℝ}
    (hB : ContinuousOn B (Metric.closedBall (0 : ℝ × ℝ) ε)) :
    Integrable (fun p : ℝ × ℝ => |KdK ρ ε a b p| * B p) := by
  have hon : IntegrableOn (fun p : ℝ × ℝ => |KdK ρ ε a b p| * B p)
      (Metric.closedBall (0 : ℝ × ℝ) ε) :=
    (((KdK_continuous hρ ε a b).abs.continuousOn).mul hB).integrableOn_compact
      (isCompact_closedBall (0 : ℝ × ℝ) ε)
  refine hon.integrable_of_forall_notMem_eq_zero (fun p hp => ?_)
  rw [KdK_eq_zero_of_notMem_closedBall hρ hε a b hp, abs_zero, zero_mul]

/-- The mass of a single routed kernel is bounded by the total mass `Ksm`. -/
private lemma integral_abs_KdK_le_Ksm {ρ : ℝ × ℝ → ℝ}
    (ε : ℝ) {M a b : ℕ} (ha : a ≤ M) (hb : b ≤ M) :
    (∫ p : ℝ × ℝ, |KdK ρ ε a b p|) ≤ Ksm ρ ε M := by
  have hmem : (∫ p : ℝ × ℝ, |KdK ρ ε a b p|)
      ≤ ∑ a' ∈ Finset.range (M + 1), ∑ b' ∈ Finset.range (M + 1),
          ∫ p : ℝ × ℝ, |KdK ρ ε a' b' p| := by
    calc (∫ p : ℝ × ℝ, |KdK ρ ε a b p|)
        ≤ ∑ a' ∈ Finset.range (M + 1), ∫ p : ℝ × ℝ, |KdK ρ ε a' b p| :=
          Finset.single_le_sum (f := fun a' => ∫ p : ℝ × ℝ, |KdK ρ ε a' b p|)
            (fun _ _ => integral_nonneg fun p => abs_nonneg _)
            (Finset.mem_range.mpr (by omega))
      _ ≤ ∑ a' ∈ Finset.range (M + 1), ∑ b' ∈ Finset.range (M + 1),
            ∫ p : ℝ × ℝ, |KdK ρ ε a' b' p| :=
          Finset.sum_le_sum fun a' _ => Finset.single_le_sum
            (f := fun b' => ∫ p : ℝ × ℝ, |KdK ρ ε a' b' p|)
            (fun _ _ => integral_nonneg fun p => abs_nonneg _)
            (Finset.mem_range.mpr (by omega))
  simpa only [Ksm] using hmem

/-- `((2^n a) b)^2 = 2^{2n} (ab)^2`. -/
private lemma sq_mul_pow_two (n : ℕ) (a b : ℝ) :
    ((2 : ℝ) ^ n * a * b) ^ 2 = (2 : ℝ) ^ (2 * n) * (a * b) ^ 2 := by
  rw [mul_pow, mul_pow, ← pow_mul, Nat.mul_comm]
  ring

/-- **The real-valued core of the `θ`-routed slot bound**: the routed identity of
`mixed_Jeps_kernel_partial` (all `j` `z`-derivatives and `i - 1` `θ`-derivatives on the kernel),
then weighted Cauchy–Schwarz (`StepFacts.srb_cs_core`), then the domination of the routed kernel
by `LamAll` (pointwise) and by `Ksm · 2^{2M} = KgainBig` (in mass). -/
private lemma mslot_core {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {ε α c : ℝ}
    (hε : 0 < ε) {M : ℕ} {f : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hW : ∀ p : ℝ × ℝ, Work.Spaces.Wt α z θ ≤ Real.exp (c * (|p.1| + |p.2|))
      * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2))
    {j i : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ M) :
    ((2 : ℝ) ^ (i - 1) * (∫ p : ℝ × ℝ, KdK ρ ε j (i - 1) p
        * Work.Spaces.mixed 0 1 f (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2)) * Work.Spaces.Wt α z θ) ^ 2
      ≤ KgainBig ρ ε M
          * ∫ p : ℝ × ℝ, |KdK ρ ε j (i - 1) p|
              * Real.exp (2 * c * (|p.1| + |p.2|))
              * (Work.Spaces.mixed 0 1 f (Work.FTS.StrongEps.zShift z p.1)
                  (Work.FTS.StrongEps.thShift θ p.2)
                * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2)) ^ 2 := by
  have hM1 : i - 1 ≤ M := by omega
  have hjM : j ≤ M := by omega
  have hW₀ : 0 ≤ Work.Spaces.Wt α z θ := Work.FTS.StrongEps.StepFacts.srb_Wt_nonneg α hz hθ
  have hGc : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed 0 1 f
      (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2))
      (Metric.closedBall (0 : ℝ × ℝ) ε) :=
    Work.FTS.StrongEps.HkSqAux.continuousOn_shift_ball hz hθ
      (Work.FTS.StrongEps.HkSqAux.continuousOn_mixed_region hz hε hθ hf 0 1)
  have hWc : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α
      (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2))
      (Metric.closedBall (0 : ℝ × ℝ) ε) :=
    Work.FTS.StrongEps.HkSqAux.continuousOn_shift_ball hz hθ
      (Work.FTS.StrongEps.HkSqAux.continuousOn_Wt_region hz hε hθ)
  have hexp : Continuous (fun p : ℝ × ℝ => Real.exp (2 * c * (|p.1| + |p.2|))) := by
    refine Real.continuous_exp.comp (Continuous.mul continuous_const ?_)
    exact (continuous_abs.comp continuous_fst).add (continuous_abs.comp continuous_snd)
  have hKint : Integrable (fun p : ℝ × ℝ => |KdK ρ ε j (i - 1) p|) := by
    have h := integrable_abs_KdK_mul hρ hε j (i - 1)
      (B := fun _ : ℝ × ℝ => (1 : ℝ)) continuousOn_const
    simpa only [mul_one] using h
  have hQint : Integrable (fun p : ℝ × ℝ => |KdK ρ ε j (i - 1) p|
      * Real.exp (2 * c * (|p.1| + |p.2|))
      * (Work.Spaces.mixed 0 1 f (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2)
        * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2)) ^ 2) := by
    have h := integrable_abs_KdK_mul hρ hε j (i - 1) (B := fun p : ℝ × ℝ =>
      Real.exp (2 * c * (|p.1| + |p.2|))
        * (Work.Spaces.mixed 0 1 f (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2)
          * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2)) ^ 2)
      (hexp.continuousOn.mul ((hGc.mul hWc).pow 2))
    simpa only [mul_assoc] using h
  have hK2int : Integrable (fun p : ℝ × ℝ => |KdK ρ ε j (i - 1) p|
      * (Work.Spaces.mixed 0 1 f (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2) * Work.Spaces.Wt α z θ) ^ 2) := by
    have h := integrable_abs_KdK_mul hρ hε j (i - 1) (B := fun p : ℝ × ℝ =>
      (Work.Spaces.mixed 0 1 f (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2) * Work.Spaces.Wt α z θ) ^ 2)
      ((hGc.mul continuousOn_const).pow 2)
    simpa only [mul_assoc] using h
  have hmass : (∫ p : ℝ × ℝ, |KdK ρ ε j (i - 1) p|) ≤ Ksm ρ ε M :=
    integral_abs_KdK_le_Ksm ε hjM hM1
  have hcs := Work.FTS.StrongEps.StepFacts.srb_cs_core
    (K := fun p : ℝ × ℝ => KdK ρ ε j (i - 1) p)
    (G := fun p : ℝ × ℝ => Work.Spaces.mixed 0 1 f (Work.FTS.StrongEps.zShift z p.1)
      (Work.FTS.StrongEps.thShift θ p.2))
    (W := fun p : ℝ × ℝ => Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
      (Work.FTS.StrongEps.thShift θ p.2))
    (W₀ := Work.Spaces.Wt α z θ) (c := c)
    (M := ∫ p : ℝ × ℝ, KdK ρ ε j (i - 1) p
        * Work.Spaces.mixed 0 1 f (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2))
    hW₀ hW hKint hQint hK2int rfl
  have key : (2 : ℝ) ^ (2 * (i - 1))
        * ((∫ p : ℝ × ℝ, |KdK ρ ε j (i - 1) p|)
          * ∫ p : ℝ × ℝ, |KdK ρ ε j (i - 1) p|
              * Real.exp (2 * c * (|p.1| + |p.2|))
              * (Work.Spaces.mixed 0 1 f (Work.FTS.StrongEps.zShift z p.1)
                  (Work.FTS.StrongEps.thShift θ p.2)
                * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2)) ^ 2)
      ≤ KgainBig ρ ε M
          * ∫ p : ℝ × ℝ, |KdK ρ ε j (i - 1) p|
              * Real.exp (2 * c * (|p.1| + |p.2|))
              * (Work.Spaces.mixed 0 1 f (Work.FTS.StrongEps.zShift z p.1)
                  (Work.FTS.StrongEps.thShift θ p.2)
                * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2)) ^ 2 := by
    have h2pow : (2 : ℝ) ^ (2 * (i - 1)) ≤ 2 ^ (2 * M) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hF0 : 0 ≤ ∫ p : ℝ × ℝ, |KdK ρ ε j (i - 1) p|
              * Real.exp (2 * c * (|p.1| + |p.2|))
              * (Work.Spaces.mixed 0 1 f (Work.FTS.StrongEps.zShift z p.1)
                  (Work.FTS.StrongEps.thShift θ p.2)
                * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2)) ^ 2 :=
      integral_nonneg fun p =>
        mul_nonneg (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le) (sq_nonneg _)
    have hK0 : 0 ≤ ∫ p : ℝ × ℝ, |KdK ρ ε j (i - 1) p| := integral_nonneg fun p => abs_nonneg _
    calc (2 : ℝ) ^ (2 * (i - 1))
          * ((∫ p : ℝ × ℝ, |KdK ρ ε j (i - 1) p|)
            * ∫ p : ℝ × ℝ, |KdK ρ ε j (i - 1) p|
                * Real.exp (2 * c * (|p.1| + |p.2|))
                * (Work.Spaces.mixed 0 1 f (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2)
                  * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
                      (Work.FTS.StrongEps.thShift θ p.2)) ^ 2)
        ≤ 2 ^ (2 * M) * ((∫ p : ℝ × ℝ, |KdK ρ ε j (i - 1) p|)
            * ∫ p : ℝ × ℝ, |KdK ρ ε j (i - 1) p|
                * Real.exp (2 * c * (|p.1| + |p.2|))
                * (Work.Spaces.mixed 0 1 f (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2)
                  * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
                      (Work.FTS.StrongEps.thShift θ p.2)) ^ 2) :=
          mul_le_mul_of_nonneg_right h2pow (mul_nonneg hK0 hF0)
      _ ≤ 2 ^ (2 * M) * (Ksm ρ ε M
            * ∫ p : ℝ × ℝ, |KdK ρ ε j (i - 1) p|
                * Real.exp (2 * c * (|p.1| + |p.2|))
                * (Work.Spaces.mixed 0 1 f (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2)
                  * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
                      (Work.FTS.StrongEps.thShift θ p.2)) ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmass hF0) (by positivity)
      _ = KgainBig ρ ε M
            * ∫ p : ℝ × ℝ, |KdK ρ ε j (i - 1) p|
                * Real.exp (2 * c * (|p.1| + |p.2|))
                * (Work.Spaces.mixed 0 1 f (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2)
                  * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
                      (Work.FTS.StrongEps.thShift θ p.2)) ^ 2 := by
          simp only [KgainBig]
          ring
  calc ((2 : ℝ) ^ (i - 1) * (∫ p : ℝ × ℝ, KdK ρ ε j (i - 1) p
          * Work.Spaces.mixed 0 1 f (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2)) * Work.Spaces.Wt α z θ) ^ 2
      = (2 : ℝ) ^ (2 * (i - 1)) * ((∫ p : ℝ × ℝ,
            KdK ρ ε j (i - 1) p
          * Work.Spaces.mixed 0 1 f (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2)) * Work.Spaces.Wt α z θ) ^ 2 :=
        sq_mul_pow_two (i - 1) _ _
    _ ≤ (2 : ℝ) ^ (2 * (i - 1))
          * ((∫ p : ℝ × ℝ, |KdK ρ ε j (i - 1) p|)
            * ∫ p : ℝ × ℝ, |KdK ρ ε j (i - 1) p|
                * Real.exp (2 * c * (|p.1| + |p.2|))
                * (Work.Spaces.mixed 0 1 f (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2)
                  * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
                      (Work.FTS.StrongEps.thShift θ p.2)) ^ 2) :=
        mul_le_mul_of_nonneg_left hcs (by positivity)
    _ ≤ KgainBig ρ ε M
          * ∫ p : ℝ × ℝ, |KdK ρ ε j (i - 1) p|
              * Real.exp (2 * c * (|p.1| + |p.2|))
              * (Work.Spaces.mixed 0 1 f (Work.FTS.StrongEps.zShift z p.1)
                  (Work.FTS.StrongEps.thShift θ p.2)
                * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2)) ^ 2 := key

/-- `Work.FTS.StrongEps.TenOfEight.mslot_le_gain_all` (namespace `Work.FTS.StrongEps.TenOfEight`).

**Recipe.** Copy `Submission/Work/FTS/StrongEps/EpsE4Thr/GainSlot/mslot_le_gain.lean` into the
new file (including its private helpers `tsupport_KdK_subset_closedBall`,
`KdK_eq_zero_of_notMem_closedBall`, `integrable_abs_KdK_mul`, `integral_abs_KdK_le_Ksm`,
`sq_mul_pow_two` and `mslot_core`, which are `private` and hence must be reproduced; note that
from the new namespace the unqualified names `KdK`, `Ksm`, `LamK`, … need `open Work.FTS.StrongEps.EpsE4Thr`),
then
(i) drop the hypothesis `hε1 : ε ≤ 1`,
(ii) replace the density `Work.FTS.StrongEps.EpsE4Thr.LamFull ρ ε c M` everywhere by
`Work.FTS.StrongEps.TenOfEight.LamAll ρ ε c M` (defined in
`Submission/Work/FTS/StrongEps/TenOfEight/LamAllDefs.lean`),
(iii) replace the three uses of `LamFull_nonneg hρ hε M` by `LamAll_nonneg hρ hε M` and the use
of `abs_KdK_mul_exp_le_LamFull hρ hε hε1 hc (by omega) p` by
`abs_KdK_mul_exp_le_LamAll hρ hε hc (by omega) p`
(both live in `Work.FTS.StrongEps.TenOfEight`).
Nothing else changes: the private core `mslot_core` and the mass constants `KgainBig`/`Ksm`
are unchanged. -/
theorem mslot_le_gain_all {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {ε α c : ℝ}
    (hε : 0 < ε) (hc : 0 ≤ c) {M k : ℕ} (hk : 1 ≤ k) {f : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hW : ∀ p : ℝ × ℝ, Work.Spaces.Wt α z θ ≤ Real.exp (c * (|p.1| + |p.2|))
      * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2))
    {j i : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ M) :
    ENNReal.ofReal ((Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f) z θ
        * Work.Spaces.Wt α z θ) ^ 2)
      ≤ ENNReal.ofReal (Work.FTS.StrongEps.EpsE4Thr.KgainBig ρ ε M)
        * ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Work.FTS.StrongEps.TenOfEight.LamAll ρ ε c M p)
            * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
                (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) := by
  have hcore := mslot_core (ρ := ρ) (α := α) (c := c) (M := M) (f := f) (z := z) (θ := θ)
    (j := j) (i := i) hρ hε hf hz hθ hW hi hij
  -- the routed identity: all `j` `z`-derivatives and `i - 1` `θ`-derivatives sit on the kernel
  have hroute : Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f) z θ
      = (2 : ℝ) ^ (i - 1) * ∫ p : ℝ × ℝ, KdK ρ ε j (i - 1) p
          * Work.Spaces.mixed 0 1 f (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2) := by
    have hKd : ∀ p : ℝ × ℝ, KdK ρ ε j (i - 1) p
        = iteratedDeriv j (fun s : ℝ => iteratedDeriv (i - 1)
            (fun t : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, t)) p.2) p.1 :=
      fun p => congrFun (Work.FTS.StrongEps.Kd_eq (Work.FTS.StrongEps.Jker ρ ε) j (i - 1)) p
    have h := Work.FTS.StrongEps.mixed_Jeps_kernel_partial ρ hρ hε hf hz hθ j i 0 1
      (Nat.zero_le j) hi
    simp only [Nat.sub_zero] at h
    rw [h]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only [hKd p]
  rw [hroute]
  refine (ENNReal.ofReal_le_ofReal hcore).trans ?_
  have hF0 : ∀ p : ℝ × ℝ, 0 ≤ |KdK ρ ε j (i - 1) p|
      * Real.exp (2 * c * (|p.1| + |p.2|))
      * (Work.Spaces.mixed 0 1 f (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2)
        * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2)) ^ 2 :=
    fun p => mul_nonneg (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le) (sq_nonneg _)
  have hF'0 : ∀ p : ℝ × ℝ, 0 ≤ LamAll ρ ε c M p
      * Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2) :=
    fun p => mul_nonneg (LamAll_nonneg hρ hε M p)
      (Work.Spaces.HkIntegrand_nonneg α k f _ _)
  have hFF : ∀ p : ℝ × ℝ, |KdK ρ ε j (i - 1) p|
      * Real.exp (2 * c * (|p.1| + |p.2|))
      * (Work.Spaces.mixed 0 1 f (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2)
        * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2)) ^ 2
      ≤ LamAll ρ ε c M p
      * Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2) := by
    intro p
    have h1 : |KdK ρ ε j (i - 1) p| * Real.exp (2 * c * (|p.1| + |p.2|))
        ≤ LamAll ρ ε c M p :=
      abs_KdK_mul_exp_le_LamAll hρ hε hc (by omega) p
    have h2 : (Work.Spaces.mixed 0 1 f (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2)
        * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2)) ^ 2
        ≤ Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2) :=
      Work.Spaces.sq_le_HkIntegrand_mixed α k f _ _ 1 0 le_rfl (by omega)
    exact mul_le_mul h1 h2 (sq_nonneg _) (LamAll_nonneg hρ hε M p)
  refine (Work.FTS.StrongEps.StepFacts.ofReal_mul_integral_le_lintegral
    (KgainBig_nonneg hρ ε M) (KgainBig_nonneg hρ ε M) le_rfl hF0 hF'0 hFF).trans ?_
  rw [lintegral_congr (fun p => ENNReal.ofReal_mul (LamAll_nonneg hρ hε M p))]

end Work.FTS.StrongEps.TenOfEight
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Rhs.CoupledVfs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs

open Work.FTS.Galerkin (Fn)
open Work.Spaces (HkIntegrand HkMem HkNorm HkSq Dz Dth pth)

set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem contDiffOn_gc_top (α : ℝ) :
    ContDiffOn ℝ ⊤ (fun θ : ℝ => Work.Spaces.Gam α θ / Work.Spaces.c α) (Set.Ioo 0 (π / 2)) := by
  have hbase : ContDiffOn ℝ ⊤ (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2)
      (Set.Ioo (0 : ℝ) (π / 2)) :=
    (Real.contDiff_sin.contDiffOn).mul ((Real.contDiff_cos.contDiffOn).pow 2)
  have hne : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), Real.sin θ * Real.cos θ ^ 2 ≠ 0 := by
    intro θ hθ
    have h1 : 0 < Real.sin θ :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have h2 : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    positivity
  have hgam : ContDiffOn ℝ ⊤ (fun θ : ℝ => Work.Spaces.Gam α θ) (Set.Ioo (0 : ℝ) (π / 2)) :=
    hbase.rpow_const_of_ne hne
  simpa only [VfsGc] using hgam.div_const (Work.Spaces.c α)

theorem contDiffOn_VfsA1 (α : ℝ) :
    ContDiffOn ℝ 3 (VfsA1 α) (Set.Ioo (0 : ℝ) (π / 2)) := by
  have hgc : ContDiffOn ℝ 4 (fun θ : ℝ => VfsGc α θ) (Set.Ioo (0 : ℝ) (π / 2)) :=
    (contDiffOn_gc_top α).of_le (by norm_num : ((4 : ℕ) : WithTop ℕ∞) ≤ ⊤)
  have hd : ContDiffOn ℝ 3 (deriv (fun θ : ℝ => VfsGc α θ)) (Set.Ioo (0 : ℝ) (π / 2)) :=
    hgc.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hs2 : ContDiffOn ℝ 3 (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo (0 : ℝ) (π / 2)) := by
    fun_prop
  have hprod : ContDiffOn ℝ 3 (fun θ : ℝ =>
      deriv (fun θ : ℝ => VfsGc α θ) θ * Real.sin (2 * θ)) (Set.Ioo (0 : ℝ) (π / 2)) :=
    hd.mul hs2
  have hcs := (contDiffOn_const (c := (3 / 2 : ℝ)) (s := Set.Ioo (0 : ℝ) (π / 2))).mul hprod
  refine hcs.congr (fun θ _ => ?_)
  simp only [VfsA1, Work.Spaces.dthU]
  ring

theorem contDiffOn_VfsA2 (α : ℝ) :
    ContDiffOn ℝ 3 (VfsA2 α) (Set.Ioo (0 : ℝ) (π / 2)) := by
  have hc2m : ContDiffOn ℝ 3 (fun θ : ℝ => Real.cos (2 * θ) - Real.sin θ ^ 2)
      (Set.Ioo (0 : ℝ) (π / 2)) := by fun_prop
  have hgc : ContDiffOn ℝ 3 (fun θ : ℝ => VfsGc α θ) (Set.Ioo (0 : ℝ) (π / 2)) :=
    (contDiffOn_gc_top α).of_le (by norm_num : ((3 : ℕ) : WithTop ℕ∞) ≤ ⊤)
  have hprod : ContDiffOn ℝ 3 (fun θ : ℝ =>
      (Real.cos (2 * θ) - Real.sin θ ^ 2) * VfsGc α θ) (Set.Ioo (0 : ℝ) (π / 2)) :=
    hc2m.mul hgc
  have hcs := (contDiffOn_const (c := -α) (s := Set.Ioo (0 : ℝ) (π / 2))).mul hprod
  refine hcs.congr (fun θ _ => ?_)
  simp only [VfsA2, Work.Construction.c2m_eq]
  ring

theorem contDiffOn_VfsRad (n : ℕ) : ContDiffOn ℝ n VfsRad (Set.Ioi (0 : ℝ)) := by
  have h : ContDiffOn ℝ n (fun z : ℝ => (2 * z) / (1 + z) ^ 2) (Set.Ioi (0 : ℝ)) := by
    refine ContDiffOn.div (by fun_prop) (by fun_prop) (fun z hz => ?_)
    have hz' : (0 : ℝ) < z := Set.mem_Ioi.mp hz
    have h4 : (0 : ℝ) < (1 + z) ^ 2 := by positivity
    exact ne_of_gt h4
  refine ContDiffOn.congr h (fun z _ => ?_)
  simp only [VfsRad]

theorem contDiffOn_VfsRadZ (n : ℕ) : ContDiffOn ℝ n VfsRadZ (Set.Ioi (0 : ℝ)) := by
  have hd : ContDiffOn ℝ n (deriv VfsRad) (Set.Ioi (0 : ℝ)) :=
    (contDiffOn_VfsRad (n + 1)).deriv_of_isOpen isOpen_Ioi (by simp)
  have hm : ContDiffOn ℝ n (fun z : ℝ => z * deriv VfsRad z) (Set.Ioi (0 : ℝ)) :=
    contDiffOn_id.mul hd
  refine ContDiffOn.congr hm (fun z _ => ?_)
  simp only [VfsRadZ, Work.Spaces.Zop]

theorem angMaj_nonneg (α : ℝ) (C : ℝ → ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ angMaj α C θ := by
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  simp only [angMaj]
  refine add_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs _)) ?_
  refine Finset.sum_nonneg fun i _ => ?_
  split_ifs with hi
  · exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs _)
  · exact le_refl 0

theorem VfsAngMaj_nonneg {α : ℝ} {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ VfsAngMaj α θ := by
  simp only [VfsAngMaj]
  exact add_nonneg (angMaj_nonneg α (VfsA1 α) hθ) (angMaj_nonneg α (VfsA2 α) hθ)

/-- The weighted radial slot sum attached to the radial factor `B`. -/
def Sz (f : Fn) (B : ℝ → ℝ) (z : ℝ) : ℝ :=
  ∑ q ∈ Finset.range 4, (Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 f z * B z) z 0) ^ 2
    * (Work.Spaces.w z) ^ 2

/-- **The pointwise bound for `Mf f · Vfs α`.** -/
theorem P2_integrand_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : Fn}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (hsep : ∀ z θ : ℝ, Vfs α z θ = VfsA1 α θ * VfsRad z + VfsA2 α θ * VfsRadZ z) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 3 (fun z θ => Mf f z θ * Vfs α z θ) z θ
        ≤ 2 * (angMaj α (VfsA1 α) θ * Sz f VfsRad z + angMaj α (VfsA2 α) θ * Sz f VfsRadZ z) := by
  intro z hz θ hθ
  have hVfsep : (fun z θ => Mf f z θ * Vfs α z θ)
      = fun z θ => VfsA1 α θ * (Work.Construction.L12 f z * VfsRad z)
          + VfsA2 α θ * (Work.Construction.L12 f z * VfsRadZ z) := by
    funext z θ
    rw [hsep z θ, Mf]
    ring
  -- smoothness of the two separated terms
  have hL12 : ContDiffOn ℝ 3 (fun z : ℝ => Work.Construction.L12 f z) (Set.Ioi (0 : ℝ)) :=
    (Work.FTS.EllipticEst.UopHk.contDiffOn_L12_k α 4 f hα hα1 hso hmem
      (by norm_num)).of_le (by norm_num)
  have hB1 : ContDiffOn ℝ 3 (fun z : ℝ => Work.Construction.L12 f z * VfsRad z)
      (Set.Ioi (0 : ℝ)) := hL12.mul (contDiffOn_VfsRad 3)
  have hB2 : ContDiffOn ℝ 3 (fun z : ℝ => Work.Construction.L12 f z * VfsRadZ z)
      (Set.Ioi (0 : ℝ)) := hL12.mul (contDiffOn_VfsRadZ 3)
  have hA1 : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => VfsA1 α p.2) Work.FTS.EllipticEst.Q0 :=
    (contDiffOn_VfsA1 α).comp contDiffOn_snd
      (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).2)
  have hA2 : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => VfsA2 α p.2) Work.FTS.EllipticEst.Q0 :=
    (contDiffOn_VfsA2 α).comp contDiffOn_snd
      (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).2)
  have hB1q : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => Work.Construction.L12 f p.1 * VfsRad p.1)
      Work.FTS.EllipticEst.Q0 :=
    hB1.comp contDiffOn_fst (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
  have hB2q : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => Work.Construction.L12 f p.1 * VfsRadZ p.1)
      Work.FTS.EllipticEst.Q0 :=
    hB2.comp contDiffOn_fst (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
  have hT1 : ContDiffOn ℝ 3 (Function.uncurry
      (fun z θ => VfsA1 α θ * (Work.Construction.L12 f z * VfsRad z)))
      Work.FTS.EllipticEst.Q0 := hA1.mul hB1q
  have hT2 : ContDiffOn ℝ 3 (Function.uncurry
      (fun z θ => VfsA2 α θ * (Work.Construction.L12 f z * VfsRadZ z)))
      Work.FTS.EllipticEst.Q0 := hA2.mul hB2q
  rw [hVfsep]
  have hadd : Work.Spaces.HkIntegrand α 3 (fun z θ =>
        VfsA1 α θ * (Work.Construction.L12 f z * VfsRad z)
          + VfsA2 α θ * (Work.Construction.L12 f z * VfsRadZ z)) z θ
      ≤ 2 * Work.Spaces.HkIntegrand α 3
          (fun z θ => VfsA1 α θ * (Work.Construction.L12 f z * VfsRad z)) z θ
        + 2 * Work.Spaces.HkIntegrand α 3
          (fun z θ => VfsA2 α θ * (Work.Construction.L12 f z * VfsRadZ z)) z θ :=
    Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.HkIntegrand_add_le_domain α 3 hT1 hT2 z hz θ hθ
  have hS1 : Work.Spaces.HkIntegrand α 3
        (fun z θ => VfsA1 α θ * (Work.Construction.L12 f z * VfsRad z)) z θ
      ≤ angMaj α (VfsA1 α) θ * Sz f VfsRad z :=
    Work.FTS.StrongPersist.L3Aux.HkIntegrand_sep_le (α := α) (C := VfsA1 α)
      (B := fun z => Work.Construction.L12 f z * VfsRad z) (z := z) (θ := θ) hθ
  have hS2 : Work.Spaces.HkIntegrand α 3
        (fun z θ => VfsA2 α θ * (Work.Construction.L12 f z * VfsRadZ z)) z θ
      ≤ angMaj α (VfsA2 α) θ * Sz f VfsRadZ z :=
    Work.FTS.StrongPersist.L3Aux.HkIntegrand_sep_le (α := α) (C := VfsA2 α)
      (B := fun z => Work.Construction.L12 f z * VfsRadZ z) (z := z) (θ := θ) hθ
  calc Work.Spaces.HkIntegrand α 3 (fun z θ =>
        VfsA1 α θ * (Work.Construction.L12 f z * VfsRad z)
          + VfsA2 α θ * (Work.Construction.L12 f z * VfsRadZ z)) z θ
      ≤ 2 * Work.Spaces.HkIntegrand α 3
          (fun z θ => VfsA1 α θ * (Work.Construction.L12 f z * VfsRad z)) z θ
        + 2 * Work.Spaces.HkIntegrand α 3
          (fun z θ => VfsA2 α θ * (Work.Construction.L12 f z * VfsRadZ z)) z θ := hadd
    _ ≤ 2 * (angMaj α (VfsA1 α) θ * Sz f VfsRad z)
        + 2 * (angMaj α (VfsA2 α) θ * Sz f VfsRadZ z) :=
        add_le_add (mul_le_mul_of_nonneg_left hS1 (by norm_num))
          (mul_le_mul_of_nonneg_left hS2 (by norm_num))
    _ = 2 * (angMaj α (VfsA1 α) θ * Sz f VfsRad z
        + angMaj α (VfsA2 α) θ * Sz f VfsRadZ z) := by ring

theorem Sz_nonneg (f : Fn) (B : ℝ → ℝ) (z : ℝ) : 0 ≤ Sz f B z := by
  simp only [Sz]
  exact Finset.sum_nonneg fun q _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)

theorem jets_VfsRad : ∀ b ≤ 4, ∀ z ∈ Work.Spaces.Iz,
    |Work.Spaces.Zop^[b] VfsRad z| ≤ 24000 := by
  intro b hb z hz
  have h2 : |Work.Spaces.DzIter b (fun z (_ : ℝ) => 2 * z / (1 + z) ^ 2) z 0| ≤ 24000 :=
    Work.FTS.StrongPersist.L3Aux.zslot_supBound b hb z hz 0
      ⟨le_refl 0, by linarith [Real.pi_pos]⟩
  have hfun : (fun z => Work.Spaces.DzIter b (fun z (_ : ℝ) => 2 * z / (1 + z) ^ 2) z 0)
      = Work.Spaces.Zop^[b] VfsRad := by
    rw [Work.Spaces.Zop_slice b (fun z (_ : ℝ) => 2 * z / (1 + z) ^ 2) 0]
    rfl
  rw [← congrFun hfun z]
  exact h2

theorem jets_VfsRadZ : ∀ b ≤ 3, ∀ z ∈ Work.Spaces.Iz,
    |Work.Spaces.Zop^[b] VfsRadZ z| ≤ 24000 := by
  intro b hb z hz
  have h1 : Work.Spaces.Zop^[b] VfsRadZ = Work.Spaces.Zop^[b + 1] VfsRad := by
    have hz0 : VfsRadZ = Work.Spaces.Zop VfsRad := rfl
    rw [hz0]
    exact (Function.iterate_succ_apply Work.Spaces.Zop b VfsRad).symm
  rw [h1]
  exact jets_VfsRad (b + 1) (by omega) z hz

/-- `Vfs α` is `C^∞` on the open quadrant. -/
theorem smoothOpen_Vfs (α : ℝ) : Work.FTS.EllipticEst.SmoothOpen (Vfs α) := by
  have hF : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.StrongPersist.Degen.smoothOpen_Fstar α
  have ha : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (3 / (2 * α)) * (Real.sin (2 * θ)
        * Work.Spaces.pth (Work.Construction.Fstar α) z θ)) :=
    contDiffOn_const.mul (smoothOpen_sin_two.mul hF.pth)
  have hb : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (Real.cos (2 * θ) - Real.sin θ ^ 2)
        * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) :=
    smoothOpen_c2m.mul hF.Dz
  have hmain : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      (3 / (2 * α)) * (Real.sin (2 * θ) * Work.Spaces.pth (Work.Construction.Fstar α) z θ)
        - (Real.cos (2 * θ) - Real.sin θ ^ 2)
          * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) := ha.sub hb
  have hfun : (fun z θ =>
      (3 / (2 * α)) * (Real.sin (2 * θ) * Work.Spaces.pth (Work.Construction.Fstar α) z θ)
        - (Real.cos (2 * θ) - Real.sin θ ^ 2)
          * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) = Vfs α := by
    funext z θ
    simp only [Vfs, Work.Construction.s2_eq, Work.Construction.c2m_eq]
    ring
  rwa [hfun] at hmain

/-- `Bf α f` is `C^∞` on the open quadrant for `f` smooth there. -/
theorem smoothOpen_Bf {α : ℝ} {f : Fn} (hso : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (Bf α f) := by
  have hmain : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Vf α f z θ + Vfs α z θ) :=
    (smoothOpen_Vf hso).add (smoothOpen_Vfs α)
  have hfun : (fun z θ => Vf α f z θ + Vfs α z θ) = Bf α f := by
    funext z θ
    simp only [Bf]
  rwa [hfun] at hmain

end Work.FTS.StrongPersist.L3Rhs
end
end
