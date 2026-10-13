/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/DiffAux/MainEst.lean`

The assembly of the mollifier approximation estimate `HkSq_Jeps_sub_le`: the pointwise difference
estimate of `DiffAux/JepsSubPointwise.lean`, summed over the finitely many slots of the level-`k`
integrand, Tonelli's theorem, the log-coordinate shift invariance, and the combinatorial shadow
bound `DiffAux/shadow_le`.
-/
import Submission.Work.FTS.StrongEps.DiffAux.MainSetup
import Submission.Work.FTS.StrongEps.DiffAux.ShadowPointwise
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.StrongEps.Weights
import Submission.Work.FTS.StrongEps.mixed_Jeps
import Submission.Work.FTS.StrongEps.HkSqAux.Defs
import Submission.Work.FTS.StrongEps.HkSqAux.LogCoord
import Submission.Work.FTS.StrongEps.HkSqAux.lintegral_quad_log_subst
import Submission.Work.FTS.StrongEps.HkSqAux.lintegral_prod_shift
import Submission.Work.FTS.StrongEps.HkSqAux.logJac_shift_le
import Submission.Work.FTS.StrongEps.HkSqAux.continuousOn_mixed_Quad
import Submission.Work.FTS.StrongEps.HkSqAux.sq_integral_Jker_mul_le
import Submission.Work.FTS.StrongEps.HkSqAux.Chain
import Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen
import Submission.Work.FTS.LocData.SmoothChain

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
