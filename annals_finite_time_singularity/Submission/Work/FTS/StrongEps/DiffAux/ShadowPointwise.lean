/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/DiffAux/MainEst.lean`

The assembly of the mollifier approximation estimate `HkSq_Jeps_sub_le`: the pointwise difference
estimate of `DiffAux/JepsSubPointwise.lean`, summed over the finitely many slots of the level-`k`
integrand, Tonelli's theorem, the log-coordinate shift invariance, and the combinatorial shadow
bound `DiffAux/shadow_le`.
-/
import Submission.Work.FTS.StrongEps.DiffAux.MainSetup
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
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

/-! ## The pointwise sum of brackets against the shadow -/

theorem sum_bracket_le_shadow {α : ℝ} (hα : α ∈ Set.Ioc 0 1) (k : ℕ)
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad) (y : (ℝ × ℝ) × ℝ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (∑ i ∈ Finset.range (k + 1), bracket (Work.Spaces.DzIter i f) wE z θ y.1 y.2)
      + (∑ q ∈ slots k, bracket (Work.Spaces.mixed q.2 q.1 f) (Work.Spaces.Wt α) z θ y.1 y.2)
      ≤ shadow α k f (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2)) := by
  have hsQ : (zShift z (y.2 * y.1.1), thShift θ (y.2 * y.1.2)) ∈ Quad :=
    shift_mem_Quad hz hθ y
  have hsm : Work.FTS.StrongEps.SmQ (Work.Spaces.DthIter 1 f) :=
    (Work.FTS.StrongEps.smQ_of_forall_nat hf).DthIter 1
  have h1 : ∀ i ∈ Finset.range (k + 1),
      bracket (Work.Spaces.DzIter i f) wE z θ y.1 y.2
        ≤ (Work.Spaces.DzIter (i + 1) f (zShift z (y.2 * y.1.1))
              (thShift θ (y.2 * y.1.2))
            * wE (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2))) ^ 2
          + 1 / 4 * (Work.Spaces.mixed i 1 f (zShift z (y.2 * y.1.1))
              (thShift θ (y.2 * y.1.2))
            * Work.Spaces.Wt α (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2))) ^ 2 := by
    intro i _
    have hcomm := Work.FTS.EllipticEst.ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen
      isOpen_Quad hf i 1 hsQ
    have hDth : Work.Spaces.Dth (Work.Spaces.DzIter i f) (zShift z (y.2 * y.1.1))
        (thShift θ (y.2 * y.1.2)) = Work.Spaces.mixed i 1 f (zShift z (y.2 * y.1.1))
          (thShift θ (y.2 * y.1.2)) := hcomm
    have hle : wE (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2))
        ≤ Work.Spaces.Wt α (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2)) :=
      wE_le_Wt (z := zShift z (y.2 * y.1.1)) hα hsQ.2
    have hnn : 0 ≤ wE (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2)) :=
      wE_nonneg hsQ.2
    rw [bracket, ← Work.Spaces.DzIter_succ, hDth]
    have h2 : (wE (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2))
        * Work.Spaces.mixed i 1 f (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2))) ^ 2
        ≤ (Work.Spaces.mixed i 1 f (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2))
          * Work.Spaces.Wt α (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2))) ^ 2 := by
      calc (wE (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2))
            * Work.Spaces.mixed i 1 f (zShift z (y.2 * y.1.1))
              (thShift θ (y.2 * y.1.2))) ^ 2
          = (Work.Spaces.mixed i 1 f (zShift z (y.2 * y.1.1))
              (thShift θ (y.2 * y.1.2))) ^ 2
            * (wE (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2))) ^ 2 := by ring
        _ ≤ (Work.Spaces.mixed i 1 f (zShift z (y.2 * y.1.1))
              (thShift θ (y.2 * y.1.2))) ^ 2
            * (Work.Spaces.Wt α (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2))) ^ 2 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnn hle 2) (sq_nonneg _)
        _ = (Work.Spaces.mixed i 1 f (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2))
            * Work.Spaces.Wt α (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2))) ^ 2 := by ring
    have h3 : (wE (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2))
        * Work.Spaces.DzIter (i + 1) f (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2))) ^ 2
        = (Work.Spaces.DzIter (i + 1) f (zShift z (y.2 * y.1.1))
            (thShift θ (y.2 * y.1.2))
          * wE (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2))) ^ 2 := by rw [mul_comm]
    rw [h3]
    linarith [h2]
  have h2 : ∀ q ∈ slots k,
      bracket (Work.Spaces.mixed q.2 q.1 f) (Work.Spaces.Wt α) z θ y.1 y.2
        ≤ (Work.Spaces.mixed (q.2 + 1) q.1 f (zShift z (y.2 * y.1.1))
              (thShift θ (y.2 * y.1.2))
            * Work.Spaces.Wt α (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2))) ^ 2
          + 1 / 4 * (Work.Spaces.mixed q.2 (q.1 + 1) f (zShift z (y.2 * y.1.1))
              (thShift θ (y.2 * y.1.2))
            * Work.Spaces.Wt α (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2))) ^ 2 := by
    intro q _
    have hcomm := Work.FTS.EllipticEst.ThetaU.OpenSliceAux.Dth_DzIter_eqOn_of_smooth
      isOpen_Quad ((Work.FTS.StrongEps.smQ_of_forall_nat hf).DthIter q.1) q.2 hsQ
    have hDth : Work.Spaces.Dth (Work.Spaces.mixed q.2 q.1 f)
        (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2))
        = Work.Spaces.mixed q.2 (q.1 + 1) f (zShift z (y.2 * y.1.1))
          (thShift θ (y.2 * y.1.2)) := hcomm
    rw [bracket,
      show Work.Spaces.Dz (Work.Spaces.mixed q.2 q.1 f) = Work.Spaces.mixed (q.2 + 1) q.1 f
        from rfl,
      hDth]
    exact le_of_eq (by ring)
  have hsum1 := Finset.sum_le_sum h1
  have hsum2 := Finset.sum_le_sum h2
  have hsum1' : (∑ i ∈ Finset.range (k + 1), bracket (Work.Spaces.DzIter i f) wE z θ y.1 y.2)
      ≤ (∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter (i + 1) f (zShift z (y.2 * y.1.1))
              (thShift θ (y.2 * y.1.2))
            * wE (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2))) ^ 2)
        + 1 / 4 * (∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.mixed i 1 f (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2))
              * Work.Spaces.Wt α (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2))) ^ 2) := by
    have := hsum1
    rwa [Finset.sum_add_distrib, ← Finset.mul_sum] at this
  have hsum2' : (∑ q ∈ slots k,
        bracket (Work.Spaces.mixed q.2 q.1 f) (Work.Spaces.Wt α) z θ y.1 y.2)
      ≤ (∑ q ∈ slots k, (Work.Spaces.mixed (q.2 + 1) q.1 f (zShift z (y.2 * y.1.1))
              (thShift θ (y.2 * y.1.2))
            * Work.Spaces.Wt α (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2))) ^ 2)
        + 1 / 4 * (∑ q ∈ slots k,
            (Work.Spaces.mixed q.2 (q.1 + 1) f (zShift z (y.2 * y.1.1))
              (thShift θ (y.2 * y.1.2))
              * Work.Spaces.Wt α (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2))) ^ 2) := by
    have := hsum2
    rwa [Finset.sum_add_distrib, ← Finset.mul_sum] at this
  rw [shadow]
  linarith [hsum1', hsum2']


end Work.FTS.StrongEps.DiffAux
