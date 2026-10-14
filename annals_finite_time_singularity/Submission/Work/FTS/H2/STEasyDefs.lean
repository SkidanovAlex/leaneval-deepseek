import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.H2.STEasy
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.StabilityFar.Decay.KernelDefs
import Submission.Work.StabilityFar.Decay.timeDeriv_eq_zero_of_notMem_closedBall
-- ===== merged: Submission.Work.FTS.BSSwirl.biotSavart_eq_vorticity_newtonPotential =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory
open scoped Matrix Topology
open Work.StabilityFar.Decay (crossL)

set_option autoImplicit false

namespace Work.FTS.BSSwirl

theorem biotSavart_eq_vorticity_newtonPotential {ω : Work.FTS.BSSwirl.R3 → Work.FTS.BSSwirl.R3}
    {R M : ℝ} (hM : 0 ≤ M) (hbdd : ∀ y, ‖ω y‖ ≤ M)
    (hsupp : ∀ y, ω y ≠ 0 → y ∈ Metric.closedBall 0 R)
    (hmeas : MeasureTheory.AEStronglyMeasurable ω MeasureTheory.volume)
    (hd : ∀ x, HasFDerivAt (Work.FTS.BSSwirl.newtonPotential ω) (Work.FTS.BSSwirl.potDeriv ω x) x)
    (x : Work.FTS.BSSwirl.R3) :
    Work.LWP.biotSavart ω x
      = FiniteTimeSingularity.vorticity (Work.FTS.BSSwirl.newtonPotential ω) x := by
  -- `ofLp`/`toLp` commute with Bochner integrals (unconditional for continuous linear
  -- equivalences)
  have ofLp_integral : ∀ f : R3 → R3, (∫ y, f y).ofLp = ∫ y, (f y).ofLp := by
    intro f
    have hL : ∀ v : R3, (EuclideanSpace.equiv (Fin 3) ℝ) v = v.ofLp := fun v => rfl
    have h := ContinuousLinearEquiv.integral_comp_comm (μ := volume) (EuclideanSpace.equiv (Fin 3) ℝ) f
    simpa only [hL] using h.symm
  have toLp_integral : ∀ f : R3 → Fin 3 → ℝ,
      (∫ y, WithLp.toLp 2 (f y)) = WithLp.toLp 2 (∫ y, f y) := by
    intro f
    have hL : ∀ v : Fin 3 → ℝ, (EuclideanSpace.equiv (Fin 3) ℝ).symm v = WithLp.toLp 2 v :=
      fun v => rfl
    have h := ContinuousLinearEquiv.integral_comp_comm (μ := volume)
      ((EuclideanSpace.equiv (Fin 3) ℝ).symm) f
    simpa only [hL] using h
  have hderiv : fderiv ℝ (newtonPotential ω) x = potDeriv ω x := (hd x).fderiv
  -- the Fréchet derivative integrand is Bochner integrable
  have hintCLM : Integrable
      (fun y : R3 => ((‖x - y‖ ^ (3:ℕ))⁻¹ : ℝ) • (innerSL ℝ (y - x)).smulRight (ω y))
      volume := integrable_inv_cube_smulRight hM hbdd hsupp hmeas x
  -- (A) the value of the derivative on the standard basis `e i`
  have hPot : ∀ i : Fin 3, potDeriv ω x (FiniteTimeSingularity.e i)
      = (4 * Real.pi)⁻¹ • ∫ y : R3,
          ((‖x - y‖ ^ (3:ℕ))⁻¹ : ℝ) • (inner ℝ (y - x) (FiniteTimeSingularity.e i) • ω y) := by
    intro i
    rw [potDeriv, ContinuousLinearMap.smul_apply]
    rw [ContinuousLinearMap.integral_apply hintCLM]
    refine congrArg (fun t => (4 * Real.pi)⁻¹ • t) ?_
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro y
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
      innerSL_apply_apply]
  -- (B) the curl of the Newtonian potential
  have hRHS : FiniteTimeSingularity.vorticity (newtonPotential ω) x
      = WithLp.toLp 2 (∑ i : Fin 3,
          (FiniteTimeSingularity.e i).ofLp ⨯₃ ((potDeriv ω x (FiniteTimeSingularity.e i)).ofLp)) := by
    rw [FiniteTimeSingularity.vorticity, hderiv]
  -- (C) the Biot–Savart field
  have hLHS : Work.LWP.biotSavart ω x
      = WithLp.toLp 2 ((4 * Real.pi)⁻¹ • ∫ y : R3,
          ((‖x - y‖ ^ (3:ℕ))⁻¹ : ℝ) • crossProduct (ω y).ofLp (x.ofLp - y.ofLp)) := by
    rw [Work.LWP.biotSavart]
    rw [toLp_integral (fun y : R3 => ((‖x - y‖ ^ (3:ℕ))⁻¹ : ℝ) •
      crossProduct (ω y).ofLp (x.ofLp - y.ofLp)), WithLp.toLp_smul]
  let G : Fin 3 → R3 → R3 := fun i y =>
    ((‖x - y‖ ^ (3:ℕ))⁻¹ : ℝ) • (inner ℝ (y - x) (FiniteTimeSingularity.e i) • ω y)
  let Φ : Fin 3 → R3 → R3 := fun i y => (4 * Real.pi)⁻¹ • G i y
  have hIntG : ∀ i : Fin 3, Integrable (G i) volume := by
    intro i
    dsimp only [G]
    exact integrable_inv_cube_inner_smul hM hbdd hsupp hmeas x (FiniteTimeSingularity.e i)
  have hIntΦ : ∀ i : Fin 3, Integrable (Φ i) volume := by
    intro i
    dsimp only [Φ]
    exact (hIntG i).smul (4 * Real.pi)⁻¹
  have hPot' : ∀ i : Fin 3, potDeriv ω x (FiniteTimeSingularity.e i) = ∫ y : R3, Φ i y := by
    intro i
    rw [hPot i, ← MeasureTheory.integral_smul]
  -- (D) `crossL (e i)` commutes with the integral, and summing over the basis produces
  --     the cross product with `x - y`
  have hsummand : ∀ i : Fin 3,
      (FiniteTimeSingularity.e i).ofLp ⨯₃ ((potDeriv ω x (FiniteTimeSingularity.e i)).ofLp)
        = ∫ y : R3, (FiniteTimeSingularity.e i).ofLp ⨯₃ ((Φ i y).ofLp) := by
    intro i
    calc (FiniteTimeSingularity.e i).ofLp ⨯₃ ((potDeriv ω x (FiniteTimeSingularity.e i)).ofLp)
        = (FiniteTimeSingularity.e i).ofLp ⨯₃ ((∫ y : R3, Φ i y).ofLp) := by rw [hPot' i]
      _ = (crossL (FiniteTimeSingularity.e i) (∫ y : R3, Φ i y)).ofLp := by
            rw [Work.StabilityFar.Decay.crossL_apply, WithLp.ofLp_toLp]
      _ = (∫ y : R3, crossL (FiniteTimeSingularity.e i) (Φ i y)).ofLp := by
            rw [← ContinuousLinearMap.integral_comp_comm (crossL (FiniteTimeSingularity.e i))
              (hIntΦ i)]
      _ = ∫ y : R3, (crossL (FiniteTimeSingularity.e i) (Φ i y)).ofLp := ofLp_integral _
      _ = ∫ y : R3, (FiniteTimeSingularity.e i).ofLp ⨯₃ ((Φ i y).ofLp) := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with y
            rw [Work.StabilityFar.Decay.crossL_apply, WithLp.ofLp_toLp]
  have hIntSum : ∀ i : Fin 3, Integrable
      (fun y : R3 => (FiniteTimeSingularity.e i).ofLp ⨯₃ ((Φ i y).ofLp)) volume := by
    intro i
    have h1 : Integrable (fun y : R3 => crossL (FiniteTimeSingularity.e i) (Φ i y)) volume :=
      (crossL (FiniteTimeSingularity.e i)).integrable_comp (hIntΦ i)
    have h2 : Integrable
        (fun y : R3 => (crossL (FiniteTimeSingularity.e i) (Φ i y)).ofLp) volume :=
      (ContinuousLinearEquiv.integrable_comp_iff (EuclideanSpace.equiv (Fin 3) ℝ)).mpr h1
    simpa only [Work.StabilityFar.Decay.crossL_apply, WithLp.ofLp_toLp] using h2
  have hstep1 : (∑ i : Fin 3,
        (FiniteTimeSingularity.e i).ofLp ⨯₃ ((potDeriv ω x (FiniteTimeSingularity.e i)).ofLp))
      = ∑ i : Fin 3, ∫ y : R3, (FiniteTimeSingularity.e i).ofLp ⨯₃ ((Φ i y).ofLp) :=
    Finset.sum_congr rfl (fun i _ => hsummand i)
  have hstep2 : (∑ i : Fin 3, ∫ y : R3, (FiniteTimeSingularity.e i).ofLp ⨯₃ ((Φ i y).ofLp))
      = ∫ y : R3, ∑ i : Fin 3, (FiniteTimeSingularity.e i).ofLp ⨯₃ ((Φ i y).ofLp) := by
    rw [MeasureTheory.integral_finsetSum Finset.univ (fun i _ => hIntSum i)]
  have hpt : ∀ y : R3, (∑ i : Fin 3,
        (FiniteTimeSingularity.e i).ofLp ⨯₃ ((Φ i y).ofLp))
      = ((4 * Real.pi)⁻¹ * (‖x - y‖ ^ (3:ℕ))⁻¹) • crossProduct (ω y).ofLp (x.ofLp - y.ofLp) := by
    intro y
    have hΦ : ∀ i : Fin 3, (Φ i y).ofLp
        = ((4 * Real.pi)⁻¹ * (‖x - y‖ ^ (3:ℕ))⁻¹) •
            (inner ℝ (y - x) (FiniteTimeSingularity.e i) • (ω y).ofLp) := by
      intro i
      dsimp only [Φ, G]
      simp only [WithLp.ofLp_smul, smul_smul, mul_assoc]
    calc (∑ i : Fin 3, (FiniteTimeSingularity.e i).ofLp ⨯₃ ((Φ i y).ofLp))
        = ∑ i : Fin 3, crossProduct ((FiniteTimeSingularity.e i).ofLp)
            (((4 * Real.pi)⁻¹ * (‖x - y‖ ^ (3:ℕ))⁻¹) •
              (inner ℝ (y - x) (FiniteTimeSingularity.e i) • (ω y).ofLp)) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hΦ i]
      _ = ((4 * Real.pi)⁻¹ * (‖x - y‖ ^ (3:ℕ))⁻¹) •
            crossProduct (ω y).ofLp (x.ofLp - y.ofLp) := by
          simpa only [WithLp.ofLp_sub] using
            sum_e_cross_eq x y (ω y) ((4 * Real.pi)⁻¹ * (‖x - y‖ ^ (3:ℕ))⁻¹)
  have hstep3 : (∫ y : R3, ∑ i : Fin 3, (FiniteTimeSingularity.e i).ofLp ⨯₃ ((Φ i y).ofLp))
      = (4 * Real.pi)⁻¹ • ∫ y : R3,
          ((‖x - y‖ ^ (3:ℕ))⁻¹ : ℝ) • crossProduct (ω y).ofLp (x.ofLp - y.ofLp) := by
    rw [show (∫ y : R3, ∑ i : Fin 3, (FiniteTimeSingularity.e i).ofLp ⨯₃ ((Φ i y).ofLp))
        = ∫ y : R3, ((4 * Real.pi)⁻¹ * (‖x - y‖ ^ (3:ℕ))⁻¹) •
            crossProduct (ω y).ofLp (x.ofLp - y.ofLp) from
          MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
    rw [← MeasureTheory.integral_smul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with y
    rw [smul_smul]
  have hchain : (∑ i : Fin 3,
        (FiniteTimeSingularity.e i).ofLp ⨯₃ ((potDeriv ω x (FiniteTimeSingularity.e i)).ofLp))
      = (4 * Real.pi)⁻¹ • ∫ y : R3,
          ((‖x - y‖ ^ (3:ℕ))⁻¹ : ℝ) • crossProduct (ω y).ofLp (x.ofLp - y.ofLp) :=
    hstep1.trans (hstep2.trans hstep3)
  calc Work.LWP.biotSavart ω x
      = WithLp.toLp 2 ((4 * Real.pi)⁻¹ • ∫ y : R3,
          ((‖x - y‖ ^ (3:ℕ))⁻¹ : ℝ) • crossProduct (ω y).ofLp (x.ofLp - y.ofLp)) := hLHS
    _ = WithLp.toLp 2 (∑ i : Fin 3,
          (FiniteTimeSingularity.e i).ofLp ⨯₃ ((potDeriv ω x (FiniteTimeSingularity.e i)).ofLp)) :=
        congrArg (WithLp.toLp 2) hchain.symm
    _ = FiniteTimeSingularity.vorticity (newtonPotential ω) x := hRHS.symm

end Work.FTS.BSSwirl
end
-- ===== merged: Submission.Work.FTS.H2.STEasyDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false
set_option maxHeartbeats 4000000





end Work.FTS.H2
end
end
