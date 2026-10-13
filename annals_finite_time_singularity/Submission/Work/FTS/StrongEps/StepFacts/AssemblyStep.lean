/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/StepFacts/AssemblyStep.lean`

The assembly of the **one-order smoothing estimate** for the log-coordinate mollifier `J_ε`:

  `HkSq α m (J_ε u) ≤ C (ε⁻¹)² HkSq α (m-1) u`

for `2 ≤ m ≤ 8`, from

* the pointwise step `step_pointwise` (level-`m` integrand of `J_ε u` against the density `Ψ`
  and the level-`m-1` integrand of `u`),
* the generic chain `HkSq_step_of_pointwise` (Tonelli + the log-coordinate shift comparison
  `logJac_shift_le`),
* the moment bound `Psi_mass` for the density `Ψ`.

The constant is `C = Bconst ρ · Dmass ρ (2 max cη cγ + δ) + 1`, i.e. an explicit `ρ`-dependent
positive real (the `+ 1` makes positivity unconditional).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.StrongEps.HkMem_Jeps
import Submission.Work.FTS.StrongEps.HkSqAux.wdiv_shift_le
import Submission.Work.FTS.StrongEps.HkSqAux.Wt_shift_le
import Submission.Work.FTS.StrongEps.HkSqAux.logJac_shift_le
import Submission.Work.FTS.StrongEps.HkSqAux.continuousOn_HkIntegrand_Quad
import Submission.Work.FTS.StrongEps.StepFacts.KernelFacts
import Submission.Work.FTS.StrongEps.StepFacts.StepPointwise
import Submission.Work.FTS.StrongEps.StepFacts.HkSq_step_of_pointwise
import Submission.Work.FTS.StrongEps.StepFacts.HkMem_Jeps_step

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.StepFacts

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- `Dmass` is nonnegative (it is the integral of a nonnegative function). -/
theorem Dmass_nonneg (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ) (γ : ℝ) :
    0 ≤ Dmass ρ γ :=
  integral_nonneg fun t => mul_nonneg (rhoTilde_nonneg ρ hρ.moll.nonneg t) (Real.exp_pos _).le

/-- `ofReal` is multiplicative on nonnegative triples (in the product shape used below). -/
theorem ofReal_mul3 {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    ENNReal.ofReal a * ENNReal.ofReal b * ENNReal.ofReal c = ENNReal.ofReal (a * b * c) := by
  rw [← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul (mul_nonneg ha hb)]

/-- **The one-order smoothing estimate of `J_ε` in the weighted `H^k`-norms** — the auxiliary
form of `Work.FTS.StrongEps.HkSq_Jeps_step_le`, with the same statement. -/
theorem step_le_aux (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 → ∀ m : ℕ, 2 ≤ m → m ≤ 8 →
      ∀ ε : ℝ, ε ∈ Set.Ioc 0 1 → ∀ u : ℝ → ℝ → ℝ,
        (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) Work.FTS.StrongEps.Quad) →
        Work.Spaces.HkMem α (m - 1) u →
        Work.Spaces.HkMem α m (Work.FTS.StrongEps.Jeps ρ ε u) ∧
          Work.Spaces.HkSq α m (Work.FTS.StrongEps.Jeps ρ ε u)
            ≤ C * (ε⁻¹) ^ 2 * Work.Spaces.HkSq α (m - 1) u := by
  obtain ⟨cη, hcη, hWη0⟩ := HkSqAux.wdiv_shift_le
  obtain ⟨cγ, hcγ, hWγ0⟩ := HkSqAux.Wt_shift_le
  obtain ⟨δ, hδ, hJac0⟩ := HkSqAux.logJac_shift_le
  refine ⟨Bconst ρ * Dmass ρ (2 * max cη cγ + δ) + 1, ?_, ?_⟩
  · have h1 : 0 < Bconst ρ := Bconst_pos ρ
    have h2 : 0 ≤ Dmass ρ (2 * max cη cγ + δ) := Dmass_nonneg ρ hρ _
    have h3 : 0 ≤ Bconst ρ * Dmass ρ (2 * max cη cγ + δ) := mul_nonneg h1.le h2
    linarith
  intro α hα m hm hm8 ε hεI u hu hMem
  obtain ⟨hε, hε1⟩ := hεI
  have hcη' : 0 < max cη cγ := lt_of_lt_of_le hcη (le_max_left _ _)
  have hc : (0 : ℝ) ≤ max cη cγ := hcη'.le
  have hγ : (0 : ℝ) ≤ 2 * max cη cγ + δ := by linarith
  have hMemJ : Work.Spaces.HkMem α m (Work.FTS.StrongEps.Jeps ρ ε u) :=
    HkMem_Jeps_step ρ hρ hα hm hm8 hε hε1 hu hMem
  refine ⟨hMemJ, ?_⟩
  -- the two weight-shift comparisons with the common constant `max cη cγ`
  have hWη : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → ∀ p : ℝ × ℝ,
      Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
        ≤ Real.exp (max cη cγ * (|p.1| + |p.2|))
          * (Work.Spaces.w (Work.FTS.StrongEps.zShift z p.1)
              / (Real.sin (2 * Work.FTS.StrongEps.thShift θ p.2)) ^ (Work.Spaces.eta / 2)) := by
    intro z θ hz hθ p
    refine (hWη0 z θ p.1 p.2 hz hθ).trans (mul_le_mul_of_nonneg_right ?_ ?_)
    · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    · exact div_nonneg (Work.FTS.StrongEps.w_nonneg _)
        (Real.rpow_nonneg (le_of_lt (sin_two_pos (thShift_mem hθ))) _)
  have hWγ : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → ∀ p : ℝ × ℝ,
      Work.Spaces.Wt α z θ ≤ Real.exp (max cη cγ * (|p.1| + |p.2|))
        * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2) := by
    intro z θ hz hθ p
    exact (hWγ0 α hα z θ p.1 p.2 hz hθ).trans (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)))
      (mul_nonneg (Work.FTS.StrongEps.w_nonneg _)
        (Real.rpow_nonneg (le_of_lt (sin_two_pos (thShift_mem hθ))) _)))
  -- the pointwise step, extended to the closed quadrant (the integrand vanishes on the boundary)
  have hP : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      ENNReal.ofReal (Work.Spaces.HkIntegrand α m (Work.FTS.StrongEps.Jeps ρ ε u) z θ)
        ≤ ENNReal.ofReal (ε⁻¹ * Bconst ρ) * ∫⁻ p : ℝ × ℝ,
            ENNReal.ofReal (Psi ρ ε p)
              * ENNReal.ofReal (Real.exp (2 * max cη cγ * (|p.1| + |p.2|)))
              * ENNReal.ofReal (Work.Spaces.HkIntegrand α (m - 1) u
                  (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) := by
    intro z hz θ hθ
    by_cases hq : 0 < z ∧ θ ∈ Set.Ioo 0 (π / 2)
    · exact step_pointwise ρ hρ hε hε1 hα hm hm8 hu hWη hWγ hq.1 hq.2
    · have hzero : Work.Spaces.HkIntegrand α m (Work.FTS.StrongEps.Jeps ρ ε u) z θ = 0 :=
        HkSqAux.HkIntegrand_boundary_zero hα hz hθ hq
      rw [hzero, ENNReal.ofReal_zero]
      exact zero_le
  have hAe : AEMeasurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      ENNReal.ofReal (Psi ρ ε q.2)
        * ENNReal.ofReal (Real.exp (2 * max cη cγ * (|q.2.1| + |q.2.2|)))
        * ENNReal.ofReal (Work.Spaces.HkIntegrand α (m - 1) u
            (Work.FTS.StrongEps.zShift q.1.1 q.2.1)
            (Work.FTS.StrongEps.thShift q.1.2 q.2.2)))
      (((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)).prod MeasureTheory.volume) :=
    aemeasurable_Psi_shift (ρ := ρ) (ε := ε) (c := max cη cγ) (α := α) (k := m - 1) (u := u) hρ
      (HkSqAux.continuousOn_HkIntegrand_Quad α (m - 1) hu)
  -- the generic chain
  have hmain := HkSq_step_of_pointwise (ρ := ρ) (α := α) (c := max cη cγ) (δ := δ)
    (B := Bconst ρ) (ε := ε) (m := m) (by omega) (u := u) (Ψ := Psi ρ ε)
    hc hδ.le hMemJ hMem hu hAe hP (fun s ζ p₁ p₂ => hJac0 s ζ p₁ p₂)
  -- the moment bound for the density
  have hmom : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Psi ρ ε p
        * Real.exp ((2 * max cη cγ + δ) * (|p.1| + |p.2|))))
      ≤ ENNReal.ofReal (ε⁻¹ * Dmass ρ (2 * max cη cγ + δ)) := by
    have hint := Psi_moment_integrable ρ hρ hε hε1 hγ
    refine (le_of_eq (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun p =>
        mul_nonneg (Psi_nonneg ρ hρ hε p) (Real.exp_pos _).le)).symm).trans ?_
    exact ENNReal.ofReal_le_ofReal (Psi_mass ρ hρ hε hε1 hγ)
  -- the final assembly
  have h1 : 0 ≤ ε⁻¹ * Bconst ρ := mul_nonneg (by positivity) (Bconst_pos ρ).le
  have h2 : 0 ≤ ε⁻¹ * Dmass ρ (2 * max cη cγ + δ) := by
    exact mul_nonneg (by positivity) (Dmass_nonneg ρ hρ _)
  have hBD : 0 ≤ Bconst ρ * Dmass ρ (2 * max cη cγ + δ) :=
    mul_nonneg (Bconst_pos ρ).le (Dmass_nonneg ρ hρ _)
  have hH : 0 ≤ Work.Spaces.HkSq α (m - 1) u := Work.Spaces.HkSq_nonneg α (m - 1) u
  have hfinal : ENNReal.ofReal (Work.Spaces.HkSq α m (Work.FTS.StrongEps.Jeps ρ ε u))
      ≤ ENNReal.ofReal ((Bconst ρ * Dmass ρ (2 * max cη cγ + δ) + 1) * (ε⁻¹) ^ 2
          * Work.Spaces.HkSq α (m - 1) u) := by
    refine hmain.trans ?_
    calc ENNReal.ofReal (ε⁻¹ * Bconst ρ)
          * (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Psi ρ ε p
              * Real.exp ((2 * max cη cγ + δ) * (|p.1| + |p.2|))))
          * ENNReal.ofReal (Work.Spaces.HkSq α (m - 1) u)
        ≤ ENNReal.ofReal (ε⁻¹ * Bconst ρ)
            * ENNReal.ofReal (ε⁻¹ * Dmass ρ (2 * max cη cγ + δ))
            * ENNReal.ofReal (Work.Spaces.HkSq α (m - 1) u) :=
          mul_le_mul_left (mul_le_mul_right hmom (ENNReal.ofReal (ε⁻¹ * Bconst ρ))) _
      _ = ENNReal.ofReal ((ε⁻¹ * Bconst ρ) * (ε⁻¹ * Dmass ρ (2 * max cη cγ + δ))
            * Work.Spaces.HkSq α (m - 1) u) :=
          ofReal_mul3 h1 h2 hH
      _ ≤ ENNReal.ofReal ((Bconst ρ * Dmass ρ (2 * max cη cγ + δ) + 1) * (ε⁻¹) ^ 2
            * Work.Spaces.HkSq α (m - 1) u) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hsq : 0 ≤ (ε⁻¹) ^ 2 := sq_nonneg _
          calc (ε⁻¹ * Bconst ρ) * (ε⁻¹ * Dmass ρ (2 * max cη cγ + δ))
                * Work.Spaces.HkSq α (m - 1) u
              = (Bconst ρ * Dmass ρ (2 * max cη cγ + δ))
                  * ((ε⁻¹) ^ 2 * Work.Spaces.HkSq α (m - 1) u) := by ring
            _ ≤ (Bconst ρ * Dmass ρ (2 * max cη cγ + δ) + 1)
                  * ((ε⁻¹) ^ 2 * Work.Spaces.HkSq α (m - 1) u) :=
                mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hsq hH)
            _ = (Bconst ρ * Dmass ρ (2 * max cη cγ + δ) + 1) * (ε⁻¹) ^ 2
                  * Work.Spaces.HkSq α (m - 1) u := by ring
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hfinal

end Work.FTS.StrongEps.StepFacts
