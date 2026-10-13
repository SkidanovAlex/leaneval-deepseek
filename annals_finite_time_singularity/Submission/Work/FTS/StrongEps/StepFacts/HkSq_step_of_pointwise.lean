import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.HkSqAux.Defs
import Submission.Work.FTS.StrongEps.HkSqAux.Chain
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.StepFacts

set_option maxHeartbeats 1000000

-- context: namespace Work.FTS.StrongEps.StepFacts. `HkSq α k f = ∫z∈Iz ∫θ∈Iθ HkIntegrand α k f z θ`, `Jeps ρ ε` the
-- log-coordinate mollifier, `zShift z p = z*exp(-p)`, `thShift θ p = arctan(tan θ * exp(-p))`, `Iz = [0,∞)`, `Iθ = [0,π/2]`,
-- `logJac s ζ = exp s * kappa ζ` the Jacobian of the log substitution. `hP` is a pointwise bound on the
-- level-`m` integrand of `Jeps ρ ε u` by an average of the level-`m-1` integrand of `u` against a density `Ψ`.
-- The proof should mirror `Work.FTS.StrongEps.HkSqAux.ofReal_HkSq_Jeps_le` in `HkSqAux/Chain.lean`, using the proved
-- `Work.FTS.StrongEps.HkSqAux.integral_shift_le` for the shift step and `Work.FTS.StrongEps.HkSqAux.continuousOn_HkIntegrand_Quad` for continuity.
theorem HkSq_step_of_pointwise
    {ρ : ℝ × ℝ → ℝ} {α c δ B ε : ℝ} {m : ℕ} (hm : 1 ≤ m)
    {u : ℝ → ℝ → ℝ} {Ψ : ℝ × ℝ → ℝ}
    (hc : 0 ≤ c) (hδ : 0 ≤ δ)
    (hMemJ : Work.Spaces.HkMem α m (Work.FTS.StrongEps.Jeps ρ ε u))
    (hMem : Work.Spaces.HkMem α (m - 1) u)
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) Work.FTS.StrongEps.Quad)
    (hAe : AEMeasurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
        ENNReal.ofReal (Ψ q.2) * ENNReal.ofReal (Real.exp (2 * c * (|q.2.1| + |q.2.2|)))
          * ENNReal.ofReal (Work.Spaces.HkIntegrand α (m - 1) u
              (Work.FTS.StrongEps.zShift q.1.1 q.2.1)
              (Work.FTS.StrongEps.thShift q.1.2 q.2.2)))
        (((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)).prod MeasureTheory.volume))
    (hP : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α m (Work.FTS.StrongEps.Jeps ρ ε u) z θ)
          ≤ ENNReal.ofReal (ε⁻¹ * B) * ∫⁻ p : ℝ × ℝ,
              ENNReal.ofReal (Ψ p) * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
                * ENNReal.ofReal (Work.Spaces.HkIntegrand α (m - 1) u
                    (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2)))
    (hJac : ∀ s ζ p₁ p₂ : ℝ, Work.FTS.StrongEps.HkSqAux.logJac s ζ
      ≤ Real.exp (δ * (|p₁| + |p₂|)) * Work.FTS.StrongEps.HkSqAux.logJac (s - p₁) (ζ - p₂)) :
    ENNReal.ofReal (Work.Spaces.HkSq α m (Work.FTS.StrongEps.Jeps ρ ε u))
      ≤ ENNReal.ofReal (ε⁻¹ * B)
          * (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Ψ p * Real.exp ((2 * c + δ) * (|p.1| + |p.2|))))
          * ENNReal.ofReal (Work.Spaces.HkSq α (m - 1) u) := by
  have hcont : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.HkIntegrand α (m - 1) u q.1 q.2)
      Work.FTS.StrongEps.Quad :=
    Work.FTS.StrongEps.HkSqAux.continuousOn_HkIntegrand_Quad α (m - 1) hu
  -- (1) the weighted `L²`-integral of `J_ε u` as an iterated `lintegral` of its `H^m`-integrand
  have h1 : ENNReal.ofReal (Work.Spaces.HkSq α m (Work.FTS.StrongEps.Jeps ρ ε u))
      = ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α m (Work.FTS.StrongEps.Jeps ρ ε u) z θ) := by
    rw [Work.Spaces.HkSq]
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hMemJ.2
      (Eventually.of_forall fun z => integral_nonneg fun θ =>
        Work.Spaces.HkIntegrand_nonneg α m (Work.FTS.StrongEps.Jeps ρ ε u) z θ)]
    exact MeasureTheory.setLIntegral_congr_fun (by rw [Work.Spaces.Iz]; exact measurableSet_Ici)
      (fun z hz => MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hMemJ.1 z hz)
        (Eventually.of_forall fun θ =>
          Work.Spaces.HkIntegrand_nonneg α m (Work.FTS.StrongEps.Jeps ρ ε u) z θ))
  -- (2) the pointwise bound `hP`, integrated
  have h2 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α m (Work.FTS.StrongEps.Jeps ρ ε u) z θ))
      ≤ ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (ε⁻¹ * B) * ∫⁻ p : ℝ × ℝ,
          ENNReal.ofReal (Ψ p) * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
            * ENNReal.ofReal (Work.Spaces.HkIntegrand α (m - 1) u
                (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) := by
    refine MeasureTheory.setLIntegral_mono' (by rw [Work.Spaces.Iz]; exact measurableSet_Ici)
      fun z hz => MeasureTheory.setLIntegral_mono' (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc)
      fun θ hθ => hP z hz θ hθ
  -- (3) the constant `ε⁻¹ B` comes out of the two integrals
  have h3 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (ε⁻¹ * B) * ∫⁻ p : ℝ × ℝ,
          ENNReal.ofReal (Ψ p) * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
            * ENNReal.ofReal (Work.Spaces.HkIntegrand α (m - 1) u
                (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)))
      = ENNReal.ofReal (ε⁻¹ * B) * (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ p : ℝ × ℝ,
          ENNReal.ofReal (Ψ p) * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
            * ENNReal.ofReal (Work.Spaces.HkIntegrand α (m - 1) u
                (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2))) := by
    have hinner : ∀ z : ℝ, (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (ε⁻¹ * B) * ∫⁻ p : ℝ × ℝ,
          ENNReal.ofReal (Ψ p) * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
            * ENNReal.ofReal (Work.Spaces.HkIntegrand α (m - 1) u
                (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)))
        = ENNReal.ofReal (ε⁻¹ * B) * ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ p : ℝ × ℝ,
          ENNReal.ofReal (Ψ p) * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
            * ENNReal.ofReal (Work.Spaces.HkIntegrand α (m - 1) u
                (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) :=
      fun z => MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    simp only [hinner]
    rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  -- (4) Tonelli: the `p`-integration is exchanged with the `(z,θ)`-integration
  have h4 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ p : ℝ × ℝ,
        ENNReal.ofReal (Ψ p) * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
          * ENNReal.ofReal (Work.Spaces.HkIntegrand α (m - 1) u
              (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)))
      = ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Ψ p) * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
          * (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal (Work.Spaces.HkIntegrand α (m - 1) u
                (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2))) := by
    have hL : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ p : ℝ × ℝ,
        ENNReal.ofReal (Ψ p) * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
          * ENNReal.ofReal (Work.Spaces.HkIntegrand α (m - 1) u
              (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)))
        = ∫⁻ q : ℝ × ℝ, ∫⁻ p : ℝ × ℝ,
            ENNReal.ofReal (Ψ p) * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
              * ENNReal.ofReal (Work.Spaces.HkIntegrand α (m - 1) u
                  (Work.FTS.StrongEps.zShift q.1 p.1) (Work.FTS.StrongEps.thShift q.2 p.2))
          ∂volume ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
      rw [show ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))
          = (volume.prod volume).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) from
        Measure.prod_restrict _ _]
      exact (MeasureTheory.setLIntegral_prod (fun q : ℝ × ℝ => ∫⁻ p : ℝ × ℝ,
          ENNReal.ofReal (Ψ p) * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
            * ENNReal.ofReal (Work.Spaces.HkIntegrand α (m - 1) u
                (Work.FTS.StrongEps.zShift q.1 p.1) (Work.FTS.StrongEps.thShift q.2 p.2)))
        (s := Work.Spaces.Iz) (t := Work.Spaces.Iθ) (by
          rw [← Measure.prod_restrict (μ := volume) (ν := volume) _ _]
          exact hAe.lintegral_prod_right')).symm
    rw [hL]
    rw [MeasureTheory.lintegral_lintegral_swap (μ := (volume.restrict Work.Spaces.Iz).prod
      (volume.restrict Work.Spaces.Iθ)) (ν := volume) hAe]
    refine lintegral_congr fun p => ?_
    rw [MeasureTheory.lintegral_const_mul' _ _
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
    have hAB : (∫⁻ q : ℝ × ℝ, ENNReal.ofReal (Work.Spaces.HkIntegrand α (m - 1) u
          (Work.FTS.StrongEps.zShift q.1 p.1) (Work.FTS.StrongEps.thShift q.2 p.2))
        ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)))
        = ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
            (Work.Spaces.HkIntegrand α (m - 1) u (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2)) := by
      rw [show ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))
          = (volume.prod volume).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) from
        Measure.prod_restrict _ _]
      exact MeasureTheory.setLIntegral_prod (fun q : ℝ × ℝ => ENNReal.ofReal
        (Work.Spaces.HkIntegrand α (m - 1) u (Work.FTS.StrongEps.zShift q.1 p.1)
          (Work.FTS.StrongEps.thShift q.2 p.2))) (s := Work.Spaces.Iz) (t := Work.Spaces.Iθ) (by
          rw [← Measure.prod_restrict (μ := volume) (ν := volume) _ _]
          exact Work.FTS.StrongEps.HkSqAux.aemeasurable_shift_slice hcont p)
    rw [hAB]
  -- (5) the shift step: for each `p` the shifted `H^{m-1}`-integral of `u` is bounded
  have h5 : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Ψ p) * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
        * (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (Work.Spaces.HkIntegrand α (m - 1) u
              (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2))))
      ≤ ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Ψ p) * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
        * (ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
            * ENNReal.ofReal (Work.Spaces.HkSq α (m - 1) u)) := by
    refine lintegral_mono fun p => mul_le_mul_right ?_ _
    exact Work.FTS.StrongEps.HkSqAux.integral_shift_le hJac hMem hcont p
  -- (6) the two exponential factors combine and `HkSq α (m-1) u` comes out of the integral
  have hexp : ∀ p : ℝ × ℝ, ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
      * ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
      = ENNReal.ofReal (Real.exp ((2 * c + δ) * (|p.1| + |p.2|))) := by
    intro p
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 1
    ring_nf
  have hPsi : ∀ p : ℝ × ℝ, ENNReal.ofReal (Ψ p)
      * ENNReal.ofReal (Real.exp ((2 * c + δ) * (|p.1| + |p.2|)))
      = ENNReal.ofReal (Ψ p * Real.exp ((2 * c + δ) * (|p.1| + |p.2|))) := by
    intro p
    rw [mul_comm (ENNReal.ofReal (Ψ p)) (ENNReal.ofReal (Real.exp _)),
      ← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm (Real.exp _) (Ψ p)]
  have hpt : ∀ p : ℝ × ℝ, ENNReal.ofReal (Ψ p) * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
        * (ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
            * ENNReal.ofReal (Work.Spaces.HkSq α (m - 1) u))
      = ENNReal.ofReal (Ψ p * Real.exp ((2 * c + δ) * (|p.1| + |p.2|)))
          * ENNReal.ofReal (Work.Spaces.HkSq α (m - 1) u) := by
    intro p
    calc ENNReal.ofReal (Ψ p) * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
            * (ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
                * ENNReal.ofReal (Work.Spaces.HkSq α (m - 1) u))
        = (ENNReal.ofReal (Ψ p) * (ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
              * ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))))
            * ENNReal.ofReal (Work.Spaces.HkSq α (m - 1) u) := by ring
      _ = (ENNReal.ofReal (Ψ p) * ENNReal.ofReal (Real.exp ((2 * c + δ) * (|p.1| + |p.2|))))
            * ENNReal.ofReal (Work.Spaces.HkSq α (m - 1) u) := by rw [hexp p]
      _ = _ := by rw [hPsi p]
  have h6 : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Ψ p) * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
        * (ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
            * ENNReal.ofReal (Work.Spaces.HkSq α (m - 1) u)))
      = (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Ψ p * Real.exp ((2 * c + δ) * (|p.1| + |p.2|))))
          * ENNReal.ofReal (Work.Spaces.HkSq α (m - 1) u) := by
    rw [show (fun p : ℝ × ℝ => ENNReal.ofReal (Ψ p) * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
          * (ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
              * ENNReal.ofReal (Work.Spaces.HkSq α (m - 1) u)))
        = fun p : ℝ × ℝ => ENNReal.ofReal (Ψ p * Real.exp ((2 * c + δ) * (|p.1| + |p.2|)))
            * ENNReal.ofReal (Work.Spaces.HkSq α (m - 1) u) from funext hpt]
    rw [MeasureTheory.lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  calc ENNReal.ofReal (Work.Spaces.HkSq α m (Work.FTS.StrongEps.Jeps ρ ε u))
      = ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α m (Work.FTS.StrongEps.Jeps ρ ε u) z θ) := h1
    _ ≤ ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (ε⁻¹ * B) * ∫⁻ p : ℝ × ℝ,
          ENNReal.ofReal (Ψ p) * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
            * ENNReal.ofReal (Work.Spaces.HkIntegrand α (m - 1) u
                (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) := h2
    _ = ENNReal.ofReal (ε⁻¹ * B) * (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ p : ℝ × ℝ,
          ENNReal.ofReal (Ψ p) * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
            * ENNReal.ofReal (Work.Spaces.HkIntegrand α (m - 1) u
                (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2))) := h3
    _ = ENNReal.ofReal (ε⁻¹ * B) * (∫⁻ p : ℝ × ℝ,
          ENNReal.ofReal (Ψ p) * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
          * (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal (Work.Spaces.HkIntegrand α (m - 1) u
                (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)))) := by rw [h4]
    _ ≤ ENNReal.ofReal (ε⁻¹ * B) * (∫⁻ p : ℝ × ℝ,
          ENNReal.ofReal (Ψ p) * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
          * (ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
              * ENNReal.ofReal (Work.Spaces.HkSq α (m - 1) u))) := mul_le_mul_right h5 _
    _ = ENNReal.ofReal (ε⁻¹ * B)
          * ((∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Ψ p * Real.exp ((2 * c + δ) * (|p.1| + |p.2|))))
              * ENNReal.ofReal (Work.Spaces.HkSq α (m - 1) u)) := by rw [h6]
    _ = ENNReal.ofReal (ε⁻¹ * B)
          * (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Ψ p * Real.exp ((2 * c + δ) * (|p.1| + |p.2|))))
          * ENNReal.ofReal (Work.Spaces.HkSq α (m - 1) u) := by rw [mul_assoc]

end Work.FTS.StrongEps.StepFacts
