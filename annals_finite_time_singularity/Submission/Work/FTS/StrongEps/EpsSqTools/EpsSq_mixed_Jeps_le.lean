/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsSqTools/EpsSq_mixed_Jeps_le.lean`

**The smoothing estimate for the mixed slots of the log-coordinate mollifier `J_ε` in the
weighted space `X = (EpsSq, EpsMem)` of `EpsSpace.lean`:**

  `EpsSq α (D_z^j D_θ^i (J_ε f)) ≤ C · (C / ε)^{2(j+i)} · EpsSq α f`   for `j + i ≤ 3`,

with a constant `C > 0` depending only on the kernel `ρ` (and not on `α ∈ (0,1]`, `ε ∈ (0,1]`).

## Route

`EpsSq α g = ∫_z∈Iz ∫_θ∈Iθ (g z θ · epsW α z θ)²` with `epsW α z θ = w z / sin(2θ)^{γ/2}`
(`γ = 1 + α/10`); on `Iz × Iθ` this weight coincides with `Wt α` of `Spaces.Defs`.

* **Routing** (`mixed_Jeps_kernel_partial` with `(j',i') = (0,0)`): all `j` `z`-derivatives and all
  `i` `θ`-derivatives are moved onto the (smooth, compactly supported) kernel,
  `D_z^j D_θ^i (J_ε f)(z,θ) = 2^i ∫ p, KdK ρ ε j i p · f(zShift z p₁)(thShift θ p₂)`,
  where `KdK ρ ε j i = ∂₁^j∂₂^i (Jker ρ ε)`.
* **Pointwise Cauchy–Schwarz** (`StepFacts.srb_cs_core`) with the weight comparison
  `HkSqAux.Wt_shift_le` gives `MixedJepsEpsWpt`.
* **Integration** (`iter_le_of_pointwise`): the weighted `L²`-norm of `f` at the shifted points is
  compared with `EpsSq α f` through the log-coordinate Jacobian comparison
  `HkSqAux.logJac_shift_le` (`EpsSqTools.shift_step`) and the two Tonelli exchanges
  (`setLIntegral_prod`, `lintegral_lintegral_swap`).  No integrability hypothesis on the *left*
  side is needed: the chain produces `ofReal (EpsSq …) ≤ ofReal (…)` directly (via
  `ofReal_EpsSq_le_iter`), and `EpsSq` on the right is honest because `EpsMem α f` is assumed.
* **Constants** (`KdKFacts`): `∫|KdK ρ ε j i| = ε⁻¹^{j+i} ∫|KdK ρ 1 j i|` and
  `∫|KdK ρ 1 j i| ≤ Ksm ρ 1 3`, so the per-slot constant is
  `4^i · (∫|KdK ρ 1 j i|)² · exp(2(2c+δ)) ≤ 64 · (Ksm ρ 1 3)² · exp(2(2c+δ))`, which the
  constant `C = max 1 (64 (Ksm ρ 1 3)² e^{2(2c+δ)})` absorbs.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsSq_Jeps_le
import Submission.Work.FTS.StrongEps.StepFacts.slot_route_bounds
import Submission.Work.FTS.StrongEps.mixed_Jeps_kernel_partial
import Submission.Work.FTS.StrongEps.StepFacts.mixed_Jeps_route_z
import Submission.Work.FTS.StrongEps.EpsE4Thr.GainDefs
import Submission.Work.FTS.StrongEps.EpsSqTools.KdKFacts
import Submission.Work.FTS.StrongEps.EpsSqTools.MixedJepsEpsWpt
import Submission.Work.FTS.StrongEps.HkSqAux.aemeasurable_shift_slice
import Submission.Work.FTS.StrongEps.JepsHkMem.AuxMeas
import Submission.Work.FTS.StrongEps.StepFacts.OfRealTools
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsSqTools

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-! ## The weight `epsW` is continuous on the open quadrant -/

theorem continuousOn_epsW_quad (α : ℝ) :
    ContinuousOn (fun q : ℝ × ℝ => Work.FTS.StrongEps.epsW α q.1 q.2)
      Work.FTS.StrongEps.Quad :=
  (Work.FTS.StrongEps.JepsHkMem.continuousOn_Wt α).congr
    (fun _ hq => epsW_eq_Wt_of_mem_Iθ ⟨hq.2.1.le, hq.2.2.le⟩)

/-! ## `EpsSq` against the iterated `lintegral` of its integrand -/

theorem ofReal_EpsSq_le_iter (α : ℝ) (g : ℝ → ℝ → ℝ) :
    ENNReal.ofReal (Work.FTS.StrongEps.EpsSq α g)
      ≤ ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal ((g z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2) := by
  have hψ : ∀ z : ℝ, 0 ≤ ∫ θ in Work.Spaces.Iθ,
      (g z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2 :=
    fun z => integral_nonneg fun θ => sq_nonneg _
  have h1 : ENNReal.ofReal (Work.FTS.StrongEps.EpsSq α g)
      ≤ ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
          (g z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2) :=
    Work.FTS.StrongEps.StepFacts.ofReal_integral_le_lintegral_ofReal hψ
  refine h1.trans (lintegral_mono fun z => ?_)
  exact Work.FTS.StrongEps.StepFacts.ofReal_integral_le_lintegral_ofReal
    (fun θ => sq_nonneg _)

/-! ## The integration chain -/

theorem iter_le_of_pointwise
    {α c δ C₀ Kmass : ℝ} {Λ : ℝ × ℝ → ℝ} {f g : ℝ → ℝ → ℝ}
    (hC₀ : 0 ≤ C₀) (hKmass : 0 ≤ Kmass) (hΛ0 : ∀ p : ℝ × ℝ, 0 ≤ Λ p)
    (hΛfin : ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p * Real.exp (δ * (|p.1| + |p.2|)))
      ≤ ENNReal.ofReal Kmass)
    (hMemF : Work.FTS.StrongEps.EpsMem α f)
    (hJac : ∀ s ζ p₁ p₂ : ℝ, Work.FTS.StrongEps.HkSqAux.logJac s ζ
      ≤ Real.exp (δ * (|p₁| + |p₂|)) * Work.FTS.StrongEps.HkSqAux.logJac (s - p₁) (ζ - p₂))
    (hFcont : ContinuousOn (fun q : ℝ × ℝ => f q.1 q.2 * Work.FTS.StrongEps.epsW α q.1 q.2)
      Work.FTS.StrongEps.Quad)
    (hAe : AEMeasurable (fun z : (ℝ × ℝ) × (ℝ × ℝ) => ENNReal.ofReal (Λ z.2)
        * ENNReal.ofReal ((f (Work.FTS.StrongEps.zShift z.1.1 z.2.1)
              (Work.FTS.StrongEps.thShift z.1.2 z.2.2)
            * Work.FTS.StrongEps.epsW α (Work.FTS.StrongEps.zShift z.1.1 z.2.1)
                (Work.FTS.StrongEps.thShift z.1.2 z.2.2)) ^ 2))
      (((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)).prod MeasureTheory.volume))
    (hP : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      ENNReal.ofReal ((g z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2)
        ≤ ENNReal.ofReal C₀ * ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
            * ENNReal.ofReal ((f (Work.FTS.StrongEps.zShift z p.1)
                  (Work.FTS.StrongEps.thShift θ p.2)
                * Work.FTS.StrongEps.epsW α (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2)) ^ 2)) :
    (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((g z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2))
      ≤ ENNReal.ofReal (C₀ * Kmass * Work.FTS.StrongEps.EpsSq α f) := by
  have hEpsSq0 : 0 ≤ Work.FTS.StrongEps.EpsSq α f := Work.FTS.StrongEps.EpsSq_nonneg α f
  -- Step 1: the pointwise bound, integrated twice
  have h1 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((g z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2))
      ≤ ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal C₀ * ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
            * ENNReal.ofReal ((f (Work.FTS.StrongEps.zShift z p.1)
                  (Work.FTS.StrongEps.thShift θ p.2)
                * Work.FTS.StrongEps.epsW α (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2)) ^ 2) :=
    MeasureTheory.setLIntegral_mono' (by rw [Work.Spaces.Iz]; exact measurableSet_Ici)
      (fun z hz => MeasureTheory.setLIntegral_mono'
        (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc) (fun θ hθ => hP z hz θ hθ))
  -- Step 2: the constant `C₀` comes out of the two integrations
  have h2 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal C₀ * ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
            * ENNReal.ofReal ((f (Work.FTS.StrongEps.zShift z p.1)
                  (Work.FTS.StrongEps.thShift θ p.2)
                * Work.FTS.StrongEps.epsW α (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2)) ^ 2))
      = ENNReal.ofReal C₀ * (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
            * ENNReal.ofReal ((f (Work.FTS.StrongEps.zShift z p.1)
                  (Work.FTS.StrongEps.thShift θ p.2)
                * Work.FTS.StrongEps.epsW α (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2)) ^ 2)) := by
    have hinner : ∀ z : ℝ, (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal C₀
          * (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
            * ENNReal.ofReal ((f (Work.FTS.StrongEps.zShift z p.1)
                  (Work.FTS.StrongEps.thShift θ p.2)
                * Work.FTS.StrongEps.epsW α (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2)) ^ 2)))
        = ENNReal.ofReal C₀ * ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
            * ENNReal.ofReal ((f (Work.FTS.StrongEps.zShift z p.1)
                  (Work.FTS.StrongEps.thShift θ p.2)
                * Work.FTS.StrongEps.epsW α (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2)) ^ 2) :=
      fun z => MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    simp only [hinner]
    exact MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  -- Step 3: Tonelli -- the `p`-integration is exchanged with the `(z,θ)`-integration
  have h3 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ p : ℝ × ℝ,
        ENNReal.ofReal (Λ p) * ENNReal.ofReal ((f (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2)
            * Work.FTS.StrongEps.epsW α (Work.FTS.StrongEps.zShift z p.1)
                (Work.FTS.StrongEps.thShift θ p.2)) ^ 2))
      = ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p) * (∫⁻ z in Work.Spaces.Iz,
          ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((f (Work.FTS.StrongEps.zShift z p.1)
                (Work.FTS.StrongEps.thShift θ p.2)
              * Work.FTS.StrongEps.epsW α (Work.FTS.StrongEps.zShift z p.1)
                  (Work.FTS.StrongEps.thShift θ p.2)) ^ 2)) := by
    have hL : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ p : ℝ × ℝ,
          ENNReal.ofReal (Λ p) * ENNReal.ofReal ((f (Work.FTS.StrongEps.zShift z p.1)
                (Work.FTS.StrongEps.thShift θ p.2)
              * Work.FTS.StrongEps.epsW α (Work.FTS.StrongEps.zShift z p.1)
                  (Work.FTS.StrongEps.thShift θ p.2)) ^ 2))
        = ∫⁻ q : ℝ × ℝ, (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
            * ENNReal.ofReal ((f (Work.FTS.StrongEps.zShift q.1 p.1)
                  (Work.FTS.StrongEps.thShift q.2 p.2)
                * Work.FTS.StrongEps.epsW α (Work.FTS.StrongEps.zShift q.1 p.1)
                    (Work.FTS.StrongEps.thShift q.2 p.2)) ^ 2))
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
      rw [show ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))
          = (MeasureTheory.volume.prod MeasureTheory.volume).restrict
              (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) from Measure.prod_restrict _ _]
      exact (MeasureTheory.setLIntegral_prod (fun q : ℝ × ℝ => ∫⁻ p : ℝ × ℝ,
            ENNReal.ofReal (Λ p) * ENNReal.ofReal ((f (Work.FTS.StrongEps.zShift q.1 p.1)
                  (Work.FTS.StrongEps.thShift q.2 p.2)
                * Work.FTS.StrongEps.epsW α (Work.FTS.StrongEps.zShift q.1 p.1)
                    (Work.FTS.StrongEps.thShift q.2 p.2)) ^ 2))
        (s := Work.Spaces.Iz) (t := Work.Spaces.Iθ) (by
          rw [← Measure.prod_restrict (μ := MeasureTheory.volume)
            (ν := MeasureTheory.volume) _ _]
          exact hAe.lintegral_prod_right')).symm
    rw [hL]
    rw [MeasureTheory.lintegral_lintegral_swap
      (μ := (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (ν := MeasureTheory.volume) hAe]
    refine lintegral_congr fun p => ?_
    rw [MeasureTheory.lintegral_const_mul' (ENNReal.ofReal (Λ p)) _ ENNReal.ofReal_ne_top]
    congr 1
    rw [show ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))
        = (MeasureTheory.volume.prod MeasureTheory.volume).restrict
            (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) from Measure.prod_restrict _ _]
    exact MeasureTheory.setLIntegral_prod (fun q : ℝ × ℝ => ENNReal.ofReal
        ((f (Work.FTS.StrongEps.zShift q.1 p.1) (Work.FTS.StrongEps.thShift q.2 p.2)
          * Work.FTS.StrongEps.epsW α (Work.FTS.StrongEps.zShift q.1 p.1)
              (Work.FTS.StrongEps.thShift q.2 p.2)) ^ 2))
      (s := Work.Spaces.Iz) (t := Work.Spaces.Iθ) (by
        rw [← Measure.prod_restrict (μ := MeasureTheory.volume)
          (ν := MeasureTheory.volume) _ _]
        exact Work.FTS.StrongEps.HkSqAux.aemeasurable_shift_slice (G := fun z θ =>
          (f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2) (hFcont.pow 2) p)
  -- Step 4: the shift step
  have h4 : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p) * (∫⁻ z in Work.Spaces.Iz,
        ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((f (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2)
            * Work.FTS.StrongEps.epsW α (Work.FTS.StrongEps.zShift z p.1)
                (Work.FTS.StrongEps.thShift θ p.2)) ^ 2)))
      ≤ ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p) * (ENNReal.ofReal
          (Real.exp (δ * (|p.1| + |p.2|))) * ENNReal.ofReal (Work.FTS.StrongEps.EpsSq α f)) :=
    lintegral_mono fun p => mul_le_mul_of_nonneg_left
      (Work.FTS.StrongEps.EpsSqTools.shift_step (f := f) hMemF (δ := δ) hJac p) zero_le
  -- Step 5: combine the two exponentials and pull `EpsSq α f` out
  have h5 : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p) * (ENNReal.ofReal
        (Real.exp (δ * (|p.1| + |p.2|))) * ENNReal.ofReal (Work.FTS.StrongEps.EpsSq α f)))
      = (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p * Real.exp (δ * (|p.1| + |p.2|))))
          * ENNReal.ofReal (Work.FTS.StrongEps.EpsSq α f) := by
    rw [← MeasureTheory.lintegral_mul_const' (ENNReal.ofReal (Work.FTS.StrongEps.EpsSq α f)) _
      ENNReal.ofReal_ne_top]
    refine lintegral_congr fun p => ?_
    rw [← mul_assoc, ← ENNReal.ofReal_mul (hΛ0 p)]
  have h6 : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p * Real.exp (δ * (|p.1| + |p.2|))))
      * ENNReal.ofReal (Work.FTS.StrongEps.EpsSq α f)
      ≤ ENNReal.ofReal Kmass * ENNReal.ofReal (Work.FTS.StrongEps.EpsSq α f) :=
    mul_le_mul_of_nonneg_right hΛfin zero_le
  have h7 : ENNReal.ofReal Kmass * ENNReal.ofReal (Work.FTS.StrongEps.EpsSq α f)
      = ENNReal.ofReal (Kmass * Work.FTS.StrongEps.EpsSq α f) :=
    (ENNReal.ofReal_mul hKmass).symm
  calc (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((g z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2))
      ≤ ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal C₀ * ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
            * ENNReal.ofReal ((f (Work.FTS.StrongEps.zShift z p.1)
                  (Work.FTS.StrongEps.thShift θ p.2)
                * Work.FTS.StrongEps.epsW α (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2)) ^ 2) := h1
    _ = ENNReal.ofReal C₀ * (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ p : ℝ × ℝ,
          ENNReal.ofReal (Λ p) * ENNReal.ofReal ((f (Work.FTS.StrongEps.zShift z p.1)
                (Work.FTS.StrongEps.thShift θ p.2)
              * Work.FTS.StrongEps.epsW α (Work.FTS.StrongEps.zShift z p.1)
                  (Work.FTS.StrongEps.thShift θ p.2)) ^ 2)) := h2
    _ = ENNReal.ofReal C₀ * (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p) * (∫⁻ z in Work.Spaces.Iz,
          ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((f (Work.FTS.StrongEps.zShift z p.1)
                (Work.FTS.StrongEps.thShift θ p.2)
              * Work.FTS.StrongEps.epsW α (Work.FTS.StrongEps.zShift z p.1)
                  (Work.FTS.StrongEps.thShift θ p.2)) ^ 2))) := by rw [h3]
    _ ≤ ENNReal.ofReal C₀ * (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p) * (ENNReal.ofReal
          (Real.exp (δ * (|p.1| + |p.2|))) * ENNReal.ofReal (Work.FTS.StrongEps.EpsSq α f))) :=
        mul_le_mul_of_nonneg_left h4 zero_le
    _ = ENNReal.ofReal C₀ * ((∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p
          * Real.exp (δ * (|p.1| + |p.2|))))
            * ENNReal.ofReal (Work.FTS.StrongEps.EpsSq α f)) := by rw [h5]
    _ ≤ ENNReal.ofReal C₀ * (ENNReal.ofReal Kmass
          * ENNReal.ofReal (Work.FTS.StrongEps.EpsSq α f)) :=
        mul_le_mul_of_nonneg_left h6 zero_le
    _ = ENNReal.ofReal C₀ * ENNReal.ofReal (Kmass * Work.FTS.StrongEps.EpsSq α f) := by rw [h7]
    _ = ENNReal.ofReal (C₀ * (Kmass * Work.FTS.StrongEps.EpsSq α f)) :=
        (ENNReal.ofReal_mul hC₀).symm
    _ = ENNReal.ofReal (C₀ * Kmass * Work.FTS.StrongEps.EpsSq α f) := by rw [mul_assoc]

/-! ## The main theorem (development copy) -/

theorem EpsSq_mixed_Jeps_le (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 → ∀ ε : ℝ, ε ∈ Set.Ioc 0 1 →
      ∀ f : Work.FTS.Galerkin.Fn,
        (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad) →
        Work.FTS.StrongEps.EpsMem α f →
        ∀ j i : ℕ, j + i ≤ 3 →
          Work.FTS.StrongEps.EpsSq α
              (Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f))
            ≤ C * (C / ε) ^ (2 * (j + i)) * Work.FTS.StrongEps.EpsSq α f := by
  obtain ⟨c, hcpos, hWc⟩ := Work.FTS.StrongEps.HkSqAux.Wt_shift_le
  obtain ⟨δ, hδpos, hJac0⟩ := Work.FTS.StrongEps.HkSqAux.logJac_shift_le
  have hc0 : 0 ≤ c := hcpos.le
  have hδ0 : 0 ≤ δ := hδpos.le
  obtain ⟨kscale, ksm_le, kint, ksupp, kmom⟩ := KdKFacts ρ hρ
  set Cv : ℝ := max 1 (64 * (Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 3) ^ 2
    * Real.exp (2 * (2 * c + δ))) with hCv
  have hCv1 : 1 ≤ Cv := le_max_left _ _
  have hCvpos : 0 < Cv := lt_of_lt_of_le zero_lt_one hCv1
  have hCvbig : 64 * (Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 3) ^ 2
      * Real.exp (2 * (2 * c + δ)) ≤ Cv := le_max_right _ _
  refine ⟨Cv, hCvpos, ?_⟩
  intro α hα ε hε f hf hfmem j i hji
  have hε0 : 0 < ε := hε.1
  have hε1 : ε ≤ 1 := hε.2
  have hα0 : 0 < α := hα.1
  have hi3 : i ≤ 3 := by omega
  have hj3 : j ≤ 3 := by omega
  set A : ℝ := ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε j i p| with hAdef
  set Λ : ℝ × ℝ → ℝ := fun p =>
    |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε j i p| * Real.exp (2 * c * (|p.1| + |p.2|)) with hΛdef
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    exact integral_nonneg fun p => abs_nonneg _
  have hΛ0 : ∀ p : ℝ × ℝ, 0 ≤ Λ p := by
    intro p
    rw [hΛdef]
    exact mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
  -- the pointwise bound on the open quadrant
  have hpt : ∀ {z θ : ℝ}, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      ENNReal.ofReal ((Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f) z θ
            * Work.FTS.StrongEps.epsW α z θ) ^ 2)
        ≤ ENNReal.ofReal (4 ^ i * A) * ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
            * ENNReal.ofReal ((f (Work.FTS.StrongEps.zShift z p.1)
                  (Work.FTS.StrongEps.thShift θ p.2)
                * Work.FTS.StrongEps.epsW α (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2)) ^ 2) := by
    intro z θ hz hθ
    exact MixedJepsEpsWpt ρ hρ (ε := ε) (α := α) (c := c) hε0 (f := f) hf hz hθ
      (fun p => hWc α hα z θ p.1 p.2 hz hθ) j i
  have hP : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      ENNReal.ofReal ((Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f) z θ
            * Work.FTS.StrongEps.epsW α z θ) ^ 2)
        ≤ ENNReal.ofReal (4 ^ i * A) * ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
            * ENNReal.ofReal ((f (Work.FTS.StrongEps.zShift z p.1)
                  (Work.FTS.StrongEps.thShift θ p.2)
                * Work.FTS.StrongEps.epsW α (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2)) ^ 2) := by
    intro z hz θ hθ
    by_cases hc' : 0 < z ∧ θ ∈ Set.Ioo 0 (π / 2)
    · exact hpt hc'.1 hc'.2
    · rw [epsW_eq_zero_of_not_mem_quad hα0 hz hθ hc', mul_zero,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0), ENNReal.ofReal_zero]
      exact zero_le
  -- the mass bound for the density
  have hΛexp : ∀ p : ℝ × ℝ, Λ p * Real.exp (δ * (|p.1| + |p.2|))
      = |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε j i p|
          * Real.exp ((2 * c + δ) * (|p.1| + |p.2|)) := by
    intro p
    rw [hΛdef, mul_assoc, ← Real.exp_add]
    congr 1
    ring_nf
  have hΛfin : ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p * Real.exp (δ * (|p.1| + |p.2|)))
      ≤ ENNReal.ofReal (Real.exp (2 * (2 * c + δ)) * A) := by
    refine le_trans (le_of_eq (lintegral_congr (fun p => by rw [hΛexp p]))) ?_
    simpa only [hAdef] using kmom hε0 hε1 hc0 hδ0 j i
  -- continuity and measurability
  have hfcont : ContinuousOn (fun q : ℝ × ℝ => f q.1 q.2) Work.FTS.StrongEps.Quad :=
    (hf 0).continuousOn
  have hFcont : ContinuousOn (fun q : ℝ × ℝ => f q.1 q.2
      * Work.FTS.StrongEps.epsW α q.1 q.2) Work.FTS.StrongEps.Quad :=
    hfcont.mul (continuousOn_epsW_quad α)
  have hΛcont : Continuous Λ := by
    rw [hΛdef]
    refine (Work.FTS.StrongEps.EpsE4Thr.KdK_continuous hρ ε j i).abs.mul ?_
    refine Real.continuous_exp.comp ?_
    exact continuous_const.mul
      ((continuous_abs.comp continuous_fst).add (continuous_abs.comp continuous_snd))
  have hFmeas : AEMeasurable (fun q : ℝ × ℝ => ENNReal.ofReal
      ((f q.1 q.2 * Work.FTS.StrongEps.epsW α q.1 q.2) ^ 2))
      (MeasureTheory.volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hfmem.aestronglyMeasurable.aemeasurable
  have hAe : AEMeasurable (fun z : (ℝ × ℝ) × (ℝ × ℝ) => ENNReal.ofReal (Λ z.2)
      * ENNReal.ofReal ((f (Work.FTS.StrongEps.zShift z.1.1 z.2.1)
            (Work.FTS.StrongEps.thShift z.1.2 z.2.2)
          * Work.FTS.StrongEps.epsW α (Work.FTS.StrongEps.zShift z.1.1 z.2.1)
              (Work.FTS.StrongEps.thShift z.1.2 z.2.2)) ^ 2))
      (((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)).prod MeasureTheory.volume) := by
    have h2 := aemeasurable_shift_comp'
      (F := fun q : ℝ × ℝ => ENNReal.ofReal
        ((f q.1 q.2 * Work.FTS.StrongEps.epsW α q.1 q.2) ^ 2)) hFmeas
    have h1 : AEMeasurable (fun z : (ℝ × ℝ) × (ℝ × ℝ) => ENNReal.ofReal (Λ z.2))
        (((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)).prod MeasureTheory.volume) :=
      (ENNReal.measurable_ofReal.comp hΛcont.measurable).comp_aemeasurable
        measurable_snd.aemeasurable
    exact h1.mul h2
  -- the chain
  have hC₀ : 0 ≤ 4 ^ i * A := mul_nonneg (by positivity) hA0
  have hKmass : 0 ≤ Real.exp (2 * (2 * c + δ)) * A :=
    mul_nonneg (Real.exp_pos _).le hA0
  have hZ := iter_le_of_pointwise (α := α) (c := c) (δ := δ) (Λ := Λ)
      (C₀ := 4 ^ i * A) (Kmass := Real.exp (2 * (2 * c + δ)) * A)
      (f := f) (g := Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f))
      hC₀ hKmass hΛ0 hΛfin hfmem hJac0 hFcont hAe hP
  have hfin : Work.FTS.StrongEps.EpsSq α (Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f))
      ≤ (4 ^ i * A) * (Real.exp (2 * (2 * c + δ)) * A)
          * Work.FTS.StrongEps.EpsSq α f := by
    refine (ENNReal.ofReal_le_ofReal_iff ?_).mp ?_
    · exact mul_nonneg (mul_nonneg hC₀ hKmass) (Work.FTS.StrongEps.EpsSq_nonneg α f)
    · exact (ofReal_EpsSq_le_iter α _).trans hZ
  -- the constants
  have hKsm0 : 0 ≤ Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 3 :=
    Work.FTS.StrongEps.EpsE4Thr.Ksm_nonneg hρ 1 3
  have hA_bound : A ≤ ε⁻¹ ^ (j + i) * Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 3 := by
    rw [hAdef, kscale hε0 j i]
    exact mul_le_mul_of_nonneg_left (ksm_le hj3 hi3) (by positivity)
  have hAA : A ^ 2 ≤ (ε⁻¹ ^ (j + i) * Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 3) ^ 2 :=
    pow_le_pow_left₀ hA0 hA_bound 2
  have h4i : (4 : ℝ) ^ i ≤ 64 := by
    have h1 : (4 : ℝ) ^ i ≤ 4 ^ 3 := pow_le_pow_right₀ (by norm_num) hi3
    norm_num at h1
    exact h1
  have hexp2 : (ε⁻¹ ^ (j + i) * Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 3) ^ 2
      = ε⁻¹ ^ (2 * (j + i)) * (Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 3) ^ 2 := by
    rw [mul_pow, ← pow_mul, Nat.mul_comm]
  have hconst : (4 ^ i * A) * (Real.exp (2 * (2 * c + δ)) * A)
      ≤ Cv * ε⁻¹ ^ (2 * (j + i)) := by
    have h2 : A ^ 2 ≤ ε⁻¹ ^ (2 * (j + i))
        * (Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 3) ^ 2 := by
      rw [← hexp2]
      exact hAA
    calc (4 ^ i * A) * (Real.exp (2 * (2 * c + δ)) * A)
        = (4 ^ i * Real.exp (2 * (2 * c + δ))) * A ^ 2 := by ring
      _ ≤ (4 ^ i * Real.exp (2 * (2 * c + δ)))
            * (ε⁻¹ ^ (2 * (j + i)) * (Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 3) ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (4 ^ i * (Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 3) ^ 2
              * Real.exp (2 * (2 * c + δ))) * ε⁻¹ ^ (2 * (j + i)) := by ring
      _ ≤ (64 * (Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 3) ^ 2
              * Real.exp (2 * (2 * c + δ))) * ε⁻¹ ^ (2 * (j + i)) := by
          have hfe : (4 : ℝ) ^ i * (Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 3) ^ 2
                * Real.exp (2 * (2 * c + δ))
              = (4 : ℝ) ^ i * ((Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 3) ^ 2
                  * Real.exp (2 * (2 * c + δ))) := by ring
          have hfe2 : 64 * (Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 3) ^ 2
                * Real.exp (2 * (2 * c + δ))
              = 64 * ((Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 3) ^ 2
                  * Real.exp (2 * (2 * c + δ))) := by ring
          rw [hfe, hfe2]
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_right h4i (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
      _ ≤ Cv * ε⁻¹ ^ (2 * (j + i)) := mul_le_mul_of_nonneg_right hCvbig (by positivity)
  have hCeps : Cv * ε⁻¹ ^ (2 * (j + i)) ≤ Cv * (Cv / ε) ^ (2 * (j + i)) := by
    refine mul_le_mul_of_nonneg_left ?_ hCvpos.le
    rw [div_eq_mul_inv]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    simpa using mul_le_mul_of_nonneg_right hCv1 (by positivity : (0 : ℝ) ≤ ε⁻¹)
  calc Work.FTS.StrongEps.EpsSq α
          (Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f))
      ≤ (4 ^ i * A) * (Real.exp (2 * (2 * c + δ)) * A)
          * Work.FTS.StrongEps.EpsSq α f := hfin
    _ ≤ (Cv * ε⁻¹ ^ (2 * (j + i))) * Work.FTS.StrongEps.EpsSq α f :=
        mul_le_mul_of_nonneg_right hconst (Work.FTS.StrongEps.EpsSq_nonneg α f)
    _ ≤ (Cv * (Cv / ε) ^ (2 * (j + i))) * Work.FTS.StrongEps.EpsSq α f :=
        mul_le_mul_of_nonneg_right hCeps (Work.FTS.StrongEps.EpsSq_nonneg α f)

end

end Work.FTS.StrongEps.EpsSqTools
