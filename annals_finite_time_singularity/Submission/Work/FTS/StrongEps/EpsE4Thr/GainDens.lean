/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/GainDens.lean`

The facts about the routed density
`LamFull ρ ε c M = Jker (ε⁻¹^M · e^{4cε} · Σ_{a,b≤M}|∂₁^a∂₂^b ρ|) ε`
that the integrated membership step (`GainMem/HkMem_Jeps_of_pointwise_gain`) consumes:
nonnegativity, continuity, support in the closed ball of radius `ε`, and the two measurability
statements (slice at fixed `z > 0`, and joint in `(z,θ,p)`).
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsE4Thr.GainDefs
import Submission.Work.FTS.StrongEps.JepsHkMem.aemeasurable_pair_slice
import Submission.Work.FTS.StrongEps.HkSqAux.aemeasurable_shift_pair
import Submission.Work.FTS.StrongEps.HkSqAux.continuousOn_HkIntegrand_Quad

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The kernel-side datum of `LamFull`. -/
def LamSig (ρ : ℝ × ℝ → ℝ) (ε c : ℝ) (M : ℕ) : ℝ × ℝ → ℝ :=
  fun q => ε⁻¹ ^ M * Real.exp (4 * c * ε) * sigKd ρ M q

theorem LamSig_nonneg {ρ : ℝ × ℝ → ℝ} {ε : ℝ} (hε : 0 < ε) (c : ℝ) (M : ℕ) (q : ℝ × ℝ) :
    0 ≤ LamSig ρ ε c M q :=
  mul_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le) (sigKd_nonneg ρ M q)

theorem LamSig_continuous {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) (ε c : ℝ) (M : ℕ) :
    Continuous (LamSig ρ ε c M) := by
  have h1 : Continuous (sigKd ρ M) := sigKd_continuous hρ M
  exact h1.const_mul (ε⁻¹ ^ M * Real.exp (4 * c * ε))

theorem LamSig_support {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) {ε c : ℝ} (M : ℕ)
    (q : ℝ × ℝ) (hq : LamSig ρ ε c M q ≠ 0) : q.1 ^ 2 + q.2 ^ 2 ≤ 1 := by
  have hk : sigKd ρ M q ≠ 0 := by
    intro h
    refine hq ?_
    simp only [LamSig, h]
    ring
  exact sigKd_support hρ M hk

/-- **Slice measurability** of the density against the shifted level-`k` integrand, in the shape
consumed by the Tonelli step of the membership lemma (fixed `z > 0`). -/
theorem LamFull_aemeasurable_slice {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) {α : ℝ} {k : ℕ}
    {f : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad)
    {ε c : ℝ} (M : ℕ) {z : ℝ} (hz : 0 < z) :
    AEMeasurable (fun q : ℝ × (ℝ × ℝ) =>
        ENNReal.ofReal (LamFull ρ ε c M q.2)
          * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
              (Work.FTS.StrongEps.zShift z q.2.1) (Work.FTS.StrongEps.thShift q.1 q.2.2)))
      ((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod MeasureTheory.volume) := by
  have hH : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.HkIntegrand α k f q.1 q.2)
      Work.FTS.StrongEps.Quad := HkSqAux.continuousOn_HkIntegrand_Quad α k hf
  have hbase := JepsHkMem.aemeasurable_pair_slice (H := fun z' θ' =>
      Work.Spaces.HkIntegrand α k f z' θ') hH (LamSig_continuous hρ ε c M) (ε := ε) (c := 0)
    (z := z) hz
  refine hbase.congr (Eventually.of_forall fun q => ?_)
  have hLam : LamFull ρ ε c M q.2 = Work.FTS.StrongEps.Jker (LamSig ρ ε c M) ε q.2 := rfl
  simp only [hLam, mul_zero, zero_mul, Real.exp_zero, ENNReal.ofReal_one, mul_one]

/-- **Joint measurability** of the density against the shifted level-`k` integrand. -/
theorem LamFull_aemeasurable_joint {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) {α : ℝ} {k : ℕ}
    {f : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad)
    {ε c : ℝ} (M : ℕ) :
    AEMeasurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
        ENNReal.ofReal (LamFull ρ ε c M q.2)
          * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
              (Work.FTS.StrongEps.zShift q.1.1 q.2.1) (Work.FTS.StrongEps.thShift q.1.2 q.2.2)))
      (((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)).prod MeasureTheory.volume) := by
  have hH : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.HkIntegrand α k f q.1 q.2)
      Work.FTS.StrongEps.Quad := HkSqAux.continuousOn_HkIntegrand_Quad α k hf
  have hbase := HkSqAux.aemeasurable_shift_pair (G := fun z' θ' =>
      Work.Spaces.HkIntegrand α k f z' θ') hH (LamSig ρ ε c M) (LamSig_continuous hρ ε c M) ε
  refine hbase.congr (Eventually.of_forall fun q => ?_)
  have hLam : LamFull ρ ε c M q.2 = Work.FTS.StrongEps.Jker (LamSig ρ ε c M) ε q.2 := rfl
  simp only [hLam]

end Work.FTS.StrongEps.EpsE4Thr
