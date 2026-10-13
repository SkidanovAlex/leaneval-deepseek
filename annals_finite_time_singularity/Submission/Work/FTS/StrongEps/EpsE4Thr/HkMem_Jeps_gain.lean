/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/HkMem_Jeps_gain.lean`

The **`m`-order gain** of the log-coordinate mollifier `J_ε`:
`HkMem α k f → HkMem α (k+m) (J_ε f)` for every `k ≥ 1` and every `m`.

Proof, in four pieces (all sorry-free, in this directory):

* `GainDefs.lean` — the routed kernel derivatives `∂₁^a∂₂^b (Jker ρ ε)`, the scaling identity
  `∂₁^a∂₂^b (Jker ρ ε) = ε⁻¹^{a+b} Jker (∂₁^a∂₂^b ρ) ε`, the single density
  `LamFull ρ ε c M = Jker (ε⁻¹^M e^{4cε} Σ_{a,b≤M}|∂₁^a∂₂^b ρ|) ε` dominating every routed kernel
  derivative with its weight-shift factor, and the constants `KgainBig`, `Cgain`;
* `GainSlot/zslot_le_gain`, `GainSlot/mslot_le_gain` — the per-slot Cauchy–Schwarz bounds, using
  the fully routed identity `Work.FTS.StrongEps.mixed_Jeps_kernel_partial` (all derivatives of the
  slot land on the kernel, leaving the level-`0`, resp. level-`1`, slot of `f`);
* `GainPt.lean` — the sum over the `(M+1) + (M+1)²` slots of `HkIntegrand α M`;
* `GainMem/HkMem_Jeps_of_pointwise_gain` — the integrated membership step, with the reference level
  `k` decoupled from `M` (the version in `StepMembership.lean` has reference level `m - 1`).

At `m = 0` the statement is the same-level preservation `Work.FTS.StrongEps.HkMem_Jeps`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsE4Thr.HkMem_Jeps_succ
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongEps.HkMem_Jeps
import Submission.Work.FTS.StrongEps.HkSqAux.wdiv_shift_le
import Submission.Work.FTS.StrongEps.HkSqAux.Wt_shift_le
import Submission.Work.FTS.StrongEps.EpsE4Thr.GainDefs
import Submission.Work.FTS.StrongEps.EpsE4Thr.GainDens
import Submission.Work.FTS.StrongEps.EpsE4Thr.GainPt
import Submission.Work.FTS.StrongEps.EpsE4Thr.GainDens.Jker_comp_zShift_exp_lt_top
import Submission.Work.FTS.StrongEps.EpsE4Thr.GainDens.Jker_lintegral_mul_exp_lt_top
import Submission.Work.FTS.StrongEps.EpsE4Thr.GainMem.HkMem_Jeps_of_pointwise_gain

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

theorem HkMem_Jeps_gain {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) :
    ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ k m : ℕ, 1 ≤ k → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ f : ℝ → ℝ → ℝ,
        (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.EllipticEst.Q0) →
        (∀ z, 0 ≤ z → f z 0 = 0 ∧ f z (π / 2) = 0) →
        Work.Spaces.HkMem α k f →
        Work.Spaces.HkMem α (k + m) (Work.FTS.StrongEps.Jeps ρ ε f) := by
  intro α hα0 hα1 k m hk ε hε0 hε1 f hsm hvan hmem
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    simpa only [Nat.add_zero] using
      Work.FTS.StrongEps.HkMem_Jeps hρ.moll ⟨hα0, hα1⟩ hε0 (fun n => hsm n) hmem
  · set M : ℕ := k + m with hMdef
    have hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad :=
      fun n => hsm n
    -- the two weight-shift constants, exactly as in `HkMem_Jeps_succ`
    obtain ⟨cη, hcηpos, hWη0⟩ := HkSqAux.wdiv_shift_le
    obtain ⟨cγ, hcγpos, hWγ0⟩ := HkSqAux.Wt_shift_le
    set c : ℝ := max cη cγ with hcdef
    have hc0 : 0 ≤ c := le_of_lt (lt_of_lt_of_le hcηpos (le_max_left _ _))
    have hWη : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → ∀ p : ℝ × ℝ,
        Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
          ≤ Real.exp (c * (|p.1| + |p.2|))
            * (Work.Spaces.w (Work.FTS.StrongEps.zShift z p.1)
                / (Real.sin (2 * Work.FTS.StrongEps.thShift θ p.2))
                  ^ (Work.Spaces.eta / 2)) := by
      intro z θ hz hθ p
      refine (hWη0 z θ p.1 p.2 hz hθ).trans (mul_le_mul_of_nonneg_right ?_ ?_)
      · exact Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
      · exact div_nonneg (Work.FTS.StrongEps.w_nonneg _)
          (Real.rpow_nonneg (le_of_lt (sin_two_pos (thShift_mem hθ))) _)
    have hWγ : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → ∀ p : ℝ × ℝ,
        Work.Spaces.Wt α z θ
          ≤ Real.exp (c * (|p.1| + |p.2|))
            * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
                (Work.FTS.StrongEps.thShift θ p.2) := by
      intro z θ hz hθ p
      exact (hWγ0 α ⟨hα0, hα1⟩ z θ p.1 p.2 hz hθ).trans (mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)))
        (mul_nonneg (Work.FTS.StrongEps.w_nonneg _)
          (Real.rpow_nonneg (le_of_lt (sin_two_pos (thShift_mem hθ))) _)))
    -- the pointwise bound: the whole level-`M` integrand against the routed density
    have hP : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α M (Work.FTS.StrongEps.Jeps ρ ε f) z θ)
          ≤ ENNReal.ofReal (Cgain ρ ε M)
            * ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (LamFull ρ ε c M p)
                * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
                    (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) := by
      intro z hz θ hθ
      by_cases hq : 0 < z ∧ θ ∈ Set.Ioo 0 (π / 2)
      · exact HkIntegrand_Jeps_gain_pt hρ hε0 hε1 hc0 hk hf hq.1 hq.2
          (hWη z θ hq.1 hq.2) (hWγ z θ hq.1 hq.2)
      · have hzero := Work.FTS.StrongEps.HkSqAux.HkIntegrand_boundary_zero
          (α := α) (k := M) (f := Work.FTS.StrongEps.Jeps ρ ε f) ⟨hα0, hα1⟩ hz hθ hq
        rw [hzero, ENNReal.ofReal_zero]
        exact zero_le
    -- the density facts consumed by the membership lemma
    have hΛ0 : ∀ p : ℝ × ℝ, 0 ≤ LamFull ρ ε c M p := fun p => LamFull_nonneg hρ hε0 M p
    have hΛc : Continuous (LamFull ρ ε c M) := LamFull_continuous hρ ε c M
    have hΛs : ∀ p : ℝ × ℝ, LamFull ρ ε c M p ≠ 0 → p.1 ^ 2 + p.2 ^ 2 ≤ ε ^ 2 :=
      fun p hp => LamFull_support hρ M hp
    have hΛmeas : ∀ z : ℝ, 0 < z → AEMeasurable (fun q : ℝ × (ℝ × ℝ) =>
        ENNReal.ofReal (LamFull ρ ε c M q.2)
          * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
              (Work.FTS.StrongEps.zShift z q.2.1) (Work.FTS.StrongEps.thShift q.1 q.2.2)))
        ((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod MeasureTheory.volume) :=
      fun z hz => LamFull_aemeasurable_slice hρ hf M hz
    have hΛjoint : AEMeasurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
        ENNReal.ofReal (LamFull ρ ε c M q.2)
          * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
              (Work.FTS.StrongEps.zShift q.1.1 q.2.1) (Work.FTS.StrongEps.thShift q.1.2 q.2.2)))
        (((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)).prod MeasureTheory.volume) :=
      LamFull_aemeasurable_joint hρ hf M
    have hΛcomp : ∀ z : ℝ, 0 < z → ∀ δ : ℝ, 0 ≤ δ → ∀ G : ℝ → ENNReal,
        AEMeasurable (fun p₁ : ℝ => G (z * Real.exp (-p₁))) MeasureTheory.volume →
        (∫⁻ z' in Set.Ioi (0 : ℝ), G z') < ⊤ →
        (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (LamFull ρ ε c M p)
            * ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
            * G (z * Real.exp (-(p.1)))) < ⊤ := by
      intro z hz δ hδ G hmeas hfin
      have h1 := GainDens.Jker_comp_zShift_exp_lt_top (σ := LamSig ρ ε c M)
        (LamSig_nonneg hε0 c M) (LamSig_continuous hρ ε c M) (fun q hq => LamSig_support hρ M q hq)
        (ε := ε) (δ := δ) (z := z) hε0 hδ hz hmeas hfin
      exact h1
    have hΛmass : ∀ δ : ℝ, 0 ≤ δ → (∫⁻ p : ℝ × ℝ,
        ENNReal.ofReal (LamFull ρ ε c M p * Real.exp (δ * (|p.1| + |p.2|)))) < ⊤ := by
      intro δ hδ
      have h1 := GainDens.Jker_lintegral_mul_exp_lt_top (σ := LamSig ρ ε c M)
        (LamSig_nonneg hε0 c M) (LamSig_continuous hρ ε c M) (fun q hq => LamSig_support hρ M q hq)
        (ε := ε) (δ := δ) hε0 hε1 hδ
      exact h1
    exact GainMem.HkMem_Jeps_of_pointwise_gain hρ ⟨hα0, hα1⟩ hε0 hf
      hΛ0 hΛc hΛs hΛmeas hΛjoint hΛcomp hΛmass hmem hP

end Work.FTS.StrongEps.EpsE4Thr
