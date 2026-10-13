/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/TenOfEight/GainAll.lean`

**The `m`-order gain of the log-coordinate mollifier at every scale**: if `f` is `C^∞` on the
open quadrant and `HkMem α k f` with `k ≥ 1`, then `HkMem α (k+m) (J_ε f)` for **every**
`ε > 0` and every `m`.

This is `Work.FTS.StrongEps.EpsE4Thr.HkMem_Jeps_gain` with the two restrictions removed:

* the hypothesis `ε ≤ 1`: the scale-free density `TenOfEight.LamAll ρ ε c M` of
  `TenOfEight/LamAllDefs.lean` dominates every routed kernel derivative of order `≤ M` at every
  scale (`abs_KdK_mul_exp_le_LamAll`), and all the density facts consumed by the membership
  step (`LamAll_nonneg`, `LamAll_continuous`, `LamAll_support`, `LamAll_aemeasurable_slice`,
  `LamAll_aemeasurable_joint`, the `p₁`-substitution `GainDens.Jker_comp_zShift_exp_lt_top` and
  the weighted mass `LamAll_mass_lt_top`, whose proof uses the scale-free moment finiteness
  `Jker_lintegral_mul_exp_lt_top_pos`) are proved there;
* the boundary-vanishing hypothesis `f z 0 = 0 ∧ f z (π/2) = 0`: it was never used (the
  pointwise gain is applied to the shifted integrand at interior points `θ ∈ (0, π/2)`).

The pointwise input comes from `TenOfEight/GainPtAll.lean`
(`HkIntegrand_Jeps_gain_pt_all`), the integrated membership step is the abstract
`EpsE4Thr.GainMem.HkMem_Jeps_of_pointwise_gain`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.TenOfEight.LamAllDefs
import Submission.Work.FTS.StrongEps.TenOfEight.GainPtAll
import Submission.Work.FTS.StrongEps.HkMem_Jeps
import Submission.Work.FTS.StrongEps.HkSqAux.wdiv_shift_le
import Submission.Work.FTS.StrongEps.HkSqAux.Wt_shift_le
import Submission.Work.FTS.StrongEps.EpsE4Thr.GainMem.HkMem_Jeps_of_pointwise_gain
import Submission.Work.FTS.StrongEps.EpsE4Thr.GainDens.Jker_comp_zShift_exp_lt_top
import Submission.Work.FTS.StrongEps.HkSqAux.Chain
import Submission.Work.FTS.StrongEps.wtE_shift_le

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

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

theorem HkMem_Jeps_gain_pos {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) :
    ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ k m : ℕ, 1 ≤ k → ∀ ε : ℝ, 0 < ε → ∀ f : ℝ → ℝ → ℝ,
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad) →
      Work.Spaces.HkMem α k f →
      Work.Spaces.HkMem α (k + m) (Work.FTS.StrongEps.Jeps ρ ε f) := by
  intro α hα0 hα1 k m hk ε hε0 f hf hmem
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    simpa only [Nat.add_zero] using
      Work.FTS.StrongEps.HkMem_Jeps hρ.moll ⟨hα0, hα1⟩ hε0 hf hmem
  · set M : ℕ := k + m with hMdef
    -- the two weight-shift constants, exactly as in `HkMem_Jeps_gain`
    obtain ⟨cη, hcηpos, hWη0⟩ := Work.FTS.StrongEps.HkSqAux.wdiv_shift_le
    obtain ⟨cγ, hcγpos, hWγ0⟩ := Work.FTS.StrongEps.HkSqAux.Wt_shift_le
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
          (Real.rpow_nonneg (le_of_lt (Work.FTS.StrongEps.sin_two_pos
            (Work.FTS.StrongEps.thShift_mem hθ))) _)
    have hWγ : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → ∀ p : ℝ × ℝ,
        Work.Spaces.Wt α z θ
          ≤ Real.exp (c * (|p.1| + |p.2|))
            * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p.1)
                (Work.FTS.StrongEps.thShift θ p.2) := by
      intro z θ hz hθ p
      exact (hWγ0 α ⟨hα0, hα1⟩ z θ p.1 p.2 hz hθ).trans (mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)))
        (mul_nonneg (Work.FTS.StrongEps.w_nonneg _)
          (Real.rpow_nonneg (le_of_lt (Work.FTS.StrongEps.sin_two_pos
            (Work.FTS.StrongEps.thShift_mem hθ))) _)))
    -- the pointwise bound: the whole level-`M` integrand against the routed density
    have hP : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α M (Work.FTS.StrongEps.Jeps ρ ε f) z θ)
          ≤ ENNReal.ofReal (Cgain ρ ε M)
            * ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (LamAll ρ ε c M p)
                * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
                    (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) := by
      intro z hz θ hθ
      by_cases hq : 0 < z ∧ θ ∈ Set.Ioo 0 (π / 2)
      · exact HkIntegrand_Jeps_gain_pt_all hρ hε0 hc0 hk hf hq.1 hq.2
          (hWη z θ hq.1 hq.2) (hWγ z θ hq.1 hq.2)
      · have hzero := Work.FTS.StrongEps.HkSqAux.HkIntegrand_boundary_zero
          (α := α) (k := M) (f := Work.FTS.StrongEps.Jeps ρ ε f) ⟨hα0, hα1⟩ hz hθ hq
        rw [hzero, ENNReal.ofReal_zero]
        exact zero_le
    -- the density facts consumed by the membership lemma
    have hΛ0 : ∀ p : ℝ × ℝ, 0 ≤ LamAll ρ ε c M p := fun p => LamAll_nonneg hρ hε0 M p
    have hΛc : Continuous (LamAll ρ ε c M) := LamAll_continuous hρ ε c M
    have hΛs : ∀ p : ℝ × ℝ, LamAll ρ ε c M p ≠ 0 → p.1 ^ 2 + p.2 ^ 2 ≤ ε ^ 2 :=
      fun p hp => LamAll_support hρ M hp
    have hΛmeas : ∀ z : ℝ, 0 < z → AEMeasurable (fun q : ℝ × (ℝ × ℝ) =>
        ENNReal.ofReal (LamAll ρ ε c M q.2)
          * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
              (Work.FTS.StrongEps.zShift z q.2.1) (Work.FTS.StrongEps.thShift q.1 q.2.2)))
        ((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod MeasureTheory.volume) :=
      fun z hz => LamAll_aemeasurable_slice hρ hf M hz
    have hΛjoint : AEMeasurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
        ENNReal.ofReal (LamAll ρ ε c M q.2)
          * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
              (Work.FTS.StrongEps.zShift q.1.1 q.2.1) (Work.FTS.StrongEps.thShift q.1.2 q.2.2)))
        (((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)).prod MeasureTheory.volume) :=
      LamAll_aemeasurable_joint hρ hf M
    have hΛcomp : ∀ z : ℝ, 0 < z → ∀ δ : ℝ, 0 ≤ δ → ∀ G : ℝ → ENNReal,
        AEMeasurable (fun p₁ : ℝ => G (z * Real.exp (-p₁))) MeasureTheory.volume →
        (∫⁻ z' in Set.Ioi (0 : ℝ), G z') < ⊤ →
        (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (LamAll ρ ε c M p)
            * ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
            * G (z * Real.exp (-(p.1)))) < ⊤ := by
      intro z hz δ hδ G hmeas hfin
      have h1 := GainDens.Jker_comp_zShift_exp_lt_top (σ := LamSigAll ρ ε c M)
        (fun q => LamSigAll_nonneg ε c M q) (LamSigAll_continuous hρ ε c M)
        (fun q hq => LamSigAll_support hρ ε c M q hq)
        (ε := ε) (δ := δ) (z := z) hε0 hδ hz hmeas hfin
      exact h1
    have hΛmass : ∀ δ : ℝ, 0 ≤ δ → (∫⁻ p : ℝ × ℝ,
        ENNReal.ofReal (LamAll ρ ε c M p * Real.exp (δ * (|p.1| + |p.2|)))) < ⊤ :=
      fun δ hδ => LamAll_mass_lt_top hρ hε0 hc0 M hδ
    exact Work.FTS.StrongEps.EpsE4Thr.GainMem.HkMem_Jeps_of_pointwise_gain hρ ⟨hα0, hα1⟩ hε0 hf
      hΛ0 hΛc hΛs hΛmeas hΛjoint hΛcomp hΛmass hmem hP

end Work.FTS.StrongEps.TenOfEight
