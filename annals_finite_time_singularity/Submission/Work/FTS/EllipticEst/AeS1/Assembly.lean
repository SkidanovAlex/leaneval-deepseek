/-
Copyright: work module for the Elgindi finite-time singularity project.

# `AeS1/Assembly` — `remov.AeStep1Full` from the first-order energy inequalities

This file reduces the deliverable `Work.FTS.EllipticEst.remov.AeStep1Full` (Step 1 of
`prop:H2` of Elgindi, Annals **194** (2021), in the almost-everywhere class `H2W.Ae.AeData`)
to analytic inputs, stated here as hypotheses (all of them axiom-clean *statements*):

* `hE` — the **unweighted** (radial weight `w²` only) first-order energy inequality
  `α²‖z∂_zu‖²_{w²} + ‖∂_θu‖²_{w²} ≤ C‖G‖²_{ρ}` plus the two `L2Mem` honesty conjuncts
  (the statement of `H2W.Ae.aeFirstEnergy` / `Dispatch.aeFirstEnergyD`);
* `hU` — the σ-Poincaré upgrade `HkSq α 0 u ≤ C·L2Sq (∂_θu·w)` (the statement of
  `Dispatch.aeSigmaUpD`, *proved* there from the axiom-clean `AeSigmaUpgradeU_all`);
* `hD` — the **σ-weighted** radial inequality `α²‖z∂_zu‖²_ρ ≤ C(‖G‖²_ρ + ‖u‖²_ρ)`
  (the statement of `Dispatch.aeSigmaEnergyD`);
* `h2` — the `∂_θθ`-bound of Step 2, `‖∂_θθu‖_ρ ≤ C(‖G‖_ρ + α‖z∂_zu‖_ρ)`
  (the statement of `Dispatch.step2AeD`).

`aeStep1Full_of` uses `h2` for the `u/cos θ` bound, via the proved `H2W.AeProof.hkSqBar_le`
(`HkSq α 0 (u/cos θ) ≤ 1010000 (HkSq α 0 u + HkSq α 0 (∂_θθu))`).  `aeStep1Full_of_bar` instead
takes that bound directly (`HkSq α 0 (u/cos θ) ≤ C(HkSq α 0 G + HkSq α 0 u)`) — the form given by
the σ-weighted *first-order* energy identity; use it when Step 2 is not available.

Everything else is proved here or in axiom-clean modules: the inlined `step1_of` (the four
conjuncts `HkMem α 0 u`, `HkMem α 0 (z∂_zu)`, `‖u‖_ρ ≤ C‖G‖_ρ`, `α‖z∂_zu‖_ρ ≤ C‖G‖_ρ`), the
honesty of `u/cos θ` (`H2W.AeProof.hkMemBar`) and `H2W.AeProof.hkSqBar_le`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.remov.AeChainDefs
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.Dispatch.hkMemUD
import Submission.Work.FTS.EllipticEst.H2W.Ae.AeSliceRightTendsto
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeGapSlices
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeSigmaUpgradeU
import Submission.Work.FTS.EllipticEst.H2W.AeProof.BarAux.hkSqBar_le
import Submission.Work.FTS.EllipticEst.AeS1.DzAgmonClean
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AeS1

set_option autoImplicit false

/-- **Step 1 of `prop:H2` in the a.e. class** (`H2W.Ae.Step1`), from the unweighted energy
inequality, the σ-Poincaré upgrade and the σ-weighted radial inequality.  This is the inlined
form of `Dispatch.step1AeD_of`. -/
theorem step1_of
    (hE : ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
        Work.Spaces.L2Mem (fun z θ => z * Work.Spaces.pz u z θ * Work.Spaces.w z) ∧
        Work.Spaces.L2Mem (fun z θ => Work.Spaces.pth u z θ * Work.Spaces.w z) ∧
        α ^ 2 * Work.Spaces.L2Sq (fun z θ => z * Work.Spaces.pz u z θ * Work.Spaces.w z)
          + Work.Spaces.L2Sq (fun z θ => Work.Spaces.pth u z θ * Work.Spaces.w z)
        ≤ C * Work.Spaces.HkSq α 0 G)
    (hU : ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
        Work.Spaces.L2Mem (fun z θ => Work.Spaces.pth u z θ * Work.Spaces.w z) →
        Work.Spaces.HkSq α 0 u
          ≤ C * Work.Spaces.L2Sq (fun z θ => Work.Spaces.pth u z θ * Work.Spaces.w z))
    (hD : ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
        Work.Spaces.L2Mem (fun z θ => z * Work.Spaces.pz u z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ∧
        α ^ 2 * Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u)
          ≤ C * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u)) :
    Work.FTS.EllipticEst.H2W.Ae.Step1 := by
  obtain ⟨C₁, hC₁, hE'⟩ := hE
  obtain ⟨Cσ, hCσ, hU'⟩ := hU
  obtain ⟨C₂, hC₂, hD'⟩ := hD
  have hK1 : 0 ≤ Cσ * C₁ := le_of_lt (mul_pos hCσ hC₁)
  have hK2 : 0 ≤ C₂ * (1 + Cσ * C₁) := le_of_lt (mul_pos hC₂ (by linarith))
  refine ⟨Real.sqrt (Cσ * C₁) + Real.sqrt (C₂ * (1 + Cσ * C₁)),
    lt_of_lt_of_le (Real.sqrt_pos.mpr (mul_pos hCσ hC₁))
      (le_add_of_nonneg_right (Real.sqrt_nonneg _)), ?_⟩
  intro α u G hA
  obtain ⟨hL2D, hL2θ, hineq⟩ := hE' α u G hA
  have hup := hU' α u G hA hL2θ
  obtain ⟨hL2Dρ, hineqD⟩ := hD' α u G hA
  have hG0 : 0 ≤ Work.Spaces.HkSq α 0 G := Work.Spaces.HkSq_nonneg α 0 G
  have hSle : Work.Spaces.L2Sq (fun z θ => Work.Spaces.pth u z θ * Work.Spaces.w z)
      ≤ C₁ * Work.Spaces.HkSq α 0 G := by
    have hA2 : (0 : ℝ) ≤ α ^ 2 * Work.Spaces.L2Sq
        (fun z θ => z * Work.Spaces.pz u z θ * Work.Spaces.w z) :=
      mul_nonneg (sq_nonneg α) (integral_nonneg fun z => integral_nonneg fun θ => sq_nonneg _)
    linarith
  have hUu : Work.Spaces.HkSq α 0 u ≤ (Cσ * C₁) * Work.Spaces.HkSq α 0 G := by
    calc Work.Spaces.HkSq α 0 u
        ≤ Cσ * Work.Spaces.L2Sq (fun z θ => Work.Spaces.pth u z θ * Work.Spaces.w z) := hup
      _ ≤ Cσ * (C₁ * Work.Spaces.HkSq α 0 G) := mul_le_mul_of_nonneg_left hSle (le_of_lt hCσ)
      _ = (Cσ * C₁) * Work.Spaces.HkSq α 0 G := by ring
  have hnrmG0 : 0 ≤ Work.FTS.EllipticEst.H2W.Ae.nrm α G := Real.sqrt_nonneg _
  have hG2 : (Work.FTS.EllipticEst.H2W.Ae.nrm α G) ^ 2 = Work.Spaces.HkSq α 0 G :=
    Real.sq_sqrt hG0
  have hu1 : Work.FTS.EllipticEst.H2W.Ae.nrm α u ≤ Real.sqrt (Cσ * C₁)
      * Work.FTS.EllipticEst.H2W.Ae.nrm α G :=
    calc Work.FTS.EllipticEst.H2W.Ae.nrm α u
        = Real.sqrt (Work.Spaces.HkSq α 0 u) := rfl
      _ ≤ Real.sqrt ((Cσ * C₁) * Work.Spaces.HkSq α 0 G) := Real.sqrt_le_sqrt hUu
      _ = Real.sqrt (Cσ * C₁) * Real.sqrt (Work.Spaces.HkSq α 0 G) := Real.sqrt_mul hK1 _
  have hgrad1 : α ^ 2 * Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u)
      ≤ (C₂ * (1 + Cσ * C₁)) * Work.Spaces.HkSq α 0 G := by
    have h2 : Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u
        ≤ Work.Spaces.HkSq α 0 G + (Cσ * C₁) * Work.Spaces.HkSq α 0 G := by linarith
    calc α ^ 2 * Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u)
        ≤ C₂ * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u) := hineqD
      _ ≤ C₂ * (Work.Spaces.HkSq α 0 G + (Cσ * C₁) * Work.Spaces.HkSq α 0 G) :=
          mul_le_mul_of_nonneg_left h2 (le_of_lt hC₂)
      _ = (C₂ * (1 + Cσ * C₁)) * Work.Spaces.HkSq α 0 G := by ring
  have hgrad3 : α * Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.FTS.EllipticEst.H2W.Ae.grad u)
      ≤ Real.sqrt (C₂ * (1 + Cσ * C₁)) * Work.FTS.EllipticEst.H2W.Ae.nrm α G := by
    have hgrad2 : (α * Work.FTS.EllipticEst.H2W.Ae.nrm α
          (Work.FTS.EllipticEst.H2W.Ae.grad u)) ^ 2
        ≤ (Real.sqrt (C₂ * (1 + Cσ * C₁))
            * Work.FTS.EllipticEst.H2W.Ae.nrm α G) ^ 2 := by
      have h3 : (Work.FTS.EllipticEst.H2W.Ae.nrm α
          (Work.FTS.EllipticEst.H2W.Ae.grad u)) ^ 2
          = Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) :=
        Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 0 _)
      rw [mul_pow, mul_pow, h3, Real.sq_sqrt hK2, hG2]
      exact hgrad1
    have hnn : 0 ≤ Real.sqrt (C₂ * (1 + Cσ * C₁)) * Work.FTS.EllipticEst.H2W.Ae.nrm α G :=
      mul_nonneg (Real.sqrt_nonneg _) hnrmG0
    have hα0 : 0 ≤ α := le_of_lt hA.hα
    have hD0 : 0 ≤ Work.FTS.EllipticEst.H2W.Ae.nrm α
        (Work.FTS.EllipticEst.H2W.Ae.grad u) := Real.sqrt_nonneg _
    have h := Real.sqrt_le_sqrt hgrad2
    rw [Real.sqrt_sq (mul_nonneg hα0 hD0), Real.sqrt_sq hnn] at h
    exact h
  refine ⟨Work.FTS.EllipticEst.Dispatch.hkMem_uM α u G hA, ?_, ?_, ?_⟩
  · obtain ⟨C, _hC, hmain⟩ := Work.Blocks.DzVamgm.HkNorm_Dz_amgm 0
    have hα1 : α ≤ 1 := by linarith [hA.hα4]
    have hu : Work.Spaces.HkMem α 0 u := Work.FTS.EllipticEst.Dispatch.hkMem_uM α u G hA
    exact (hmain α u hA.hα hα1 hA.smooth hu hA.memRad2).1
  · calc Work.FTS.EllipticEst.H2W.Ae.nrm α u
        ≤ Real.sqrt (Cσ * C₁) * Work.FTS.EllipticEst.H2W.Ae.nrm α G := hu1
      _ ≤ (Real.sqrt (Cσ * C₁) + Real.sqrt (C₂ * (1 + Cσ * C₁)))
            * Work.FTS.EllipticEst.H2W.Ae.nrm α G :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (Real.sqrt_nonneg _)) hnrmG0
  · calc α * Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.FTS.EllipticEst.H2W.Ae.grad u)
        ≤ Real.sqrt (C₂ * (1 + Cσ * C₁)) * Work.FTS.EllipticEst.H2W.Ae.nrm α G := hgrad3
      _ ≤ (Real.sqrt (Cσ * C₁) + Real.sqrt (C₂ * (1 + Cσ * C₁)))
            * Work.FTS.EllipticEst.H2W.Ae.nrm α G :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (Real.sqrt_nonneg _)) hnrmG0

/-- **The reduction**: the deliverable follows from the four analytic inputs listed in the
module docstring. -/
theorem aeStep1Full_of
    (hE : ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
        Work.Spaces.L2Mem (fun z θ => z * Work.Spaces.pz u z θ * Work.Spaces.w z) ∧
        Work.Spaces.L2Mem (fun z θ => Work.Spaces.pth u z θ * Work.Spaces.w z) ∧
        α ^ 2 * Work.Spaces.L2Sq (fun z θ => z * Work.Spaces.pz u z θ * Work.Spaces.w z)
          + Work.Spaces.L2Sq (fun z θ => Work.Spaces.pth u z θ * Work.Spaces.w z)
        ≤ C * Work.Spaces.HkSq α 0 G)
    (hU : ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
        Work.Spaces.L2Mem (fun z θ => Work.Spaces.pth u z θ * Work.Spaces.w z) →
        Work.Spaces.HkSq α 0 u
          ≤ C * Work.Spaces.L2Sq (fun z θ => Work.Spaces.pth u z θ * Work.Spaces.w z))
    (hD : ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
        Work.Spaces.L2Mem (fun z θ => z * Work.Spaces.pz u z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ∧
        α ^ 2 * Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u)
          ≤ C * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u))
    (h2 : ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
        Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.Spaces.pthIter 2 u)
          ≤ C * (Work.FTS.EllipticEst.H2W.Ae.nrm α G
            + α * Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.FTS.EllipticEst.H2W.Ae.grad u))) :
    Work.FTS.EllipticEst.remov.AeStep1Full := by
  obtain ⟨C, hCpos, hStep1⟩ := step1_of hE hU hD
  obtain ⟨C₂, hC₂pos, hTw⟩ := h2
  refine ⟨Real.sqrt (1010000 * (C ^ 2 + C₂ ^ 2)) + C + 1, by positivity, ?_⟩
  intro α u G hA
  obtain ⟨hmu, hgrad, hun, hugrad⟩ := hStep1 α u G hA
  have hbar : Work.Spaces.HkMem α 0 (fun z θ => u z θ / Real.cos θ) :=
    Work.FTS.EllipticEst.H2W.AeProof.BarAux.hkMemBar α u G hA hmu
  have hbarSq := Work.FTS.EllipticEst.H2W.AeProof.BarAux.hkSqBar_le α u G hA hmu
  have hα0 : 0 ≤ α := hA.hα.le
  have hG0 : (0 : ℝ) ≤ Work.Spaces.HkSq α 0 G := Work.Spaces.HkSq_nonneg α 0 G
  have hu0 : (0 : ℝ) ≤ Work.Spaces.HkSq α 0 u := Work.Spaces.HkSq_nonneg α 0 u
  have hw0 : (0 : ℝ) ≤ Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 u) :=
    Work.Spaces.HkSq_nonneg α 0 _
  have hnG : (0 : ℝ) ≤ Work.FTS.EllipticEst.H2W.Ae.nrm α G := Real.sqrt_nonneg _
  have hnq : (0 : ℝ) ≤ Work.FTS.EllipticEst.H2W.Ae.nrm α
      (Work.FTS.EllipticEst.H2W.Ae.grad u) := Real.sqrt_nonneg _
  have hnw : (0 : ℝ) ≤ Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.Spaces.pthIter 2 u) :=
    Real.sqrt_nonneg _
  have hsum0 : (0 : ℝ) ≤ Work.FTS.EllipticEst.H2W.Ae.nrm α G
      + α * Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.FTS.EllipticEst.H2W.Ae.grad u) :=
    add_nonneg hnG (mul_nonneg hα0 hnq)
  have huSq : Work.Spaces.HkSq α 0 u
      ≤ C ^ 2 * (Work.FTS.EllipticEst.H2W.Ae.nrm α G
        + α * Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.FTS.EllipticEst.H2W.Ae.grad u)) ^ 2 := by
    have h1 : Work.Spaces.HkSq α 0 u ≤ C ^ 2 * (Work.FTS.EllipticEst.H2W.Ae.nrm α G) ^ 2 := by
      rw [← Real.sq_sqrt hu0, ← mul_pow]
      exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hun 2
    have h2 : (Work.FTS.EllipticEst.H2W.Ae.nrm α G) ^ 2
        ≤ (Work.FTS.EllipticEst.H2W.Ae.nrm α G
          + α * Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.FTS.EllipticEst.H2W.Ae.grad u)) ^ 2 :=
      pow_le_pow_left₀ hnG (le_add_of_nonneg_right (mul_nonneg hα0 hnq)) 2
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (sq_nonneg _))
  have htwSq : Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 u)
      ≤ C₂ ^ 2 * (Work.FTS.EllipticEst.H2W.Ae.nrm α G
        + α * Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.FTS.EllipticEst.H2W.Ae.grad u)) ^ 2 := by
    rw [← Real.sq_sqrt hw0, ← mul_pow]
    exact pow_le_pow_left₀ hnw (hTw α u G hA) 2
  have hcast : Work.Spaces.HkSq α 0 (fun z θ => u z θ / Real.cos θ)
      ≤ 1010000 * (C ^ 2 + C₂ ^ 2) * (Work.FTS.EllipticEst.H2W.Ae.nrm α G
        + α * Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.FTS.EllipticEst.H2W.Ae.grad u)) ^ 2 := by
    refine hbarSq.trans ?_
    have hsum : Work.Spaces.HkSq α 0 u + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 u)
        ≤ (C ^ 2 + C₂ ^ 2) * (Work.FTS.EllipticEst.H2W.Ae.nrm α G
          + α * Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.FTS.EllipticEst.H2W.Ae.grad u)) ^ 2 := by
      have h3 : C ^ 2 * (Work.FTS.EllipticEst.H2W.Ae.nrm α G
            + α * Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.FTS.EllipticEst.H2W.Ae.grad u)) ^ 2
          + C₂ ^ 2 * (Work.FTS.EllipticEst.H2W.Ae.nrm α G
            + α * Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.FTS.EllipticEst.H2W.Ae.grad u)) ^ 2
          = (C ^ 2 + C₂ ^ 2) * (Work.FTS.EllipticEst.H2W.Ae.nrm α G
            + α * Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.FTS.EllipticEst.H2W.Ae.grad u)) ^ 2 := by
        ring
      linarith [huSq, htwSq, h3]
    calc 1010000 * (Work.Spaces.HkSq α 0 u + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 u))
        ≤ 1010000 * ((C ^ 2 + C₂ ^ 2) * (Work.FTS.EllipticEst.H2W.Ae.nrm α G
            + α * Work.FTS.EllipticEst.H2W.Ae.nrm α
              (Work.FTS.EllipticEst.H2W.Ae.grad u)) ^ 2) :=
          mul_le_mul_of_nonneg_left hsum (by norm_num : (0:ℝ) ≤ 1010000)
      _ = 1010000 * (C ^ 2 + C₂ ^ 2) * (Work.FTS.EllipticEst.H2W.Ae.nrm α G
            + α * Work.FTS.EllipticEst.H2W.Ae.nrm α
              (Work.FTS.EllipticEst.H2W.Ae.grad u)) ^ 2 := by ring
  have hbarBd : Work.FTS.EllipticEst.H2W.Ae.nrm α (fun z θ => u z θ / Real.cos θ)
      ≤ Real.sqrt (1010000 * (C ^ 2 + C₂ ^ 2))
        * (Work.FTS.EllipticEst.H2W.Ae.nrm α G
          + α * Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.FTS.EllipticEst.H2W.Ae.grad u)) := by
    have hK0 : (0 : ℝ) ≤ 1010000 * (C ^ 2 + C₂ ^ 2) := by positivity
    calc Work.FTS.EllipticEst.H2W.Ae.nrm α (fun z θ => u z θ / Real.cos θ)
        = Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => u z θ / Real.cos θ)) := rfl
      _ ≤ Real.sqrt (1010000 * (C ^ 2 + C₂ ^ 2) * (Work.FTS.EllipticEst.H2W.Ae.nrm α G
            + α * Work.FTS.EllipticEst.H2W.Ae.nrm α
              (Work.FTS.EllipticEst.H2W.Ae.grad u)) ^ 2) := Real.sqrt_le_sqrt hcast
      _ = Real.sqrt (1010000 * (C ^ 2 + C₂ ^ 2))
            * (Work.FTS.EllipticEst.H2W.Ae.nrm α G
              + α * Work.FTS.EllipticEst.H2W.Ae.nrm α
                (Work.FTS.EllipticEst.H2W.Ae.grad u)) := by
            rw [Real.sqrt_mul hK0, Real.sqrt_sq hsum0]
  have hbig1 : C ≤ Real.sqrt (1010000 * (C ^ 2 + C₂ ^ 2)) + C + 1 := by
    linarith [Real.sqrt_nonneg (1010000 * (C ^ 2 + C₂ ^ 2))]
  have hun' : Work.FTS.EllipticEst.H2W.Ae.nrm α u
      ≤ (Real.sqrt (1010000 * (C ^ 2 + C₂ ^ 2)) + C + 1)
        * Work.FTS.EllipticEst.H2W.Ae.nrm α G :=
    hun.trans (mul_le_mul_of_nonneg_right hbig1 hnG)
  have hugrad' : α * Work.FTS.EllipticEst.H2W.Ae.nrm α
        (Work.FTS.EllipticEst.H2W.Ae.grad u)
      ≤ (Real.sqrt (1010000 * (C ^ 2 + C₂ ^ 2)) + C + 1)
        * Work.FTS.EllipticEst.H2W.Ae.nrm α G :=
    hugrad.trans (mul_le_mul_of_nonneg_right hbig1 hnG)
  refine ⟨hmu, hgrad, hbar, hun', hugrad', ?_⟩
  exact hbarBd.trans (mul_le_mul_of_nonneg_right
    (by linarith [Real.sqrt_nonneg (1010000 * (C ^ 2 + C₂ ^ 2))]) hsum0)

/-- **The alternative reduction**: as `aeStep1Full_of`, but with the `u/cos θ` bound supplied
directly (as `HkSq α 0 (u/cos θ) ≤ C (HkSq α 0 G + HkSq α 0 u)`) instead of via Step 2. -/
theorem aeStep1Full_of_bar
    (hE : ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
        Work.Spaces.L2Mem (fun z θ => z * Work.Spaces.pz u z θ * Work.Spaces.w z) ∧
        Work.Spaces.L2Mem (fun z θ => Work.Spaces.pth u z θ * Work.Spaces.w z) ∧
        α ^ 2 * Work.Spaces.L2Sq (fun z θ => z * Work.Spaces.pz u z θ * Work.Spaces.w z)
          + Work.Spaces.L2Sq (fun z θ => Work.Spaces.pth u z θ * Work.Spaces.w z)
        ≤ C * Work.Spaces.HkSq α 0 G)
    (hU : ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
        Work.Spaces.L2Mem (fun z θ => Work.Spaces.pth u z θ * Work.Spaces.w z) →
        Work.Spaces.HkSq α 0 u
          ≤ C * Work.Spaces.L2Sq (fun z θ => Work.Spaces.pth u z θ * Work.Spaces.w z))
    (hD : ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
        Work.Spaces.L2Mem (fun z θ => z * Work.Spaces.pz u z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ∧
        α ^ 2 * Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u)
          ≤ C * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u))
    (hBar : ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
        Work.Spaces.HkSq α 0 (fun z θ => u z θ / Real.cos θ)
          ≤ C * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u)) :
    Work.FTS.EllipticEst.remov.AeStep1Full := by
  obtain ⟨C, hCpos, hStep1⟩ := step1_of hE hU hD
  obtain ⟨C₂, hC₂pos, hBar⟩ := hBar
  refine ⟨Real.sqrt (C₂ * (1 + C ^ 2)) + C + 1, by positivity, ?_⟩
  intro α u G hA
  obtain ⟨hmu, hgrad, hun, hugrad⟩ := hStep1 α u G hA
  have hbar : Work.Spaces.HkMem α 0 (fun z θ => u z θ / Real.cos θ) :=
    Work.FTS.EllipticEst.H2W.AeProof.BarAux.hkMemBar α u G hA hmu
  have hα0 : 0 ≤ α := hA.hα.le
  have hG0 : (0 : ℝ) ≤ Work.Spaces.HkSq α 0 G := Work.Spaces.HkSq_nonneg α 0 G
  have hu0 : (0 : ℝ) ≤ Work.Spaces.HkSq α 0 u := Work.Spaces.HkSq_nonneg α 0 u
  have hnG : (0 : ℝ) ≤ Work.FTS.EllipticEst.H2W.Ae.nrm α G := Real.sqrt_nonneg _
  have hnq : (0 : ℝ) ≤ Work.FTS.EllipticEst.H2W.Ae.nrm α
      (Work.FTS.EllipticEst.H2W.Ae.grad u) := Real.sqrt_nonneg _
  have huSq : Work.Spaces.HkSq α 0 u ≤ (C ^ 2) * Work.Spaces.HkSq α 0 G := by
    have h1 : Work.Spaces.HkSq α 0 u ≤ (C * Work.FTS.EllipticEst.H2W.Ae.nrm α G) ^ 2 := by
      calc Work.Spaces.HkSq α 0 u = (Work.FTS.EllipticEst.H2W.Ae.nrm α u) ^ 2 :=
            (Real.sq_sqrt hu0).symm
        _ ≤ (C * Work.FTS.EllipticEst.H2W.Ae.nrm α G) ^ 2 :=
            pow_le_pow_left₀ (Real.sqrt_nonneg _) hun 2
    rw [mul_pow] at h1
    simp only [Work.FTS.EllipticEst.H2W.Ae.nrm] at h1
    rw [Real.sq_sqrt hG0] at h1
    exact h1
  have hsum0 : (0 : ℝ) ≤ Work.FTS.EllipticEst.H2W.Ae.nrm α G
      + α * Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.FTS.EllipticEst.H2W.Ae.grad u) :=
    add_nonneg hnG (mul_nonneg hα0 hnq)
  have hcast : Work.Spaces.HkSq α 0 (fun z θ => u z θ / Real.cos θ)
      ≤ C₂ * (1 + C ^ 2) * (Work.FTS.EllipticEst.H2W.Ae.nrm α G
        + α * Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.FTS.EllipticEst.H2W.Ae.grad u)) ^ 2 := by
    have hb := hBar α u G hA
    have hGle : Work.Spaces.HkSq α 0 G
        ≤ (Work.FTS.EllipticEst.H2W.Ae.nrm α G
          + α * Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.FTS.EllipticEst.H2W.Ae.grad u)) ^ 2 := by
      rw [← Real.sq_sqrt hG0]
      exact pow_le_pow_left₀ hnG (le_add_of_nonneg_right (mul_nonneg hα0 hnq)) 2
    have hsum : Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u
        ≤ (1 + C ^ 2) * (Work.FTS.EllipticEst.H2W.Ae.nrm α G
          + α * Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.FTS.EllipticEst.H2W.Ae.grad u)) ^ 2 := by
      nlinarith [hGle, huSq, sq_nonneg C, sq_nonneg (Work.Spaces.HkSq α 0 G)]
    calc Work.Spaces.HkSq α 0 (fun z θ => u z θ / Real.cos θ)
        ≤ C₂ * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u) := hb
      _ ≤ C₂ * ((1 + C ^ 2) * (Work.FTS.EllipticEst.H2W.Ae.nrm α G
            + α * Work.FTS.EllipticEst.H2W.Ae.nrm α
              (Work.FTS.EllipticEst.H2W.Ae.grad u)) ^ 2) :=
            mul_le_mul_of_nonneg_left hsum hC₂pos.le
      _ = C₂ * (1 + C ^ 2) * (Work.FTS.EllipticEst.H2W.Ae.nrm α G
            + α * Work.FTS.EllipticEst.H2W.Ae.nrm α
              (Work.FTS.EllipticEst.H2W.Ae.grad u)) ^ 2 := by ring
  have hK0 : (0 : ℝ) ≤ C₂ * (1 + C ^ 2) := by positivity
  have hbarBd : Work.FTS.EllipticEst.H2W.Ae.nrm α (fun z θ => u z θ / Real.cos θ)
      ≤ Real.sqrt (C₂ * (1 + C ^ 2)) * (Work.FTS.EllipticEst.H2W.Ae.nrm α G
          + α * Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.FTS.EllipticEst.H2W.Ae.grad u)) := by
    calc Work.FTS.EllipticEst.H2W.Ae.nrm α (fun z θ => u z θ / Real.cos θ)
        = Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => u z θ / Real.cos θ)) := rfl
      _ ≤ Real.sqrt (C₂ * (1 + C ^ 2) * (Work.FTS.EllipticEst.H2W.Ae.nrm α G
            + α * Work.FTS.EllipticEst.H2W.Ae.nrm α
              (Work.FTS.EllipticEst.H2W.Ae.grad u)) ^ 2) := Real.sqrt_le_sqrt hcast
      _ = Real.sqrt (C₂ * (1 + C ^ 2)) * (Work.FTS.EllipticEst.H2W.Ae.nrm α G
            + α * Work.FTS.EllipticEst.H2W.Ae.nrm α
              (Work.FTS.EllipticEst.H2W.Ae.grad u)) := by
          rw [Real.sqrt_mul hK0, Real.sqrt_sq hsum0]
  have hbig1 : C ≤ Real.sqrt (C₂ * (1 + C ^ 2)) + C + 1 := by
    linarith [Real.sqrt_nonneg (C₂ * (1 + C ^ 2))]
  have hun' : Work.FTS.EllipticEst.H2W.Ae.nrm α u
      ≤ (Real.sqrt (C₂ * (1 + C ^ 2)) + C + 1) * Work.FTS.EllipticEst.H2W.Ae.nrm α G :=
    hun.trans (mul_le_mul_of_nonneg_right hbig1 hnG)
  have hugrad' : α * Work.FTS.EllipticEst.H2W.Ae.nrm α
        (Work.FTS.EllipticEst.H2W.Ae.grad u)
      ≤ (Real.sqrt (C₂ * (1 + C ^ 2)) + C + 1) * Work.FTS.EllipticEst.H2W.Ae.nrm α G :=
    hugrad.trans (mul_le_mul_of_nonneg_right hbig1 hnG)
  refine ⟨hmu, hgrad, hbar, hun', hugrad', ?_⟩
  exact hbarBd.trans (mul_le_mul_of_nonneg_right
    (by linarith [Real.sqrt_nonneg (C₂ * (1 + C ^ 2))]) hsum0)


end Work.FTS.EllipticEst.AeS1
