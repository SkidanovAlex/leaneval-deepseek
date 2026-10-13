/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS/ClassC/level0_psiSeries_concrete` — the level-`0` honesty with the explicit `μ_m`

`level0_psiSeries.lintegral_psiSeries_le` carries the uniform bound
`Σ_{m≤N}((m+1)/μ_m)² ≤ S` as a hypothesis.  Here it is instantiated at the paper's per-mode
constant

  `μ_m = lamR m − 3α² − 3α(5+α)/2 = 2m(2m+5) − 3α² − 3α(5+α)/2`   (`m ≥ 1`),   `μ_0 = 1`,

using the arithmetic bound `modeSum_muSeq_sum_le` (`S = 8`) and the elementary positivity
`μ_m > 0` (`m ≥ 1`: `lamR m ≥ 14 > 69/32 ≥ 3α² + 3α(5+α)/2` for `α ≤ 1/4`).

The result is the source-controlled finiteness of the `σ`-weighted `L²`-mass of the modal
solution:

  `∫⁻_z ∫⁻_θ ofReal (psiSeries α F ² w² σ) ≤ ofReal (72 · (∫θ σ) · HkSq α 0 F)`,
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.ClassC.level0_psiSeries
import Submission.Work.FTS.ClassC.modeSum_muSeq_sum_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

set_option autoImplicit false

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz
local notation "w" => Work.Spaces.w
local notation "sEta" => Work.FTS.EllipticEst.sEta

/-- The paper's per-mode constant: `μ_0 = 1` and `μ_m = lamR m − 3α² − 3α(5+α)/2`. -/
def muSeq (α : ℝ) (m : ℕ) : ℝ :=
  if m = 0 then 1 else Work.FTS.PhiStar.Radial.lamR m - 3 * α ^ 2 - 3 * α * (5 + α) / 2

/-- `μ_m > 0` for `α ≤ 1/4`. -/
theorem muSeq_pos {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) (m : ℕ) : 0 < muSeq α m := by
  rcases eq_or_ne m 0 with h | h
  · rw [muSeq, if_pos h]; norm_num
  · rw [muSeq, if_neg h]
    have hm : (1 : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
    rw [Work.FTS.PhiStar.Radial.lamR]
    nlinarith [hm, hα.le, hα4, sq_nonneg α]

/-- **The level-`0` honesty of the modal solution, with the explicit `μ_m`.** -/
theorem lintegral_psiSeries_le_concrete (α : ℝ) (F : ℝ → ℝ → ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α 0 F)
    (hint : ∀ z ∈ Set.Ioi (0 : ℝ),
      MeasureTheory.IntegrableOn (fun θ => (F z θ) ^ 2 * Real.cos θ) Iθ)
    (hintσ : ∀ z ∈ Set.Ioi (0 : ℝ),
      MeasureTheory.IntegrableOn (fun θ => (F z θ) ^ 2 * sEta θ) Iθ)
    (hint_a : ∀ m : ℕ, MeasureTheory.IntegrableOn
      (fun z => (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2 * (w z) ^ 2) Iz)
    (hper : ∀ m : ℕ, muSeq α m *
        Real.sqrt (∫ z in Iz, (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2 * (w z) ^ 2)
      ≤ Real.sqrt (∫ z in Iz, (Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m)
          * Work.FTS.PhiStar.Series.cmode m F z) ^ 2 * (w z) ^ 2))
    (hconv : ∀ z θ : ℝ, Filter.Tendsto
      (fun N => Work.FTS.PhiStar.Series.psiTrunc α F N z θ) Filter.atTop
      (nhds (Work.FTS.PhiStar.Series.psiSeries α F z θ)))
    (hmeas : ∀ N : ℕ, AEMeasurable (fun z => ∫⁻ θ in Iθ,
        ENNReal.ofReal ((Work.FTS.PhiStar.Series.psiTrunc α F N z θ) ^ 2
          * (w z) ^ 2 * sEta θ)) (MeasureTheory.volume.restrict Iz)) :
    (∫⁻ z in Iz, ∫⁻ θ in Iθ,
        ENNReal.ofReal ((Work.FTS.PhiStar.Series.psiSeries α F z θ) ^ 2
          * (w z) ^ 2 * sEta θ))
      ≤ ENNReal.ofReal (72 * (∫ θ in Iθ, sEta θ) * Work.Spaces.HkSq α 0 F) := by
  have h9 : 9 * (∫ θ in Iθ, sEta θ) * (8 : ℝ) * Work.Spaces.HkSq α 0 F
      = 72 * (∫ θ in Iθ, sEta θ) * Work.Spaces.HkSq α 0 F := by ring
  rw [← h9]
  exact lintegral_psiSeries_le α F hsm hmem hint hintσ hint_a (fun m => muSeq_pos hα hα4 m) hper
    (fun N => modeSum_muSeq_sum_le α hα hα4 N) hconv hmeas

end Work.FTS.ClassC
