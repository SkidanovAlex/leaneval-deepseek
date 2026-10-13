/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS/ClassC/level0_psiSeries` — the level-`0` honesty of the modal solution `psiSeries`

The capstone of the level-`0` honest-modal route (`NOTES_mode_sum_level0.md`): the *exact* modal
solution `Ψ = psiSeries α F` of `bslOp α Ψ = F` has finite `σ`-weighted `L²`-mass, uniformly
controlled by the source,

  `∫⁻_z ∫⁻_θ ofReal (Ψ² w² σ) ≤ ofReal (9 (∫θ σ) · S · HkSq α 0 F)`.

It is obtained by combining the two halves:

* `level0_psiTrunc.lintegral_psiTrunc_le` — the same bound for the truncations
  `Ψ_N = psiTrunc α F N`, with the `N`-dependent factor `Σ_{m≤N}((m+1)/μ_m)²`;
* `lintegral_psiSeries_le_of_trunc` — Fatou in `N`, from the pointwise convergence
  `Ψ_N(z,θ) → Ψ(z,θ)`;

the uniform bound `Σ_{m≤N}((m+1)/μ_m)² ≤ S` is carried as the hypothesis `hS` (for the concrete
choice `μ m = if m = 0 then 1 else lamR m − 3α² − 3α(5+α)/2` it is
`modeSum_muSeq_sum_le`, with `S = 8`), and the `AEMeasurable` hypothesis `hmeas` of the Fatou
step is exposed as stated by that lemma.

The per-mode bound `hper` is the `radGreen_modeEnergy` instance at
`a = acoeff α m F = radGreen α m (cmode m F)`, `c = √(eNorm m)·cmode m F`; the consumer supplies
the two-sided decay and the weighted-`L²` integrability of the mode coefficients that
`radGreen_modeEnergy` needs.

This is the `Ψ`-side *seed* of the paper's proof of Proposition `prop:L2` (Elgindi, Annals 194
(2021), §Elliptic Regularity Estimates): the estimate `Σ_{n≥1} 4n²|Ψ_n w|² ≤ 20 |Fw||Ψw|` is
consumed only through the finiteness of the weighted mass of `Ψ`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.ClassC.level0_psiTrunc
import Submission.Work.FTS.ClassC.lintegral_psiSeries_le_of_trunc

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

/-- **The level-`0` honesty of the modal solution.** -/
theorem lintegral_psiSeries_le (α : ℝ) (F : ℝ → ℝ → ℝ)
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α 0 F)
    (hint : ∀ z ∈ Set.Ioi (0 : ℝ),
      MeasureTheory.IntegrableOn (fun θ => (F z θ) ^ 2 * Real.cos θ) Iθ)
    (hintσ : ∀ z ∈ Set.Ioi (0 : ℝ),
      MeasureTheory.IntegrableOn (fun θ => (F z θ) ^ 2 * sEta θ) Iθ)
    (hint_a : ∀ m : ℕ, MeasureTheory.IntegrableOn
      (fun z => (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2 * (w z) ^ 2) Iz)
    {μ : ℕ → ℝ} (hμ : ∀ m, 0 < μ m)
    (hper : ∀ m : ℕ, μ m *
        Real.sqrt (∫ z in Iz, (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2 * (w z) ^ 2)
      ≤ Real.sqrt (∫ z in Iz, (Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m)
          * Work.FTS.PhiStar.Series.cmode m F z) ^ 2 * (w z) ^ 2))
    {S : ℝ} (hS : ∀ N : ℕ, (∑ m ∈ Finset.range (N + 1), (((m : ℝ) + 1) / μ m) ^ 2) ≤ S)
    (hconv : ∀ z θ : ℝ, Filter.Tendsto
      (fun N => Work.FTS.PhiStar.Series.psiTrunc α F N z θ) Filter.atTop
      (nhds (Work.FTS.PhiStar.Series.psiSeries α F z θ)))
    (hmeas : ∀ N : ℕ, AEMeasurable (fun z => ∫⁻ θ in Iθ,
        ENNReal.ofReal ((Work.FTS.PhiStar.Series.psiTrunc α F N z θ) ^ 2
          * (w z) ^ 2 * sEta θ)) (MeasureTheory.volume.restrict Iz)) :
    (∫⁻ z in Iz, ∫⁻ θ in Iθ,
        ENNReal.ofReal ((Work.FTS.PhiStar.Series.psiSeries α F z θ) ^ 2
          * (w z) ^ 2 * sEta θ))
      ≤ ENNReal.ofReal (9 * (∫ θ in Iθ, sEta θ) * S * Work.Spaces.HkSq α 0 F) := by
  have hσ0 : 0 ≤ ∫ θ in Iθ, sEta θ :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => Work.FTS.EllipticEst.Honest.sEta_nonneg hθ)
  have hHk0 : 0 ≤ Work.Spaces.HkSq α 0 F := by
    rw [Work.FTS.ClassC.HkSq_zero_eq_w α F]
    refine MeasureTheory.setIntegral_nonneg measurableSet_Ici (fun z _ => ?_)
    refine MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ => ?_)
    have hs := Work.FTS.EllipticEst.Honest.sEta_nonneg hθ
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hs
  have hS0 : 0 ≤ S :=
    le_trans (Finset.sum_nonneg (fun m _ => sq_nonneg _)) (hS 0)
  refine lintegral_psiSeries_le_of_trunc α F (9 * (∫ θ in Iθ, sEta θ) * S * Work.Spaces.HkSq α 0 F)
    (by positivity) hconv hmeas ?_
  intro N
  refine le_trans (lintegral_psiTrunc_le α F N hsm hmem hint hintσ
    (fun m _ => hint_a m) hμ (fun m _ => hper m)) (ENNReal.ofReal_le_ofReal ?_)
  have h2 : 9 * (∫ θ in Iθ, sEta θ) * (∑ m ∈ Finset.range (N + 1), (((m : ℝ) + 1) / μ m) ^ 2)
      ≤ 9 * (∫ θ in Iθ, sEta θ) * S :=
    mul_le_mul_of_nonneg_left (hS N) (by linarith : (0 : ℝ) ≤ 9 * (∫ θ in Iθ, sEta θ))
  exact mul_le_mul_of_nonneg_right h2 hHk0

end Work.FTS.ClassC
