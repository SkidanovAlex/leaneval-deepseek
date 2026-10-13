/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS/ClassC/level0_psiTrunc` — the level-`0` honest estimate for the modal truncations

Assembles the level-`0` estimate `HkSq α 0 Ψ_N ≤ C · HkSq α 0 F` for the truncations
`Ψ_N = psiTrunc α F N` of the modal solution `Ψ = psiSeries α F` of `bslOp α Ψ = F`,
**in `lintegral` form** — i.e. the honest statement that the `σ`-weighted `L²`-mass of `Ψ_N`
is finite and controlled by the source's `ℋ⁰`-norm.

The three inputs are

* `Work.FTS.ClassC.lintegral_modeSum_le` — the angular/radial mode-sum bound
  `∫⁻_z ∫⁻_θ ofReal ((Σ_{m≤N} a_m e_m)² w² σ) ≤ ofReal (9(∫θ σ)(Σ_{m≤N}(m+1)‖a_m w‖)²)`;
* `Work.FTS.ClassC.modeSum_arith` — the ℓ²-Cauchy–Schwarz step turning the per-mode bounds
  `μ_m‖a_m w‖ ≤ ‖c_m w‖` into `(Σ_{m≤N}(m+1)‖a_m w‖)² ≤ (Σ_{m≤N}((m+1)/μ_m)²)(Σ_{m≤N}‖c_m w‖²)`;
* `Work.FTS.ClassC.sum_eNorm_cmode_sq_le_HkSq` (`bessel_z.lean`) — Bessel's inequality
  integrated in `z`, `Σ_{m≤N} eNorm_m ∫_z (cmode_m F)²w² ≤ HkSq α 0 F`.

The per-mode bound is carried as the hypothesis `hper` (it is `RadGreenModeEnergy.radGreen_modeEnergy`
at `a = acoeff α m F = radGreen α m (cmode m F)`, with `c := √(eNorm m)·cmode m F`), exactly as in
`HkSq_zero_modeSum_le_of_perMode`; the consumer supplies the two-sided decay and integrability
hypotheses on the mode coefficients that `radGreen_modeEnergy` needs.

Combined with
`Work.FTS.ClassC.lintegral_psiSeries_le_of_trunc` (Fatou in `N`, using
`psiTrunc α F N z θ → psiSeries α F z θ`), this gives the level-`0` honesty of the exact modal
solution: the *seed* of the paper's proof of Proposition `prop:L2` (Elgindi, Annals 194 (2021),
§Elliptic Regularity Estimates).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.ClassC.bessel_z
import Submission.Work.FTS.ClassC.modeSum_arith
import Submission.Work.FTS.ClassC.lintegral_modeSum_le

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

/-- **The level-`0` honest estimate for the modal truncations.**

With `Ψ_N = psiTrunc α F N` and `a_m = acoeff α m F`, `c_m = cmode m F`,

  `∫⁻_z ∫⁻_θ ofReal (Ψ_N² w² σ) ≤ ofReal (9(∫θ σ)·(Σ_{m≤N}((m+1)/μ_m)²)·HkSq α 0 F)`.

The hypotheses are: the source in the honest class (`hsm`, `hmem`), the two slice
integrability conditions `hint`/`hintσ`, the integrability of `a_m² w²` for `m ≤ N`, and the
per-mode bounds `hper`. -/
theorem lintegral_psiTrunc_le (α : ℝ) (F : ℝ → ℝ → ℝ) (N : ℕ)
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α 0 F)
    (hint : ∀ z ∈ Set.Ioi (0 : ℝ),
      MeasureTheory.IntegrableOn (fun θ => (F z θ) ^ 2 * Real.cos θ) Iθ)
    (hintσ : ∀ z ∈ Set.Ioi (0 : ℝ),
      MeasureTheory.IntegrableOn (fun θ => (F z θ) ^ 2 * sEta θ) Iθ)
    (hint_a : ∀ m, m ≤ N → MeasureTheory.IntegrableOn
      (fun z => (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2 * (w z) ^ 2) Iz)
    {μ : ℕ → ℝ} (hμ : ∀ m, 0 < μ m)
    (hper : ∀ m, m ≤ N → μ m *
        Real.sqrt (∫ z in Iz, (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2 * (w z) ^ 2)
      ≤ Real.sqrt (∫ z in Iz, (Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m)
          * Work.FTS.PhiStar.Series.cmode m F z) ^ 2 * (w z) ^ 2)) :
    (∫⁻ z in Iz, ∫⁻ θ in Iθ,
        ENNReal.ofReal ((Work.FTS.PhiStar.Series.psiTrunc α F N z θ) ^ 2
          * (w z) ^ 2 * sEta θ))
      ≤ ENNReal.ofReal (9 * (∫ θ in Iθ, sEta θ)
          * (∑ m ∈ Finset.range (N + 1), (((m : ℝ) + 1) / μ m) ^ 2)
          * Work.Spaces.HkSq α 0 F) := by
  -- the mode-sum bound
  have h1 : (∫⁻ z in Iz, ∫⁻ θ in Iθ,
        ENNReal.ofReal ((∑ m ∈ Finset.range (N + 1),
            Work.FTS.PhiStar.Series.acoeff α m F z
              * Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2 * (w z) ^ 2 * sEta θ))
      ≤ ENNReal.ofReal (9 * (∫ θ in Iθ, sEta θ)
          * (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1)
              * Real.sqrt (∫ z in Iz,
                  (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2 * (w z) ^ 2)) ^ 2) :=
    lintegral_modeSum_le (fun m z => Work.FTS.PhiStar.Series.acoeff α m F z) N hint_a
  -- the ℓ²-Cauchy–Schwarz step with the per-mode bounds
  have h2 : (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1)
        * Real.sqrt (∫ z in Iz,
            (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2 * (w z) ^ 2)) ^ 2
      ≤ (∑ m ∈ Finset.range (N + 1), (((m : ℝ) + 1) / μ m) ^ 2)
          * (∑ m ∈ Finset.range (N + 1),
              ∫ z in Iz, (Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m)
                * Work.FTS.PhiStar.Series.cmode m F z) ^ 2 * (w z) ^ 2) :=
    modeSum_arith (N := N)
      (a := fun m z => Work.FTS.PhiStar.Series.acoeff α m F z)
      (c := fun m z => Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m)
        * Work.FTS.PhiStar.Series.cmode m F z) hμ hper
  -- Bessel, integrated in `z`
  have h3 : (∑ m ∈ Finset.range (N + 1), ∫ z in Iz,
        (Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m)
          * Work.FTS.PhiStar.Series.cmode m F z) ^ 2 * (w z) ^ 2)
      ≤ Work.Spaces.HkSq α 0 F := by
    have hsq : ∀ m ∈ Finset.range (N + 1), (∫ z in Iz,
          (Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m)
            * Work.FTS.PhiStar.Series.cmode m F z) ^ 2 * (w z) ^ 2)
        = Work.EllipticEst.ModalSolution.eNorm m
          * ∫ z in Set.Ioi (0 : ℝ),
              (Work.FTS.PhiStar.Series.cmode m F z) ^ 2 * (w z) ^ 2 := by
      intro m _
      have hpt : ∀ z : ℝ, (Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m)
            * Work.FTS.PhiStar.Series.cmode m F z) ^ 2 * (w z) ^ 2
          = Work.EllipticEst.ModalSolution.eNorm m
            * ((Work.FTS.PhiStar.Series.cmode m F z) ^ 2 * (w z) ^ 2) := by
        intro z
        rw [mul_pow, Real.sq_sqrt (le_of_lt (Work.EllipticEst.ModalSolution.eNorm_pos m))]
        ring
      calc (∫ z in Iz, (Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m)
            * Work.FTS.PhiStar.Series.cmode m F z) ^ 2 * (w z) ^ 2)
          = ∫ z in Iz, Work.EllipticEst.ModalSolution.eNorm m
              * ((Work.FTS.PhiStar.Series.cmode m F z) ^ 2 * (w z) ^ 2) :=
            MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => hpt z)
        _ = Work.EllipticEst.ModalSolution.eNorm m
              * ∫ z in Iz, (Work.FTS.PhiStar.Series.cmode m F z) ^ 2 * (w z) ^ 2 :=
            MeasureTheory.integral_const_mul _ _
        _ = Work.EllipticEst.ModalSolution.eNorm m
              * ∫ z in Set.Ioi (0 : ℝ),
                  (Work.FTS.PhiStar.Series.cmode m F z) ^ 2 * (w z) ^ 2 := by
            congr 1
            exact MeasureTheory.integral_Ici_eq_integral_Ioi
              (μ := MeasureTheory.volume) (x := (0 : ℝ))
    rw [Finset.sum_congr rfl hsq]
    exact sum_eNorm_cmode_sq_le_HkSq α F N hsm hmem hint hintσ
  -- the arithmetic
  have hK0 : 0 ≤ 9 * (∫ θ in Iθ, sEta θ) := by
    have h : 0 ≤ ∫ θ in Iθ, sEta θ :=
      MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ hθ => Work.FTS.EllipticEst.Honest.sEta_nonneg hθ)
    linarith
  have hS0 : 0 ≤ ∑ m ∈ Finset.range (N + 1), (((m : ℝ) + 1) / μ m) ^ 2 :=
    Finset.sum_nonneg (fun m _ => sq_nonneg _)
  have hAll : 9 * (∫ θ in Iθ, sEta θ)
        * (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1)
            * Real.sqrt (∫ z in Iz,
                (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2 * (w z) ^ 2)) ^ 2
      ≤ 9 * (∫ θ in Iθ, sEta θ)
          * (∑ m ∈ Finset.range (N + 1), (((m : ℝ) + 1) / μ m) ^ 2)
          * Work.Spaces.HkSq α 0 F :=
    calc 9 * (∫ θ in Iθ, sEta θ)
          * (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1)
              * Real.sqrt (∫ z in Iz,
                  (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2 * (w z) ^ 2)) ^ 2
        ≤ 9 * (∫ θ in Iθ, sEta θ)
            * ((∑ m ∈ Finset.range (N + 1), (((m : ℝ) + 1) / μ m) ^ 2)
              * (∑ m ∈ Finset.range (N + 1), ∫ z in Iz,
                  (Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m)
                    * Work.FTS.PhiStar.Series.cmode m F z) ^ 2 * (w z) ^ 2)) :=
          mul_le_mul_of_nonneg_left h2 hK0
      _ = (9 * (∫ θ in Iθ, sEta θ)
              * (∑ m ∈ Finset.range (N + 1), (((m : ℝ) + 1) / μ m) ^ 2))
            * (∑ m ∈ Finset.range (N + 1), ∫ z in Iz,
                (Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m)
                  * Work.FTS.PhiStar.Series.cmode m F z) ^ 2 * (w z) ^ 2) := by ring
      _ ≤ (9 * (∫ θ in Iθ, sEta θ)
              * (∑ m ∈ Finset.range (N + 1), (((m : ℝ) + 1) / μ m) ^ 2))
            * Work.Spaces.HkSq α 0 F := mul_le_mul_of_nonneg_left h3 (mul_nonneg hK0 hS0)
      _ = 9 * (∫ θ in Iθ, sEta θ)
            * (∑ m ∈ Finset.range (N + 1), (((m : ℝ) + 1) / μ m) ^ 2)
            * Work.Spaces.HkSq α 0 F := by ring
  exact le_trans h1 (ENNReal.ofReal_le_ofReal hAll)

end Work.FTS.ClassC
