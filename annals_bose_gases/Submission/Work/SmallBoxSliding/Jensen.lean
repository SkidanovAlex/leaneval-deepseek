import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.SmallBoxSliding.Geom
import Submission.Work.SmallBoxSliding.R_Psi_lower
import Submission.Work.SmallBoxSliding.R_Psi_nonneg
import Submission.Work.SmallBoxSliding.psiWeight_lower
import Submission.Work.SmallBoxSliding.wSmall1Pair_mass_nonneg
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Item 2a — the Jensen layer over the good set

The per-configuration tile Jensen (`SmallBoxQ0.tile_density_jensen`,
`tile_repulsion_mass`) already gives, for a convex density `F`,
`Σ_tiles (F(tile density)) ≥ ℓ³·F(total density)`; summed against the
sliding kernels this is the FS step-4 remainder

    R_Ψ = ∫_{I₋} F(n(u)/|B(u)|)·(∬ w_{1,B(u)}) du ,   F(t) = c(t−μ)²/(1+tμ⁻¹) .

This module discharges the two structural hypotheses of
`R_Psi_nonneg`/`R_Psi_lower` from the corpus:

* the per-box kernel mass is nonnegative — `wSmall1Pair_mass_nonneg` (proved);
* `psiWeight c μ t ≥ 0` / `psiWeight c μ t ≥ c(t−μ)²/3` from the FS regime
  `0 ≤ t ≤ 2μ` — `psiWeight_lower` (proved).

so that in the FS dilute regime `R_Ψ ≥ 0` and
`R_Ψ ≥ (c/3)·∫_{I₋}(n(u)/|B(u)| − μ)²(∬ w_{1,B(u)}) du` hold with only the
integrability obligations left to the consumer.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.SmallBoxSliding

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases
open BoseGases

/-- **`R_Ψ ≥ 0`** for the FS `F = psiWeight c μ` with `c ≥ 0` and the regime
`1 + (n(u)/|B(u)|)μ⁻¹ ≥ 0` on `I₋` (in particular for `n(u)/|B(u)| ≥ 0`). -/
theorem R_Psi_nonneg_of_regime {v : ℝ³ → ℝ} {Rv : ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) Rv) (hRv : 0 < Rv)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {μ c : ℝ} (hc : 0 ≤ c) (n : ℝ³ → ℝ)
    (hden : ∀ u ∈ interiorSet ℓ d μ, 0 ≤ 1 + (n u / boxVol ℓ d) * μ⁻¹) :
    0 ≤ R_Psi h M ℓ d μ c n := by
  refine R_Psi_nonneg h M ℓ d μ c n ?_ ?_
  · intro u hu
    rw [psiWeight]
    exact div_nonneg (mul_nonneg hc (sq_nonneg _)) (hden u hu)
  · intro u _
    exact wSmall1Pair_mass_nonneg hv_nonneg hvrad hv_supp hRv h hM hℓ hd u

/-- **`R_Ψ ≥ (c/3)·∫_{I₋}(n(u)/|B(u)| − μ)²(∬ w_{1,B(u)})`** in the FS
regime `0 ≤ n(u)/|B(u)| ≤ 2μ` on `I₋`: the Jensen remainder dominates the
quadratic deviation of the local density from `μ`, which is exactly what the
Cauchy–Schwarz particle window consumes. -/
theorem R_Psi_lower_of_regime {v : ℝ³ → ℝ} {Rv : ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) Rv) (hRv : 0 < Rv)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {μ c : ℝ} (hc : 0 ≤ c) (hμ : 0 < μ) (n : ℝ³ → ℝ)
    (hrange : ∀ u ∈ interiorSet ℓ d μ,
      0 ≤ n u / boxVol ℓ d ∧ n u / boxVol ℓ d ≤ 2 * μ)
    (hint : IntegrableOn (fun u =>
      (n u / boxVol ℓ d - μ) ^ 2 *
        (∫ x : ℝ³, ∫ y : ℝ³, wSmall1Pair h M ℓ d u x y))
      (interiorSet ℓ d μ))
    (hintPsi : IntegrableOn (fun u =>
      psiWeight c μ (n u / boxVol ℓ d) *
        (∫ x : ℝ³, ∫ y : ℝ³, wSmall1Pair h M ℓ d u x y))
      (interiorSet ℓ d μ)) :
    (c / 3) * (∫ u in interiorSet ℓ d μ,
      (n u / boxVol ℓ d - μ) ^ 2 *
        (∫ x : ℝ³, ∫ y : ℝ³, wSmall1Pair h M ℓ d u x y))
      ≤ R_Psi h M ℓ d μ c n := by
  have hc3 : 0 ≤ c / 3 := by positivity
  refine R_Psi_lower h M ℓ d μ c (c / 3) n hc3 ?_ ?_ ?_ hintPsi
  · intro u hu
    have h := psiWeight_lower (c := c) (μ := μ) hc hμ (hrange u hu).1 (hrange u hu).2
    have heq : c / 3 * (n u / boxVol ℓ d - μ) ^ 2
        = c * (n u / boxVol ℓ d - μ) ^ 2 / 3 := by ring
    rw [heq]
    exact h
  · intro u _
    exact wSmall1Pair_mass_nonneg hv_nonneg hvrad hv_supp hRv h hM hℓ hd u
  · exact hint

end Work.SmallBoxSliding
