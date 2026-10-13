/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS/ClassC/ModeSumMain` — the level-`0` estimate from the per-mode bounds

Combines the two pieces proved in this directory:

* `ModeSumZ.HkSq_zero_modeSum_le` — the level-`0` `HkSq` of a finite angular mode sum,
  `HkSq α 0 (Σ_{m≤N} a_m e_m) ≤ 9(∫_θ σ)·(Σ_{m≤N}(m+1)‖a_m w‖)²`;
* `modeSum_arith` — the ℓ² Cauchy–Schwarz step turning the per-mode bounds
  `μ_m‖a_m w‖ ≤ ‖c_m w‖` into `(Σ_{m≤N}(m+1)‖a_m w‖)² ≤ (Σ_{m≤N}((m+1)/μ_m)²)·(Σ_{m≤N}‖c_m w‖²)`,

into the level-`0` estimate

  `HkSq α 0 Ψ_N ≤ 9(∫_θ σ)·(Σ_{m≤N}((m+1)/μ_m)²)·(Σ_{m≤N}‖c_m w‖²)`

(`HkSq_zero_modeSum_le_of_perMode`), where `‖f w‖² = ∫_z f² w²`.

With the per-mode bound of `ModeEnergyCS.modeWeightedEnergy_norm` (`μ_m = λ_m − 3α² − 3α(5+α)/2
≈ 4m²`, so `Σ_m ((m+1)/μ_m)² ≍ Σ_m 1/m² < ∞`) and the Bessel bound `bessel_cmode` on the source
(`Σ_{m≤N} n_m‖c_m w‖² ≤ HkSq α 0 F` after integration in `z`), this gives
`HkSq α 0 Ψ_N ≤ C·HkSq α 0 F` **uniformly in `N`** — see `NOTES_mode_sum_level0.md`.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.Honest.HonEnergyAux
import Submission.Work.FTS.ClassC.ModeSumZ
import Submission.Work.FTS.ClassC.modeSum_arith

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
local notation "eFam" => Work.FTS.PhiStar.Gegenbauer.eFam
local notation "sEta" => Work.FTS.EllipticEst.sEta

/-- **The level-`0` estimate of a finite mode sum from the per-mode bounds.** -/
theorem HkSq_zero_modeSum_le_of_perMode (α : ℝ) (a c : ℕ → ℝ → ℝ) (N : ℕ) {μ : ℕ → ℝ}
    (hμ : ∀ m, 0 < μ m)
    (hper : ∀ m, m ≤ N →
      μ m * Real.sqrt (∫ z in Iz, (a m z) ^ 2 * (w z) ^ 2)
        ≤ Real.sqrt (∫ z in Iz, (c m z) ^ 2 * (w z) ^ 2))
    (hint : ∀ m, m ≤ N → MeasureTheory.IntegrableOn
      (fun z => (a m z) ^ 2 * (w z) ^ 2) Iz) :
    Work.Spaces.HkSq α 0 (fun z θ => ∑ m ∈ Finset.range (N + 1), a m z * eFam m θ)
      ≤ 9 * (∫ θ in Iθ, sEta θ)
          * (∑ m ∈ Finset.range (N + 1), (((m : ℝ) + 1) / μ m) ^ 2)
          * (∑ m ∈ Finset.range (N + 1),
              ∫ z in Iz, (c m z) ^ 2 * (w z) ^ 2) := by
  have hK0 : 0 ≤ 9 * (∫ θ in Iθ, sEta θ) := by
    have h : 0 ≤ ∫ θ in Iθ, sEta θ :=
      setIntegral_nonneg measurableSet_Icc fun θ hθ =>
        Work.FTS.EllipticEst.Honest.sEta_nonneg hθ
    linarith
  refine le_trans (HkSq_zero_modeSum_le α a N hint) ?_
  have h1 := modeSum_arith (N := N) (a := a) (c := c) (μ := μ) hμ hper
  calc 9 * (∫ θ in Iθ, sEta θ)
        * (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1)
            * Real.sqrt (∫ z in Iz, (a m z) ^ 2 * (w z) ^ 2)) ^ 2
      ≤ 9 * (∫ θ in Iθ, sEta θ)
          * ((∑ m ∈ Finset.range (N + 1), (((m : ℝ) + 1) / μ m) ^ 2)
              * (∑ m ∈ Finset.range (N + 1),
                  ∫ z in Iz, (c m z) ^ 2 * (w z) ^ 2)) :=
        mul_le_mul_of_nonneg_left h1 hK0
    _ = 9 * (∫ θ in Iθ, sEta θ)
          * (∑ m ∈ Finset.range (N + 1), (((m : ℝ) + 1) / μ m) ^ 2)
          * (∑ m ∈ Finset.range (N + 1),
              ∫ z in Iz, (c m z) ^ 2 * (w z) ^ 2) := by ring

end Work.FTS.ClassC
