import ChallengeDeps
import Submission.Work.BoseFixB1S.abs_wSmallScaled_div_convScale_le
import Submission.Work.MGroupInput.newtonianSharp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real ENNReal

namespace Work.BoseFixB1S

open Submission BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-- **Sharp Newtonian mass of a general renormalised kernel.**  If `W` is integrable,
a.e. nonnegative, supported in `ball 0 R`, and a.e. dominated by `(1+δ)·g₀`, then
`(2π)^{-3}∫_q (pairW W q)²/‖q‖² ≤ 2(1+δ)²·g0w0Mass` where `g0w0Mass = ∫g₀ω₀` is the mass of
the chosen radial scattering solution `ω₀ = Classical.choose h`.

This is `Work.MGroupInput.newtonianSharp` with the specific kernel `wScaled s (g0 v h)`
replaced by an abstract `W` (integrability, nonnegativity, support and the sharp comparison become
hypotheses instead of being supplied by `integrable_wScaled_g0_of_sharp`).  Assembly, as in that
proof: `Submission.BoseGases.lintegral_lintegral_ne_top_of_integrable`,
`Work.MGroupInput.newtonianSharp_integrable_double_coulPot`,
`Work.MGroupInput.newtonianSharp_g0_coulPot_integrable`,
`Work.MGroupInput.newtonianSharp_integrable_double_of_sharp`,
`Submission.BoseGases.integral_pairW_sq_div_sq_le_newtonian_of_fin`,
`Submission.BoseGases.coulomb_rect_le` (with `cA = cB = 1+δ`),
`Submission.BoseGases.chosen_newton_double_eq` (`∬g₀g₀/‖x−y‖ = 8π·g0w0Mass`) and the arithmetic
`(1/(4π))·(1+δ)²·8π = 2(1+δ)²`. -/
theorem pairW_newtonian_sharp {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R δ : ℝ}
    (hR : 0 < R) (hδ : 0 ≤ δ) (hv_nonneg : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (h : Work.UBB.ScatSol v)
    {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hWint : MeasureTheory.Integrable W)
    (hW0 : 0 ≤ᵐ[MeasureTheory.volume] W)
    (hWsupp : ∀ x : EuclideanSpace ℝ (Fin 3), R ≤ ‖x‖ → W x = 0)
    (hWle : ∀ᵐ x : EuclideanSpace ℝ (Fin 3),
      W x ≤ (1 + δ) * Submission.BoseGases.g0 v h x) :
    ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : EuclideanSpace ℝ (Fin 3),
        (Submission.BoseGases.pairW W q) ^ 2 / ‖q‖ ^ 2
      ≤ 2 * (1 + δ) ^ 2 * Submission.BoseGases.g0w0Mass (v := v) h := by
  set G : ℝ³ → ℝ := Submission.BoseGases.g0 v h with hGdef
  change ((2 * Real.pi) ^ 3)⁻¹ * (∫ q : ℝ³,
        (Submission.BoseGases.pairW W q) ^ 2 / ‖q‖ ^ 2)
      ≤ 2 * (1 + δ) ^ 2 * (∫ z : ℝ³, G z * Classical.choose h z)
  have hWmeas : AEMeasurable W := hWint.aestronglyMeasurable.aemeasurable
  have hGint : Integrable G := by
    rw [hGdef]
    exact Submission.BoseGases.g0_integrable hR hv_supp h
  have hG0 : ∀ᵐ x : ℝ³, 0 ≤ G x := by
    rw [hGdef]
    exact Submission.BoseGases.g0_nonneg_ae hR hv_nonneg hvrad hv_supp h
  have hGsupp : ∀ x : ℝ³, R ≤ ‖x‖ → G x = 0 := by
    intro x hx
    rw [hGdef]
    exact Submission.BoseGases.g0_zero_of_norm_ge hv_supp hx h
  have hVgInt : Integrable (fun x : ℝ³ => G x * coulPot G x) := by
    have h1 := Work.MGroupInput.newtonianSharp_g0_coulPot_integrable (v := v) (R := R)
      hR hv_nonneg hvrad hv_supp h
    rw [← hGdef] at h1
    exact h1
  have hGjoint : Integrable (fun p : ℝ³ × ℝ³ => G p.1 * G p.2 * (‖p.1 - p.2‖ : ℝ)⁻¹) :=
    Work.MGroupInput.newtonianSharp_integrable_double_coulPot hR hGint hG0 hGsupp hVgInt
  have hsharpW : ∀ᵐ x : ℝ³, W x ≤ (1 + δ) * G x := by
    filter_upwards [hWle] with x hx
    rw [hGdef]
    exact hx
  have hWjoint : Integrable (fun p : ℝ³ × ℝ³ => W p.1 * W p.2 * (‖p.1 - p.2‖ : ℝ)⁻¹) :=
    Work.MGroupInput.newtonianSharp_integrable_double_of_sharp hδ hWint hW0 hsharpW hGjoint
  have hfin : (∫⁻ x : ℝ³, ∫⁻ y : ℝ³, ENNReal.ofReal (W x * W y / ‖x - y‖)) ≠ ⊤ :=
    Submission.BoseGases.lintegral_lintegral_ne_top_of_integrable hW0 hWjoint
  have hM1 := Submission.BoseGases.integral_pairW_sq_div_sq_le_newtonian_of_fin
    (W := W) hWint hW0 hWmeas hfin
  have hrect := Submission.BoseGases.coulomb_rect_le (R := R) (A := W) (B := W) (g := G)
    (cA := 1 + δ) (cB := 1 + δ) hR
    hWint hWint hGint hWsupp hWsupp hGsupp hW0 hW0 hG0 hsharpW hsharpW
    (by linarith) (by linarith) hVgInt
  have hnewton : (∫ x : ℝ³, ∫ y : ℝ³, G x * G y * (‖x - y‖ : ℝ)⁻¹)
      = 8 * Real.pi * (∫ x : ℝ³, G x * Classical.choose h x) := by
    have h1 := Submission.BoseGases.chosen_newton_double_eq (v := v) (R := R) hR hvrad hv_supp h
    simpa only [hGdef, Submission.BoseGases.g0] using h1
  calc ((2 * Real.pi) ^ 3)⁻¹ * (∫ q : ℝ³, (Submission.BoseGases.pairW W q) ^ 2 / ‖q‖ ^ 2)
      ≤ (1 / (4 * Real.pi)) * (∫ x : ℝ³, ∫ y : ℝ³, W x * W y * (‖x - y‖ : ℝ)⁻¹) := hM1
    _ ≤ (1 / (4 * Real.pi)) *
          ((1 + δ) * (1 + δ) * (∫ x : ℝ³, ∫ y : ℝ³, G x * G y * (‖x - y‖ : ℝ)⁻¹)) := by
        exact mul_le_mul_of_nonneg_left hrect (by positivity)
    _ = (1 / (4 * Real.pi)) *
          ((1 + δ) ^ 2 * (8 * Real.pi * (∫ x : ℝ³, G x * Classical.choose h x))) := by
        rw [hnewton]; ring
    _ = 2 * (1 + δ) ^ 2 * (∫ x : ℝ³, G x * Classical.choose h x) := by
        field_simp
        ring

end Work.BoseFixB1S
