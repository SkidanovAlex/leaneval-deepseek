import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.remov.slice_v_identities
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.remov.Step4.integrableOn_sq_sin_cos_rel

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.Step4

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ### Continuity of `(tan θ·u)''` on the open angular interval

`u` is `C³` on `(0, π/2)` and `tan` is smooth there (`cos θ > 0`), so `θ ↦ tan θ · u θ` is
`C²`, whence `(tan θ·u)''` is continuous.  This supplies the a.e. strong measurability of the
left-hand side of the estimate. -/
private lemma contDiffOn_Xt_second {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ 0 (fun θ => deriv (deriv (fun t => Real.tan t * u t)) θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
  have hI : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo
  have htu : ContDiffOn ℝ 2 (fun t => Real.tan t * u t) (Set.Ioo 0 (Real.pi / 2)) := by
    intro θ hθ
    have hcos : Real.cos θ ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos],
        by linarith [hθ.2, Real.pi_pos]⟩)
    exact ((Real.contDiffAt_tan.mpr hcos).mul
      ((hu.contDiffAt (hI.mem_nhds hθ)).of_le (by norm_num))).contDiffWithinAt
  have h1 : ContDiffOn ℝ 1 (deriv (fun t => Real.tan t * u t)) (Set.Ioo 0 (Real.pi / 2)) :=
    htu.deriv_of_isOpen hI (by norm_num)
  exact h1.deriv_of_isOpen hI (by norm_num)

/-
# Step 4 (Elgindi §H2, tex 931-953): the weighted square bound for `(tan θ·u)''`

Writing `v = u / cos θ`, `X = (tan θ·u)''` and `σ = sin(2θ)^{2-γ}` on `Iθ = [0, π/2]`, this
proves `∫ X² σ ≤ 3 (∫ (v'')²σ + 4 ∫ (v')²σ + ∫ v²σ)`, together with the integrability of
`X²σ` that goes with it.

Route: `Work.FTS.EllipticEst.remov.slice_v_identities` gives, for `θ ∈ (0, π/2)`,
`(tan θ·u)''θ = sin θ·v''θ + 2 cos θ·v'θ - sin θ·vθ`, so pointwise on `(0, π/2)`
`X² ≤ 3((v'')² + 4(v')² + v²)` (Cauchy–Schwarz `(a+b+c)² ≤ 3(a²+b²+c²)` and `sin²θ,cos²θ ≤ 1`).
Then bound `∫ X²σ` by the integral of an integrable function and compare
(`MeasureTheory.setIntegral_mono_ae_restrict`), using
`volume.restrict Iθ = volume.restrict (0, π/2)` to pass the pointwise facts from `(0,π/2)` to
`Iθ`, and continuity of `v, v', v'', X` on `(0,π/2)` for the strong measurability.
-/
theorem slice_Xt_sq_bound (γ : ℝ) {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)))
    (hV2 : MeasureTheory.IntegrableOn (fun θ =>
        (deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ)
    (hY2 : MeasureTheory.IntegrableOn (fun θ =>
        (deriv (fun t => u t / Real.cos t) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ)
    (hY3 : MeasureTheory.IntegrableOn (fun θ =>
        (u θ / Real.cos θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ =>
        (deriv (deriv (fun t => Real.tan t * u t)) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ
      ∧ (∫ θ in Work.Spaces.Iθ,
          (deriv (deriv (fun t => Real.tan t * u t)) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (2 - γ))
        ≤ 3 * ((∫ θ in Work.Spaces.Iθ,
                (deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ) ^ 2 *
                Real.rpow (Real.sin (2 * θ)) (2 - γ))
            + 4 * (∫ θ in Work.Spaces.Iθ,
                (deriv (fun t => u t / Real.cos t) θ) ^ 2 *
                Real.rpow (Real.sin (2 * θ)) (2 - γ))
            + (∫ θ in Work.Spaces.Iθ, (u θ / Real.cos θ) ^ 2 *
                Real.rpow (Real.sin (2 * θ)) (2 - γ))) := by
  set S : Set ℝ := Set.Ioo 0 (Real.pi / 2) with hSdef
  set σ : ℝ → ℝ := fun θ => Real.rpow (Real.sin (2 * θ)) (2 - γ) with hσdef
  set X : ℝ → ℝ := fun θ => deriv (deriv (fun t => Real.tan t * u t)) θ with hXdef
  set A : ℝ → ℝ := fun θ => deriv (fun t => deriv (fun s => u s / Real.cos s) t) θ with hAdef
  set B : ℝ → ℝ := fun θ => deriv (fun t => u t / Real.cos t) θ with hBdef
  set C : ℝ → ℝ := fun θ => u θ / Real.cos θ with hCdef
  have hSmeas : MeasurableSet S := by rw [hSdef]; exact measurableSet_Ioo
  have hset : (Work.Spaces.Iθ : Set ℝ) =ᵐ[volume] S := by
    simp only [Work.Spaces.Iθ, hSdef]
    exact (MeasureTheory.Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := Real.pi / 2)).symm
  have hrestrict : (volume.restrict Work.Spaces.Iθ : Measure ℝ) = volume.restrict S :=
    Measure.restrict_congr_set hset
  have hmem : ∀ θ ∈ S, θ ∈ Set.Ioo 0 (Real.pi / 2) := by
    intro θ hθ
    rwa [hSdef] at hθ
  -- the pointwise identity of `slice_v_identities`
  have hrel : ∀ θ ∈ S, X θ = Real.sin θ * A θ + 2 * Real.cos θ * B θ - Real.sin θ * C θ := by
    intro θ hθ
    have h := (slice_v_identities u hu θ (hmem θ hθ)).2.2.1
    simp only [hXdef, hAdef, hBdef, hCdef]
    exact h
  have hσ0 : ∀ θ ∈ S, 0 ≤ σ θ := by
    intro θ hθ
    have hsin : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [(hmem θ hθ).1])
        (by linarith [(hmem θ hθ).2, Real.pi_pos])
    simp only [hσdef]
    exact Real.rpow_nonneg hsin.le _
  have hσm : AEStronglyMeasurable σ (volume.restrict S) := by
    rw [hσdef]
    exact (by measurability : Measurable
      (fun θ : ℝ => Real.rpow (Real.sin (2 * θ)) (2 - γ))).aestronglyMeasurable
  have hXcont : ContinuousOn X S := by
    rw [hXdef, hSdef]
    exact (contDiffOn_Xt_second hu).continuousOn
  have hXm : AEStronglyMeasurable X (volume.restrict S) :=
    hXcont.aestronglyMeasurable hSmeas
  have hA : IntegrableOn (fun θ => (A θ) ^ 2 * σ θ) S := by
    show MeasureTheory.Integrable _ (volume.restrict S)
    rw [← hrestrict]
    rw [hAdef, hσdef]
    exact hV2
  have hB : IntegrableOn (fun θ => (B θ) ^ 2 * σ θ) S := by
    show MeasureTheory.Integrable _ (volume.restrict S)
    rw [← hrestrict]
    rw [hBdef, hσdef]
    exact hY2
  have hC : IntegrableOn (fun θ => (C θ) ^ 2 * σ θ) S := by
    show MeasureTheory.Integrable _ (volume.restrict S)
    rw [← hrestrict]
    rw [hCdef, hσdef]
    exact hY3
  obtain ⟨hInt, hineq⟩ :=
    integrableOn_sq_sin_cos_rel (s := S) (σ := σ) (X := X) (A := A) (B := B) (C := C)
      hσ0 hrel hXm hσm hA hB hC
  refine ⟨?_, ?_⟩
  · show MeasureTheory.Integrable _ (volume.restrict Work.Spaces.Iθ)
    rw [hrestrict]
    exact hInt
  · rw [MeasureTheory.setIntegral_congr_set hset, MeasureTheory.setIntegral_congr_set hset,
      MeasureTheory.setIntegral_congr_set hset, MeasureTheory.setIntegral_congr_set hset]
    simpa only [hXdef, hσdef, hAdef, hBdef, hCdef] using hineq

end Work.FTS.EllipticEst.remov.Step4
