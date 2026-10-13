import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllSol.PkgK5.radialAuxHk

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# The radial profile is controlled by its `sin (2θ)`-multiple

The main theorem of this file: for every `k` there is `C > 0`, independent of `α ∈ (0,1/4]`
and of the radial profile `Λ`, with

`|Λ|_{ℋ^k} ≤ C · |Λ · sin 2θ|_{ℋ^k}`.

The proof is assembled in `Radial` (see `radialAuxBase`, `radialAuxAng`, `radialAuxInt`,
`radialAuxHk`): the `θ`-integral of `HkIntegrand α k (Λ)` is `Φ z · A_η` and that of
`HkIntegrand α k (Λ · sin 2θ)` is `Φ z · A_{2-η} + W α k Λ z` with `W ≥ 0` and
`W ≤ (∑_i B(α,i)) · Φ`, so that both `HkSq`s are controlled by the single number
`∫_z Φ z`.  The case distinction on `Integrable Φ` handles the junk value `0` that the
Bochner integral assigns to non-integrable functions.
-/

namespace Work.FTS.EllSol.PkgK5

/-- On `[0,∞)` the point `0` is negligible. -/
theorem Iz_ae_eq_Ioi : Work.Spaces.Iz =ᵐ[(volume : Measure ℝ)] Set.Ioi 0 := by
  have h0 : ∀ᵐ z ∂(volume : Measure ℝ), z ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simp
  filter_upwards [h0] with z hz
  exact propext ⟨fun h => lt_of_le_of_ne h (Ne.symm hz),
    fun h => by simpa only [Work.Spaces.Iz, Set.mem_Ici] using h.le⟩

theorem radialHkNorm_le_sinMul (k : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (Λ : ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      (∀ n : ℕ, ContDiffOn ℝ n Λ (Set.Ioi 0)) →
      Work.Spaces.HkNorm α k (fun z θ => Λ z)
        ≤ C * Work.Spaces.HkNorm α k (fun z θ => Λ z * Real.sin (2 * θ)) := by
  obtain ⟨A, hApos, hAbound⟩ := Work.FTS.EllipticEst.Lop_iter_sin_bound k
  have hAeta : 0 < Radial.Aeta :=
    Radial.sin_rpow_pos (by norm_num [Work.Spaces.eta]) (by norm_num [Work.Spaces.eta])
  have hAeta2 : 0 < Radial.Aeta2 :=
    Radial.sin_rpow_pos (by norm_num [Work.Spaces.eta]) (by norm_num [Work.Spaces.eta])
  refine ⟨Real.sqrt (Radial.Aeta / Radial.Aeta2) + 1, by positivity, ?_⟩
  intro α Λ hα hα1 hΛ
  have hWcont : ContinuousOn (fun z => Radial.W α k Λ z) (Set.Ioi 0) :=
    Radial.continuousOn_W α k Λ hΛ
  have hinner0 : ∀ z ∈ Set.Ioi 0,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (fun z θ => Λ z) z θ)
        = Radial.Phi k Λ z * Radial.Aeta := fun z hz => Radial.thetaIntegral_radial α k Λ hΛ hz
  have hinner1 : ∀ z ∈ Set.Ioi 0,
      (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k (fun z θ => Λ z * Real.sin (2 * θ)) z θ)
        = Radial.Phi k Λ z * Radial.Aeta2 + Radial.W α k Λ z :=
    fun z hz => Radial.thetaIntegral_sinMul α k Λ hα hα1 hΛ hz
  have hSq0 : Work.Spaces.HkSq α k (fun z θ => Λ z)
      = ∫ z in Set.Ioi 0, Radial.Phi k Λ z * Radial.Aeta := by
    rw [Work.Spaces.HkSq, MeasureTheory.setIntegral_congr_set Iz_ae_eq_Ioi]
    exact MeasureTheory.integral_congr_ae
      (MeasureTheory.ae_restrict_of_forall_mem isOpen_Ioi.measurableSet hinner0)
  have hSq1 : Work.Spaces.HkSq α k (fun z θ => Λ z * Real.sin (2 * θ))
      = ∫ z in Set.Ioi 0, (Radial.Phi k Λ z * Radial.Aeta2 + Radial.W α k Λ z) := by
    rw [Work.Spaces.HkSq, MeasureTheory.setIntegral_congr_set Iz_ae_eq_Ioi]
    exact MeasureTheory.integral_congr_ae
      (MeasureTheory.ae_restrict_of_forall_mem isOpen_Ioi.measurableSet hinner1)
  by_cases hΦint : Integrable (fun z => Radial.Phi k Λ z) (volume.restrict (Set.Ioi 0))
  · -- Case 1: `Φ` is integrable, so both `HkSq`s are controlled by `∫ Φ`.
    have hA2int : Integrable (fun z => Radial.Phi k Λ z * Radial.Aeta2)
        (volume.restrict (Set.Ioi 0)) := Integrable.mul_const hΦint _
    have hWint : Integrable (fun z => Radial.W α k Λ z) (volume.restrict (Set.Ioi 0)) := by
      refine MeasureTheory.Integrable.mono'
        (Integrable.const_mul hΦint (∑ i ∈ Finset.range (k + 1), Radial.Bcoef α i))
        (hWcont.aestronglyMeasurable isOpen_Ioi.measurableSet) ?_
      filter_upwards with z
      rw [Real.norm_of_nonneg (Radial.W_nonneg α k Λ z)]
      exact Radial.W_le_sum_Bcoef_mul_Phi α k Λ z
    have h1 : Radial.Aeta2 * (∫ z in Set.Ioi 0, Radial.Phi k Λ z)
        ≤ Work.Spaces.HkSq α k (fun z θ => Λ z * Real.sin (2 * θ)) := by
      rw [hSq1, MeasureTheory.integral_add hA2int hWint]
      have h2 : 0 ≤ ∫ z in Set.Ioi 0, Radial.W α k Λ z :=
        MeasureTheory.integral_nonneg_of_ae (MeasureTheory.ae_of_all _
          (fun z => Radial.W_nonneg α k Λ z))
      rw [MeasureTheory.integral_mul_const]
      linarith
    have h0 : Work.Spaces.HkSq α k (fun z θ => Λ z)
        = Radial.Aeta * (∫ z in Set.Ioi 0, Radial.Phi k Λ z) := by
      rw [hSq0, MeasureTheory.integral_mul_const]; ring
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, h0]
    have hsplit : Radial.Aeta * (∫ z in Set.Ioi 0, Radial.Phi k Λ z)
        = (Radial.Aeta / Radial.Aeta2)
          * (Radial.Aeta2 * (∫ z in Set.Ioi 0, Radial.Phi k Λ z)) := by
      rw [← mul_assoc, div_mul_cancel₀ _ (ne_of_gt hAeta2)]
    rw [hsplit, Real.sqrt_mul (by positivity : 0 ≤ Radial.Aeta / Radial.Aeta2)]
    have hsqrt : Real.sqrt (Radial.Aeta2 * (∫ z in Set.Ioi 0, Radial.Phi k Λ z))
        ≤ Real.sqrt (Work.Spaces.HkSq α k (fun z θ => Λ z * Real.sin (2 * θ))) :=
      Real.sqrt_le_sqrt h1
    have h0le : Real.sqrt (Radial.Aeta / Radial.Aeta2)
          * Real.sqrt (Work.Spaces.HkSq α k (fun z θ => Λ z * Real.sin (2 * θ)))
        ≤ (Real.sqrt (Radial.Aeta / Radial.Aeta2) + 1)
          * Real.sqrt (Work.Spaces.HkSq α k (fun z θ => Λ z * Real.sin (2 * θ))) := by
      have h2 : 0 ≤ Real.sqrt (Work.Spaces.HkSq α k (fun z θ => Λ z * Real.sin (2 * θ))) :=
        Real.sqrt_nonneg _
      nlinarith [h2]
    calc Real.sqrt (Radial.Aeta / Radial.Aeta2)
          * Real.sqrt (Radial.Aeta2 * (∫ z in Set.Ioi 0, Radial.Phi k Λ z))
        ≤ Real.sqrt (Radial.Aeta / Radial.Aeta2)
          * Real.sqrt (Work.Spaces.HkSq α k (fun z θ => Λ z * Real.sin (2 * θ))) :=
          mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg _)
      _ ≤ (Real.sqrt (Radial.Aeta / Radial.Aeta2) + 1)
          * Real.sqrt (Work.Spaces.HkSq α k (fun z θ => Λ z * Real.sin (2 * θ))) := h0le
  · -- Case 2: `Φ` is not integrable, so `HkSq α k (Λ) = 0` (junk value of the integral).
    have hnot : ¬ Integrable (fun z => Radial.Phi k Λ z * Radial.Aeta)
        (volume.restrict (Set.Ioi 0)) := by
      intro hc
      have hc' : Integrable (fun z => Radial.Aeta * Radial.Phi k Λ z)
          (volume.restrict (Set.Ioi 0)) :=
        Integrable.congr hc (Filter.Eventually.of_forall (fun z => by ring))
      exact hΦint ((integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (ne_of_gt hAeta)) _).mp hc')
    have h0 : Work.Spaces.HkSq α k (fun z θ => Λ z) = 0 := by
      rw [hSq0, MeasureTheory.integral_undef hnot]
    rw [Work.Spaces.HkNorm, h0, Real.sqrt_zero]
    exact mul_nonneg (by positivity)
      (Real.sqrt_nonneg (Work.Spaces.HkSq α k (fun z θ => Λ z * Real.sin (2 * θ))))

end Work.FTS.EllSol.PkgK5
