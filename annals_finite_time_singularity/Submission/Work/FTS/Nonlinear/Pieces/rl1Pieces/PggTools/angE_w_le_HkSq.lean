import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The weighted `L²`-bound for an angular density dominated a.e. by the `H^k`-integrand

This is the almost-everywhere version of `angE_w_le_HkSq_of_pointwise`: instead of the
pointwise domination `w z * B z θ ^ 2 ≤ HkIntegrand α k f z θ` for all `(z,θ)`, we only
assume it for every `z > 0` and almost every `θ ∈ Iθ`.

The proof is the same as in the pointwise case.  For `z > 0` the weight `w z` is positive, so
`w z * ∫_θ B z θ ^ 2 = ∫_θ w z * B z θ ^ 2`, and the a.e. domination together with the
integrability of `θ ↦ HkIntegrand α k f z θ` (from `HkMem`) gives both the integrability of
the angular slice `θ ↦ B z θ ^ 2` and the pointwise-in-`z` inequality
`w z * ∫_θ B z θ ^ 2 ≤ ∫_θ HkIntegrand α k f z θ`.  The remaining two steps —
measurability of `z ↦ ∫_θ B z θ ^ 2` from the joint measurability `hjn`, and the comparison
of the `z`-integrals over `(0,∞)` and over `Iz = [0,∞)` — are as before; the point `z = 0`
carries no weight (`w 0 = 0`) and `{0}` is null, so the restriction of the hypothesis to
`z > 0` costs nothing.
-/

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.rl1Pieces.PggTools

theorem angE_w_le_HkSq {α : ℝ} {k : ℕ} {f B : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α k f)
    (hsl : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.AEStronglyMeasurable (fun θ => B z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hjn : MeasureTheory.AEStronglyMeasurable (Function.uncurry B)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hpt : ∀ z, 0 < z → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.w z * (B z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α k f z θ) :
    (∀ z, 0 < z → MeasureTheory.IntegrableOn (fun θ => (B z θ) ^ 2) Work.Spaces.Iθ) ∧
    MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, (B z θ) ^ 2) (MeasureTheory.volume.restrict (Set.Ioi 0)) ∧
    MeasureTheory.IntegrableOn
      (fun z => Work.Spaces.w z * (∫ θ in Work.Spaces.Iθ, (B z θ) ^ 2)) (Set.Ioi 0) ∧
    (∫ z in Set.Ioi (0 : ℝ), Work.Spaces.w z * (∫ θ in Work.Spaces.Iθ, (B z θ) ^ 2))
      ≤ Work.Spaces.HkSq α k f := by
  have hIz_of_le : ∀ z : ℝ, 0 ≤ z → z ∈ Work.Spaces.Iz := fun z hz => hz
  have hw_pos : ∀ z : ℝ, 0 < z → 0 < Work.Spaces.w z := by
    intro z hz
    rw [Work.Spaces.w]
    exact div_pos (pow_pos (by linarith) 2) (pow_pos hz 2)
  have hw_nonneg : ∀ z : ℝ, 0 ≤ Work.Spaces.w z := by
    intro z
    rw [Work.Spaces.w]
    exact div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hsub : Set.Ioi (0 : ℝ) ⊆ Work.Spaces.Iz := fun z hz => hIz_of_le z (le_of_lt hz)
  -- the pointwise-in-`z` inequality, obtained by pulling the `θ`-independent factor `w z` out
  have key : ∀ z, 0 < z →
      Work.Spaces.w z * (∫ θ in Work.Spaces.Iθ, (B z θ) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := by
    intro z hz
    have hzIz : z ∈ Work.Spaces.Iz := hIz_of_le z (le_of_lt hz)
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_mono_of_nonneg
      (ae_of_all _ fun θ => mul_nonneg (hw_nonneg z) (sq_nonneg _))
      (hmem.1 z hzIz)
      (hpt z hz)
  -- each angular slice is square-integrable
  have hB2int : ∀ z, 0 < z →
      MeasureTheory.IntegrableOn (fun θ => (B z θ) ^ 2) Work.Spaces.Iθ := by
    intro z hz
    have hzIz : z ∈ Work.Spaces.Iz := hIz_of_le z (le_of_lt hz)
    have hwz : Work.Spaces.w z ≠ 0 := ne_of_gt (hw_pos z hz)
    have hmeas : MeasureTheory.AEStronglyMeasurable (fun θ => Work.Spaces.w z * (B z θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      ((hsl z hzIz).pow 2).const_mul _
    have h1 : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.w z * (B z θ) ^ 2) Work.Spaces.Iθ :=
      MeasureTheory.Integrable.mono' (hmem.1 z hzIz) hmeas (by
        filter_upwards [hpt z hz] with θ hθ
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw_nonneg z) (sq_nonneg _))]
        exact hθ)
    have h2 : MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.w z)⁻¹ * (Work.Spaces.w z * (B z θ) ^ 2)) Work.Spaces.Iθ :=
      h1.const_mul _
    have h3 : (fun θ => (Work.Spaces.w z)⁻¹ * (Work.Spaces.w z * (B z θ) ^ 2))
        = fun θ => (B z θ) ^ 2 := by
      funext θ
      rw [inv_mul_cancel_left₀ hwz]
    rwa [h3] at h2
  -- joint measurability of the angular integral
  have hB2measIz : MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, (B z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have huncurry : Function.uncurry (fun z θ => (B z θ) ^ 2)
        = fun p : ℝ × ℝ => (Function.uncurry B p) ^ 2 := by
      funext p; rfl
    have hp : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => (Function.uncurry B p) ^ 2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := hjn.pow 2
    have := hp.integral_prod_right'
    simpa [huncurry] using this
  have hB2meas0 : MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, (B z θ) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    hB2measIz.mono_measure (MeasureTheory.Measure.restrict_mono hsub le_rfl)
  have hgint : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) Work.Spaces.Iz := hmem.2
  have hgint0 : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) (Set.Ioi 0) :=
    MeasureTheory.IntegrableOn.mono_set hgint hsub
  have hwmeas : Measurable (fun z : ℝ => Work.Spaces.w z) := by
    unfold Work.Spaces.w
    fun_prop
  -- integrability of the `z`-integrand on `(0,∞)`
  have hFint : MeasureTheory.IntegrableOn
      (fun z => Work.Spaces.w z * (∫ θ in Work.Spaces.Iθ, (B z θ) ^ 2)) (Set.Ioi 0) := by
    refine MeasureTheory.Integrable.mono' hgint0 (hwmeas.aestronglyMeasurable.mul hB2meas0) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (hw_nonneg z) (MeasureTheory.integral_nonneg fun θ => sq_nonneg _))]
    exact key z hz
  refine ⟨hB2int, hB2meas0, hFint, ?_⟩
  have h1 : ∫ z in Set.Ioi (0 : ℝ), Work.Spaces.w z * (∫ θ in Work.Spaces.Iθ, (B z θ) ^ 2)
      ≤ ∫ z in Set.Ioi (0 : ℝ),
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) :=
    MeasureTheory.setIntegral_mono_ae_restrict hFint hgint0 (by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
      exact key z hz)
  have h2 : ∫ z in Set.Ioi (0 : ℝ), (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
      ≤ ∫ z in Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) :=
    MeasureTheory.setIntegral_mono_set hgint
      (ae_of_all _ fun z => MeasureTheory.integral_nonneg fun θ =>
        Work.Spaces.HkIntegrand_nonneg α k f z θ)
      (ae_of_all _ fun z hz => hIz_of_le z (le_of_lt hz))
  simpa [Work.Spaces.HkSq] using h1.trans h2

end Work.FTS.Nonlinear.Pieces.rl1Pieces.PggTools
