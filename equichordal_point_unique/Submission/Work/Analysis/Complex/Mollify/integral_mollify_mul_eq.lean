import Mathlib

/-!
# The adjoint of mollification

For `u` locally integrable, a continuous compactly supported mollifier `ρ : ℂ → ℝ` and a continuous
compactly supported test function `ψ`,

  `∫ z, (∫ t, ρ t • u (z - t)) * ψ z = ∫ w, u w * (∫ t, ρ t * ψ (w + t))`.

This is the Fubini/translation identity which turns the weak equation `∫ u ∂̄φ = 0` into the same
equation for the mollification `u ⋆ ρ`: it is the transport step of Weyl's lemma.

Proof sketch.  Both sides are absolutely convergent.  Let `K` be a closed ball containing
`tsupport ψ - tsupport ρ` and put `ũ := K.indicator u`, so that `ũ` is integrable and agrees with `u`
on everything that matters.  The identity for `ũ` is the chain (pull `ψ z` in, Fubini, `z ↦ z - t`,
Fubini, pull `ũ w` out), and passing from `ũ` back to `u` is pointwise on the outer integrands.
-/

open MeasureTheory Set
open scoped Topology

noncomputable section

namespace Work.Analysis.Complex.Mollify

/-- **The adjoint of mollification.** -/
theorem integral_mollify_mul_eq {u : ℂ → ℂ} {ρ : ℂ → ℝ} {ψ : ℂ → ℂ}
    (hu : LocallyIntegrable u volume)
    (hρc : Continuous ρ) (hρs : HasCompactSupport ρ)
    (hψc : Continuous ψ) (hψs : HasCompactSupport ψ) :
    ∫ z, (∫ t, ρ t • u (z - t)) * ψ z = ∫ w, u w * (∫ t, ρ t * ψ (w + t)) := by
  obtain ⟨C, hC⟩ := hψs.exists_bound_of_continuousOn hψc.continuousOn
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  obtain ⟨R₁, hR₁⟩ := hψs.isBounded.subset_closedBall (0 : ℂ)
  obtain ⟨R₂, hR₂⟩ := hρs.isBounded.subset_closedBall (0 : ℂ)
  set K : Set ℂ := Metric.closedBall 0 (R₁ + R₂) with hKdef
  have hKc : IsCompact K := isCompact_closedBall (0 : ℂ) (R₁ + R₂)
  have hψ0 : ∀ z, z ∉ tsupport ψ → ψ z = 0 := fun z hz => image_eq_zero_of_notMem_tsupport hz
  have hρ0 : ∀ t, t ∉ tsupport ρ → ρ t = 0 := fun t ht => image_eq_zero_of_notMem_tsupport ht
  have hmemK : ∀ z t : ℂ, z ∈ tsupport ψ → t ∈ tsupport ρ → z - t ∈ K := by
    intro z t hz ht
    have h1 : ‖z‖ ≤ R₁ := by
      have := hR₁ hz
      rwa [Metric.mem_closedBall, dist_zero_right] at this
    have h2 : ‖t‖ ≤ R₂ := by
      have := hR₂ ht
      rwa [Metric.mem_closedBall, dist_zero_right] at this
    rw [hKdef, Metric.mem_closedBall, dist_zero_right]
    calc ‖z - t‖ ≤ ‖z‖ + ‖t‖ := norm_sub_le _ _
      _ ≤ R₁ + R₂ := by linarith
  set ũ : ℂ → ℂ := K.indicator u with hũdef
  have hũ : Integrable ũ volume := by
    rw [hũdef]
    exact (integrable_indicator_iff hKc.measurableSet).mpr (hu.integrableOn_isCompact hKc)
  have hũeq : ∀ z t : ℂ, z ∈ tsupport ψ → t ∈ tsupport ρ → ũ (z - t) = u (z - t) := by
    intro z t hz ht
    rw [hũdef]
    exact Set.indicator_of_mem (hmemK z t hz ht) u
  have houter : ∀ z : ℂ, (∫ t, ρ t • u (z - t)) * ψ z = (∫ t, ρ t • ũ (z - t)) * ψ z := by
    intro z
    by_cases hz : z ∈ tsupport ψ
    · have hinner : (∫ t, ρ t • u (z - t)) = (∫ t, ρ t • ũ (z - t)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        simp only []
        by_cases ht : t ∈ tsupport ρ
        · rw [hũeq z t hz ht]
        · rw [hρ0 t ht, zero_smul, zero_smul]
      rw [hinner]
    · rw [hψ0 z hz, mul_zero, mul_zero]
  have hRight : ∀ w : ℂ, u w * (∫ t, ρ t * ψ (w + t)) = ũ w * (∫ t, ρ t * ψ (w + t)) := by
    intro w
    by_cases hw : w ∈ K
    · rw [hũdef, Set.indicator_of_mem hw]
    · have hI : (∫ t, ρ t * ψ (w + t)) = 0 := by
        have hzero : ∀ t : ℂ, ρ t * ψ (w + t) = 0 := by
          intro t
          by_cases ht : t ∈ tsupport ρ
          · by_cases hwt : w + t ∈ tsupport ψ
            · exfalso
              exact hw (by
                have := hmemK (w + t) t hwt ht
                rwa [add_sub_cancel_right] at this)
            · rw [hψ0 (w + t) hwt, mul_zero]
          · rw [hρ0 t ht, Complex.ofReal_zero, zero_mul]
        rw [show (∫ t, ρ t * ψ (w + t)) = ∫ _t : ℂ, (0 : ℂ) from
          integral_congr_ae (Filter.Eventually.of_forall hzero), integral_zero]
      rw [hI, mul_zero, hũdef, Set.indicator_of_notMem hw u, zero_mul]
  have hρint : Integrable ρ volume := hρc.integrable_of_hasCompactSupport hρs
  have hIntA : Integrable (Function.uncurry fun z t => (ρ t : ℂ) * ũ (z - t))
      (volume.prod volume) := by
    have h := hρint.convolution_integrand (L := ContinuousLinearMap.lsmul ℝ ℝ) hũ
    have hfun : (fun p : ℂ × ℂ => (ContinuousLinearMap.lsmul ℝ ℝ (ρ p.2)) (ũ (p.1 - p.2)))
        = (Function.uncurry fun z t => (ρ t : ℂ) * ũ (z - t)) := by
      funext p
      simp only [ContinuousLinearMap.lsmul_apply, Complex.real_smul, Function.uncurry]
    rwa [hfun] at h
  have hIntB : Integrable (Function.uncurry fun z t => (ρ t : ℂ) * (ũ (z - t) * ψ z))
      (volume.prod volume) := by
    have hmeas : AEStronglyMeasurable (fun p : ℂ × ℂ => ψ p.1) (volume.prod volume) :=
      (hψc.measurable.comp measurable_fst).aestronglyMeasurable
    have hbound : ∀ᵐ p : ℂ × ℂ ∂(volume.prod volume), ‖ψ p.1‖ ≤ max C 0 := by
      filter_upwards with p
      by_cases hp : p.1 ∈ tsupport ψ
      · exact le_trans (hC p.1 hp) (le_max_left _ _)
      · rw [hψ0 p.1 hp, norm_zero]
        exact hC0
    have h := hIntA.mul_bdd hmeas hbound
    refine h.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry]
    ring_nf
  have hIntC : Integrable (Function.uncurry fun t w => (ρ t : ℂ) * (ũ w * ψ (w + t)))
      (volume.prod volume) := by
    have h1 : Integrable (fun p : ℂ × ℂ => (ρ p.1 : ℂ) * ũ p.2) (volume.prod volume) :=
      hρint.ofReal.mul_prod (g := ũ) hũ
    have hmeas : AEStronglyMeasurable (fun p : ℂ × ℂ => ψ (p.1 + p.2)) (volume.prod volume) :=
      (hψc.measurable.comp (measurable_fst.add measurable_snd)).aestronglyMeasurable
    have hbound : ∀ᵐ p : ℂ × ℂ ∂(volume.prod volume), ‖ψ (p.1 + p.2)‖ ≤ max C 0 := by
      filter_upwards with p
      by_cases hp : p.1 + p.2 ∈ tsupport ψ
      · exact le_trans (hC _ hp) (le_max_left _ _)
      · rw [hψ0 _ hp, norm_zero]
        exact hC0
    have h := h1.mul_bdd hmeas hbound
    refine h.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry]
    ring_nf
  have key : ∫ z, (∫ t, ρ t • ũ (z - t)) * ψ z = ∫ w, ũ w * (∫ t, ρ t * ψ (w + t)) := by
    calc
      ∫ z, (∫ t, ρ t • ũ (z - t)) * ψ z
          = ∫ z, ∫ t, (ρ t : ℂ) * (ũ (z - t) * ψ z) := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
            simp only []
            rw [← MeasureTheory.integral_mul_const (ψ z) (fun t => ρ t • ũ (z - t))]
            refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
            simp only []
            rw [Complex.real_smul]
            ring
        _ = ∫ t, ∫ z, (ρ t : ℂ) * (ũ (z - t) * ψ z) :=
            MeasureTheory.integral_integral_swap hIntB
        _ = ∫ t, ∫ w, (ρ t : ℂ) * (ũ w * ψ (w + t)) := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
            simp only []
            rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
            congr 1
            rw [← MeasureTheory.integral_sub_right_eq_self (fun y : ℂ => ũ y * ψ (y + t)) t]
            refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
            simp only [sub_add_cancel]
        _ = ∫ w, ∫ t, (ρ t : ℂ) * (ũ w * ψ (w + t)) :=
            MeasureTheory.integral_integral_swap hIntC
        _ = ∫ w, ũ w * (∫ t, ρ t * ψ (w + t)) := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
            simp only []
            rw [show (fun t : ℂ => (ρ t : ℂ) * (ũ w * ψ (w + t)))
                = (fun t : ℂ => ũ w * ((ρ t : ℂ) * ψ (w + t))) from funext fun t => by ring,
              MeasureTheory.integral_const_mul]
  calc ∫ z, (∫ t, ρ t • u (z - t)) * ψ z
      = ∫ z, (∫ t, ρ t • ũ (z - t)) * ψ z :=
        integral_congr_ae (Filter.Eventually.of_forall houter)
    _ = ∫ w, ũ w * (∫ t, ρ t * ψ (w + t)) := key
    _ = ∫ w, u w * (∫ t, ρ t * ψ (w + t)) :=
        (integral_congr_ae (Filter.Eventually.of_forall hRight)).symm

end Work.Analysis.Complex.Mollify
