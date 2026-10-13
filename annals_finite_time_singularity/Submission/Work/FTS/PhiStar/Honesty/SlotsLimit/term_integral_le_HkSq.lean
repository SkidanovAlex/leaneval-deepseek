import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.integrable_prod_of_iterated
import Submission.Work.Spaces.aesm_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.SlotsLimit

/-- **Every term of the level-`k` integrand is bounded by the level-`k` norm.**  For `h` smooth on the open quadrant and `h ∈ ℋ^k`, the `(j,i)`-sub-slot of `h` (with the guard `i = 0 ∧ j ≤ k` for the pure terms and `1 ≤ i ∧ i + j ≤ k` for the mixed ones) is bounded in weighted `L²` by the whole `ℋ^k`-norm; the weight is `termWeight α i` (the pure `w/√sin^η` for `i = 0`, `Wt` otherwise), and the integral is the set integral over the open quadrant `Q0`, which agrees with the iterated integral because the integrand vanishes on the boundary and is jointly a.e. strongly measurable (smoothness on `Q0`). -/
theorem term_integral_le_HkSq (α : ℝ) (k : ℕ) {h : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen h) (hmem : Work.Spaces.HkMem α k h)
    (j i : ℕ) (hij : (i = 0 ∧ j ≤ k) ∨ (1 ≤ i ∧ i + j ≤ k)) :
    (∫ p in Work.FTS.EllipticEst.Q0,
        (Work.Spaces.mixed j i h p.1 p.2 * termWeight α i p.1 p.2) ^ 2)
      ≤ Work.Spaces.HkSq α k h := by
  -- The open quadrant is contained in the closed one, and the weights vanish on the boundary,
  -- so it suffices to bound the single summand of `HkIntegrand` and integrate over `Iz ×ˢ Iθ`.
  have hsub : Work.FTS.EllipticEst.Q0 ⊆ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ := by
    intro p hp
    simp only [Work.FTS.EllipticEst.Q0, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp
    exact ⟨le_of_lt hp.1, le_of_lt hp.2.1, le_of_lt hp.2.2⟩
  -- **The pointwise bound**: the `(j,i)`-term of `HkIntegrand` dominates the slot.
  have hFsq : ∀ z θ : ℝ, (Work.Spaces.mixed j i h z θ
      * termWeight α i z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α k h z θ := by
    intro z θ
    rcases hij with ⟨rfl, hjk⟩ | ⟨hi1, hijk⟩
    · have htw : termWeight α 0 z θ
          = Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := by
        simp [termWeight]
      rw [Work.Spaces.mixed_zero_right, htw]
      exact Work.Spaces.sq_le_HkIntegrand_z α k h z θ j hjk
    · have hne : i ≠ 0 := by omega
      have htw : termWeight α i z θ = Work.Spaces.Wt α z θ := by
        simp [termWeight, hne]
      rw [htw]
      exact Work.Spaces.sq_le_HkIntegrand_mixed α k h z θ i j hi1 hijk
  have hHnn : ∀ z θ : ℝ, 0 ≤ Work.Spaces.HkIntegrand α k h z θ := by
    intro z θ
    rw [Work.Spaces.HkIntegrand]
    exact add_nonneg (Work.Spaces.hkZSum_nonneg α k h z θ)
      (Work.Spaces.hkMixedSum_nonneg α k h z θ)
  -- **Joint integrability** of the integrand over `Iz ×ˢ Iθ`, by one-sided Tonelli: the
  -- a.e. strong measurability comes from continuity on the open quadrant (`hsm`), and the
  -- two iterated integrability conditions are exactly `HkMem`.
  have hAE : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (fun z θ : ℝ => Work.Spaces.HkIntegrand α k h z θ))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k h p.1 p.2)
      (Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand hsm α k)
  have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ : ℝ => Work.Spaces.HkIntegrand α k h z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => hmem.1 z hz)
  obtain ⟨hInt, hEq⟩ := Work.Spaces.integrable_prod_of_iterated
    (G := fun z θ : ℝ => Work.Spaces.HkIntegrand α k h z θ) hHnn hAE hslice hmem.2
  have hvol : (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ))
      = MeasureTheory.volume.prod (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
    MeasureTheory.Measure.volume_eq_prod ℝ ℝ
  have hmeas : MeasurableSet (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    measurableSet_Ici.prod measurableSet_Icc
  have hIntOn : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k h p.1 p.2)
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    show MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k h p.1 p.2)
      ((MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    rw [hvol, ← MeasureTheory.Measure.prod_restrict (Work.Spaces.Iz) (Work.Spaces.Iθ)]
    exact hInt
  have hIntIndicator : MeasureTheory.Integrable
      ((Work.Spaces.Iz ×ˢ Work.Spaces.Iθ).indicator
        (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k h p.1 p.2))
      (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)) :=
    (MeasureTheory.integrable_indicator_iff hmeas).mpr hIntOn
  -- The product integral of the integrand is exactly the iterated integral defining `HkSq`.
  have hEqOn : (∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k h p.1 p.2) = Work.Spaces.HkSq α k h := by
    have hstep : (∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k h p.1 p.2)
        = ∫ p, Work.Spaces.HkIntegrand α k h p.1 p.2
            ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
              (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
      show (∫ p, Work.Spaces.HkIntegrand α k h p.1 p.2
            ∂((MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
              (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))) = _
      rw [hvol, ← MeasureTheory.Measure.prod_restrict (Work.Spaces.Iz) (Work.Spaces.Iθ)]
    rw [hstep, hEq]
    rfl
  -- The indicator of `Q0` is dominated by the indicator of `Iz ×ˢ Iθ`.
  have hpoint : ∀ p : ℝ × ℝ, Work.FTS.EllipticEst.Q0.indicator
        (fun p : ℝ × ℝ => (Work.Spaces.mixed j i h p.1 p.2
          * termWeight α i p.1 p.2) ^ 2) p
      ≤ (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ).indicator
        (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k h p.1 p.2) p := by
    intro p
    by_cases hp : p ∈ Work.FTS.EllipticEst.Q0
    · have hp' : p ∈ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ := hsub hp
      rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp']
      exact hFsq p.1 p.2
    · rw [Set.indicator_of_notMem hp]
      by_cases hp' : p ∈ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ
      · rw [Set.indicator_of_mem hp']
        exact hHnn p.1 p.2
      · rw [Set.indicator_of_notMem hp']
  calc (∫ p in Work.FTS.EllipticEst.Q0,
        (Work.Spaces.mixed j i h p.1 p.2 * termWeight α i p.1 p.2) ^ 2)
      = ∫ p, Work.FTS.EllipticEst.Q0.indicator
          (fun p : ℝ × ℝ => (Work.Spaces.mixed j i h p.1 p.2
            * termWeight α i p.1 p.2) ^ 2) p :=
        (MeasureTheory.integral_indicator Work.FTS.EllipticEst.isOpen_Q0.measurableSet).symm
    _ ≤ ∫ p, (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ).indicator
          (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k h p.1 p.2) p :=
        MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun p => Set.indicator_nonneg (fun _ _ => sq_nonneg _) p)
          hIntIndicator
          (Filter.Eventually.of_forall hpoint)
    _ = (∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k h p.1 p.2) :=
        MeasureTheory.integral_indicator hmeas
    _ = Work.Spaces.HkSq α k h := hEqOn

end Work.FTS.PhiStar.Honesty.SlotsLimit
