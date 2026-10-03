import Mathlib
import Submission.Lib.Unif2.Work.Analysis.Complex.DbarCauchy.Defs
import Submission.Lib.Unif2.Work.Analysis.Complex.DbarCauchy.dbar_representation
import Submission.Lib.Unif2.Work.Analysis.Complex.Mollify.integral_mollify_mul_eq
import Submission.Lib.Unif2.Work.Analysis.Complex.Mollify.mollify_contDiff
import Submission.Lib.Unif2.Work.Analysis.Complex.Mollify.dbar_convolution_eq

/-!
# The transport of the weak `∂̄`-equation to the mollification

If `u` is locally integrable and `∫_U u ∂̄φ = 0` for every test function `φ` with `tsupport φ ⊆ U`,
and `ρ` is a `C¹` mollifier with `tsupport ρ ⊆ closedBall 0 ε`, then the mollification
`u ⋆ ρ` again satisfies the same weak equation for every test function `φ` whose support is at
distance `≥ ε` from `∂U` (expressed as `closedBall z ε ⊆ U` for `z ∈ tsupport φ`).

This is the transport step of Weyl's lemma: it feeds the *differentiable* Weyl lemma
`Work.Analysis.Complex.DbarCauchy.analyticOnNhd_of_dbar_eq_zero` with `u ⋆ ρ`.
-/

open MeasureTheory Set
open scoped Topology Pointwise

noncomputable section

namespace Work.Analysis.Complex.DbarCauchy

/-- **The mollification of a weak `∂̄`-solution is a weak `∂̄`-solution on the `ε`-shrunk domain.** -/
theorem mollify_weak {U : Set ℂ} (hU : IsOpen U) {u : ℂ → ℂ}
    (hu : LocallyIntegrable u volume)
    (h : ∀ φ : ℂ → ℂ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ z in U, u z * dbar φ z = 0)
    {ρ : ℂ → ℝ} (hρc : ContDiff ℝ 1 ρ) (hρs : HasCompactSupport ρ) {ε : ℝ}
    (hε : ∀ t ∈ tsupport ρ, ‖t‖ ≤ ε) :
    ∀ φ : ℂ → ℂ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      (∀ z ∈ tsupport φ, Metric.closedBall z ε ⊆ U) →
      ∫ z, (∫ t, ρ t • u (z - t)) * dbar φ z = 0 := by
  intro φ hφc hφs hφU
  set Ψ : ℂ → ℂ := fun y => ∫ t, ρ t * φ (y + t) with hΨdef
  -- ψ is a reflected mollification of φ
  have hΨeq : Ψ = fun z => ∫ t, ρ (-t) • φ (z - t) := by
    funext z
    rw [hΨdef]
    simp only []
    have h1 : (∫ t, ρ t * φ (z + t)) = ∫ t, ρ t • φ (z + t) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      simp only []
      rw [Complex.real_smul]
    rw [h1, show (fun t : ℂ => ρ (-t) • φ (z - t))
        = (fun t : ℂ => (fun s : ℂ => ρ s • φ (z + s)) (-t)) from rfl,
      MeasureTheory.integral_neg_eq_self (fun s : ℂ => ρ s • φ (z + s)) volume]
  have hρᵣcd : ContDiff ℝ 1 (fun s : ℂ => ρ (-s)) := hρc.comp contDiff_neg
  have hρᵣcs : HasCompactSupport (fun s : ℂ => ρ (-s)) := by
    have h := hρs.comp_homeomorph (Homeomorph.neg ℂ)
    simpa [Function.comp_def] using h
  have hφli : LocallyIntegrable φ volume := hφc.continuous.locallyIntegrable
  have hΨcd : ContDiff ℝ 1 Ψ := by
    rw [hΨeq]
    exact Work.Analysis.Complex.Mollify.mollify_contDiff hφli hρᵣcd hρᵣcs
  -- the support of ψ lies in `tsupport φ - tsupport ρ`
  have hSupsub : Function.support Ψ ⊆ tsupport φ + (-tsupport ρ) := by
    intro z hz
    change (∫ t, ρ t * φ (z + t)) ≠ 0 at hz
    by_contra hcon
    have hcon' : ∀ a : ℂ, a ∈ tsupport φ → ∀ b : ℂ, b ∈ (-tsupport ρ) → a + b ≠ z := by
      intro a ha b hb hab
      exact hcon (hab ▸ Set.mem_add.mpr ⟨a, ha, b, hb, rfl⟩)
    have hzero : ∀ t : ℂ, ρ t * φ (z + t) = 0 := by
      intro t
      by_cases ht : t ∈ tsupport ρ
      · by_cases hzt : z + t ∈ tsupport φ
        · exact absurd (by ring : (z + t) + (-t) = z)
            (hcon' (z + t) hzt (-t) (by simpa using ht))
        · simp [image_eq_zero_of_notMem_tsupport hzt]
      · simp [image_eq_zero_of_notMem_tsupport ht]
    rw [show (∫ t, ρ t * φ (z + t)) = ∫ _t : ℂ, (0 : ℂ) from
      integral_congr_ae (Filter.Eventually.of_forall hzero), integral_zero] at hz
    exact hz rfl
  have hΨsupp : tsupport Ψ ⊆ tsupport φ + (-tsupport ρ) :=
    closure_minimal hSupsub ((hφs.isCompact.add hρs.isCompact.neg).isClosed)
  have hΨcs : HasCompactSupport Ψ :=
    (hφs.isCompact.add hρs.isCompact.neg).of_isClosed_subset isClosed_closure hΨsupp
  have hΨU : tsupport Ψ ⊆ U := by
    intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := hΨsupp hz
    refine hφU a ha ?_
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hnb : ‖b‖ ≤ ε := by
      have h1 := hε (-b) (by simpa using hb)
      simpa using h1
    calc ‖a + b - a‖ = ‖b‖ := by ring_nf
      _ ≤ ε := hnb
  -- `∂̄` of `Ψ` is the mollification of `∂̄φ`
  have hdbar : ∀ w : ℂ, dbar Ψ w = ∫ t, ρ t * dbar φ (w + t) := by
    intro w
    rw [hΨdef]
    exact Work.Analysis.Complex.Mollify.dbar_convolution_eq hρc hρs hφc hφs w
  -- the transport identity
  have hterm : (∫ z, (∫ t, ρ t • u (z - t)) * dbar φ z) = ∫ w, u w * dbar Ψ w := by
    rw [Work.Analysis.Complex.Mollify.integral_mollify_mul_eq hu hρc.continuous hρs
      (continuous_dbar φ hφc) (hasCompactSupport_dbar φ hφs)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only []
    rw [hdbar w]
  -- the integrand vanishes off `U`
  have hoff : ∀ w : ℂ, w ∉ U → u w * dbar Ψ w = 0 := by
    intro w hw
    have hw' : w ∉ tsupport Ψ := fun h => hw (hΨU h)
    have hzero : Ψ =ᶠ[𝓝 w] (fun _ : ℂ => (0 : ℂ)) :=
      notMem_tsupport_iff_eventuallyEq.mp hw'
    have hd : dbar Ψ w = 0 := by
      rw [dbar_congr hzero]
      simp
    rw [hd, mul_zero]
  rw [hterm, ← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := U) (f := fun w => u w * dbar Ψ w) hoff]
  exact h Ψ hΨcd hΨcs hΨU

end Work.Analysis.Complex.DbarCauchy
