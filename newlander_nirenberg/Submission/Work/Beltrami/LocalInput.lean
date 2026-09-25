/-
# The local holomorphic input, from the `ℂ`-picture Beltrami solution

This file derives `Work.Beltrami.LocalHolInput` (the local existence of a `J`-holomorphic function
with nowhere vanishing differential, for an arbitrary smooth complex structure `J` on `ℂ`) from
the *normalised* Beltrami solution `Work.Beltrami.exists_hol_of_beltrami_global`:

* `standardFormC` puts the structure at the base point `z₀` into standard form: there is
  `S : ℂ ≃L[ℝ] ℂ` with `S (J z₀ v) = i * S v`;
* the pulled-back structure `pullbackC S z₀ J : u ↦ S ∘ J (z₀ + S⁻¹ u) ∘ S⁻¹` then satisfies
  `pullbackC S z₀ J 0 = JstdC 0`, so the normalised Beltrami solution applies to it;
* the solution is pulled back along `z ↦ S (z - z₀)` by the chain rule, and the `∀ᶠ`-conclusion is
  converted into the ball-shaped conclusion required by `LocalHolInput`.
-/
import Mathlib
import Submission.Work.Beltrami.Main
import Submission.Work.Beltrami.ExistsHolGlobal
import Submission.Work.Beltrami.StandardFormC

namespace Work.Beltrami

open LeanEval.Geometry.NewlanderNirenberg
open Submission
open scoped ContDiff Topology

noncomputable section

/-- The pull-back of a field of endomorphisms `J` on `ℂ` by a real-linear equivalence `S`, based at
`z₀`: `J' u = S ∘ J (z₀ + S⁻¹ u) ∘ S⁻¹`. -/
def pullbackC (S : ℂ ≃L[ℝ] ℂ) (z₀ : ℂ) (J : ℂ → ℂ →L[ℝ] ℂ) : ℂ → ℂ →L[ℝ] ℂ :=
  fun u => (S : ℂ →L[ℝ] ℂ).comp ((J (z₀ + S.symm u)).comp (S.symm : ℂ →L[ℝ] ℂ))

theorem pullbackC_apply (S : ℂ ≃L[ℝ] ℂ) (z₀ : ℂ) (J : ℂ → ℂ →L[ℝ] ℂ) (u v : ℂ) :
    pullbackC S z₀ J u v = S (J (z₀ + S.symm u) (S.symm v)) := rfl

/-- The pulled-back structure still squares to `-1`. -/
theorem pullbackC_sq (S : ℂ ≃L[ℝ] ℂ) (z₀ : ℂ) (J : ℂ → ℂ →L[ℝ] ℂ) {ρ : ℝ}
    (hJ2 : ∀ z ∈ Metric.ball z₀ ρ, ∀ v : ℂ, J z (J z v) = -v) {u : ℂ}
    (hu : z₀ + S.symm u ∈ Metric.ball z₀ ρ) :
    ∀ v : ℂ, pullbackC S z₀ J u (pullbackC S z₀ J u v) = -v := by
  intro v
  rw [pullbackC_apply, pullbackC_apply, ContinuousLinearEquiv.symm_apply_apply,
    hJ2 _ hu (S.symm v)]
  simp

/-- If `S` intertwines `J z₀` with multiplication by `i`, the pulled-back structure at `0` is the
standard structure. -/
theorem pullbackC_zero (S : ℂ ≃L[ℝ] ℂ) (z₀ : ℂ) (J : ℂ → ℂ →L[ℝ] ℂ)
    (hS : ∀ v : ℂ, S (J z₀ v) = Complex.I * S v) :
    pullbackC S z₀ J 0 = JstdC 0 := by
  ext v
  rw [pullbackC_apply, JstdC_apply]
  have h1 : z₀ + S.symm 0 = z₀ := by simp
  rw [h1, hS]
  simp

/-- Smoothness of the pulled-back structure. -/
theorem pullbackC_contDiffOn (S : ℂ ≃L[ℝ] ℂ) (z₀ : ℂ) (J : ℂ → ℂ →L[ℝ] ℂ) {ρ ρ' : ℝ}
    (hJs : ContDiffOn ℝ ∞ J (Metric.ball z₀ ρ))
    (hρ' : ∀ u : ℂ, u ∈ Metric.ball 0 ρ' → z₀ + S.symm u ∈ Metric.ball z₀ ρ) :
    ContDiffOn ℝ ∞ (pullbackC S z₀ J) (Metric.ball 0 ρ') := by
  rw [contDiffOn_clm_apply]
  intro v
  have h2 : ContDiffOn ℝ ∞ (fun u : ℂ => J (z₀ + S.symm u)) (Metric.ball 0 ρ') :=
    hJs.comp (by fun_prop) hρ'
  have h3 : ContDiffOn ℝ ∞ (fun u : ℂ => (J (z₀ + S.symm u)) (S.symm v))
      (Metric.ball 0 ρ') :=
    h2.clm_apply contDiffOn_const
  have h4 := (ContinuousLinearMap.contDiff (n := ∞) (S : ℂ →L[ℝ] ℂ)).comp_contDiffOn h3
  simpa [pullbackC, Function.comp_def] using h4

/-- The chain rule for `z ↦ w (S (z - z₀))`. -/
theorem fderiv_comp_sub_C (S : ℂ ≃L[ℝ] ℂ) (z₀ z : ℂ) (w : ℂ → ℂ)
    (hw : DifferentiableAt ℝ w (S (z - z₀))) :
    fderiv ℝ (fun y : ℂ => w (S (y - z₀))) z
      = (fderiv ℝ w (S (z - z₀))).comp (S : ℂ →L[ℝ] ℂ) := by
  have h3 : HasFDerivAt (fun y : ℂ => y - z₀) (1 : ℂ →L[ℝ] ℂ) z :=
    (hasFDerivAt_id z).sub_const z₀
  have h4 : HasFDerivAt (fun y : ℂ => (S : ℂ →L[ℝ] ℂ) y) (S : ℂ →L[ℝ] ℂ) (z - z₀) :=
    (S : ℂ →L[ℝ] ℂ).hasFDerivAt
  have h5 : HasFDerivAt (fun y : ℂ => S (y - z₀)) (S : ℂ →L[ℝ] ℂ) z := by
    have h6 := h4.comp z h3
    have h7 : (S : ℂ →L[ℝ] ℂ) ∘SL (1 : ℂ →L[ℝ] ℂ) = (S : ℂ →L[ℝ] ℂ) :=
      ContinuousLinearMap.comp_id _
    rw [h7] at h6
    simpa [Function.comp_def] using h6
  exact (hw.hasFDerivAt.comp z h5).fderiv

/-- **Holomorphy transfers across the pull-back.** -/
theorem isJHolAt_comp_C {J : ℂ → ℂ →L[ℝ] ℂ} (S : ℂ ≃L[ℝ] ℂ) (z₀ z : ℂ) {w : ℂ → ℂ}
    (hw : DifferentiableAt ℝ w (S (z - z₀)))
    (hhol : ∀ v : ℂ, fderiv ℝ w (S (z - z₀)) (pullbackC S z₀ J (S (z - z₀)) v)
        = Complex.I * fderiv ℝ w (S (z - z₀)) v) :
    ∀ v : ℂ, fderiv ℝ (fun y => w (S (y - z₀))) z (J z v)
      = Complex.I * fderiv ℝ (fun y => w (S (y - z₀))) z v := by
  intro v
  rw [fderiv_comp_sub_C S z₀ z w hw]
  simp only [ContinuousLinearMap.comp_apply]
  have hpull : pullbackC S z₀ J (S (z - z₀)) (S v) = S (J z v) := by
    rw [pullbackC_apply]
    have h1 : z₀ + S.symm (S (z - z₀)) = z := by simp
    rw [h1, ContinuousLinearEquiv.symm_apply_apply]
  change fderiv ℝ w (S (z - z₀)) (S (J z v))
      = Complex.I * fderiv ℝ w (S (z - z₀)) (S v)
  rw [← hpull]
  exact hhol (S v)

/-- **Nonvanishing of the differential transfers across the pull-back.** -/
theorem fderiv_ne_zero_comp_C (S : ℂ ≃L[ℝ] ℂ) (z₀ z : ℂ) {w : ℂ → ℂ}
    (hw : DifferentiableAt ℝ w (S (z - z₀))) (h : fderiv ℝ w (S (z - z₀)) ≠ 0) :
    fderiv ℝ (fun y : ℂ => w (S (y - z₀))) z ≠ 0 := by
  rw [fderiv_comp_sub_C S z₀ z w hw]
  intro hcon
  apply h
  have h3 : ((fderiv ℝ w (S (z - z₀))).comp (S : ℂ →L[ℝ] ℂ)).comp (S.symm : ℂ →L[ℝ] ℂ) = 0 := by
    rw [hcon]; ext v; simp
  have h4 : (fderiv ℝ w (S (z - z₀))).comp ((S : ℂ →L[ℝ] ℂ).comp (S.symm : ℂ →L[ℝ] ℂ))
      = fderiv ℝ w (S (z - z₀)) := by
    have h5 : (S : ℂ →L[ℝ] ℂ).comp (S.symm : ℂ →L[ℝ] ℂ) = 1 := by ext v; simp
    rw [h5]; ext v; simp
  have h6 : ((fderiv ℝ w (S (z - z₀))).comp (S : ℂ →L[ℝ] ℂ)).comp (S.symm : ℂ →L[ℝ] ℂ)
      = (fderiv ℝ w (S (z - z₀))).comp ((S : ℂ →L[ℝ] ℂ).comp (S.symm : ℂ →L[ℝ] ℂ)) :=
    ContinuousLinearMap.comp_assoc _ _ _
  rw [h6, h4] at h3
  exact h3

/-- **`LocalHolInput` holds, given the analytic estimates `CauchyEstimates`.** -/
theorem localHolInput_of_cauchyEstimates (H : CauchyEstimates) : LocalHolInput := by
  intro J ρ z₀ hρ hJsm hJ2
  have hz₀ : z₀ ∈ Metric.ball z₀ ρ := by
    rw [Metric.mem_ball, dist_self]; exact hρ
  obtain ⟨S, hS⟩ := standardFormC (J z₀) (hJ2 z₀ hz₀)
  -- a radius on which the pulled-back structure is defined
  obtain ⟨ρ₁, hρ₁pos, hρ₁⟩ :=
    Metric.continuousAt_iff.mp
      ((continuous_iff_continuousAt.mp (S.symm : ℂ →L[ℝ] ℂ).continuous) (0 : ℂ)) ρ hρ
  have hmem : ∀ u : ℂ, u ∈ Metric.ball 0 ρ₁ → z₀ + S.symm u ∈ Metric.ball z₀ ρ := by
    intro u hu
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    have h1 := hρ₁ (x := u) (by simpa [Metric.mem_ball, dist_eq_norm] using hu)
    rw [map_zero, dist_eq_norm, sub_zero] at h1
    exact h1
  have hJ₂sm : ContDiffOn ℝ ∞ (pullbackC S z₀ J) (Metric.ball 0 ρ₁) :=
    pullbackC_contDiffOn S z₀ J hJsm hmem
  have hJ₂2 : ∀ u ∈ Metric.ball 0 ρ₁,
      ∀ v : ℂ, pullbackC S z₀ J u (pullbackC S z₀ J u v) = -v :=
    fun u hu => pullbackC_sq S z₀ J hJ2 (hmem u hu)
  have hJ₂0 : pullbackC S z₀ J 0 = JstdC 0 := pullbackC_zero S z₀ J hS
  obtain ⟨w, hwsm, hwne0, hwhol⟩ :=
    exists_hol_of_beltrami_global H hρ₁pos hJ₂sm hJ₂2 hJ₂0
  -- holomorphy on a ball
  obtain ⟨σ₁, hσ₁pos, hσ₁⟩ := Metric.mem_nhds_iff.mp hwhol
  -- nonvanishing on a ball
  have hcont : ContinuousAt (fderiv ℝ w) (0 : ℂ) :=
    (hwsm.continuous_fderiv (by simp)).continuousAt
  obtain ⟨σ₂, hσ₂pos, hσ₂⟩ := Metric.mem_nhds_iff.mp (hcont.eventually_ne hwne0)
  -- a radius around `z₀` mapped into `ball 0 (min σ₁ σ₂)`
  obtain ⟨σ, hσpos, hσ⟩ :=
    Metric.continuousAt_iff.mp
      ((continuous_iff_continuousAt.mp (S : ℂ →L[ℝ] ℂ).continuous) (0 : ℂ))
      (min σ₁ σ₂) (lt_min hσ₁pos hσ₂pos)
  have hmaps : ∀ z ∈ Metric.ball z₀ σ, S (z - z₀) ∈ Metric.ball 0 (min σ₁ σ₂) := by
    intro z hz
    have h1 : dist (z - z₀) (0 : ℂ) < σ := by
      rw [dist_eq_norm, sub_zero, ← dist_eq_norm]
      exact Metric.mem_ball.mp hz
    have h2 := hσ h1
    rwa [map_zero] at h2
  refine ⟨fun z => w (S (z - z₀)), σ, hσpos, ?_, ?_, ?_⟩
  · have h1 : ContDiff ℝ ∞ (fun z : ℂ => S (z - z₀)) := by fun_prop
    simpa [Function.comp_def] using hwsm.comp_contDiffOn h1.contDiffOn
  · intro z hz v
    have hd : DifferentiableAt ℝ w (S (z - z₀)) := (hwsm.contDiffAt).differentiableAt (by simp)
    exact isJHolAt_comp_C S z₀ z hd
      (hσ₁ (Metric.ball_subset_ball (min_le_left σ₁ σ₂) (hmaps z hz))) v
  · intro z hz
    have hd : DifferentiableAt ℝ w (S (z - z₀)) := (hwsm.contDiffAt).differentiableAt (by simp)
    exact fderiv_ne_zero_comp_C S z₀ z hd
      (hσ₂ (Metric.ball_subset_ball (min_le_right σ₁ σ₂) (hmaps z hz)))

end

end Work.Beltrami
