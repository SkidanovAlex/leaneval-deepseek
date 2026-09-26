import Mathlib
import Submission.Work.Kernels.ModerateGrowth

namespace Work.CKFinal

open UpperHalfPlane Filter
open scoped Manifold

/-- If `‖F n τ - Dl τ‖ ≤ C n * (scale τ)^M` with `C n → 0` and `M ≥ 0`, then the sequence
`F n`, viewed as functions on the upper half plane embedded in `ℂ`, converges to `Dl` locally
uniformly on the upper half plane. -/
lemma tendstoLocallyUniformlyOn_of_scale_bound {F : ℕ → UpperHalfPlane → ℂ}
    {Dl : UpperHalfPlane → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hC : ∃ C : ℕ → ℝ, Filter.Tendsto C Filter.atTop (nhds 0) ∧
      ∀ (n : ℕ) (τ : UpperHalfPlane),
        ‖F n τ - Dl τ‖ ≤ C n * (Work.Kernels.scale τ) ^ M) :
    TendstoLocallyUniformlyOn (fun n : ℕ => F n ∘ ofComplex) (Dl ∘ ofComplex)
      Filter.atTop {z : ℂ | 0 < z.im} := by
  obtain ⟨C, hC0, hCb⟩ := hC
  have hs : IsOpen {z : ℂ | 0 < z.im} := isOpen_upperHalfPlaneSet
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hs]
  intro K hKs hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  -- On `K` the scale is bounded by a constant `B`.
  have hcont : ContinuousOn (fun z : ℂ => Work.Kernels.scale (ofComplex z)) K := by
    have hφc : ContinuousOn (fun z : ℂ => 1 + (z.im)⁻¹ + ‖z‖) K :=
      ((continuous_const.continuousOn.add ((Complex.continuous_im.continuousOn).inv₀
        (fun z hz => ne_of_gt (hKs hz)))).add continuous_norm.continuousOn)
    exact hφc.congr (fun z hz => by
      have hzpos : 0 < z.im := hKs hz
      have hcoe : ((ofComplex z : UpperHalfPlane) : ℂ) = z :=
        congrArg (fun w : UpperHalfPlane => (w : ℂ)) (ofComplex_apply_of_im_pos hzpos)
      simp only [Work.Kernels.scale, UpperHalfPlane.im, hcoe])
  obtain ⟨B, hB⟩ := hK.bddAbove_image
    (f := fun z : ℂ => Work.Kernels.scale (ofComplex z)) hcont
  have hCabs : Filter.Tendsto (fun n : ℕ => |C n| * B ^ M) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun n : ℕ => |C n|) Filter.atTop (nhds 0) := by
      simpa using hC0.abs
    simpa using h1.mul_const (B ^ M)
  have hCa : ∀ᶠ n : ℕ in Filter.atTop, |C n| * B ^ M < ε :=
    hCabs.eventually_lt tendsto_const_nhds hε
  filter_upwards [hCa] with n hn x hx
  simp only [Function.comp_apply, dist_eq_norm, norm_sub_rev]
  have h1 := hCb n (ofComplex x)
  have h2 : C n * (Work.Kernels.scale (ofComplex x)) ^ M
      ≤ |C n| * (Work.Kernels.scale (ofComplex x)) ^ M :=
    mul_le_mul_of_nonneg_right (le_abs_self _)
      (Real.rpow_nonneg (le_of_lt (Work.Kernels.scale_pos _)) M)
  have h3 : (Work.Kernels.scale (ofComplex x)) ^ M ≤ B ^ M :=
    Real.rpow_le_rpow (le_of_lt (Work.Kernels.scale_pos _)) (hB ⟨x, hx, rfl⟩) hM
  have h4 : |C n| * (Work.Kernels.scale (ofComplex x)) ^ M ≤ |C n| * B ^ M :=
    mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
  linarith

/-- A sequence of holomorphic functions on the upper half plane converging to `Dl` with a
quantitative locally bounded rate `C n * (scale τ)^M`, `C n → 0`, has holomorphic limit `Dl`. -/
lemma mdifferentiable_of_scale_bound {F : ℕ → UpperHalfPlane → ℂ} {Dl : UpperHalfPlane → ℂ} {M : ℝ}
    (hM : 0 ≤ M)
    (hF : ∀ n : ℕ, MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (F n))
    (hC : ∃ C : ℕ → ℝ, Filter.Tendsto C Filter.atTop (nhds 0) ∧
      ∀ (n : ℕ) (τ : UpperHalfPlane), ‖F n τ - Dl τ‖ ≤ C n * (Work.Kernels.scale τ) ^ M) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) Dl := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  have hs : IsOpen {z : ℂ | 0 < z.im} := isOpen_upperHalfPlaneSet
  have hdiff : ∀ᶠ n : ℕ in Filter.atTop,
      DifferentiableOn ℂ ((fun n : ℕ => F n ∘ ofComplex) n) {z : ℂ | 0 < z.im} :=
    Eventually.of_forall fun n => UpperHalfPlane.mdifferentiable_iff.mp (hF n)
  exact (tendstoLocallyUniformlyOn_of_scale_bound hM hC).differentiableOn hdiff hs

end Work.CKFinal
