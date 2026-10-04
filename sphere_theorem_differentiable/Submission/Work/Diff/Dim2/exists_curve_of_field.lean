import Mathlib
import Submission.Work.Diff.Dim2.Lib
import Submission.Work.Diff.Dim2.flow_of_field
import Submission.Work.Diff.ODE.flow_smooth

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Dim2

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set Filter

theorem exists_curve_of_field
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [CompactSpace M]
    {W : (x : M) → TangentSpace I x}
    (hW : ContMDiff I (I.prod (modelWithCornersSelf ℝ E)) ∞
        (fun y : M => (⟨y, W y⟩ : Bundle.TotalSpace E (TangentSpace I))))
    {ϑ : M → ℝ} (hϑ : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ ϑ)
    {x₀ : M} (h1 : ∀ᶠ y in 𝓝 x₀, mvfderiv I ϑ y (W y) = 1) :
    ∃ γ : ℝ → M,
      ContMDiff (modelWithCornersSelf ℝ ℝ) I ∞ γ ∧
      γ 0 = x₀ ∧
      (∀ t : ℝ, HasMFDerivAt (modelWithCornersSelf ℝ ℝ) I γ t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (W (γ t)))) ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), ϑ (γ t) = ϑ x₀ + t) := by
  -- The global flow of the (time-independent) field `W`, from the contract `SmoothFlow`.
  have hFlow : Submission.Diff.SmoothFlow I M := Work.Diff.ODE.flow_smooth
  obtain ⟨Φ, hΦsm, hΦself, hΦderiv, -⟩ := Work.Diff.Dim2.flow_of_field hFlow hW
  let γ : ℝ → M := fun t => Φ 0 t x₀
  have hγsm : ContMDiff (modelWithCornersSelf ℝ ℝ) I ∞ γ := by
    have hslice : ContMDiff 𝓘(ℝ,ℝ) ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod I) ∞
        (fun t : ℝ => (((0 : ℝ), t), x₀)) :=
      ContMDiff.prodMk (ContMDiff.prodMk contMDiff_const contMDiff_id) contMDiff_const
    exact hΦsm.comp hslice
  have hγ0 : γ 0 = x₀ := hΦself 0 x₀
  have hγ' : ∀ t : ℝ, HasMFDerivAt 𝓘(ℝ,ℝ) I γ t ((1 : ℝ →L[ℝ] ℝ).smulRight (W (γ t))) :=
    fun t => hΦderiv 0 t x₀
  -- Along `γ` the function `ϑ` has derivative `1`, hence `s ↦ ϑ (γ s) - s` is locally constant.
  have hmvf : ∀ t : ℝ, mvfderiv I ϑ (γ t) (W (γ t)) = 1 →
      HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) (fun s => ϑ (γ s)) t (1 : ℝ →L[ℝ] ℝ) := by
    intro t ht
    have h0 : HasMFDerivAt I (modelWithCornersSelf ℝ ℝ) ϑ (γ t) (mvfderiv I ϑ (γ t)) :=
      ((hϑ.contMDiffAt (x := γ t)).mdifferentiableAt (by simp)).hasMFDerivAt
    have h1' := h0.comp t (hγ' t)
    have hlast : (mvfderiv I ϑ (γ t) ∘SL ((1 : ℝ →L[ℝ] ℝ).smulRight (W (γ t))))
        = (1 : ℝ →L[ℝ] ℝ) := by
      apply ContinuousLinearMap.ext
      intro c
      simp [ht]
    exact hlast.symm ▸ h1'
  have hderiv : ∀ t : ℝ, mvfderiv I ϑ (γ t) (W (γ t)) = 1 →
      HasDerivAt (fun s => ϑ (γ s) - s) 0 t := by
    intro t ht
    have hfd : HasFDerivAt (fun s => ϑ (γ s)) (1 : ℝ →L[ℝ] ℝ) t := (hmvf t ht).hasFDerivAt
    have hsub : HasFDerivAt (fun s => ϑ (γ s) - s) ((1 : ℝ →L[ℝ] ℝ) - 1) t :=
      hfd.sub (hasFDerivAt_id t)
    have hh := hsub.hasDerivAt
    have hzero : ((1 : ℝ →L[ℝ] ℝ) - 1) 1 = (0 : ℝ) := by simp
    rwa [hzero] at hh
  -- The hypothesis `h1` transfers to a neighbourhood of `t = 0` along the trajectory.
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), mvfderiv I ϑ (γ t) (W (γ t)) = 1 := by
    have h1' : ∀ᶠ y in 𝓝 (γ 0), mvfderiv I ϑ y (W y) = 1 := by rw [hγ0]; exact h1
    exact hγsm.continuous.continuousAt.tendsto.eventually h1'
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hεpos, hε⟩ := hev
  -- On the whole interval `(-ε, ε)` the pointwise condition `mvfderiv ϑ · (W ·) = 1` holds.
  have hcond : ∀ s : ℝ, |s| < ε → mvfderiv I ϑ (γ s) (W (γ s)) = 1 := fun s hs =>
    hε (by simpa [Real.dist_eq] using hs)
  have hmem : (0 : ℝ) ∈ Set.Ioo (-ε) ε := ⟨by linarith, by linarith⟩
  refine ⟨γ, hγsm, hγ0, hγ', ?_⟩
  filter_upwards [isOpen_Ioo.mem_nhds hmem] with t ht
  have hD : DifferentiableOn ℝ (fun s => ϑ (γ s) - s) (Set.Ioo (-ε) ε) := fun s hs =>
    (hderiv s (hcond s (abs_lt.mpr hs))).differentiableAt.differentiableWithinAt
  have hD' : Set.EqOn (deriv (fun s => ϑ (γ s) - s)) 0 (Set.Ioo (-ε) ε) := fun s hs =>
    (hderiv s (hcond s (abs_lt.mpr hs))).deriv
  have hthis := isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo hD hD' hmem ht
  simp only [hγ0, sub_zero] at hthis
  linarith

end Work.Diff.Dim2
