import Mathlib
import Submission.Work.Analysis.Harmonic.integral_inner_gradient_eq_zero

namespace Work.Analysis.Harmonic

open MeasureTheory
open scoped Topology Gradient

/-- The set of points at which a function is `C¹` is open: being `C¹` at `z` means being `C¹` on a
neighbourhood of `z`, and on that neighbourhood the function is `C¹` at every point. -/
lemma isOpen_setOf_contDiffAt_one_complex (h : ℂ → ℝ) :
    IsOpen {z : ℂ | ContDiffAt ℝ 1 h z} := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  have hz' : ContDiffAt ℝ 1 h z := hz
  obtain ⟨u, hu, huC⟩ : ∃ u ∈ 𝓝 z, ContDiffOn ℝ 1 h u := hz'.contDiffOn le_rfl (by simp)
  obtain ⟨v, hvu, hvopen, hzv⟩ := mem_nhds_iff.mp hu
  refine Filter.mem_of_superset (hvopen.mem_nhds hzv) ?_
  intro y hy
  exact (huC.mono hvu).contDiffAt (hvopen.mem_nhds hy)

/-- **Integrability of the Dirichlet pairing against a function that is `C¹` near the support.**
If `φ` is `C¹` with compact support and `h` is `C¹` at every point of `tsupport φ`, then
`z ↦ ⟪∇h z, ∇φ z⟫` is integrable. (Proof idea: a smooth Urysohn cutoff `ψ` equal to `1` on a
neighbourhood of `tsupport φ` and supported where `h` is `C¹` makes `ψ·h` globally `C¹` with compact
support; `∇(ψh) = ∇h` on `tsupport φ`, so `⟪∇h,∇φ⟫ = ⟪∇(ψh),∇φ⟫` everywhere, and the latter is
continuous with compact support, hence integrable.) -/
theorem integrable_inner_gradient_of_contDiffAt_near {h φ : ℂ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (hh : ∀ z ∈ tsupport φ, ContDiffAt ℝ 1 h z) :
    MeasureTheory.Integrable (fun z ↦ inner (𝕜 := ℝ) (gradient h z) (gradient φ z))
      MeasureTheory.volume := by
  -- A smooth cutoff which is `1` near `tsupport φ` and supported where `h` is `C¹`.
  obtain ⟨ψ, hψC, hψsupp, V, hVopen, hKV, hψV⟩ :=
    exists_contDiff_eqOn_one_of_isCompact_subset_isOpen (K := tsupport φ)
      (U := {z | ContDiffAt ℝ 1 h z}) hφc (isOpen_setOf_contDiffAt_one_complex h) hh
  set H : ℂ → ℝ := fun z => ψ z * h z with hHdef
  -- `ψ * h` is globally `C¹`: on `tsupport ψ` it is a product of `C¹` functions, elsewhere it
  -- vanishes identically near the point.
  have hHC : ContDiff ℝ 1 H := by
    rw [hHdef, contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ tsupport ψ
    · exact (hψC.contDiffAt.of_le (by norm_num)).mul (hψsupp hz)
    · have hzero : (fun y => ψ y * h y) =ᶠ[𝓝 z] 0 := by
        filter_upwards [(isClosed_tsupport ψ).isOpen_compl.mem_nhds hz] with y hy
        rw [image_eq_zero_of_notMem_tsupport hy]
        simp
      exact contDiffAt_const.congr_of_eventuallyEq hzero
  -- Hence the pairing `⟪∇(ψ h), ∇φ⟫` is continuous ...
  have hgradcont : Continuous (fun z : ℂ => gradient H z) := by
    have hfd : Continuous (fun z : ℂ => fderiv ℝ H z) := hHC.continuous_fderiv one_ne_zero
    show Continuous (fun z => (InnerProductSpace.toDual ℝ ℂ).symm (fderiv ℝ H z))
    exact ((InnerProductSpace.toDual ℝ ℂ).symm.isometry.continuous).comp hfd
  have hgradφcont : Continuous (fun z : ℂ => gradient φ z) := by
    have hfd : Continuous (fun z : ℂ => fderiv ℝ φ z) := hφ.continuous_fderiv one_ne_zero
    show Continuous (fun z => (InnerProductSpace.toDual ℝ ℂ).symm (fderiv ℝ φ z))
    exact ((InnerProductSpace.toDual ℝ ℂ).symm.isometry.continuous).comp hfd
  have hcont : Continuous (fun z : ℂ => inner (𝕜 := ℝ) (gradient H z) (gradient φ z)) :=
    hgradcont.inner hgradφcont
  -- ... and compactly supported, since the support is contained in `tsupport (∇φ) ⊆ tsupport φ`.
  have hcs : HasCompactSupport
      (fun z : ℂ => inner (𝕜 := ℝ) (gradient H z) (gradient φ z)) := by
    refine HasCompactSupport.intro'
      (IsCompact.of_isClosed_subset hφc (isClosed_tsupport _) (tsupport_gradient_subset φ))
      (isClosed_tsupport _) ?_
    intro z hz
    rw [image_eq_zero_of_notMem_tsupport hz, inner_zero_right]
  -- `ψ * h` agrees with `h` near every point of `tsupport φ`.
  have hHeq : ∀ z ∈ tsupport φ, H =ᶠ[𝓝 z] h := by
    intro z hz
    filter_upwards [hVopen.mem_nhds (hKV hz)] with y hy
    show ψ y * h y = h y
    rw [hψV hy, Pi.one_apply, one_mul]
  -- The two pairings therefore agree everywhere, and the second one is integrable.
  refine (Continuous.integrable_of_hasCompactSupport hcont hcs).congr
    (Filter.Eventually.of_forall ?_)
  intro z
  dsimp only
  by_cases hz : gradient φ z = 0
  · rw [hz, inner_zero_right, inner_zero_right]
  · have hzK : z ∈ tsupport φ :=
      tsupport_gradient_subset φ (subset_closure (by rwa [Function.mem_support]))
    rw [(hHeq z hzK).gradient_eq]

end Work.Analysis.Harmonic
