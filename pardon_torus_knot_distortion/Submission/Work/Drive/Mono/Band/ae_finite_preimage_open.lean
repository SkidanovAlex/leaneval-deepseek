import Mathlib
import Submission.Work.Drive.Mono.Band.ae_finite_preimage

namespace Work.Drive.Mono.Band

open scoped Topology

/-- Sard in fixed dimension, **on an open domain**: for a `C¹` map `Ω : ℝ² → ℝ²` defined on an
open set `V` and a compact `K ⊆ V`, the set of target values whose fibre in `K` is infinite has
measure zero.

This is the `ContDiffOn` version of `ae_finite_preimage`, and the proof is the same accumulation
argument: an infinite fibre inside `K` accumulates at some `x₀ ∈ K`; if the derivative of `Ω` at
`x₀` were invertible, the inverse function theorem would make `Ω` locally injective there. As `V`
is a neighbourhood of `x₀`, the within-derivative at `x₀` coincides with the ordinary derivative,
so the bad values are contained in the Sard-null set `Ω '' {x ∈ V | det (fderivWithin Ω V x) = 0}`. -/
theorem ae_finite_preimage_open {Ω : ℝ × ℝ → ℝ × ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hΩ : ContDiffOn ℝ 1 Ω V) {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKV : K ⊆ V) :
    MeasureTheory.volume {y : ℝ × ℝ | (Ω ⁻¹' {y} ∩ K).Infinite} = 0 := by
  set s : Set (ℝ × ℝ) := {x ∈ V | (fderivWithin ℝ Ω V x).det = 0} with hs
  have hnull : MeasureTheory.volume (Ω '' s) = 0 := by
    refine MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero
      (MeasureTheory.volume) (s := s) (f := Ω) (f' := fun x => fderivWithin ℝ Ω V x) ?_ ?_
    · intro x hx
      exact ((hΩ.contDiffWithinAt hx.1).differentiableWithinAt one_ne_zero).hasFDerivWithinAt.mono
        (fun z hz => hz.1)
    · intro x hx
      exact hx.2
  refine MeasureTheory.measure_mono_null ?_ hnull
  rintro y hy
  -- an infinite fibre in the compact `K` has an accumulation point `x₀ ∈ K`
  obtain ⟨x₀, hx₀K, hacc⟩ := hy.exists_accPt_of_subset_isCompact hK Set.inter_subset_right
  have hcl : x₀ ∈ closure (Ω ⁻¹' {y} ∩ K) :=
    mem_closure_iff_nhds.mpr (clusterPt_principal_iff.mp hacc.clusterPt)
  have hx₀V : x₀ ∈ V := hKV hx₀K
  -- by continuity, `Ω x₀ = y`
  have hx₀y : Ω x₀ = y := by
    have hcwt : ContinuousWithinAt Ω (Ω ⁻¹' {y} ∩ K) x₀ :=
      (hΩ.continuousOn.continuousWithinAt hx₀V).mono (fun z hz => hKV hz.2)
    have hmem : Ω x₀ ∈ closure ({y} : Set (ℝ × ℝ)) :=
      hcwt.mem_closure hcl (fun z hz => hz.1)
    simpa using hmem
  refine ⟨x₀, ⟨hx₀V, ?_⟩, hx₀y⟩
  -- if the (within-)derivative at `x₀` were invertible, `Ω` would be injective near `x₀`,
  -- contradicting that `x₀` is an accumulation point of the fibre
  by_contra hdet
  have hmem : V ∈ 𝓝 x₀ := hV.mem_nhds hx₀V
  have hfd : fderivWithin ℝ Ω V x₀ = fderiv ℝ Ω x₀ := fderivWithin_of_mem_nhds hmem
  have hdet' : (fderiv ℝ Ω x₀).det ≠ 0 := by
    rw [← hfd]; exact hdet
  have hinv : (fderiv ℝ Ω x₀).IsInvertible := isInvertible_of_det_ne_zero _ hdet'
  obtain ⟨U, hU, hUinj⟩ := injOn_of_isInvertible_fderiv (hΩ.contDiffAt hmem) hinv
  obtain ⟨z, ⟨hzU, hzs⟩, hzx⟩ := (accPt_iff_nhds.mp hacc) U hU
  exact hzx (hUinj hzU (mem_of_mem_nhds hU) (by rw [hzs.1, hx₀y]))

end Work.Drive.Mono.Band
