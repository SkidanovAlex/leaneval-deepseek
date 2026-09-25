import Mathlib

namespace Work.NN.Core.TelTwoDF

open Set Filter
open scoped Topology ContDiff

/-- If `χ` is `C^m` with `tsupport χ ⊆ Ω` and `u` is `C^m` on the open set `Ω`,
then `χ * u` is `C^m` on the whole space: outside `tsupport χ` the product vanishes,
and on `Ω ∩ tsupport χ` it is a product of `C^m` functions. -/
theorem contDiff_mul_of_contDiffOn_of_tsupport_subset {n : ℕ} {m : ℕ} {Ω : Set (Fin n → ℂ)}
    (hΩ : IsOpen Ω) {χ u : (Fin n → ℂ) → ℂ} (hχ : ContDiff ℝ m χ) (hχs : tsupport χ ⊆ Ω)
    (hu : ContDiffOn ℝ m u Ω) : ContDiff ℝ m (fun z => χ z * u z) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport χ
  · exact (hχ.contDiffAt).mul (hu.contDiffAt (hΩ.mem_nhds (hχs hx)))
  · have hzero : ∀ y ∈ (tsupport χ)ᶜ, χ y = 0 := by
      intro y hy
      by_contra h
      exact hy (subset_tsupport χ (Function.mem_support.mpr h))
    have hev : (fun z => χ z * u z) =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := by
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hx] with y hy
      simp [hzero y hy]
    exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq hev

end Work.NN.Core.TelTwoDF
