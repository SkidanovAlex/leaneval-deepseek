import Mathlib

namespace Work.NN.Final

open scoped ContDiff

/-- If `η` is smooth with support contained in the open set `O` and `f` is `C^m` on `O`, then the
product `η * f` is globally `C^m`.  (Every point of `tsupport η` has a neighbourhood in `O`, where
the product is a product of `C^m` functions, while outside `tsupport η` the product vanishes
locally.) -/
theorem contDiff_mul_of_contDiffOn_tsupport {n m : ℕ} {O : Set (Fin n → ℂ)} (hO : IsOpen O)
    {η f : (Fin n → ℂ) → ℂ} (hη : ContDiff ℝ ∞ η) (hηt : tsupport η ⊆ O)
    (hf : ContDiffOn ℝ m f O) : ContDiff ℝ m (fun z => η z * f z) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ tsupport η
  · exact ((hη.of_le (by simp)).contDiffAt).mul (hf.contDiffAt (hO.mem_nhds (hηt hz)))
  · have h0 : η =ᶠ[nhds z] 0 := by
      filter_upwards [(isClosed_tsupport η).compl_mem_nhds hz] with y hy
      exact Function.notMem_support.mp fun hy' => hy (by rw [tsupport]; exact subset_closure hy')
    have hev : (fun y => η y * f y) =ᶠ[nhds z] (fun _ => 0) := by
      filter_upwards [h0] with y hy
      simp [hy]
    exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq hev

end Work.NN.Final
