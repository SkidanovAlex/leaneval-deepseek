import Mathlib

namespace Work.RPB.B2

open scoped ContDiff
open Filter

/-- If `χ` is `C^n` on all of `X`, `h` is `C^n` on an open set `U`, and the (closed) support of
`χ` is contained in `U`, then `x ↦ χ x * h x` is `C^n` on all of `X`: near points of `U` both
factors are smooth, while off `U` the function `χ` vanishes on a whole neighbourhood. -/
theorem contDiff_mul_of_contDiffOn {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {h χ : X → ℝ} {n : WithTop ℕ∞} {U : Set X} (hU : IsOpen U) (hh : ContDiffOn ℝ n h U)
    (hχ : ContDiff ℝ n χ) (hsub : tsupport χ ⊆ U) :
    ContDiff ℝ n (fun x => χ x * h x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact (hχ.contDiffAt).mul (hh.contDiffAt (hU.mem_nhds hx))
  · apply ContDiffAt.congr_of_eventuallyEq (contDiffAt_const (c := (0 : ℝ)) (x := x))
    have hzero : ∀ᶠ y in nhds x, χ y = 0 := by
      have hx' : x ∈ (tsupport χ)ᶜ := by
        simp only [Set.mem_compl_iff]
        exact fun h => hx (hsub h)
      refine Filter.mem_of_superset ((isClosed_tsupport χ).isOpen_compl.mem_nhds hx') ?_
      intro y hy
      simp only [Set.mem_compl_iff] at hy
      exact Function.notMem_support.mp (fun hsy => hy (subset_tsupport χ hsy))
    filter_upwards [hzero] with y hy
    rw [hy, zero_mul]

end Work.RPB.B2
