import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Hadamard

namespace Commons.Analysis.Complex

open Set

/-- **Hadamard's three-lines theorem** (special form on the strip `0 ≤ re z ≤ 1`).

If `f : ℂ → ℂ` is entire (indeed differentiable) and bounded on the closed vertical
strip `0 ≤ re z ≤ 1`, with bounds `M0` resp. `M1` on the two boundary lines
`re z = 0` resp. `re z = 1`, then on the whole closed strip
`‖f z‖ ≤ M0 ^ (1 - z.re) * M1 ^ z.re`.

This is Mathlib's `Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁'`
after matching hypotheses: differentiability gives `DiffContOnCl` on the open strip, the
pointwise bound `B` gives `BddAbove` of the norm image, and the boundary bounds are
re-indexed along the two boundary lines. -/
theorem hadamard_three_lines (f : ℂ → ℂ) (hf : Differentiable ℂ f) {M0 M1 B : ℝ}
    (hM0 : 0 < M0) (hM1 : 0 < M1)
    (hB : ∀ z, 0 ≤ z.re → z.re ≤ 1 → ‖f z‖ ≤ B)
    (h0 : ∀ y : ℝ, ‖f ((y : ℂ) * Complex.I)‖ ≤ M0)
    (h1 : ∀ y : ℝ, ‖f (1 + (y : ℂ) * Complex.I)‖ ≤ M1) :
    ∀ z, 0 ≤ z.re → z.re ≤ 1 → ‖f z‖ ≤ M0 ^ (1 - z.re) * M1 ^ z.re := by
  intro z hz0 hz1
  refine Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁' f
    (z := z) (a := M0) (b := M1) ?_ hf.diffContOnCl ?_ ?_ ?_
  · -- `z` lies in the closed vertical strip
    show z.re ∈ Icc (0 : ℝ) 1
    exact ⟨hz0, hz1⟩
  · -- boundedness on the closed strip
    refine ⟨B, ?_⟩
    rintro y ⟨w, hw, rfl⟩
    simp only [Complex.HadamardThreeLines.verticalClosedStrip, mem_preimage, mem_Icc] at hw
    exact hB w hw.1 hw.2
  · -- bound on the line `re z = 0`
    intro w hw
    rw [mem_preimage, mem_singleton_iff] at hw
    have hw' : w = (w.im : ℂ) * Complex.I := by
      rw [← Complex.re_add_im w, hw]; simp
    rw [hw']
    exact h0 w.im
  · -- bound on the line `re z = 1`
    intro w hw
    rw [mem_preimage, mem_singleton_iff] at hw
    have hw' : w = 1 + (w.im : ℂ) * Complex.I := by
      rw [← Complex.re_add_im w, hw]; simp
    rw [hw']
    exact h1 w.im

end Commons.Analysis.Complex