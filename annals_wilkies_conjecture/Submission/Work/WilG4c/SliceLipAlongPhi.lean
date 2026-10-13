import Mathlib
import Submission.Work.WilG4c.SliceLipInX
import Submission.Work.WilG4c.LipDefs

namespace Work.WilG4c

theorem SliceLipAlongPhi {p n : ℕ} (F : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (φ : (Fin p → ℝ) → ℝ → ℝ) (l : Fin p → ℝ)
    (hφC1 : ContDiffOn ℝ 1 (φ l) Work.WilkG4c.I)
    (hC1 : ∀ t ∈ Work.WilkG4c.I, ∀ y ∈ WilkiesDesign.openCube n,
      ContDiffAt ℝ 1 (Work.WilkG4c.famFunHat F) (Work.WilkG4c.xPt l (φ l t) y))
    (hx : ∀ t ∈ Work.WilkG4c.I, ∀ y ∈ WilkiesDesign.openCube n,
      |Work.WilkG4c.xDeriv F l (φ l t) y| * |deriv (φ l) t| ≤ 2 * ((n : ℝ) + 1)) :
    ∀ a ∈ Work.WilkG4c.I, ∀ b ∈ Work.WilkG4c.I, ∀ y ∈ WilkiesDesign.openCube n,
      |F l (Work.WilkG4c.pt (φ l a) y) - F l (Work.WilkG4c.pt (φ l b) y)|
        ≤ (2 * ((n : ℝ) + 1)) * |a - b| := by
  intro a ha b hb y hy
  -- Chain rule: along `t ↦ φ l t`, the `x`-slice `x ↦ F l (pt x y)` composes to
  -- `t ↦ F l (pt (φ l t) y)`, whose derivative is `∂₀F · (φ l)'`.
  have hderiv : ∀ t ∈ Work.WilkG4c.I,
      HasDerivAt (fun t : ℝ => F l (Work.WilkG4c.pt (φ l t) y))
        (Work.WilkG4c.xDeriv F l (φ l t) y * deriv (φ l) t) t := by
    intro t ht
    have hφd : HasDerivAt (φ l) (deriv (φ l) t) t :=
      ((hφC1.contDiffAt (isOpen_Ioo.mem_nhds ht)).differentiableAt_one).hasDerivAt
    have hslice := Work.WilkG4c.hasDerivAt_sliceX F l (φ l t) y (hC1 t ht y hy)
    exact hslice.comp t hφd
  -- The derivative is bounded by `2 (n+1)` everywhere on `I`, by hypothesis `hx`.
  have hbound : ∀ t ∈ Work.WilkG4c.I,
      ‖deriv (fun t : ℝ => F l (Work.WilkG4c.pt (φ l t) y)) t‖ ≤ 2 * ((n : ℝ) + 1) := by
    intro t ht
    rw [Real.norm_eq_abs, (hderiv t ht).deriv, abs_mul]
    exact hx t ht y hy
  -- Mean value inequality on the convex interval `I = (0, 1)`.
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun t ht => (hderiv t ht).differentiableAt) hbound (convex_Ioo (0:ℝ) 1) ha hb
  simpa only [Real.norm_eq_abs, abs_sub_comm] using hmvt

end Work.WilG4c
