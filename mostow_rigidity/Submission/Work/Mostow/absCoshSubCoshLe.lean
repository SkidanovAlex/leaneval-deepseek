import Mathlib

namespace Work.Mostow

/-- If `0 ≤ a ≤ M` and `0 ≤ b ≤ M`, then `cosh` is `sinh M`-Lipschitz on `[0, M]`:
`|cosh a - cosh b| ≤ sinh M * |a - b|`. Follows from the mean value theorem, since
the derivative of `cosh` is `sinh`, which is nonnegative and monotone on `[0, M]`. -/
lemma absCoshSubCoshLe (M a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (haM : a ≤ M) (hbM : b ≤ M) :
    |Real.cosh a - Real.cosh b| ≤ Real.sinh M * |a - b| := by
  have hbound : ∀ x ∈ Set.Icc (0 : ℝ) M, ‖deriv Real.cosh x‖ ≤ Real.sinh M := by
    intro x hx
    rw [Real.deriv_cosh, Real.norm_eq_abs,
      abs_of_nonneg (Real.sinh_nonneg_iff.mpr hx.1)]
    exact (Real.sinh_le_sinh).mpr hx.2
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := Real.cosh) (s := Set.Icc (0 : ℝ) M) (C := Real.sinh M)
    (fun x _ => Real.differentiableAt_cosh) hbound (convex_Icc 0 M) ⟨hb, hbM⟩ ⟨ha, haM⟩
  simpa only [Real.norm_eq_abs] using h

end Work.Mostow
