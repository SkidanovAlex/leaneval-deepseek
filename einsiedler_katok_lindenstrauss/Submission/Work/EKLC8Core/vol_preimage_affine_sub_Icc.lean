import Mathlib
import Submission.Work.EKLC8Core.Vol

namespace Work.EKLC8Core

/-- The affine map `x ↦ a * x + b`, for `a > 0`, carries the interval `[0,T]` onto
`[b, b + a*T]`; consequently the preimage of a set `Q` under it, cut down to `[0,T]`,
is exactly the preimage of `Q ∩ [b, b + a*T]`. -/
theorem preimage_affine_inter_Icc_eq {a b T : ℝ} (ha : 0 < a) (Q : Set ℝ) :
    (fun x : ℝ => a * x + b) ⁻¹' Q ∩ Set.Icc 0 T
      = (fun x : ℝ => a * x + b) ⁻¹' (Q ∩ Set.Icc b (b + a * T)) := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Icc]
  constructor
  · intro ⟨hQ, hx0, hxT⟩
    exact ⟨hQ, by nlinarith [mul_nonneg ha.le hx0],
      by nlinarith [mul_le_mul_of_nonneg_left hxT ha.le]⟩
  · intro ⟨hQ, hb, hbT⟩
    exact ⟨hQ, by nlinarith, by nlinarith⟩

theorem vol_preimage_affine_sub_Icc {a b T : ℝ} (ha : 0 < a) (Q : Set ℝ) :
    Work.EKLC8Core.vol ((fun x : ℝ => a * x + b) ⁻¹' Q ∩ Set.Icc 0 T)
      = a⁻¹ * Work.EKLC8Core.vol (Q ∩ Set.Icc b (b + a * T)) := by
  rw [preimage_affine_inter_Icc_eq ha Q, vol_preimage_affine (ne_of_gt ha), abs_of_pos ha]

end Work.EKLC8Core
