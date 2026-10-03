import Mathlib
import Submission.Work.Pert.AsmDefs

namespace Work.Pert.pert2v2

/-- Pure triangle-inequality estimate: if the `m`-th iterate of `ς` stays within `(m : ℝ) * κ` of
`ς + m`, and the points `ς, w, v, ζ - m` form a chain of bounded steps, then the iterate lands
within `1/‖α‖` of `ζ`, provided `(C + m κ + B + 2) * ‖α‖ < 1`. -/
theorem norm_iterate_sub_landed_lt {F : ℂ → ℂ} {ς ζ w v : ℂ} {α : ℂ} {m : ℕ} {C κ B : ℝ}
    (hα : α ≠ 0)
    (hw : ‖ς - w‖ ≤ C)
    (hFm : ‖F^[m] ς - (ς + (m : ℂ))‖ ≤ (m : ℝ) * κ)
    (hE : ‖v - w‖ ≤ B)
    (hζ : ‖ζ - (m : ℂ) - v‖ ≤ 2)
    (hsmall : (C + (m : ℝ) * κ + B + 2) * ‖α‖ < 1) :
    ‖F^[m] ς - ζ‖ < 1 / ‖α‖ := by
  have hαpos : 0 < ‖α‖ := norm_pos_iff.mpr hα
  -- Distance from `ς + m` to the landing point `ζ`.
  have hmid : ‖(ς + (m : ℂ)) - ζ‖ ≤ C + B + 2 := by
    have hsplit : (ς + (m : ℂ)) - ζ = (ς - w) + (w - v) + (v + (m : ℂ) - ζ) := by ring
    calc ‖(ς + (m : ℂ)) - ζ‖ = ‖(ς - w) + (w - v) + (v + (m : ℂ) - ζ)‖ := by rw [hsplit]
      _ ≤ ‖(ς - w) + (w - v)‖ + ‖v + (m : ℂ) - ζ‖ := norm_add_le _ _
      _ ≤ (‖ς - w‖ + ‖w - v‖) + ‖v + (m : ℂ) - ζ‖ := by
            have := norm_add_le (ς - w) (w - v)
            linarith
      _ ≤ (C + B) + 2 := by
            have hv : ‖v + (m : ℂ) - ζ‖ = ‖ζ - (m : ℂ) - v‖ := by
              have h : v + (m : ℂ) - ζ = -(ζ - (m : ℂ) - v) := by ring
              rw [h, norm_neg]
            have hwv : ‖w - v‖ = ‖v - w‖ := norm_sub_rev w v
            rw [hv, hwv]
            linarith
      _ = C + B + 2 := by ring
  -- Triangle inequality through `F^[m] ς → ς + m → ζ`.
  have htotal : ‖F^[m] ς - ζ‖ ≤ C + (m : ℝ) * κ + B + 2 := by
    have h1 : ‖F^[m] ς - ζ‖ ≤ ‖F^[m] ς - (ς + (m : ℂ))‖ + ‖(ς + (m : ℂ)) - ζ‖ := by
      have hle := norm_add_le (F^[m] ς - (ς + (m : ℂ))) ((ς + (m : ℂ)) - ζ)
      rwa [show (F^[m] ς - (ς + (m : ℂ))) + ((ς + (m : ℂ)) - ζ) = F^[m] ς - ζ by ring] at hle
    have h2 : ‖F^[m] ς - (ς + (m : ℂ))‖ + ‖(ς + (m : ℂ)) - ζ‖
        ≤ (m : ℝ) * κ + (C + B + 2) := add_le_add hFm hmid
    linarith
  rw [lt_div_iff₀ hαpos]
  calc ‖F^[m] ς - ζ‖ * ‖α‖
      ≤ (C + (m : ℝ) * κ + B + 2) * ‖α‖ :=
        mul_le_mul_of_nonneg_right htotal (norm_nonneg _)
    _ < 1 := hsmall

end Work.Pert.pert2v2
