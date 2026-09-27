import Mathlib.Analysis.CStarAlgebra.Classes

namespace Commons.Topology.Metric

theorem isBounded_image_similarity {c d : ℂ} (hc : c ≠ 0) (s : Set ℂ) :
    Bornology.IsBounded ((fun z : ℂ => c * z + d) '' s) ↔ Bornology.IsBounded s := by
  constructor
  · intro h
    obtain ⟨C, hC⟩ := Metric.isBounded_iff.1 h
    refine Metric.isBounded_iff.2 ⟨‖c⁻¹‖ * C, fun x hx y hy => ?_⟩
    have h1 : x - y = c⁻¹ * ((c * x + d) - (c * y + d)) := by
      rw [show (c * x + d) - (c * y + d) = c * (x - y) by ring, ← mul_assoc,
        inv_mul_cancel₀ hc, one_mul]
    calc dist x y = ‖x - y‖ := dist_eq_norm x y
      _ = ‖c⁻¹ * ((c * x + d) - (c * y + d))‖ := by rw [h1]
      _ = ‖c⁻¹‖ * ‖(c * x + d) - (c * y + d)‖ := norm_mul _ _
      _ = ‖c⁻¹‖ * dist (c * x + d) (c * y + d) := by rw [dist_eq_norm]
      _ ≤ ‖c⁻¹‖ * C :=
          mul_le_mul_of_nonneg_left (hC (⟨x, hx, rfl⟩ : c * x + d ∈ (fun z : ℂ => c * z + d) '' s) (⟨y, hy, rfl⟩ : c * y + d ∈ (fun z : ℂ => c * z + d) '' s))
            (norm_nonneg _)
  · intro h
    obtain ⟨C, hC⟩ := Metric.isBounded_iff.1 h
    refine Metric.isBounded_iff.2 ⟨‖c‖ * C, fun x hx y hy => ?_⟩
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨v, hv, rfl⟩ := hy
    have h1 : c * u + d - (c * v + d) = c * (u - v) := by ring
    calc dist (c * u + d) (c * v + d) = ‖c * u + d - (c * v + d)‖ := dist_eq_norm _ _
      _ = ‖c * (u - v)‖ := by rw [h1]
      _ = ‖c‖ * ‖u - v‖ := norm_mul _ _
      _ = ‖c‖ * dist u v := by rw [dist_eq_norm]
      _ ≤ ‖c‖ * C :=
          mul_le_mul_of_nonneg_left (hC hu hv) (norm_nonneg _)

end Commons.Topology.Metric