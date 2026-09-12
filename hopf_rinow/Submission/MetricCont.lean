import Submission.Metric

open scoped ENNReal
open Set Filter

namespace Submission
namespace Metric
namespace IsLocLinear

variable {M : Type*} [PseudoEMetricSpace M]

/-- Local linearity implies continuity at every point of the open interval. -/
lemma continuousAt {a b : ℝ} {c : NNReal} {γ : ℝ → M}
    (hγ : IsLocLinear a b c γ) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b) : ContinuousAt γ t₀ := by
  rw [continuousAt_def]
  intro A hA
  rcases EMetric.mem_nhds_iff.mp hA with ⟨ε, hεpos, hεball⟩
  rcases exists_lt_of_mul_ofReal hεpos c with ⟨δ₁, hδ₁pos, hδ₁⟩
  let η : ℝ := min (t₀ - a) (b - t₀)
  have hηpos : 0 < η := lt_min (sub_pos.mpr ht₀.1) (sub_pos.mpr ht₀.2)
  let δ : ℝ := min δ₁ η
  have hδpos : 0 < δ := lt_min hδ₁pos hηpos
  refine mem_of_superset (Metric.ball_mem_nhds t₀ hδpos) ?_
  intro x hx
  rw [Set.mem_preimage]
  have hdist : dist x t₀ < δ := (Metric.mem_ball).mp hx
  have habs : |x - t₀| < δ := by simpa [Real.dist_eq] using hdist
  have hδleη : δ ≤ η := min_le_right δ₁ η
  have hδlea : δ ≤ t₀ - a := le_trans hδleη (min_le_left (t₀ - a) (b - t₀))
  have hδleb : δ ≤ b - t₀ := le_trans hδleη (min_le_right (t₀ - a) (b - t₀))
  have hx₁ : |x - t₀| < δ₁ := lt_of_lt_of_le habs (min_le_left δ₁ η)
  have hxI : x ∈ Ioo a b := by
    constructor
    · have hlt₀a : |x - t₀| < t₀ - a := lt_of_lt_of_le habs hδlea
      have hneg : -(t₀ - a) < x - t₀ := (abs_lt.mp hlt₀a).1
      linarith
    · have hlt₀b : |x - t₀| < b - t₀ := lt_of_lt_of_le habs hδleb
      have hpos : x - t₀ < b - t₀ := (abs_lt.mp hlt₀b).2
      linarith
  have hle : edist (γ x) (γ t₀) ≤ (c : ℝ≥0∞) * ENNReal.ofReal |x - t₀| := by
    calc
      edist (γ x) (γ t₀) = edist (γ t₀) (γ x) := edist_comm (γ x) (γ t₀)
      _ ≤ (c : ℝ≥0∞) * ENNReal.ofReal |x - t₀| := edist_le hγ ht₀ hxI
  have hεlt : (c : ℝ≥0∞) * ENNReal.ofReal |x - t₀| < ε :=
    hδ₁ |x - t₀| (abs_nonneg (x - t₀)) hx₁
  have hxε : edist (γ x) (γ t₀) < ε := lt_of_le_of_lt hle hεlt
  exact hεball (Metric.mem_eball.mpr hxε)

/-- Local linearity implies continuity on the open interval. -/
lemma continuousOn {a b : ℝ} {c : NNReal} {γ : ℝ → M}
    (hγ : IsLocLinear a b c γ) : ContinuousOn γ (Ioo a b) := by
  rw [isOpen_Ioo.continuousOn_iff]
  intro t₀ ht₀
  exact continuousAt hγ ht₀

end IsLocLinear
end Metric
end Submission
