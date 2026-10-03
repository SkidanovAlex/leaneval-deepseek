import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.MeanInequalities

namespace Commons.Analysis.Integral

theorem holder_complex_finset {ι : Type*} (s : Finset ι) (u g : ι → ℂ) {p q : ℝ}
    (hpq : Real.HolderConjugate p q) :
    ‖∑ i ∈ s, u i * g i‖ ≤
      (∑ i ∈ s, ‖u i‖ ^ p) ^ (1 / p) * (∑ i ∈ s, ‖g i‖ ^ q) ^ (1 / q) := by
  calc ‖∑ i ∈ s, u i * g i‖
      ≤ ∑ i ∈ s, ‖u i * g i‖ := norm_sum_le s (fun i => u i * g i)
    _ = ∑ i ∈ s, ‖u i‖ * ‖g i‖ := by simp only [norm_mul]
    _ ≤ (∑ i ∈ s, ‖u i‖ ^ p) ^ (1 / p) * (∑ i ∈ s, ‖g i‖ ^ q) ^ (1 / q) :=
        Real.inner_le_Lp_mul_Lq_of_nonneg s (f := fun i => ‖u i‖) (g := fun i => ‖g i‖) hpq
          (fun i _ => norm_nonneg _) (fun i _ => norm_nonneg _)

end Commons.Analysis.Integral