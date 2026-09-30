import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.mr_direct_defs
import Submission.Work.BMF.mr_direct_range_defs
import Submission.Work.BMF.mr_direct.mv_natIcc_mean_value
import Submission.Work.BMF.mr_direct.goodSet_E1_bound
import Submission.Work.BMF.mr_direct.goodSet_bound_range_defs
import Submission.Work.BMF.mr_direct.goodSet_range3_core
import Submission.Work.BMF.mr_direct.goodSet_range3_arith

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

open MeasureTheory intervalIntegral Finset
open scoped BigOperators

theorem goodSet_bound_range3 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (X₁ X₂ K P Q S α : ℝ) (b c : ℕ → ℂ) (u : Set ℝ),
        1 ≤ X₁ → X₁ ≤ X₂ → X₂ ≤ 4 * X₁ → 3 ≤ K → 2 ≤ P → P ≤ Q → 0 ≤ S →
        0 < α → α ≤ 1 / 4 →
        (∀ m, ‖b m‖ ≤ 1) → (∀ p, ‖c p‖ ≤ 1) →
        u ⊆ Set.Icc (-S) S →
        (∀ t ∈ u, ∀ j ∈ Work.BMF.mrDirect.indexSet K P Q,
          ‖Work.BMF.mrDirect.primePoly c K j t‖ ≤ Real.exp (-(α * (j : ℝ) / K))) →
        K * Real.log (Q / P) *
          (∑ j ∈ Work.BMF.mrDirect.indexSet K P Q,
            ∫ t in u, ‖Work.BMF.mrDirect.primePoly c K j t *
                Work.BMF.mrDirect.remPolyR b P Q K X₁ X₂ j t‖ ^ 2)
        ≤ C * (1 + 1 / α) * (K + 1) ^ 3 * (Real.log (Q / P) + 1) ^ 2 *
            (S / X₁ * Q ^ (1 - 2 * α) + X₂ / X₁ * P ^ (-(2 * α))) := by
  obtain ⟨C_W, hCWpos, hCW⟩ := window_mean_value
  refine ⟨100 * (C_W + 1), by positivity, ?_⟩
  intro X₁ X₂ K P Q S α b c u hX₁ hX₁X₂ hX₂ hK hP hPQ hS hα0 hα1 hb hc hu hgood
  have hX₁pos : 0 < X₁ := by linarith
  have hX₂pos : 0 < X₂ := by linarith
  have hPpos : 0 < P := by linarith
  have hQpos : 0 < Q := by linarith
  have hKnn : 0 ≤ K := by linarith
  have hLnn : 0 ≤ Real.log (Q / P) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hPpos]; linarith
  have hqq : 0 ≤ Q ^ (1 - 2 * α) / X₁ :=
    div_nonneg (Real.rpow_nonneg hQpos.le _) hX₁pos.le
  have hpp : 0 ≤ X₂ / X₁ * P ^ (-(2 * α)) :=
    mul_nonneg (div_nonneg hX₂pos.le hX₁pos.le) (Real.rpow_nonneg hPpos.le _)
  have hcore := goodSet_range3_core C_W hCWpos hCW X₁ X₂ K P Q S α b c u
    hX₁ hX₁X₂ hK hP hPQ hS hα0 hα1 hb hc hu hgood
  have har := goodSet_range3_arith K (Real.log (Q / P)) S (Q ^ (1 - 2 * α) / X₁)
    (X₂ / X₁ * P ^ (-(2 * α))) C_W α hK hLnn hS hqq hpp hCWpos hα0 hα1
  calc K * Real.log (Q / P) *
        (∑ j ∈ Work.BMF.mrDirect.indexSet K P Q,
          ∫ t in u, ‖Work.BMF.mrDirect.primePoly c K j t *
              Work.BMF.mrDirect.remPolyR b P Q K X₁ X₂ j t‖ ^ 2)
      ≤ K * Real.log (Q / P) * (C_W * (K * Real.log (Q / P) + 2) *
            (40 * (S * (Q ^ (1 - 2 * α) / X₁)) + 54 * (X₂ / X₁ * P ^ (-(2 * α))))) :=
        mul_le_mul_of_nonneg_left hcore (mul_nonneg hKnn hLnn)
    _ ≤ 100 * (C_W + 1) * (1 + 1 / α) * (K + 1) ^ 3 * (Real.log (Q / P) + 1) ^ 2 *
            (S * (Q ^ (1 - 2 * α) / X₁) + X₂ / X₁ * P ^ (-(2 * α))) := har
    _ = 100 * (C_W + 1) * (1 + 1 / α) * (K + 1) ^ 3 * (Real.log (Q / P) + 1) ^ 2 *
            (S / X₁ * Q ^ (1 - 2 * α) + X₂ / X₁ * P ^ (-(2 * α))) := by ring

end Work.BMF.mr_direct
