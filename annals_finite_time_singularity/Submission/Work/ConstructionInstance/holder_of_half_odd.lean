import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.ConstructionInstance.Defs
import Submission.Work.Cyl.dist_reflZ_le
import Submission.Work.Cyl.dist_mid_neg_le
import Submission.Work.Cyl.dist_mid_pos_le
import Submission.Work.Stability.holderWith_of_dist_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

open scoped NNReal

/-- Extend a Hölder map from the closed half space `{x₂ ≥ 0}` to `ℝ³` along the odd reflection
`Cyl.reflZ = (x₀,x₁,-x₂)`: if `Φ` is `α`-Hölder and vanishes on the plane `{x₂ = 0}`, and `ω`
agrees with `Φ` on `{x₂ ≥ 0}` and satisfies `ω (reflZ x) = - ω x`, then `ω` is `α`-Hölder
(with constant `3 C_Φ`).

Intended proof.  Let `C` be a Hölder constant of `Φ`.  For `x,y`:
* `x₂, y₂ ≥ 0`:  `ω x - ω y = Φ x - Φ y`, so `‖ω x - ω y‖ ≤ C ‖x-y‖^α`.
* `x₂, y₂ < 0`:  reflect both (`reflZ` preserves `dist`, and `ω (reflZ z) = -ω z`).
* `x₂ ≥ 0 > y₂`:  put `ry = reflZ y` (so `(ry)₂ = -y₂ ≥ 0`) and `yp = !₂[y 0, y 1, 0]`
  (so `(yp)₂ = 0`). Then
  `ω x - ω y = ω x + ω ry = (Φ x - Φ ry) + 2 (Φ ry - Φ yp)` (using `Φ yp = 0`), whence
  `‖ω x - ω y‖ ≤ C ‖x - ry‖^α + 2 C ‖ry - yp‖^α`.  Now `‖x - ry‖ ≤ ‖x - y‖` and
  `‖ry - yp‖ = |y₂| ≤ ‖x - y‖` (both from `Work.Cyl.dist_sq_coords`, using `x₂ ≥ 0 > y₂`),
  so the bound is `≤ 3 C ‖x-y‖^α`.
* `x₂ < 0 ≤ y₂`: symmetric.
Finish with `Work.Stability.holderWith_of_dist_le` (or `AuxOmegaStar.holder_of_norm_le`). -/
theorem holder_of_half_odd {ω Φ : R3 → R3} {α : ℝ} (hα : 0 < α)
    (hΦ : Holder ⟨α, hα.le⟩ Φ)
    (hhalf : ∀ x : R3, 0 ≤ x 2 → ω x = Φ x)
    (hodd : ∀ x : R3, ω (Work.Cyl.reflZ x) = - ω x)
    (hplane : ∀ x : R3, x 2 = 0 → Φ x = 0) :
    Holder ⟨α, hα.le⟩ ω := by
  obtain ⟨C, hC⟩ := hΦ
  have hΦb : ∀ a b : R3, ‖Φ a - Φ b‖ ≤ (C : ℝ) * ‖a - b‖ ^ α := by
    intro a b
    rw [← dist_eq_norm, ← dist_eq_norm]
    exact hC.dist_le a b
  have hCnn : (0 : ℝ) ≤ (C : ℝ) := C.coe_nonneg
  have key : ∀ x y : R3, ‖ω x - ω y‖ ≤ 3 * (C : ℝ) * ‖x - y‖ ^ α := by
    intro x y
    have hxy : (0 : ℝ) ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
    have refl2 : ∀ z : R3, (Work.Cyl.reflZ z) 2 = - z 2 := by
      intro z; simp [Work.Cyl.reflZ]
    -- the two "mixed" configurations all start from the same decomposition of `Φ a + Φ b`
    rcases le_or_gt (0 : ℝ) (x 2) with hx | hx
    · rcases le_or_gt (0 : ℝ) (y 2) with hy | hy
      · -- both points in the closed half space
        rw [hhalf x hx, hhalf y hy]
        calc ‖Φ x - Φ y‖ ≤ (C : ℝ) * ‖x - y‖ ^ α := hΦb x y
          _ ≤ 3 * (C : ℝ) * ‖x - y‖ ^ α := by nlinarith
      · -- `x₂ ≥ 0 > y₂`
        have hy2 : 0 ≤ (Work.Cyl.reflZ y) 2 := by rw [refl2]; linarith
        have hry : ω (Work.Cyl.reflZ y) = Φ (Work.Cyl.reflZ y) := hhalf _ hy2
        have hwx : ω x = Φ x := hhalf x hx
        have hwy : ω y = - Φ (Work.Cyl.reflZ y) := by
          have h := hodd y
          rw [hry] at h
          rw [h]; simp
        have hmid : Φ (!₂[y 0, y 1, (0:ℝ)]) = 0 := hplane _ (by simp)
        have h1 := (Work.Cyl.dist_mid_neg_le hx hy).1
        have h2 := (Work.Cyl.dist_mid_neg_le hx hy).2
        have hpb : ‖Φ x + Φ (Work.Cyl.reflZ y)‖ ≤ 2 * (C : ℝ) * ‖x - y‖ ^ α := by
          have hdec : Φ x + Φ (Work.Cyl.reflZ y)
              = (Φ x - Φ (!₂[y 0, y 1, (0:ℝ)]))
                + (Φ (Work.Cyl.reflZ y) - Φ (!₂[y 0, y 1, (0:ℝ)])) := by
            rw [hmid]; abel
          rw [hdec]
          have htri := norm_add_le (Φ x - Φ (!₂[y 0, y 1, (0:ℝ)]))
            (Φ (Work.Cyl.reflZ y) - Φ (!₂[y 0, y 1, (0:ℝ)]))
          have ha : ‖Φ x - Φ (!₂[y 0, y 1, (0:ℝ)])‖ ≤ (C : ℝ) * ‖x - y‖ ^ α := by
            calc ‖Φ x - Φ (!₂[y 0, y 1, (0:ℝ)])‖
                ≤ (C : ℝ) * ‖x - !₂[y 0, y 1, (0:ℝ)]‖ ^ α := hΦb x _
              _ ≤ (C : ℝ) * ‖x - y‖ ^ α := by
                  apply mul_le_mul_of_nonneg_left _ hCnn
                  apply Real.rpow_le_rpow (norm_nonneg _) _ hα.le
                  rw [← dist_eq_norm, ← dist_eq_norm]
                  exact h1
          have hb : ‖Φ (Work.Cyl.reflZ y) - Φ (!₂[y 0, y 1, (0:ℝ)])‖
              ≤ (C : ℝ) * ‖x - y‖ ^ α := by
            calc ‖Φ (Work.Cyl.reflZ y) - Φ (!₂[y 0, y 1, (0:ℝ)])‖
                ≤ (C : ℝ) * ‖Work.Cyl.reflZ y - !₂[y 0, y 1, (0:ℝ)]‖ ^ α := hΦb _ _
              _ ≤ (C : ℝ) * ‖x - y‖ ^ α := by
                  apply mul_le_mul_of_nonneg_left _ hCnn
                  apply Real.rpow_le_rpow (norm_nonneg _) _ hα.le
                  rw [← dist_eq_norm, ← dist_eq_norm]
                  exact h2
          calc ‖(Φ x - Φ (!₂[y 0, y 1, (0:ℝ)]))
                  + (Φ (Work.Cyl.reflZ y) - Φ (!₂[y 0, y 1, (0:ℝ)]))‖
              ≤ _ := htri
            _ ≤ (C : ℝ) * ‖x - y‖ ^ α + (C : ℝ) * ‖x - y‖ ^ α := add_le_add ha hb
            _ = 2 * (C : ℝ) * ‖x - y‖ ^ α := by ring
        have hsplit : ω x - ω y = Φ x + Φ (Work.Cyl.reflZ y) := by rw [hwx, hwy]; abel
        rw [hsplit]
        calc ‖Φ x + Φ (Work.Cyl.reflZ y)‖ ≤ 2 * (C : ℝ) * ‖x - y‖ ^ α := hpb
          _ ≤ 3 * (C : ℝ) * ‖x - y‖ ^ α := by nlinarith
    · rcases le_or_gt (0 : ℝ) (y 2) with hy | hy
      · -- `x₂ < 0 ≤ y₂`
        have hx2 : 0 ≤ (Work.Cyl.reflZ x) 2 := by rw [refl2]; linarith
        have hrx : ω (Work.Cyl.reflZ x) = Φ (Work.Cyl.reflZ x) := hhalf _ hx2
        have hwx : ω x = - Φ (Work.Cyl.reflZ x) := by
          have h := hodd x
          rw [hrx] at h
          rw [h]; simp
        have hwy : ω y = Φ y := hhalf y hy
        have hmid : Φ (!₂[y 0, y 1, (0:ℝ)]) = 0 := hplane _ (by simp)
        have h1 := (Work.Cyl.dist_mid_pos_le hx hy).1
        have h2 := (Work.Cyl.dist_mid_pos_le hx hy).2
        have hpb : ‖Φ (Work.Cyl.reflZ x) + Φ y‖ ≤ 2 * (C : ℝ) * ‖x - y‖ ^ α := by
          have hdec : Φ (Work.Cyl.reflZ x) + Φ y
              = (Φ (Work.Cyl.reflZ x) - Φ (!₂[y 0, y 1, (0:ℝ)]))
                + (Φ y - Φ (!₂[y 0, y 1, (0:ℝ)])) := by
            rw [hmid]; abel
          rw [hdec]
          have htri := norm_add_le (Φ (Work.Cyl.reflZ x) - Φ (!₂[y 0, y 1, (0:ℝ)]))
            (Φ y - Φ (!₂[y 0, y 1, (0:ℝ)]))
          have ha : ‖Φ (Work.Cyl.reflZ x) - Φ (!₂[y 0, y 1, (0:ℝ)])‖
              ≤ (C : ℝ) * ‖x - y‖ ^ α := by
            calc ‖Φ (Work.Cyl.reflZ x) - Φ (!₂[y 0, y 1, (0:ℝ)])‖
                ≤ (C : ℝ) * ‖Work.Cyl.reflZ x - !₂[y 0, y 1, (0:ℝ)]‖ ^ α := hΦb _ _
              _ ≤ (C : ℝ) * ‖x - y‖ ^ α := by
                  apply mul_le_mul_of_nonneg_left _ hCnn
                  apply Real.rpow_le_rpow (norm_nonneg _) _ hα.le
                  rw [← dist_eq_norm, ← dist_eq_norm]
                  exact h1
          have hb : ‖Φ y - Φ (!₂[y 0, y 1, (0:ℝ)])‖ ≤ (C : ℝ) * ‖x - y‖ ^ α := by
            calc ‖Φ y - Φ (!₂[y 0, y 1, (0:ℝ)])‖
                ≤ (C : ℝ) * ‖y - !₂[y 0, y 1, (0:ℝ)]‖ ^ α := hΦb y _
              _ ≤ (C : ℝ) * ‖x - y‖ ^ α := by
                  apply mul_le_mul_of_nonneg_left _ hCnn
                  apply Real.rpow_le_rpow (norm_nonneg _) _ hα.le
                  rw [← dist_eq_norm, ← dist_eq_norm]
                  exact h2
          calc ‖(Φ (Work.Cyl.reflZ x) - Φ (!₂[y 0, y 1, (0:ℝ)]))
                  + (Φ y - Φ (!₂[y 0, y 1, (0:ℝ)]))‖
              ≤ _ := htri
            _ ≤ (C : ℝ) * ‖x - y‖ ^ α + (C : ℝ) * ‖x - y‖ ^ α := add_le_add ha hb
            _ = 2 * (C : ℝ) * ‖x - y‖ ^ α := by ring
        have hsplit : ω x - ω y = - (Φ (Work.Cyl.reflZ x) + Φ y) := by rw [hwx, hwy]; abel
        rw [hsplit, norm_neg]
        calc ‖Φ (Work.Cyl.reflZ x) + Φ y‖ ≤ 2 * (C : ℝ) * ‖x - y‖ ^ α := hpb
          _ ≤ 3 * (C : ℝ) * ‖x - y‖ ^ α := by nlinarith
      · -- both points below the plane
        have hx2 : 0 ≤ (Work.Cyl.reflZ x) 2 := by rw [refl2]; linarith
        have hy2 : 0 ≤ (Work.Cyl.reflZ y) 2 := by rw [refl2]; linarith
        have hrx : ω (Work.Cyl.reflZ x) = Φ (Work.Cyl.reflZ x) := hhalf _ hx2
        have hry : ω (Work.Cyl.reflZ y) = Φ (Work.Cyl.reflZ y) := hhalf _ hy2
        have hwx : ω x = - Φ (Work.Cyl.reflZ x) := by
          have h := hodd x
          rw [hrx] at h
          rw [h]; simp
        have hwy : ω y = - Φ (Work.Cyl.reflZ y) := by
          have h := hodd y
          rw [hry] at h
          rw [h]; simp
        have hsplit : ω x - ω y
            = - (Φ (Work.Cyl.reflZ x) - Φ (Work.Cyl.reflZ y)) := by rw [hwx, hwy]; abel
        rw [hsplit, norm_neg]
        calc ‖Φ (Work.Cyl.reflZ x) - Φ (Work.Cyl.reflZ y)‖
            ≤ (C : ℝ) * ‖Work.Cyl.reflZ x - Work.Cyl.reflZ y‖ ^ α := hΦb _ _
          _ ≤ (C : ℝ) * ‖x - y‖ ^ α := by
              apply mul_le_mul_of_nonneg_left _ hCnn
              apply Real.rpow_le_rpow (norm_nonneg _) _ hα.le
              rw [← dist_eq_norm, ← dist_eq_norm]
              exact Work.Cyl.dist_reflZ_le x y
          _ ≤ 3 * (C : ℝ) * ‖x - y‖ ^ α := by nlinarith
  refine ⟨3 * C, ?_⟩
  apply Work.Stability.holderWith_of_dist_le (C := 3 * C) (r := ⟨α, hα.le⟩)
  intro x y
  rw [dist_eq_norm, dist_eq_norm]
  have hco : ((3 * C : ℝ≥0) : ℝ) = 3 * (C : ℝ) := by push_cast; ring
  rw [hco]
  exact key x y

end Work.ConstructionInstance
