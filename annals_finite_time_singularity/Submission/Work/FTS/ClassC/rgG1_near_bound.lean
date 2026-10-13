import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.FTS.EllExist.RadGreenDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.unusedVariables false

namespace Work.FTS.ClassC

/-- Near `0` the decaying branch `g₁ = z^{-q} ∫_0^z c t^{q-1} dt` (with `q = rgQ α m > 0`) is
dominated by `Kc z^{pc}/(pc+q)` whenever `|c t| ≤ Kc t^{pc}` for `0 < t ≤ 1`: the exponent
`pc + q - 1 > -1` makes the primitive integrate to exactly `z^{pc+q}/(pc+q)`.

No measurability of `c` is needed: if `t ↦ c t · t^{q-1}` is not a.e. strongly measurable then
Mathlib's (junk) integral vanishes and the bound is trivial, while in the measurable case the
`norm_integral_le_of_norm_le` majorant `Kc t^{pc+q-1}` is integrable. -/
theorem rgG1_near_bound {α : ℝ} (hα : 0 < α) {m : ℕ} {c : ℝ → ℝ} {pc Kc : ℝ}
    (hKc : 0 < Kc) (hpc : 0 < pc)
    (hvy : ∀ t : ℝ, 0 < t → t ≤ 1 → |c t| ≤ Kc * t ^ pc) :
    ∀ z : ℝ, 0 < z → z ≤ 1 →
      |Work.FTS.EllExist.rgG1 α m c z|
        ≤ Kc * z ^ pc / (pc + Work.FTS.EllExist.rgQ α m) := by
  intro z hz hz1
  have hqpos : 0 < Work.FTS.EllExist.rgQ α m := Work.FTS.EllExist.rgQ_pos hα m
  have hA : |Work.FTS.EllExist.rgA α m c z|
      ≤ Kc * z ^ (pc + Work.FTS.EllExist.rgQ α m) / (pc + Work.FTS.EllExist.rgQ α m) := by
    have hbound : ‖∫ t in (0:ℝ)..z, Work.FTS.EllExist.rgF1 α m c t‖
        ≤ ∫ t in (0:ℝ)..z, Kc * t ^ (pc + Work.FTS.EllExist.rgQ α m - 1) := by
      refine intervalIntegral.norm_integral_le_of_norm_le hz.le ?_ ?_
      · refine Filter.Eventually.of_forall (fun t ht => ?_)
        obtain ⟨ht0, htz⟩ := ht
        have ht1 : t ≤ 1 := le_trans htz hz1
        have hq1 : (0:ℝ) < t ^ (Work.FTS.EllExist.rgQ α m - 1) := Real.rpow_pos_of_pos ht0 _
        simp only [Work.FTS.EllExist.rgF1, Real.norm_eq_abs, abs_mul, abs_of_pos hq1]
        calc |c t| * t ^ (Work.FTS.EllExist.rgQ α m - 1)
            ≤ Kc * t ^ pc * t ^ (Work.FTS.EllExist.rgQ α m - 1) :=
              mul_le_mul_of_nonneg_right (hvy t ht0 ht1) (le_of_lt hq1)
          _ = Kc * t ^ (pc + Work.FTS.EllExist.rgQ α m - 1) := by
              rw [show Kc * t ^ pc * t ^ (Work.FTS.EllExist.rgQ α m - 1)
                    = Kc * (t ^ pc * t ^ (Work.FTS.EllExist.rgQ α m - 1)) from by ring,
                ← Real.rpow_add ht0,
                show pc + (Work.FTS.EllExist.rgQ α m - 1)
                    = pc + Work.FTS.EllExist.rgQ α m - 1 from by ring]
      · exact (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul Kc
    have hval : ∫ t in (0:ℝ)..z, Kc * t ^ (pc + Work.FTS.EllExist.rgQ α m - 1)
        = Kc * z ^ (pc + Work.FTS.EllExist.rgQ α m) / (pc + Work.FTS.EllExist.rgQ α m) := by
      rw [intervalIntegral.integral_const_mul,
        integral_rpow (Or.inl (by linarith : (-1:ℝ) < pc + Work.FTS.EllExist.rgQ α m - 1))]
      rw [Real.zero_rpow (by linarith : pc + Work.FTS.EllExist.rgQ α m - 1 + 1 ≠ 0),
        show pc + Work.FTS.EllExist.rgQ α m - 1 + 1 = pc + Work.FTS.EllExist.rgQ α m from by ring]
      ring
    rw [Work.FTS.EllExist.rgA, ← hval]
    simpa only [Real.norm_eq_abs] using hbound
  rw [Work.FTS.EllExist.rgG1, abs_mul]
  have hpos : 0 < z ^ (-(Work.FTS.EllExist.rgQ α m)) := Real.rpow_pos_of_pos hz _
  rw [abs_of_pos hpos]
  calc z ^ (-(Work.FTS.EllExist.rgQ α m)) * |Work.FTS.EllExist.rgA α m c z|
      ≤ z ^ (-(Work.FTS.EllExist.rgQ α m))
          * (Kc * z ^ (pc + Work.FTS.EllExist.rgQ α m) / (pc + Work.FTS.EllExist.rgQ α m)) :=
        mul_le_mul_of_nonneg_left hA (le_of_lt hpos)
    _ = Kc * z ^ pc / (pc + Work.FTS.EllExist.rgQ α m) := by
        rw [show z ^ (-(Work.FTS.EllExist.rgQ α m))
              * (Kc * z ^ (pc + Work.FTS.EllExist.rgQ α m) / (pc + Work.FTS.EllExist.rgQ α m))
            = Kc * (z ^ (-(Work.FTS.EllExist.rgQ α m)) * z ^ (pc + Work.FTS.EllExist.rgQ α m))
              / (pc + Work.FTS.EllExist.rgQ α m) from by ring]
        rw [← Real.rpow_add hz,
          show (-(Work.FTS.EllExist.rgQ α m)) + (pc + Work.FTS.EllExist.rgQ α m) = pc from by ring]

end Work.FTS.ClassC
