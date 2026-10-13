import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.ModalSolR

open MeasureTheory

/-- `t ^ (-β/2) · t ^ (-β/2) = t ^ (-β)` for `t > 0`: the exponent `-β/2` is one half of `-β`. -/
private theorem rpow_half_mul_half {t : ℝ} (ht : 0 < t) (β : ℝ) :
    t ^ (-β / 2) * t ^ (-β / 2) = t ^ (-β) := by
  rw [← Real.rpow_add ht]
  congr 1
  ring

/-- `t ^ (-β/2) · t ^ (-β/2 - 1) = t ^ (-β - 1)` for `t > 0`. -/
private theorem rpow_half_mul_half_sub_one {t : ℝ} (ht : 0 < t) (β : ℝ) :
    t ^ (-β / 2) * t ^ (-β / 2 - 1) = t ^ (-β - 1) := by
  rw [← Real.rpow_add ht]
  congr 1
  ring

/-- `t ^ (-β/2 - 1) · t ^ (-β/2 - 1) = t ^ (-β - 2)` for `t > 0`. -/
private theorem rpow_sub_half_mul_sub_half {t : ℝ} (ht : 0 < t) (β : ℝ) :
    t ^ (-β / 2 - 1) * t ^ (-β / 2 - 1) = t ^ (-β - 2) := by
  rw [← Real.rpow_add ht]
  congr 1
  ring

/-- For `c` with `∫_0^∞ c² < ∞` and `β ≥ 0`, the function `t ↦ c t · t ^ (-β - 1)` is integrable
on `(z,∞)` for every `z > 0`.  Route: it is a.e. the product of the two `L²` functions
`u t = √(c t ²) · t ^ (-β/2)` and `v t = t ^ (-β/2 - 1)` (whose squares are `c t ² · t ^ (-β)`,
dominated on `(z,∞)` by `z ^ (-β) · c t ^ 2`, and `t ^ (-β - 2)`, with `∫_z^∞ t ^ (-β-2) =
z ^ (-β-1)/(β+1)`); conclude with `MemLp.mul` (Hölder with `p = q = 2`) and
`memLp_one_iff_integrable`.  Note `c` itself is only a.e. strongly measurable, so use
`√(c t ²) = |c t|`. -/
theorem integrableOn_Ioi_mul_rpow_neg {c : ℝ → ℝ} {β z : ℝ}
    (hc : MeasureTheory.IntegrableOn (fun t => c t ^ 2) (Set.Ioi 0))
    (hcm : MeasureTheory.AEStronglyMeasurable c (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hβ : 0 ≤ β) (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun t => c t * t ^ (-β - 1)) (Set.Ioi z) := by
  have hsub : Set.Ioi z ⊆ Set.Ioi 0 := Set.Ioi_subset_Ioi hz.le
  -- Integrability of the two summands of the majorant on `(z,∞)`.
  have hcz : Integrable (fun t : ℝ => c t ^ 2) (volume.restrict (Set.Ioi z)) :=
    hc.mono_set hsub
  have hA : Integrable (fun t : ℝ => (1 / 2) * (z ^ (-β) * c t ^ 2))
      (volume.restrict (Set.Ioi z)) :=
    (hcz.const_mul (z ^ (-β))).const_mul (1 / 2)
  have hB : Integrable (fun t : ℝ => (1 / 2) * t ^ (-β - 2))
      (volume.restrict (Set.Ioi z)) :=
    ((integrableOn_Ioi_rpow_of_lt (show -β - 2 < -1 by linarith) hz :
      Integrable (fun t : ℝ => t ^ (-β - 2)) (volume.restrict (Set.Ioi z)))).const_mul (1 / 2)
  have hG : Integrable (fun t : ℝ => (1 / 2) * (z ^ (-β) * c t ^ 2) + (1 / 2) * t ^ (-β - 2))
      (volume.restrict (Set.Ioi z)) := hA.add hB
  -- A.e. strong measurability of the integrand: `c` is a.e. strongly measurable on `(0,∞)` and
  -- `t ↦ t ^ (-β-1)` is continuous on `(z,∞)`.
  have hmeas : AEStronglyMeasurable (fun t : ℝ => c t * t ^ (-β - 1))
      (volume.restrict (Set.Ioi z)) :=
    (hcm.mono_set hsub).mul ((continuousOn_id.rpow_const (fun t ht =>
      Or.inl (ne_of_gt (lt_trans hz ht)))).aestronglyMeasurable measurableSet_Ioi)
  refine Integrable.mono' hG hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := lt_trans hz ht
  have hpow1 : 0 ≤ t ^ (-β - 1) := Real.rpow_nonneg ht0.le _
  -- The pointwise bound `|c t| · t^(-β-1) ≤ ½ (c t ² · t^(-β)) + ½ t^(-β-2)`, the AM–GM
  -- (or Young, i.e. Cauchy–Schwarz) inequality applied to `|c t| t^(-β/2)` and `t^(-β/2-1)`,
  -- together with `t ^ (-β) ≤ z ^ (-β)` (which holds since `β ≥ 0` and `t ≥ z`).
  have hle_z : c t ^ 2 * t ^ (-β) ≤ z ^ (-β) * c t ^ 2 := by
    have hzpow : t ^ (-β) ≤ z ^ (-β) :=
      Real.rpow_le_rpow_of_nonpos hz (le_of_lt ht) (by linarith : -β ≤ 0)
    calc c t ^ 2 * t ^ (-β) ≤ c t ^ 2 * z ^ (-β) :=
          mul_le_mul_of_nonneg_left hzpow (sq_nonneg _)
      _ = z ^ (-β) * c t ^ 2 := by ring
  calc ‖c t * t ^ (-β - 1)‖ = |c t| * t ^ (-β - 1) := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hpow1]
    _ = (|c t| * t ^ (-β / 2)) * (t ^ (-β / 2 - 1)) := by
        rw [mul_assoc, rpow_half_mul_half_sub_one ht0]
    _ ≤ (1 / 2) * ((|c t| * t ^ (-β / 2)) ^ 2 + (t ^ (-β / 2 - 1)) ^ 2) := by
        have h := two_mul_le_add_sq (|c t| * t ^ (-β / 2)) (t ^ (-β / 2 - 1))
        linarith
    _ = (1 / 2) * (c t ^ 2 * t ^ (-β) + t ^ (-β - 2)) := by
        have ha2 : (|c t| * t ^ (-β / 2)) ^ 2 = c t ^ 2 * t ^ (-β) := by
          rw [mul_pow, sq_abs]
          congr 1
          rw [sq, rpow_half_mul_half ht0]
        have hb2 : (t ^ (-β / 2 - 1)) ^ 2 = t ^ (-β - 2) := by
          rw [sq, rpow_sub_half_mul_sub_half ht0]
        rw [ha2, hb2]
    _ ≤ (1 / 2) * (z ^ (-β) * c t ^ 2 + t ^ (-β - 2)) :=
        mul_le_mul_of_nonneg_left (add_le_add hle_z le_rfl) (by norm_num)
    _ = (1 / 2) * (z ^ (-β) * c t ^ 2) + (1 / 2) * t ^ (-β - 2) := by ring

end Work.FTS.H2.ModalSolR
