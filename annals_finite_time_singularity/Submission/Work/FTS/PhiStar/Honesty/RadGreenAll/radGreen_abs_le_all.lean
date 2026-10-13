/-
# `Work.FTS.PhiStar.Honesty.RadGreenAll.radGreen_abs_le_all`

The modal Green function of `Work.FTS.PhiStar.Radial.Defs` is

  `radGreen α m c z = rgK α m · ( z ^ (-(rgQ α m)) · rgA α m c z
                                   + z ^ (rgP α m) · rgB α m c z )`

with `rgK = 1/(α(4m+5))`, `rgQ = (2m+5)/α`, `rgP = 2m/α` and the two primitives
`rgA α m c z = ∫_0^z c t · t ^ (rgQ - 1) dt`,  `rgB α m c z = ∫_{Ioi z} c t · t ^ (-(rgP) - 1) dt`.

Here we prove the **`m`-uniform** `L²`-to-weighted-`L^∞` bound

  `|radGreen α m c z| ≤ 2 · rgK α m · √(∫_{Ioi 0} c²) · z ^ (-1/2)`   (`0 < α ≤ 1`, all `m : ℕ`,
  `z > 0`),

whose point is that it holds **also for `m = 0`** (where `rgP α 0 = 0` and the tail exponent
`-(rgP) - 1 = -1` is the borderline one).  The workspace already has, for `m ≥ 1`, the sharper
`Work.EllipticEst.ModalSolution.radGreen_abs_le` (constant `1/(α(4m+5)√m)`) and the two pieces

* `radGreen_head_shaped` : `|z ^ (-r) ∫_0^z c t^(r-1)| ≤ √(∫c²) z^(-1/2)/√(2r-1)` for `r ≥ 1`,
* `radGreen_tail_bound` : `|z ^ p ∫_{Ioi z} c t^(-p-1)| ≤ √(∫c²) z^(-1/2)/√(2p+1)` for `p > 0`.

The second one is stated with `p > 0`, so it does **not** apply at `m = 0`; the gap is closed
here by the sharper hypothesis `0 ≤ p` (`radGreen_tail_bound_nonneg`), whose proof is the same
Cauchy–Schwarz computation with the weight `t ^ (-p-1)`: the only places where `p > 0` was used
are the integrability/summability of `t ^ (-2p-2)` on `Ioi z` (needing `p > -1/2`) and the
positivity of `z ^ p`, both of which hold under `0 ≤ p`.

Both pieces come with the factor `1/√(2·exp - 1)` resp. `1/√(2·exp + 1)`, and both exponents
satisfy `2·exp ∓ 1 ≥ 1` (because `rgQ ≥ 5 ≥ 1` and `rgP ≥ 0`), so each piece is at most
`√(∫c²) · z ^ (-1/2)`; adding the two and pulling out `rgK` gives exactly the factor `2`.
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.L2Space
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.FTS.EllExist.RadGreenDefs
import Submission.Work.EllipticEst.ModalSolution.radGreen_abs_le
import Submission.Work.EllipticEst.ModalSolution.radGreen_tail_bound
import Submission.Work.FTS.PhiStar.Honesty.radGreen_head_shaped

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

open MeasureTheory Set

namespace Work.FTS.PhiStar.Honesty.RadGreenAll

/-- **Tail piece, valid for `0 ≤ p`.**

For `p ≥ 0`, `z > 0` and `c` with `∫_0^∞ c² < ∞`,

  `|z ^ p · ∫_{Ioi z} c t · t ^ (-p-1)| ≤ √(∫_{Ioi 0} c²) · z ^ (-1/2) / √(2p+1)`.

This is `Work.EllipticEst.ModalSolution.radGreen_tail_bound` with the hypothesis `0 < p` relaxed
to `0 ≤ p` (the case `p = 0`, i.e. `m = 0`, is exactly what `radGreen_abs_le_all` needs).  The
proof is unchanged: Cauchy–Schwarz for `√(c²)` against `t ^ (-p-1)` on `Ioi z`, using
`∫_z^∞ t ^ (-2p-2) = z ^ (-2p-1)/(2p+1)`. -/
theorem radGreen_tail_bound_nonneg (c : ℝ → ℝ)
    (hc : MeasureTheory.IntegrableOn (fun t => c t ^ 2) (Set.Ioi 0))
    {p z : ℝ} (hp : 0 ≤ p) (hz : 0 < z) :
    |z ^ p * (∫ t in Set.Ioi z, c t * t ^ (-p - 1))| ≤
      Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (-(1 / 2) : ℝ) / Real.sqrt (2 * p + 1) := by
  have hz0 : 0 ≤ z := le_of_lt hz
  have h2p1 : 0 < 2 * p + 1 := by linarith
  have hsub : Set.Ioi z ⊆ Set.Ioi (0 : ℝ) := Set.Ioi_subset_Ioi hz0
  -- ## the factor `u t = |c t| = √(c t ^ 2)`
  have hu_ae : AEStronglyMeasurable (fun t => Real.sqrt (c t ^ 2)) (volume.restrict (Set.Ioi 0)) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hc.1
  have hu_m : AEStronglyMeasurable (fun t => Real.sqrt (c t ^ 2)) (volume.restrict (Set.Ioi z)) :=
    hu_ae.mono_set hsub
  have hu_int : Integrable (fun t => (Real.sqrt (c t ^ 2)) ^ 2) (volume.restrict (Set.Ioi z)) := by
    refine (hc.mono_set hsub).congr (Filter.Eventually.of_forall (fun t => ?_))
    exact (Real.sq_sqrt (sq_nonneg (c t))).symm
  have hu : MemLp (fun t => Real.sqrt (c t ^ 2)) 2 (volume.restrict (Set.Ioi z)) :=
    (memLp_two_iff_integrable_sq hu_m).mpr hu_int
  -- ## the weight `v t = t ^ (-p-1)`
  have hcont_v : ContinuousOn (fun t : ℝ => t ^ (-p - 1)) (Set.Ioi z) :=
    continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt (lt_trans hz ht)))
  have hv_m : AEStronglyMeasurable (fun t : ℝ => t ^ (-p - 1)) (volume.restrict (Set.Ioi z)) :=
    hcont_v.aestronglyMeasurable measurableSet_Ioi
  have hptv : ∀ t : ℝ, 0 < t → t ^ (-2 * p - 2) = (t ^ (-p - 1)) ^ 2 := by
    intro t ht
    rw [pow_two, ← Real.rpow_add ht]
    congr 1
    ring
  have hv_int : Integrable (fun t => (t ^ (-p - 1)) ^ 2) (volume.restrict (Set.Ioi z)) := by
    refine (integrableOn_Ioi_rpow_of_lt (a := -2 * p - 2) (by linarith) hz).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hptv t (lt_trans hz ht)
  have hv : MemLp (fun t => t ^ (-p - 1)) 2 (volume.restrict (Set.Ioi z)) :=
    (memLp_two_iff_integrable_sq hv_m).mpr hv_int
  -- ## the value of `∫_z^∞ t ^ (-2p-2)`
  have hVval : (∫ t in Set.Ioi z, t ^ (-2 * p - 2)) = z ^ (-2 * p - 1) / (2 * p + 1) := by
    have h := integral_Ioi_rpow_of_lt (a := -2 * p - 2) (c := z) (by linarith) hz
    have h' : -z ^ ((-2 * p - 2 : ℝ) + 1) / ((-2 * p - 2 : ℝ) + 1)
        = z ^ (-2 * p - 1) / (2 * p + 1) := by
      rw [show ((-2 * p - 2 : ℝ) + 1) = -(2 * p + 1) by ring]
      rw [neg_div_neg_eq]
      rw [show -(2 * p + 1 : ℝ) = -2 * p - 1 by ring]
    rw [h, h']
  have hIntV : (∫ t in Set.Ioi z, (t ^ (-p - 1)) ^ 2) = z ^ (-2 * p - 1) / (2 * p + 1) := by
    rw [show (∫ t in Set.Ioi z, (t ^ (-p - 1)) ^ 2) = ∫ t in Set.Ioi z, t ^ (-2 * p - 2) from
      integral_congr_ae (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact (hptv t (lt_trans hz ht)).symm)]
    exact hVval
  have hIntU : (∫ t in Set.Ioi z, (Real.sqrt (c t ^ 2)) ^ 2) = ∫ t in Set.Ioi z, c t ^ 2 :=
    integral_congr_ae (Filter.Eventually.of_forall (fun t => Real.sq_sqrt (sq_nonneg (c t))))
  -- ## Cauchy–Schwarz
  have hCS := Work.FTS.EllipticEst.remov.Ebs.abs_integral_mul_le_sqrt hu hv
  have hCS' : (∫ t in Set.Ioi z, Real.sqrt (c t ^ 2) * t ^ (-p - 1)) ≤
      Real.sqrt (∫ t in Set.Ioi z, c t ^ 2) * Real.sqrt (z ^ (-2 * p - 1) / (2 * p + 1)) := by
    refine le_trans (le_abs_self _) (le_trans hCS ?_)
    rw [hIntU, hIntV]
  -- ## the tail integral itself, bounded by the `L²` pairing
  have hJ : |∫ t in Set.Ioi z, c t * t ^ (-p - 1)| ≤
      ∫ t in Set.Ioi z, Real.sqrt (c t ^ 2) * t ^ (-p - 1) := by
    have h1 : |∫ t in Set.Ioi z, c t * t ^ (-p - 1)| ≤
        ∫ t in Set.Ioi z, ‖c t * t ^ (-p - 1)‖ := by
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (μ := volume.restrict (Set.Ioi z))
          (f := fun t => c t * t ^ (-p - 1)))
    refine le_trans h1 (le_of_eq ?_)
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans hz ht
    rw [Real.norm_eq_abs, abs_mul, Real.sqrt_sq_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos ht0 (-p - 1))]
  have hmain : |∫ t in Set.Ioi z, c t * t ^ (-p - 1)| ≤
      Real.sqrt (∫ t in Set.Ioi z, c t ^ 2) * Real.sqrt (z ^ (-2 * p - 1) / (2 * p + 1)) :=
    le_trans hJ hCS'
  -- ## monotonicity of the `L²` mass in the domain
  have hUQ : (∫ t in Set.Ioi z, c t ^ 2) ≤ ∫ t in Set.Ioi 0, c t ^ 2 := by
    refine setIntegral_mono_set (μ := volume) (s := Set.Ioi z) (t := Set.Ioi 0) hc ?_ ?_
    · exact Filter.Eventually.of_forall (fun t => sq_nonneg (c t))
    · exact Filter.Eventually.of_forall (fun t ht => lt_trans hz ht)
  have hsqrtUQ : Real.sqrt (∫ t in Set.Ioi z, c t ^ 2) ≤ Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) :=
    Real.sqrt_le_sqrt hUQ
  -- ## the weight computation
  have hW : z ^ p * Real.sqrt (z ^ (-2 * p - 1) / (2 * p + 1)) =
      z ^ (-(1 / 2) : ℝ) / Real.sqrt (2 * p + 1) := by
    have hzW : 0 ≤ z ^ (-2 * p - 1) := le_of_lt (Real.rpow_pos_of_pos hz _)
    have hsq : Real.sqrt (z ^ (-2 * p - 1)) = z ^ (-p - (1 / 2)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hz0]
      rw [show (-2 * p - 1) * (1 / 2) = -p - (1 / 2) by ring]
    rw [Real.sqrt_div hzW (2 * p + 1), hsq]
    rw [← mul_div_assoc, ← Real.rpow_add hz]
    rw [show p + (-p - (1 / 2)) = -(1 / 2 : ℝ) by ring]
  have hzp : 0 < z ^ p := Real.rpow_pos_of_pos hz p
  calc |z ^ p * (∫ t in Set.Ioi z, c t * t ^ (-p - 1))|
      = z ^ p * |∫ t in Set.Ioi z, c t * t ^ (-p - 1)| := by
        rw [abs_mul, abs_of_pos hzp]
    _ ≤ z ^ p * (Real.sqrt (∫ t in Set.Ioi z, c t ^ 2) *
          Real.sqrt (z ^ (-2 * p - 1) / (2 * p + 1))) :=
        mul_le_mul_of_nonneg_left hmain (le_of_lt hzp)
    _ = Real.sqrt (∫ t in Set.Ioi z, c t ^ 2) *
          (z ^ p * Real.sqrt (z ^ (-2 * p - 1) / (2 * p + 1))) := by ring
    _ = Real.sqrt (∫ t in Set.Ioi z, c t ^ 2) *
          (z ^ (-(1 / 2) : ℝ) / Real.sqrt (2 * p + 1)) := by rw [hW]
    _ ≤ Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) *
          (z ^ (-(1 / 2) : ℝ) / Real.sqrt (2 * p + 1)) :=
        mul_le_mul_of_nonneg_right hsqrtUQ
          (div_nonneg (le_of_lt (Real.rpow_pos_of_pos hz _)) (Real.sqrt_nonneg _))
    _ = Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (-(1 / 2) : ℝ) / Real.sqrt (2 * p + 1) := by
        rw [mul_div_assoc]

/-- **Tail piece without the denominator.**  Since `2p + 1 ≥ 1` for `p ≥ 0`, the previous bound
gives the cleaner estimate `|z ^ p ∫_{Ioi z} c t ^ (-p-1)| ≤ √(∫ c²) · z ^ (-1/2)`. -/
theorem radGreen_tail_le_nonneg (c : ℝ → ℝ)
    (hc : MeasureTheory.IntegrableOn (fun t => c t ^ 2) (Set.Ioi 0))
    {p z : ℝ} (hp : 0 ≤ p) (hz : 0 < z) :
    |z ^ p * (∫ t in Set.Ioi z, c t * t ^ (-p - 1))| ≤
      Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (-(1 / 2) : ℝ) := by
  have h := radGreen_tail_bound_nonneg c hc hp hz
  have h1 : 1 ≤ Real.sqrt (2 * p + 1) := by
    have hs : Real.sqrt (1 : ℝ) ≤ Real.sqrt (2 * p + 1) :=
      Real.sqrt_le_sqrt (by linarith)
    rwa [Real.sqrt_one] at hs
  have hpos : 0 < Real.sqrt (2 * p + 1) := lt_of_lt_of_le zero_lt_one h1
  have hA : 0 ≤ Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (-(1 / 2) : ℝ) :=
    mul_nonneg (Real.sqrt_nonneg _) (le_of_lt (Real.rpow_pos_of_pos hz _))
  calc |z ^ p * (∫ t in Set.Ioi z, c t * t ^ (-p - 1))|
      ≤ Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (-(1 / 2) : ℝ) / Real.sqrt (2 * p + 1) := h
    _ ≤ Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (-(1 / 2) : ℝ) := by
        rw [div_le_iff₀ hpos]
        exact le_mul_of_one_le_right hA h1

/-- **The `m`-uniform Green bound.**  For `0 < α ≤ 1`, every `m : ℕ`, `z > 0` and `c` with
`∫_{Ioi 0} c² < ∞`,

  `|radGreen α m c z| ≤ 2 · rgK α m · √(∫_{Ioi 0} c²) · z ^ (-1/2)`.

Both Green pieces are bounded by `√(∫ c²) · z ^ (-1/2)` — the head via `radGreen_head_shaped`
(with `r = rgQ α m ≥ 1`, using `α ≤ 1`) together with `√(2·rgQ α m - 1) ≥ 1`, the tail via
`radGreen_tail_le_nonneg` (with `rgP α m ≥ 0`) together with `√(2·rgP α m + 1) ≥ 1` — and the
factor `rgK α m` is pulled out of the absolute value.  No case distinction on `m` is needed:
`m = 0` corresponds to `rgP α 0 = 0`, which is exactly the borderline case covered by the
relaxed tail bound. -/
theorem radGreen_abs_le_all {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (m : ℕ) {c : ℝ → ℝ}
    (hc : MeasureTheory.IntegrableOn (fun t => c t ^ 2) (Set.Ioi 0)) {z : ℝ} (hz : 0 < z) :
    |Work.FTS.PhiStar.Radial.radGreen α m c z| ≤
      2 * Work.FTS.EllExist.rgK α m * Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (-(1 / 2) : ℝ) := by
  have hK : 0 ≤ Work.FTS.EllExist.rgK α m := le_of_lt (Work.FTS.EllExist.rgK_pos hα m)
  have hS : 0 ≤ Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) := Real.sqrt_nonneg _
  have hzp : 0 ≤ z ^ (-(1 / 2) : ℝ) := le_of_lt (Real.rpow_pos_of_pos hz _)
  have hA : 0 ≤ Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (-(1 / 2) : ℝ) := mul_nonneg hS hzp
  -- ## the head piece
  have hq1 : 1 ≤ Work.FTS.EllExist.rgQ α m := by
    rw [Work.FTS.EllExist.rgQ, le_div_iff₀ hα]
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    nlinarith
  have hhead : |z ^ (-(Work.FTS.EllExist.rgQ α m)) * Work.FTS.EllExist.rgA α m c z| ≤
      Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (-(1 / 2) : ℝ) := by
    have h := Work.FTS.PhiStar.Honesty.radGreen_head_shaped c hc
      (r := Work.FTS.EllExist.rgQ α m) hq1 hz
    have hrg : Work.FTS.EllExist.rgA α m c z
        = ∫ t in (0 : ℝ)..z, c t * t ^ (Work.FTS.EllExist.rgQ α m - 1) := by
      simp [Work.FTS.EllExist.rgA, Work.FTS.EllExist.rgF1]
    rw [hrg]
    have h1 : 1 ≤ Real.sqrt (2 * Work.FTS.EllExist.rgQ α m - 1) := by
      have hs : Real.sqrt (1 : ℝ) ≤ Real.sqrt (2 * Work.FTS.EllExist.rgQ α m - 1) :=
        Real.sqrt_le_sqrt (by linarith)
      rwa [Real.sqrt_one] at hs
    have hpos : 0 < Real.sqrt (2 * Work.FTS.EllExist.rgQ α m - 1) := lt_of_lt_of_le zero_lt_one h1
    refine le_trans h ?_
    rw [div_le_iff₀ hpos]
    exact le_mul_of_one_le_right hA h1
  -- ## the tail piece
  have htail : |z ^ (Work.FTS.EllExist.rgP α m) * Work.FTS.EllExist.rgB α m c z| ≤
      Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (-(1 / 2) : ℝ) := by
    have h := radGreen_tail_le_nonneg c hc (p := Work.FTS.EllExist.rgP α m)
      (Work.FTS.EllExist.rgP_nonneg hα m) hz
    have hrg : Work.FTS.EllExist.rgB α m c z
        = ∫ t in Set.Ioi z, c t * t ^ (-(Work.FTS.EllExist.rgP α m) - 1) := by
      simp [Work.FTS.EllExist.rgB, Work.FTS.EllExist.rgF2]
    rwa [hrg]
  -- ## assembly
  calc |Work.FTS.PhiStar.Radial.radGreen α m c z|
      = Work.FTS.EllExist.rgK α m *
          |z ^ (-(Work.FTS.EllExist.rgQ α m)) * Work.FTS.EllExist.rgA α m c z
            + z ^ (Work.FTS.EllExist.rgP α m) * Work.FTS.EllExist.rgB α m c z| := by
        rw [Work.FTS.EllExist.radGreen_eq, abs_mul, abs_of_nonneg hK]
    _ ≤ Work.FTS.EllExist.rgK α m *
          (|z ^ (-(Work.FTS.EllExist.rgQ α m)) * Work.FTS.EllExist.rgA α m c z|
            + |z ^ (Work.FTS.EllExist.rgP α m) * Work.FTS.EllExist.rgB α m c z|) :=
        mul_le_mul_of_nonneg_left (abs_add_le _ _) hK
    _ ≤ Work.FTS.EllExist.rgK α m *
          (Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (-(1 / 2) : ℝ)
            + Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (-(1 / 2) : ℝ)) :=
        mul_le_mul_of_nonneg_left (add_le_add hhead htail) hK
    _ = 2 * Work.FTS.EllExist.rgK α m * Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2)
          * z ^ (-(1 / 2) : ℝ) := by
        ring

end Work.FTS.PhiStar.Honesty.RadGreenAll
