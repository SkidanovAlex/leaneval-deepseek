/-
# `Work.EllipticEst.ModalSolution.radGreen_abs_le`

The modal Green function `radGreen α m c` of `Work.FTS.PhiStar.Radial.Defs` is the
decaying-at-`∞` solution of the mode-`m` radial Euler equation
`-α²z²a'' - α(5+α)z a' + λ_m a = c` (`λ_m = 2m(2m+5)`), in explicit Green's-function form

  `radGreen α m c z = 1/(α(4m+5)) · [ z ^ (-(2m+5)/α) ∫_0^z c t · t ^ ((2m+5)/α - 1) dt
                                       + z ^ (2m/α)   ∫_z^∞ c t · t ^ (-(2m/α) - 1) dt ]`.

The estimate proved here is the `L²`-to-weighted-`L^∞` bound

  `|radGreen α m c z| ≤ √(∫_0^∞ c²) · z ^ (-1/2) / (α(4m+5)√m)`   (`0 < α ≤ 1`, `m ≥ 1`, `z > 0`).

Its content is Cauchy–Schwarz on the two Green integrals.  Write `p = 2m/α`, `q = (2m+5)/α`.
For the near-origin integral, Cauchy–Schwarz against `t ^ (q-1)` on `(0,z)` together with
`∫_0^z t ^ (2q-2) = z ^ (2q-1)/(2q-1)` gives

  `z ^ (-q)|∫_0^z c t ^ (q-1)| ≤ √(∫_{Ioi 0} c²) · z ^ (-1/2)/√(2q-1)`,

and for the tail integral, Cauchy–Schwarz on `Ioi z` together with
`∫_z^∞ t ^ (-2p-2) = z ^ (-2p-1)/(2p+1)` gives

  `z ^ p |∫_z^∞ c t ^ (-p-1)| ≤ √(∫_{Ioi 0} c²) · z ^ (-1/2)/√(2p+1)`.

Since `α ≤ 1` we have `2p+1 ≥ 4m+1` and `2q-1 ≥ 4m+9 ≥ 4m+1`, so

  `1/√(2q-1) + 1/√(2p+1) ≤ 2/√(4m+1) ≤ 1/√m`,

which produces exactly the stated constant `α(4m+5)√m`.

The measurability of `c` is never needed: `∫_0^z c t ^ (q-1)` is first bounded by
`∫_0^z |c| t ^ (q-1) = ∫_0^z √(c²) t ^ (q-1)`, and the integrability of `c²` supplies both the
measurability of `√(c²)` and the finiteness of the `L²` mass — so no case distinction on
integrability of `c · t ^ (q-1)` is required.
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.FTS.EllipticEst.remov.Ebs.abs_integral_mul_le_sqrt
import Submission.Work.EllipticEst.ModalSolution.radGreen_tail_bound
import Submission.Work.EllipticEst.ModalSolution.inv_sqrt_add_inv_sqrt_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

open MeasureTheory Set

namespace Work.EllipticEst.ModalSolution

/-- **Head piece.**  For `r ≥ 1`, `z > 0` and `c` with `∫_0^∞ c² < ∞`, the near-origin Green
integral is bounded by the `L²` mass of `c`: Cauchy–Schwarz for `√(c ²)` against `t ^ (r-1)` on
`(0,z)`, using `∫_0^z t ^ (2r-2) = z ^ (2r-1)/(2r-1)`. -/
theorem radGreen_head_bound (c : ℝ → ℝ)
    (hc : MeasureTheory.IntegrableOn (fun t => c t ^ 2) (Set.Ioi 0))
    {r z : ℝ} (hr : 1 ≤ r) (hz : 0 < z) :
    |∫ t in (0 : ℝ)..z, c t * t ^ (r - 1)| ≤
      Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (r - 1 / 2) / Real.sqrt (2 * r - 1) := by
  have hz0 : 0 ≤ z := le_of_lt hz
  have hsub : Set.Ioc (0 : ℝ) z ⊆ Set.Ioi 0 := Set.Ioc_subset_Ioi_self
  -- ## step 1: `|∫ c · w| ≤ ∫ |c| · w` on `(0,z)`, with `w = t ^ (r-1) > 0`
  have hJ : |∫ t in Set.Ioc (0 : ℝ) z, c t * t ^ (r - 1)| ≤
      ∫ t in Set.Ioc (0 : ℝ) z, Real.sqrt (c t ^ 2) * t ^ (r - 1) := by
    have h1 : |∫ t in Set.Ioc (0 : ℝ) z, c t * t ^ (r - 1)| ≤
        ∫ t in Set.Ioc (0 : ℝ) z, ‖c t * t ^ (r - 1)‖ := by
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (μ := volume.restrict (Set.Ioc (0 : ℝ) z))
          (f := fun t => c t * t ^ (r - 1)))
    refine le_trans h1 (le_of_eq ?_)
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs, abs_mul, Real.sqrt_sq_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos ht.1 (r - 1))]
  -- ## step 2: Cauchy–Schwarz with `u t = √(c t ²)` and `v t = t ^ (r-1)`
  have hu_m : AEStronglyMeasurable (fun t => Real.sqrt (c t ^ 2))
      (volume.restrict (Set.Ioc (0 : ℝ) z)) :=
    (Real.continuous_sqrt.comp_aestronglyMeasurable hc.1).mono_set hsub
  have hu_int : Integrable (fun t => (Real.sqrt (c t ^ 2)) ^ 2)
      (volume.restrict (Set.Ioc (0 : ℝ) z)) := by
    refine (hc.mono_set hsub).congr (Filter.Eventually.of_forall (fun t => ?_))
    exact (Real.sq_sqrt (sq_nonneg (c t))).symm
  have hu : MemLp (fun t => Real.sqrt (c t ^ 2)) 2 (volume.restrict (Set.Ioc (0 : ℝ) z)) :=
    (memLp_two_iff_integrable_sq hu_m).mpr hu_int
  have hcont_v : ContinuousOn (fun t : ℝ => t ^ (r - 1)) (Set.Ioc (0 : ℝ) z) :=
    continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt ht.1))
  have hv_m : AEStronglyMeasurable (fun t : ℝ => t ^ (r - 1))
      (volume.restrict (Set.Ioc (0 : ℝ) z)) :=
    hcont_v.aestronglyMeasurable measurableSet_Ioc
  have hptv : ∀ t : ℝ, 0 < t → t ^ (2 * r - 2) = (t ^ (r - 1)) ^ 2 := by
    intro t ht
    rw [pow_two, ← Real.rpow_add ht]
    congr 1
    ring
  have hv_int : Integrable (fun t => (t ^ (r - 1)) ^ 2)
      (volume.restrict (Set.Ioc (0 : ℝ) z)) := by
    have hbase : IntegrableOn (fun t : ℝ => t ^ (2 * r - 2)) (Set.Ioc (0 : ℝ) z) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hz0).mp
        (intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1 : ℝ) < 2 * r - 2)
          (a := (0 : ℝ)) (b := z))
    refine hbase.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hptv t ht.1
  have hv : MemLp (fun t : ℝ => t ^ (r - 1)) 2 (volume.restrict (Set.Ioc (0 : ℝ) z)) :=
    (memLp_two_iff_integrable_sq hv_m).mpr hv_int
  have hCS := Work.FTS.EllipticEst.remov.Ebs.abs_integral_mul_le_sqrt
    (u := fun t => Real.sqrt (c t ^ 2)) (v := fun t : ℝ => t ^ (r - 1)) hu hv
  -- ## step 3: the values of the two `L²` integrals
  have hIntU : (∫ t in Set.Ioc (0 : ℝ) z, (Real.sqrt (c t ^ 2)) ^ 2) =
      ∫ t in Set.Ioc (0 : ℝ) z, c t ^ 2 :=
    integral_congr_ae (Filter.Eventually.of_forall (fun t => Real.sq_sqrt (sq_nonneg (c t))))
  have hVval : (∫ t in Set.Ioc (0 : ℝ) z, t ^ (2 * r - 2)) = z ^ (2 * r - 1) / (2 * r - 1) := by
    rw [← intervalIntegral.integral_of_le hz0]
    rw [integral_rpow (Or.inl (by linarith : (-1 : ℝ) < 2 * r - 2))]
    rw [show (2 * r - 2 + 1 : ℝ) = 2 * r - 1 by ring]
    rw [Real.zero_rpow (by linarith : (2 * r - 1 : ℝ) ≠ 0), sub_zero]
  have hIntV : (∫ t in Set.Ioc (0 : ℝ) z, (t ^ (r - 1)) ^ 2) = z ^ (2 * r - 1) / (2 * r - 1) := by
    have hcong : (∫ t in Set.Ioc (0 : ℝ) z, (t ^ (r - 1)) ^ 2) =
        ∫ t in Set.Ioc (0 : ℝ) z, t ^ (2 * r - 2) :=
      integral_congr_ae (by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact (hptv t ht.1).symm)
    rw [hcong, hVval]
  have hCSp : (∫ t in Set.Ioc (0 : ℝ) z, Real.sqrt (c t ^ 2) * t ^ (r - 1)) ≤
      Real.sqrt (∫ t in Set.Ioc (0 : ℝ) z, c t ^ 2) *
        Real.sqrt (z ^ (2 * r - 1) / (2 * r - 1)) := by
    refine le_trans (le_abs_self _) (le_trans hCS ?_)
    rw [hIntU, hIntV]
  have hW : Real.sqrt (z ^ (2 * r - 1) / (2 * r - 1)) =
      z ^ (r - 1 / 2) / Real.sqrt (2 * r - 1) := by
    have hzW : 0 ≤ z ^ (2 * r - 1) := le_of_lt (Real.rpow_pos_of_pos hz _)
    rw [Real.sqrt_div hzW (2 * r - 1)]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hz0]
    rw [show (2 * r - 1) * (1 / 2) = r - 1 / 2 by ring]
  have hUQ : (∫ t in Set.Ioc (0 : ℝ) z, c t ^ 2) ≤ ∫ t in Set.Ioi 0, c t ^ 2 := by
    refine setIntegral_mono_set (μ := volume) (s := Set.Ioc (0 : ℝ) z) (t := Set.Ioi 0) hc ?_ ?_
    · exact Filter.Eventually.of_forall (fun t => sq_nonneg (c t))
    · exact Filter.Eventually.of_forall (fun t ht => ht.1)
  have hsqrtUQ : Real.sqrt (∫ t in Set.Ioc (0 : ℝ) z, c t ^ 2) ≤
      Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) := Real.sqrt_le_sqrt hUQ
  calc |∫ t in (0 : ℝ)..z, c t * t ^ (r - 1)|
      = |∫ t in Set.Ioc (0 : ℝ) z, c t * t ^ (r - 1)| := by
        rw [intervalIntegral.integral_of_le hz0]
    _ ≤ ∫ t in Set.Ioc (0 : ℝ) z, Real.sqrt (c t ^ 2) * t ^ (r - 1) := hJ
    _ ≤ Real.sqrt (∫ t in Set.Ioc (0 : ℝ) z, c t ^ 2) *
          Real.sqrt (z ^ (2 * r - 1) / (2 * r - 1)) := hCSp
    _ = Real.sqrt (∫ t in Set.Ioc (0 : ℝ) z, c t ^ 2) *
          (z ^ (r - 1 / 2) / Real.sqrt (2 * r - 1)) := by rw [hW]
    _ ≤ Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * (z ^ (r - 1 / 2) / Real.sqrt (2 * r - 1)) :=
        mul_le_mul_of_nonneg_right hsqrtUQ
          (div_nonneg (le_of_lt (Real.rpow_pos_of_pos hz _)) (Real.sqrt_nonneg _))
    _ = Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (r - 1 / 2) / Real.sqrt (2 * r - 1) := by
        rw [mul_div_assoc]

theorem radGreen_abs_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (m : ℕ) (hm : 1 ≤ m) {c : ℝ → ℝ}
    (hc : MeasureTheory.IntegrableOn (fun t => c t ^ 2) (Set.Ioi 0)) {z : ℝ} (hz : 0 < z) :
    |Work.FTS.PhiStar.Radial.radGreen α m c z| ≤
      Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (-(1 / 2) : ℝ)
        / (α * (4 * (m : ℝ) + 5) * Real.sqrt m) := by
  -- notation: `M = m`, `p = 2m/α`, `q = (2m+5)/α`
  set M : ℝ := (m : ℝ) with hMdef
  set p : ℝ := 2 * M / α with hpdef
  set q : ℝ := (2 * M + 5) / α with hqdef
  have hM1 : 1 ≤ M := by rw [hMdef]; exact_mod_cast hm
  have hM0 : 0 ≤ M := by linarith
  have hKpos : 0 < α * (4 * M + 5) := mul_pos hα (by linarith)
  have honeK : 0 ≤ 1 / (α * (4 * M + 5)) := le_of_lt (one_div_pos.mpr hKpos)
  have hp0 : 0 < p := by
    rw [hpdef]
    exact div_pos (by linarith : (0 : ℝ) < 2 * M) hα
  have hq1 : 1 ≤ q := by
    have h7 : (7 : ℝ) ≤ q := by
      rw [hqdef, le_div_iff₀ hα]
      nlinarith
    linarith
  have hdef : Work.FTS.PhiStar.Radial.radGreen α m c z = 1 / (α * (4 * M + 5)) *
      (z ^ (-q) * (∫ t in (0 : ℝ)..z, c t * t ^ (q - 1))
        + z ^ p * (∫ t in Set.Ioi z, c t * t ^ (-p - 1))) := by
    simp only [Work.FTS.PhiStar.Radial.radGreen]
    rw [neg_div, ← hMdef, ← hpdef, ← hqdef]
  -- ## the two Green pieces
  have hhead : |∫ t in (0 : ℝ)..z, c t * t ^ (q - 1)| ≤
      Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (q - 1 / 2) / Real.sqrt (2 * q - 1) :=
    radGreen_head_bound c hc (r := q) hq1 hz
  have htail : |z ^ p * (∫ t in Set.Ioi z, c t * t ^ (-p - 1))| ≤
      Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (-(1 / 2) : ℝ) / Real.sqrt (2 * p + 1) :=
    radGreen_tail_bound c hc (p := p) hp0 hz
  have hzq : 0 < z ^ (-q) := Real.rpow_pos_of_pos hz _
  have hzA : z ^ (-q) * z ^ (q - 1 / 2) = z ^ (-(1 / 2) : ℝ) := by
    rw [← Real.rpow_add hz]
    congr 1
    ring
  have hhead' : |z ^ (-q) * (∫ t in (0 : ℝ)..z, c t * t ^ (q - 1))| ≤
      Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (-(1 / 2) : ℝ) / Real.sqrt (2 * q - 1) := by
    have key : z ^ (-q) * (Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (q - 1 / 2)
          / Real.sqrt (2 * q - 1))
        = Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (-(1 / 2) : ℝ)
          / Real.sqrt (2 * q - 1) := by
      rw [← hzA]
      ring
    rw [abs_mul, abs_of_pos hzq]
    exact le_trans (mul_le_mul_of_nonneg_left hhead (le_of_lt hzq)) (le_of_eq key)
  -- ## the numeric side conditions
  have hq_eq : 2 * q - 1 = (2 * (2 * M + 5) - α) / α := by
    rw [hqdef]
    field_simp
  have h1 : 4 * M + 1 ≤ 2 * q - 1 := by
    rw [hq_eq, le_div_iff₀ hα]
    nlinarith
  have hp_eq : 2 * p + 1 = (4 * M + α) / α := by
    rw [hpdef]
    field_simp
    ring
  have h2 : 4 * M + 1 ≤ 2 * p + 1 := by
    rw [hp_eq, le_div_iff₀ hα]
    nlinarith
  have hnum := inv_sqrt_add_inv_sqrt_le hM1 h1 h2
  have hS : 0 ≤ Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) := Real.sqrt_nonneg _
  have hpre : 0 ≤ Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (-(1 / 2) : ℝ)
      / (α * (4 * M + 5)) :=
    div_nonneg (mul_nonneg hS (le_of_lt (Real.rpow_pos_of_pos hz _))) (le_of_lt hKpos)
  -- ## assembly
  calc |Work.FTS.PhiStar.Radial.radGreen α m c z|
      = 1 / (α * (4 * M + 5)) *
          |z ^ (-q) * (∫ t in (0 : ℝ)..z, c t * t ^ (q - 1))
            + z ^ p * (∫ t in Set.Ioi z, c t * t ^ (-p - 1))| := by
        rw [hdef, abs_mul, abs_of_pos (one_div_pos.mpr hKpos)]
    _ ≤ 1 / (α * (4 * M + 5)) *
          (|z ^ (-q) * (∫ t in (0 : ℝ)..z, c t * t ^ (q - 1))|
            + |z ^ p * (∫ t in Set.Ioi z, c t * t ^ (-p - 1))|) :=
        mul_le_mul_of_nonneg_left (abs_add_le _ _) honeK
    _ ≤ 1 / (α * (4 * M + 5)) *
          (Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (-(1 / 2) : ℝ)
              / Real.sqrt (2 * q - 1)
            + Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (-(1 / 2) : ℝ)
              / Real.sqrt (2 * p + 1)) :=
        mul_le_mul_of_nonneg_left (add_le_add hhead' htail) honeK
    _ = Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (-(1 / 2) : ℝ) / (α * (4 * M + 5))
          * (1 / Real.sqrt (2 * q - 1) + 1 / Real.sqrt (2 * p + 1)) := by ring
    _ ≤ Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (-(1 / 2) : ℝ) / (α * (4 * M + 5))
          * (1 / Real.sqrt M) :=
        mul_le_mul_of_nonneg_left hnum hpre
    _ = Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (-(1 / 2) : ℝ)
          / (α * (4 * (m : ℝ) + 5) * Real.sqrt m) := by
        rw [← hMdef, div_mul_div_comm, mul_one]

end Work.EllipticEst.ModalSolution
