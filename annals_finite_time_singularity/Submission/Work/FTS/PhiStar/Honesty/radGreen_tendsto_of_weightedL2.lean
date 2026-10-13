import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllExist.RadGreenDefs
import Submission.Work.FTS.PhiStar.Honesty.WeightedL2Aux.cs
import Submission.Work.FTS.PhiStar.Honesty.WeightedL2Aux.rgA_sq_le
import Submission.Work.FTS.PhiStar.Honesty.WeightedL2Aux.rgB_sq_le
import Submission.Work.FTS.PhiStar.Honesty.rgF1_integrableOn_Ioc
import Submission.Work.FTS.PhiStar.Honesty.rgB_int_Ioi

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `radGreen_tendsto_of_weightedL2`

For fixed `z > 0` the radial Green function `radGreen α m c z` is *continuous in the source*
`c` with respect to the two weighted `L²` norms

  `c ↦ ∫_{(0,1)} c²/t⁴`,      `c ↦ ∫_{(1,∞)} c²`.

The value bound rests on two Cauchy–Schwarz estimates (proved in the sibling modules
`WeightedL2Aux.rgA_sq_le`, `WeightedL2Aux.rgB_sq_le`):

  `(rgA α m d z)² ≤ ((Ad) + (Bd))·z^{2q+3}/(2q+3)`,
  `(rgB α m d z)² ≤ ((Ad) + (Bd))·z^{-2p-1}/(2p+1)`,

with `q = rgQ α m ≥ 28`, `p = rgP α m ≥ 8` and
`Ad = ∫_{(0,1)} d²/t⁴`, `Bd = ∫_{(1,∞)} d²`.  Together with the *junk-robust* linearity
`|∫_s f - ∫_s g| ≤ |∫_s (f-g)|` (`WeightedL2Aux.integral_sub_abs_le`) this gives

  `|radGreen α m c' z - radGreen α m c z| ≤ C(z)·(√Ad + √Bd)`,   `d = c' - c`,

whence the convergence: the two positive quantities `√(Ad n)`, `√(Bd n)` tend to `0` by
hypothesis (the integrabilities `hint1`, `hint2` are what make the Bochner integrals honest),
so the values converge.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false

open Work.FTS.EllExist
open Work.FTS.PhiStar.Honesty.WeightedL2Aux

/-! ## Elementary helpers -/

/-- `AEMeasurable d` gives a.e. strong measurability of `|d|` on `(0,∞)`. -/
private lemma aesm_abs_of_aemeasurable {d : ℝ → ℝ} (hd : AEMeasurable d) :
    AEStronglyMeasurable (fun t : ℝ => |d t|) (volume.restrict (Set.Ioi 0)) := by
  exact (hd.abs.aestronglyMeasurable).restrict

/-- **Integrability of the tail integrand `rgF2`** on `(z,∞)` for every `z > 0`, from the two
weighted `L²` bounds and a.e. measurability of the source. -/
private lemma integrableOn_rgF2_of {α : ℝ} {m : ℕ} {d : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hd : AEMeasurable d)
    (hnear : IntegrableOn (fun t : ℝ => (d t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : IntegrableOn (fun t : ℝ => (d t) ^ 2) (Set.Ioi 1)) :
    ∀ z : ℝ, 0 < z → IntegrableOn (rgF2 α m d) (Set.Ioi z) := by
  intro z hz
  have hp1 : (1 : ℝ) ≤ rgP α m := by have h := rgP_ge hα hα4 hm; linarith
  have hnorm : IntegrableOn (fun t : ℝ => ‖d t * t ^ (-(rgP α m) - 1)‖) (Set.Ioi z) :=
    rgB_int_Ioi hp1 hz (aesm_abs_of_aemeasurable hd) hnear hfar
  have haesm : AEStronglyMeasurable (fun t : ℝ => d t * t ^ (-(rgP α m) - 1))
      (volume.restrict (Set.Ioi z)) := by
    have h1 : AEStronglyMeasurable d (volume.restrict (Set.Ioi z)) :=
      hd.aestronglyMeasurable.restrict
    have h2 : AEStronglyMeasurable (fun t : ℝ => t ^ (-(rgP α m) - 1))
        (volume.restrict (Set.Ioi z)) :=
      ((continuousOn_id.rpow_const
        (fun t ht => Or.inl (ne_of_gt (lt_trans hz ht)))).aestronglyMeasurable
          measurableSet_Ioi)
    exact h1.mul h2
  have hmain : IntegrableOn (fun t : ℝ => d t * t ^ (-(rgP α m) - 1)) (Set.Ioi z) :=
    MeasureTheory.Integrable.mono' hnorm haesm (Filter.Eventually.of_forall (fun t => le_rfl))
  show IntegrableOn (fun t : ℝ => d t * t ^ (-(rgP α m) - 1)) (Set.Ioi z)
  exact hmain

/-- **Pointwise value bound for the difference of two radial Green functions.**  For
`d = c' - c`,

  `|radGreen α m c' z - radGreen α m c z| ≤ |rgK α m|·(z^{-q}·|rgA α m d z| + z^p·|rgB α m d z|)`.

The content is the junk-robust linearity `|∫_s f - ∫_s g| ≤ |∫_s (f - g)|`: since
`rgF1 α m d = rgF1 α m c' - rgF1 α m c` (and likewise for `rgF2`), and the left-hand integrand
is genuinely integrable on the relevant set, either both of `rgF1 α m c'`, `rgF1 α m c` are
integrable (and the difference is the integral of `rgF1 α m d`) or neither is (and both
integrals vanish). -/
private lemma radGreen_diff_bound {α : ℝ} {m : ℕ} {c c' : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hc : AEMeasurable c) (hc' : AEMeasurable c')
    (hnear : IntegrableOn (fun t : ℝ => (c' t - c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : IntegrableOn (fun t : ℝ => (c' t - c t) ^ 2) (Set.Ioi 1))
    {z : ℝ} (hz : 0 < z) :
    |Work.FTS.PhiStar.Radial.radGreen α m c' z - Work.FTS.PhiStar.Radial.radGreen α m c z|
      ≤ |rgK α m| * (z ^ (-(rgQ α m)) * |rgA α m (fun t => c' t - c t) z|
          + z ^ (rgP α m) * |rgB α m (fun t => c' t - c t) z|) := by
  set d : ℝ → ℝ := fun t => c' t - c t with hd
  have hdae : AEMeasurable d := hc'.sub hc
  have hF1 : IntegrableOn (rgF1 α m d) (Set.Ioc 0 z) :=
    rgF1_integrableOn_Ioc hα hα4 hm hdae hnear hfar z hz
  have hF2 : IntegrableOn (rgF2 α m d) (Set.Ioi z) :=
    integrableOn_rgF2_of hα hα4 hm hdae hnear hfar z hz
  -- the two integrands are the differences of the corresponding integrands of `c'` and `c`
  have hsub1 : IntegrableOn (fun t => rgF1 α m c' t - rgF1 α m c t) (Set.Ioc 0 z) :=
    MeasureTheory.Integrable.congr hF1 (Filter.Eventually.of_forall (fun t => by
      show rgF1 α m d t = rgF1 α m c' t - rgF1 α m c t
      simp only [rgF1, hd]
      ring))
  have hsub2 : IntegrableOn (fun t => rgF2 α m c' t - rgF2 α m c t) (Set.Ioi z) :=
    MeasureTheory.Integrable.congr hF2 (Filter.Eventually.of_forall (fun t => by
      show rgF2 α m d t = rgF2 α m c' t - rgF2 α m c t
      simp only [rgF2, hd]
      ring))
  have hA : |rgA α m c' z - rgA α m c z| ≤ |rgA α m d z| := by
    have e1 : rgA α m c' z = ∫ t in Set.Ioc 0 z, rgF1 α m c' t := by
      rw [rgA, intervalIntegral.integral_of_le hz.le]
    have e2 : rgA α m c z = ∫ t in Set.Ioc 0 z, rgF1 α m c t := by
      rw [rgA, intervalIntegral.integral_of_le hz.le]
    have e3 : rgA α m d z = ∫ t in Set.Ioc 0 z, (rgF1 α m c' t - rgF1 α m c t) := by
      rw [rgA, intervalIntegral.integral_of_le hz.le]
      exact setIntegral_congr_fun measurableSet_Ioc (fun t _ => by
        show rgF1 α m d t = rgF1 α m c' t - rgF1 α m c t
        simp only [rgF1, hd]
        ring)
    rw [e1, e2, e3]
    exact integral_sub_abs_le hsub1
  have hB : |rgB α m c' z - rgB α m c z| ≤ |rgB α m d z| := by
    have e1 : rgB α m c' z = ∫ t in Set.Ioi z, rgF2 α m c' t := rfl
    have e2 : rgB α m c z = ∫ t in Set.Ioi z, rgF2 α m c t := rfl
    have e3 : rgB α m d z = ∫ t in Set.Ioi z, (rgF2 α m c' t - rgF2 α m c t) := by
      rw [rgB]
      exact setIntegral_congr_fun measurableSet_Ioi (fun t _ => by
        show rgF2 α m d t = rgF2 α m c' t - rgF2 α m c t
        simp only [rgF2, hd]
        ring)
    rw [e1, e2, e3]
    exact integral_sub_abs_le hsub2
  -- expand both Green values and combine
  rw [radGreen_eq, radGreen_eq]
  have hsplit : rgK α m * (z ^ (-(rgQ α m)) * rgA α m c' z + z ^ (rgP α m) * rgB α m c' z)
        - rgK α m * (z ^ (-(rgQ α m)) * rgA α m c z + z ^ (rgP α m) * rgB α m c z)
      = rgK α m * (z ^ (-(rgQ α m)) * (rgA α m c' z - rgA α m c z)
          + z ^ (rgP α m) * (rgB α m c' z - rgB α m c z)) := by
    ring
  rw [hsplit, abs_mul]
  calc |rgK α m| * |z ^ (-(rgQ α m)) * (rgA α m c' z - rgA α m c z)
          + z ^ (rgP α m) * (rgB α m c' z - rgB α m c z)|
      ≤ |rgK α m| * (|z ^ (-(rgQ α m)) * (rgA α m c' z - rgA α m c z)|
          + |z ^ (rgP α m) * (rgB α m c' z - rgB α m c z)|) :=
        mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg _)
    _ = |rgK α m| * (z ^ (-(rgQ α m)) * |rgA α m c' z - rgA α m c z|
          + z ^ (rgP α m) * |rgB α m c' z - rgB α m c z|) := by
        rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hz.le _),
          abs_of_nonneg (Real.rpow_nonneg hz.le _)]
    _ ≤ |rgK α m| * (z ^ (-(rgQ α m)) * |rgA α m d z| + z ^ (rgP α m) * |rgB α m d z|) :=
        mul_le_mul_of_nonneg_left (add_le_add
          (mul_le_mul_of_nonneg_left hA (Real.rpow_nonneg hz.le _))
          (mul_le_mul_of_nonneg_left hB (Real.rpow_nonneg hz.le _))) (abs_nonneg _)

/-! ## The main theorem -/

theorem radGreen_tendsto_of_weightedL2 {α : ℝ} {m : ℕ} {c : ℝ → ℝ} {c_ : ℕ → ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m)
    (hc : AEMeasurable c) (hc_ : ∀ n, AEMeasurable (c_ n))
    (hint1 : ∀ n, MeasureTheory.IntegrableOn (fun t : ℝ => (c_ n t - c t) ^ 2 / t ^ 4)
      (Set.Ioo 0 1))
    (hint2 : ∀ n, MeasureTheory.IntegrableOn (fun t : ℝ => (c_ n t - c t) ^ 2) (Set.Ioi 1))
    (hconv1 : Filter.Tendsto (fun n => ∫ t in Set.Ioo (0:ℝ) 1, (c_ n t - c t) ^ 2 / t ^ 4)
      Filter.atTop (nhds 0))
    (hconv2 : Filter.Tendsto (fun n => ∫ t in Set.Ioi (1:ℝ), (c_ n t - c t) ^ 2)
      Filter.atTop (nhds 0)) :
    ∀ z : ℝ, 0 < z → Filter.Tendsto (fun n => Work.FTS.PhiStar.Radial.radGreen α m (c_ n) z)
      Filter.atTop (nhds (Work.FTS.PhiStar.Radial.radGreen α m c z)) := by
  intro z hz
  set d : ℕ → ℝ → ℝ := fun n t => c_ n t - c t with hd
  have hdae : ∀ n, AEMeasurable (d n) := fun n => (hc_ n).sub hc
  set Ad : ℕ → ℝ := fun n => ∫ t in Set.Ioo (0:ℝ) 1, (d n t) ^ 2 / t ^ 4 with hAd
  set Bd : ℕ → ℝ := fun n => ∫ t in Set.Ioi (1:ℝ), (d n t) ^ 2 with hBd
  have hAdnn : ∀ n, 0 ≤ Ad n := fun n =>
    setIntegral_nonneg measurableSet_Ioo (fun t _ => div_nonneg (sq_nonneg _) (by positivity))
  have hBdnn : ∀ n, 0 ≤ Bd n := fun n =>
    setIntegral_nonneg measurableSet_Ioi (fun t _ => sq_nonneg _)
  have hAdc : Filter.Tendsto Ad Filter.atTop (nhds 0) := by
    simpa only [hAd, hd] using hconv1
  have hBdc : Filter.Tendsto Bd Filter.atTop (nhds 0) := by
    simpa only [hBd, hd] using hconv2
  -- the sequence of `√` of the two masses tends to zero
  have hSc : Filter.Tendsto (fun n => Real.sqrt (Ad n) + Real.sqrt (Bd n))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun n => Real.sqrt (Ad n)) Filter.atTop (nhds 0) := by
      have h := hAdc.sqrt
      rwa [Real.sqrt_zero] at h
    have h2 : Filter.Tendsto (fun n => Real.sqrt (Bd n)) Filter.atTop (nhds 0) := by
      have h := hBdc.sqrt
      rwa [Real.sqrt_zero] at h
    simpa using h1.add h2
  -- the constant of the value bound
  have hCnn : 0 ≤ z ^ ((3:ℝ)/2) / Real.sqrt (2 * rgQ α m + 3)
      + z ^ (-(1:ℝ)/2) / Real.sqrt (2 * rgP α m + 1) := by
    have h1 : 0 ≤ z ^ ((3:ℝ)/2) / Real.sqrt (2 * rgQ α m + 3) := by positivity
    have h2 : 0 ≤ z ^ (-(1:ℝ)/2) / Real.sqrt (2 * rgP α m + 1) := by positivity
    linarith
  -- the pointwise bound
  have hbd : ∀ n, |Work.FTS.PhiStar.Radial.radGreen α m (c_ n) z
        - Work.FTS.PhiStar.Radial.radGreen α m c z|
      ≤ (|rgK α m| * (z ^ ((3:ℝ)/2) / Real.sqrt (2 * rgQ α m + 3)
            + z ^ (-(1:ℝ)/2) / Real.sqrt (2 * rgP α m + 1)))
        * (Real.sqrt (Ad n) + Real.sqrt (Bd n)) := by
    intro n
    have hd1 : IntegrableOn (fun t : ℝ => (d n t) ^ 2 / t ^ 4) (Set.Ioo 0 1) := by
      simpa only [hd] using hint1 n
    have hd2 : IntegrableOn (fun t : ℝ => (d n t) ^ 2) (Set.Ioi 1) := by
      simpa only [hd] using hint2 n
    have hdiff := radGreen_diff_bound (c := c) (c' := c_ n) hα hα4 hm hc (hc_ n)
      (by simpa only [hd] using hint1 n) (by simpa only [hd] using hint2 n) hz
    have hnear2 := rgA_sq_le hα hα4 hm (hdae n) hd1 hd2 hz
    have hfar2 := rgB_sq_le hα hα4 hm (hdae n) hd1 hd2 hz
    have hGnn : 0 ≤ Ad n + Bd n := add_nonneg (hAdnn n) (hBdnn n)
    -- the near half
    have hA' : z ^ (-(rgQ α m)) * |rgA α m (d n) z|
        ≤ Real.sqrt (Ad n + Bd n) * (z ^ ((3:ℝ)/2) / Real.sqrt (2 * rgQ α m + 3)) := by
      have hsq : Real.sqrt ((rgA α m (d n) z) ^ 2)
          ≤ Real.sqrt ((Ad n + Bd n) * (z ^ (2 * rgQ α m + 3) / (2 * rgQ α m + 3))) :=
        Real.sqrt_le_sqrt hnear2
      rw [Real.sqrt_sq_eq_abs] at hsq
      have hstep := mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg hz.le (-(rgQ α m)))
      have hpow : z ^ (-(rgQ α m)) * z ^ (rgQ α m + 3 / 2) = z ^ ((3:ℝ)/2) := by
        rw [← Real.rpow_add hz]
        congr 1
        ring
      have hsqz : Real.sqrt (z ^ (2 * rgQ α m + 3)) = z ^ (rgQ α m + 3 / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hz.le]
        congr 1
        ring
      have hval : z ^ (-(rgQ α m))
            * Real.sqrt ((Ad n + Bd n) * (z ^ (2 * rgQ α m + 3) / (2 * rgQ α m + 3)))
          = Real.sqrt (Ad n + Bd n) * (z ^ ((3:ℝ)/2) / Real.sqrt (2 * rgQ α m + 3)) := by
        rw [Real.sqrt_mul hGnn, Real.sqrt_div (Real.rpow_nonneg hz.le _), hsqz, ← hpow]
        ring
      rwa [hval] at hstep
    -- the far half
    have hB' : z ^ (rgP α m) * |rgB α m (d n) z|
        ≤ Real.sqrt (Ad n + Bd n) * (z ^ (-(1:ℝ)/2) / Real.sqrt (2 * rgP α m + 1)) := by
      have hsq : Real.sqrt ((rgB α m (d n) z) ^ 2)
          ≤ Real.sqrt ((Ad n + Bd n) * (z ^ (-(2 * rgP α m) - 1) / (2 * rgP α m + 1))) :=
        Real.sqrt_le_sqrt hfar2
      rw [Real.sqrt_sq_eq_abs] at hsq
      have hstep := mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg hz.le (rgP α m))
      have hpow : z ^ (rgP α m) * z ^ (-(rgP α m) - 1 / 2) = z ^ (-(1:ℝ)/2) := by
        rw [← Real.rpow_add hz]
        congr 1
        ring
      have hsqz : Real.sqrt (z ^ (-(2 * rgP α m) - 1)) = z ^ (-(rgP α m) - 1 / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hz.le]
        congr 1
        ring
      have hval : z ^ (rgP α m)
            * Real.sqrt ((Ad n + Bd n) * (z ^ (-(2 * rgP α m) - 1) / (2 * rgP α m + 1)))
          = Real.sqrt (Ad n + Bd n) * (z ^ (-(1:ℝ)/2) / Real.sqrt (2 * rgP α m + 1)) := by
        rw [Real.sqrt_mul hGnn, Real.sqrt_div (Real.rpow_nonneg hz.le _), hsqz, ← hpow]
        ring
      rwa [hval] at hstep
    -- combine
    have hmid : z ^ (-(rgQ α m)) * |rgA α m (d n) z| + z ^ (rgP α m) * |rgB α m (d n) z|
        ≤ Real.sqrt (Ad n + Bd n) * (z ^ ((3:ℝ)/2) / Real.sqrt (2 * rgQ α m + 3)
            + z ^ (-(1:ℝ)/2) / Real.sqrt (2 * rgP α m + 1)) := by
      refine le_trans (add_le_add hA' hB') (le_of_eq ?_)
      ring
    have hsqrt := sqrt_add_le (hAdnn n) (hBdnn n)
    calc |Work.FTS.PhiStar.Radial.radGreen α m (c_ n) z
          - Work.FTS.PhiStar.Radial.radGreen α m c z|
        ≤ |rgK α m| * (z ^ (-(rgQ α m)) * |rgA α m (d n) z|
            + z ^ (rgP α m) * |rgB α m (d n) z|) := hdiff
      _ ≤ |rgK α m| * (Real.sqrt (Ad n + Bd n) * (z ^ ((3:ℝ)/2) / Real.sqrt (2 * rgQ α m + 3)
            + z ^ (-(1:ℝ)/2) / Real.sqrt (2 * rgP α m + 1))) :=
          mul_le_mul_of_nonneg_left hmid (abs_nonneg _)
      _ ≤ |rgK α m| * ((Real.sqrt (Ad n) + Real.sqrt (Bd n))
            * (z ^ ((3:ℝ)/2) / Real.sqrt (2 * rgQ α m + 3)
              + z ^ (-(1:ℝ)/2) / Real.sqrt (2 * rgP α m + 1))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsqrt hCnn) (abs_nonneg _)
      _ = (|rgK α m| * (z ^ ((3:ℝ)/2) / Real.sqrt (2 * rgQ α m + 3)
            + z ^ (-(1:ℝ)/2) / Real.sqrt (2 * rgP α m + 1)))
          * (Real.sqrt (Ad n) + Real.sqrt (Bd n)) := by
          ring
  -- squeeze
  have hlimC : Filter.Tendsto (fun n => (|rgK α m| * (z ^ ((3:ℝ)/2) / Real.sqrt (2 * rgQ α m + 3)
      + z ^ (-(1:ℝ)/2) / Real.sqrt (2 * rgP α m + 1))) * (Real.sqrt (Ad n) + Real.sqrt (Bd n)))
      Filter.atTop (nhds 0) := by
    simpa using hSc.const_mul _
  have habs : Filter.Tendsto (fun n => |Work.FTS.PhiStar.Radial.radGreen α m (c_ n) z
      - Work.FTS.PhiStar.Radial.radGreen α m c z|) Filter.atTop (nhds 0) :=
    squeeze_zero (fun n => abs_nonneg _) (fun n => hbd n) hlimC
  have hsub : Filter.Tendsto (fun n => Work.FTS.PhiStar.Radial.radGreen α m (c_ n) z
      - Work.FTS.PhiStar.Radial.radGreen α m c z) Filter.atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using habs)
  have h3 := hsub.add_const (Work.FTS.PhiStar.Radial.radGreen α m c z)
  have heq : (fun n => (Work.FTS.PhiStar.Radial.radGreen α m (c_ n) z
      - Work.FTS.PhiStar.Radial.radGreen α m c z) + Work.FTS.PhiStar.Radial.radGreen α m c z)
      = fun n => Work.FTS.PhiStar.Radial.radGreen α m (c_ n) z := by
    funext n
    ring
  rw [heq] at h3
  simpa using h3

end Work.FTS.PhiStar.Honesty
