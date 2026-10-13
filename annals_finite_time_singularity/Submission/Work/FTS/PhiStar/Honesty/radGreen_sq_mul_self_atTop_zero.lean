/-
# `radGreen α m c z = O(z^{-1/2}·(∫_z^∞ c²)^{1/2})`, hence `z·(radGreen z)² → 0`

`radGreen α m c = K·(G1 + G2)` with

* `G1 z = z^{-q}·∫_0^z c t t^{q-1} dt`,  `q = radQ α m = (2m+5)/α ≥ 28`,
* `G2 z = z^{p}·∫_{Ioi z} c t t^{-p-1} dt`,  `p = radP α m = 2m/α ≥ 8`,
* `K = radK α m = 1/(α(4m+5))`.

Under the two `L²`-type hypotheses on `c` (`c²/t⁴ ∈ L¹(0,1)`, `c² ∈ L¹(1,∞)`) we show
`z·(radGreen α m c z)² → 0` at `∞`.

The estimate (every quantity below is *junk-robust*: Mathlib gives the Bochner integral of a
non-integrable function the value `0`, which is why the `¬Integrable` branches of the helper lemmas
cause no trouble):

* `(∫_0^1 c t t^{q-1})² ≤ M0`, `M0 = ∫_0^1 c²/t⁴` (Cauchy–Schwarz, `t^{2q+2} ≤ 1`);
* `(∫_1^w c t t^{q-1})² ≤ P·w^{2q-1}`, `P = ∫_{Ioi 1} c²`;
* `(∫_w^z c t t^{q-1})² ≤ T(w)·z^{2q-1}`, `T(w) = ∫_{Ioi w} c²`;
* `(∫_{Ioi z} c t t^{-p-1})² ≤ T(z)·z^{-2p-1}/(2p+1)`.

Splitting `∫_0^z = ∫_0^1 + ∫_1^{√z} + ∫_{√z}^z` (the *tail* information is used only on the last
piece — the crude bound alone would leave a non-vanishing constant) gives

  `z·(G1 z)² ≤ 3·(M0·z^{1-2q} + P·z^{1/2-q} + T(√z))`,  `z·(G2 z)² ≤ T(z)/(2p+1)`,

and each of the four terms tends to `0` (the last two because `T(w) → 0` as `w → ∞`, i.e.
`MeasureTheory.tendsto_integral_Ioi_zero`).  Squeezing `z·(radGreen z)² ≥ 0` between these bounds
finishes.  The four Cauchy–Schwarz pieces are delegated to
`FTS/PhiStar/Honesty/CSTools/`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllExist.Honesty.RadGreenDefs
import Submission.Work.FTS.PhiStar.RadialWAux.Defs
import Submission.Work.FTS.PhiStar.Honesty.sq_integral_le_mul_integral_sq
import Submission.Work.FTS.PhiStar.Honesty.CSTools.sq_interval_le_tail
import Submission.Work.FTS.PhiStar.Honesty.CSTools.sq_tail_le
import Submission.Work.FTS.PhiStar.Honesty.CSTools.abs_intervalIntegral_le_abs_add

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

/-! ### elementary real-power and square estimates -/

/-- `(z^a)² = z^{2a}` for `z > 0`. -/
private lemma rpow_sq {z : ℝ} (hz : 0 < z) (a : ℝ) : (z ^ a) ^ 2 = z ^ (2 * a) := by
  rw [sq, ← Real.rpow_add hz]
  congr 1
  ring

/-- `z · z^a = z^{1+a}` for `z > 0`. -/
private lemma rpow_one_mul {z : ℝ} (hz : 0 < z) (a : ℝ) : z * z ^ a = z ^ (1 + a) := by
  nth_rewrite 1 [← Real.rpow_one z]
  rw [← Real.rpow_add hz]

/-- `z^a · z^b = z^c` when `a + b = c` and `z > 0`. -/
private lemma rpow_mul_expo {z : ℝ} (hz : 0 < z) {a b c : ℝ} (h : a + b = c) :
    z ^ a * z ^ b = z ^ c := by
  rw [← Real.rpow_add hz, h]

/-- `(√z)^a = z^{a/2}` for `z ≥ 0`. -/
private lemma sqrt_rpow {z : ℝ} (hz : 0 ≤ z) (a : ℝ) : (Real.sqrt z) ^ a = z ^ (a / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hz]
  congr 1
  ring

/-- `z · z^{-2q} = z^{1-2q}` for `z > 0`. -/
private lemma mul_rpow_neg_two {z : ℝ} (hz : 0 < z) (q : ℝ) :
    z * z ^ (-(2 * q)) = z ^ (1 - 2 * q) :=
  rpow_one_mul hz _

/-- `z · z^{2p} = z^{1+2p}` for `z > 0`. -/
private lemma mul_rpow_two {z : ℝ} (hz : 0 < z) (p : ℝ) :
    z * z ^ (2 * p) = z ^ (1 + 2 * p) :=
  rpow_one_mul hz _

/-- `(z^{-a})² = z^{-2a}` for `z > 0`. -/
private lemma rpow_sq_neg {z : ℝ} (hz : 0 < z) (a : ℝ) : (z ^ (-a)) ^ 2 = z ^ (-(2 * a)) := by
  rw [rpow_sq hz]
  congr 1
  ring

/-- `1 ≤ √z` for `z ≥ 1`. -/
private lemma sqrt_one_le {z : ℝ} (hz1 : 1 ≤ z) : 1 ≤ Real.sqrt z := by
  rw [← Real.sqrt_one]
  exact Real.sqrt_le_sqrt hz1

/-- `√z ≤ z` for `z ≥ 1`. -/
private lemma sqrt_le_self {z : ℝ} (hz1 : 1 ≤ z) : Real.sqrt z ≤ z := by
  have hz0 : (0 : ℝ) < z := lt_of_lt_of_le one_pos hz1
  have hsq : (Real.sqrt z) ^ 2 = z := Real.sq_sqrt hz0.le
  have h1 : 1 ≤ Real.sqrt z := sqrt_one_le hz1
  nlinarith [hsq, h1, sq_nonneg (Real.sqrt z - 1)]

/-- `(a+b+c)² ≤ 3(a²+b²+c²)`. -/
private lemma sq_add_three_le (a b c : ℝ) : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]

/-- `(a+b)² ≤ 2(a²+b²)`. -/
private lemma sq_add_two_le (a b : ℝ) : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  nlinarith [sq_nonneg (a - b)]

/-- Pointwise left-end estimate: `(c t · t^r)² ≤ (c t)²/t⁴` for `0 < t ≤ 1` and `r ≥ -2`
(the weight `t^{2r+4} ≤ 1` is the whole content). -/
private lemma rg_pointwise_bound (c : ℝ → ℝ) {r t : ℝ} (hr : -2 ≤ r) (ht0 : 0 < t)
    (ht1 : t ≤ 1) : (c t * t ^ r) ^ 2 ≤ (c t) ^ 2 / t ^ 4 := by
  have hrp : t ^ r ≤ (t ^ 2)⁻¹ := by
    calc t ^ r ≤ t ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_ge ht0 ht1 (by linarith)
      _ = (t ^ (2 : ℝ))⁻¹ := Real.rpow_neg ht0.le 2
      _ = (t ^ 2)⁻¹ := by rw [Real.rpow_two]
  calc (c t * t ^ r) ^ 2 = (c t) ^ 2 * (t ^ r) ^ 2 := by rw [mul_pow]
    _ ≤ (c t) ^ 2 * ((t ^ 2)⁻¹) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.rpow_nonneg ht0.le r) hrp 2)
          (sq_nonneg _)
    _ = (c t) ^ 2 / t ^ 4 := by
        rw [div_eq_mul_inv, inv_pow, show (t ^ 2) ^ 2 = t ^ 4 by ring]

/-- **Cauchy–Schwarz at the left end**: `(∫_0^1 c t t^r)² ≤ ∫_0^1 c²/t⁴` for `r ≥ -2`,
junk-robust (the Bochner integral of a non-integrable function is `0`). -/
private lemma sq_near_zero_local {c : ℝ → ℝ} {r : ℝ} (hr : -2 ≤ r)
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1)) :
    (∫ t in (0 : ℝ)..1, c t * t ^ r) ^ 2 ≤ ∫ t in (0 : ℝ)..1, (c t) ^ 2 / t ^ 4 := by
  set F : ℝ → ℝ := fun t => c t * t ^ r with hF
  have hnI : Integrable (fun t : ℝ => (c t) ^ 2 / t ^ 4)
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := hnear.congr_set_ae (Ioo_ae_eq_Ioc).symm
  have hpt : ∀ t ∈ Set.Ioo (0 : ℝ) 1, (F t) ^ 2 ≤ (c t) ^ 2 / t ^ 4 := by
    intro t ht
    rw [hF]; simp only []
    exact rg_pointwise_bound c hr ht.1 ht.2.le
  have hptIoc : ∀ t ∈ Set.Ioc (0 : ℝ) 1, (F t) ^ 2 ≤ (c t) ^ 2 / t ^ 4 := by
    intro t ht
    rw [hF]; simp only []
    exact rg_pointwise_bound c hr ht.1 ht.2
  have hemptyF : IntegrableOn F (Set.Ioc (1 : ℝ) 0) volume := by
    rw [Set.Ioc_eq_empty_of_le (by norm_num : (0 : ℝ) ≤ 1)]; exact integrableOn_empty
  have hemptyF2 : IntegrableOn (fun t : ℝ => (F t) ^ 2) (Set.Ioc (1 : ℝ) 0) volume := by
    rw [Set.Ioc_eq_empty_of_le (by norm_num : (0 : ℝ) ≤ 1)]; exact integrableOn_empty
  have hemptyn : IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioc (1 : ℝ) 0) volume := by
    rw [Set.Ioc_eq_empty_of_le (by norm_num : (0 : ℝ) ≤ 1)]; exact integrableOn_empty
  by_cases hint : Integrable F (volume.restrict (Set.Ioc (0 : ℝ) 1))
  · have hF2I : Integrable (fun t : ℝ => (F t) ^ 2) (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
      refine Integrable.mono' hnI ?_ ?_
      · have hc2 : AEStronglyMeasurable (fun t : ℝ => (c t) ^ 2)
            (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
          have h2 : AEStronglyMeasurable (fun t : ℝ => t ^ 4)
              (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
            (continuous_id.pow 4).continuousOn.aestronglyMeasurable measurableSet_Ioc
          refine (hnI.aestronglyMeasurable.mul h2).congr ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
          have ht0 : 0 < t := ht.1
          have ht4 : (t : ℝ) ^ 4 ≠ 0 := pow_ne_zero 4 (ne_of_gt ht0)
          simp only [Pi.mul_apply]
          field_simp
        have htr : AEStronglyMeasurable (fun t : ℝ => (t ^ r) ^ 2)
            (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
          have hcont : ContinuousOn (fun t : ℝ => t ^ r) (Set.Ioc (0 : ℝ) 1) := fun t ht =>
            (Real.continuousAt_rpow_const t r (Or.inl (ne_of_gt ht.1))).continuousWithinAt
          exact (hcont.pow 2).aestronglyMeasurable measurableSet_Ioc
        refine (hc2.mul htr).congr ?_
        filter_upwards [] with t
        simp only [Pi.mul_apply, hF]
        ring
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (F t))]
        exact hptIoc t ht
    have hFint : IntervalIntegrable F volume (0 : ℝ) 1 := ⟨hint, hemptyF⟩
    have hF2int : IntervalIntegrable (fun t : ℝ => (F t) ^ 2) volume (0 : ℝ) 1 :=
      ⟨hF2I, hemptyF2⟩
    have hnIint : IntervalIntegrable (fun t : ℝ => (c t) ^ 2 / t ^ 4) volume (0 : ℝ) 1 :=
      ⟨hnI, hemptyn⟩
    have hCS : (∫ t in (0 : ℝ)..1, F t) ^ 2 ≤ ∫ t in (0 : ℝ)..1, (F t) ^ 2 := by
      have h := Work.FTS.PhiStar.Honesty.sq_integral_le_mul_integral_sq (f := F) (z := (1 : ℝ))
        zero_le_one hFint hF2int
      simpa using h
    have hmono : (∫ t in (0 : ℝ)..1, (F t) ^ 2) ≤ ∫ t in (0 : ℝ)..1, (c t) ^ 2 / t ^ 4 :=
      intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one hF2int hnIint hpt
    calc (∫ t in (0 : ℝ)..1, c t * t ^ r) ^ 2 = (∫ t in (0 : ℝ)..1, F t) ^ 2 := by rw [hF]
      _ ≤ ∫ t in (0 : ℝ)..1, (F t) ^ 2 := hCS
      _ ≤ ∫ t in (0 : ℝ)..1, (c t) ^ 2 / t ^ 4 := hmono
  · have h0 : (∫ t in (0 : ℝ)..1, F t) = 0 := by
      rw [intervalIntegral.integral_of_le zero_le_one]
      exact integral_undef hint
    rw [show (∫ t in (0 : ℝ)..1, c t * t ^ r) = (∫ t in (0 : ℝ)..1, F t) from by simp only [hF],
      h0, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    exact intervalIntegral.integral_nonneg zero_le_one
      (fun u _ => div_nonneg (sq_nonneg (c u)) (by positivity))

/-! ### the three constants of the estimate -/

/-- `M0 = ∫_0^1 c²/t⁴`. -/
private def rgM0 (c : ℝ → ℝ) : ℝ := ∫ t in (0 : ℝ)..1, (c t) ^ 2 / t ^ 4

/-- `P = ∫_{Ioi 1} c²`. -/
private def rgP (c : ℝ → ℝ) : ℝ := ∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2

/-- `T z = ∫_{Ioi z} c²`. -/
private def rgT (c : ℝ → ℝ) : ℝ → ℝ := fun z => ∫ t in Set.Ioi z, (c t) ^ 2

private lemma rgM0_apply (c : ℝ → ℝ) : rgM0 c = ∫ t in (0 : ℝ)..1, (c t) ^ 2 / t ^ 4 := rfl
private lemma rgP_apply (c : ℝ → ℝ) : rgP c = ∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2 := rfl
private lemma rgT_apply (c : ℝ → ℝ) (z : ℝ) : rgT c z = ∫ t in Set.Ioi z, (c t) ^ 2 := rfl

/-- The bound function which `z ↦ z·(radGreen z)²` is dominated by. -/
private def rgBound (α : ℝ) (m : ℕ) (c : ℝ → ℝ) : ℝ → ℝ := fun z =>
  2 * (Work.FTS.PhiStar.RadialWAux.radK α m) ^ 2 *
    (3 * (rgM0 c * z ^ (1 - 2 * Work.FTS.PhiStar.RadialWAux.radQ α m)
        + rgP c * z ^ (1 / 2 - Work.FTS.PhiStar.RadialWAux.radQ α m)
        + rgT c (Real.sqrt z))
      + rgT c z / (2 * Work.FTS.PhiStar.RadialWAux.radP α m + 1))

private lemma rgBound_apply (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (z : ℝ) :
    rgBound α m c z =
      2 * (Work.FTS.PhiStar.RadialWAux.radK α m) ^ 2 *
        (3 * (rgM0 c * z ^ (1 - 2 * Work.FTS.PhiStar.RadialWAux.radQ α m)
            + rgP c * z ^ (1 / 2 - Work.FTS.PhiStar.RadialWAux.radQ α m)
            + rgT c (Real.sqrt z))
          + rgT c z / (2 * Work.FTS.PhiStar.RadialWAux.radP α m + 1)) := rfl

/-- `T z = ∫_{Ioi z} c² → 0` as `z → ∞` (no integrability hypothesis needed: it is built into
Mathlib's `MeasureTheory.tendsto_integral_Ioi_zero`). -/
private lemma rgT_tendsto_zero (c : ℝ → ℝ) : Tendsto (rgT c) atTop (nhds 0) := by
  unfold rgT
  exact MeasureTheory.tendsto_integral_Ioi_zero (f := fun t : ℝ => (c t) ^ 2) (μ := volume)
    (l := atTop) (b := fun z : ℝ => z) tendsto_id

/-- The bound function tends to `0`. -/
private lemma rgBound_tendsto (α : ℝ) (m : ℕ) (c : ℝ → ℝ)
    (hq : 1 / 2 < Work.FTS.PhiStar.RadialWAux.radQ α m) :
    Tendsto (rgBound α m c) atTop (nhds 0) := by
  have hTtend : Tendsto (rgT c) atTop (nhds 0) := rgT_tendsto_zero c
  have h1 : Tendsto (fun z : ℝ => rgM0 c * z ^ (1 - 2 * Work.FTS.PhiStar.RadialWAux.radQ α m))
      atTop (nhds 0) := by
    have h := (tendsto_rpow_neg_atTop (y := 2 * Work.FTS.PhiStar.RadialWAux.radQ α m - 1)
      (by linarith)).const_mul (rgM0 c)
    simpa only [show -(2 * Work.FTS.PhiStar.RadialWAux.radQ α m - 1)
      = 1 - 2 * Work.FTS.PhiStar.RadialWAux.radQ α m by ring, mul_zero] using h
  have h2 : Tendsto (fun z : ℝ => rgP c * z ^ (1 / 2 - Work.FTS.PhiStar.RadialWAux.radQ α m))
      atTop (nhds 0) := by
    have h := (tendsto_rpow_neg_atTop (y := Work.FTS.PhiStar.RadialWAux.radQ α m - 1 / 2)
      (by linarith)).const_mul (rgP c)
    simpa only [show -(Work.FTS.PhiStar.RadialWAux.radQ α m - 1 / 2)
      = 1 / 2 - Work.FTS.PhiStar.RadialWAux.radQ α m by ring, mul_zero] using h
  have h3 : Tendsto (fun z : ℝ => rgT c (Real.sqrt z)) atTop (nhds 0) :=
    hTtend.comp Real.tendsto_sqrt_atTop
  have h4 : Tendsto (fun z : ℝ => rgT c z / (2 * Work.FTS.PhiStar.RadialWAux.radP α m + 1))
      atTop (nhds 0) := by
    have h := hTtend.div_const (2 * Work.FTS.PhiStar.RadialWAux.radP α m + 1)
    simpa using h
  have h5 : Tendsto (fun z : ℝ =>
      (rgM0 c * z ^ (1 - 2 * Work.FTS.PhiStar.RadialWAux.radQ α m)
        + rgP c * z ^ (1 / 2 - Work.FTS.PhiStar.RadialWAux.radQ α m)) + rgT c (Real.sqrt z))
      atTop (nhds 0) := by
    simpa using (h1.add h2).add h3
  have h6 : Tendsto (fun z : ℝ => 2 * (Work.FTS.PhiStar.RadialWAux.radK α m) ^ 2 *
        (3 * ((rgM0 c * z ^ (1 - 2 * Work.FTS.PhiStar.RadialWAux.radQ α m)
            + rgP c * z ^ (1 / 2 - Work.FTS.PhiStar.RadialWAux.radQ α m)) + rgT c (Real.sqrt z))
          + rgT c z / (2 * Work.FTS.PhiStar.RadialWAux.radP α m + 1))) atTop (nhds 0) := by
    have h := ((h5.const_mul 3).add h4).const_mul
      (2 * (Work.FTS.PhiStar.RadialWAux.radK α m) ^ 2)
    simpa using h
  convert h6 using 1
  ext z
  rw [rgBound_apply]

/-! ### the two halves of the pointwise bound -/

/-- The `G1` half: `z·G1(z)² ≤ 3(M0·z^{1-2q} + P·z^{1/2-q} + T(√z))`. -/
private lemma rgG1_bound {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m)
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1))
    {z : ℝ} (hz1 : 1 ≤ z) :
    z * (Work.FTS.EllExist.Honesty.G1 α m c z) ^ 2
      ≤ 3 * (rgM0 c * z ^ (1 - 2 * Work.FTS.PhiStar.RadialWAux.radQ α m)
          + rgP c * z ^ (1 / 2 - Work.FTS.PhiStar.RadialWAux.radQ α m)
          + rgT c (Real.sqrt z)) := by
  have hq28 : 28 ≤ Work.FTS.PhiStar.RadialWAux.radQ α m := by
    rw [Work.FTS.PhiStar.RadialWAux.radQ, le_div_iff₀ hα]
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    nlinarith
  have hr2 : (-2 : ℝ) ≤ Work.FTS.PhiStar.RadialWAux.radQ α m - 1 := by linarith
  have hr0 : (0 : ℝ) ≤ Work.FTS.PhiStar.RadialWAux.radQ α m - 1 := by linarith
  have hz0 : (0 : ℝ) < z := lt_of_lt_of_le one_pos hz1
  set w : ℝ := Real.sqrt z with hwdef
  have hw1 : 1 ≤ w := by
    rw [hwdef]
    exact sqrt_one_le hz1
  have hwz : w ≤ z := by
    rw [hwdef]
    exact sqrt_le_self hz1
  have hA : (∫ t in (0 : ℝ)..1, c t * t ^ (Work.FTS.PhiStar.RadialWAux.radQ α m - 1)) ^ 2
      ≤ rgM0 c := by
    rw [rgM0_apply]
    exact sq_near_zero_local (r := Work.FTS.PhiStar.RadialWAux.radQ α m - 1) hr2 hnear
  have hB : (∫ t in (1 : ℝ)..w, c t * t ^ (Work.FTS.PhiStar.RadialWAux.radQ α m - 1)) ^ 2
      ≤ rgP c * w ^ (2 * Work.FTS.PhiStar.RadialWAux.radQ α m - 1) := by
    have h := CSTools.sq_interval_le_tail (c := c) (r := Work.FTS.PhiStar.RadialWAux.radQ α m - 1)
      hr0 (w := (1 : ℝ)) (z := w) le_rfl hw1 hfar
    rw [← rgP_apply c] at h
    have he : 2 * (Work.FTS.PhiStar.RadialWAux.radQ α m - 1) + 1
        = 2 * Work.FTS.PhiStar.RadialWAux.radQ α m - 1 := by ring
    simpa only [he] using h
  have hC : (∫ t in w..z, c t * t ^ (Work.FTS.PhiStar.RadialWAux.radQ α m - 1)) ^ 2
      ≤ rgT c w * z ^ (2 * Work.FTS.PhiStar.RadialWAux.radQ α m - 1) := by
    have h := CSTools.sq_interval_le_tail (c := c) (r := Work.FTS.PhiStar.RadialWAux.radQ α m - 1)
      hr0 hw1 hwz hfar
    rw [← rgT_apply c w] at h
    have he : 2 * (Work.FTS.PhiStar.RadialWAux.radQ α m - 1) + 1
        = 2 * Work.FTS.PhiStar.RadialWAux.radQ α m - 1 := by ring
    simpa only [he] using h
  have hsplit : |∫ t in (0 : ℝ)..z, c t * t ^ (Work.FTS.PhiStar.RadialWAux.radQ α m - 1)|
      ≤ |∫ t in (0 : ℝ)..1, c t * t ^ (Work.FTS.PhiStar.RadialWAux.radQ α m - 1)|
        + |∫ t in (1 : ℝ)..w, c t * t ^ (Work.FTS.PhiStar.RadialWAux.radQ α m - 1)|
        + |∫ t in w..z, c t * t ^ (Work.FTS.PhiStar.RadialWAux.radQ α m - 1)| := by
    have h1 := CSTools.abs_intervalIntegral_le_abs_add
      (f := fun t : ℝ => c t * t ^ (Work.FTS.PhiStar.RadialWAux.radQ α m - 1))
      (a := (0 : ℝ)) (m := (1 : ℝ)) (b := z) zero_le_one hz1
    have h2 := CSTools.abs_intervalIntegral_le_abs_add
      (f := fun t : ℝ => c t * t ^ (Work.FTS.PhiStar.RadialWAux.radQ α m - 1))
      (a := (1 : ℝ)) (m := w) (b := z) hw1 hwz
    linarith
  have hI1 : (∫ t in (0 : ℝ)..z, c t * t ^ (Work.FTS.PhiStar.RadialWAux.radQ α m - 1)) ^ 2
      ≤ 3 * (rgM0 c + rgP c * w ^ (2 * Work.FTS.PhiStar.RadialWAux.radQ α m - 1)
          + rgT c w * z ^ (2 * Work.FTS.PhiStar.RadialWAux.radQ α m - 1)) := by
    have h1 := pow_le_pow_left₀
      (abs_nonneg (∫ t in (0 : ℝ)..z, c t * t ^ (Work.FTS.PhiStar.RadialWAux.radQ α m - 1)))
      hsplit 2
    rw [sq_abs] at h1
    have h2 := sq_add_three_le
      |∫ t in (0 : ℝ)..1, c t * t ^ (Work.FTS.PhiStar.RadialWAux.radQ α m - 1)|
      |∫ t in (1 : ℝ)..w, c t * t ^ (Work.FTS.PhiStar.RadialWAux.radQ α m - 1)|
      |∫ t in w..z, c t * t ^ (Work.FTS.PhiStar.RadialWAux.radQ α m - 1)|
    simp only [sq_abs] at h2
    linarith [h1, h2, hA, hB, hC]
  have hpow : (z ^ (-(Work.FTS.PhiStar.RadialWAux.radQ α m))) ^ 2
      = z ^ (-(2 * Work.FTS.PhiStar.RadialWAux.radQ α m)) := rpow_sq_neg hz0 _
  have hzq : 0 ≤ z ^ (1 - 2 * Work.FTS.PhiStar.RadialWAux.radQ α m) := Real.rpow_nonneg hz0.le _
  have hweq : w ^ (2 * Work.FTS.PhiStar.RadialWAux.radQ α m - 1)
      = z ^ ((2 * Work.FTS.PhiStar.RadialWAux.radQ α m - 1) / 2) := by
    rw [hwdef]
    exact sqrt_rpow hz0.le _
  have hG1unfold : Work.FTS.EllExist.Honesty.G1 α m c z
      = z ^ (-(Work.FTS.PhiStar.RadialWAux.radQ α m))
        * (∫ t in (0 : ℝ)..z, c t * t ^ (Work.FTS.PhiStar.RadialWAux.radQ α m - 1)) := by
    rw [Work.FTS.EllExist.Honesty.G1, Work.FTS.PhiStar.RadialWAux.radQ]
    have he : -(2 * (m : ℝ) + 5) / α = -((2 * (m : ℝ) + 5) / α) := by ring
    rw [he]
  calc z * (Work.FTS.EllExist.Honesty.G1 α m c z) ^ 2
      = z * z ^ (-(2 * Work.FTS.PhiStar.RadialWAux.radQ α m))
        * (∫ t in (0 : ℝ)..z, c t * t ^ (Work.FTS.PhiStar.RadialWAux.radQ α m - 1)) ^ 2 := by
        rw [hG1unfold, mul_pow, hpow]
        ring
    _ = z ^ (1 - 2 * Work.FTS.PhiStar.RadialWAux.radQ α m)
        * (∫ t in (0 : ℝ)..z, c t * t ^ (Work.FTS.PhiStar.RadialWAux.radQ α m - 1)) ^ 2 := by
        rw [mul_rpow_neg_two hz0]
    _ ≤ z ^ (1 - 2 * Work.FTS.PhiStar.RadialWAux.radQ α m)
        * (3 * (rgM0 c + rgP c * w ^ (2 * Work.FTS.PhiStar.RadialWAux.radQ α m - 1)
            + rgT c w * z ^ (2 * Work.FTS.PhiStar.RadialWAux.radQ α m - 1))) :=
        mul_le_mul_of_nonneg_left hI1 hzq
    _ = 3 * (rgM0 c * z ^ (1 - 2 * Work.FTS.PhiStar.RadialWAux.radQ α m)
        + rgP c * z ^ (1 / 2 - Work.FTS.PhiStar.RadialWAux.radQ α m)
        + rgT c w) := by
        rw [hweq]
        have hre : z ^ (1 - 2 * Work.FTS.PhiStar.RadialWAux.radQ α m)
              * (3 * (rgM0 c + rgP c * z ^ ((2 * Work.FTS.PhiStar.RadialWAux.radQ α m - 1) / 2)
                  + rgT c w * z ^ (2 * Work.FTS.PhiStar.RadialWAux.radQ α m - 1)))
            = 3 * (z ^ (1 - 2 * Work.FTS.PhiStar.RadialWAux.radQ α m) * rgM0 c
                + rgP c * (z ^ (1 - 2 * Work.FTS.PhiStar.RadialWAux.radQ α m)
                  * z ^ ((2 * Work.FTS.PhiStar.RadialWAux.radQ α m - 1) / 2))
                + rgT c w * (z ^ (1 - 2 * Work.FTS.PhiStar.RadialWAux.radQ α m)
                  * z ^ (2 * Work.FTS.PhiStar.RadialWAux.radQ α m - 1))) := by ring
        rw [hre,
          rpow_mul_expo hz0 (show 1 - 2 * Work.FTS.PhiStar.RadialWAux.radQ α m
              + (2 * Work.FTS.PhiStar.RadialWAux.radQ α m - 1) / 2
              = 1 / 2 - Work.FTS.PhiStar.RadialWAux.radQ α m by ring),
          rpow_mul_expo hz0 (show 1 - 2 * Work.FTS.PhiStar.RadialWAux.radQ α m
              + (2 * Work.FTS.PhiStar.RadialWAux.radQ α m - 1) = 0 by ring),
          Real.rpow_zero, mul_one]
        ring

/-- The `G2` half: `z·G2(z)² ≤ T(z)/(2p+1)`. -/
private lemma rgG2_bound {α : ℝ} {m : ℕ} {c : ℝ → ℝ} (hα : 0 < α) (hm : 1 ≤ m)
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1))
    {z : ℝ} (hz1 : 1 ≤ z) :
    z * (Work.FTS.EllExist.Honesty.G2 α m c z) ^ 2
      ≤ rgT c z / (2 * Work.FTS.PhiStar.RadialWAux.radP α m + 1) := by
  have hz0 : (0 : ℝ) < z := lt_of_lt_of_le one_pos hz1
  have hp0 : (0 : ℝ) < Work.FTS.PhiStar.RadialWAux.radP α m := by
    rw [Work.FTS.PhiStar.RadialWAux.radP]
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    positivity
  have hq := CSTools.sq_tail_le (c := c) (s := -(Work.FTS.PhiStar.RadialWAux.radP α m) - 1)
    (by linarith) hz1 hfar
  rw [← rgT_apply c z] at hq
  have he1 : 2 * (-(Work.FTS.PhiStar.RadialWAux.radP α m) - 1) + 1
      = -(2 * Work.FTS.PhiStar.RadialWAux.radP α m + 1) := by ring
  have he2 : -(2 * (-(Work.FTS.PhiStar.RadialWAux.radP α m) - 1) + 1)
      = 2 * Work.FTS.PhiStar.RadialWAux.radP α m + 1 := by ring
  rw [he2, he1] at hq
  have hG2sq : (Work.FTS.EllExist.Honesty.G2 α m c z) ^ 2
      = z ^ (2 * Work.FTS.PhiStar.RadialWAux.radP α m)
        * (∫ t in Set.Ioi z, c t * t ^ (-(Work.FTS.PhiStar.RadialWAux.radP α m) - 1)) ^ 2 := by
    rw [Work.FTS.EllExist.Honesty.G2, Work.FTS.PhiStar.RadialWAux.radP, mul_pow, rpow_sq hz0]
  calc z * (Work.FTS.EllExist.Honesty.G2 α m c z) ^ 2
      = z * z ^ (2 * Work.FTS.PhiStar.RadialWAux.radP α m)
        * (∫ t in Set.Ioi z, c t * t ^ (-(Work.FTS.PhiStar.RadialWAux.radP α m) - 1)) ^ 2 := by
        rw [hG2sq]; ring
    _ = z ^ (1 + 2 * Work.FTS.PhiStar.RadialWAux.radP α m)
        * (∫ t in Set.Ioi z, c t * t ^ (-(Work.FTS.PhiStar.RadialWAux.radP α m) - 1)) ^ 2 := by
        rw [mul_rpow_two hz0]
    _ ≤ z ^ (1 + 2 * Work.FTS.PhiStar.RadialWAux.radP α m)
        * (rgT c z * (z ^ (-(2 * Work.FTS.PhiStar.RadialWAux.radP α m + 1))
            / (2 * Work.FTS.PhiStar.RadialWAux.radP α m + 1))) :=
        mul_le_mul_of_nonneg_left hq (Real.rpow_nonneg hz0.le _)
    _ = rgT c z / (2 * Work.FTS.PhiStar.RadialWAux.radP α m + 1) := by
        have hre : z ^ (1 + 2 * Work.FTS.PhiStar.RadialWAux.radP α m)
              * (rgT c z * (z ^ (-(2 * Work.FTS.PhiStar.RadialWAux.radP α m + 1))
                  / (2 * Work.FTS.PhiStar.RadialWAux.radP α m + 1)))
            = rgT c z / (2 * Work.FTS.PhiStar.RadialWAux.radP α m + 1)
              * (z ^ (1 + 2 * Work.FTS.PhiStar.RadialWAux.radP α m)
                * z ^ (-(2 * Work.FTS.PhiStar.RadialWAux.radP α m + 1))) := by ring
        rw [hre,
          rpow_mul_expo hz0 (show 1 + 2 * Work.FTS.PhiStar.RadialWAux.radP α m
              + -(2 * Work.FTS.PhiStar.RadialWAux.radP α m + 1) = 0 by ring),
          Real.rpow_zero, mul_one]

/-! ### the pointwise bound and the main theorem -/

/-- The pointwise bound, for `z ≥ 1`. -/
private lemma radGreen_pointwise_bound {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m)
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    ∀ z : ℝ, 1 ≤ z →
      z * (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2 ≤ rgBound α m c z := by
  intro z hz1
  have hz0 : (0 : ℝ) < z := lt_of_lt_of_le one_pos hz1
  have hG1 := rgG1_bound hα hα4 hm hnear hfar hz1
  have hG2 := rgG2_bound hα hm hfar hz1
  have hrg : Work.FTS.PhiStar.Radial.radGreen α m c z
      = Work.FTS.PhiStar.RadialWAux.radK α m
        * (Work.FTS.EllExist.Honesty.G1 α m c z + Work.FTS.EllExist.Honesty.G2 α m c z) := by
    rw [Work.FTS.EllExist.Honesty.radGreen_eq_G1_add_G2]
    rfl
  have hK2nn : 0 ≤ (Work.FTS.PhiStar.RadialWAux.radK α m) ^ 2 := sq_nonneg _
  have h2K : 0 ≤ 2 * (Work.FTS.PhiStar.RadialWAux.radK α m) ^ 2 := by positivity
  rw [rgBound_apply]
  calc z * (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2
      = z * (Work.FTS.PhiStar.RadialWAux.radK α m) ^ 2
        * (Work.FTS.EllExist.Honesty.G1 α m c z + Work.FTS.EllExist.Honesty.G2 α m c z) ^ 2 := by
        rw [hrg]; ring
    _ ≤ z * (Work.FTS.PhiStar.RadialWAux.radK α m) ^ 2
        * (2 * ((Work.FTS.EllExist.Honesty.G1 α m c z) ^ 2
            + (Work.FTS.EllExist.Honesty.G2 α m c z) ^ 2)) :=
        mul_le_mul_of_nonneg_left
          (sq_add_two_le (Work.FTS.EllExist.Honesty.G1 α m c z)
            (Work.FTS.EllExist.Honesty.G2 α m c z))
          (mul_nonneg hz0.le hK2nn)
    _ = 2 * (Work.FTS.PhiStar.RadialWAux.radK α m) ^ 2
        * (z * (Work.FTS.EllExist.Honesty.G1 α m c z) ^ 2
          + z * (Work.FTS.EllExist.Honesty.G2 α m c z) ^ 2) := by ring
    _ ≤ 2 * (Work.FTS.PhiStar.RadialWAux.radK α m) ^ 2
        * (3 * (rgM0 c * z ^ (1 - 2 * Work.FTS.PhiStar.RadialWAux.radQ α m)
            + rgP c * z ^ (1 / 2 - Work.FTS.PhiStar.RadialWAux.radQ α m)
            + rgT c (Real.sqrt z))
          + rgT c z / (2 * Work.FTS.PhiStar.RadialWAux.radP α m + 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ h2K
        linarith [hG1, hG2]

theorem radGreen_sq_mul_self_atTop_zero {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m)
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    Filter.Tendsto (fun z : ℝ => z * (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2)
      Filter.atTop (nhds 0) := by
  have hq28 : 28 ≤ Work.FTS.PhiStar.RadialWAux.radQ α m := by
    rw [Work.FTS.PhiStar.RadialWAux.radQ, le_div_iff₀ hα]
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    nlinarith
  refine squeeze_zero' ?_ ?_ (rgBound_tendsto α m c (by linarith))
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with z hz
    exact mul_nonneg hz (sq_nonneg _)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with z hz
    exact radGreen_pointwise_bound hα hα4 hm hnear hfar z hz

end Work.FTS.PhiStar.Honesty
