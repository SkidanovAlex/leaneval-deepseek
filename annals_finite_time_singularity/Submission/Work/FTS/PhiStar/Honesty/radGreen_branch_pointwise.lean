import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Submission.Work.FTS.EllExist.RadGreenDefs
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.FTS.PhiStar.Honesty.CSTools.sq_interval_le_tail
import Submission.Work.FTS.PhiStar.Honesty.CSTools.sq_tail_le
import Submission.Work.FTS.PhiStar.Honesty.CSTools.sq_near_zero
import Submission.Work.FTS.PhiStar.Honesty.CSTools.abs_intervalIntegral_le_abs_add

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Topology
open MeasureTheory Set Filter
open Work.FTS.EllExist (rgG1 rgG2 rgP rgQ rgQ_ge rgP_pos)

namespace Work.FTS.PhiStar.Honesty

/-!
# `z · (rgG1 z)² → 0` and `z · (rgG2 z)² → 0` at infinity

The two branches of the radial Green function are

  `rgG1 z = z^{-q}·∫_0^z c t·t^{q-1} dt`,   `rgG2 z = z^{p}·∫_z^∞ c t·t^{-p-1} dt`

with `q = rgQ α m = (2m+5)/α ≥ 28` and `p = rgP α m = 2m/α ≥ 8`.  Under the two `L²`-type
hypotheses on `c` (`c²/t⁴ ∈ L¹(0,1)`, `c² ∈ L¹(1,∞)`) both `z·(rgG1 z)²` and `z·(rgG2 z)²`
vanish at `∞`; we package this as the existence of dominating functions tending to `0`.

The estimate (junk-robust: the Bochner integral of a non-integrable function is `0`, so the
`¬Integrable` branches cause no trouble):

* `(∫_0^1 c t t^{q-1})² ≤ M0`,  `M0 = ∫_0^1 c²/t⁴`  (Cauchy–Schwarz, `t^{2q+2} ≤ 1`);
* `(∫_1^w c t t^{q-1})² ≤ P·w^{2q-1}`,  `P = ∫_{Ioi 1} c²`;
* `(∫_w^z c t t^{q-1})² ≤ T(w)·z^{2q-1}`,  `T(w) = ∫_{Ioi w} c²`;
* `(∫_{Ioi z} c t t^{-p-1})² ≤ T(z)·z^{-2p-1}/(2p+1)`.

Splitting `∫_0^z = ∫_0^1 + ∫_1^{√z} + ∫_{√z}^z` (the *tail* information is used only on the
last piece — the crude bound alone would leave a non-vanishing constant) gives

  `z·(rgG1 z)² ≤ 3·(M0·z^{1-2q} + P·z^{1/2-q} + T(√z))`,   `z·(rgG2 z)² ≤ T(z)/(2p+1)`,

and each of the four terms tends to `0` (the last two because `T(w) → 0` as `w → ∞`).
-/

/-! ### elementary real-power and square estimates -/

/-- `(z^{-a})² = z^{-2a}` for `z > 0`. -/
private lemma rpow_sq_neg {z : ℝ} (hz : 0 < z) (a : ℝ) : (z ^ (-a)) ^ 2 = z ^ (-(2 * a)) := by
  rw [sq, ← Real.rpow_add hz]
  congr 1
  ring

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

/-- `z · z^{-2q} = z^{1-2q}` for `z > 0`. -/
private lemma mul_rpow_neg_two {z : ℝ} (hz : 0 < z) (q : ℝ) :
    z * z ^ (-(2 * q)) = z ^ (1 - 2 * q) :=
  rpow_one_mul hz _

/-- `z · z^{2p} = z^{1+2p}` for `z > 0`. -/
private lemma mul_rpow_two {z : ℝ} (hz : 0 < z) (p : ℝ) :
    z * z ^ (2 * p) = z ^ (1 + 2 * p) :=
  rpow_one_mul hz _

/-! ### the three constants of the estimate -/

/-- `M0 = ∫_0^1 c²/t⁴`: the `L¹`-mass of `c²/t⁴` at the origin. -/
private def nearMass (c : ℝ → ℝ) : ℝ := ∫ t in (0 : ℝ)..1, (c t) ^ 2 / t ^ 4

/-- `P = ∫_{Ioi 1} c²`: the `L¹`-mass of `c²` far out. -/
private def farMass (c : ℝ → ℝ) : ℝ := ∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2

/-- `T z = ∫_{Ioi z} c²`: the tail mass, which tends to `0` at `∞`. -/
private def tailMass (c : ℝ → ℝ) : ℝ → ℝ := fun z => ∫ t in Set.Ioi z, (c t) ^ 2

private lemma nearMass_apply (c : ℝ → ℝ) :
    nearMass c = ∫ t in (0 : ℝ)..1, (c t) ^ 2 / t ^ 4 := rfl

private lemma farMass_apply (c : ℝ → ℝ) :
    farMass c = ∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2 := rfl

private lemma tailMass_apply (c : ℝ → ℝ) (z : ℝ) :
    tailMass c z = ∫ t in Set.Ioi z, (c t) ^ 2 := rfl

/-- `T z = ∫_{Ioi z} c² → 0` as `z → ∞` (no integrability hypothesis needed: it is built into
Mathlib's `MeasureTheory.tendsto_integral_Ioi_zero`). -/
private lemma tailMass_tendsto_zero (c : ℝ → ℝ) : Tendsto (tailMass c) atTop (nhds 0) := by
  unfold tailMass
  exact MeasureTheory.tendsto_integral_Ioi_zero (f := fun t : ℝ => (c t) ^ 2) (μ := volume)
    (l := atTop) (b := fun z : ℝ => z) tendsto_id

/-! ### the two halves of the pointwise bound -/

/-- The `G1` half: `z·rgG1(z)² ≤ 3(M0·z^{1-2q} + P·z^{1/2-q} + T(√z))`. -/
private lemma rgG1_bound {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m)
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1))
    {z : ℝ} (hz1 : 1 ≤ z) :
    z * (rgG1 α m c z) ^ 2
      ≤ 3 * (nearMass c * z ^ (1 - 2 * rgQ α m)
          + farMass c * z ^ (1 / 2 - rgQ α m)
          + tailMass c (Real.sqrt z)) := by
  have hq28 : 28 ≤ rgQ α m := rgQ_ge hα hα4 hm
  have hr2 : (-2 : ℝ) ≤ rgQ α m - 1 := by linarith
  have hr0 : (0 : ℝ) ≤ rgQ α m - 1 := by linarith
  have hz0 : (0 : ℝ) < z := lt_of_lt_of_le one_pos hz1
  set w : ℝ := Real.sqrt z with hwdef
  have hw1 : 1 ≤ w := by
    rw [hwdef]
    exact sqrt_one_le hz1
  have hwz : w ≤ z := by
    rw [hwdef]
    exact sqrt_le_self hz1
  have hA : (∫ t in (0 : ℝ)..1, c t * t ^ (rgQ α m - 1)) ^ 2 ≤ nearMass c := by
    rw [nearMass_apply]
    exact CSTools.sq_near_zero (r := rgQ α m - 1) hr2 hnear
  have hB : (∫ t in (1 : ℝ)..w, c t * t ^ (rgQ α m - 1)) ^ 2
      ≤ farMass c * w ^ (2 * rgQ α m - 1) := by
    have h := CSTools.sq_interval_le_tail (c := c) (r := rgQ α m - 1)
      hr0 (w := (1 : ℝ)) (z := w) le_rfl hw1 hfar
    rw [← farMass_apply c] at h
    have he : 2 * (rgQ α m - 1) + 1 = 2 * rgQ α m - 1 := by ring
    simpa only [he] using h
  have hC : (∫ t in w..z, c t * t ^ (rgQ α m - 1)) ^ 2
      ≤ tailMass c w * z ^ (2 * rgQ α m - 1) := by
    have h := CSTools.sq_interval_le_tail (c := c) (r := rgQ α m - 1)
      hr0 hw1 hwz hfar
    rw [← tailMass_apply c w] at h
    have he : 2 * (rgQ α m - 1) + 1 = 2 * rgQ α m - 1 := by ring
    simpa only [he] using h
  have hsplit : |∫ t in (0 : ℝ)..z, c t * t ^ (rgQ α m - 1)|
      ≤ |∫ t in (0 : ℝ)..1, c t * t ^ (rgQ α m - 1)|
        + |∫ t in (1 : ℝ)..w, c t * t ^ (rgQ α m - 1)|
        + |∫ t in w..z, c t * t ^ (rgQ α m - 1)| := by
    have h1 := CSTools.abs_intervalIntegral_le_abs_add
      (f := fun t : ℝ => c t * t ^ (rgQ α m - 1))
      (a := (0 : ℝ)) (m := (1 : ℝ)) (b := z) zero_le_one hz1
    have h2 := CSTools.abs_intervalIntegral_le_abs_add
      (f := fun t : ℝ => c t * t ^ (rgQ α m - 1))
      (a := (1 : ℝ)) (m := w) (b := z) hw1 hwz
    linarith
  have hI1 : (∫ t in (0 : ℝ)..z, c t * t ^ (rgQ α m - 1)) ^ 2
      ≤ 3 * (nearMass c + farMass c * w ^ (2 * rgQ α m - 1)
          + tailMass c w * z ^ (2 * rgQ α m - 1)) := by
    have h1 := pow_le_pow_left₀
      (abs_nonneg (∫ t in (0 : ℝ)..z, c t * t ^ (rgQ α m - 1))) hsplit 2
    rw [sq_abs] at h1
    have h2 := sq_add_three_le
      |∫ t in (0 : ℝ)..1, c t * t ^ (rgQ α m - 1)|
      |∫ t in (1 : ℝ)..w, c t * t ^ (rgQ α m - 1)|
      |∫ t in w..z, c t * t ^ (rgQ α m - 1)|
    simp only [sq_abs] at h2
    linarith [h1, h2, hA, hB, hC]
  have hpow : (z ^ (-(rgQ α m))) ^ 2 = z ^ (-(2 * rgQ α m)) := rpow_sq_neg hz0 _
  have hzq : 0 ≤ z ^ (1 - 2 * rgQ α m) := Real.rpow_nonneg hz0.le _
  have hweq : w ^ (2 * rgQ α m - 1) = z ^ ((2 * rgQ α m - 1) / 2) := by
    rw [hwdef]
    exact sqrt_rpow hz0.le _
  have hG1unfold : rgG1 α m c z
      = z ^ (-(rgQ α m))
        * (∫ t in (0 : ℝ)..z, c t * t ^ (rgQ α m - 1)) := by
    simp only [Work.FTS.EllExist.rgG1, Work.FTS.EllExist.rgA, Work.FTS.EllExist.rgF1]
  calc z * (rgG1 α m c z) ^ 2
      = z * z ^ (-(2 * rgQ α m))
        * (∫ t in (0 : ℝ)..z, c t * t ^ (rgQ α m - 1)) ^ 2 := by
        rw [hG1unfold, mul_pow, hpow]
        ring
    _ = z ^ (1 - 2 * rgQ α m)
        * (∫ t in (0 : ℝ)..z, c t * t ^ (rgQ α m - 1)) ^ 2 := by
        rw [mul_rpow_neg_two hz0]
    _ ≤ z ^ (1 - 2 * rgQ α m)
        * (3 * (nearMass c + farMass c * w ^ (2 * rgQ α m - 1)
            + tailMass c w * z ^ (2 * rgQ α m - 1))) :=
        mul_le_mul_of_nonneg_left hI1 hzq
    _ = 3 * (nearMass c * z ^ (1 - 2 * rgQ α m)
        + farMass c * z ^ (1 / 2 - rgQ α m)
        + tailMass c w) := by
        rw [hweq]
        have hre : z ^ (1 - 2 * rgQ α m)
              * (3 * (nearMass c + farMass c * z ^ ((2 * rgQ α m - 1) / 2)
                  + tailMass c w * z ^ (2 * rgQ α m - 1)))
            = 3 * (z ^ (1 - 2 * rgQ α m) * nearMass c
                + farMass c * (z ^ (1 - 2 * rgQ α m)
                  * z ^ ((2 * rgQ α m - 1) / 2))
                + tailMass c w * (z ^ (1 - 2 * rgQ α m)
                  * z ^ (2 * rgQ α m - 1))) := by ring
        rw [hre,
          rpow_mul_expo hz0 (show 1 - 2 * rgQ α m
              + (2 * rgQ α m - 1) / 2 = 1 / 2 - rgQ α m by ring),
          rpow_mul_expo hz0 (show 1 - 2 * rgQ α m
              + (2 * rgQ α m - 1) = 0 by ring),
          Real.rpow_zero, mul_one]
        ring

/-- The `G2` half: `z·rgG2(z)² ≤ T(z)/(2p+1)`. -/
private lemma rgG2_bound {α : ℝ} {m : ℕ} {c : ℝ → ℝ} (hα : 0 < α) (hm : 1 ≤ m)
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1))
    {z : ℝ} (hz1 : 1 ≤ z) :
    z * (rgG2 α m c z) ^ 2 ≤ tailMass c z / (2 * rgP α m + 1) := by
  have hz0 : (0 : ℝ) < z := lt_of_lt_of_le one_pos hz1
  have hp0 : (0 : ℝ) < rgP α m := rgP_pos hα hm
  have hq := CSTools.sq_tail_le (c := c) (s := -(rgP α m) - 1)
    (by linarith) hz1 hfar
  rw [← tailMass_apply c z] at hq
  have he1 : 2 * (-(rgP α m) - 1) + 1 = -(2 * rgP α m + 1) := by ring
  have he2 : -(2 * (-(rgP α m) - 1) + 1) = 2 * rgP α m + 1 := by ring
  rw [he2, he1] at hq
  have hG2sq : (rgG2 α m c z) ^ 2
      = z ^ (2 * rgP α m)
        * (∫ t in Set.Ioi z, c t * t ^ (-(rgP α m) - 1)) ^ 2 := by
    rw [show rgG2 α m c z
        = z ^ (rgP α m) * (∫ t in Set.Ioi z, c t * t ^ (-(rgP α m) - 1)) from by
      simp only [Work.FTS.EllExist.rgG2, Work.FTS.EllExist.rgB, Work.FTS.EllExist.rgF2]]
    rw [mul_pow, rpow_sq hz0]
  calc z * (rgG2 α m c z) ^ 2
      = z * z ^ (2 * rgP α m)
        * (∫ t in Set.Ioi z, c t * t ^ (-(rgP α m) - 1)) ^ 2 := by
        rw [hG2sq]; ring
    _ = z ^ (1 + 2 * rgP α m)
        * (∫ t in Set.Ioi z, c t * t ^ (-(rgP α m) - 1)) ^ 2 := by
        rw [mul_rpow_two hz0]
    _ ≤ z ^ (1 + 2 * rgP α m)
        * (tailMass c z * (z ^ (-(2 * rgP α m + 1))
            / (2 * rgP α m + 1))) :=
        mul_le_mul_of_nonneg_left hq (Real.rpow_nonneg hz0.le _)
    _ = tailMass c z / (2 * rgP α m + 1) := by
        have hre : z ^ (1 + 2 * rgP α m)
              * (tailMass c z * (z ^ (-(2 * rgP α m + 1))
                  / (2 * rgP α m + 1)))
            = tailMass c z / (2 * rgP α m + 1)
              * (z ^ (1 + 2 * rgP α m)
                * z ^ (-(2 * rgP α m + 1))) := by ring
        rw [hre,
          rpow_mul_expo hz0 (show 1 + 2 * rgP α m
              + -(2 * rgP α m + 1) = 0 by ring),
          Real.rpow_zero, mul_one]

/-! ### the two limit computations -/

/-- `3·(M0·z^{1-2q} + P·z^{1/2-q} + T(√z)) → 0` for `q > 1/2`. -/
private lemma tendsto_b1 (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (hq : 1 / 2 < rgQ α m) :
    Tendsto (fun z : ℝ =>
      3 * (nearMass c * z ^ (1 - 2 * rgQ α m)
        + farMass c * z ^ (1 / 2 - rgQ α m)
        + tailMass c (Real.sqrt z))) atTop (nhds 0) := by
  have hTtend : Tendsto (tailMass c) atTop (nhds 0) := tailMass_tendsto_zero c
  have h1 : Tendsto (fun z : ℝ => nearMass c * z ^ (1 - 2 * rgQ α m))
      atTop (nhds 0) := by
    have h := (tendsto_rpow_neg_atTop (y := 2 * rgQ α m - 1) (by linarith)).const_mul
      (nearMass c)
    simpa only [show -(2 * rgQ α m - 1) = 1 - 2 * rgQ α m by ring, mul_zero] using h
  have h2 : Tendsto (fun z : ℝ => farMass c * z ^ (1 / 2 - rgQ α m))
      atTop (nhds 0) := by
    have h := (tendsto_rpow_neg_atTop (y := rgQ α m - 1 / 2) (by linarith)).const_mul
      (farMass c)
    simpa only [show -(rgQ α m - 1 / 2) = 1 / 2 - rgQ α m by ring, mul_zero] using h
  have h3 : Tendsto (fun z : ℝ => tailMass c (Real.sqrt z)) atTop (nhds 0) :=
    hTtend.comp Real.tendsto_sqrt_atTop
  have h5 : Tendsto (fun z : ℝ =>
      nearMass c * z ^ (1 - 2 * rgQ α m)
        + farMass c * z ^ (1 / 2 - rgQ α m) + tailMass c (Real.sqrt z))
      atTop (nhds 0) := by
    simpa using (h1.add h2).add h3
  simpa using h5.const_mul 3

/-- `T z / (2p+1) → 0`. -/
private lemma tendsto_b2 (α : ℝ) (m : ℕ) (c : ℝ → ℝ) :
    Tendsto (fun z : ℝ => tailMass c z / (2 * rgP α m + 1)) atTop (nhds 0) := by
  have h := (tailMass_tendsto_zero c).div_const (2 * rgP α m + 1)
  simpa using h

/-! ### the packaged statement -/

/-- The two radial Green branches satisfy `z * (rgG1 z)^2 → 0` and `z * (rgG2 z)^2 → 0` at `∞`,
packaged as the existence of dominating functions tending to `0` (only `z ≥ 1` is asserted
pointwise).  The proof is already written, with `private` helpers, in
`Submission/Work/FTS/PhiStar/Honesty/radGreen_sq_mul_self_atTop_zero.lean` (`rgG1_bound`,
`rgG2_bound`, `rgBound_tendsto`): copy those helpers into your file (they cannot be imported) and
finish with the limit computations for
`b1 z = 3 * (rgM0 c * z^(1-2q) + rgP c * z^(1/2-q) + rgT c (Real.sqrt z))` and
`b2 z = rgT c z / (2p+1)` (`rgT c z = ∫ t in Ioi z, (c t)^2 → 0`).  Details:
`Submission/Work/FTS/PhiStar/Honesty/NOTES_radGreen_branch_pointwise.md`. -/
theorem radGreen_branch_pointwise {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m)
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    ∃ b1 b2 : ℝ → ℝ,
      (∀ z : ℝ, 1 ≤ z → z * (Work.FTS.EllExist.rgG1 α m c z) ^ 2 ≤ b1 z) ∧
      (∀ z : ℝ, 1 ≤ z → z * (Work.FTS.EllExist.rgG2 α m c z) ^ 2 ≤ b2 z) ∧
      Filter.Tendsto b1 Filter.atTop (nhds 0) ∧
      Filter.Tendsto b2 Filter.atTop (nhds 0) := by
  have hq : 1 / 2 < rgQ α m := by have h := rgQ_ge hα hα4 hm; linarith
  exact ⟨fun z => 3 * (nearMass c * z ^ (1 - 2 * rgQ α m)
        + farMass c * z ^ (1 / 2 - rgQ α m)
        + tailMass c (Real.sqrt z)),
    fun z => tailMass c z / (2 * rgP α m + 1),
    fun z hz => rgG1_bound hα hα4 hm hnear hfar hz,
    fun z hz => rgG2_bound hα hm hfar hz,
    tendsto_b1 α m c hq,
    tendsto_b2 α m c⟩

end Work.FTS.PhiStar.Honesty
