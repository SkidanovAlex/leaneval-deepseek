import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixR.LatGreen.MadelungBound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The far-time tail of the periodised heat kernel

`Work.BoseFixR.LatGreen.tailIntegral_le`:

`∫_{t > 1/10} (heatPeriod t u − 1) dt ≤ 1/250`  for every `u`.

The mean-zero part of the periodised heat kernel decays like the *Fourier* tail
`rhoZ t = 2 Σ_{j≥1} e^{−4π²tj²}` (`md_tail_pointwise` gives
`|heatPeriod t u − 1| ≤ 3 ρ + 3 ρ² + ρ³` for `t ≥ etaZ = 1/32`, where `ρ = rhoZ t`), and
`rhoZ` decays exponentially with rate `4π²` (`SZDecay`).  Splitting at `η = 1/10` (rather
than at `etaZ`) makes the numerical constant small: with `ρ(t) ≤ e^{−4π²(t−η)} R` and
`R = ρ(η) ≤ 25/594`, the cubic majorant `tailMajor` has integral

`3R/a + 3R²/(2a) + R³/(3a) ≤ 1/250`,  `a = 4π² ≥ 39`.

The only numerical input at the splitting point is `SZ (1/10) ≤ 25/1188`, proved from the
geometric majorant `exp_geom_majorant` together with `e^{−39/10} ≤ 1/48` and
`e^{−117/10} ≤ 1/100`.
-/

set_option maxHeartbeats 1000000

noncomputable section

open scoped Real BigOperators
open MeasureTheory Set

namespace Work.BoseFixR.LatGreen

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ### Elementary numerical estimates -/

/-- `e^{−39/10} ≤ 1/48` (the partial sum of `e^{39/10}` up to order `10` exceeds `48`). -/
lemma exp_neg_39_div_10_le : Real.exp (-(39 / 10 : ℝ)) ≤ 1 / 48 := by
  have hkey : (48 : ℝ)
      ≤ ∑ i ∈ Finset.range 11, ((39 / 10 : ℝ) ^ i / (i.factorial : ℝ)) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hsum := Real.sum_le_exp_of_nonneg (x := (39 / 10 : ℝ)) (by norm_num) 11
  have h48 : (48 : ℝ) ≤ Real.exp (39 / 10 : ℝ) := le_trans hkey hsum
  calc Real.exp (-(39 / 10 : ℝ)) = (Real.exp (39 / 10 : ℝ))⁻¹ := by rw [Real.exp_neg]
    _ ≤ (48 : ℝ)⁻¹ := (inv_le_inv₀ (Real.exp_pos _) (by norm_num)).mpr h48
    _ = 1 / 48 := by norm_num

/-- `e^{−117/10} ≤ 1/100` (the partial sum of `e^{117/10}` up to order `3` exceeds `100`). -/
lemma exp_neg_117_div_10_le : Real.exp (-(117 / 10 : ℝ)) ≤ 1 / 100 := by
  have hkey : (100 : ℝ)
      ≤ ∑ i ∈ Finset.range 4, ((117 / 10 : ℝ) ^ i / (i.factorial : ℝ)) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hsum := Real.sum_le_exp_of_nonneg (x := (117 / 10 : ℝ)) (by norm_num) 4
  have h100 : (100 : ℝ) ≤ Real.exp (117 / 10 : ℝ) := le_trans hkey hsum
  calc Real.exp (-(117 / 10 : ℝ)) = (Real.exp (117 / 10 : ℝ))⁻¹ := by rw [Real.exp_neg]
    _ ≤ (100 : ℝ)⁻¹ := (inv_le_inv₀ (Real.exp_pos _) (by norm_num)).mpr h100
    _ = 1 / 100 := by norm_num

/-- The Fourier tail at the splitting time `1/10` is small: `SZ (1/10) ≤ 25/1188`.

Indeed with `c = 4π²/10 ≥ 39/10` the geometric majorant gives
`SZ (1/10) ≤ e^{-c}/(1 - e^{-3c}) ≤ (1/48)/(99/100) = 25/1188`. -/
lemma SZ_ten_le : SZ (1 / 10) ≤ 25 / 1188 := by
  set c : ℝ := 4 * Real.pi ^ 2 / 10 with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  have hc39 : (39 : ℝ) / 10 ≤ c := by
    rw [hc]; nlinarith [Real.pi_gt_d2, Real.pi_pos]
  have hSZeq : SZ (1 / 10) = ∑' j : ℕ, Real.exp (-c * ((j : ℝ) + 1) ^ 2) := by
    rw [SZ]
    refine tsum_congr (fun j => ?_)
    rw [hc]
    congr 1
    ring
  have hmajor := exp_geom_majorant hcpos
  have hE1 : Real.exp (-c) ≤ 1 / 48 :=
    le_trans (Real.exp_le_exp.mpr (by linarith)) exp_neg_39_div_10_le
  have hE3 : Real.exp (-(3 * c)) ≤ 1 / 100 :=
    le_trans (Real.exp_le_exp.mpr (by linarith)) exp_neg_117_div_10_le
  have hden : (99 : ℝ) / 100 ≤ 1 - Real.exp (-(3 * c)) := by linarith
  have hdenpos : 0 < 1 - Real.exp (-(3 * c)) := by
    have h := Real.exp_pos (-(3 * c)); linarith
  have hfinal : Real.exp (-c) / (1 - Real.exp (-(3 * c))) ≤ 25 / 1188 := by
    rw [div_le_iff₀ hdenpos]
    have h2b : 25 / 1188 * (99 / 100) ≤ 25 / 1188 * (1 - Real.exp (-(3 * c))) :=
      mul_le_mul_of_nonneg_left hden (by norm_num)
    have h2c : (25 : ℝ) / 1188 * (99 / 100) = 1 / 48 := by norm_num
    linarith [hE1, h2b, h2c]
  calc SZ (1 / 10) = ∑' j : ℕ, Real.exp (-c * ((j : ℝ) + 1) ^ 2) := hSZeq
    _ ≤ Real.exp (-c) / (1 - Real.exp (-(3 * c))) := by
        simpa only [neg_mul] using hmajor
    _ ≤ 25 / 1188 := hfinal

/-! ### Integrating the cubic majorant -/

/-- The majorant `tailMajor a R η` is integrable on `(η, ∞)` when `a > 0`. -/
lemma integrableOn_tailMajor {a R η : ℝ} (ha : 0 < a) :
    MeasureTheory.IntegrableOn (fun t : ℝ => tailMajor a R η t) (Set.Ioi η) := by
  have h1 : MeasureTheory.Integrable (fun t : ℝ => Real.exp (-(a * (t - η))))
      (volume.restrict (Set.Ioi η)) := integrableOn_exp_shift ha
  have h2 : MeasureTheory.Integrable (fun t : ℝ => Real.exp (-((2 * a) * (t - η))))
      (volume.restrict (Set.Ioi η)) :=
    integrableOn_exp_shift (by linarith : (0 : ℝ) < 2 * a)
  have h3 : MeasureTheory.Integrable (fun t : ℝ => Real.exp (-((3 * a) * (t - η))))
      (volume.restrict (Set.Ioi η)) :=
    integrableOn_exp_shift (by linarith : (0 : ℝ) < 3 * a)
  have hsum : MeasureTheory.Integrable (fun t : ℝ => tailMajor a R η t)
      (volume.restrict (Set.Ioi η)) :=
    ((h1.const_mul (3 * R)).add (h2.const_mul (3 * R ^ 2))).add (h3.const_mul (R ^ 3))
  exact hsum

/-- The integral of the cubic majorant:
`∫_{t > η} tailMajor a R η = 3R/a + 3R²/(2a) + R³/(3a)`. -/
lemma integral_tailMajor {a R η : ℝ} (ha : 0 < a) :
    ∫ t in Set.Ioi η, tailMajor a R η t = 3 * R / a + 3 * R ^ 2 / (2 * a) + R ^ 3 / (3 * a) := by
  have ha2 : (0 : ℝ) < 2 * a := by linarith
  have ha3 : (0 : ℝ) < 3 * a := by linarith
  have h1 : MeasureTheory.Integrable (fun t : ℝ => Real.exp (-(a * (t - η))))
      (volume.restrict (Set.Ioi η)) := integrableOn_exp_shift ha
  have h2 : MeasureTheory.Integrable (fun t : ℝ => Real.exp (-((2 * a) * (t - η))))
      (volume.restrict (Set.Ioi η)) := integrableOn_exp_shift ha2
  have h3 : MeasureTheory.Integrable (fun t : ℝ => Real.exp (-((3 * a) * (t - η))))
      (volume.restrict (Set.Ioi η)) := integrableOn_exp_shift ha3
  have hA : ∫ t in Set.Ioi η, (3 * R) * Real.exp (-(a * (t - η))) = 3 * R / a := by
    rw [integral_const_mul, integral_exp_shift ha, one_div, div_eq_mul_inv]
  have hB : ∫ t in Set.Ioi η, (3 * R ^ 2) * Real.exp (-((2 * a) * (t - η)))
      = 3 * R ^ 2 / (2 * a) := by
    rw [integral_const_mul, integral_exp_shift ha2, one_div, div_eq_mul_inv]
  have hC : ∫ t in Set.Ioi η, (R ^ 3) * Real.exp (-((3 * a) * (t - η)))
      = R ^ 3 / (3 * a) := by
    rw [integral_const_mul, integral_exp_shift ha3, one_div, div_eq_mul_inv]
  have hsplit1 : ∫ t in Set.Ioi η,
        ((3 * R) * Real.exp (-(a * (t - η))) + (3 * R ^ 2) * Real.exp (-((2 * a) * (t - η)))
          + (R ^ 3) * Real.exp (-((3 * a) * (t - η))))
      = (∫ t in Set.Ioi η,
            ((3 * R) * Real.exp (-(a * (t - η)))
              + (3 * R ^ 2) * Real.exp (-((2 * a) * (t - η)))))
        + ∫ t in Set.Ioi η, (R ^ 3) * Real.exp (-((3 * a) * (t - η))) :=
    integral_add ((h1.const_mul (3 * R)).add (h2.const_mul (3 * R ^ 2)))
      (h3.const_mul (R ^ 3))
  have hsplit2 : ∫ t in Set.Ioi η,
        ((3 * R) * Real.exp (-(a * (t - η))) + (3 * R ^ 2) * Real.exp (-((2 * a) * (t - η))))
      = (∫ t in Set.Ioi η, (3 * R) * Real.exp (-(a * (t - η))))
        + ∫ t in Set.Ioi η, (3 * R ^ 2) * Real.exp (-((2 * a) * (t - η))) :=
    integral_add (h1.const_mul (3 * R)) (h2.const_mul (3 * R ^ 2))
  simp only [tailMajor]
  rw [hsplit1, hsplit2, hA, hB, hC]

/-- The numerical value of the majorant integral at `R = 25/594` is at most `1/250`
(for any decay rate `a ≥ 39`, and `4π² ≥ 39`). -/
lemma tailMajor_arith_ten {a : ℝ} (ha : (39 : ℝ) ≤ a) :
    3 * (25 / 594 : ℝ) / a + 3 * (25 / 594 : ℝ) ^ 2 / (2 * a)
      + (25 / 594 : ℝ) ^ 3 / (3 * a) ≤ 1 / 250 := by
  have e1 : 3 * (25 / 594 : ℝ) / a ≤ 3 * (25 / 594 : ℝ) / 39 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) ha
  have e2 : 3 * (25 / 594 : ℝ) ^ 2 / (2 * a) ≤ 3 * (25 / 594 : ℝ) ^ 2 / (2 * 39) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith : (2 : ℝ) * 39 ≤ 2 * a)
  have e3 : (25 / 594 : ℝ) ^ 3 / (3 * a) ≤ (25 / 594 : ℝ) ^ 3 / (3 * 39) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith : (3 : ℝ) * 39 ≤ 3 * a)
  have hsum : 3 * (25 / 594 : ℝ) / 39 + 3 * (25 / 594 : ℝ) ^ 2 / (2 * 39)
      + (25 / 594 : ℝ) ^ 3 / (3 * 39) ≤ 1 / 250 := by norm_num
  linarith

/-! ### The tail integral -/

theorem tailIntegral_le (u : EuclideanSpace ℝ (Fin 3)) :
    ∫ t in Set.Ioi (1 / 10), (heatPeriod t u - 1) ≤ 1 / 250 := by
  set η : ℝ := 1 / 10 with hη
  set a : ℝ := 4 * Real.pi ^ 2 with ha
  set R : ℝ := 25 / 594 with hR
  have hηpos : (0 : ℝ) < η := by rw [hη]; norm_num
  have hηetaZ : etaZ ≤ η := by rw [hη, etaZ]; norm_num
  have hapos : (0 : ℝ) < a := by rw [ha]; positivity
  have ha39 : (39 : ℝ) ≤ a := by rw [ha]; nlinarith [Real.pi_gt_d2, Real.pi_pos]
  have hSZη : SZ η ≤ 25 / 1188 := by rw [hη]; exact SZ_ten_le
  -- the Fourier tail decays exponentially from the splitting time
  have hrho : ∀ t : ℝ, η ≤ t → rhoZ t ≤ Real.exp (-(a * (t - η))) * R := by
    intro t ht
    have h1 : SZ t ≤ Real.exp (-(a * (t - η))) * SZ η := by
      have h := SZDecay hηpos ht
      rwa [← ha] at h
    have h2 : (2 : ℝ) * SZ η ≤ R := by rw [hR]; linarith
    calc rhoZ t = 2 * SZ t := rfl
      _ ≤ 2 * (Real.exp (-(a * (t - η))) * SZ η) := by linarith
      _ = Real.exp (-(a * (t - η))) * (2 * SZ η) := by ring
      _ ≤ Real.exp (-(a * (t - η))) * R := mul_le_mul_of_nonneg_left h2 (Real.exp_nonneg _)
  -- the pointwise cubic majorant
  have hbnd : ∀ t : ℝ, t ∈ Set.Ioi η → heatPeriod t u - 1 ≤ tailMajor a R η t := by
    intro t ht
    have htge : η ≤ t := le_of_lt ht
    have hpt : heatPeriod t u - 1 ≤ 3 * rhoZ t + 3 * (rhoZ t) ^ 2 + (rhoZ t) ^ 3 :=
      le_trans (le_abs_self _) (md_tail_pointwise (le_trans hηetaZ htge) u)
    have hρ0 : 0 ≤ rhoZ t := rhoZ_nonneg t
    have hdec := hrho t htge
    have hE2 : (Real.exp (-(a * (t - η)))) ^ 2 = Real.exp (-((2 * a) * (t - η))) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hE3 : (Real.exp (-(a * (t - η)))) ^ 3 = Real.exp (-((3 * a) * (t - η))) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hp2 := pow_le_pow_left₀ hρ0 hdec 2
    have hp3 := pow_le_pow_left₀ hρ0 hdec 3
    rw [mul_pow, hE2] at hp2
    rw [mul_pow, hE3] at hp3
    simp only [tailMajor]
    nlinarith [hp2, hp3, hdec]
  -- integration
  have hfint : IntegrableOn (fun t : ℝ => heatPeriod t u - 1) (Set.Ioi η) :=
    (md_integrableOn_tail u).mono_set (Set.Ioi_subset_Ioi hηetaZ)
  have hGint : IntegrableOn (fun t : ℝ => tailMajor a R η t) (Set.Ioi η) :=
    integrableOn_tailMajor hapos
  have hle_ae : (fun t : ℝ => heatPeriod t u - 1) ≤ᵐ[volume.restrict (Set.Ioi η)]
      (fun t : ℝ => tailMajor a R η t) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact hbnd t ht
  have hmono := integral_mono_ae hfint hGint hle_ae
  have hGval : ∫ t in Set.Ioi η, tailMajor a R η t
      = 3 * R / a + 3 * R ^ 2 / (2 * a) + R ^ 3 / (3 * a) := integral_tailMajor hapos
  have harith : 3 * R / a + 3 * R ^ 2 / (2 * a) + R ^ 3 / (3 * a) ≤ 1 / 250 := by
    rw [hR]
    exact tailMajor_arith_ten ha39
  calc ∫ t in Set.Ioi (1 / 10), (heatPeriod t u - 1)
      = ∫ t in Set.Ioi η, (heatPeriod t u - 1) := by rw [← hη]
    _ ≤ ∫ t in Set.Ioi η, tailMajor a R η t := hmono
    _ = 3 * R / a + 3 * R ^ 2 / (2 * a) + R ^ 3 / (3 * a) := hGval
    _ ≤ 1 / 250 := harith

end Work.BoseFixR.LatGreen
