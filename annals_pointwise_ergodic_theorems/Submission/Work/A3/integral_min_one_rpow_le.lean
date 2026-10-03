import Mathlib
import Submission.Work.A3.rpow_pow_of_neg_inv

namespace Work.A3

open MeasureTheory Set

/-- The one-sided model integral behind `integral_min_one_rpow_le`: on `(0,1]` the integrand
`(min 1 (x^{-1/d}))^{2s}` equals `1`, and on `(1,∞)` it equals `x^{-2s/d}`, whose integral
converges because `2s/d > 1`; the value is `1 + d/(2s-d)`.

The hypotheses are the ones used by the caller (`d ≥ 1`, `d < 2s`); note `d ≥ 1` is only
needed to have `d ≠ 0`, and `d < 2s` gives the convergence of the tail. -/
lemma integral_Ioi_min_one_rpow (d s : ℕ) (hd : 1 ≤ d) (hs : d < 2 * s) :
    ∫ x in Set.Ioi (0 : ℝ), (min 1 (x ^ (-(1 : ℝ) / (d : ℝ)))) ^ (2 * s)
      = 1 + (d : ℝ) / (((2 * s - d : ℕ) : ℝ)) := by
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : (0 : ℕ) < d)
  -- the exponent of the inner power is non-positive, so `x ↦ x ^ (-1/d)` is antitone on `(0,∞)`
  have hz : (-(1 : ℝ) / (d : ℝ)) ≤ 0 := by
    rw [neg_div]; exact neg_nonpos.mpr (by positivity)
  -- the tail exponent is `< -1`, i.e. `1 < 2s/d`
  have hq_lt : -(2 * (s : ℝ) / (d : ℝ)) < -1 := by
    have hsR : (d : ℝ) < 2 * (s : ℝ) := by exact_mod_cast hs
    rw [neg_lt_neg_iff]
    exact (one_lt_div hdpos).mpr hsR
  set F : ℝ → ℝ := fun x => (min 1 (x ^ (-(1 : ℝ) / (d : ℝ)))) ^ (2 * s) with hF
  -- on `(0,1]` the integrand is constantly `1`
  have hF1 : EqOn F (fun _ : ℝ => (1 : ℝ)) (Set.Ioc 0 1) := by
    intro x hx
    have hge : (1 : ℝ) ≤ x ^ (-(1 : ℝ) / (d : ℝ)) := by
      have := Real.rpow_le_rpow_of_nonpos hx.1 hx.2 hz
      rwa [Real.one_rpow] at this
    simp only [hF]
    rw [min_eq_left hge, one_pow]
  -- on `(1,∞)` the integrand is `x ^ (-(2s)/d)`
  have hF2 : EqOn F (fun x : ℝ => x ^ (-(2 * (s : ℝ) / (d : ℝ)))) (Set.Ioi 1) := by
    intro x hx
    have hpos : (0 : ℝ) < x := lt_trans zero_lt_one hx
    have hle : x ^ (-(1 : ℝ) / (d : ℝ)) ≤ 1 := by
      have := Real.rpow_le_rpow_of_nonpos (x := (1 : ℝ)) (y := x) zero_lt_one (le_of_lt hx) hz
      rwa [Real.one_rpow] at this
    simp only [hF]
    rw [min_eq_right hle]
    exact rpow_pow_of_neg_inv d s hd x (le_of_lt hpos)
  have hInt1 : IntegrableOn F (Set.Ioc (0 : ℝ) 1) volume :=
    (integrableOn_const (C := (1 : ℝ)) (by simp [Real.volume_Ioc]) (by simp)).congr_fun
      hF1.symm measurableSet_Ioc
  have hInt2 : IntegrableOn F (Set.Ioi (1 : ℝ)) volume :=
    (integrableOn_Ioi_rpow_of_lt hq_lt zero_lt_one).congr_fun hF2.symm measurableSet_Ioi
  have hsplit : ∫ x in Set.Ioi (0 : ℝ), F x
      = (∫ x in Set.Ioc (0 : ℝ) 1, F x) + (∫ x in Set.Ioi (1 : ℝ), F x) := by
    have h := setIntegral_union (s := Set.Ioc (0 : ℝ) 1) (t := Set.Ioi (1 : ℝ))
      (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hInt1 hInt2
    rw [Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)] at h
    exact h
  have hA : (∫ x in Set.Ioc (0 : ℝ) 1, F x) = 1 := by
    rw [setIntegral_congr_fun measurableSet_Ioc hF1]
    rw [setIntegral_const]
    simp [Measure.real, Real.volume_Ioc]
  have hB : (∫ x in Set.Ioi (1 : ℝ), F x) = (d : ℝ) / (((2 * s - d : ℕ) : ℝ)) := by
    rw [setIntegral_congr_fun measurableSet_Ioi hF2]
    rw [integral_Ioi_rpow_of_lt hq_lt zero_lt_one]
    rw [Real.one_rpow]
    have ha1 : -(2 * (s : ℝ) / (d : ℝ)) + 1 = -((((2 * s - d : ℕ) : ℝ)) / (d : ℝ)) := by
      rw [Nat.cast_sub (le_of_lt hs), Nat.cast_mul, Nat.cast_ofNat]
      field_simp
      ring
    rw [ha1]
    have hk : (((2 * s - d : ℕ) : ℝ)) ≠ 0 := by
      have : (0 : ℕ) < 2 * s - d := by omega
      exact_mod_cast (ne_of_gt this)
    field_simp
  rw [hsplit, hA, hB]

theorem integral_min_one_rpow_le (d s : ℕ) (hd : 2 ≤ d) (hs : d < 2 * s) :
    ∫ γ : ℝ, (min 1 (|γ| ^ (-(1 : ℝ) / (d : ℝ)))) ^ (2 * s) ≤ 2 * (1 + (d : ℝ)) := by
  -- the integrand is a function of `|γ|`, so the integral over `ℝ` is twice that over `(0,∞)`
  rw [integral_comp_abs (f := fun x : ℝ => (min 1 (x ^ (-(1 : ℝ) / (d : ℝ)))) ^ (2 * s))]
  have hd1 : 1 ≤ d := by omega
  rw [integral_Ioi_min_one_rpow d s hd1 hs]
  -- `d/(2s-d) ≤ d` because `2s - d ≥ 1`
  have h2s : (1 : ℝ) ≤ (((2 * s - d : ℕ) : ℝ)) := by
    exact_mod_cast (by omega : 1 ≤ 2 * s - d)
  have hle : (d : ℝ) / (((2 * s - d : ℕ) : ℝ)) ≤ (d : ℝ) :=
    div_le_self (by positivity) h2s
  linarith

end Work.A3
