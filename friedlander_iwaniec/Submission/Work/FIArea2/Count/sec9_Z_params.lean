/-
# The numerical side of `Work.FIArea2.Count.sec9_Z_bound`

The arithmetic core of §9 (`ZAc_bound`, `ZBc_bound`) is stated for a *free* box radius `R`, threshold
`thr`, parameter `Nr`, saving factor `ϑ` and divisor cutoff `Dm`.  This module discharges the
numerical hypotheses in the actual setting of `Work.FITop.Params`: `R = radN Pa = ⌈√(4N)⌉₊`,
`thr = √(ϑN)`, `Nr = N`:

* `thetaU_lt_one` : `ϑ < 1` (from `ϑ = (log x)^{-A}`, `A > 0`, `x ≥ 3`);
* `radN_nonneg`, `radN_bound` : `0 ≤ radN` and `2·radN + 1 ≤ 8√N`;
* `DmN`, `one_le_DmN`, `cdg_le_DmN` : an explicit bound `(Λ,Δ) ≤ DmN` on the whole box;
* `log_add_two_le_add` : `log(N+2) ≤ log N + 2` for `N ≥ 1`.
-/
import Mathlib
import Submission.Work.FIArea2.Count.sec9_Z_defs

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Work.FIArea2.Count

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The saving factor -/

/-- `ϑ < 1`: `ϑ = (log x)^{-A}` with `A > 0` and `log x ≥ log 3 > 1`. -/
lemma thetaU_lt_one (Pa : Work.FITop.Params) : Pa.ϑ < 1 := by
  have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
  have hlog3 : 1 < Real.log 3 := by
    have h := Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
    rwa [Real.log_exp] at h
  have hlt : Real.log 3 ≤ Real.log (Pa.x : ℝ) := Real.log_le_log (by norm_num) hx3
  have h1 : 1 < Real.log (Pa.x : ℝ) := lt_of_lt_of_le hlog3 hlt
  rw [Pa.hϑ]
  exact Real.rpow_lt_one_of_one_lt_of_neg h1 (by linarith [Pa.hA])

/-! ## 2. The box radius -/

/-- `0 ≤ radN Pa`. -/
lemma radN_nonneg (Pa : Work.FITop.Params) : 0 ≤ Work.FITop.radN Pa := by
  unfold Work.FITop.radN
  exact Nat.cast_nonneg _

/-- `2·radN Pa + 1 ≤ 8√N`. -/
lemma radN_bound (Pa : Work.FITop.Params) :
    2 * (Work.FITop.radN Pa : ℝ) + 1 ≤ 8 * Real.sqrt Pa.N := by
  have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
  have hN0 : (0 : ℝ) ≤ Pa.N := by linarith
  have hceil : ((⌈Real.sqrt (4 * Pa.N)⌉₊ : ℕ) : ℝ) ≤ Real.sqrt (4 * Pa.N) + 1 := by
    have h := Nat.ceil_le_floor_add_one (Real.sqrt (4 * Pa.N))
    have h2 : ((⌊Real.sqrt (4 * Pa.N)⌋₊ : ℕ) : ℝ) ≤ Real.sqrt (4 * Pa.N) :=
      Nat.floor_le (Real.sqrt_nonneg _)
    calc ((⌈Real.sqrt (4 * Pa.N)⌉₊ : ℕ) : ℝ)
        ≤ (((⌊Real.sqrt (4 * Pa.N)⌋₊ + 1 : ℕ)) : ℝ) := by exact_mod_cast h
      _ = ((⌊Real.sqrt (4 * Pa.N)⌋₊ : ℕ) : ℝ) + 1 := by push_cast; ring
      _ ≤ Real.sqrt (4 * Pa.N) + 1 := by linarith
  have hsqrt4 : Real.sqrt (4 * Pa.N) = 2 * Real.sqrt Pa.N := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 ^ 2) Pa.N,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have hrad : (Work.FITop.radN Pa : ℝ) ≤ Real.sqrt (4 * Pa.N) + 1 := by
    unfold Work.FITop.radN
    push_cast
    exact hceil
  have hN1' : (1 : ℝ) ≤ Real.sqrt Pa.N := Real.one_le_sqrt.mpr hN1
  rw [hsqrt4] at hrad
  linarith

/-- `thr = √(ϑN)` is positive. -/
lemma sqrt_thetaN_pos (Pa : Work.FITop.Params) : 0 < Real.sqrt (Pa.ϑ * Pa.N) := by
  have hN1 : (0 : ℝ) < Pa.N := by linarith [Pa.hN1]
  exact Real.sqrt_pos.mpr (mul_pos Pa.hϑ0 hN1)

/-! ## 3. A bound for `(Λ,Δ)` on the box -/

/-- `gcd a b ≤ max a b`. -/
lemma gcd_le_max (a b : ℕ) : Nat.gcd a b ≤ max a b := by
  rcases Nat.eq_zero_or_pos a with h | ha
  · rw [h, Nat.gcd_zero_left, max_eq_right (Nat.zero_le b)]
  · exact le_trans (Nat.le_of_dvd ha (Nat.gcd_dvd_left a b)) (le_max_left a b)

private lemma abs_le_of_mem {R x : ℤ} (h : x ∈ Finset.Icc (-R) R) : |x| ≤ R := by
  rw [Finset.mem_Icc] at h
  exact abs_le.mpr h

private lemma natAbs_tA_le {R h1 h2 r1 r2 : ℤ}
    (ha : |r1| ≤ R) (hb : |r2| ≤ R) :
    (tA h1 h2 r1 r2).natAbs ≤ (R * (h1 ^ 2 + h2 ^ 2)).natAbs := by
  have hsq1 : (0 : ℤ) ≤ h1 ^ 2 := sq_nonneg h1
  have hsq2 : (0 : ℤ) ≤ h2 ^ 2 := sq_nonneg h2
  have hR0 : (0 : ℤ) ≤ R := le_trans (abs_nonneg r1) ha
  have hmain : |tA h1 h2 r1 r2| ≤ |R * (h1 ^ 2 + h2 ^ 2)| := by
    have hA : |tA h1 h2 r1 r2| ≤ |r1| * h1 ^ 2 + |r2| * h2 ^ 2 := by
      calc |tA h1 h2 r1 r2| = |r1 * h1 ^ 2 - r2 * h2 ^ 2| := by rw [tA]
        _ ≤ |r1 * h1 ^ 2| + |r2 * h2 ^ 2| := abs_sub _ _
        _ = |r1| * h1 ^ 2 + |r2| * h2 ^ 2 := by
            rw [abs_mul, abs_mul, abs_of_nonneg hsq1, abs_of_nonneg hsq2]
    have hB1 : |r1| * h1 ^ 2 ≤ R * h1 ^ 2 := mul_le_mul_of_nonneg_right ha hsq1
    have hB2 : |r2| * h2 ^ 2 ≤ R * h2 ^ 2 := mul_le_mul_of_nonneg_right hb hsq2
    have hB : |r1| * h1 ^ 2 + |r2| * h2 ^ 2 ≤ R * (h1 ^ 2 + h2 ^ 2) := by
      have he : R * (h1 ^ 2 + h2 ^ 2) = R * h1 ^ 2 + R * h2 ^ 2 := by ring
      linarith [hB1, hB2, he.le, he.ge]
    exact le_trans hA (le_trans hB (le_abs_self _))
  have hcast : (((tA h1 h2 r1 r2).natAbs : ℕ) : ℤ)
      ≤ (((R * (h1 ^ 2 + h2 ^ 2)).natAbs : ℕ) : ℤ) := by
    rw [Int.natCast_natAbs, Int.natCast_natAbs]
    exact hmain
  exact_mod_cast hcast

private lemma natAbs_tB_le {R h1 h2 s1 s2 : ℤ}
    (ha : |s1| ≤ R) (hb : |s2| ≤ R) :
    (tB h1 h2 s1 s2).natAbs ≤ (R * (h1 ^ 2 + h2 ^ 2)).natAbs := by
  have h := natAbs_tA_le (R := R) (h1 := h2) (h2 := h1) (r1 := s2) (r2 := s1) hb ha
  have e1 : s2 * h2 ^ 2 - s1 * h1 ^ 2 = -(tB h1 h2 s1 s2) := by unfold tB; ring
  have e2 : R * (h2 ^ 2 + h1 ^ 2) = R * (h1 ^ 2 + h2 ^ 2) := by ring
  unfold tA at h
  rwa [e1, Int.natAbs_neg, e2] at h

private lemma dlt_le {R r1 s1 r2 s2 : ℤ}
    (ha : |r1| ≤ R) (hb : |s1| ≤ R) (hc : |r2| ≤ R) (hd : |s2| ≤ R) :
    dlt r1 s1 r2 s2 ≤ (2 * R * R).natAbs := by
  have hR0 : (0 : ℤ) ≤ R := le_trans (abs_nonneg r1) ha
  have hmain : |r1 * s2 - r2 * s1| ≤ |2 * R * R| := by
    calc |r1 * s2 - r2 * s1| ≤ |r1 * s2| + |r2 * s1| := abs_sub _ _
      _ = |r1| * |s2| + |r2| * |s1| := by rw [abs_mul, abs_mul]
      _ ≤ R * R + R * R := by
          have hA : |r1| * |s2| ≤ R * R := mul_le_mul ha hd (abs_nonneg s2) hR0
          have hB : |r2| * |s1| ≤ R * R := mul_le_mul hc hb (abs_nonneg s1) hR0
          linarith
      _ = |2 * R * R| := by
          have h2 : |2 * R * R| = R * R + R * R := by
            rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℤ) ≤ 2), abs_of_nonneg hR0]
            ring
          rw [h2]
  have hcast : (((r1 * s2 - r2 * s1).natAbs : ℕ) : ℤ)
      ≤ (((2 * R * R).natAbs : ℕ) : ℤ) := by
    rw [Int.natCast_natAbs, Int.natCast_natAbs]
    exact hmain
  exact_mod_cast hcast

/-- An explicit bound for `(Λ,Δ)` over the coordinate box `[-R,R]⁴`. -/
def DmN (R : ℤ) (h1 h2 : ℤ) : ℕ :=
  (2 * R * R).natAbs + (R * (h1 ^ 2 + h2 ^ 2)).natAbs + 2

lemma one_le_DmN (R : ℤ) (h1 h2 : ℤ) : 1 ≤ DmN R h1 h2 := by
  unfold DmN; omega

/-- `(Λ,Δ) ≤ DmN R h1 h2` on the coordinate box `[-R,R]⁴`. -/
lemma cdg_le_DmN {R : ℤ} (h1 h2 r1 s1 r2 s2 : ℤ)
    (hr1 : r1 ∈ Finset.Icc (-R) R) (hs1 : s1 ∈ Finset.Icc (-R) R)
    (hr2 : r2 ∈ Finset.Icc (-R) R) (hs2 : s2 ∈ Finset.Icc (-R) R) :
    cdg h1 h2 r1 s1 r2 s2 ≤ DmN R h1 h2 := by
  have ha := abs_le_of_mem hr1
  have hb := abs_le_of_mem hs1
  have hc := abs_le_of_mem hr2
  have hd := abs_le_of_mem hs2
  have hta := natAbs_tA_le (R := R) (h1 := h1) (h2 := h2) ha hc
  have htb := natAbs_tB_le (R := R) (h1 := h1) (h2 := h2) hb hd
  have hdlt := dlt_le (R := R) ha hb hc hd
  have hle : cdg h1 h2 r1 s1 r2 s2
      ≤ max ((2 * R * R).natAbs) ((R * (h1 ^ 2 + h2 ^ 2)).natAbs) := by
    unfold cdg
    rcases Nat.eq_zero_or_pos (dlt r1 s1 r2 s2) with hz | hpos
    · rw [hz, Nat.gcd_zero_right]
      exact le_trans (le_trans (gcd_le_max _ _) (max_le hta htb)) (le_max_right _ _)
    · rcases Nat.eq_zero_or_pos
          (Nat.gcd (tA h1 h2 r1 r2).natAbs (tB h1 h2 s1 s2).natAbs) with hg | hg
      · rw [hg, Nat.gcd_zero_left]
        exact le_trans hdlt (le_max_left _ _)
      · refine le_trans ?_ (le_max_right _ _)
        refine le_trans ?_ (le_trans (gcd_le_max _ _) (max_le hta htb))
        exact Nat.le_of_dvd hg
          (Nat.gcd_dvd_left (Nat.gcd (tA h1 h2 r1 r2).natAbs (tB h1 h2 s1 s2).natAbs)
            (dlt r1 s1 r2 s2))
  have hmono : max ((2 * R * R).natAbs) ((R * (h1 ^ 2 + h2 ^ 2)).natAbs)
      ≤ DmN R h1 h2 := by
    unfold DmN
    omega
  linarith

/-! ## 4. The logarithmic comparison -/

/-- `log(N+2) ≤ log N + 2` for `N ≥ 1`. -/
lemma log_add_two_le_add (N : ℝ) (hN : 1 ≤ N) : Real.log (N + 2) ≤ Real.log N + 2 := by
  have hN0 : 0 < N := by linarith
  have h1 : N + 2 ≤ 3 * N := by linarith
  have h2 : Real.log (N + 2) ≤ Real.log (3 * N) := Real.log_le_log (by linarith) h1
  rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (ne_of_gt hN0)] at h2
  have h3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith
  linarith

end

end Work.FIArea2.Count
