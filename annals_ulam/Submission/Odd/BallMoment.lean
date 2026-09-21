import Mathlib

/-!
# The ball moment identities for every positive slope

`Work.Odd.ball_moment_identity` proves the two reference identities of the ball (semicircular
profile, `h = 0`, chord endpoints `±1/√(1+s²)`) for `s ≥ 1`; this file is the same statement for
all `s > 0`, which is the range needed by the Volterra/transition-slope analysis of the odd case
(the transition window `[1-3/10, 1-1/10]` lies below `1`).  The proof is the scaling substitution
`t = u/√(1+s²)`; it does not use the hypothesis on `s` beyond its positivity.
-/

namespace Submission.Odd
namespace BallMoment

open MeasureTheory
open scoped Interval

set_option autoImplicit false

/-- The two reference identities of the ball at every positive slope. -/
lemma ball_moment_identity_pos (n : ℕ) {s : ℝ} (hs : 0 < s) :
    (∫ t in (-(1 / Real.sqrt (1 + s ^ 2)))..(1 / Real.sqrt (1 + s ^ 2)),
        (1 - t ^ 2 - (s * t) ^ 2) ^ n * Real.sqrt (1 - t ^ 2 - (s * t) ^ 2)) =
      (∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ n * Real.sqrt (1 - u ^ 2)) / Real.sqrt (1 + s ^ 2) ∧
    (∫ t in (-(1 / Real.sqrt (1 + s ^ 2)))..(1 / Real.sqrt (1 + s ^ 2)),
        (1 - t ^ 2 - (s * t) ^ 2) ^ (n - 1) * Real.sqrt (1 - t ^ 2 - (s * t) ^ 2) * t) = 0 := by
  set k : ℝ := Real.sqrt (1 + s ^ 2) with hkdef
  have hspos : (0:ℝ) < 1 + s^2 := by positivity
  have hspos' : (1:ℝ) + s^2 ≠ 0 := ne_of_gt hspos
  have hk2 : k ^ 2 = 1 + s ^ 2 := by rw [hkdef, Real.sq_sqrt hspos.le]
  have hkpos : 0 < k := by rw [hkdef]; exact Real.sqrt_pos.mpr hspos
  have hkne : k ≠ 0 := ne_of_gt hkpos
  -- the key pointwise identity: the scaled radicand equals `1 - u ^ 2`
  have key1 : ∀ u : ℝ, 1 - (u / k) ^ 2 - (s * (u / k)) ^ 2 = 1 - u ^ 2 := by
    intro u
    have h' : (u / k) ^ 2 * (1 + s^2) = u^2 := by
      rw [div_pow, hk2, div_mul_cancel₀ _ hspos']
    have h : (u / k) ^ 2 + (s * (u / k)) ^ 2 = u^2 := by
      calc (u/k)^2 + (s*(u/k))^2 = (u/k)^2 * (1+s^2) := by ring
        _ = u^2 := h'
    linarith
  constructor
  · -- even moment: change of variables `t = u / k`
    have hFG : (fun x : ℝ => (1 - (x/k)^2 - (s*(x/k))^2)^n * Real.sqrt (1 - (x/k)^2 - (s*(x/k))^2))
        = (fun u : ℝ => (1 - u^2)^n * Real.sqrt (1 - u^2)) := by
      funext u; rw [key1 u]
    have hcomp := intervalIntegral.integral_comp_div
      (f := fun t : ℝ => (1 - t^2 - (s*t)^2)^n * Real.sqrt (1 - t^2 - (s*t)^2))
      (a := (-1:ℝ)) (b := 1) (c := k) hkne
    rw [hFG] at hcomp
    have hnegk : ((-1:ℝ)/k) = -(1/k) := by rw [← neg_div]
    rw [hnegk] at hcomp
    have hgoal : (∫ u in (-1:ℝ)..1, (1-u^2)^n * Real.sqrt (1-u^2)) / k
        = ∫ t in (-(1/k))..(1/k), (1 - t^2 - (s*t)^2)^n * Real.sqrt (1 - t^2 - (s*t)^2) := by
      rw [hcomp, smul_eq_mul, mul_div_cancel_left₀ _ hkne]
    exact hgoal.symm
  · -- odd moment: the scaled integrand is odd, so its integral over `[-1,1]` vanishes
    have hG2zero : (∫ u in (-1:ℝ)..1, (1-u^2)^(n-1) * Real.sqrt (1-u^2) * u) = 0 := by
      let g : ℝ → ℝ := fun x => (1-x^2)^(n-1) * Real.sqrt (1-x^2) * x
      change (∫ u in (-1:ℝ)..1, g u) = 0
      have h1 : (∫ u in (-1:ℝ)..1, g (-u)) = ∫ u in (-1:ℝ)..1, g u := by
        rw [intervalIntegral.integral_comp_neg]
        norm_num
      have h3 : (fun u : ℝ => g (-u)) = (fun u : ℝ => - g u) := by
        funext u
        simp only [g]
        rw [neg_sq]
        ring
      have h2 : (∫ u in (-1:ℝ)..1, g (-u)) = -(∫ u in (-1:ℝ)..1, g u) := by
        rw [h3, intervalIntegral.integral_neg]
      linarith
    have hF2zero : (∫ u in (-1:ℝ)..1, ((1-u^2)^(n-1) * Real.sqrt (1-u^2) * u) * k⁻¹) = 0 := by
      rw [intervalIntegral.integral_mul_const, hG2zero, zero_mul]
    have hcomp2 := intervalIntegral.integral_comp_div
      (f := fun t : ℝ => (1 - t^2 - (s*t)^2)^(n-1) * Real.sqrt (1 - t^2 - (s*t)^2) * t)
      (a := (-1:ℝ)) (b := 1) (c := k) hkne
    have hF2 : (fun x : ℝ => (1 - (x/k)^2 - (s*(x/k))^2)^(n-1) * Real.sqrt (1 - (x/k)^2 - (s*(x/k))^2) * (x/k))
        = (fun u : ℝ => ((1-u^2)^(n-1) * Real.sqrt (1-u^2) * u) * k⁻¹) := by
      funext u
      rw [key1 u, div_eq_mul_inv]
      ring
    rw [hF2, hF2zero] at hcomp2
    have hnegk : ((-1:ℝ)/k) = -(1/k) := by rw [← neg_div]
    rw [hnegk] at hcomp2
    have hzero : k • (∫ t in (-(1/k))..(1/k), (1-t^2-(s*t)^2)^(n-1) * Real.sqrt (1-t^2-(s*t)^2) * t) = 0 := hcomp2.symm
    rcases (smul_eq_zero.mp hzero) with h | h
    · exact absurd h hkne
    · exact h

end BallMoment
end Submission.Odd
