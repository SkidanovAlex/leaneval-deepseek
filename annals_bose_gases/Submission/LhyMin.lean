import Mathlib.Analysis.SpecialFunctions.Pow.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Pure-calculus atom for the final LHY assembly (Session 31)

Statement of the two minimisation estimates needed by the endgame "F2"
step of the corpus-native Fournais--Solovej replay.  They are pure real
analysis, numerically verified, and interface-robust.

Mathematical content:
1. `lhyMin_tangent`:  for `x ∈ [0,1]`, `x^(5/2) ≥ 1 + (5/2)(x−1)`
   (the tangent line at `x = 1` lies below the convex graph of `x ↦ x^(5/2)`).
2. `lhyMinCore`:  for `B := c·√q ≤ 4/5` and `s ∈ [0,2]`,
   `(s−1)² + B·s^(5/2) ≥ B − (25/16)·B²`.
   Consequently, with `s := t/ρ` and `B := c·√(ρa³)`, the density-window
   infimum of the two-term LHY expression is controlled from below.
-/

namespace Submission

namespace BoseGases

open scoped Real

/-- Tangent-line lower bound for `x ↦ x^(5/2)` on `[0,1]`:
`x^(5/2) ≥ 1 + (5/2)(x - 1)`.  Proof certificate: with `y := x^(1/2) ∈ [0,1]`,
`2·x^(5/2) - 5·x + 3 = 2y^5 - 5y^2 + 3 = (y-1)^2·(2y^3 + 4y^2 + 6y + 3) ≥ 0`. -/
lemma lhyMin_tangent {x : ℝ} (hx0 : 0 ≤ x) (_hx1 : x ≤ 1) :
    1 + (5 / 2 : ℝ) * (x - 1) ≤ x ^ (5 / 2 : ℝ) := by
  let u : ℝ := x ^ (1 / 2 : ℝ)
  have hu0 : 0 ≤ u := Real.rpow_nonneg hx0 (1 / 2)
  have hu2 : u ^ 2 = x := by
    dsimp [u]
    calc
      (x ^ (1 / 2 : ℝ)) ^ 2 = √x ^ 2 := by rw [← Real.sqrt_eq_rpow]
      _ = x := Real.sq_sqrt hx0
  have hu5 : u ^ 5 = x ^ (5 / 2 : ℝ) := by
    dsimp [u]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hx0]
    congr 1
    norm_num
  have hpoly : 0 ≤ 2 * u ^ 5 - 5 * u ^ 2 + 3 := by
    have hfac : 2 * u ^ 5 - 5 * u ^ 2 + 3 = (u - 1) ^ 2 * (2 * u ^ 3 + 4 * u ^ 2 + 6 * u + 3) := by ring
    rw [hfac]
    have hf2 : 0 ≤ 2 * u ^ 3 + 4 * u ^ 2 + 6 * u + 3 := by
      have h1 : 0 ≤ 2 * u ^ 3 := mul_nonneg (by norm_num) (pow_nonneg hu0 3)
      have h2 : 0 ≤ 4 * u ^ 2 := mul_nonneg (by norm_num) (sq_nonneg u)
      have h3 : 0 ≤ 6 * u := mul_nonneg (by norm_num) hu0
      linarith
    exact mul_nonneg (sq_nonneg (u - 1)) hf2
  have hmain : 0 ≤ 2 * x ^ (5 / 2 : ℝ) - 5 * x + 3 := by
    rw [← hu5, ← hu2]
    simpa [pow_succ, pow_two] using hpoly
  nlinarith

/-- Version of `lhyMinCore` phrased directly with `B := c·√q`. -/
lemma lhyMinCore_B {B : ℝ} (hB0 : 0 ≤ B) (_hB : B ≤ 4 / 5) :
    ∀ s : ℝ, 0 ≤ s → s ≤ 2 →
      (s - 1) ^ 2 + B * s ^ (5 / 2 : ℝ) ≥ B - (25 / 16) * B ^ 2 := by
  intro s hs0 hs2
  by_cases hs1 : s ≤ 1
  · -- s ∈ [0,1]: use the tangent line at 1 and complete the square.
    have htan : 1 + (5 / 2 : ℝ) * (s - 1) ≤ s ^ (5 / 2 : ℝ) :=
      lhyMin_tangent (x := s) hs0 hs1
    have hBtan : B * (1 + (5 / 2 : ℝ) * (s - 1)) ≤ B * s ^ (5 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left htan hB0
    let u : ℝ := 1 - s
    have hu0 : 0 ≤ u := by dsimp [u]; linarith
    have hs1' : s - 1 = -u := by dsimp [u]; ring
    have hsq : (s - 1) ^ 2 = u ^ 2 := by rw [hs1']; ring
    have hsqfree : B + u ^ 2 - (5 / 2 : ℝ) * B * u = (u - (5 / 4 : ℝ) * B) ^ 2 + B - (25 / 16 : ℝ) * B ^ 2 := by
      ring
    have hsqnonneg : 0 ≤ (u - (5 / 4 : ℝ) * B) ^ 2 := sq_nonneg (u - (5 / 4 : ℝ) * B)
    have hB1 : B * (1 + (5 / 2 : ℝ) * (s - 1)) = B - (5 / 2 : ℝ) * B * (1 - s) := by ring
    calc
      (s - 1) ^ 2 + B * s ^ (5 / 2 : ℝ) ≥ u ^ 2 + B * (1 + (5 / 2 : ℝ) * (s - 1)) := by
        rw [hsq]
        have h := add_le_add_right hBtan (u ^ 2)
        simpa [add_comm] using h
      _ = B + u ^ 2 - (5 / 2 : ℝ) * B * u := by dsimp [u]; ring
      _ = (u - (5 / 4 : ℝ) * B) ^ 2 + B - (25 / 16 : ℝ) * B ^ 2 := hsqfree
      _ ≥ B - (25 / 16 : ℝ) * B ^ 2 := by linarith
  · -- s ∈ (1,2]: (s−1)² ≥ 0 and s^{5/2} ≥ 1, so B·s^{5/2} ≥ B.
    have hsgt1 : 1 < s := lt_of_not_ge hs1
    have hsge1 : 1 ≤ s := le_of_lt hsgt1
    have hone : (1 : ℝ) ^ (5 / 2 : ℝ) = 1 := by norm_num
    have hpow : 1 ≤ s ^ (5 / 2 : ℝ) := by
      rw [← hone]
      exact Real.rpow_le_rpow (by norm_num) hsge1 (by norm_num : 0 ≤ (5 / 2 : ℝ))
    have hBpow : B ≤ B * s ^ (5 / 2 : ℝ) := by
      calc
        B = B * 1 := by ring
        _ ≤ B * s ^ (5 / 2 : ℝ) := mul_le_mul_of_nonneg_left hpow hB0
    have hB2 : 0 ≤ (25 / 16 : ℝ) * B ^ 2 := mul_nonneg (by norm_num) (sq_nonneg B)
    have hsq2 : 0 ≤ (s - 1) ^ 2 := sq_nonneg (s - 1)
    linarith

/-- Core density-window minimisation: for `0 ≤ B := c·√q ≤ 4/5` and
`s ∈ [0,2]`, `(s−1)² + B·s^(5/2) ≥ B − (25/16)·B²`.  (Proof: split at `s = 1`;
for `s ≤ 1` write `u := 1−s`, use `lhyMin_tangent` on `s = 1−u` and complete
the square `u² − (5/2)B·u + B = (u − (5/4)B)² + B − (25/16)B²`.) -/
lemma lhyMinCore {c q : ℝ} (hc : 0 ≤ c) (hq : 0 ≤ q) (hB : c * √q ≤ 4 / 5) :
    ∀ s : ℝ, 0 ≤ s → s ≤ 2 →
      (s - 1) ^ 2 + c * √q * s ^ (5 / 2 : ℝ) ≥ c * √q - (25 / 16) * c ^ 2 * q := by
  let B : ℝ := c * √q
  have hB0 : 0 ≤ B := mul_nonneg hc (Real.sqrt_nonneg q)
  have hBle : B ≤ 4 / 5 := by dsimp [B]; exact hB
  have hBsq : B ^ 2 = c ^ 2 * q := by
    dsimp [B]
    calc
      (c * √q) ^ 2 = c ^ 2 * (√q) ^ 2 := by ring
      _ = c ^ 2 * q := by rw [Real.sq_sqrt hq]
  intro s hs0 hs2
  have hmain := lhyMinCore_B (B := B) hB0 hBle s hs0 hs2
  have hL : (s - 1) ^ 2 + B * s ^ (5 / 2 : ℝ) = (s - 1) ^ 2 + c * √q * s ^ (5 / 2 : ℝ) := by
    dsimp [B]
  have hR : B - (25 / 16) * B ^ 2 = c * √q - (25 / 16) * c ^ 2 * q := by
    rw [hBsq]
    dsimp [B]
    ring
  rw [hL, hR] at hmain
  exact hmain

end BoseGases

end Submission
