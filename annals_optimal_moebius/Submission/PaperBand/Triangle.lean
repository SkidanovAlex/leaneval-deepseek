import Mathlib
open Real
open scoped BigOperators

/-!
# Lemma A1 of Schwartz, *The optimal paper Moebius band* (Lemma 2.3)

A triangle whose base has length `√(1+t²)` and whose height is at least `1`
has the sum of its two remaining sides at least `√(5+t²)` (with equality
exactly for the isosceles triangle of height `1`).

This module proves the needed analytic inequalities.  We place the base
endpoints at `(±a, 0)` and the apex at `(s, h)`, so the two sides have lengths
`√((s+a)²+h²)` and `√((a−s)²+h²)`.  The key step is the reflection trick of
the paper: reflecting one base endpoint across the horizontal line through the
apex and applying the triangle inequality gives `side₁ + side₂ ≥ 2√(a²+h²)`.
-/

noncomputable section
namespace Submission.PaperBand

/-- For any reals `s, a, h` (apex abscissa `s`, half-base `a`, apex height `h`):
the sum of the distances from the apex to the two base endpoints `(±a, 0)` is at
least `2√(a²+h²)`.  (Unconditional: no sign hypotheses are needed.) -/
lemma side_sum_ge_two_sqrt (s a h : ℝ) :
    Real.sqrt ((s+a)^2 + h^2) + Real.sqrt ((a-s)^2 + h^2) ≥ 2 * Real.sqrt (a^2 + h^2) := by
  have h1 : Real.sqrt ((s+a)^2 + h^2) = ‖!₂[s+a, h]‖ := by
    rw [EuclideanSpace.norm_eq]; simp [Fin.sum_univ_two]
  have h2 : Real.sqrt ((a-s)^2 + h^2) = ‖!₂[a-s, h]‖ := by
    rw [EuclideanSpace.norm_eq]; simp [Fin.sum_univ_two]
  have h3 : 2 * Real.sqrt (a^2 + h^2) = ‖!₂[2*a, 2*h]‖ := by
    rw [EuclideanSpace.norm_eq]; simp [Fin.sum_univ_two]
    rw [show (2 * a)^2 + (2 * h)^2 = 4 * (a^2 + h^2) by ring]
    rw [Real.sqrt_mul (by norm_num : 0 ≤ (4:ℝ))]
    congr 1
    norm_num [Real.sq_sqrt]
  rw [h1, h2, h3]
  have hv : !₂[2*a, 2*h] = !₂[s+a, h] + !₂[a-s, h] := by
    ext i <;> fin_cases i <;> simp <;> ring
  rw [hv]
  exact norm_add_le !₂[s+a, h] !₂[a-s, h]

/-- **Lemma A1 / Schwartz Lemma 2.3.**  Let a triangle have base length
`√(1+t²)` (half-base `a = √(1+t²)/2`) and height `h ≥ 1`; if the apex is at
horizontal displacement `s` from the base midpoint then the sum of the two
non-base sides is at least `√(5+t²)`. -/
lemma triangle_sides_bound (s t h : ℝ) (hh : 1 ≤ h) :
    Real.sqrt ((s + Real.sqrt (1 + t^2) / 2)^2 + h^2) +
    Real.sqrt ((Real.sqrt (1 + t^2) / 2 - s)^2 + h^2) ≥ Real.sqrt (5 + t^2) := by
  let a : ℝ := Real.sqrt (1 + t^2) / 2
  have hsides : Real.sqrt ((s + a)^2 + h^2) + Real.sqrt ((a - s)^2 + h^2) ≥
      2 * Real.sqrt (a^2 + h^2) := by
    simpa [a] using side_sum_ge_two_sqrt s a h
  have hm : 4 * (a^2 + 1) = 5 + t^2 := by
    dsimp [a]
    have hs : (Real.sqrt (1 + t^2))^2 = 1 + t^2 := Real.sq_sqrt (by positivity)
    calc
      4 * (((Real.sqrt (1 + t^2)) / 2)^2 + 1) = (Real.sqrt (1 + t^2))^2 + 4 := by ring_nf
      _ = 5 + t^2 := by rw [hs]; ring
  have hsq : 2 * Real.sqrt (a^2 + h^2) ≥ Real.sqrt (5 + t^2) := by
    have hle : 4 * (a^2 + 1) ≤ 4 * (a^2 + h^2) := by nlinarith [hh]
    calc
      2 * Real.sqrt (a^2 + h^2) = Real.sqrt (4 * (a^2 + h^2)) := by
        rw [Real.sqrt_mul (by norm_num : 0 ≤ (4:ℝ))]
        congr 1
        norm_num [Real.sq_sqrt]
      _ ≥ Real.sqrt (4 * (a^2 + 1)) := by
        exact Real.sqrt_le_sqrt hle
      _ = Real.sqrt (5 + t^2) := by rw [hm]
  exact le_trans hsq hsides

/-- **Strict form** (the starred inequality `√(5+t²) < ℓ(∨)` used inside the
proof of Lemma G): if the height is strictly greater than `1` then the sum of
the two sides is strictly greater than `√(5+t²)`. -/
lemma triangle_sides_bound_strict (s t h : ℝ) (hh : 1 < h) :
    Real.sqrt (5 + t^2) <
    Real.sqrt ((s + Real.sqrt (1 + t^2) / 2)^2 + h^2) +
    Real.sqrt ((Real.sqrt (1 + t^2) / 2 - s)^2 + h^2) := by
  let a : ℝ := Real.sqrt (1 + t^2) / 2
  have hsides : Real.sqrt ((s + a)^2 + h^2) + Real.sqrt ((a - s)^2 + h^2) ≥
      2 * Real.sqrt (a^2 + h^2) := by
    simpa [a] using side_sum_ge_two_sqrt s a h
  have hm : 4 * (a^2 + 1) = 5 + t^2 := by
    dsimp [a]
    have hs : (Real.sqrt (1 + t^2))^2 = 1 + t^2 := Real.sq_sqrt (by positivity)
    calc
      4 * (((Real.sqrt (1 + t^2)) / 2)^2 + 1) = (Real.sqrt (1 + t^2))^2 + 4 := by ring_nf
      _ = 5 + t^2 := by rw [hs]; ring
  have hgt : Real.sqrt (5 + t^2) < 2 * Real.sqrt (a^2 + h^2) := by
    have hlt : 4 * (a^2 + 1) < 4 * (a^2 + h^2) := by nlinarith [hh]
    calc
      Real.sqrt (5 + t^2) = Real.sqrt (4 * (a^2 + 1)) := by rw [hm]
      _ < Real.sqrt (4 * (a^2 + h^2)) := Real.sqrt_lt_sqrt (by positivity) hlt
      _ = 2 * Real.sqrt (a^2 + h^2) := by
        rw [Real.sqrt_mul (by norm_num : 0 ≤ (4:ℝ))]
        congr 1
        norm_num [Real.sq_sqrt]
  exact lt_of_lt_of_le hgt hsides

end Submission.PaperBand
end
