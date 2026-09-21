import Mathlib
import Submission.Work.OddCurve.LowSlope.RadSharpDefs
import Submission.Work.OddCurve.LowSlope.RadialLogDefs
import Submission.Work.OddCurve.LowSlope.RadialLogConstruction
import Submission.Work.OddCurve.LowSlope.sol_deriv_formulas
import Submission.Work.OddCurve.LowSlope.deriv_bounds_generic
import Submission.Work.OddCurve.LowSlope.radial_first_coeff

/-!
# Sharp first- and second-derivative bounds for the low-slope odd radial pair

For the normalised two-power system

  `R^{2n+2} + r^{2n+2} = 2 + A`,  `R^{2n+1} - r^{2n+1} = B`

with data bounds `|A| ≤ σ ≤ 1/8`, `|A'| ≤ √(2δ(σ-|A|))`, `|A''| ≤ δ` (and the same for `B`)
and the sharp box `SharpBox n R r`, this file proves

  `|R'| ≤ 3(σ+δ)/(n+1)`, `|r'| ≤ 3(σ+δ)/(n+1)`,
  `|R''| ≤ 3(σ+δ)/(n+1)`, `|r''| ≤ 3(σ+δ)/(n+1)`.

The proof uses the explicit formulas `sol_deriv_formulas`, `sol_deriv2_R_formula_aux` and the
box bounds: writing `Q = 2n+1`, `P = 2n+2`, `N = n+1`, the two denominators of the formulas are
bounded below by `P·Q·R^{2n}(R+r) ≥ P·Q·(25/18)` etc.

* First derivative: `|Q·A' + P·r·B'| ≤ (Q + P r)√(2δσ) ≤ (198/125)·P·R^{2n}(R+r)·√(2δσ)`
  (using `Q ≤ P`, `r ≤ 6/5`, `R^{2n} ≥ 5/6`, `R + r ≥ 5/3`), whence
  `|R'| ≤ (198/125)√(2δσ)/Q ≤ (198/125)·(3/4)(σ+δ)/N ≤ 3(σ+δ)/N`,
  and `(R')² ≤ (26/5)δσ/Q²`.
* Second derivative: the four terms of the solved formula are bounded by
  `9δ/(25N)`, `108δ/(125N)`, `39δ/(50N)`, `117δ/(200N)` respectively (the last two using
  `(R')² ≤ (26/5)δσ/Q²`, `(r/R)^{2n} ≤ 3/2` and `σ ≤ 1/8`); their sum is `(2589/1000)δ/N ≤ 3(σ+δ)/N`.

The final theorem `sol_deriv_bounds_sharp` applies this to `R = solR n A B`, `r = solr n A B`.
-/

noncomputable section

open Filter Topology Set
open scoped Topology ContDiff

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Work.OddCurve.LowSlope

/-! ## Three elementary lemmas -/

/-- `√(2δσ) ≤ (3/4)(σ+δ)` for `σ, δ ≥ 0` (weighted AM–GM; `√2 < 3/2`). -/
lemma sdb_sqrt_le {σ δ : ℝ} (hσ : 0 ≤ σ) (hδ : 0 ≤ δ) :
    Real.sqrt (2 * δ * σ) ≤ (3 / 4) * (σ + δ) := by
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [sq_nonneg (σ - δ), mul_nonneg hσ hδ]

/-- Negating a function negates its derivative. -/
lemma sdb_deriv_neg_fun (f : ℝ → ℝ) :
    deriv (fun y : ℝ => - f y) = fun y : ℝ => - deriv f y := by
  funext y
  by_cases h : DifferentiableAt ℝ f y
  · exact (h.hasDerivAt.neg).deriv
  · have h2 : ¬ DifferentiableAt ℝ (fun y : ℝ => - f y) y :=
      fun hh => h (differentiableAt_fun_neg_iff.mp hh)
    rw [deriv_zero_of_not_differentiableAt h2, deriv_zero_of_not_differentiableAt h, neg_zero]

/-! ## The four terms of the second-order formula -/

/-- The first term `A''/((2n+2) R^{2n} (R+r))` of the formula for `R''`. -/
lemma sdb_term1 (n : ℕ) {R r A : ℝ → ℝ} {δ α : ℝ} (hδ : 0 < δ)
    (hbox : SharpBox n (R α) (r α)) (hA2 : |deriv (deriv A) α| ≤ δ) :
    |deriv (deriv A) α / (↑(2 * n + 2) * R α ^ (2 * n) * (R α + r α))|
      ≤ 9 * δ / (25 * ((n : ℝ) + 1)) := by
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6, hc1, hc2, hc3, hc4, hc5, hc6, hd1, hd2, he⟩ := hbox
  have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hN25 : (0 : ℝ) < 25 * ((n : ℝ) + 1) := by positivity
  have hP2N : ((2 * n + 2 : ℕ) : ℝ) = 2 * ((n : ℝ) + 1) := by push_cast; ring
  have hX0 : (0 : ℝ) ≤ R α ^ (2 * n) := by linarith
  have hXY : ((5 : ℝ) / 6) * (5 / 3) ≤ R α ^ (2 * n) * (R α + r α) :=
    mul_le_mul hb3 he (by norm_num) hX0
  have hXY9 : (25 : ℝ) / 18 ≤ R α ^ (2 * n) * (R α + r α) := by linarith [hXY]
  have hkey : 25 * ((n : ℝ) + 1) ≤ 9 * (((2 * n + 2 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α)) := by
    rw [hP2N]
    nlinarith only [hXY9, hN]
  have hD1 : 0 < ↑(2 * n + 2) * R α ^ (2 * n) * (R α + r α) := by positivity
  rw [abs_div, abs_of_pos hD1, div_le_div_iff₀ hD1 hN25]
  have h1 := mul_le_mul_of_nonneg_right hA2 (by positivity : (0 : ℝ) ≤ 25 * ((n : ℝ) + 1))
  have h2 := mul_le_mul_of_nonneg_left hkey (le_of_lt hδ)
  nlinarith only [h1, h2]

/-- The second term `r B''/((2n+1) R^{2n} (R+r))` of the formula for `R''`. -/
lemma sdb_term2 (n : ℕ) {R r B : ℝ → ℝ} {δ α : ℝ} (hδ : 0 < δ)
    (hbox : SharpBox n (R α) (r α)) (hB2 : |deriv (deriv B) α| ≤ δ) :
    |r α * deriv (deriv B) α / (↑(2 * n + 1) * R α ^ (2 * n) * (R α + r α))|
      ≤ 108 * δ / (125 * ((n : ℝ) + 1)) := by
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6, hc1, hc2, hc3, hc4, hc5, hc6, hd1, hd2, he⟩ := hbox
  have hQ : (0 : ℝ) < ((2 * n + 1 : ℕ) : ℝ) := by positivity
  have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hN125 : (0 : ℝ) < 125 * ((n : ℝ) + 1) := by positivity
  have hQN : (n : ℝ) + 1 ≤ ((2 * n + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hX0 : (0 : ℝ) ≤ R α ^ (2 * n) := by linarith
  have hXY : ((5 : ℝ) / 6) * (5 / 3) ≤ R α ^ (2 * n) * (R α + r α) :=
    mul_le_mul hb3 he (by norm_num) hX0
  have hXY9 : (25 : ℝ) / 18 ≤ R α ^ (2 * n) * (R α + r α) := by linarith [hXY]
  have hkey : 150 * ((n : ℝ) + 1)
      ≤ 108 * (((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α)) := by
    have h150 : 150 * ((n : ℝ) + 1)
        ≤ 108 * (R α ^ (2 * n) * (R α + r α)) * ((n : ℝ) + 1) := by
      have h := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hXY9 (by norm_num : (0:ℝ) ≤ 108)) (le_of_lt hN)
      linarith [h]
    have hQN' : 108 * (R α ^ (2 * n) * (R α + r α)) * ((n : ℝ) + 1)
        ≤ 108 * (R α ^ (2 * n) * (R α + r α)) * ((2 * n + 1 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hQN (by positivity)
    linarith [h150, hQN']
  have hD2 : 0 < ↑(2 * n + 1) * R α ^ (2 * n) * (R α + r α) := by positivity
  rw [abs_div, abs_mul, abs_of_pos (by linarith : (0:ℝ) < r α), abs_of_pos hD2,
    div_le_div_iff₀ hD2 hN125]
  have hstep1 : r α * |deriv (deriv B) α| * (125 * ((n : ℝ) + 1))
      ≤ (6 / 5) * |deriv (deriv B) α| * (125 * ((n : ℝ) + 1)) := by
    have h0 : r α * |deriv (deriv B) α| ≤ (6 / 5) * |deriv (deriv B) α| :=
      mul_le_mul_of_nonneg_right hc2 (abs_nonneg _)
    exact mul_le_mul_of_nonneg_right h0 (by positivity)
  have hstep2 : (6 / 5) * |deriv (deriv B) α| * (125 * ((n : ℝ) + 1))
      ≤ (6 / 5) * δ * (125 * ((n : ℝ) + 1)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB2 (by norm_num)) (by positivity)
  have hstep3 : (6 / 5) * δ * (125 * ((n : ℝ) + 1)) = δ * (150 * ((n : ℝ) + 1)) := by ring
  have hstep4 : δ * (150 * ((n : ℝ) + 1))
      ≤ δ * (108 * (((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α))) :=
    mul_le_mul_of_nonneg_left hkey (le_of_lt hδ)
  calc r α * |deriv (deriv B) α| * (125 * ((n : ℝ) + 1))
      ≤ δ * (108 * (((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α))) := by
        linarith [hstep1, hstep2, hstep3, hstep4]
    _ = 108 * δ * (↑(2 * n + 1) * R α ^ (2 * n) * (R α + r α)) := by ring

/-- The third term `(R')²((2n+1) - r/(R+r))/R` of the formula for `R''`. -/
lemma sdb_term3 (n : ℕ) {R r : ℝ → ℝ} {σ δ α : ℝ} (hσ8 : σ ≤ 1 / 8) (hδ : 0 < δ)
    (hbox : SharpBox n (R α) (r α))
    (hRsq : (deriv R α) ^ 2 ≤ (26 / 5) * (δ * σ) / (((2 * n + 1 : ℕ) : ℝ)) ^ 2) :
    |deriv R α ^ 2 * (↑(2 * n + 2) - 1 - r α / (R α + r α)) / R α|
      ≤ 39 * δ / (50 * ((n : ℝ) + 1)) := by
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6, hc1, hc2, hc3, hc4, hc5, hc6, hd1, hd2, he⟩ := hbox
  have hRpos : (0 : ℝ) < R α := by linarith
  have hrpos : (0 : ℝ) < r α := by linarith
  have hQ : (0 : ℝ) < ((2 * n + 1 : ℕ) : ℝ) := by positivity
  have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hQN : (n : ℝ) + 1 ≤ ((2 * n + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hPm1 : ((2 * n + 2 : ℕ) : ℝ) - 1 = ((2 * n + 1 : ℕ) : ℝ) := by push_cast; ring
  have hQ1 : (1 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := by
    have : (1 : ℕ) ≤ 2 * n + 1 := by omega
    exact_mod_cast this
  have hdivle1 : r α / (R α + r α) ≤ 1 := by
    rw [div_le_one (by linarith : (0:ℝ) < R α + r α)]
    linarith
  have hdivnn : 0 ≤ r α / (R α + r α) := div_nonneg (le_of_lt hrpos) (by linarith)
  have hc0 : 0 ≤ ((2 * n + 2 : ℕ) : ℝ) - 1 - r α / (R α + r α) := by rw [hPm1]; linarith
  have hc1 : ((2 * n + 2 : ℕ) : ℝ) - 1 - r α / (R α + r α) ≤ ((2 * n + 1 : ℕ) : ℝ) := by
    rw [hPm1]; linarith
  have hnn : 0 ≤ deriv R α ^ 2 * (((2 * n + 2 : ℕ) : ℝ) - 1 - r α / (R α + r α)) / R α :=
    div_nonneg (mul_nonneg (sq_nonneg _) hc0) (le_of_lt hRpos)
  rw [abs_of_nonneg hnn]
  have hmid : deriv R α ^ 2 * (((2 * n + 2 : ℕ) : ℝ) - 1 - r α / (R α + r α)) / R α
      ≤ 156 * δ * σ / (25 * ((2 * n + 1 : ℕ) : ℝ)) := by
    calc deriv R α ^ 2 * (((2 * n + 2 : ℕ) : ℝ) - 1 - r α / (R α + r α)) / R α
        ≤ deriv R α ^ 2 * ((2 * n + 1 : ℕ) : ℝ) / R α := by
          rw [div_le_div_iff_of_pos_right hRpos]
          exact mul_le_mul_of_nonneg_left hc1 (sq_nonneg _)
      _ ≤ deriv R α ^ 2 * ((2 * n + 1 : ℕ) : ℝ) * (6 / 5) := by
          rw [div_le_iff₀ hRpos]
          have h6R : (1:ℝ) ≤ (6/5)*R α := by nlinarith [hb1]
          have hnn2 : (0:ℝ) ≤ deriv R α ^ 2 * ((2 * n + 1 : ℕ) : ℝ) := by positivity
          nlinarith only [h6R, hnn2]
      _ ≤ ((26 / 5) * (δ * σ) / (((2 * n + 1 : ℕ) : ℝ)) ^ 2) * ((2 * n + 1 : ℕ) : ℝ) * (6 / 5) := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hRsq (le_of_lt hQ)) (by norm_num)
      _ = 156 * δ * σ / (25 * ((2 * n + 1 : ℕ) : ℝ)) := by
          field_simp
          ring
  have hσN : 8 * σ * ((n : ℝ) + 1) ≤ ((2 * n + 1 : ℕ) : ℝ) := by
    nlinarith only [hσ8, hQN, hN]
  have hfin : 156 * δ * σ / (25 * ((2 * n + 1 : ℕ) : ℝ)) ≤ 39 * δ / (50 * ((n : ℝ) + 1)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith only [hσN, hδ, hQ, hN]
  linarith [hmid, hfin]

/-- The fourth term `(r/R)^{2n}(r')²/(R+r)` of the formula for `R''`. -/
lemma sdb_term4 (n : ℕ) {R r : ℝ → ℝ} {σ δ α : ℝ} (hσ8 : σ ≤ 1 / 8) (hδ : 0 < δ)
    (hbox : SharpBox n (R α) (r α))
    (hrsq : (deriv r α) ^ 2 ≤ (26 / 5) * (δ * σ) / (((2 * n + 1 : ℕ) : ℝ)) ^ 2) :
    |(r α / R α) ^ (2 * n) * deriv r α ^ 2 / (R α + r α)|
      ≤ 117 * δ / (200 * ((n : ℝ) + 1)) := by
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6, hc1, hc2, hc3, hc4, hc5, hc6, hd1, hd2, he⟩ := hbox
  have hRpos : (0 : ℝ) < R α := by linarith
  have hrpos : (0 : ℝ) < r α := by linarith
  have hQ : (0 : ℝ) < ((2 * n + 1 : ℕ) : ℝ) := by positivity
  have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hQN : (n : ℝ) + 1 ≤ ((2 * n + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hnn : 0 ≤ (r α / R α) ^ (2 * n) * deriv r α ^ 2 / (R α + r α) := by positivity
  rw [abs_of_nonneg hnn]
  have hmid : (r α / R α) ^ (2 * n) * deriv r α ^ 2 / (R α + r α)
      ≤ 117 * δ * σ / (25 * (((2 * n + 1 : ℕ) : ℝ)) ^ 2) := by
    calc (r α / R α) ^ (2 * n) * deriv r α ^ 2 / (R α + r α)
        ≤ (3 / 2) * deriv r α ^ 2 / (R α + r α) := by
          apply div_le_div_of_nonneg_right _ (by linarith : (0:ℝ) ≤ R α + r α)
          exact mul_le_mul_of_nonneg_right hd1 (sq_nonneg _)
      _ ≤ (3 / 2) * deriv r α ^ 2 * (3 / 5) := by
          rw [div_le_iff₀ (by linarith : (0:ℝ) < R α + r α)]
          have h5 : (1:ℝ) ≤ (3/5)*(R α + r α) := by nlinarith [he]
          nlinarith only [h5, sq_nonneg (deriv r α)]
      _ ≤ (3 / 2) * ((26 / 5) * (δ * σ) / (((2 * n + 1 : ℕ) : ℝ)) ^ 2) * (3 / 5) := by
          apply mul_le_mul_of_nonneg_right _ (by norm_num)
          exact mul_le_mul_of_nonneg_left hrsq (by norm_num)
      _ = 117 * δ * σ / (25 * (((2 * n + 1 : ℕ) : ℝ)) ^ 2) := by
          field_simp
          ring
  have hσN : 8 * σ * ((n : ℝ) + 1) ≤ ((2 * n + 1 : ℕ) : ℝ) := by
    nlinarith only [hσ8, hQN, hN]
  have hfin : 117 * δ * σ / (25 * (((2 * n + 1 : ℕ) : ℝ)) ^ 2)
      ≤ 117 * δ / (200 * ((n : ℝ) + 1)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hσN2 : 8 * σ * ((n : ℝ) + 1) ≤ (((2 * n + 1 : ℕ) : ℝ)) ^ 2 := by
      nlinarith only [hσN, hQN, hQ, hN]
    nlinarith only [hσN2, hδ, hQ, hN]
  linarith [hmid, hfin]

/-! ## The first-order formula bound -/

/-- Sharp bound for a first derivative given the explicit formula of `sol_deriv_formulas`. -/
lemma deriv_one_bound_of_formula (n : ℕ) (hn : 1 ≤ n) {R r A B : ℝ → ℝ} {σ δ α : ℝ}
    (hσ : 0 < σ) (hσ8 : σ ≤ 1 / 8) (hδ : 0 < δ)
    (hRpos : 0 < R α) (hrpos : 0 < r α) (hbox : SharpBox n (R α) (r α))
    (hA1 : |deriv A α| ≤ Real.sqrt (2 * δ * σ)) (hB1 : |deriv B α| ≤ Real.sqrt (2 * δ * σ))
    (hform : deriv R α = (((2 * n + 1 : ℕ) : ℝ) * deriv A α + ((2 * n + 2 : ℕ) : ℝ) * r α * deriv B α)
        / (((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α))) :
    |deriv R α| ≤ 3 * (σ + δ) / ((n : ℝ) + 1) ∧
      (deriv R α) ^ 2 ≤ (26 / 5) * (δ * σ) / (((2 * n + 1 : ℕ) : ℝ)) ^ 2 := by
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6, hc1, hc2, hc3, hc4, hc5, hc6, hd1, hd2, he⟩ := hbox
  have hQ : (0 : ℝ) < ((2 * n + 1 : ℕ) : ℝ) := by positivity
  have hP : (0 : ℝ) < ((2 * n + 2 : ℕ) : ℝ) := by positivity
  have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hQN : (n : ℝ) + 1 ≤ ((2 * n + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hPQ : ((2 * n + 1 : ℕ) : ℝ) ≤ ((2 * n + 2 : ℕ) : ℝ) := by push_cast; linarith
  have hs := sdb_sqrt_le (le_of_lt hσ) (le_of_lt hδ)
  have hs0 : 0 ≤ Real.sqrt (2 * δ * σ) := Real.sqrt_nonneg _
  have hnum : |((2 * n + 1 : ℕ) : ℝ) * deriv A α + ((2 * n + 2 : ℕ) : ℝ) * r α * deriv B α|
      ≤ (((2 * n + 1 : ℕ) : ℝ) + ((2 * n + 2 : ℕ) : ℝ) * r α) * Real.sqrt (2 * δ * σ) := by
    have h1 : |deriv A α| ≤ Real.sqrt (2 * δ * σ) := hA1
    have h2 : |deriv B α| ≤ Real.sqrt (2 * δ * σ) := hB1
    have hQnn : (0 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := le_of_lt hQ
    have hPrnn : (0 : ℝ) ≤ ((2 * n + 2 : ℕ) : ℝ) * r α := by positivity
    rw [abs_le] at h1 h2
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · have ha := mul_le_mul_of_nonneg_left h1.1 hQnn
      have hb := mul_le_mul_of_nonneg_left h2.1 hPrnn
      nlinarith only [ha, hb]
    · have ha := mul_le_mul_of_nonneg_left h1.2 hQnn
      have hb := mul_le_mul_of_nonneg_left h2.2 hPrnn
      nlinarith only [ha, hb]
  have hkey : (((2 * n + 1 : ℕ) : ℝ) + ((2 * n + 2 : ℕ) : ℝ) * r α)
      ≤ (198 / 125) * (((2 * n + 2 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α)) := by
    have hX0 : (0 : ℝ) ≤ R α ^ (2 * n) := by linarith
    have hXY : ((5 : ℝ) / 6) * (5 / 3) ≤ R α ^ (2 * n) * (R α + r α) :=
      mul_le_mul hb3 he (by norm_num) hX0
    have hPr : ((2 * n + 2 : ℕ) : ℝ) * r α ≤ ((2 * n + 2 : ℕ) : ℝ) * (6 / 5) :=
      mul_le_mul_of_nonneg_left hc2 (le_of_lt hP)
    nlinarith only [hXY, hPr, hPQ, hP]
  have hden : 0 < ((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α) := by
    positivity
  have hbound : |deriv R α| ≤ (198 / 125) * Real.sqrt (2 * δ * σ) / ((2 * n + 1 : ℕ) : ℝ) := by
    rw [hform, abs_div, abs_of_pos hden, div_le_div_iff₀ hden hQ]
    calc |((2 * n + 1 : ℕ) : ℝ) * deriv A α + ((2 * n + 2 : ℕ) : ℝ) * r α * deriv B α|
          * ((2 * n + 1 : ℕ) : ℝ)
        ≤ ((((2 * n + 1 : ℕ) : ℝ) + ((2 * n + 2 : ℕ) : ℝ) * r α) * Real.sqrt (2 * δ * σ))
          * ((2 * n + 1 : ℕ) : ℝ) := mul_le_mul_of_nonneg_right hnum (le_of_lt hQ)
      _ ≤ (((198 / 125) * (((2 * n + 2 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α))) * Real.sqrt (2 * δ * σ))
          * ((2 * n + 1 : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hkey hs0) (le_of_lt hQ)
      _ = (198 / 125) * Real.sqrt (2 * δ * σ)
          * (((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α)) := by ring
  constructor
  · have hstep1 : Real.sqrt (2 * δ * σ) * ((n : ℝ) + 1) ≤ (3 / 4 * (σ + δ)) * ((2 * n + 1 : ℕ) : ℝ) :=
      mul_le_mul hs hQN (le_of_lt hN) (by positivity)
    have hstep2 : (198 / 125) * (Real.sqrt (2 * δ * σ) * ((n : ℝ) + 1))
        ≤ (198 / 125) * ((3 / 4 * (σ + δ)) * ((2 * n + 1 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hstep1 (by norm_num)
    have hnn : (0 : ℝ) ≤ (σ + δ) * ((2 * n + 1 : ℕ) : ℝ) := by positivity
    have hfin : (198 / 125) * Real.sqrt (2 * δ * σ) / ((2 * n + 1 : ℕ) : ℝ)
        ≤ 3 * (σ + δ) / ((n : ℝ) + 1) := by
      rw [div_le_div_iff₀ hQ hN]
      linarith [hstep2, hnn]
    linarith [hbound, hfin]
  · have hsq1 : (deriv R α) ^ 2 ≤ ((198 / 125) * Real.sqrt (2 * δ * σ) / ((2 * n + 1 : ℕ) : ℝ)) ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg (deriv R α)) hbound 2
      rwa [sq_abs] at this
    have hsq2 : ((198 / 125) * Real.sqrt (2 * δ * σ) / ((2 * n + 1 : ℕ) : ℝ)) ^ 2
        = (198 / 125) ^ 2 * (2 * δ * σ) / (((2 * n + 1 : ℕ) : ℝ)) ^ 2 := by
      rw [div_pow, mul_pow, Real.sq_sqrt (by positivity)]
    rw [hsq2] at hsq1
    have hc : (198 / 125) ^ 2 * (2 * δ * σ) / (((2 * n + 1 : ℕ) : ℝ)) ^ 2
        ≤ (26 / 5) * (δ * σ) / (((2 * n + 1 : ℕ) : ℝ)) ^ 2 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith only [hδ, hσ]
    linarith [hsq1, hc]

/-! ## The second-order formula bound -/

/-- Sharp bound for `R''` given the explicit formula of `sol_deriv2_R_formula_aux`. -/
lemma deriv_two_bound_of_formula (n : ℕ) (hn : 1 ≤ n) {R r A B : ℝ → ℝ} {σ δ α : ℝ}
    (hσ : 0 < σ) (hσ8 : σ ≤ 1 / 8) (hδ : 0 < δ)
    (hbox : SharpBox n (R α) (r α))
    (hRsq : (deriv R α) ^ 2 ≤ (26 / 5) * (δ * σ) / (((2 * n + 1 : ℕ) : ℝ)) ^ 2)
    (hrsq : (deriv r α) ^ 2 ≤ (26 / 5) * (δ * σ) / (((2 * n + 1 : ℕ) : ℝ)) ^ 2)
    (hA2 : |deriv (deriv A) α| ≤ δ) (hB2 : |deriv (deriv B) α| ≤ δ)
    (hform : deriv (deriv R) α =
      deriv (deriv A) α / (↑(2 * n + 2) * R α ^ (2 * n) * (R α + r α)) +
            r α * deriv (deriv B) α / (↑(2 * n + 1) * R α ^ (2 * n) * (R α + r α)) -
          deriv R α ^ 2 * (↑(2 * n + 2) - 1 - r α / (R α + r α)) / R α -
        (r α / R α) ^ (2 * n) * deriv r α ^ 2 / (R α + r α)) :
    |deriv (deriv R) α| ≤ 3 * (σ + δ) / ((n : ℝ) + 1) := by
  set N : ℝ := (n : ℝ) + 1 with hNdef
  set tA : ℝ := deriv (deriv A) α / (↑(2 * n + 2) * R α ^ (2 * n) * (R α + r α)) with htA
  set tB : ℝ := r α * deriv (deriv B) α / (↑(2 * n + 1) * R α ^ (2 * n) * (R α + r α)) with htB
  set tC : ℝ := deriv R α ^ 2 * (↑(2 * n + 2) - 1 - r α / (R α + r α)) / R α with htC
  set tD : ℝ := (r α / R α) ^ (2 * n) * deriv r α ^ 2 / (R α + r α) with htD
  have hNpos : 0 < N := by rw [hNdef]; positivity
  have hT1 : |tA| ≤ 9 * δ / (25 * N) := by rw [htA, hNdef]; exact sdb_term1 n hδ hbox hA2
  have hT2 : |tB| ≤ 108 * δ / (125 * N) := by rw [htB, hNdef]; exact sdb_term2 n hδ hbox hB2
  have hT3 : |tC| ≤ 39 * δ / (50 * N) := by rw [htC, hNdef]; exact sdb_term3 n hσ8 hδ hbox hRsq
  have hT4 : |tD| ≤ 117 * δ / (200 * N) := by rw [htD, hNdef]; exact sdb_term4 n hσ8 hδ hbox hrsq
  have htri : |tA + tB - tC - tD| ≤ |tA| + |tB| + |tC| + |tD| := by
    have h := abs_sub (tA + tB) (tC + tD)
    have h1 := abs_add_le tA tB
    have h2 := abs_add_le tC tD
    calc |tA + tB - tC - tD| = |(tA + tB) - (tC + tD)| := by ring_nf
      _ ≤ |tA + tB| + |tC + tD| := h
      _ ≤ (|tA| + |tB|) + (|tC| + |tD|) := add_le_add h1 h2
      _ = |tA| + |tB| + |tC| + |tD| := by ring
  have hsum : 9 * δ / (25 * N) + 108 * δ / (125 * N) + 39 * δ / (50 * N) + 117 * δ / (200 * N)
      ≤ 3 * (σ + δ) / N := by
    have h1 : 9 * δ / (25 * N) + 108 * δ / (125 * N) + 39 * δ / (50 * N) + 117 * δ / (200 * N)
        = (2589 / 1000) * (δ / N) := by
      field_simp
      ring
    rw [h1, show (2589 / 1000) * (δ / N) = (2589 / 1000) * δ / N from by ring,
      div_le_div_iff₀ hNpos hNpos]
    nlinarith only [hσ, hδ, hNpos]
  have hmain : |deriv (deriv R) α|
      ≤ 9 * δ / (25 * N) + 108 * δ / (125 * N) + 39 * δ / (50 * N) + 117 * δ / (200 * N) := by
    rw [hform]
    linarith [htri, hT1, hT2, hT3, hT4]
  linarith [hmain, hsum]

/-! ## The generic sharp bounds and the target -/

/-- The sharp first- and second-derivative bounds for a pair `(R,r)` solving the normalised
two-power system with data bounds `|A| ≤ σ`, `|A'| ≤ √(2δσ)`, `|A''| ≤ δ`. -/
theorem sol_deriv_bounds_sharp_core (n : ℕ) (hn : 1 ≤ n) {A B R r : ℝ → ℝ} {σ δ α : ℝ}
    (hσ : 0 < σ) (hσ8 : σ ≤ 1 / 8) (hδ : 0 < δ)
    (hRc : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) R α)
    (hrc : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) r α)
    (hAcd : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) A α)
    (hBcd : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) B α)
    (hRpos : 0 < R α) (hrpos : 0 < r α)
    (hsys : ∀ᶠ β in nhds α, R β ^ (2 * n + 2) + r β ^ (2 * n + 2) = 2 + A β ∧
      R β ^ (2 * n + 1) - r β ^ (2 * n + 1) = B β)
    (hbox : SharpBox n (R α) (r α))
    (hA1 : |deriv A α| ≤ Real.sqrt (2 * δ * σ)) (hB1 : |deriv B α| ≤ Real.sqrt (2 * δ * σ))
    (hA2 : |deriv (deriv A) α| ≤ δ) (hB2 : |deriv (deriv B) α| ≤ δ) :
    |deriv R α| ≤ 3 * (σ + δ) / ((n : ℝ) + 1) ∧
    |deriv r α| ≤ 3 * (σ + δ) / ((n : ℝ) + 1) ∧
    |deriv (deriv R) α| ≤ 3 * (σ + δ) / ((n : ℝ) + 1) ∧
    |deriv (deriv r) α| ≤ 3 * (σ + δ) / ((n : ℝ) + 1) := by
  obtain ⟨hR'⟩ := sol_deriv_formulas n hRc hrc hAcd hBcd hRpos hrpos hsys
  obtain ⟨-, hr'⟩ := sol_deriv_formulas n hRc hrc hAcd hBcd hRpos hrpos hsys
  -- the system with the two radial functions exchanged and `B` negated
  have hsys_sw : ∀ᶠ β in nhds α, r β ^ (2 * n + 2) + R β ^ (2 * n + 2) = 2 + A β ∧
      r β ^ (2 * n + 1) - R β ^ (2 * n + 1) = (fun y => -B y) β := by
    filter_upwards [hsys] with β hβ
    exact ⟨by linarith [hβ.1], by linarith [hβ.2]⟩
  have hB1' : |deriv (fun y => -B y) α| ≤ Real.sqrt (2 * δ * σ) := by
    rw [sdb_deriv_neg_fun B]
    simpa using hB1
  have hB2' : |deriv (deriv (fun y => -B y)) α| ≤ δ := by
    rw [show deriv (fun y : ℝ => -B y) = fun y : ℝ => -deriv B y from sdb_deriv_neg_fun B,
      show deriv (fun y : ℝ => -deriv B y) = fun y : ℝ => -deriv (deriv B) y from
        sdb_deriv_neg_fun (deriv B)]
    simpa using hB2
  -- first derivatives
  have hR1 := deriv_one_bound_of_formula n hn hσ hσ8 hδ hRpos hrpos hbox hA1 hB1 hR'
  have hform_r : deriv r α = (((2 * n + 1 : ℕ) : ℝ) * deriv A α +
        ((2 * n + 2 : ℕ) : ℝ) * R α * deriv (fun y => -B y) α)
      / (((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) * r α ^ (2 * n) * (r α + R α)) := by
    rw [hr', sdb_deriv_neg_fun B]
    congr 1 <;> ring
  have hr1 := deriv_one_bound_of_formula n hn hσ hσ8 hδ hrpos hRpos (sharpBox_swap hbox)
    hA1 hB1' hform_r
  -- second derivatives
  have hformR := sol_deriv2_R_formula_aux n hn hRc hrc hAcd hBcd hRpos hrpos hsys
  have hformr := sol_deriv2_R_formula_aux n hn hrc hRc hAcd hBcd.neg hrpos hRpos hsys_sw
  exact ⟨hR1.1, hr1.1,
    deriv_two_bound_of_formula n hn hσ hσ8 hδ hbox hR1.2 hr1.2 hA2 hB2 hformR,
    deriv_two_bound_of_formula n hn hσ hσ8 hδ (sharpBox_swap hbox) hr1.2 hR1.2 hA2 hB2' hformr⟩

theorem sol_deriv_bounds_sharp (n : ℕ) (hn : 1 ≤ n) {A B : ℝ → ℝ} {σ δ α : ℝ}
    (hσ : 0 < σ) (hσ8 : σ ≤ 1 / 8) (hδ : 0 < δ)
    (hAc : ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) A (Set.Ioo (-1) (Real.pi / 2 + 1)))
    (hBc : ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) B (Set.Ioo (-1) (Real.pi / 2 + 1)))
    (hAval : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |A β| ≤ σ)
    (hBval : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |B β| ≤ σ)
    (hA1 : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |deriv A β| ≤ Real.sqrt (2 * δ * (σ - |A β|)))
    (hB1 : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |deriv B β| ≤ Real.sqrt (2 * δ * (σ - |B β|)))
    (hA2 : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |deriv (deriv A) β| ≤ δ)
    (hB2 : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |deriv (deriv B) β| ≤ δ)
    (hbox : SharpBox n (solR n A B α) (solr n A B α))
    (hα : α ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    |deriv (solR n A B) α| ≤ 3 * (σ + δ) / ((n : ℝ) + 1) ∧
    |deriv (solr n A B) α| ≤ 3 * (σ + δ) / ((n : ℝ) + 1) ∧
    |deriv (deriv (solR n A B)) α| ≤ 3 * (σ + δ) / ((n : ℝ) + 1) ∧
    |deriv (deriv (solr n A B)) α| ≤ 3 * (σ + δ) / ((n : ℝ) + 1) := by
  have hσ' : σ ≤ 1 / 2 := by linarith
  have hRpos : 0 < solR n A B α := by linarith [hbox.1]
  have hrpos : 0 < solr n A B α := by linarith [hbox.2.2.2.2.2.2.1]
  have hAcd : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) A α :=
    hAc.contDiffAt (Ioo_mem_nhds (by linarith [hα.1]) (by linarith [hα.2, Real.pi_pos]))
  have hBcd : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) B α :=
    hBc.contDiffAt (Ioo_mem_nhds (by linarith [hα.1]) (by linarith [hα.2, Real.pi_pos]))
  have hA1' : |deriv A α| ≤ Real.sqrt (2 * δ * σ) :=
    le_trans (hA1 α hα) (Real.sqrt_le_sqrt (by nlinarith [abs_nonneg (A α), hδ.le]))
  have hB1' : |deriv B α| ≤ Real.sqrt (2 * δ * σ) :=
    le_trans (hB1 α hα) (Real.sqrt_le_sqrt (by nlinarith [abs_nonneg (B α), hδ.le]))
  exact sol_deriv_bounds_sharp_core n hn hσ hσ8 hδ
    (solR_contDiffAt n hn hσ' hAc hBc hAval hBval hα)
    (solr_contDiffAt n hn hσ' hAc hBc hAval hBval hα)
    hAcd hBcd hRpos hrpos
    (sol_system_eventually n hn hσ' hAc hBc hAval hBval hα)
    hbox hA1' hB1' (hA2 α hα) (hB2 α hα)

end Work.OddCurve.LowSlope
