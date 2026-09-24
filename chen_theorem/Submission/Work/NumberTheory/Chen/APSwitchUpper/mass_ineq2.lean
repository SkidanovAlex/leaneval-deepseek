/-
# `APSwitchUpper.mass_ineq2` — the mass inequality for two consecutive delay levels

The level constants `Cv n = ∫_2^{2n+4} oddSum n` and `Tv n = ∫_3^{2n+3} evenSum n` of the
Rosser–Iwaniec delay calculus (`APSwitchUpper.riPhiLevelCore`) satisfy the *mass identity*
(`riPhiLevelCore.mass_identity`)

  `Tv (n+2) = ∫_2^{2n+6} oddSum (n+1) u · log ((u+1)/3) du`,

and on `[2,4]` the odd level has the closed form (`riPhiLevelCore.oddSum_formula`)

  `u · oddSum (n+1) u = (3 + Cv n)·log (3/(u-1)) − 4 + u + Tv (n+1)`.

The present file proves

  `(3+Cv n)·A + Tv(n+1)·B + Cc + (49/96)·(Cv (n+1) − (3+Cv n)·D − (Tv(n+1)−4)·log 2 − 2) ≤ Tv (n+2)`

with the explicit constants

  `A  = ∫_2^4 L1lo·L2lo/u`,  `B = ∫_2^4 L2lo/u`,  `Cc = ∫_2^4 (u−4)·L2lo/u`,
  `D  = ∫_2^4 L1up/u`,

where `L1lo`, `L2lo` are the two-term truncations of the odd series of
`log (3/(u−1))`, `log ((u+1)/3)` and `L1up = L1lo + (2/5) x^5/(1−x^2)` is the
geometric majorant of `log (3/(u−1))` (all already computed in the sibling modules
`integral_L1lo`, `integral_L2lo`, `integral_L1lo_mul_L2lo`, `integral_L2lo_mul_u4`,
`integral_L1up_tail`).

## The route

Write `α = 3 + Cv n`, `β = Tv (n+1)`, `c = 49/96`, `f u = oddSum (n+1) u`, and put
`log1 u = log (3/(u−1))`, `log2 u = log ((u+1)/3)`.

1. `Tv (n+2) = ∫_2^{2n+6} f·log2 = ∫_2^4 f·log2 + ∫_4^{2n+6} f·log2`.
2. On `[2,4]` the pointwise bound `f u·log2 u ≥ (α·L1lo·L2lo + β·L2lo + (u−4)·L2lo)/u` is
   proved from `L1lo ≤ log1`, `L2lo ≤ log2`, `3·L1lo ≥ 4 − u` (all pointwise), `α ≥ 3`,
   `β ≥ 0`; integrating gives
   `∫_2^4 f·log2 ≥ α·A + β·B + Cc`.
3. On `[4, 2n+6]` one has `log2 ≥ log (5/3) ≥ 49/96 = c`, so
   `∫_4^{2n+6} f·log2 ≥ c·∫_4^{2n+6} f = c·(Cv (n+1) − ∫_2^4 f)`, and by
   `integral_oddSum_Icc`, `∫_2^4 f = α·Aprime 4 + (β−4)·log 2 + 2`.
4. Since `Aprime 4 = ∫_2^4 log1/u ≤ ∫_2^4 L1up/u = D`, the resulting lower bound
   `α·A + β·B + Cc + c·(Cv(n+1) − α·D − (β−4)·log2 − 2)` is exactly the left-hand side.

The whole numerical content sits in the *pointwise* inequalities; the constants `49/96` and
the `(u−4)` factor are matched so that `3·(∫_2^4 log1·log2/u − A) ≥ Cc − ∫_2^4 (u−4)·log2/u`.
-/
import Mathlib
import Submission.Work.NumberTheory.Chen.APSwitchUpper.riPhiLevelCore
import Submission.Work.NumberTheory.Chen.APSwitchUpper.oddSum_formula
import Submission.Work.NumberTheory.Chen.APSwitchUpper.integral_oddSum_Icc
import Submission.Work.NumberTheory.Chen.APSwitchUpper.mass_identity

namespace Work.NumberTheory.Chen.APSwitchUpper

open MeasureTheory intervalIntegral

noncomputable section

/-! ## The two truncations and the geometric tail -/

/-- The first (lower) truncation `2x + (2/3)x³`, `x = (4−u)/(u+2)`, for `log (3/(u−1))`. -/
abbrev chenL1 (u : ℝ) : ℝ := 2 * ((4 - u) / (u + 2)) + (2 / 3 : ℝ) * ((4 - u) / (u + 2)) ^ 3

/-- The second (lower) truncation `2y + (2/3)y³`, `y = (u−2)/(u+4)`, for `log ((u+1)/3)`. -/
abbrev chenL2 (u : ℝ) : ℝ := 2 * ((u - 2) / (u + 4)) + (2 / 3 : ℝ) * ((u - 2) / (u + 4)) ^ 3

/-- The geometric majorant `(2/5)x^5/(1−x²)` of the tail of the first series. -/
abbrev chenTail (u : ℝ) : ℝ :=
  (2 / 5 : ℝ) * ((4 - u) / (u + 2)) ^ 5 / (1 - ((4 - u) / (u + 2)) ^ 2)

/-! ## Continuity of the elementary profiles -/

lemma contOn_chenL1 (a b : ℝ) (ha : -2 < a) : ContinuousOn chenL1 (Set.Icc a b) := by
  unfold chenL1
  have h : ContinuousOn (fun u : ℝ => (4 - u) / (u + 2)) (Set.Icc a b) :=
    ContinuousOn.div (continuousOn_const.sub continuousOn_id)
      (continuousOn_id.add continuousOn_const) (fun x hx => by linarith [hx.1])
  exact (h.const_mul 2).add ((h.pow 3).const_mul (2 / 3))

lemma contOn_chenL2 (a b : ℝ) (ha : -4 < a) : ContinuousOn chenL2 (Set.Icc a b) := by
  unfold chenL2
  have h : ContinuousOn (fun u : ℝ => (u - 2) / (u + 4)) (Set.Icc a b) :=
    ContinuousOn.div (continuousOn_id.sub continuousOn_const)
      (continuousOn_id.add continuousOn_const) (fun x hx => by linarith [hx.1])
  exact (h.const_mul 2).add ((h.pow 3).const_mul (2 / 3))

lemma contOn_log_u1_div3 (a b : ℝ) (ha : -1 < a) :
    ContinuousOn (fun u : ℝ => Real.log ((u + 1) / 3)) (Set.Icc a b) := by
  refine ContinuousOn.log
    (ContinuousOn.div (continuousOn_id.add continuousOn_const) continuousOn_const ?_) ?_
  · intro x hx; norm_num
  · intro x hx; exact ne_of_gt (div_pos (by linarith [hx.1]) (by norm_num))

lemma contOn_log_three_div (a b : ℝ) (ha : 1 < a) :
    ContinuousOn (fun u : ℝ => Real.log (3 / (u - 1))) (Set.Icc a b) := by
  refine ContinuousOn.log
    (ContinuousOn.div continuousOn_const (continuousOn_id.sub continuousOn_const) ?_) ?_
  · intro x hx; linarith [hx.1]
  · intro x hx; exact ne_of_gt (div_pos (by norm_num) (by linarith [hx.1]))

lemma contOn_chenTail : ContinuousOn chenTail (Set.Icc (2 : ℝ) 4) := by
  unfold chenTail
  have h : ContinuousOn (fun u : ℝ => (4 - u) / (u + 2)) (Set.Icc (2 : ℝ) 4) :=
    ContinuousOn.div (continuousOn_const.sub continuousOn_id)
      (continuousOn_id.add continuousOn_const) (fun x hx => by linarith [hx.1])
  refine ContinuousOn.div ((h.pow 5).const_mul (2 / 5))
    (continuousOn_const.sub (h.pow 2)) ?_
  intro x hx
  have hx1 : (2 : ℝ) ≤ x := hx.1
  have hx4 : x ≤ 4 := hx.2
  have hx2 : (0 : ℝ) < x + 2 := by linarith
  have hs0 : 0 ≤ (4 - x) / (x + 2) := div_nonneg (by linarith) (by linarith)
  have hs1 : (4 - x) / (x + 2) < 1 := by
    rw [div_lt_one hx2]; linarith
  have hsq : ((4 - x) / (x + 2)) ^ 2 < 1 := by nlinarith
  intro hzero
  nlinarith [hsq, hzero]

/-! ## Integrability of the profile quotients on `[2,4]` -/

lemma integrable_chenL1_div : IntervalIntegrable (fun u : ℝ => chenL1 u / u) volume (2 : ℝ) 4 := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 4)]
  exact (contOn_chenL1 2 4 (by norm_num)).div continuousOn_id
    (fun x hx => by linarith [hx.1])

lemma integrable_chenTail_div : IntervalIntegrable (fun u : ℝ => chenTail u / u) volume (2 : ℝ) 4 := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 4)]
  exact contOn_chenTail.div continuousOn_id (fun x hx => by linarith [hx.1])

lemma integrable_chenL2_div : IntervalIntegrable (fun u : ℝ => chenL2 u / u) volume (2 : ℝ) 4 := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 4)]
  exact (contOn_chenL2 2 4 (by norm_num)).div continuousOn_id
    (fun x hx => by linarith [hx.1])

lemma integrable_chenL1L2_div :
    IntervalIntegrable (fun u : ℝ => chenL1 u * chenL2 u / u) volume (2 : ℝ) 4 := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 4)]
  exact ((contOn_chenL1 2 4 (by norm_num)).mul (contOn_chenL2 2 4 (by norm_num))).div
    continuousOn_id (fun x hx => by linarith [hx.1])

lemma integrable_chenL2_u4_div :
    IntervalIntegrable (fun u : ℝ => (u - 4) * chenL2 u / u) volume (2 : ℝ) 4 := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 4)]
  exact ((continuousOn_id.sub continuousOn_const).mul (contOn_chenL2 2 4 (by norm_num))).div
    continuousOn_id (fun x hx => by linarith [hx.1])

lemma integrable_oddSum_log2 (n : ℕ) (a b : ℝ) (h : ∀ x ∈ Set.uIcc a b, -1 < x) :
    IntervalIntegrable (fun u : ℝ => oddSum (n + 1) u * Real.log ((u + 1) / 3)) volume a b := by
  have hcont : ContinuousOn (fun u : ℝ => Real.log ((u + 1) / 3)) (Set.uIcc a b) := by
    refine ContinuousOn.log
      (ContinuousOn.div (continuousOn_id.add continuousOn_const) continuousOn_const ?_) ?_
    · intro x _; norm_num
    · intro x hx; exact ne_of_gt (div_pos (by linarith [h x hx]) (by norm_num))
  exact ((oddSum_intervalIntegrable (n + 1) a b).continuousOn_mul hcont).congr
    (fun x _ => by ring)

/-! ## The elementary pointwise facts -/

lemma three_mul_chenL1_ge (u : ℝ) (h2 : 2 ≤ u) (h4 : u ≤ 4) :
    4 - u ≤ 3 * chenL1 u := by
  have key : 3 * chenL1 u - (4 - u)
      = (4 - u) ^ 2 * (u ^ 2 + 2 * u + 12) / (u + 2) ^ 3 := by
    unfold chenL1
    field_simp
    ring
  have hpos : 0 ≤ (4 - u) ^ 2 * (u ^ 2 + 2 * u + 12) / (u + 2) ^ 3 := by
    apply div_nonneg
    · exact mul_nonneg (sq_nonneg _) (by nlinarith)
    · positivity
  linarith [key ▸ hpos]

lemma chenL1_nonneg (u : ℝ) (h2 : 2 ≤ u) (h4 : u ≤ 4) : 0 ≤ chenL1 u := by
  unfold chenL1
  have : (0 : ℝ) ≤ (4 - u) / (u + 2) := div_nonneg (by linarith) (by linarith)
  positivity

lemma chenL2_nonneg (u : ℝ) (h2 : 2 ≤ u) (h4 : u ≤ 4) : 0 ≤ chenL2 u := by
  unfold chenL2
  have : (0 : ℝ) ≤ (u - 2) / (u + 4) := div_nonneg (by linarith) (by linarith)
  positivity

/-- The geometric majorant `L1up = L1lo + chenTail` dominates `log (3/(u−1))` on `[2,4]`. -/
lemma log_three_div_le_L1up (u : ℝ) (h2 : 2 ≤ u) (h4 : u ≤ 4) :
    Real.log (3 / (u - 1)) ≤ chenL1 u + chenTail u := by
  simpa only [chenL1, chenTail] using logPad2_L1_upper u h2 h4

/-! ## `Aprime 4 ≤ D`, `D = ∫_2^4 L1up/u` -/

/-- **Upper bound for `Aprime 4`.**  The truncated series plus its geometric tail dominates
`log (3/(u−1))` on `[2,4]`, and the two pieces integrate to
`-5/4 + (64/3) log 2 - 12 log 3` and `41/60 + (51/10) log 3 - (136/15) log 2`. -/
lemma Aprime_four_le_D :
    Aprime 4
      ≤ -17 / 30 + (184 / 15 : ℝ) * Real.log 2 - (69 / 10 : ℝ) * Real.log 3 := by
  rw [Aprime]
  have hI1 : IntervalIntegrable (fun u : ℝ => Real.log (3 / (u - 1)) / u) volume (2 : ℝ) 4 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 4)]
    exact (contOn_log_three_div 2 4 (by norm_num)).div continuousOn_id
      (fun x hx => by linarith [hx.1])
  have hI2 : IntervalIntegrable (fun u : ℝ => (chenL1 u + chenTail u) / u) volume (2 : ℝ) 4 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 4)]
    refine ((contOn_chenL1 2 4 (by norm_num)).add contOn_chenTail).div continuousOn_id ?_
    intro x hx; linarith [hx.1]
  have hpt : ∀ u ∈ Set.Icc (2 : ℝ) 4,
      Real.log (3 / (u - 1)) / u ≤ (chenL1 u + chenTail u) / u := by
    intro u hu
    refine div_le_div_of_nonneg_right (log_three_div_le_L1up u hu.1 hu.2) ?_
    linarith [hu.1]
  have hmono := intervalIntegral.integral_mono_on (by norm_num) hI1 hI2 hpt
  have hsplit : (∫ u in (2 : ℝ)..4, (chenL1 u + chenTail u) / u)
      = (∫ u in (2 : ℝ)..4, chenL1 u / u) + ∫ u in (2 : ℝ)..4, chenTail u / u := by
    rw [show (fun u : ℝ => (chenL1 u + chenTail u) / u)
        = fun u : ℝ => chenL1 u / u + chenTail u / u from by funext u; ring]
    exact intervalIntegral.integral_add integrable_chenL1_div integrable_chenTail_div
  have hL1 : (∫ u in (2 : ℝ)..4, chenL1 u / u)
      = -5 / 4 + (64 / 3 : ℝ) * Real.log 2 - 12 * Real.log 3 := by
    simp only [chenL1]
    exact integral_L1lo
  have hL2 : (∫ u in (2 : ℝ)..4, chenTail u / u)
      = 41 / 60 + (51 / 10 : ℝ) * Real.log 3 - (136 / 15 : ℝ) * Real.log 2 := by
    simp only [chenTail]
    exact integral_L1up_tail
  linarith [hmono, hsplit, hL1, hL2]

/-! ## `49/96 ≤ log (5/3)` -/

lemma c_le_log_five_thirds : (49 / 96 : ℝ) ≤ Real.log (5 / 3) := by
  have h := logPad2_L2_lower 4 (by norm_num) (by norm_num)
  have h' : chenL2 (4 : ℝ) ≤ Real.log (((4 : ℝ) + 1) / 3) := by simpa only [chenL2] using h
  have hL : chenL2 (4 : ℝ) = 49 / 96 := by simp only [chenL2]; norm_num
  rw [hL] at h'
  have harg : (((4 : ℝ) + 1) / 3) = 5 / 3 := by norm_num
  rwa [harg] at h'

/-! ## The pointwise mass bound on `[2,4]` -/

lemma mass_pt (n : ℕ) : ∀ u ∈ Set.Icc (2 : ℝ) 4,
      ((3 + Cv n) * (chenL1 u * chenL2 u) + Tv (n + 1) * chenL2 u
          + (u - 4) * chenL2 u) / u
        ≤ oddSum (n + 1) u * Real.log ((u + 1) / 3) := by
  intro u hu
  have hu2 : (2 : ℝ) ≤ u := hu.1
  have hu4 : u ≤ 4 := hu.2
  have hu0 : (0 : ℝ) < u := by linarith
  set H := Real.log (3 / (u - 1)) with hHdef
  set G := Real.log ((u + 1) / 3) with hGdef
  set L1 := chenL1 u with hL1def
  set L2 := chenL2 u with hL2def
  have hHge : L1 ≤ H := by
    rw [hHdef, hL1def]; exact logPad2_L1_lower u hu2 hu4
  have hGge : L2 ≤ G := by
    rw [hGdef, hL2def]; exact logPad2_L2_lower u hu2 hu4
  have hL1nn : 0 ≤ L1 := by rw [hL1def]; exact chenL1_nonneg u hu2 hu4
  have hL2nn : 0 ≤ L2 := by rw [hL2def]; exact chenL2_nonneg u hu2 hu4
  have hGnn : 0 ≤ G := by
    rw [hGdef]
    apply Real.log_nonneg
    linarith
  have h3L1 : 4 - u ≤ 3 * L1 := by rw [hL1def]; exact three_mul_chenL1_ge u hu2 hu4
  have hform := oddSum_formula n hu2 hu4
  have hodd : oddSum (n + 1) u = ((3 + Cv n) * H - 4 + u + Tv (n + 1)) / u := by
    rw [eq_div_iff (ne_of_gt hu0), mul_comm, hHdef]
    linarith
  rw [hodd]
  have hα : (0 : ℝ) ≤ 3 + Cv n := by linarith [Cv_nonneg n]
  have hCv : (0 : ℝ) ≤ Cv n := Cv_nonneg n
  have hβ : (0 : ℝ) ≤ Tv (n + 1) := Tv_nonneg (n + 1)
  have hGN : 0 ≤ G - L2 := by linarith
  have hHL : L1 * (G - L2) ≤ H * G - L1 * L2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hHge) hGnn]
  have hξ : (4 - u) ≤ (3 + Cv n) * L1 := by nlinarith [h3L1, hL1nn, hCv]
  have k1 : (4 - u) * (G - L2) ≤ (3 + Cv n) * (L1 * (G - L2)) := by
    have := mul_le_mul_of_nonneg_right hξ hGN
    linarith [this]
  have k2 : (3 + Cv n) * (L1 * (G - L2)) ≤ (3 + Cv n) * (H * G - L1 * L2) :=
    mul_le_mul_of_nonneg_left hHL hα
  have k3 : 0 ≤ Tv (n + 1) * (G - L2) := mul_nonneg hβ hGN
  have hnum : (3 + Cv n) * (L1 * L2) + Tv (n + 1) * L2 + (u - 4) * L2
      ≤ ((3 + Cv n) * H - 4 + u + Tv (n + 1)) * G := by nlinarith [k1, k2, k3]
  rw [show (((3 + Cv n) * H - 4 + u + Tv (n + 1)) / u) * G
        = (((3 + Cv n) * H - 4 + u + Tv (n + 1)) * G) / u from by ring]
  exact div_le_div_of_nonneg_right hnum hu0.le

/-! ## The integral identity and the key inequality -/

lemma mass_int_split (n : ℕ) :
    (∫ u in (2 : ℝ)..4,
        ((3 + Cv n) * (chenL1 u * chenL2 u) + Tv (n + 1) * chenL2 u
          + (u - 4) * chenL2 u) / u)
      = (3 + Cv n) * (∫ u in (2 : ℝ)..4, chenL1 u * chenL2 u / u)
        + Tv (n + 1) * (∫ u in (2 : ℝ)..4, chenL2 u / u)
        + (∫ u in (2 : ℝ)..4, (u - 4) * chenL2 u / u) := by
  have e1 : (∫ u in (2 : ℝ)..4,
        ((3 + Cv n) * (chenL1 u * chenL2 u) + Tv (n + 1) * chenL2 u
          + (u - 4) * chenL2 u) / u)
      = ∫ u in (2 : ℝ)..4,
          (((3 + Cv n) * (chenL1 u * chenL2 u / u) + Tv (n + 1) * (chenL2 u / u))
            + (u - 4) * chenL2 u / u) := by
    apply intervalIntegral.integral_congr
    intro u _
    ring
  rw [e1,
    intervalIntegral.integral_add
      ((integrable_chenL1L2_div.const_mul _).add (integrable_chenL2_div.const_mul _))
      integrable_chenL2_u4_div,
    intervalIntegral.integral_add (integrable_chenL1L2_div.const_mul _)
      (integrable_chenL2_div.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

/-- **The key integral inequality.**  The integral of the first odd level on `[2,4]` against
`log ((u+1)/3)` dominates the three explicit constants. -/
lemma mass_key (n : ℕ) :
    (3 + Cv n) * (-1763 / 12 - (35137 / 9 : ℝ) * Real.log 2 + 2597 * Real.log 3)
      + Tv (n + 1) * (-5 / 32 + (77 / 12 : ℝ) * Real.log 2 - (15 / 4 : ℝ) * Real.log 3)
      + (97 / 12 - (221 / 3 : ℝ) * Real.log 2 + 39 * Real.log 3)
      ≤ ∫ u in (2 : ℝ)..4, oddSum (n + 1) u * Real.log ((u + 1) / 3) := by
  have hI1 : IntervalIntegrable
      (fun u : ℝ => ((3 + Cv n) * (chenL1 u * chenL2 u) + Tv (n + 1) * chenL2 u
        + (u - 4) * chenL2 u) / u) volume (2 : ℝ) 4 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 4)]
    have hAB : ContinuousOn (fun u : ℝ =>
        (3 + Cv n) * (chenL1 u * chenL2 u) + Tv (n + 1) * chenL2 u) (Set.Icc (2 : ℝ) 4) :=
      (((contOn_chenL1 2 4 (by norm_num)).mul (contOn_chenL2 2 4 (by norm_num))).const_mul _).add
        ((contOn_chenL2 2 4 (by norm_num)).const_mul _)
    have h1 : ContinuousOn (fun u : ℝ =>
        (3 + Cv n) * (chenL1 u * chenL2 u) + Tv (n + 1) * chenL2 u
          + (u - 4) * chenL2 u) (Set.Icc (2 : ℝ) 4) :=
      hAB.add (((continuousOn_id.sub continuousOn_const).mul (contOn_chenL2 2 4 (by norm_num))))
    exact h1.div continuousOn_id (fun x hx => by linarith [hx.1])
  have hI2 := integrable_oddSum_log2 n 2 4
    (fun x hx => by rw [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 4)] at hx; linarith [hx.1])
  have hmono := intervalIntegral.integral_mono_on (by norm_num) hI1 hI2 (mass_pt n)
  have hsplit := mass_int_split n
  have h1 : (∫ u in (2 : ℝ)..4, chenL1 u * chenL2 u / u)
      = -1763 / 12 - (35137 / 9 : ℝ) * Real.log 2 + 2597 * Real.log 3 := by
    simp only [chenL1, chenL2]
    exact integral_L1lo_mul_L2lo
  have h2 : (∫ u in (2 : ℝ)..4, chenL2 u / u)
      = -5 / 32 + (77 / 12 : ℝ) * Real.log 2 - (15 / 4 : ℝ) * Real.log 3 := by
    simp only [chenL2]
    exact integral_L2lo
  have h3 : (∫ u in (2 : ℝ)..4, (u - 4) * chenL2 u / u)
      = 97 / 12 - (221 / 3 : ℝ) * Real.log 2 + 39 * Real.log 3 := by
    simp only [chenL2]
    exact integral_L2lo_mul_u4
  rw [h1, h2, h3] at hsplit
  linarith [hmono, hsplit]

/-! ## The target -/

theorem mass_ineq2 (n : ℕ) :
    (3 + Cv n) * (-1763 / 12 - (35137 / 9 : ℝ) * Real.log 2 + 2597 * Real.log 3)
      + Tv (n + 1) * (-5 / 32 + (77 / 12 : ℝ) * Real.log 2 - (15 / 4 : ℝ) * Real.log 3)
      + (97 / 12 - (221 / 3 : ℝ) * Real.log 2 + 39 * Real.log 3)
      + (49 / 96 : ℝ) * (Cv (n + 1)
          - (3 + Cv n) * (-17 / 30 + (184 / 15 : ℝ) * Real.log 2 - (69 / 10 : ℝ) * Real.log 3)
          - (Tv (n + 1) - 4) * Real.log 2 - 2)
    ≤ Tv (n + 2) := by
  have h4N : (4 : ℝ) ≤ ((2 * n + 6 : ℕ) : ℝ) := by
    have : 4 ≤ 2 * n + 6 := by omega
    exact_mod_cast this
  -- the mass identity at level `n+1`
  have hmass : Tv (n + 2)
      = ∫ u in (2 : ℝ)..((2 * n + 6 : ℕ) : ℝ),
          oddSum (n + 1) u * Real.log ((u + 1) / 3) := by
    have h := mass_identity (n + 1)
    have h1 : n + 1 + 1 = n + 2 := by omega
    have h2 : 2 * (n + 1) + 4 = 2 * n + 6 := by omega
    rw [h1, h2] at h
    exact h
  -- integrability on the two pieces
  have hI24 := integrable_oddSum_log2 n 2 4
    (fun x hx => by rw [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 4)] at hx; linarith [hx.1])
  have hI4N : IntervalIntegrable
      (fun u : ℝ => oddSum (n + 1) u * Real.log ((u + 1) / 3)) volume (4 : ℝ)
      (((2 * n + 6 : ℕ) : ℝ)) := by
    apply integrable_oddSum_log2
    intro x hx
    rw [Set.uIcc_of_le h4N] at hx
    linarith [hx.1]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hI24 hI4N
  -- the lower bound on `[4, 2n+6]`
  have hpiece : (49 / 96 : ℝ) * (∫ u in (4 : ℝ)..(((2 * n + 6 : ℕ) : ℝ)), oddSum (n + 1) u)
      ≤ ∫ u in (4 : ℝ)..(((2 * n + 6 : ℕ) : ℝ)),
          oddSum (n + 1) u * Real.log ((u + 1) / 3) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on h4N ((oddSum_intervalIntegrable (n + 1) 4 _).const_mul _) hI4N ?_
    intro u hu
    have hc : (49 / 96 : ℝ) ≤ Real.log ((u + 1) / 3) := by
      have hle := c_le_log_five_thirds
      have hmono : Real.log ((5:ℝ) / 3) ≤ Real.log ((u + 1) / 3) := by
        apply Real.log_le_log (by norm_num)
        linarith [hu.1]
      linarith
    have hfnn : 0 ≤ oddSum (n + 1) u := oddSum_nonneg (n + 1) u
    calc (49 / 96 : ℝ) * oddSum (n + 1) u
        ≤ Real.log ((u + 1) / 3) * oddSum (n + 1) u := mul_le_mul_of_nonneg_right hc hfnn
      _ = oddSum (n + 1) u * Real.log ((u + 1) / 3) := by ring
  -- `∫_4^{2n+6} oddSum (n+1) = Cv (n+1) - ∫_2^4 oddSum (n+1)`
  have hCv : Cv (n + 1) = ∫ u in (2 : ℝ)..(((2 * n + 6 : ℕ) : ℝ)), oddSum (n + 1) u := by
    rw [Cv]
    rw [show (2 * (n + 1) + 4 : ℕ) = 2 * n + 6 from by omega]
  have hJ4N : (∫ u in (4 : ℝ)..(((2 * n + 6 : ℕ) : ℝ)), oddSum (n + 1) u)
      = Cv (n + 1) - ∫ u in (2 : ℝ)..4, oddSum (n + 1) u := by
    have hadj := intervalIntegral.integral_add_adjacent_intervals
      (oddSum_intervalIntegrable (n + 1) (2 : ℝ) 4)
      (oddSum_intervalIntegrable (n + 1) (4 : ℝ) (((2 * n + 6 : ℕ) : ℝ)))
    rw [hCv]
    linarith
  have hJ24 : (∫ u in (2 : ℝ)..4, oddSum (n + 1) u)
      = (3 + Cv n) * Aprime 4 + (Tv (n + 1) - 4) * Real.log 2 + 2 := integral_oddSum_Icc n
  -- the key inequality and the final assembly
  have hkey := mass_key n
  have hprod : (49 / 96 : ℝ) * ((3 + Cv n) * Aprime 4)
      ≤ (49 / 96 : ℝ) * ((3 + Cv n)
          * (-17 / 30 + (184 / 15 : ℝ) * Real.log 2 - (69 / 10 : ℝ) * Real.log 3)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    exact mul_le_mul_of_nonneg_left Aprime_four_le_D (by linarith [Cv_nonneg n])
  linarith [hmass, hsplit, hpiece, hJ4N, hJ24, hkey, hprod]

end

end Work.NumberTheory.Chen.APSwitchUpper
