import Mathlib
import Submission.L2Norm
import Submission.Commons.Analysis.Interval.aux_averaging_count

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

noncomputable section

/-!
# Prop ell-2 update (Tikhomirov 2020, Section 3)

Deterministic and counting foundations for `Prop ell-2 update`
(paper lines ~985–1290).  All functions live on `ℤ`.

The (only) shape of the paper's "log₂-Lipschitz" hypothesis that is used is the
multiplicative ("ratio") bound
`ratioLip ε g := ∀ s t, g s ≤ 2^{ε·|s−t|}·g t`
(equivalent, for positive `g`, to `|log₂ g(s) − log₂ g(t)| ≤ ε|s−t|`,
and preserved by convex combinations of translates — which is how Prop refinement
needs it).  This module records the basic consequences of `ratioLip`
plus the basic `2^x` inequalities used in the spike-threshold geometry.

-/

namespace Submission.Ell2Update

open scoped BigOperators

/-- Multiplicative ("log₂-Lipschitz in ratio form") condition. -/
def ratioLip (ε : ℝ) (g : ℤ → ℝ) : Prop :=
  ∀ s t : ℤ, g s ≤ (2 : ℝ) ^ (ε * |(t : ℝ) - (s : ℝ)|) * g t

/-- Positivity of `2^r`. -/
lemma rpow_two_pos (r : ℝ) : 0 < (2 : ℝ) ^ r :=
  Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) r

/-- `2^r · 2^s = 2^(r+s)`. -/
lemma rpow_two_add (r s : ℝ) : (2 : ℝ) ^ r * (2 : ℝ) ^ s = (2 : ℝ) ^ (r + s) := by
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]

/-- `2^r · 2^(−r) = 1`. -/
lemma rpow_two_add_neg (r : ℝ) : (2 : ℝ) ^ r * (2 : ℝ) ^ (-r) = 1 := by
  rw [rpow_two_add]
  norm_num

/-- Lower bound implied by `ratioLip`: a spike of `g` at `y` forces lower values
at `x` down to `2^{−ε|x−y|}` of it. -/
lemma ratioLip_lower {ε : ℝ} {g : ℤ → ℝ} (hlip : ratioLip ε g) (x y : ℤ) :
    (2 : ℝ) ^ (-ε * |(y : ℝ) - (x : ℝ)|) * g y ≤ g x := by
  have hu0 := hlip y x
  rw [abs_sub_comm] at hu0
  have hu : g y ≤ (2 : ℝ) ^ (ε * |(y : ℝ) - (x : ℝ)|) * g x := hu0
  have hnonneg : 0 ≤ (2 : ℝ) ^ (-ε * |(y : ℝ) - (x : ℝ)|) := (rpow_two_pos _).le
  have hmul := mul_le_mul_of_nonneg_left hu hnonneg
  have hprod : (2 : ℝ) ^ (-ε * |(y : ℝ) - (x : ℝ)|) * (2 : ℝ) ^ (ε * |(y : ℝ) - (x : ℝ)|) = 1 := by
    rw [rpow_two_add]
    have hsum : -ε * |(y : ℝ) - (x : ℝ)| + ε * |(y : ℝ) - (x : ℝ)| = 0 := by ring
    rw [hsum]
    norm_num
  calc
    (2 : ℝ) ^ (-ε * |(y : ℝ) - (x : ℝ)|) * g y
        ≤ (2 : ℝ) ^ (-ε * |(y : ℝ) - (x : ℝ)|) * ((2 : ℝ) ^ (ε * |(y : ℝ) - (x : ℝ)|) * g x) := hmul
    _ = ((2 : ℝ) ^ (-ε * |(y : ℝ) - (x : ℝ)|) * (2 : ℝ) ^ (ε * |(y : ℝ) - (x : ℝ)|)) * g x := by ring
    _ = g x := by rw [hprod]; ring

/-- `ratioLip` is preserved under pointwise convex combinations of translates. -/
lemma ratioLip_avg {ε : ℝ} {g : ℤ → ℝ} (hlip : ratioLip ε g) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {y : ℤ} : ratioLip ε (fun t : ℤ => (1 - p) * g t + p * g (t + y)) := by
  intro s t
  let d : ℝ := |(t : ℝ) - (s : ℝ)|
  have h1 := hlip s t
  have h2 := hlip (s + y) (t + y)
  have hdiff : ((t + y : ℤ) : ℝ) - ((s + y : ℤ) : ℝ) = (t : ℝ) - (s : ℝ) := by
    rw [Int.cast_add, Int.cast_add]
    ring
  have hd1 : |((t + y : ℤ) : ℝ) - ((s + y : ℤ) : ℝ)| = |(t : ℝ) - (s : ℝ)| := by
    rw [hdiff]
  have h2' : g (s + y) ≤ (2 : ℝ) ^ (ε * d) * g (t + y) := by
    rw [hd1] at h2
    simpa [d] using h2
  have hp2 : 0 ≤ (2 : ℝ) ^ (ε * d) := (rpow_two_pos _).le
  calc
    (1 - p) * g s + p * g (s + y) ≤ (1 - p) * ((2 : ℝ) ^ (ε * d) * g t) + p * ((2 : ℝ) ^ (ε * d) * g (t + y)) := by
      have hc1 : (1 - p) * g s ≤ (1 - p) * ((2 : ℝ) ^ (ε * d) * g t) := by
        exact mul_le_mul_of_nonneg_left h1 (by linarith)
      have hc2 : p * g (s + y) ≤ p * ((2 : ℝ) ^ (ε * d) * g (t + y)) := by
        exact mul_le_mul_of_nonneg_left h2' hp0
      nlinarith
    _ = (2 : ℝ) ^ (ε * d) * ((1 - p) * g t + p * g (t + y)) := by ring

/-- A spike at `y` forces `g x ≥ a` for `x` within distance `D` of `y`, provided
`a ≤ 2^{-εD}·B` and `g y ≥ B`. -/
lemma ratioLip_spike {ε : ℝ} {g : ℤ → ℝ} (hlip : ratioLip ε g) {x y : ℤ} {B a D : ℝ}
    (hB : B ≤ g y) (hB0 : 0 ≤ B) (hD : |(y : ℝ) - (x : ℝ)| ≤ D) (hε0 : 0 ≤ ε)
    (hdec : a ≤ (2 : ℝ) ^ (-ε * D) * B) :
    a ≤ g x := by
  have hεD : ε * |(y : ℝ) - (x : ℝ)| ≤ ε * D := mul_le_mul_of_nonneg_left hD hε0
  have hexp : -ε * D ≤ -ε * |(y : ℝ) - (x : ℝ)| := by nlinarith
  have hmono : (2 : ℝ) ^ (-ε * D) ≤ (2 : ℝ) ^ (-ε * |(y : ℝ) - (x : ℝ)|) := by
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ (2 : ℝ)) hexp
  have hstep1 : (2 : ℝ) ^ (-ε * D) * B ≤ (2 : ℝ) ^ (-ε * |(y : ℝ) - (x : ℝ)|) * B := by
    exact mul_le_mul_of_nonneg_right hmono hB0
  have hlow := ratioLip_lower (ε := ε) (g := g) hlip x y
  have hstep2 : (2 : ℝ) ^ (-ε * |(y : ℝ) - (x : ℝ)|) * B ≤ (2 : ℝ) ^ (-ε * |(y : ℝ) - (x : ℝ)|) * g y := by
    exact mul_le_mul_of_nonneg_left hB (rpow_two_pos _).le
  calc
    a ≤ (2 : ℝ) ^ (-ε * D) * B := hdec
    _ ≤ (2 : ℝ) ^ (-ε * |(y : ℝ) - (x : ℝ)|) * B := hstep1
    _ ≤ (2 : ℝ) ^ (-ε * |(y : ℝ) - (x : ℝ)|) * g y := hstep2
    _ ≤ g x := hlow

/-- `log 2 ≥ 1/2`. -/
lemma log_two_ge_half : (1 : ℝ) / 2 ≤ Real.log (2 : ℝ) := by
  have hexp_le : Real.exp ((1 : ℝ) / 2) ≤ (2 : ℝ) := by
    rw [Real.exp_half (1 : ℝ)]
    have hle4 : Real.exp 1 ≤ (4 : ℝ) := by linarith [Real.exp_one_lt_three]
    have hsqrt : Real.sqrt (Real.exp 1) ≤ Real.sqrt (4 : ℝ) := Real.sqrt_le_sqrt hle4
    norm_num at hsqrt
    exact hsqrt
  have hlog := Real.log_le_log (Real.exp_pos ((1 : ℝ) / 2)) hexp_le
  rw [Real.log_exp] at hlog
  exact hlog

/-- `log 2 ≤ 1`. -/
lemma log_two_le_one : Real.log (2 : ℝ) ≤ 1 := by
  have hle : (2 : ℝ) ≤ Real.exp 1 := le_of_lt Real.exp_one_gt_two
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hle
  rwa [Real.log_exp] at hlog

/-- `2^x ≥ 1 + x·log 2`. -/
lemma two_pow_ge_one_add_mul_log (x : ℝ) (hx0 : 0 ≤ x) :
    (1 : ℝ) + x * Real.log (2 : ℝ) ≤ (2 : ℝ) ^ x := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlogpos : 0 < Real.log (2 : ℝ) := by
    exact (Real.log_pos_iff (by norm_num : (0 : ℝ) ≤ (2 : ℝ))).mpr (by norm_num : (1 : ℝ) < (2 : ℝ))
  have hxlog0 : 0 ≤ x * Real.log (2 : ℝ) := mul_nonneg hx0 hlogpos.le
  have h1 : x * Real.log (2 : ℝ) + 1 ≤ Real.exp (x * Real.log (2 : ℝ)) :=
    Real.add_one_le_exp (x * Real.log (2 : ℝ))
  have hmul : Real.log (2 : ℝ) * x = x * Real.log (2 : ℝ) := by ring
  rw [hmul]
  rw [show (1 : ℝ) + x * Real.log (2 : ℝ) = x * Real.log (2 : ℝ) + 1 by ring]
  exact h1

/-- `2^x − 1 ≥ x/2` for `x ∈ [0,1]` (lower bound on `2^{μ²}−1`). -/
lemma two_pow_sub_one_ge_half (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x / 2 ≤ (2 : ℝ) ^ x - 1 := by
  have hlogge : (1 : ℝ) / 2 ≤ Real.log (2 : ℝ) := log_two_ge_half
  have hxlog : x * ((1 : ℝ) / 2) ≤ x * Real.log (2 : ℝ) :=
    mul_le_mul_of_nonneg_left hlogge hx0
  have hg := two_pow_ge_one_add_mul_log x hx0
  have hcast : x * ((1 : ℝ) / 2) = x / 2 := by ring
  rw [hcast] at hxlog
  linarith

/-- `2^x ≤ 2` for `0 ≤ x ≤ 1` (monotonicity). -/
lemma two_pow_le_two (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (2 : ℝ) ^ x ≤ 2 := by
  have hmono := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ (2 : ℝ)) hx1
  have h2 : (2 : ℝ) ^ (1 : ℝ) = 2 := by norm_num
  rwa [h2] at hmono

/-- `2^x > 1` for `0 < x`. -/
lemma two_pow_gt_one (x : ℝ) (hx : 0 < x) : (1 : ℝ) < (2 : ℝ) ^ x := by
  have hg := two_pow_ge_one_add_mul_log x (le_of_lt hx)
  have hlogpos : 0 < Real.log (2 : ℝ) := by
    exact (Real.log_pos_iff (by norm_num : (0 : ℝ) ≤ (2 : ℝ))).mpr (by norm_num : (1 : ℝ) < (2 : ℝ))
  have hxlog : 0 < x * Real.log (2 : ℝ) := mul_pos hx hlogpos
  linarith


/-- `2^a ≤ 2^b` for `a ≤ b` (base `2 ≥ 1`). -/
lemma rpow_two_mono {a b : ℝ} (h : a ≤ b) : (2 : ℝ) ^ a ≤ (2 : ℝ) ^ b :=
  Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ (2 : ℝ)) h

/-- `2^a ≥ 1` for `a ≥ 0`. -/
lemma rpow_two_ge_one (a : ℝ) (ha : 0 ≤ a) : (1 : ℝ) ≤ (2 : ℝ) ^ a := by
  simpa using (rpow_two_mono (a := 0) (b := a) ha)



/-- `ratioLip` is monotone in the Lipschitz constant `ε`. -/
lemma ratioLip_mono {ε₁ ε₂ : ℝ} {g : ℤ → ℝ} (hg0 : ∀ t : ℤ, 0 ≤ g t) (hε : ε₁ ≤ ε₂)
    (hlip : ratioLip ε₁ g) : ratioLip ε₂ g := by
  intro s t
  have h1 := hlip s t
  have hd0 : 0 ≤ |(t : ℝ) - (s : ℝ)| := abs_nonneg _
  have hεd : ε₁ * |(t : ℝ) - (s : ℝ)| ≤ ε₂ * |(t : ℝ) - (s : ℝ)| :=
    mul_le_mul_of_nonneg_right hε hd0
  have hmono : (2 : ℝ) ^ (ε₁ * |(t : ℝ) - (s : ℝ)|) ≤ (2 : ℝ) ^ (ε₂ * |(t : ℝ) - (s : ℝ)|) :=
    rpow_two_mono hεd
  have hmul := mul_le_mul_of_nonneg_right hmono (hg0 t)
  calc
    g s ≤ (2 : ℝ) ^ (ε₁ * |(t : ℝ) - (s : ℝ)|) * g t := h1
    _ ≤ (2 : ℝ) ^ (ε₂ * |(t : ℝ) - (s : ℝ)|) * g t := hmul

/-- `ratioLip` is preserved under pointwise multiplication by a nonnegative
constant. -/
lemma ratioLip_mul_const {ε : ℝ} {g : ℤ → ℝ} {a : ℝ} (ha : 0 ≤ a) (hlip : ratioLip ε g) :
    ratioLip ε (fun t : ℤ => a * g t) := by
  intro s t
  have h1 := hlip s t
  calc
    a * g s ≤ a * ((2 : ℝ) ^ (ε * |(t : ℝ) - (s : ℝ)|) * g t) := by
      exact mul_le_mul_of_nonneg_left h1 ha
    _ = (2 : ℝ) ^ (ε * |(t : ℝ) - (s : ℝ)|) * (a * g t) := by ring


end Submission.Ell2Update
