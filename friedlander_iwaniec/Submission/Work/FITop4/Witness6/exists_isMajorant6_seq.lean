import Mathlib
import Submission.Work.FITop4.Defs6
import Submission.Work.FITop4.Witness6.step9_props

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.FITop4.Witness6

noncomputable section

open scoped Topology

/-! # The §5/§7 majorant of round 6, built directly from the clamped nonic step

`Work.FITop4.Witness6.step9` (`Witness6/Step9Defs`) is the clamped nonic Hermite step
`step9 t = 0` for `t ≤ 0`, `= 1` for `1 ≤ t`, `= p9 t` on `[0,1]`, and
`Work.FITop4.Witness6.step9_props` provides its `C⁴`-regularity, its chain of clamped derivatives
`st8 = deriv step9`, `st7 = deriv st8`, `st6 = deriv st7`, `st5 = deriv st6`, and the bounds
`|st8| ≤ 5/2`, `|st7| ≤ 25`.

This file assembles from it an explicit round-6 majorant `f : ℤ → ℝ` with the *fixed* absolute
derivative constants `Defs6.cMaj`.  Concretely, for `M > 0` put `α = 4/(3M)` and

  `F u = step9 (α·u - 1/3) - step9 (α·u - 13/3) = step9 (α·(u - M/4)) - step9 (α·(u - 13M/4))`.

Because `α·M = 4/3`, the first step is `0` for `u ≤ M/4` and `1` for `u ≥ M`, while the second is
`0` for `u ≤ 13M/4` and `1` for `u ≥ 4M`; consequently `F = 0` off `(M/4, 4M)`, `F = 1` on
`[M, 13M/4] ⊇ (M, 2M]`, and `0 ≤ F ≤ 1`.  The two ramps are *disjoint* (`13M/4 > M`), so at every
`u` at least one of the two summands has all of its clamped derivatives equal to `0`; hence each
iterated derivative of `F` is bounded by that of a *single* rescaled step, which is exactly what
makes the fixed constants `cMaj j` available:

  `|F^{(j)}(u)| ≤ α^j · sup|p9^{(j)}|`, with `sup|p9| ≤ 1`, `sup|p9'| ≤ 5/2`, `sup|p9''| ≤ 25`,
  `sup|p9'''| ≤ 312480`, `sup|p9''''| ≤ 1360800`.

Dividing by `M^{-j}` leaves `(4/3)^j·C_j ≤ cMaj j`, checked numerically:
`(4/3)·(5/2) = 10/3 ≤ 8`, `(4/3)²·25 = 400/9 ≤ 64`, `(4/3)³·312480 ≤ 2^36`,
`(4/3)⁴·1360800 = 4300800 ≤ 2^48`. -/


/-! ## 0. Bounds on the clamped third and fourth derivatives of `step9` -/

lemma abs_p6_le (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) : |p6 t| ≤ 312480 := by
  have h2 : t ^ 2 ≤ 1 := pow_le_one₀ h0 h1
  have h3 : t ^ 3 ≤ 1 := pow_le_one₀ h0 h1
  have h4 : t ^ 4 ≤ 1 := pow_le_one₀ h0 h1
  have h5 : t ^ 5 ≤ 1 := pow_le_one₀ h0 h1
  have h6 : t ^ 6 ≤ 1 := pow_le_one₀ h0 h1
  have g2 : 0 ≤ t ^ 2 := pow_nonneg h0 2
  have g3 : 0 ≤ t ^ 3 := pow_nonneg h0 3
  have g4 : 0 ≤ t ^ 4 := pow_nonneg h0 4
  have g5 : 0 ≤ t ^ 5 := pow_nonneg h0 5
  have g6 : 0 ≤ t ^ 6 := pow_nonneg h0 6
  rw [show p6 t = 7560 * t^2 - 50400 * t^3 + 113400 * t^4 - 105840 * t^5 + 35280 * t^6 by
    unfold p6; ring]
  rw [abs_le]
  constructor <;> nlinarith

lemma abs_p5_le (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) : |p5 t| ≤ 1360800 := by
  have h2 : t ^ 2 ≤ 1 := pow_le_one₀ h0 h1
  have h3 : t ^ 3 ≤ 1 := pow_le_one₀ h0 h1
  have h4 : t ^ 4 ≤ 1 := pow_le_one₀ h0 h1
  have h5 : t ^ 5 ≤ 1 := pow_le_one₀ h0 h1
  have g1 : 0 ≤ t ^ 1 := pow_nonneg h0 1
  have g2 : 0 ≤ t ^ 2 := pow_nonneg h0 2
  have g3 : 0 ≤ t ^ 3 := pow_nonneg h0 3
  have g4 : 0 ≤ t ^ 4 := pow_nonneg h0 4
  have g5 : 0 ≤ t ^ 5 := pow_nonneg h0 5
  rw [show p5 t = 15120 * t - 151200 * t^2 + 453600 * t^3 - 529200 * t^4 + 211680 * t^5 by
    unfold p5; ring]
  rw [abs_le]
  constructor <;> nlinarith

lemma abs_st6_le (t : ℝ) : |st6 t| ≤ 312480 := by
  unfold st6
  by_cases h : t ≤ 0
  · rw [if_pos h, abs_zero]; norm_num
  · rw [if_neg h]
    by_cases h' : 1 ≤ t
    · rw [if_pos h', abs_zero]; norm_num
    · rw [if_neg h']
      push Not at h h'
      exact abs_p6_le t h.le h'.le

lemma abs_st5_le (t : ℝ) : |st5 t| ≤ 1360800 := by
  unfold st5
  by_cases h : t ≤ 0
  · rw [if_pos h, abs_zero]; norm_num
  · rw [if_neg h]
    by_cases h' : 1 ≤ t
    · rw [if_pos h', abs_zero]; norm_num
    · rw [if_neg h']
      push Not at h h'
      exact abs_p5_le t h.le h'.le

/-! ## 1. The affine rescaling of `step9` and its derivative chain -/

/-- `sOf a b u = step9 (a*u + b)`. -/
def sOf (a b : ℝ) : ℝ → ℝ := fun u => step9 (a * u + b)

def rh1 (a b : ℝ) : ℝ → ℝ := fun u => a * st8 (a * u + b)
def rh2 (a b : ℝ) : ℝ → ℝ := fun u => a * (a * st7 (a * u + b))
def rh3 (a b : ℝ) : ℝ → ℝ := fun u => a * (a * (a * st6 (a * u + b)))
def rh4 (a b : ℝ) : ℝ → ℝ := fun u => a * (a * (a * (a * st5 (a * u + b))))

lemma hasDerivAt_affine_mul (a b c : ℝ) (g g' : ℝ → ℝ)
    (hg : ∀ y, HasDerivAt g (g' y) y) (x : ℝ) :
    HasDerivAt (fun u => c * g (a * u + b)) (c * (g' (a * x + b) * a)) x := by
  have hlin : HasDerivAt (fun u : ℝ => a * u + b) a x := by
    simpa using ((hasDerivAt_id x).const_mul a).add_const b
  have h1 : HasDerivAt (fun u : ℝ => g (a * u + b)) (g' (a * x + b) * a) x :=
    (hg (a * x + b)).comp x hlin
  exact h1.const_mul c

lemma hasDerivAt_sOf (a b x : ℝ) : HasDerivAt (sOf a b) (st8 (a * x + b) * a) x := by
  have h := hasDerivAt_affine_mul a b 1 step9 st8 step9_hasDerivAt x
  rw [show sOf a b = fun u : ℝ => step9 (a * u + b) from rfl]
  simpa using h

lemma hasDerivAt_rh1 (a b x : ℝ) :
    HasDerivAt (rh1 a b) (a * (st7 (a * x + b) * a)) x :=
  hasDerivAt_affine_mul a b a st8 st7 st8_hasDerivAt x

lemma hasDerivAt_rh2 (a b x : ℝ) :
    HasDerivAt (rh2 a b) (a * ((a * st6 (a * x + b)) * a)) x :=
  hasDerivAt_affine_mul a b a (fun y => a * st7 y) (fun y => a * st6 y)
    (fun y => (st7_hasDerivAt y).const_mul a) x

lemma hasDerivAt_rh3 (a b x : ℝ) :
    HasDerivAt (rh3 a b) (a * ((a * (a * st5 (a * x + b))) * a)) x :=
  hasDerivAt_affine_mul a b a (fun y => a * (a * st6 y)) (fun y => a * (a * st5 y))
    (fun y => ((st6_hasDerivAt y).const_mul a).const_mul a) x

/-! ## 2. Vanishing of the clamped derivatives outside `[0,1]` -/

lemma st8_eq_zero_of_le (t : ℝ) (h : t ≤ 0) : st8 t = 0 := by
  unfold st8; rw [if_pos h]
lemma st8_eq_zero_of_ge (t : ℝ) (h : 1 ≤ t) : st8 t = 0 := by
  unfold st8; rw [if_neg (by linarith : ¬ t ≤ 0), if_pos h]
lemma st7_eq_zero_of_le (t : ℝ) (h : t ≤ 0) : st7 t = 0 := by
  unfold st7; rw [if_pos h]
lemma st7_eq_zero_of_ge (t : ℝ) (h : 1 ≤ t) : st7 t = 0 := by
  unfold st7; rw [if_neg (by linarith : ¬ t ≤ 0), if_pos h]
lemma st6_eq_zero_of_le (t : ℝ) (h : t ≤ 0) : st6 t = 0 := by
  unfold st6; rw [if_pos h]
lemma st6_eq_zero_of_ge (t : ℝ) (h : 1 ≤ t) : st6 t = 0 := by
  unfold st6; rw [if_neg (by linarith : ¬ t ≤ 0), if_pos h]
lemma st5_eq_zero_of_le (t : ℝ) (h : t ≤ 0) : st5 t = 0 := by
  unfold st5; rw [if_pos h]
lemma st5_eq_zero_of_ge (t : ℝ) (h : 1 ≤ t) : st5 t = 0 := by
  unfold st5; rw [if_neg (by linarith : ¬ t ≤ 0), if_pos h]

lemma rh1_eq_zero_of_le (a b u : ℝ) (h : a * u + b ≤ 0) : rh1 a b u = 0 := by
  show a * st8 (a * u + b) = 0
  rw [st8_eq_zero_of_le (a * u + b) h, mul_zero]
lemma rh1_eq_zero_of_ge (a b u : ℝ) (h : 1 ≤ a * u + b) : rh1 a b u = 0 := by
  show a * st8 (a * u + b) = 0
  rw [st8_eq_zero_of_ge (a * u + b) h, mul_zero]
lemma rh2_eq_zero_of_le (a b u : ℝ) (h : a * u + b ≤ 0) : rh2 a b u = 0 := by
  show a * (a * st7 (a * u + b)) = 0
  rw [st7_eq_zero_of_le (a * u + b) h, mul_zero, mul_zero]
lemma rh2_eq_zero_of_ge (a b u : ℝ) (h : 1 ≤ a * u + b) : rh2 a b u = 0 := by
  show a * (a * st7 (a * u + b)) = 0
  rw [st7_eq_zero_of_ge (a * u + b) h, mul_zero, mul_zero]
lemma rh3_eq_zero_of_le (a b u : ℝ) (h : a * u + b ≤ 0) : rh3 a b u = 0 := by
  show a * (a * (a * st6 (a * u + b))) = 0
  rw [st6_eq_zero_of_le (a * u + b) h, mul_zero, mul_zero, mul_zero]
lemma rh3_eq_zero_of_ge (a b u : ℝ) (h : 1 ≤ a * u + b) : rh3 a b u = 0 := by
  show a * (a * (a * st6 (a * u + b))) = 0
  rw [st6_eq_zero_of_ge (a * u + b) h, mul_zero, mul_zero, mul_zero]
lemma rh4_eq_zero_of_le (a b u : ℝ) (h : a * u + b ≤ 0) : rh4 a b u = 0 := by
  show a * (a * (a * (a * st5 (a * u + b)))) = 0
  rw [st5_eq_zero_of_le (a * u + b) h, mul_zero, mul_zero, mul_zero, mul_zero]
lemma rh4_eq_zero_of_ge (a b u : ℝ) (h : 1 ≤ a * u + b) : rh4 a b u = 0 := by
  show a * (a * (a * (a * st5 (a * u + b)))) = 0
  rw [st5_eq_zero_of_ge (a * u + b) h, mul_zero, mul_zero, mul_zero, mul_zero]

/-! ## 3. Pointwise derivative bounds for `rh1 … rh4` -/

lemma abs_rh1_le (a b u : ℝ) (ha : 0 ≤ a) : |rh1 a b u| ≤ a * (5/2) := by
  have h : rh1 a b u = a * st8 (a * u + b) := rfl
  rw [h, abs_mul, abs_of_nonneg ha]
  exact mul_le_mul_of_nonneg_left (abs_st8_le (a * u + b)) ha

lemma abs_rh2_le (a b u : ℝ) (ha : 0 ≤ a) : |rh2 a b u| ≤ a^2 * 25 := by
  have h : rh2 a b u = a * (a * st7 (a * u + b)) := rfl
  rw [h, abs_mul, abs_mul, abs_of_nonneg ha]
  have h2 : |st7 (a * u + b)| ≤ 25 := abs_st7_le _
  nlinarith [h2, ha, abs_nonneg (st7 (a * u + b))]

lemma abs_rh3_le (a b u : ℝ) (ha : 0 ≤ a) : |rh3 a b u| ≤ a^3 * 312480 := by
  have h : rh3 a b u = a * (a * (a * st6 (a * u + b))) := rfl
  rw [h, abs_mul, abs_mul, abs_mul, abs_of_nonneg ha]
  have h2 : |st6 (a * u + b)| ≤ 312480 := abs_st6_le _
  have h3 : a * (a * (a * |st6 (a * u + b)|)) ≤ a * (a * (a * 312480)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 ha) ha) ha
  have h4 : a * (a * (a * (312480:ℝ))) = a^3 * 312480 := by ring
  rw [h4] at h3
  exact h3

lemma abs_rh4_le (a b u : ℝ) (ha : 0 ≤ a) : |rh4 a b u| ≤ a^4 * 1360800 := by
  have h : rh4 a b u = a * (a * (a * (a * st5 (a * u + b)))) := rfl
  rw [h, abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg ha]
  have h2 : |st5 (a * u + b)| ≤ 1360800 := abs_st5_le _
  have h3 : a * (a * (a * (a * |st5 (a * u + b)|))) ≤ a * (a * (a * (a * 1360800))) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left h2 ha) ha) ha) ha
  have h4 : a * (a * (a * (a * (1360800:ℝ)))) = a^4 * 1360800 := by ring
  rw [h4] at h3
  exact h3

/-! ## 4. The majorant -/

def alpha (M : ℝ) : ℝ := 4 / (3 * M)

lemma alpha_nonneg (M : ℝ) (hM : 0 < M) : 0 ≤ alpha M := by unfold alpha; positivity
lemma alpha_pos (M : ℝ) (hM : 0 < M) : 0 < alpha M := by unfold alpha; positivity
lemma alpha_mul_M (M : ℝ) (hM : 0 < M) : alpha M * M = 4/3 := by
  unfold alpha; field_simp; try ring

def b1 : ℝ := -(1/3)
def b2 : ℝ := -(13/3)

def majF (M : ℝ) : ℝ → ℝ := sOf (alpha M) b1 - sOf (alpha M) b2

lemma majF_apply (M u : ℝ) :
    majF M u = step9 (alpha M * u + b1) - step9 (alpha M * u + b2) := rfl

lemma hasDerivAt_majF (M x : ℝ) :
    HasDerivAt (majF M) (rh1 (alpha M) b1 x - rh1 (alpha M) b2 x) x := by
  have h := (hasDerivAt_sOf (alpha M) b1 x).sub (hasDerivAt_sOf (alpha M) b2 x)
  have hv : st8 (alpha M * x + b1) * alpha M - st8 (alpha M * x + b2) * alpha M
      = rh1 (alpha M) b1 x - rh1 (alpha M) b2 x := by
    show st8 (alpha M * x + b1) * alpha M - st8 (alpha M * x + b2) * alpha M
        = alpha M * st8 (alpha M * x + b1) - alpha M * st8 (alpha M * x + b2)
    ring
  rw [hv] at h
  rw [show majF M = sOf (alpha M) b1 - sOf (alpha M) b2 from rfl]
  exact h

lemma hasDerivAt_majF1 (M x : ℝ) :
    HasDerivAt (fun u => rh1 (alpha M) b1 u - rh1 (alpha M) b2 u)
      (rh2 (alpha M) b1 x - rh2 (alpha M) b2 x) x := by
  have h := (hasDerivAt_rh1 (alpha M) b1 x).sub (hasDerivAt_rh1 (alpha M) b2 x)
  have hv : alpha M * (st7 (alpha M * x + b1) * alpha M)
        - alpha M * (st7 (alpha M * x + b2) * alpha M)
      = rh2 (alpha M) b1 x - rh2 (alpha M) b2 x := by
    show alpha M * (st7 (alpha M * x + b1) * alpha M)
        - alpha M * (st7 (alpha M * x + b2) * alpha M)
        = alpha M * (alpha M * st7 (alpha M * x + b1))
          - alpha M * (alpha M * st7 (alpha M * x + b2))
    ring
  rw [hv] at h
  rwa [show (rh1 (alpha M) b1 - rh1 (alpha M) b2)
      = (fun u => rh1 (alpha M) b1 u - rh1 (alpha M) b2 u) from rfl] at h

lemma hasDerivAt_majF2 (M x : ℝ) :
    HasDerivAt (fun u => rh2 (alpha M) b1 u - rh2 (alpha M) b2 u)
      (rh3 (alpha M) b1 x - rh3 (alpha M) b2 x) x := by
  have h := (hasDerivAt_rh2 (alpha M) b1 x).sub (hasDerivAt_rh2 (alpha M) b2 x)
  have hv : alpha M * ((alpha M * st6 (alpha M * x + b1)) * alpha M)
        - alpha M * ((alpha M * st6 (alpha M * x + b2)) * alpha M)
      = rh3 (alpha M) b1 x - rh3 (alpha M) b2 x := by
    show alpha M * ((alpha M * st6 (alpha M * x + b1)) * alpha M)
        - alpha M * ((alpha M * st6 (alpha M * x + b2)) * alpha M)
        = alpha M * (alpha M * (alpha M * st6 (alpha M * x + b1)))
          - alpha M * (alpha M * (alpha M * st6 (alpha M * x + b2)))
    ring
  rw [hv] at h
  rwa [show (rh2 (alpha M) b1 - rh2 (alpha M) b2)
      = (fun u => rh2 (alpha M) b1 u - rh2 (alpha M) b2 u) from rfl] at h

lemma hasDerivAt_majF3 (M x : ℝ) :
    HasDerivAt (fun u => rh3 (alpha M) b1 u - rh3 (alpha M) b2 u)
      (rh4 (alpha M) b1 x - rh4 (alpha M) b2 x) x := by
  have h := (hasDerivAt_rh3 (alpha M) b1 x).sub (hasDerivAt_rh3 (alpha M) b2 x)
  have hv : alpha M * ((alpha M * (alpha M * st5 (alpha M * x + b1))) * alpha M)
        - alpha M * ((alpha M * (alpha M * st5 (alpha M * x + b2))) * alpha M)
      = rh4 (alpha M) b1 x - rh4 (alpha M) b2 x := by
    show alpha M * ((alpha M * (alpha M * st5 (alpha M * x + b1))) * alpha M)
        - alpha M * ((alpha M * (alpha M * st5 (alpha M * x + b2))) * alpha M)
        = alpha M * (alpha M * (alpha M * (alpha M * st5 (alpha M * x + b1))))
          - alpha M * (alpha M * (alpha M * (alpha M * st5 (alpha M * x + b2))))
    ring
  rw [hv] at h
  rwa [show (rh3 (alpha M) b1 - rh3 (alpha M) b2)
      = (fun u => rh3 (alpha M) b1 u - rh3 (alpha M) b2 u) from rfl] at h

lemma iteratedDeriv1_majF (M u : ℝ) :
    iteratedDeriv 1 (majF M) u = rh1 (alpha M) b1 u - rh1 (alpha M) b2 u := by
  rw [iteratedDeriv_one]; exact (hasDerivAt_majF M u).deriv

lemma iteratedDeriv2_majF (M u : ℝ) :
    iteratedDeriv 2 (majF M) u = rh2 (alpha M) b1 u - rh2 (alpha M) b2 u := by
  rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have h1 : deriv (majF M) = fun u => rh1 (alpha M) b1 u - rh1 (alpha M) b2 u :=
    funext fun x => (hasDerivAt_majF M x).deriv
  rw [h1]
  exact (hasDerivAt_majF1 M u).deriv

lemma iteratedDeriv3_majF (M u : ℝ) :
    iteratedDeriv 3 (majF M) u = rh3 (alpha M) b1 u - rh3 (alpha M) b2 u := by
  rw [show (3:ℕ) = 2 + 1 from rfl, iteratedDeriv_succ, show (2:ℕ) = 1 + 1 from rfl,
    iteratedDeriv_succ, iteratedDeriv_one]
  have h1 : deriv (majF M) = fun u => rh1 (alpha M) b1 u - rh1 (alpha M) b2 u :=
    funext fun x => (hasDerivAt_majF M x).deriv
  have h2 : deriv (fun u => rh1 (alpha M) b1 u - rh1 (alpha M) b2 u)
      = fun u => rh2 (alpha M) b1 u - rh2 (alpha M) b2 u :=
    funext fun x => (hasDerivAt_majF1 M x).deriv
  rw [h1, h2]
  exact (hasDerivAt_majF2 M u).deriv

lemma iteratedDeriv4_majF (M u : ℝ) :
    iteratedDeriv 4 (majF M) u = rh4 (alpha M) b1 u - rh4 (alpha M) b2 u := by
  rw [show (4:ℕ) = 3 + 1 from rfl, iteratedDeriv_succ, show (3:ℕ) = 2 + 1 from rfl,
    iteratedDeriv_succ, show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have h1 : deriv (majF M) = fun u => rh1 (alpha M) b1 u - rh1 (alpha M) b2 u :=
    funext fun x => (hasDerivAt_majF M x).deriv
  have h2 : deriv (fun u => rh1 (alpha M) b1 u - rh1 (alpha M) b2 u)
      = fun u => rh2 (alpha M) b1 u - rh2 (alpha M) b2 u :=
    funext fun x => (hasDerivAt_majF1 M x).deriv
  have h3 : deriv (fun u => rh2 (alpha M) b1 u - rh2 (alpha M) b2 u)
      = fun u => rh3 (alpha M) b1 u - rh3 (alpha M) b2 u :=
    funext fun x => (hasDerivAt_majF2 M x).deriv
  rw [h1, h2, h3]
  exact (hasDerivAt_majF3 M u).deriv

/-! ## 5. Numeric comparison with the fixed constants -/

lemma cMaj_zero : Work.FITop4.cMaj 0 = 1 := by norm_num [Work.FITop4.cMaj]
lemma cMaj_one : Work.FITop4.cMaj 1 = 8 := by norm_num [Work.FITop4.cMaj]
lemma cMaj_two : Work.FITop4.cMaj 2 = 64 := by norm_num [Work.FITop4.cMaj]
lemma cMaj_three : Work.FITop4.cMaj 3 = 2^36 := by norm_num [Work.FITop4.cMaj]
lemma cMaj_four : Work.FITop4.cMaj 4 = 2^48 := by norm_num [Work.FITop4.cMaj]

lemma alpha_pow_mul_le (M : ℝ) (hM : 0 < M) (j : ℕ) (C : ℝ)
    (hC : (4/3:ℝ)^j * C ≤ Work.FITop4.cMaj j) :
    (alpha M)^j * C ≤ Work.FITop4.cMaj j * M^(-(j:ℝ)) := by
  have h1 : (alpha M)^j = (4/3:ℝ)^j * (M⁻¹)^j := by
    rw [show alpha M = (4/3:ℝ) * M⁻¹ from by unfold alpha; field_simp; try ring, mul_pow]
  have h2 : M^(-(j:ℝ)) = (M⁻¹)^j := by
    rw [Real.rpow_neg hM.le (j:ℝ), Real.rpow_natCast, inv_pow]
  rw [h1, h2]
  have hp : (0:ℝ) < (M⁻¹)^j := pow_pos (inv_pos.mpr hM) j
  calc ((4/3:ℝ)^j * (M⁻¹)^j) * C = ((4/3:ℝ)^j * C) * (M⁻¹)^j := by ring
    _ ≤ Work.FITop4.cMaj j * (M⁻¹)^j := mul_le_mul_of_nonneg_right hC hp.le

lemma key1 (M : ℝ) (hM : 0 < M) :
    alpha M * (5/2) ≤ Work.FITop4.cMaj 1 * M ^ (-((1:ℕ) : ℝ)) := by
  have h := alpha_pow_mul_le M hM 1 (5/2) (by rw [cMaj_one]; norm_num)
  simpa [pow_one] using h

lemma key2 (M : ℝ) (hM : 0 < M) :
    (alpha M)^2 * 25 ≤ Work.FITop4.cMaj 2 * M ^ (-((2:ℕ) : ℝ)) :=
  alpha_pow_mul_le M hM 2 25 (by rw [cMaj_two]; norm_num)

lemma key3 (M : ℝ) (hM : 0 < M) :
    (alpha M)^3 * 312480 ≤ Work.FITop4.cMaj 3 * M ^ (-((3:ℕ) : ℝ)) :=
  alpha_pow_mul_le M hM 3 312480 (by rw [cMaj_three]; norm_num)

lemma key4 (M : ℝ) (hM : 0 < M) :
    (alpha M)^4 * 1360800 ≤ Work.FITop4.cMaj 4 * M ^ (-((4:ℕ) : ℝ)) :=
  alpha_pow_mul_le M hM 4 1360800 (by rw [cMaj_four]; norm_num)

/-! ## 6. Values of the majorant -/

lemma majF_nonneg (M : ℝ) (hM : 0 < M) (u : ℝ) : 0 ≤ majF M u := by
  have hα : 0 ≤ alpha M := alpha_nonneg M hM
  rcases le_total u M with hu | hu
  · have hle : alpha M * u ≤ 4/3 := by
      rw [← alpha_mul_M M hM]; exact mul_le_mul_of_nonneg_left hu hα
    have h : alpha M * u + b2 ≤ 0 := by rw [b2]; linarith
    rw [majF_apply, step9_eq_zero _ h, sub_zero]
    exact (step9_mem01 _).1
  · have hge : 4/3 ≤ alpha M * u := by
      rw [← alpha_mul_M M hM]; exact mul_le_mul_of_nonneg_left hu hα
    have h : 1 ≤ alpha M * u + b1 := by rw [b1]; linarith
    rw [majF_apply, step9_eq_one _ h]
    have := (step9_mem01 (alpha M * u + b2)).2
    linarith

lemma majF_le_one (M : ℝ) (u : ℝ) : majF M u ≤ 1 := by
  rw [majF_apply]
  have h1 := (step9_mem01 (alpha M * u + b1)).2
  have h2 := (step9_mem01 (alpha M * u + b2)).1
  linarith

lemma majF_eq_zero_of_le (M : ℝ) (hM : 0 < M) (u : ℝ) (hu : u ≤ M/4) : majF M u = 0 := by
  have hα : 0 ≤ alpha M := alpha_nonneg M hM
  have h1 : alpha M * (M/4) = 1/3 := by unfold alpha; field_simp; try ring
  have hle : alpha M * u ≤ 1/3 := by
    rw [← h1]; exact mul_le_mul_of_nonneg_left hu hα
  have ha : alpha M * u + b1 ≤ 0 := by rw [b1]; linarith
  have hb : alpha M * u + b2 ≤ 0 := by rw [b2]; linarith
  rw [majF_apply, step9_eq_zero _ ha, step9_eq_zero _ hb, sub_zero]

lemma majF_eq_zero_of_ge (M : ℝ) (hM : 0 < M) (u : ℝ) (hu : 4*M ≤ u) : majF M u = 0 := by
  have hα : 0 ≤ alpha M := alpha_nonneg M hM
  have h1 : alpha M * (4*M) = 16/3 := by unfold alpha; field_simp; try ring
  have hle : 16/3 ≤ alpha M * u := by
    rw [← h1]; exact mul_le_mul_of_nonneg_left hu hα
  have ha : 1 ≤ alpha M * u + b1 := by rw [b1]; linarith
  have hb : 1 ≤ alpha M * u + b2 := by rw [b2]; linarith
  rw [majF_apply, step9_eq_one _ ha, step9_eq_one _ hb, sub_self]

lemma majF_eq_one_on (M : ℝ) (hM : 0 < M) (v : ℝ) (h1 : M ≤ v) (h2 : v ≤ 2*M) :
    majF M v = 1 := by
  have hα : 0 ≤ alpha M := alpha_nonneg M hM
  have hMM : alpha M * M = 4/3 := alpha_mul_M M hM
  have h2M : alpha M * (2*M) = 8/3 := by unfold alpha; field_simp; try ring
  have hge : 4/3 ≤ alpha M * v := by
    rw [← hMM]; exact mul_le_mul_of_nonneg_left h1 hα
  have hle : alpha M * v ≤ 8/3 := by
    rw [← h2M]; exact mul_le_mul_of_nonneg_left h2 hα
  have ha : 1 ≤ alpha M * v + b1 := by rw [b1]; linarith
  have hb : alpha M * v + b2 ≤ 0 := by rw [b2]; linarith
  rw [majF_apply, step9_eq_one _ ha, step9_eq_zero _ hb, sub_zero]

lemma contDiff_sOf (a b : ℝ) : ContDiff ℝ 4 (sOf a b) := by
  have h : ContDiff ℝ 4 (fun u : ℝ => a * u + b) := by fun_prop
  exact step9_props.1.comp h

lemma contDiff_majF (M : ℝ) : ContDiff ℝ 4 (majF M) :=
  (contDiff_sOf (alpha M) b1).sub (contDiff_sOf (alpha M) b2)

/-! ## 7. The derivative bound for the majorant -/

lemma majF_deriv_bound (M : ℝ) (hM : 0 < M) (j : ℕ) (hj : j ≤ 4) (u : ℝ) :
    |iteratedDeriv j (majF M) u| ≤ Work.FITop4.cMaj j * M^(-(j:ℝ)) := by
  have hα : 0 ≤ alpha M := alpha_nonneg M hM
  have hMM : alpha M * M = 4/3 := alpha_mul_M M hM
  have up_le : ∀ v : ℝ, v ≤ M → alpha M * v ≤ 4/3 := by
    intro v hv; rw [← hMM]; exact mul_le_mul_of_nonneg_left hv hα
  have up_ge : ∀ v : ℝ, M ≤ v → 4/3 ≤ alpha M * v := by
    intro v hv; rw [← hMM]; exact mul_le_mul_of_nonneg_left hv hα
  interval_cases j
  · rw [iteratedDeriv_zero, cMaj_zero]
    simp only [Nat.cast_zero, neg_zero, Real.rpow_zero, mul_one]
    exact abs_le.mpr ⟨by linarith [majF_nonneg M hM u], majF_le_one M u⟩
  · rw [iteratedDeriv1_majF M u]
    rcases le_total u M with hu | hu
    · have hb : alpha M * u + b2 ≤ 0 := by rw [b2]; linarith [up_le u hu]
      rw [rh1_eq_zero_of_le (alpha M) b2 u hb, sub_zero]
      exact (abs_rh1_le (alpha M) b1 u hα).trans (key1 M hM)
    · have hb : 1 ≤ alpha M * u + b1 := by rw [b1]; linarith [up_ge u hu]
      rw [rh1_eq_zero_of_ge (alpha M) b1 u hb, zero_sub, abs_neg]
      exact (abs_rh1_le (alpha M) b2 u hα).trans (key1 M hM)
  · rw [iteratedDeriv2_majF M u]
    rcases le_total u M with hu | hu
    · have hb : alpha M * u + b2 ≤ 0 := by rw [b2]; linarith [up_le u hu]
      rw [rh2_eq_zero_of_le (alpha M) b2 u hb, sub_zero]
      exact (abs_rh2_le (alpha M) b1 u hα).trans (key2 M hM)
    · have hb : 1 ≤ alpha M * u + b1 := by rw [b1]; linarith [up_ge u hu]
      rw [rh2_eq_zero_of_ge (alpha M) b1 u hb, zero_sub, abs_neg]
      exact (abs_rh2_le (alpha M) b2 u hα).trans (key2 M hM)
  · rw [iteratedDeriv3_majF M u]
    rcases le_total u M with hu | hu
    · have hb : alpha M * u + b2 ≤ 0 := by rw [b2]; linarith [up_le u hu]
      rw [rh3_eq_zero_of_le (alpha M) b2 u hb, sub_zero]
      exact (abs_rh3_le (alpha M) b1 u hα).trans (key3 M hM)
    · have hb : 1 ≤ alpha M * u + b1 := by rw [b1]; linarith [up_ge u hu]
      rw [rh3_eq_zero_of_ge (alpha M) b1 u hb, zero_sub, abs_neg]
      exact (abs_rh3_le (alpha M) b2 u hα).trans (key3 M hM)
  · rw [iteratedDeriv4_majF M u]
    rcases le_total u M with hu | hu
    · have hb : alpha M * u + b2 ≤ 0 := by rw [b2]; linarith [up_le u hu]
      rw [rh4_eq_zero_of_le (alpha M) b2 u hb, sub_zero]
      exact (abs_rh4_le (alpha M) b1 u hα).trans (key4 M hM)
    · have hb : 1 ≤ alpha M * u + b1 := by rw [b1]; linarith [up_ge u hu]
      rw [rh4_eq_zero_of_ge (alpha M) b1 u hb, zero_sub, abs_neg]
      exact (abs_rh4_le (alpha M) b2 u hα).trans (key4 M hM)

/-! ## 8. The theorem -/

/-- **ROUND 6.3 satisfiability: the §5/§7 majorant with fixed constants, built directly.**
For `4 ≤ Pa.M` there is a *sequence* `f : ℤ → ℝ` with `Work.FITop4.IsMajorant6 Pa f`, i.e. an
explicit `C⁴` `F` with `F n = f n`, `|iteratedDeriv j F u| ≤ cMaj j · Pa.M^{-(j:ℝ)}` for `j ≤ 4`
(`Defs6.cMaj` = `1, 8, 64, 2^36, 2^48`), `0 ≤ f ≤ 1`, `f ≥ 1` on `Pa.M < |w|² ≤ 2·Pa.M`, and
`f u ≠ 0 → Pa.M/4 ≤ u ≤ 4·Pa.M`.

Any explicit clamped `C⁴` profile of width `≍ Pa.M` works.  A convenient choice, using a degree-9
clamped polynomial `p` with `p = 0` off `[0,1]`, `p = 1` at `1` (e.g. `p(t) = t⁵(126 - 420t + 540t²
- 315t³ + 70t⁴)` for `t ∈ [0,1]`, whose `p^{(j)}` vanish at both ends for `j ≤ 4`), is
`F u := p ((u - Pa.M/4)/(3*Pa.M/4)) * p ((4*Pa.M - u)/(3*Pa.M/4))`, for which the two rescaled
arguments sum to `5` and hence the ramps are disjoint: `F = 1` on `[Pa.M, 13·Pa.M/4] ⊇ (Pa.M, 2·Pa.M]`,
`F = 0` off `(Pa.M/4, 4·Pa.M)`, `0 ≤ F ≤ 1`; take `f n := F n`.  With the explicit `sup` bounds of
`p`'s derivatives and the rescaling `α = 4/(3·Pa.M)`, one gets `|F'| ≤ 6.7/Pa.M ≤ 8/Pa.M`,
`|F''| ≤ 60/Pa.M² ≤ 64/Pa.M²`, `|F'''| ≪ 2^36/Pa.M³`, `|F''''| ≪ 2^48/Pa.M⁴` (use the disjointness
of the ramps: the naive product-rule bound for `F''` overshoots `64`).  `step9`/`G`/`FM` in
`Witness6/Step9Defs.lean` are reusable here if the rescaling is adjusted to `3*Pa.M/4`. -/
theorem exists_isMajorant6_seq (Pa : Work.FITop.Params) (h : 4 ≤ Pa.M) :
    ∃ f : ℤ → ℝ, Work.FITop4.IsMajorant6 Pa f := by
  have hM : (0:ℝ) < Pa.M := by linarith
  refine ⟨fun n : ℤ => majF Pa.M (n : ℝ),
    ⟨majF Pa.M, contDiff_majF Pa.M, fun n => rfl, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro j hj u
    exact majF_deriv_bound Pa.M hM j hj u
  · intro u
    exact majF_nonneg Pa.M hM (u : ℝ)
  · intro u
    exact majF_le_one Pa.M (u : ℝ)
  · intro w h1 h2
    have hv1 : Pa.M ≤ ((Work.FIPlan.gnorm w : ℕ) : ℝ) := by linarith
    have hv2 : ((Work.FIPlan.gnorm w : ℕ) : ℝ) ≤ 2 * Pa.M := by linarith
    have hkey := majF_eq_one_on Pa.M hM ((Work.FIPlan.gnorm w : ℕ) : ℝ) hv1 hv2
    simp only [Int.cast_natCast]
    rw [hkey]
  · intro u hu
    constructor
    · by_contra hc
      push Not at hc
      have hz : majF Pa.M (u : ℝ) = 0 := majF_eq_zero_of_le Pa.M hM (u : ℝ) hc.le
      exact hu hz
    · by_contra hc
      push Not at hc
      have hz : majF Pa.M (u : ℝ) = 0 := majF_eq_zero_of_ge Pa.M hM (u : ℝ) hc.le
      exact hu hz

end

end Work.FITop4.Witness6
