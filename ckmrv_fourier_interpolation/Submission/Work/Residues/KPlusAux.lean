import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.Classical
import Submission.Work.Kernels.KernelGrowth
import Submission.Work.Kernels.ClassicalFacts.DeltaFun_basic
import Submission.Work.Kernels.KernelFacts.KPlus_S_add
import Submission.Work.Rigidity.AnnPlusWeightFourP
import Submission.Work.Asymptotics.jInvariantFun_imagAxis_atTop
import Submission.Work.Asymptotics.E2E4E6_combo_decay

noncomputable section
open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Residues.KPlusAux
open Work.Kernels

set_option maxHeartbeats 8000000

/-- The decay scale `ε τ = exp (-(2 π im τ))` at the cusp. -/
def eps (τ : ℍ) : ℝ := Real.exp (-(2 * Real.pi * τ.im))

lemma eps_pos (τ : ℍ) : 0 < eps τ := Real.exp_pos _

lemma eps_nonneg (τ : ℍ) : 0 ≤ eps τ := (eps_pos τ).le

/-- `J τ z = j τ - j z`. -/
def kpJ (τ z : ℍ) : ℂ := jInvariantFun τ - jInvariantFun z

/-- `h τ z = (Δ τ · (j τ - j z))⁻¹ = (E₄(τ)³ - Δ(τ) j(z))⁻¹`. -/
def kph (τ z : ℍ) : ℂ := (DeltaFun τ * kpJ τ z)⁻¹


lemma norm_mul_le_mul {x y : ℂ} {m n : ℝ} (hx : ‖x‖ ≤ m) (hy : ‖y‖ ≤ n) (hm : 0 ≤ m) :
    ‖x * y‖ ≤ m * n := by
  rw [norm_mul]; exact mul_le_mul hx hy (norm_nonneg y) hm

lemma norm_two_mul_le {x : ℂ} {m : ℝ} (hx : ‖x‖ ≤ m) : ‖(2:ℂ) * x‖ ≤ 2 * m := by
  rw [norm_mul, Complex.norm_ofNat]; linarith [norm_nonneg x]

/-- `‖x‖ * ‖y‖ ≤ m^2` when `‖x‖ ≤ m`, `‖y‖ ≤ m`, `0 ≤ m`. -/
lemma mul_norm_le_sq {x y : ℂ} {m : ℝ} (hx : ‖x‖ ≤ m) (hy : ‖y‖ ≤ m) (hm : 0 ≤ m) :
    ‖x‖ * ‖y‖ ≤ m ^ 2 := by
  have h : ‖x‖ * ‖y‖ ≤ m * m := mul_le_mul hx hy (norm_nonneg y) hm
  calc ‖x‖ * ‖y‖ ≤ m * m := h
    _ = m ^ 2 := by ring

/-- `‖v⁻¹ - 1‖ ≤ 2 m` when `‖v - 1‖ ≤ m ≤ 1/2`. -/
lemma norm_sub_one_inv_le {v : ℂ} {m : ℝ} (hm : 0 ≤ m) (hm1 : m ≤ 1/2)
    (hv : ‖v - 1‖ ≤ m) : ‖v⁻¹ - 1‖ ≤ 2 * m := by
  have h : |‖v‖ - 1| ≤ ‖v - 1‖ := by simpa using abs_norm_sub_norm_le v 1
  have h1 : (1:ℝ)/2 ≤ ‖v‖ := by
    have h2 : ‖v‖ - 1 ≤ m := le_trans (le_trans (le_abs_self _) h) hv
    have h3 : -(m:ℝ) ≤ ‖v‖ - 1 := le_trans (neg_le_neg hv) (le_trans (neg_le_neg h) (neg_abs_le _))
    linarith
  have hv0 : v ≠ 0 := by intro h0; rw [h0, norm_zero] at h1; linarith
  have h2 : ‖v⁻¹‖ ≤ 2 := by
    rw [norm_inv, inv_le_comm₀ (by linarith) (by norm_num : (0:ℝ) < 2)]
    norm_num
    linarith
  have h3 : v⁻¹ - 1 = (1 - v) * v⁻¹ := by field_simp
  rw [h3]
  calc ‖(1 - v) * v⁻¹‖ ≤ m * 2 := norm_mul_le_mul (by rw [norm_sub_rev]; exact hv) h2 hm
    _ = 2 * m := by ring

/-- `‖(a*b)⁻¹‖ ≤ B / ‖a‖` when `‖b⁻¹‖ ≤ B`. -/
lemma norm_mul_inv_le {a b : ℂ} {B : ℝ} (hb : ‖b⁻¹‖ ≤ B) :
    ‖(a * b)⁻¹‖ ≤ B / ‖a‖ := by
  rw [mul_inv, norm_mul, norm_inv]
  calc ‖a‖⁻¹ * ‖b⁻¹‖ ≤ ‖a‖⁻¹ * B := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = B / ‖a‖ := by ring

/-- `b⁻¹ = a * (a*b)⁻¹` for `a ≠ 0`. -/
lemma inv_eq_mul_inv_of_ne_zero {a b : ℂ} (ha : a ≠ 0) : b⁻¹ = a * (a * b)⁻¹ := by
  rcases eq_or_ne b 0 with hb | hb
  · rw [hb]; simp
  · field_simp

/-- `‖x * y‖ ≤ m^2` when `‖x‖ ≤ m`, `‖y‖ ≤ m`, `0 ≤ m`. -/
lemma norm_mul_le_sq {x y : ℂ} {m : ℝ} (hx : ‖x‖ ≤ m) (hy : ‖y‖ ≤ m) (hm : 0 ≤ m) :
    ‖x * y‖ ≤ m ^ 2 := by
  have h : ‖x‖ * ‖y‖ ≤ m * m := mul_le_mul hx hy (norm_nonneg y) hm
  rw [norm_mul]
  calc ‖x‖ * ‖y‖ ≤ m * m := h
    _ = m ^ 2 := by ring

/-- `‖x‖^2 ≤ m^2` when `‖x‖ ≤ m`, `0 ≤ m`. -/
lemma norm_sq_le {x : ℂ} {m : ℝ} (hx : ‖x‖ ≤ m) (hm : 0 ≤ m) : ‖x‖ ^ 2 ≤ m ^ 2 := by
  have h : ‖x‖ * ‖x‖ ≤ m * m := mul_le_mul hx hx (norm_nonneg x) hm
  calc ‖x‖ ^ 2 = ‖x‖ * ‖x‖ := by ring
    _ ≤ m * m := h
    _ = m ^ 2 := by ring

/-- `‖x‖ ≤ 2` when `‖x - 1‖ ≤ m ≤ 1`. -/
lemma norm_le_two {x : ℂ} {m : ℝ} (hx : ‖x - 1‖ ≤ m) (hm : m ≤ 1) : ‖x‖ ≤ 2 := by
  calc ‖x‖ = ‖(x - 1) + 1‖ := by ring_nf
    _ ≤ ‖x - 1‖ + ‖(1:ℂ)‖ := norm_add_le _ _
    _ ≤ m + 1 := by rw [norm_one]; linarith
    _ ≤ 2 := by linarith

/-- `‖1 + (x-1)‖ ≤ 2` when `‖x - 1‖ ≤ m ≤ 1`. -/
lemma norm_one_add_le {x : ℂ} {m : ℝ} (hx : ‖x - 1‖ ≤ m) (hm : m ≤ 1) :
    ‖(1:ℂ) + (x - 1)‖ ≤ 2 := by
  have h := norm_add_le (1:ℂ) (x - 1)
  rw [norm_one] at h
  linarith [h, hx, hm]

/-- `‖2 + (x-1)‖ ≤ 3` when `‖x - 1‖ ≤ m ≤ 1`. -/
lemma norm_two_add_le {x : ℂ} {m : ℝ} (hx : ‖x - 1‖ ≤ m) (hm : m ≤ 1) :
    ‖(2:ℂ) + (x - 1)‖ ≤ 3 := by
  have h := norm_add_le (2:ℂ) (x - 1)
  rw [Complex.norm_ofNat] at h
  linarith [h, hx, hm]

/-- `‖3 + (x-1)‖ ≤ 4` when `‖x - 1‖ ≤ m ≤ 1`. -/
lemma norm_three_add_le {x : ℂ} {m : ℝ} (hx : ‖x - 1‖ ≤ m) (hm : m ≤ 1) :
    ‖(3:ℂ) + (x - 1)‖ ≤ 4 := by
  have h := norm_add_le (3:ℂ) (x - 1)
  rw [Complex.norm_ofNat] at h
  linarith [h, hx, hm]

/-- `Q = e₄³ - e₆²`. -/
def Qf (e4 e6 : ℂ) : ℂ := e4 ^ 3 - e6 ^ 2

/-- `U = e₂e₆ - e₄²`. -/
def Uf (e2 e4 e6 : ℂ) : ℂ := e2 * e6 - e4 ^ 2

/-- `P = e₄e₆ - 2e₂e₄² + e₂²e₆`. -/
def Pf (e2 e4 e6 : ℂ) : ℂ := e4 * e6 - 2 * e2 * e4 ^ 2 + e2 ^ 2 * e6

/-- The `d = 24` `τ`-coefficient of the `φ̃₀` group. -/
def N0f (e2 e4 e6 h : ℂ) : ℂ :=
  (6:ℂ) * e4 ^ 2 * e6 - 12 * e2 * e4 ^ 3 + 5 * e2 * (e4 ^ 3 - e6 ^ 2)
    + e2 ^ 2 * e4 * e6 * (e4 ^ 3 - e6 ^ 2) * h + 6 * e2 ^ 2 * e4 * e6

/-- The `d = 24` `τ`-coefficient of the `φ̃₂` group. -/
def N2f (e2 e4 e6 h : ℂ) : ℂ :=
  e4 ^ 2 * e6 * ((e4 ^ 3 - e6 ^ 2) * h - 6) + e2 * (12 * e4 ^ 3 - 7 * (e4 ^ 3 - e6 ^ 2))
    - 6 * e2 ^ 2 * e4 * e6

/-- The `d = 24` constant coefficient of the `φ̃₀` group. -/
def M0f (e2 e4 e6 h : ℂ) : ℂ :=
  (-12 * e4 ^ 3 + 5 * (e4 ^ 3 - e6 ^ 2)) + 2 * e2 * e4 * e6 * ((e4 ^ 3 - e6 ^ 2) * h + 6)

/-- The `d = 24` constant coefficient of the `φ̃₂` group. -/
def M2f (e2 e4 e6 h : ℂ) : ℂ :=
  12 * e4 ^ 3 - 7 * (e4 ^ 3 - e6 ^ 2) - 12 * e2 * e4 * e6

/-- The linear part `12(e₂-1) - 3(e₄-1) - 2(e₆-1)` of `M0`. -/
def Linf (e2 e4 e6 : ℂ) : ℂ := 12 * (e2 - 1) - 3 * (e4 - 1) - 2 * (e6 - 1)

lemma norm_Qf_le {e4 e6 : ℂ} {K e : ℝ} (hKe : K * e ≤ 1)
    (h4 : ‖e4 - 1‖ ≤ K * e) (h6 : ‖e6 - 1‖ ≤ K * e) :
    ‖Qf e4 e6‖ ≤ 10 * (K * e) := by
  have hm0 : 0 ≤ K * e := le_trans (norm_nonneg (e4 - 1)) h4
  have hm1 : (K * e) ^ 2 ≤ K * e := by nlinarith [hm0, hKe]
  have hkey : Qf e4 e6 = (e4 - 1) * (3 + (e4 - 1) * (3 + (e4 - 1)))
      - (e6 - 1) * (2 + (e6 - 1)) := by simp only [Qf]; ring
  rw [hkey]
  -- inner factor
  have hinner1 : ‖(e4 - 1) * (3 + (e4 - 1))‖ ≤ (K*e) * 4 :=
    norm_mul_le_mul h4 (norm_three_add_le h4 hKe) hm0
  have hinner : ‖(3:ℂ) + (e4 - 1) * (3 + (e4 - 1))‖ ≤ 3 + (K*e) * 4 := by
    have h := norm_add_le (3:ℂ) ((e4 - 1) * (3 + (e4 - 1)))
    rw [Complex.norm_ofNat] at h
    linarith [h, hinner1]
  have hL : ‖(e4 - 1) * (3 + (e4 - 1) * (3 + (e4 - 1)))‖ ≤ 7 * (K * e) := by
    have h := norm_mul_le_mul h4 hinner hm0
    nlinarith [h, hm0, hKe]
  have hR : ‖(e6 - 1) * (2 + (e6 - 1))‖ ≤ 3 * (K * e) := by
    have h := norm_mul_le_mul h6 (norm_two_add_le h6 hKe) hm0
    nlinarith [h, hm0, hKe]
  have hE : (e4 - 1) * (3 + (e4 - 1) * (3 + (e4 - 1))) - (e6 - 1) * (2 + (e6 - 1))
      = (e4 - 1) * (3 + (e4 - 1) * (3 + (e4 - 1))) + -((e6 - 1) * (2 + (e6 - 1))) := by ring
  rw [hE]
  have h := norm_add_le ((e4 - 1) * (3 + (e4 - 1) * (3 + (e4 - 1))))
    (-((e6 - 1) * (2 + (e6 - 1))))
  rw [norm_neg] at h
  linarith [h, hL, hR]

lemma norm_Uf_le {e2 e4 e6 : ℂ} {K e : ℝ} (hKe : K * e ≤ 1)
    (h2 : ‖e2 - 1‖ ≤ K * e) (h4 : ‖e4 - 1‖ ≤ K * e) (h6 : ‖e6 - 1‖ ≤ K * e) :
    ‖Uf e2 e4 e6‖ ≤ 6 * (K * e) := by
  have hm0 : 0 ≤ K * e := le_trans (norm_nonneg (e2 - 1)) h2
  have hm1 : (K * e) ^ 2 ≤ K * e := by nlinarith [hm0, hKe]
  have hkey : Uf e2 e4 e6 = ((e2 - 1) + (e6 - 1) + (e2 - 1) * (e6 - 1))
      + (-(2 * (e4 - 1)) + -((e4 - 1) ^ 2)) := by simp only [Uf]; ring
  rw [hkey]
  have h1 : ‖(e2 - 1) + (e6 - 1) + (e2 - 1) * (e6 - 1)‖ ≤ 3 * (K*e) := by
    have hab : ‖(e2 - 1) * (e6 - 1)‖ ≤ (K*e)^2 := norm_mul_le_sq h2 h6 hm0
    have hE : (e2 - 1) + (e6 - 1) + (e2 - 1) * (e6 - 1)
        = ((e2 - 1) + (e6 - 1)) + (e2 - 1) * (e6 - 1) := by ring
    rw [hE]
    have h := norm_add_le ((e2 - 1) + (e6 - 1)) ((e2 - 1) * (e6 - 1))
    have h' := norm_add_le (e2 - 1) (e6 - 1)
    nlinarith [h, h', hab, hm0, hKe]
  have h2' : ‖-(2 * (e4 - 1)) + -((e4 - 1) ^ 2)‖ ≤ 3 * (K*e) := by
    have h4a : ‖(2:ℂ) * (e4 - 1)‖ ≤ 2 * (K*e) := norm_two_mul_le h4
    have h4b : ‖(e4 - 1) ^ 2‖ ≤ (K*e)^2 := by
      rw [norm_pow]; exact norm_sq_le h4 hm0
    have h := norm_add_le (-(2 * (e4 - 1))) (-((e4 - 1) ^ 2))
    rw [norm_neg, norm_neg] at h
    nlinarith [h, h4a, h4b, hm0, hKe]
  have h := norm_add_le ((e2 - 1) + (e6 - 1) + (e2 - 1) * (e6 - 1))
    (-(2 * (e4 - 1)) + -((e4 - 1) ^ 2))
  nlinarith [h, h1, h2', hm0, hKe]

lemma norm_P2_le {e2 e4 e6 : ℂ} {K e : ℝ} (hKe : K * e ≤ 1)
    (h2 : ‖e2 - 1‖ ≤ K * e) (h4 : ‖e4 - 1‖ ≤ K * e) (h6 : ‖e6 - 1‖ ≤ K * e) :
    ‖Pf e2 e4 e6 - (2 * (e6 - 1) - 3 * (e4 - 1))‖ ≤ 13 * (K * e) ^ 2 := by
  have hm0 : 0 ≤ K * e := le_trans (norm_nonneg (e2 - 1)) h2
  have hm1 : (K * e) ^ 2 ≤ K * e := by nlinarith [hm0, hKe]
  have hkey : Pf e2 e4 e6 - (2 * (e6 - 1) - 3 * (e4 - 1))
      = (e4 - 1) * ((e6 - 1) - 2 * (e4 - 1))
        + ((e2 - 1) * (-(4 * (e4 - 1)) - 2 * (e4 - 1) ^ 2 + 2 * (e6 - 1))
          + (e2 - 1) ^ 2 * (1 + (e6 - 1))) := by simp only [Pf]; ring
  rw [hkey]
  have hc1 : ‖(e6 - 1) - 2 * (e4 - 1)‖ ≤ 3 * (K * e) := by
    have hE : (e6 - 1) - 2 * (e4 - 1) = (e6 - 1) + -((2:ℂ) * (e4 - 1)) := by ring
    rw [hE]
    have h := norm_add_le (e6 - 1) (-((2:ℂ) * (e4 - 1)))
    rw [norm_neg] at h
    have h2' : ‖(2:ℂ) * (e4 - 1)‖ ≤ 2 * (K * e) := norm_two_mul_le h4
    linarith [h, h2', h6]
  have t1 : ‖(e4 - 1) * ((e6 - 1) - 2 * (e4 - 1))‖ ≤ 3 * (K*e)^2 := by
    have h := norm_mul_le_mul h4 hc1 hm0
    nlinarith [h, hm0, hKe]
  have hc2 : ‖-(4 * (e4 - 1)) - 2 * (e4 - 1) ^ 2 + 2 * (e6 - 1)‖ ≤ 8 * (K * e) := by
    have h4a : ‖(4:ℂ) * (e4 - 1)‖ ≤ 4 * (K*e) := by
      rw [norm_mul, Complex.norm_ofNat]; linarith [norm_nonneg (e4-1)]
    have h4b : ‖(2:ℂ) * (e4 - 1) ^ 2‖ ≤ 2 * (K*e) := by
      rw [norm_mul, Complex.norm_ofNat, norm_pow]
      nlinarith [norm_nonneg (e4-1), hm0, hm1]
    have h6a : ‖(2:ℂ) * (e6 - 1)‖ ≤ 2 * (K*e) := norm_two_mul_le h6
    have hE : -(4 * (e4 - 1)) - 2 * (e4 - 1) ^ 2 + 2 * (e6 - 1)
        = (-((4:ℂ) * (e4 - 1)) + -((2:ℂ) * (e4 - 1) ^ 2)) + (2:ℂ) * (e6 - 1) := by ring
    rw [hE]
    have t := norm_add_le (-((4:ℂ) * (e4 - 1)) + -((2:ℂ) * (e4 - 1) ^ 2)) ((2:ℂ) * (e6 - 1))
    have t2 := norm_add_le (-((4:ℂ) * (e4 - 1))) (-((2:ℂ) * (e4 - 1) ^ 2))
    rw [norm_neg, norm_neg] at t2
    linarith [t, t2, h4a, h4b, h6a]
  have t2 : ‖(e2 - 1) * (-(4 * (e4 - 1)) - 2 * (e4 - 1) ^ 2 + 2 * (e6 - 1))‖ ≤ 8 * (K*e)^2 := by
    have h := norm_mul_le_mul h2 hc2 hm0
    nlinarith [h, hm0, hKe]
  have t3 : ‖(e2 - 1) ^ 2 * (1 + (e6 - 1))‖ ≤ 2 * (K*e)^2 := by
    rw [norm_mul, norm_pow]
    have hc : ‖(1:ℂ) + (e6 - 1)‖ ≤ 2 := norm_one_add_le h6 hKe
    have hb : ‖e2 - 1‖ ^ 2 ≤ (K*e)^2 := norm_sq_le h2 hm0
    have hmain : ‖e2 - 1‖ ^ 2 * ‖(1:ℂ) + (e6 - 1)‖ ≤ (K*e)^2 * 2 :=
      mul_le_mul hb hc (norm_nonneg _) (by positivity)
    linarith [hmain]
  have hE : (e4 - 1) * ((e6 - 1) - 2 * (e4 - 1))
        + ((e2 - 1) * (-(4 * (e4 - 1)) - 2 * (e4 - 1) ^ 2 + 2 * (e6 - 1))
          + (e2 - 1) ^ 2 * (1 + (e6 - 1)))
      = ((e4 - 1) * ((e6 - 1) - 2 * (e4 - 1))
          + (e2 - 1) * (-(4 * (e4 - 1)) - 2 * (e4 - 1) ^ 2 + 2 * (e6 - 1)))
        + (e2 - 1) ^ 2 * (1 + (e6 - 1)) := by ring
  rw [hE]
  have t := norm_add_le ((e4 - 1) * ((e6 - 1) - 2 * (e4 - 1))
      + (e2 - 1) * (-(4 * (e4 - 1)) - 2 * (e4 - 1) ^ 2 + 2 * (e6 - 1)))
    ((e2 - 1) ^ 2 * (1 + (e6 - 1)))
  have t' := norm_add_le ((e4 - 1) * ((e6 - 1) - 2 * (e4 - 1)))
    ((e2 - 1) * (-(4 * (e4 - 1)) - 2 * (e4 - 1) ^ 2 + 2 * (e6 - 1)))
  nlinarith [t, t', t1, t2, t3, hm0, hKe]

lemma norm_e4Pf_plus_Qf_le {e2 e4 e6 : ℂ} {K e : ℝ} (hKe : K * e ≤ 1)
    (h2 : ‖e2 - 1‖ ≤ K * e) (h4 : ‖e4 - 1‖ ≤ K * e) (h6 : ‖e6 - 1‖ ≤ K * e) :
    ‖e4 * Pf e2 e4 e6 + Qf e4 e6‖ ≤ 60 * (K * e) ^ 2 := by
  have hm0 : 0 ≤ K * e := le_trans (norm_nonneg (e2 - 1)) h2
  have hm1 : (K * e) ^ 2 ≤ K * e := by nlinarith [hm0, hKe]
  have hP2 := norm_P2_le hKe h2 h4 h6
  have hkey : e4 * Pf e2 e4 e6 + Qf e4 e6
      = (Pf e2 e4 e6 - (2 * (e6 - 1) - 3 * (e4 - 1))) * (1 + (e4 - 1))
        + (2 * (e4 - 1) * (e6 - 1) + (e4 - 1) ^ 3 + -((e6 - 1) ^ 2)) := by
    simp only [Pf, Qf]; ring
  rw [hkey]
  have h1 : ‖(Pf e2 e4 e6 - (2 * (e6 - 1) - 3 * (e4 - 1))) * (1 + (e4 - 1))‖
      ≤ (13 * (K*e)^2) * 2 := by
    have h := norm_mul_le_mul hP2 (norm_one_add_le h4 hKe) (by positivity)
    linarith [h]
  have h2' : ‖2 * (e4 - 1) * (e6 - 1) + (e4 - 1) ^ 3 + -((e6 - 1) ^ 2)‖
      ≤ 2 * (K*e)^2 + (K*e)^3 + (K*e)^2 := by
    have h1' : ‖2 * (e4 - 1) * (e6 - 1)‖ ≤ 2 * (K*e)^2 := by
      rw [norm_mul, norm_mul, Complex.norm_ofNat]
      nlinarith [mul_norm_le_sq h4 h6 hm0, hm0]
    have h2'' : ‖(e4 - 1) ^ 3‖ ≤ (K*e)^3 := by
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) h4 3
    have h3 : ‖(e6 - 1) ^ 2‖ ≤ (K*e)^2 := by
      rw [norm_pow]; exact norm_sq_le h6 hm0
    have hE : 2 * (e4 - 1) * (e6 - 1) + (e4 - 1) ^ 3 + -((e6 - 1) ^ 2)
        = (2 * (e4 - 1) * (e6 - 1) + (e4 - 1) ^ 3) + -((e6 - 1) ^ 2) := by ring
    rw [hE]
    have t := norm_add_le (2 * (e4 - 1) * (e6 - 1) + (e4 - 1) ^ 3) (-((e6 - 1) ^ 2))
    have t' := norm_add_le (2 * (e4 - 1) * (e6 - 1)) ((e4 - 1) ^ 3)
    have h3' : ‖-((e6 - 1) ^ 2)‖ ≤ (K*e)^2 := by rw [norm_neg]; exact h3
    linarith [t, t', h1', h2'', h3']
  have hE : (Pf e2 e4 e6 - (2 * (e6 - 1) - 3 * (e4 - 1))) * (1 + (e4 - 1))
        + (2 * (e4 - 1) * (e6 - 1) + (e4 - 1) ^ 3 + -((e6 - 1) ^ 2))
      = ((Pf e2 e4 e6 - (2 * (e6 - 1) - 3 * (e4 - 1))) * (1 + (e4 - 1)))
        + (2 * (e4 - 1) * (e6 - 1) + (e4 - 1) ^ 3 + -((e6 - 1) ^ 2)) := rfl
  have t := norm_add_le ((Pf e2 e4 e6 - (2 * (e6 - 1) - 3 * (e4 - 1))) * (1 + (e4 - 1)))
    (2 * (e4 - 1) * (e6 - 1) + (e4 - 1) ^ 3 + -((e6 - 1) ^ 2))
  nlinarith [t, h1, h2', hm0, hKe]

lemma norm_F2_le {e2 e4 e6 h : ℂ} {K e : ℝ} (hKe : K * e ≤ 1)
    (h2 : ‖e2 - 1‖ ≤ K * e) (h4 : ‖e4 - 1‖ ≤ K * e) (h6 : ‖e6 - 1‖ ≤ K * e)
    (hh : ‖h - 1‖ ≤ K * e) :
    ‖5 * e2 - 6 + e2 ^ 2 * e4 * e6 * h‖ ≤ 40 * (K * e) := by
  have hm0 : 0 ≤ K * e := le_trans (norm_nonneg (e2 - 1)) h2
  have hm1 : (K * e) ^ 2 ≤ K * e := by nlinarith [hm0, hKe]
  have hkey : 5 * e2 - 6 + e2 ^ 2 * e4 * e6 * h
      = 5 * (e2 - 1) + (((2 * (e2 - 1) + (e2 - 1) ^ 2)
            + (1 + (e2 - 1)) ^ 2 * ((e4 - 1) + (e6 - 1) + (e4 - 1) * (e6 - 1)))
          + (e2 ^ 2 * e4 * e6) * (h - 1)) := by ring
  rw [hkey]
  have hA : ‖(2:ℂ) * (e2 - 1) + (e2 - 1) ^ 2‖ ≤ 3 * (K*e) := by
    have h1 : ‖(2:ℂ) * (e2 - 1)‖ ≤ 2 * (K*e) := norm_two_mul_le h2
    have h2' : ‖(e2 - 1) ^ 2‖ ≤ (K*e)^2 := by
      rw [norm_pow]; exact norm_sq_le h2 hm0
    have h := norm_add_le ((2:ℂ) * (e2 - 1)) ((e2 - 1) ^ 2)
    nlinarith [h, h1, h2', hm0, hKe]
  have hB : ‖(e4 - 1) + (e6 - 1) + (e4 - 1) * (e6 - 1)‖ ≤ 3 * (K*e) := by
    have h1 : ‖(e4 - 1) + (e6 - 1)‖ ≤ 2 * (K*e) := by
      have h := norm_add_le (e4 - 1) (e6 - 1)
      linarith [h]
    have h2' : ‖(e4 - 1) * (e6 - 1)‖ ≤ (K*e)^2 := norm_mul_le_sq h4 h6 hm0
    have hE : (e4 - 1) + (e6 - 1) + (e4 - 1) * (e6 - 1)
        = ((e4 - 1) + (e6 - 1)) + (e4 - 1) * (e6 - 1) := by ring
    rw [hE]
    have h := norm_add_le ((e4 - 1) + (e6 - 1)) ((e4 - 1) * (e6 - 1))
    nlinarith [h, h1, h2', hm0, hKe]
  have hC : ‖(1 + (e2 - 1)) ^ 2‖ ≤ 4 := by
    rw [norm_pow]
    have h := norm_one_add_le h2 hKe
    nlinarith [norm_nonneg ((1:ℂ) + (e2 - 1)), h]
  have hS : ‖e2 ^ 2 * e4 * e6‖ ≤ 16 := by
    have h2' : ‖e2‖ ≤ 2 := norm_le_two h2 hKe
    have h4' : ‖e4‖ ≤ 2 := norm_le_two h4 hKe
    have h6' : ‖e6‖ ≤ 2 := norm_le_two h6 hKe
    rw [norm_mul, norm_mul, norm_pow]
    have h1 : ‖e2‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg e2, h2']
    have h2'' : ‖e2‖ ^ 2 * ‖e4‖ ≤ 4 * 2 := mul_le_mul h1 h4' (norm_nonneg e4) (by norm_num)
    have h3 : ‖e2‖ ^ 2 * ‖e4‖ * ‖e6‖ ≤ 4 * 2 * 2 := mul_le_mul h2'' h6' (norm_nonneg e6) (by norm_num)
    linarith [h3]
  have t1 : ‖5 * (e2 - 1)‖ ≤ 5 * (K*e) := by
    rw [norm_mul, Complex.norm_ofNat]; linarith [norm_nonneg (e2-1)]
  have t2 : ‖(2 * (e2 - 1) + (e2 - 1) ^ 2)
      + (1 + (e2 - 1)) ^ 2 * ((e4 - 1) + (e6 - 1) + (e4 - 1) * (e6 - 1))‖
      ≤ 3 * (K*e) + 4 * (3 * (K*e)) := by
    have h34 : ‖(1 + (e2 - 1)) ^ 2 * ((e4 - 1) + (e6 - 1) + (e4 - 1) * (e6 - 1))‖
        ≤ 4 * (3 * (K*e)) := norm_mul_le_mul hC hB (by norm_num)
    have h := norm_add_le ((2 * (e2 - 1) + (e2 - 1) ^ 2))
      ((1 + (e2 - 1)) ^ 2 * ((e4 - 1) + (e6 - 1) + (e4 - 1) * (e6 - 1)))
    linarith [h, hA, h34]
  have t3 : ‖e2 ^ 2 * e4 * e6 * (h - 1)‖ ≤ 16 * (K*e) := by
    rw [norm_mul]; exact mul_le_mul hS hh (norm_nonneg _) (by norm_num)
  have hE : 5 * (e2 - 1) + (((2 * (e2 - 1) + (e2 - 1) ^ 2)
          + (1 + (e2 - 1)) ^ 2 * ((e4 - 1) + (e6 - 1) + (e4 - 1) * (e6 - 1)))
        + (e2 ^ 2 * e4 * e6) * (h - 1))
      = (5 * (e2 - 1)) + (((2 * (e2 - 1) + (e2 - 1) ^ 2)
          + (1 + (e2 - 1)) ^ 2 * ((e4 - 1) + (e6 - 1) + (e4 - 1) * (e6 - 1)))
        + (e2 ^ 2 * e4 * e6) * (h - 1)) := rfl
  have t := norm_add_le (5 * (e2 - 1)) (((2 * (e2 - 1) + (e2 - 1) ^ 2)
      + (1 + (e2 - 1)) ^ 2 * ((e4 - 1) + (e6 - 1) + (e4 - 1) * (e6 - 1)))
      + (e2 ^ 2 * e4 * e6) * (h - 1))
  have t' := norm_add_le ((2 * (e2 - 1) + (e2 - 1) ^ 2)
      + (1 + (e2 - 1)) ^ 2 * ((e4 - 1) + (e6 - 1) + (e4 - 1) * (e6 - 1)))
    ((e2 ^ 2 * e4 * e6) * (h - 1))
  have hE' : (2 * (e2 - 1) + (e2 - 1) ^ 2)
      + (1 + (e2 - 1)) ^ 2 * ((e4 - 1) + (e6 - 1) + (e4 - 1) * (e6 - 1))
      + (e2 ^ 2 * e4 * e6) * (h - 1)
      = ((2 * (e2 - 1) + (e2 - 1) ^ 2)
        + (1 + (e2 - 1)) ^ 2 * ((e4 - 1) + (e6 - 1) + (e4 - 1) * (e6 - 1)))
        + (e2 ^ 2 * e4 * e6) * (h - 1) := rfl
  linarith [t, t', t1, t2, t3, hm0, hKe]

lemma norm_G2_le {e2 e4 e6 h : ℂ} {K e : ℝ} (hKe : K * e ≤ 1)
    (h2 : ‖e2 - 1‖ ≤ K * e) (h4 : ‖e4 - 1‖ ≤ K * e) (h6 : ‖e6 - 1‖ ≤ K * e)
    (hh : ‖h - 1‖ ≤ K * e) :
    ‖e4 ^ 2 * e6 * h - 7 * e2 + 6‖ ≤ 30 * (K * e) := by
  have hm0 : 0 ≤ K * e := le_trans (norm_nonneg (e2 - 1)) h2
  have hm1 : (K * e) ^ 2 ≤ K * e := by nlinarith [hm0, hKe]
  have hkey : e4 ^ 2 * e6 * h - 7 * e2 + 6
      = (((2 * (e4 - 1) + (e4 - 1) ^ 2) + (1 + (e4 - 1)) ^ 2 * (e6 - 1))
          + e4 ^ 2 * e6 * (h - 1)) + (-(7 * (e2 - 1))) := by ring
  rw [hkey]
  have hA : ‖2 * (e4 - 1) + (e4 - 1) ^ 2‖ ≤ 3 * (K*e) := by
    have h1 : ‖(2:ℂ) * (e4 - 1)‖ ≤ 2 * (K*e) := norm_two_mul_le h4
    have h2' : ‖(e4 - 1) ^ 2‖ ≤ (K*e)^2 := by
      rw [norm_pow]; exact norm_sq_le h4 hm0
    have h := norm_add_le ((2:ℂ) * (e4 - 1)) ((e4 - 1) ^ 2)
    nlinarith [h, h1, h2', hm0, hKe]
  have hB : ‖(1 + (e4 - 1)) ^ 2 * (e6 - 1)‖ ≤ 4 * (K*e) := by
    have hC : ‖(1 + (e4 - 1)) ^ 2‖ ≤ 4 := by
      rw [norm_pow]
      have h := norm_one_add_le h4 hKe
      nlinarith [norm_nonneg ((1:ℂ) + (e4 - 1)), h]
    have h := norm_mul_le_mul hC h6 (by norm_num)
    linarith [h]
  have hS : ‖e4 ^ 2 * e6‖ ≤ 16 := by
    have h4' : ‖e4‖ ≤ 2 := norm_le_two h4 hKe
    have h6' : ‖e6‖ ≤ 2 := norm_le_two h6 hKe
    rw [norm_mul, norm_pow]
    have h1 : ‖e4‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg e4, h4']
    have h2'' : ‖e4‖ ^ 2 * ‖e6‖ ≤ 4 * 2 := mul_le_mul h1 h6' (norm_nonneg e6) (by norm_num)
    linarith [h2'']
  have hC : ‖e4 ^ 2 * e6 * (h - 1)‖ ≤ 16 * (K*e) := by
    have h := norm_mul_le_mul hS hh (by norm_num)
    linarith [h]
  have hD : ‖(2 * (e4 - 1) + (e4 - 1) ^ 2) + (1 + (e4 - 1)) ^ 2 * (e6 - 1)‖ ≤ 3 * (K*e) + 4 * (K*e) := by
    have h := norm_add_le ((2 * (e4 - 1) + (e4 - 1) ^ 2)) ((1 + (e4 - 1)) ^ 2 * (e6 - 1))
    linarith [h, hA, hB]
  have hE : ‖((2 * (e4 - 1) + (e4 - 1) ^ 2) + (1 + (e4 - 1)) ^ 2 * (e6 - 1))
      + e4 ^ 2 * e6 * (h - 1)‖ ≤ (3 * (K*e) + 4 * (K*e)) + 16 * (K*e) := by
    have h := norm_add_le ((2 * (e4 - 1) + (e4 - 1) ^ 2) + (1 + (e4 - 1)) ^ 2 * (e6 - 1))
      (e4 ^ 2 * e6 * (h - 1))
    linarith [h, hD, hC]
  have hF : ‖(7:ℂ) * (e2 - 1)‖ ≤ 7 * (K*e) := by
    rw [norm_mul, Complex.norm_ofNat]; linarith [norm_nonneg (e2-1)]
  have hFn : ‖-((7:ℂ) * (e2 - 1))‖ ≤ 7 * (K*e) := by rw [norm_neg]; exact hF
  have h := norm_add_le (((2 * (e4 - 1) + (e4 - 1) ^ 2) + (1 + (e4 - 1)) ^ 2 * (e6 - 1))
      + e4 ^ 2 * e6 * (h - 1)) (-(7 * (e2 - 1)))
  linarith [h, hE, hFn]

lemma norm_N0f_le {e2 e4 e6 h : ℂ} {K e : ℝ} (hKe : K * e ≤ 1)
    (h2 : ‖e2 - 1‖ ≤ K * e) (h4 : ‖e4 - 1‖ ≤ K * e) (h6 : ‖e6 - 1‖ ≤ K * e)
    (hh : ‖h - 1‖ ≤ K * e) :
    ‖N0f e2 e4 e6 h‖ ≤ 800 * (K * e) ^ 2 := by
  have hm0 : 0 ≤ K * e := le_trans (norm_nonneg (e2 - 1)) h2
  have hA := norm_e4Pf_plus_Qf_le hKe h2 h4 h6
  have hQ := norm_Qf_le hKe h4 h6
  have hF := norm_F2_le hKe h2 h4 h6 hh
  have hkey : N0f e2 e4 e6 h
      = (6:ℂ) * (e4 * Pf e2 e4 e6 + Qf e4 e6)
        + Qf e4 e6 * (5 * e2 - 6 + e2 ^ 2 * e4 * e6 * h) := by
    simp only [N0f, Pf, Qf]; ring
  rw [hkey]
  have h1 : ‖(6:ℂ) * (e4 * Pf e2 e4 e6 + Qf e4 e6)‖ ≤ 6 * (60 * (K*e)^2) := by
    rw [norm_mul, Complex.norm_ofNat]
    exact mul_le_mul_of_nonneg_left hA (by norm_num)
  have h2' : ‖Qf e4 e6 * (5 * e2 - 6 + e2 ^ 2 * e4 * e6 * h)‖ ≤ (10 * (K*e)) * (40 * (K*e)) :=
    norm_mul_le_mul hQ hF (by positivity)
  have t := norm_add_le ((6:ℂ) * (e4 * Pf e2 e4 e6 + Qf e4 e6))
    (Qf e4 e6 * (5 * e2 - 6 + e2 ^ 2 * e4 * e6 * h))
  nlinarith [t, h1, h2', hm0, hKe]

lemma norm_N2f_le {e2 e4 e6 h : ℂ} {K e : ℝ} (hKe : K * e ≤ 1)
    (h2 : ‖e2 - 1‖ ≤ K * e) (h4 : ‖e4 - 1‖ ≤ K * e) (h6 : ‖e6 - 1‖ ≤ K * e)
    (hh : ‖h - 1‖ ≤ K * e) :
    ‖N2f e2 e4 e6 h‖ ≤ 800 * (K * e) ^ 2 := by
  have hm0 : 0 ≤ K * e := le_trans (norm_nonneg (e2 - 1)) h2
  have hA := norm_e4Pf_plus_Qf_le hKe h2 h4 h6
  have hQ := norm_Qf_le hKe h4 h6
  have hG := norm_G2_le hKe h2 h4 h6 hh
  have hkey : N2f e2 e4 e6 h
      = -((6:ℂ) * (e4 * Pf e2 e4 e6 + Qf e4 e6))
        + Qf e4 e6 * (e4 ^ 2 * e6 * h - 7 * e2 + 6) := by
    simp only [N2f, Pf, Qf]; ring
  rw [hkey]
  have h1 : ‖(6:ℂ) * (e4 * Pf e2 e4 e6 + Qf e4 e6)‖ ≤ 6 * (60 * (K*e)^2) := by
    rw [norm_mul, Complex.norm_ofNat]
    exact mul_le_mul_of_nonneg_left hA (by norm_num)
  have h1n : ‖-((6:ℂ) * (e4 * Pf e2 e4 e6 + Qf e4 e6))‖ ≤ 6 * (60 * (K*e)^2) := by
    rw [norm_neg]; exact h1
  have h2' : ‖Qf e4 e6 * (e4 ^ 2 * e6 * h - 7 * e2 + 6)‖ ≤ (10 * (K*e)) * (30 * (K*e)) :=
    norm_mul_le_mul hQ hG (by positivity)
  have t := norm_add_le (-((6:ℂ) * (e4 * Pf e2 e4 e6 + Qf e4 e6)))
    (Qf e4 e6 * (e4 ^ 2 * e6 * h - 7 * e2 + 6))
  nlinarith [t, h1n, h2', hm0, hKe]

lemma norm_R0_le {e2 e4 e6 : ℂ} {K e : ℝ} (hKe : K * e ≤ 1)
    (h2 : ‖e2 - 1‖ ≤ K * e) (h4 : ‖e4 - 1‖ ≤ K * e) (h6 : ‖e6 - 1‖ ≤ K * e) :
    ‖12 * ((e2 - 1) * (e6 - 1) - (e4 - 1) ^ 2)
      + 7 * (3 * (e4 - 1) ^ 2 + (e4 - 1) ^ 3 - (e6 - 1) ^ 2)‖ ≤ 60 * (K * e) ^ 2 := by
  have hm0 : 0 ≤ K * e := le_trans (norm_nonneg (e2 - 1)) h2
  have hm1 : (K * e) ^ 2 ≤ K * e := by nlinarith [hm0, hKe]
  have h1 : ‖(e2 - 1) * (e6 - 1)‖ ≤ (K*e)^2 := norm_mul_le_sq h2 h6 hm0
  have h2' : ‖(e4 - 1) ^ 2‖ ≤ (K*e)^2 := by rw [norm_pow]; exact norm_sq_le h4 hm0
  have hA : ‖(e2 - 1) * (e6 - 1) - (e4 - 1) ^ 2‖ ≤ 2 * (K*e)^2 := by
    have hE : (e2 - 1) * (e6 - 1) - (e4 - 1) ^ 2 = (e2 - 1) * (e6 - 1) + -((e4 - 1) ^ 2) := by ring
    rw [hE]
    have hn : ‖-((e4 - 1) ^ 2)‖ ≤ (K*e)^2 := by rw [norm_neg]; exact h2'
    have t := norm_add_le ((e2 - 1) * (e6 - 1)) (-((e4 - 1) ^ 2))
    linarith [t, h1, hn]
  have h3 : ‖(e4 - 1) ^ 3‖ ≤ (K*e)^2 := by
    rw [norm_pow]
    have h5 : ‖e4 - 1‖ ^ 3 ≤ (K*e)^3 := pow_le_pow_left₀ (norm_nonneg _) h4 3
    have h6 : (K*e)^3 ≤ (K*e)^2 := by nlinarith [hm0, hKe, hm1, sq_nonneg (K*e)]
    linarith [h5, h6]
  have hB : ‖3 * (e4 - 1) ^ 2 + (e4 - 1) ^ 3 - (e6 - 1) ^ 2‖ ≤ 5 * (K*e)^2 := by
    have h4a : ‖(3:ℂ) * (e4 - 1) ^ 2‖ ≤ 3 * (K*e)^2 := by
      rw [norm_mul, Complex.norm_ofNat]
      exact mul_le_mul_of_nonneg_left h2' (by norm_num)
    have h6a : ‖(e6 - 1) ^ 2‖ ≤ (K*e)^2 := by rw [norm_pow]; exact norm_sq_le h6 hm0
    have h6n : ‖-((e6 - 1) ^ 2)‖ ≤ (K*e)^2 := by rw [norm_neg]; exact h6a
    have hE : (3:ℂ) * (e4 - 1) ^ 2 + (e4 - 1) ^ 3 - (e6 - 1) ^ 2
        = ((3:ℂ) * (e4 - 1) ^ 2 + (e4 - 1) ^ 3) + -((e6 - 1) ^ 2) := by ring
    rw [hE]
    have t := norm_add_le ((3:ℂ) * (e4 - 1) ^ 2 + (e4 - 1) ^ 3) (-((e6 - 1) ^ 2))
    have t' := norm_add_le ((3:ℂ) * (e4 - 1) ^ 2) ((e4 - 1) ^ 3)
    linarith [t, t', h4a, h3, h6n]
  have h12 : ‖(12:ℂ) * ((e2 - 1) * (e6 - 1) - (e4 - 1) ^ 2)‖ ≤ 12 * (2 * (K*e)^2) := by
    rw [norm_mul, Complex.norm_ofNat]
    exact mul_le_mul_of_nonneg_left hA (by norm_num)
  have h7 : ‖(7:ℂ) * (3 * (e4 - 1) ^ 2 + (e4 - 1) ^ 3 - (e6 - 1) ^ 2)‖ ≤ 7 * (5 * (K*e)^2) := by
    rw [norm_mul, Complex.norm_ofNat]
    exact mul_le_mul_of_nonneg_left hB (by norm_num)
  have t := norm_add_le ((12:ℂ) * ((e2 - 1) * (e6 - 1) - (e4 - 1) ^ 2))
    ((7:ℂ) * (3 * (e4 - 1) ^ 2 + (e4 - 1) ^ 3 - (e6 - 1) ^ 2))
  nlinarith [t, h12, h7, hm0, hKe]

lemma norm_e2e4e6h_sub_one_le {e2 e4 e6 h : ℂ} {K e : ℝ} (hKe : K * e ≤ 1)
    (h2 : ‖e2 - 1‖ ≤ K * e) (h4 : ‖e4 - 1‖ ≤ K * e) (h6 : ‖e6 - 1‖ ≤ K * e)
    (hh : ‖h - 1‖ ≤ K * e) :
    ‖e2 * e4 * e6 * h - 1‖ ≤ 25 * (K * e) := by
  have hm0 : 0 ≤ K * e := le_trans (norm_nonneg (e2 - 1)) h2
  have hm1 : (K * e) ^ 2 ≤ K * e := by nlinarith [hm0, hKe]
  have hkey : e2 * e4 * e6 * h - 1
      = ((e2 - 1) + (e4 - 1) + (e6 - 1))
        + (((e2 - 1) * (e4 - 1) + (e2 - 1) * (e6 - 1) + (e4 - 1) * (e6 - 1))
          + (e2 - 1) * (e4 - 1) * (e6 - 1))
        + e2 * e4 * e6 * (h - 1) := by
    ring
  rw [hkey]
  have h1 : ‖(e2 - 1) + (e4 - 1) + (e6 - 1)‖ ≤ 3 * (K*e) := by
    have hE : (e2 - 1) + (e4 - 1) + (e6 - 1) = ((e2 - 1) + (e4 - 1)) + (e6 - 1) := by ring
    rw [hE]
    have t := norm_add_le ((e2 - 1) + (e4 - 1)) (e6 - 1)
    have t' := norm_add_le (e2 - 1) (e4 - 1)
    linarith [t, t', h2, h4, h6]
  have hab : ‖(e2 - 1) * (e4 - 1)‖ ≤ (K*e)^2 := norm_mul_le_sq h2 h4 hm0
  have hac : ‖(e2 - 1) * (e6 - 1)‖ ≤ (K*e)^2 := norm_mul_le_sq h2 h6 hm0
  have hbc : ‖(e4 - 1) * (e6 - 1)‖ ≤ (K*e)^2 := norm_mul_le_sq h4 h6 hm0
  have habc : ‖(e2 - 1) * (e4 - 1) * (e6 - 1)‖ ≤ (K*e)^2 := by
    rw [norm_mul]
    have h := mul_le_mul (norm_mul_le_sq h2 h4 hm0) h6 (norm_nonneg _) (by positivity)
    nlinarith [h, hm0, hm1, hKe]
  have h2'' : ‖((e2 - 1) * (e4 - 1) + (e2 - 1) * (e6 - 1) + (e4 - 1) * (e6 - 1))
      + (e2 - 1) * (e4 - 1) * (e6 - 1)‖ ≤ 4 * (K*e)^2 := by
    have hE : (e2 - 1) * (e4 - 1) + (e2 - 1) * (e6 - 1) + (e4 - 1) * (e6 - 1)
        = ((e2 - 1) * (e4 - 1) + (e2 - 1) * (e6 - 1)) + (e4 - 1) * (e6 - 1) := by ring
    rw [hE]
    have t := norm_add_le (((e2 - 1) * (e4 - 1) + (e2 - 1) * (e6 - 1)) + (e4 - 1) * (e6 - 1))
      ((e2 - 1) * (e4 - 1) * (e6 - 1))
    have t' := norm_add_le ((e2 - 1) * (e4 - 1) + (e2 - 1) * (e6 - 1)) ((e4 - 1) * (e6 - 1))
    have t'' := norm_add_le ((e2 - 1) * (e4 - 1)) ((e2 - 1) * (e6 - 1))
    nlinarith [t, t', t'', hab, hac, hbc, habc, hm0, hKe]
  have hS : ‖e2 * e4 * e6‖ ≤ 16 := by
    have h2' : ‖e2‖ ≤ 2 := norm_le_two h2 hKe
    have h4' : ‖e4‖ ≤ 2 := norm_le_two h4 hKe
    have h6' : ‖e6‖ ≤ 2 := norm_le_two h6 hKe
    rw [norm_mul, norm_mul]
    have h1' : ‖e2‖ * ‖e4‖ ≤ 4 := by nlinarith [norm_nonneg e2, norm_nonneg e4, h2', h4']
    have h2b : ‖e2‖ * ‖e4‖ * ‖e6‖ ≤ 4 * 2 := mul_le_mul h1' h6' (norm_nonneg e6) (by norm_num)
    linarith [h2b]
  have hT2 : ‖e2 * e4 * e6 * (h - 1)‖ ≤ 16 * (K*e) := by
    have h := norm_mul_le_mul hS hh (by norm_num)
    linarith [h]
  have hE2 : ((e2 - 1) + (e4 - 1) + (e6 - 1))
        + (((e2 - 1) * (e4 - 1) + (e2 - 1) * (e6 - 1) + (e4 - 1) * (e6 - 1))
          + (e2 - 1) * (e4 - 1) * (e6 - 1)) + e2 * e4 * e6 * (h - 1)
      = ((e2 - 1) + (e4 - 1) + (e6 - 1))
        + ((((e2 - 1) * (e4 - 1) + (e2 - 1) * (e6 - 1) + (e4 - 1) * (e6 - 1))
          + (e2 - 1) * (e4 - 1) * (e6 - 1)) + e2 * e4 * e6 * (h - 1)) := by ring
  rw [hE2]
  have t := norm_add_le ((e2 - 1) + (e4 - 1) + (e6 - 1))
    ((((e2 - 1) * (e4 - 1) + (e2 - 1) * (e6 - 1) + (e4 - 1) * (e6 - 1))
      + (e2 - 1) * (e4 - 1) * (e6 - 1)) + e2 * e4 * e6 * (h - 1))
  have t' := norm_add_le (((e2 - 1) * (e4 - 1) + (e2 - 1) * (e6 - 1) + (e4 - 1) * (e6 - 1))
      + (e2 - 1) * (e4 - 1) * (e6 - 1)) (e2 * e4 * e6 * (h - 1))
  nlinarith [t, t', h1, h2'', hT2, hm0, hKe]

lemma norm_M0f_rest_le {e2 e4 e6 h : ℂ} {K e : ℝ} (hKe : K * e ≤ 1)
    (h2 : ‖e2 - 1‖ ≤ K * e) (h4 : ‖e4 - 1‖ ≤ K * e) (h6 : ‖e6 - 1‖ ≤ K * e)
    (hh : ‖h - 1‖ ≤ K * e) :
    ‖M0f e2 e4 e6 h - Linf e2 e4 e6‖ ≤ 700 * (K * e) ^ 2 := by
  have hm0 : 0 ≤ K * e := le_trans (norm_nonneg (e2 - 1)) h2
  have hR := norm_R0_le hKe h2 h4 h6
  have hU := norm_Uf_le hKe h2 h4 h6
  have hQ := norm_Qf_le hKe h4 h6
  have hSh := norm_e2e4e6h_sub_one_le hKe h2 h4 h6 hh
  have hkey : M0f e2 e4 e6 h - Linf e2 e4 e6
      = (12 * ((e2 - 1) * (e6 - 1) - (e4 - 1) ^ 2)
          + 7 * (3 * (e4 - 1) ^ 2 + (e4 - 1) ^ 3 - (e6 - 1) ^ 2))
        + ((12:ℂ) * ((e4 - 1) * Uf e2 e4 e6) + (2:ℂ) * Qf e4 e6 * (e2 * e4 * e6 * h - 1)) := by
    simp only [M0f, Linf, Uf, Qf]; ring
  rw [hkey]
  have hbU : ‖(e4 - 1) * Uf e2 e4 e6‖ ≤ (K * e) * (6 * (K * e)) := norm_mul_le_mul h4 hU hm0
  have h12 : ‖(12:ℂ) * ((e4 - 1) * Uf e2 e4 e6)‖ ≤ 12 * ((K * e) * (6 * (K * e))) := by
    rw [norm_mul, Complex.norm_ofNat]
    exact mul_le_mul_of_nonneg_left hbU (by norm_num)
  have h2Q : ‖(2:ℂ) * Qf e4 e6 * (e2 * e4 * e6 * h - 1)‖ ≤ 2 * ((10 * (K * e)) * (25 * (K * e))) := by
    rw [norm_mul, norm_mul, Complex.norm_ofNat]
    have h := mul_le_mul hQ hSh (norm_nonneg _) (by positivity)
    linarith [h, hm0, hKe]
  have t := norm_add_le (12 * ((e2 - 1) * (e6 - 1) - (e4 - 1) ^ 2)
      + 7 * (3 * (e4 - 1) ^ 2 + (e4 - 1) ^ 3 - (e6 - 1) ^ 2))
    ((12:ℂ) * ((e4 - 1) * Uf e2 e4 e6) + (2:ℂ) * Qf e4 e6 * (e2 * e4 * e6 * h - 1))
  have t' := norm_add_le ((12:ℂ) * ((e4 - 1) * Uf e2 e4 e6))
    ((2:ℂ) * Qf e4 e6 * (e2 * e4 * e6 * h - 1))
  nlinarith [t, t', hR, h12, h2Q, hm0, hKe]

lemma norm_M2f_rest_le {e2 e4 e6 h : ℂ} {K e : ℝ} (hKe : K * e ≤ 1)
    (h2 : ‖e2 - 1‖ ≤ K * e) (h4 : ‖e4 - 1‖ ≤ K * e) (h6 : ‖e6 - 1‖ ≤ K * e) :
    ‖M2f e2 e4 e6 h + Linf e2 e4 e6‖ ≤ 200 * (K * e) ^ 2 := by
  have hm0 : 0 ≤ K * e := le_trans (norm_nonneg (e2 - 1)) h2
  have hR := norm_R0_le hKe h2 h4 h6
  have hU := norm_Uf_le hKe h2 h4 h6
  have hkey : M2f e2 e4 e6 h + Linf e2 e4 e6
      = -((12 * ((e2 - 1) * (e6 - 1) - (e4 - 1) ^ 2)
          + 7 * (3 * (e4 - 1) ^ 2 + (e4 - 1) ^ 3 - (e6 - 1) ^ 2))
        + (12:ℂ) * ((e4 - 1) * Uf e2 e4 e6)) := by
    simp only [M2f, Linf, Uf, Qf]; ring
  rw [hkey]
  have hbU : ‖(e4 - 1) * Uf e2 e4 e6‖ ≤ (K * e) * (6 * (K * e)) := norm_mul_le_mul h4 hU hm0
  have h12 : ‖(12:ℂ) * ((e4 - 1) * Uf e2 e4 e6)‖ ≤ 12 * ((K * e) * (6 * (K * e))) := by
    rw [norm_mul, Complex.norm_ofNat]
    exact mul_le_mul_of_nonneg_left hbU (by norm_num)
  have t := norm_add_le (12 * ((e2 - 1) * (e6 - 1) - (e4 - 1) ^ 2)
      + 7 * (3 * (e4 - 1) ^ 2 + (e4 - 1) ^ 3 - (e6 - 1) ^ 2))
    ((12:ℂ) * ((e4 - 1) * Uf e2 e4 e6))
  rw [norm_neg]
  nlinarith [t, hR, h12, hm0, hKe]

lemma norm_Q2h_le {e4 e6 h : ℂ} {K e : ℝ} (hKe : K * e ≤ 1)
    (h4 : ‖e4 - 1‖ ≤ K * e) (h6 : ‖e6 - 1‖ ≤ K * e) (hh2 : ‖h‖ ≤ 2) :
    ‖Qf e4 e6 ^ 2 * h‖ ≤ 300 * (K * e) ^ 2 := by
  have hm0 : 0 ≤ K * e := le_trans (norm_nonneg (e4 - 1)) h4
  have hQ := norm_Qf_le hKe h4 h6
  rw [norm_mul, norm_pow]
  nlinarith [hQ, hh2, norm_nonneg (Qf e4 e6), hm0, hKe]

lemma norm_A8_le {e2 e4 e6 h : ℂ} {K e : ℝ} (hKe : K * e ≤ 1)
    (h2 : ‖e2 - 1‖ ≤ K * e) (h4 : ‖e4 - 1‖ ≤ K * e) (h6 : ‖e6 - 1‖ ≤ K * e)
    (hh : ‖h - 1‖ ≤ K * e) :
    ‖e6 - 2 * e4 * e2 + e2 ^ 2 * e4 ^ 2 * e6 * h‖ ≤ 100 * (K * e) := by
  have hm0 : 0 ≤ K * e := le_trans (norm_nonneg (e2 - 1)) h2
  have hm1 : (K * e) ^ 2 ≤ K * e := by nlinarith [hm0, hKe]
  have hu : ‖e2 * e4 - 1‖ ≤ 3 * (K * e) := by
    have h12 : ‖(e2 - 1) + (e4 - 1)‖ ≤ K * e + K * e := by
      calc ‖(e2 - 1) + (e4 - 1)‖ ≤ ‖e2 - 1‖ + ‖e4 - 1‖ := norm_add_le _ _
        _ ≤ K * e + K * e := by linarith
    have h34 : ‖(e2 - 1) * (e4 - 1)‖ ≤ (K * e) * (K * e) := norm_mul_le_mul h2 h4 hm0
    have hkey : e2 * e4 - 1 = (e2 - 1) + (e4 - 1) + (e2 - 1) * (e4 - 1) := by ring
    rw [hkey]
    have := norm_add_le ((e2 - 1) + (e4 - 1)) ((e2 - 1) * (e4 - 1))
    linarith [this, hm1]
  have hS : ‖e2 ^ 2 * e4 ^ 2 * e6‖ ≤ 32 := by
    have h2' : ‖e2‖ ≤ 2 := norm_le_two h2 hKe
    have h4' : ‖e4‖ ≤ 2 := norm_le_two h4 hKe
    have h6' : ‖e6‖ ≤ 2 := norm_le_two h6 hKe
    calc ‖e2 ^ 2 * e4 ^ 2 * e6‖ = ‖e2‖ ^ 2 * ‖e4‖ ^ 2 * ‖e6‖ := by
          rw [norm_mul, norm_mul, norm_pow, norm_pow]
      _ ≤ 2 ^ 2 * 2 ^ 2 * 2 := by gcongr
      _ = 32 := by norm_num
  have hkey : e6 - 2 * e4 * e2 + e2 ^ 2 * e4 ^ 2 * e6 * h
      = 2 * (e6 - 1) + (e2 * e4 - 1) ^ 2 * (1 + (e6 - 1)) + 2 * (e2 * e4 - 1) * (e6 - 1)
        + e2 ^ 2 * e4 ^ 2 * e6 * (h - 1) := by ring
  rw [hkey]
  have hc1 : ‖(1:ℂ) + (e6 - 1)‖ ≤ 1 + (K * e) := by
    calc ‖(1:ℂ) + (e6 - 1)‖ ≤ ‖(1:ℂ)‖ + ‖e6 - 1‖ := norm_add_le _ _
      _ ≤ 1 + (K * e) := by rw [norm_one]; linarith
  have t1 : ‖(2:ℂ) * (e6 - 1)‖ ≤ 2 * (K * e) := norm_two_mul_le h6
  have t2 : ‖(e2 * e4 - 1) ^ 2 * (1 + (e6 - 1))‖ ≤ (3 * (K * e)) ^ 2 * (1 + (K * e)) := by
    rw [norm_mul, norm_pow]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hu 2) hc1 (by positivity) (by positivity)
  have t3 : ‖(2:ℂ) * (e2 * e4 - 1) * (e6 - 1)‖ ≤ 2 * (3 * (K * e)) * (K * e) := by
    rw [norm_mul, norm_mul, Complex.norm_ofNat]
    have h1 : ‖e2 * e4 - 1‖ * ‖e6 - 1‖ ≤ (3 * (K * e)) * (K * e) :=
      mul_le_mul hu h6 (norm_nonneg _) (by positivity)
    linarith
  have t4 : ‖e2 ^ 2 * e4 ^ 2 * e6 * (h - 1)‖ ≤ 32 * (K * e) := by
    rw [norm_mul]
    exact mul_le_mul hS hh (norm_nonneg _) (by norm_num)
  have hE : (2:ℂ) * (e6 - 1) + (e2 * e4 - 1) ^ 2 * (1 + (e6 - 1)) + 2 * (e2 * e4 - 1) * (e6 - 1)
      + e2 ^ 2 * e4 ^ 2 * e6 * (h - 1)
      = ((2:ℂ) * (e6 - 1) + (e2 * e4 - 1) ^ 2 * (1 + (e6 - 1)))
        + (2 * (e2 * e4 - 1) * (e6 - 1) + e2 ^ 2 * e4 ^ 2 * e6 * (h - 1)) := by ring
  rw [hE]
  have htri := norm_add_le ((2:ℂ) * (e6 - 1) + (e2 * e4 - 1) ^ 2 * (1 + (e6 - 1)))
    (2 * (e2 * e4 - 1) * (e6 - 1) + e2 ^ 2 * e4 ^ 2 * e6 * (h - 1))
  have htri2 := norm_add_le ((2:ℂ) * (e6 - 1)) ((e2 * e4 - 1) ^ 2 * (1 + (e6 - 1)))
  have htri3 := norm_add_le (2 * (e2 * e4 - 1) * (e6 - 1)) (e2 ^ 2 * e4 ^ 2 * e6 * (h - 1))
  have hmain : ‖(2:ℂ) * (e6 - 1) + (e2 * e4 - 1) ^ 2 * (1 + (e6 - 1)) + 2 * (e2 * e4 - 1) * (e6 - 1)
      + e2 ^ 2 * e4 ^ 2 * e6 * (h - 1)‖
      ≤ 2 * (K * e) + (3 * (K * e)) ^ 2 * (1 + (K * e)) + 2 * (3 * (K * e)) * (K * e)
        + 32 * (K * e) := by
    rw [hE]
    linarith [htri, htri2, htri3, t1, t2, t3, t4]
  nlinarith [hmain, hm0, hm1, hKe, sq_nonneg (K * e)]

/-- **The `d = 8` constant coefficient is `O(q)`.** -/
lemma norm_B8_le {e2 e4 e6 h : ℂ} {K e : ℝ} (hKe : K * e ≤ 1)
    (h2 : ‖e2 - 1‖ ≤ K * e) (h4 : ‖e4 - 1‖ ≤ K * e) (h6 : ‖e6 - 1‖ ≤ K * e)
    (hh : ‖h - 1‖ ≤ K * e) :
    ‖e4 - e2 * e4 ^ 2 * e6 * h‖ ≤ 100 * (K * e) := by
  have hm0 : 0 ≤ K * e := le_trans (norm_nonneg (e2 - 1)) h2
  have hm1 : (K * e) ^ 2 ≤ K * e := by nlinarith [hm0, hKe]
  have hT : ‖e2 * e4 ^ 2 * e6‖ ≤ 16 := by
    have h2' : ‖e2‖ ≤ 2 := norm_le_two h2 hKe
    have h4' : ‖e4‖ ≤ 2 := norm_le_two h4 hKe
    have h6' : ‖e6‖ ≤ 2 := norm_le_two h6 hKe
    calc ‖e2 * e4 ^ 2 * e6‖ = ‖e2‖ * ‖e4‖ ^ 2 * ‖e6‖ := by
          rw [norm_mul, norm_mul, norm_pow]
      _ ≤ 2 * 2 ^ 2 * 2 := by gcongr
      _ = 16 := by norm_num
  -- `w = b + 2a + ab`
  have hw : ‖(e4 - 1) + 2 * (e2 - 1) + (e2 - 1) * (e4 - 1)‖ ≤ 4 * (K * e) := by
    have h12 : ‖(e4 - 1) + (2:ℂ) * (e2 - 1)‖ ≤ K * e + 2 * (K * e) := by
      calc ‖(e4 - 1) + (2:ℂ) * (e2 - 1)‖ ≤ ‖e4 - 1‖ + ‖(2:ℂ) * (e2 - 1)‖ := norm_add_le _ _
        _ ≤ K * e + 2 * (K * e) := by linarith [norm_two_mul_le h2]
    have h34 : ‖(e2 - 1) * (e4 - 1)‖ ≤ (K * e) * (K * e) := norm_mul_le_mul h2 h4 hm0
    have hkey : (e4 - 1) + 2 * (e2 - 1) + (e2 - 1) * (e4 - 1)
        = ((e4 - 1) + (2:ℂ) * (e2 - 1)) + (e2 - 1) * (e4 - 1) := by ring
    rw [hkey]
    have := norm_add_le ((e4 - 1) + (2:ℂ) * (e2 - 1)) ((e2 - 1) * (e4 - 1))
    linarith [this, hm1]
  have hv : ‖e2 * e4 ^ 2 - 1‖ ≤ 7 * (K * e) := by
    have h12 : ‖(e2 - 1) + 2 * (e4 - 1)‖ ≤ K * e + 2 * (K * e) := by
      calc ‖(e2 - 1) + (2:ℂ) * (e4 - 1)‖ ≤ ‖e2 - 1‖ + ‖(2:ℂ) * (e4 - 1)‖ := norm_add_le _ _
        _ ≤ K * e + 2 * (K * e) := by linarith [norm_two_mul_le h4]
    have h34 : ‖(e4 - 1) * ((e4 - 1) + 2 * (e2 - 1) + (e2 - 1) * (e4 - 1))‖
        ≤ (K * e) * (4 * (K * e)) := norm_mul_le_mul h4 hw hm0
    have hkey : e2 * e4 ^ 2 - 1 = ((e2 - 1) + 2 * (e4 - 1))
        + (e4 - 1) * ((e4 - 1) + 2 * (e2 - 1) + (e2 - 1) * (e4 - 1)) := by ring
    rw [hkey]
    have := norm_add_le ((e2 - 1) + 2 * (e4 - 1))
      ((e4 - 1) * ((e4 - 1) + 2 * (e2 - 1) + (e2 - 1) * (e4 - 1)))
    linarith [this, h12, h34, hm0, hKe, hm1]
  have hkey : e4 - e2 * e4 ^ 2 * e6 * h
      = -(e2 - 1) - (e4 - 1) - (e6 - 1)
        - (e4 - 1) * ((e4 - 1) + 2 * (e2 - 1) + (e2 - 1) * (e4 - 1))
        - (e2 * e4 ^ 2 - 1) * (e6 - 1) - e2 * e4 ^ 2 * e6 * (h - 1) := by ring
  rw [hkey]
  have t1 : ‖-(e2 - 1) - (e4 - 1) - (e6 - 1)‖ ≤ 3 * (K * e) := by
    have ha : -(e2 - 1) - (e4 - 1) - (e6 - 1) = -((e2 - 1) + (e4 - 1) + (e6 - 1)) := by ring
    rw [ha, norm_neg]
    have hb := norm_add_le ((e2 - 1) + (e4 - 1)) (e6 - 1)
    have hc := norm_add_le (e2 - 1) (e4 - 1)
    linarith
  have t2 : ‖(e4 - 1) * ((e4 - 1) + 2 * (e2 - 1) + (e2 - 1) * (e4 - 1))‖ ≤ 4 * ((K*e) * (K*e)) := by
    have := norm_mul_le_mul h4 hw hm0
    linarith [this, hm0, hKe]
  have t3 : ‖(e2 * e4 ^ 2 - 1) * (e6 - 1)‖ ≤ 7 * ((K*e) * (K*e)) := by
    have := norm_mul_le_mul hv h6 (by positivity)
    linarith [this, hm0, hKe]
  have t4 : ‖-(e2 * e4 ^ 2 * e6 * (h - 1))‖ ≤ 16 * (K * e) := by
    rw [norm_neg, norm_mul]; exact mul_le_mul hT hh (norm_nonneg _) (by norm_num)
  have hE : -(e2 - 1) - (e4 - 1) - (e6 - 1)
        - (e4 - 1) * ((e4 - 1) + 2 * (e2 - 1) + (e2 - 1) * (e4 - 1))
        - (e2 * e4 ^ 2 - 1) * (e6 - 1) - e2 * e4 ^ 2 * e6 * (h - 1)
      = (-(e2 - 1) - (e4 - 1) - (e6 - 1))
        + (- ((e4 - 1) * ((e4 - 1) + 2 * (e2 - 1) + (e2 - 1) * (e4 - 1)))
          + (- ((e2 * e4 ^ 2 - 1) * (e6 - 1)) + (-(e2 * e4 ^ 2 * e6 * (h - 1))))) := by ring
  rw [hE]
  have htri := norm_add_le (-(e2 - 1) - (e4 - 1) - (e6 - 1))
    (-((e4 - 1) * ((e4 - 1) + 2 * (e2 - 1) + (e2 - 1) * (e4 - 1)))
      + (-((e2 * e4 ^ 2 - 1) * (e6 - 1)) + (-(e2 * e4 ^ 2 * e6 * (h - 1)))))
  have htri2 := norm_add_le (-((e4 - 1) * ((e4 - 1) + 2 * (e2 - 1) + (e2 - 1) * (e4 - 1))))
    (-((e2 * e4 ^ 2 - 1) * (e6 - 1)) + (-(e2 * e4 ^ 2 * e6 * (h - 1))))
  have htri3 := norm_add_le (-((e2 * e4 ^ 2 - 1) * (e6 - 1))) (-(e2 * e4 ^ 2 * e6 * (h - 1)))
  rw [norm_neg] at htri2 htri3
  have hmain : ‖-(e2 - 1) - (e4 - 1) - (e6 - 1)
      - (e4 - 1) * ((e4 - 1) + 2 * (e2 - 1) + (e2 - 1) * (e4 - 1))
      - (e2 * e4 ^ 2 - 1) * (e6 - 1) - e2 * e4 ^ 2 * e6 * (h - 1)‖
      ≤ 3 * (K * e) + 4 * ((K * e) * (K * e)) + 7 * ((K * e) * (K * e)) + 16 * (K * e) := by
    rw [hE]
    linarith [htri, htri2, htri3, t1, t2, t3, t4]
  nlinarith [hmain, hm0, hm1, hKe, sq_nonneg (K * e)]

/-! ## Decay bounds at the cusp -/

lemma E2_decay_bound : ∃ H K : ℝ, 0 ≤ K ∧ ∀ τ : ℍ, H ≤ τ.im → ‖E2Fun τ - 1‖ ≤ K * eps τ := by
  obtain ⟨A, B, hB, hAB⟩ := Work.Rigidity.E2Fun_sub_one_decay
  exact ⟨A, B, hB, fun τ hτ => hAB τ hτ⟩

lemma E4_decay_bound : ∃ H K : ℝ, 0 ≤ K ∧ ∀ τ : ℍ, H ≤ τ.im → ‖E4Fun τ - 1‖ ≤ K * eps τ := by
  obtain ⟨A, B, hB, hAB⟩ := Work.Rigidity.modularForm_cusp_decay (ModularForm.E₄)
  have hc : Work.Rigidity.cterm (ModularForm.E₄) = 1 := by
    simp only [Work.Rigidity.cterm]
    simpa using Work.Modular.E4_qExpansion_coeff 0
  refine ⟨A, B, hB, fun τ hτ => ?_⟩
  have := hAB τ hτ
  rwa [hc] at this

lemma E6_decay_bound : ∃ H K : ℝ, 0 ≤ K ∧ ∀ τ : ℍ, H ≤ τ.im → ‖E6Fun τ - 1‖ ≤ K * eps τ := by
  obtain ⟨A, B, hB, hAB⟩ := Work.Rigidity.modularForm_cusp_decay (ModularForm.E₆)
  have hc : Work.Rigidity.cterm (ModularForm.E₆) = 1 := by
    simp only [Work.Rigidity.cterm]
    simpa using Work.Modular.E6_qExpansion_coeff 0
  refine ⟨A, B, hB, fun τ hτ => ?_⟩
  have := hAB τ hτ
  rwa [hc] at this

lemma Delta_decay_bound : ∃ H K : ℝ, 0 ≤ K ∧ ∀ τ : ℍ, H ≤ τ.im → ‖DeltaFun τ‖ ≤ K * eps τ := by
  obtain ⟨C, hC, A, hA⟩ := Work.Asymptotics.exists_bound_norm_deltaFun
  refine ⟨A, C, hC.le, fun τ hτ => ?_⟩
  have h := hA τ hτ
  rw [show Real.exp (-2 * Real.pi * τ.im) = eps τ from by simp only [eps]; ring_nf] at h
  exact h

/-- `1728 Δ = E₄³ - E₆²`, the classical identity for the modular discriminant. -/
lemma DeltaFun_eq_E4_cube_sub_E6_sq (τ : ℍ) :
    (1728 : ℂ) * DeltaFun τ = E4Fun τ ^ 3 - E6Fun τ ^ 2 := by
  have h := ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq τ
  simp only [DeltaFun, E4Fun, E6Fun, CuspForm.coe_discriminant] at h ⊢
  rw [h]
  field_simp

lemma delta_mul_j (τ : ℍ) : DeltaFun τ * jInvariantFun τ = E4Fun τ ^ 3 :=
  ClassicalFacts.DeltaFun_mul_jInvariantFun τ

lemma delta_ne_zero (τ : ℍ) : DeltaFun τ ≠ 0 := ClassicalFacts.DeltaFun_ne_zero τ

/-! ## Rewriting the kernels -/

lemma PiMat_642 (τ : ℍ) :
    PiMat ![6,4,2] τ = Matrix.diagonal ![E6Fun τ, E4Fun τ, E14Fun τ/DeltaFun τ] := by
  simp only [PiMat]; congr 1; funext i; fin_cases i <;> simp [fk]

lemma PiMat_12_10_8 (z : ℍ) :
    PiMat ![12,10,8] z = Matrix.diagonal ![DeltaFun z, E10Fun z, E8Fun z] := by
  simp only [PiMat]; congr 1; funext i; fin_cases i <;> simp [fk]

lemma PiMat_14_12_10 (τ : ℍ) :
    PiMat ![14,12,10] τ = Matrix.diagonal ![E14Fun τ, DeltaFun τ, E10Fun τ] := by
  simp only [PiMat]; congr 1; funext i; fin_cases i <;> simp [fk]

lemma PiMat_4_2_0 (z : ℍ) :
    PiMat ![4,2,0] z = Matrix.diagonal ![E4Fun z, E14Fun z/DeltaFun z, 1] := by
  simp only [PiMat]; congr 1; funext i; fin_cases i <;> simp [fk]

/-- The `d = 8` `τ`-coefficient. -/
def A8v (e2 e4 e6 hh : ℂ) : ℂ := e6 - 2 * e4 * e2 + e2 ^ 2 * e4 ^ 2 * e6 * hh

/-- The `d = 8` constant coefficient. -/
def B8v (e2 e4 e6 hh : ℂ) : ℂ := e4 - e2 * e4 ^ 2 * e6 * hh

/-- The `d = 8` kernel with the leading `τ`-linear terms grouped. -/
def G8 (τ z : ℍ) : ℂ :=
  phitVec z 0 * ((τ:ℂ) * A8v (E2Fun τ) (E4Fun τ) (E6Fun τ) (kph τ z)
      + (6*Complex.I/(Real.pi:ℂ)) * B8v (E2Fun τ) (E4Fun τ) (E6Fun τ) (kph τ z))
    + (phitVec z 2 * (τ:ℂ) * E6Fun τ * E8Fun z - 2 * phi0 τ * phitVec z 1 * E4Fun τ * E10Fun z)
        * (DeltaFun z * kpJ τ z)⁻¹

/-- **The `d = 8` kernel, grouped for the asymptotics.** -/
lemma KPlus_eight_eq (τ z : ℍ) (hJ : kpJ τ z ≠ 0) :
    KPlus 8 τ z = (Real.pi : ℂ)^2/(36*Complex.I) * G8 τ z := by
  have hD : DeltaFun τ ≠ 0 := delta_ne_zero τ
  have hz : DeltaFun z ≠ 0 := delta_ne_zero z
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hkey : DeltaFun z * E4Fun τ ^ 3 - DeltaFun τ * E4Fun z ^ 3 ≠ 0 := by
    intro h
    apply hJ
    simp only [kpJ, jInvariantFun]
    rw [sub_eq_zero, div_eq_div_iff hD hz]
    linear_combination h
  simp only [KPlus, UpsilonPlus, ite_true, PiMat_642 τ, PiMat_12_10_8 z, Fin.sum_univ_three,
    Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons,
    phiVec, phiNeg2, phi0, phi2, phitVec, E8Fun, E10Fun, E14Fun,
    _root_.zpow_neg, _root_.zpow_ofNat, kpJ, kph, G8, A8v, B8v]
  field_simp
  ring


/-- The constant multiplying the `φ̃₀` group of the `d = 24` kernel. -/
def c0f (z : ℍ) (KC K1 : ℝ) : ℝ :=
  ‖phitVec z 0‖ * ‖E4Fun z‖ * (801 + (KC / K1^2 + 700))

/-- The constant multiplying the `φ̃₁` group of the `d = 24` kernel. -/
def c1f (z : ℍ) : ℝ :=
  ‖phitVec z 1‖ * (‖E14Fun z‖ / ‖DeltaFun z‖) * ((2/1728) * 600)

/-- The constant multiplying the `φ̃₂` group of the `d = 24` kernel. -/
def c2f (z : ℍ) (KC K1 : ℝ) : ℝ :=
  ‖phitVec z 2‖ * (801 + (KC / K1^2 + 200))

/-- The constant multiplying `‖τ‖ · m²` in the `d = 24` bound. -/
def Czf (z : ℍ) (KC K1 : ℝ) : ℝ := c0f z KC K1 + c1f z + c2f z KC K1 + 1

end Work.Residues.KPlusAux
