import Mathlib
import Submission.Work.Asymptotics.KPlusXiDefs
import Submission.Work.Asymptotics.ZAtomsThird.first_order

namespace Work.Asymptotics.ZAtomsThird

open UpperHalfPlane

noncomputable section

/-!
# Cusp forms among the products of `E₂`, `E₄`, `E₆` on `{Im τ ≥ 1/3}`

The four combinations

* `E₄ - E₂²`                  (`= 288 q + O(q²)`, weight `4`),
* `E₂ E₆ - E₄²`               (`= -1008 q + O(q²)`, weight `6`),
* `E₂ E₄ - E₆`                (`= 720 q + O(q²)`, weight `6`),
* `5 E₄² - 7 E₄ E₂² + 2 E₆ E₂` (`= 388800 q² + O(q³)`, weight `8`),

vanish at the cusp `i∞`: the first three are `O(q)`, the last one `O(q²)`.  This is
the "cusp forms" input used in the third-generation atom estimates of Section 5.

The proof uses only the two-term expansions of `Work.Asymptotics.ZAtomsThird.first_order`
(`E₂ = 1 - 24q + O(q²)`, `E₄ = 1 + 240q + O(q²)`, `E₆ = 1 - 504q + O(q²)` on
`{Im τ ≥ 1/3}`) together with `‖q‖ ≤ 1` on that region, expanded by hand: writing
`E_k = A_k + s_k` with `A₂ = 1 - 24q`, `A₄ = 1 + 240q`, `A₆ = 1 - 504q`, each
combination is a polynomial in `q` of the stated order plus terms which are either
of the form (bounded) `· s_k` or `s_j s_k`, both `O(‖q‖²)`.
-/

/-- `‖q‖ ≤ 1` when `Im τ ≥ 0`, where `q = exp (2 π i τ)`. -/
private lemma qparam_norm_le_one {z : ℍ} (hz : 0 ≤ z.im) :
    ‖Work.Kernels.qParamFun z‖ ≤ 1 := by
  rw [Work.Asymptotics.norm_qParamFun, Real.exp_le_one_iff]
  nlinarith [Real.pi_pos, hz]

/-- `‖E₄ - E₂²‖ ≤ C ‖q‖` on `{Im τ ≥ 1/3}`. -/
private lemma bound_one {C2 C4 : ℝ} (hC2 : 0 ≤ C2) (hC4 : 0 ≤ C4)
    (h2 : ∀ z : ℍ, 1 / 3 ≤ z.im →
      ‖Work.Kernels.E2Fun z - 1 + 24 * Work.Kernels.qParamFun z‖ ≤
        C2 * ‖Work.Kernels.qParamFun z‖ ^ 2)
    (h4 : ∀ z : ℍ, 1 / 3 ≤ z.im →
      ‖Work.Kernels.E4Fun z - 1 - 240 * Work.Kernels.qParamFun z‖ ≤
        C4 * ‖Work.Kernels.qParamFun z‖ ^ 2) :
    ∀ z : ℍ, 1 / 3 ≤ z.im →
      ‖Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2‖ ≤
        (C4 + 864 + 50 * C2 + C2 ^ 2) * ‖Work.Kernels.qParamFun z‖ := by
  intro z hz
  have hz0 : (0:ℝ) ≤ z.im := le_trans (by norm_num) hz
  set q : ℂ := Work.Kernels.qParamFun z with hq
  have hqn : (0:ℝ) ≤ ‖q‖ := norm_nonneg q
  have hq1 : ‖q‖ ≤ 1 := qparam_norm_le_one hz0
  have hq2 : ‖q‖^2 ≤ ‖q‖ := by
    simpa using pow_le_pow_of_le_one hqn hq1 (by norm_num : 1 ≤ 2)
  set s2 : ℂ := Work.Kernels.E2Fun z - 1 + 24 * q with hs2
  set s4 : ℂ := Work.Kernels.E4Fun z - 1 - 240 * q with hs4
  have hs2b : ‖s2‖ ≤ C2 * ‖q‖^2 := by rw [hs2]; simpa [hq] using h2 z hz
  have hs4b : ‖s4‖ ≤ C4 * ‖q‖^2 := by rw [hs4]; simpa [hq] using h4 z hz
  have hA2 : ‖(1:ℂ) - 24*q‖ ≤ 25 := by
    calc ‖(1:ℂ) - 24*q‖ ≤ ‖(1:ℂ)‖ + ‖24*q‖ := norm_sub_le _ _
      _ = 1 + 24*‖q‖ := by rw [norm_mul]; norm_num
      _ ≤ 25 := by linarith [hqn, hq1]
  have hE2 : Work.Kernels.E2Fun z = (1 - 24*q) + s2 := by rw [hs2]; ring
  have hE4 : Work.Kernels.E4Fun z = (1 + 240*q) + s4 := by rw [hs4]; ring
  have hkey : Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2
      = (288*q - 576*q^2) + s4 - (2*(1-24*q)*s2 + s2^2) := by
    rw [hE2, hE4]; ring
  have hb1 : ‖288*q - 576*q^2‖ ≤ 864 * ‖q‖ := by
    calc ‖288*q - 576*q^2‖ ≤ ‖(288:ℂ)*q‖ + ‖(576:ℂ)*q^2‖ := norm_sub_le _ _
      _ = 288*‖q‖ + 576*‖q‖^2 := by rw [norm_mul, norm_mul, norm_pow]; norm_num
      _ ≤ 864 * ‖q‖ := by linarith
  have hb2 : ‖s4‖ ≤ C4 * ‖q‖ := by nlinarith [hs4b, hq2, hC4]
  have hb3 : ‖2*(1-24*q)*s2‖ ≤ 50*C2*‖q‖ := by
    have hstep : ‖(2:ℂ)‖ * ‖(1:ℂ) - 24*q‖ * ‖s2‖ ≤ 2*25*(C2*‖q‖^2) := by
      have h1 : ‖(2:ℂ)‖ * ‖(1:ℂ) - 24*q‖ ≤ 2 * 25 := by
        rw [show ‖(2:ℂ)‖ = 2 by norm_num]
        linarith [hA2]
      calc ‖(2:ℂ)‖ * ‖(1:ℂ) - 24*q‖ * ‖s2‖
          ≤ (2*25) * (C2*‖q‖^2) := mul_le_mul h1 hs2b (norm_nonneg _) (by norm_num)
        _ = 2*25*(C2*‖q‖^2) := by ring
    calc ‖2*(1-24*q)*s2‖ = ‖(2:ℂ)‖ * ‖(1:ℂ) - 24*q‖ * ‖s2‖ := by rw [norm_mul, norm_mul]
      _ ≤ 2*25*(C2*‖q‖^2) := hstep
      _ = 50*C2*‖q‖^2 := by ring
      _ ≤ 50*C2*‖q‖ := by nlinarith [hq2, hC2]
  have hb4 : ‖s2^2‖ ≤ C2^2*‖q‖ := by
    rw [norm_pow]
    have h4' : ‖q‖^4 ≤ ‖q‖ := by
      simpa using pow_le_pow_of_le_one hqn hq1 (by norm_num : 1 ≤ 4)
    calc ‖s2‖^2 ≤ (C2*‖q‖^2)^2 := pow_le_pow_left₀ (norm_nonneg s2) hs2b 2
      _ = C2^2 * ‖q‖^4 := by ring
      _ ≤ C2^2 * ‖q‖ := mul_le_mul_of_nonneg_left h4' (by positivity)
  have htri : ‖(288*q - 576*q^2) + s4 - (2*(1-24*q)*s2 + s2^2)‖
      ≤ ‖288*q - 576*q^2‖ + ‖s4‖ + (‖2*(1-24*q)*s2‖ + ‖s2^2‖) := by
    calc ‖(288*q - 576*q^2) + s4 - (2*(1-24*q)*s2 + s2^2)‖
        ≤ ‖(288*q - 576*q^2) + s4‖ + ‖2*(1-24*q)*s2 + s2^2‖ := norm_sub_le _ _
      _ ≤ (‖288*q - 576*q^2‖ + ‖s4‖) + (‖2*(1-24*q)*s2‖ + ‖s2^2‖) :=
          add_le_add (norm_add_le _ _) (norm_add_le _ _)
  rw [hkey]
  linarith [htri, hb1, hb2, hb3, hb4]

/-- `‖E₂ E₆ - E₄²‖ ≤ C ‖q‖` on `{Im τ ≥ 1/3}`. -/
private lemma bound_two {C2 C4 C6 : ℝ} (hC2 : 0 ≤ C2) (hC4 : 0 ≤ C4) (hC6 : 0 ≤ C6)
    (h2 : ∀ z : ℍ, 1 / 3 ≤ z.im →
      ‖Work.Kernels.E2Fun z - 1 + 24 * Work.Kernels.qParamFun z‖ ≤
        C2 * ‖Work.Kernels.qParamFun z‖ ^ 2)
    (h4 : ∀ z : ℍ, 1 / 3 ≤ z.im →
      ‖Work.Kernels.E4Fun z - 1 - 240 * Work.Kernels.qParamFun z‖ ≤
        C4 * ‖Work.Kernels.qParamFun z‖ ^ 2)
    (h6 : ∀ z : ℍ, 1 / 3 ≤ z.im →
      ‖Work.Kernels.E6Fun z - 1 + 504 * Work.Kernels.qParamFun z‖ ≤
        C6 * ‖Work.Kernels.qParamFun z‖ ^ 2) :
    ∀ z : ℍ, 1 / 3 ≤ z.im →
      ‖Work.Kernels.E2Fun z * Work.Kernels.E6Fun z - Work.Kernels.E4Fun z ^ 2‖ ≤
        (1008 + 45504 + C2 * (505 + C6) + 25 * C6 + C4 * (482 + C4)) *
          ‖Work.Kernels.qParamFun z‖ := by
  intro z hz
  have hz0 : (0:ℝ) ≤ z.im := le_trans (by norm_num) hz
  set q : ℂ := Work.Kernels.qParamFun z with hq
  have hqn : (0:ℝ) ≤ ‖q‖ := norm_nonneg q
  have hq1 : ‖q‖ ≤ 1 := qparam_norm_le_one hz0
  have hq2 : ‖q‖^2 ≤ ‖q‖ := by
    simpa using pow_le_pow_of_le_one hqn hq1 (by norm_num : 1 ≤ 2)
  have hq2one : ‖q‖^2 ≤ 1 := by
    simpa using pow_le_pow_of_le_one hqn hq1 (by norm_num : (0:ℕ) ≤ 2)
  set s2 : ℂ := Work.Kernels.E2Fun z - 1 + 24 * q with hs2
  set s4 : ℂ := Work.Kernels.E4Fun z - 1 - 240 * q with hs4
  set s6 : ℂ := Work.Kernels.E6Fun z - 1 + 504 * q with hs6
  have hs2b : ‖s2‖ ≤ C2 * ‖q‖^2 := by rw [hs2]; simpa [hq] using h2 z hz
  have hs4b : ‖s4‖ ≤ C4 * ‖q‖^2 := by rw [hs4]; simpa [hq] using h4 z hz
  have hs6b : ‖s6‖ ≤ C6 * ‖q‖^2 := by rw [hs6]; simpa [hq] using h6 z hz
  have hA2 : ‖(1:ℂ) - 24*q‖ ≤ 25 := by
    calc ‖(1:ℂ) - 24*q‖ ≤ ‖(1:ℂ)‖ + ‖24*q‖ := norm_sub_le _ _
      _ = 1 + 24*‖q‖ := by rw [norm_mul]; norm_num
      _ ≤ 25 := by linarith [hqn, hq1]
  have hA4 : ‖(1:ℂ) + 240*q‖ ≤ 241 := by
    calc ‖(1:ℂ) + 240*q‖ ≤ ‖(1:ℂ)‖ + ‖240*q‖ := norm_add_le _ _
      _ = 1 + 240*‖q‖ := by rw [norm_mul]; norm_num
      _ ≤ 241 := by linarith [hqn, hq1]
  have hE2 : Work.Kernels.E2Fun z = (1 - 24*q) + s2 := by rw [hs2]; ring
  have hE4 : Work.Kernels.E4Fun z = (1 + 240*q) + s4 := by rw [hs4]; ring
  have hE6 : Work.Kernels.E6Fun z = (1 - 504*q) + s6 := by rw [hs6]; ring
  have hE4size : ‖Work.Kernels.E4Fun z‖ ≤ 241 + C4 := by
    rw [hE4]
    calc ‖(1 + 240*q) + s4‖ ≤ ‖(1:ℂ) + 240*q‖ + ‖s4‖ := norm_add_le _ _
      _ ≤ 241 + C4 := by
          have h : C4 * ‖q‖^2 ≤ C4 := by nlinarith [hq2one, hC4]
          linarith [hA4, hs4b]
  have hE6size : ‖Work.Kernels.E6Fun z‖ ≤ 505 + C6 := by
    rw [hE6]
    have hA6 : ‖(1:ℂ) - 504*q‖ ≤ 505 := by
      calc ‖(1:ℂ) - 504*q‖ ≤ ‖(1:ℂ)‖ + ‖504*q‖ := norm_sub_le _ _
        _ = 1 + 504*‖q‖ := by rw [norm_mul]; norm_num
        _ ≤ 505 := by linarith [hqn, hq1]
    calc ‖(1 - 504*q) + s6‖ ≤ ‖(1:ℂ) - 504*q‖ + ‖s6‖ := norm_add_le _ _
      _ ≤ 505 + C6 := by
          have h : C6 * ‖q‖^2 ≤ C6 := by nlinarith [hq2one, hC6]
          linarith [hA6, hs6b]
  have hkey : Work.Kernels.E2Fun z * Work.Kernels.E6Fun z - Work.Kernels.E4Fun z ^ 2
      = ((-1008:ℂ)*q - (45504:ℂ)*q^2) + s2*Work.Kernels.E6Fun z + (1-24*q)*s6
        - s4*(Work.Kernels.E4Fun z + (1+240*q)) := by
    rw [hE2, hE4, hE6]; ring
  have hb1 : ‖(-1008:ℂ)*q - (45504:ℂ)*q^2‖ ≤ (1008 + 45504) * ‖q‖ := by
    calc ‖(-1008:ℂ)*q - (45504:ℂ)*q^2‖ ≤ ‖(-1008:ℂ)*q‖ + ‖(45504:ℂ)*q^2‖ := norm_sub_le _ _
      _ = 1008*‖q‖ + 45504*‖q‖^2 := by rw [norm_mul, norm_mul, norm_pow]; norm_num
      _ ≤ (1008 + 45504) * ‖q‖ := by linarith
  have hb2 : ‖s2*Work.Kernels.E6Fun z‖ ≤ C2*(505+C6)*‖q‖ := by
    rw [norm_mul]
    calc ‖s2‖ * ‖Work.Kernels.E6Fun z‖ ≤ (C2*‖q‖^2) * (505 + C6) :=
          mul_le_mul hs2b hE6size (norm_nonneg _) (by positivity)
      _ = C2*(505+C6)*‖q‖^2 := by ring
      _ ≤ C2*(505+C6)*‖q‖ := by
          have h : (0:ℝ) ≤ C2*(505+C6) := by positivity
          nlinarith [hq2]
  have hb3 : ‖(1-24*q)*s6‖ ≤ 25*C6*‖q‖ := by
    rw [norm_mul]
    calc ‖(1:ℂ) - 24*q‖ * ‖s6‖ ≤ 25 * (C6*‖q‖^2) :=
          mul_le_mul hA2 hs6b (norm_nonneg _) (by norm_num)
      _ = 25*C6*‖q‖^2 := by ring
      _ ≤ 25*C6*‖q‖ := by nlinarith [hq2, hC6]
  have hb4 : ‖s4*(Work.Kernels.E4Fun z + (1+240*q))‖ ≤ C4*(482+C4)*‖q‖ := by
    rw [norm_mul]
    have hsum : ‖Work.Kernels.E4Fun z + (1+240*q)‖ ≤ 482 + C4 := by
      calc ‖Work.Kernels.E4Fun z + (1+240*q)‖
          ≤ ‖Work.Kernels.E4Fun z‖ + ‖(1:ℂ) + 240*q‖ := norm_add_le _ _
        _ ≤ 482 + C4 := by linarith
    calc ‖s4‖ * ‖Work.Kernels.E4Fun z + (1+240*q)‖ ≤ (C4*‖q‖^2) * (482 + C4) :=
          mul_le_mul hs4b hsum (norm_nonneg _) (by positivity)
      _ = C4*(482+C4)*‖q‖^2 := by ring
      _ ≤ C4*(482+C4)*‖q‖ := by
          have h : (0:ℝ) ≤ C4*(482+C4) := by positivity
          nlinarith [hq2]
  have htri : ‖((-1008:ℂ)*q - (45504:ℂ)*q^2) + s2*Work.Kernels.E6Fun z + (1-24*q)*s6
      - s4*(Work.Kernels.E4Fun z + (1+240*q))‖
      ≤ ‖(-1008:ℂ)*q - (45504:ℂ)*q^2‖ + ‖s2*Work.Kernels.E6Fun z‖ + ‖(1-24*q)*s6‖
        + ‖s4*(Work.Kernels.E4Fun z + (1+240*q))‖ := by
    have h1 : ‖((-1008:ℂ)*q - (45504:ℂ)*q^2) + s2*Work.Kernels.E6Fun z + (1-24*q)*s6
        - s4*(Work.Kernels.E4Fun z + (1+240*q))‖
        ≤ ‖((-1008:ℂ)*q - (45504:ℂ)*q^2) + s2*Work.Kernels.E6Fun z + (1-24*q)*s6‖
          + ‖s4*(Work.Kernels.E4Fun z + (1+240*q))‖ := norm_sub_le _ _
    have h2' : ‖((-1008:ℂ)*q - (45504:ℂ)*q^2) + s2*Work.Kernels.E6Fun z + (1-24*q)*s6‖
        ≤ ‖((-1008:ℂ)*q - (45504:ℂ)*q^2) + s2*Work.Kernels.E6Fun z‖ + ‖(1-24*q)*s6‖ :=
      norm_add_le _ _
    have h3 : ‖((-1008:ℂ)*q - (45504:ℂ)*q^2) + s2*Work.Kernels.E6Fun z‖
        ≤ ‖(-1008:ℂ)*q - (45504:ℂ)*q^2‖ + ‖s2*Work.Kernels.E6Fun z‖ := norm_add_le _ _
    linarith
  rw [hkey]
  linarith [htri, hb1, hb2, hb3, hb4]

/-- `‖E₂ E₄ - E₆‖ ≤ C ‖q‖` on `{Im τ ≥ 1/3}`. -/
private lemma bound_three {C2 C4 C6 : ℝ} (hC2 : 0 ≤ C2) (hC4 : 0 ≤ C4) (hC6 : 0 ≤ C6)
    (h2 : ∀ z : ℍ, 1 / 3 ≤ z.im →
      ‖Work.Kernels.E2Fun z - 1 + 24 * Work.Kernels.qParamFun z‖ ≤
        C2 * ‖Work.Kernels.qParamFun z‖ ^ 2)
    (h4 : ∀ z : ℍ, 1 / 3 ≤ z.im →
      ‖Work.Kernels.E4Fun z - 1 - 240 * Work.Kernels.qParamFun z‖ ≤
        C4 * ‖Work.Kernels.qParamFun z‖ ^ 2)
    (h6 : ∀ z : ℍ, 1 / 3 ≤ z.im →
      ‖Work.Kernels.E6Fun z - 1 + 504 * Work.Kernels.qParamFun z‖ ≤
        C6 * ‖Work.Kernels.qParamFun z‖ ^ 2) :
    ∀ z : ℍ, 1 / 3 ≤ z.im →
      ‖Work.Kernels.E2Fun z * Work.Kernels.E4Fun z - Work.Kernels.E6Fun z‖ ≤
        (720 + 5760 + C2 * (241 + C4) + 25 * C4 + C6) *
          ‖Work.Kernels.qParamFun z‖ := by
  intro z hz
  have hz0 : (0:ℝ) ≤ z.im := le_trans (by norm_num) hz
  set q : ℂ := Work.Kernels.qParamFun z with hq
  have hqn : (0:ℝ) ≤ ‖q‖ := norm_nonneg q
  have hq1 : ‖q‖ ≤ 1 := qparam_norm_le_one hz0
  have hq2 : ‖q‖^2 ≤ ‖q‖ := by
    simpa using pow_le_pow_of_le_one hqn hq1 (by norm_num : 1 ≤ 2)
  have hq2one : ‖q‖^2 ≤ 1 := by
    simpa using pow_le_pow_of_le_one hqn hq1 (by norm_num : (0:ℕ) ≤ 2)
  set s2 : ℂ := Work.Kernels.E2Fun z - 1 + 24 * q with hs2
  set s4 : ℂ := Work.Kernels.E4Fun z - 1 - 240 * q with hs4
  set s6 : ℂ := Work.Kernels.E6Fun z - 1 + 504 * q with hs6
  have hs2b : ‖s2‖ ≤ C2 * ‖q‖^2 := by rw [hs2]; simpa [hq] using h2 z hz
  have hs4b : ‖s4‖ ≤ C4 * ‖q‖^2 := by rw [hs4]; simpa [hq] using h4 z hz
  have hs6b : ‖s6‖ ≤ C6 * ‖q‖^2 := by rw [hs6]; simpa [hq] using h6 z hz
  have hA2 : ‖(1:ℂ) - 24*q‖ ≤ 25 := by
    calc ‖(1:ℂ) - 24*q‖ ≤ ‖(1:ℂ)‖ + ‖24*q‖ := norm_sub_le _ _
      _ = 1 + 24*‖q‖ := by rw [norm_mul]; norm_num
      _ ≤ 25 := by linarith [hqn, hq1]
  have hA4 : ‖(1:ℂ) + 240*q‖ ≤ 241 := by
    calc ‖(1:ℂ) + 240*q‖ ≤ ‖(1:ℂ)‖ + ‖240*q‖ := norm_add_le _ _
      _ = 1 + 240*‖q‖ := by rw [norm_mul]; norm_num
      _ ≤ 241 := by linarith [hqn, hq1]
  have hE2 : Work.Kernels.E2Fun z = (1 - 24*q) + s2 := by rw [hs2]; ring
  have hE4 : Work.Kernels.E4Fun z = (1 + 240*q) + s4 := by rw [hs4]; ring
  have hE6 : Work.Kernels.E6Fun z = (1 - 504*q) + s6 := by rw [hs6]; ring
  have hE4size : ‖Work.Kernels.E4Fun z‖ ≤ 241 + C4 := by
    rw [hE4]
    calc ‖(1 + 240*q) + s4‖ ≤ ‖(1:ℂ) + 240*q‖ + ‖s4‖ := norm_add_le _ _
      _ ≤ 241 + C4 := by
          have h : C4 * ‖q‖^2 ≤ C4 := by nlinarith [hq2one, hC4]
          linarith [hA4, hs4b]
  have hkey : Work.Kernels.E2Fun z * Work.Kernels.E4Fun z - Work.Kernels.E6Fun z
      = ((720:ℂ)*q - (5760:ℂ)*q^2) + s2*Work.Kernels.E4Fun z + (1-24*q)*s4 - s6 := by
    rw [hE2, hE4, hE6]; ring
  have hb1 : ‖(720:ℂ)*q - (5760:ℂ)*q^2‖ ≤ (720 + 5760) * ‖q‖ := by
    calc ‖(720:ℂ)*q - (5760:ℂ)*q^2‖ ≤ ‖(720:ℂ)*q‖ + ‖(5760:ℂ)*q^2‖ := norm_sub_le _ _
      _ = 720*‖q‖ + 5760*‖q‖^2 := by rw [norm_mul, norm_mul, norm_pow]; norm_num
      _ ≤ (720 + 5760) * ‖q‖ := by linarith
  have hb2 : ‖s2*Work.Kernels.E4Fun z‖ ≤ C2*(241+C4)*‖q‖ := by
    rw [norm_mul]
    calc ‖s2‖ * ‖Work.Kernels.E4Fun z‖ ≤ (C2*‖q‖^2) * (241 + C4) :=
          mul_le_mul hs2b hE4size (norm_nonneg _) (by positivity)
      _ = C2*(241+C4)*‖q‖^2 := by ring
      _ ≤ C2*(241+C4)*‖q‖ := by
          have h : (0:ℝ) ≤ C2*(241+C4) := by positivity
          nlinarith [hq2]
  have hb3 : ‖(1-24*q)*s4‖ ≤ 25*C4*‖q‖ := by
    rw [norm_mul]
    calc ‖(1:ℂ) - 24*q‖ * ‖s4‖ ≤ 25 * (C4*‖q‖^2) :=
          mul_le_mul hA2 hs4b (norm_nonneg _) (by norm_num)
      _ = 25*C4*‖q‖^2 := by ring
      _ ≤ 25*C4*‖q‖ := by nlinarith [hq2, hC4]
  have hb4 : ‖s6‖ ≤ C6*‖q‖ := by nlinarith [hs6b, hq2, hC6]
  have htri : ‖((720:ℂ)*q - (5760:ℂ)*q^2) + s2*Work.Kernels.E4Fun z + (1-24*q)*s4 - s6‖
      ≤ ‖(720:ℂ)*q - (5760:ℂ)*q^2‖ + ‖s2*Work.Kernels.E4Fun z‖ + ‖(1-24*q)*s4‖ + ‖s6‖ := by
    have h1 : ‖((720:ℂ)*q - (5760:ℂ)*q^2) + s2*Work.Kernels.E4Fun z + (1-24*q)*s4 - s6‖
        ≤ ‖((720:ℂ)*q - (5760:ℂ)*q^2) + s2*Work.Kernels.E4Fun z + (1-24*q)*s4‖ + ‖s6‖ :=
      norm_sub_le _ _
    have h2' : ‖((720:ℂ)*q - (5760:ℂ)*q^2) + s2*Work.Kernels.E4Fun z + (1-24*q)*s4‖
        ≤ ‖((720:ℂ)*q - (5760:ℂ)*q^2) + s2*Work.Kernels.E4Fun z‖ + ‖(1-24*q)*s4‖ :=
      norm_add_le _ _
    have h3 : ‖((720:ℂ)*q - (5760:ℂ)*q^2) + s2*Work.Kernels.E4Fun z‖
        ≤ ‖(720:ℂ)*q - (5760:ℂ)*q^2‖ + ‖s2*Work.Kernels.E4Fun z‖ := norm_add_le _ _
    linarith
  rw [hkey]
  linarith [htri, hb1, hb2, hb3, hb4]

/-- `‖5 E₄² - 7 E₄ E₂² + 2 E₆ E₂‖ ≤ C ‖q‖²` on `{Im τ ≥ 1/3}`. -/
private lemma bound_four {C2 C4 C6 : ℝ} (hC2 : 0 ≤ C2) (hC4 : 0 ≤ C4) (hC6 : 0 ≤ C6)
    (h2 : ∀ z : ℍ, 1 / 3 ≤ z.im →
      ‖Work.Kernels.E2Fun z - 1 + 24 * Work.Kernels.qParamFun z‖ ≤
        C2 * ‖Work.Kernels.qParamFun z‖ ^ 2)
    (h4 : ∀ z : ℍ, 1 / 3 ≤ z.im →
      ‖Work.Kernels.E4Fun z - 1 - 240 * Work.Kernels.qParamFun z‖ ≤
        C4 * ‖Work.Kernels.qParamFun z‖ ^ 2)
    (h6 : ∀ z : ℍ, 1 / 3 ≤ z.im →
      ‖Work.Kernels.E6Fun z - 1 + 504 * Work.Kernels.qParamFun z‖ ≤
        C6 * ‖Work.Kernels.qParamFun z‖ ^ 2) :
    ∀ z : ℍ, 1 / 3 ≤ z.im →
      ‖5 * Work.Kernels.E4Fun z ^ 2 - 7 * Work.Kernels.E4Fun z * Work.Kernels.E2Fun z ^ 2
          + 2 * Work.Kernels.E6Fun z * Work.Kernels.E2Fun z‖ ≤
        (388800 + 967680 + 5 * C4 * (482 + C4) + 7 * C4 * (25 + C2) ^ 2
            + 7 * 241 * C2 * (50 + C2) + 2 * C6 * (25 + C2) + 2 * 505 * C2)
          * ‖Work.Kernels.qParamFun z‖ ^ 2 := by
  intro z hz
  have hz0 : (0:ℝ) ≤ z.im := le_trans (by norm_num) hz
  set q : ℂ := Work.Kernels.qParamFun z with hq
  have hqn : (0:ℝ) ≤ ‖q‖ := norm_nonneg q
  have hq1 : ‖q‖ ≤ 1 := qparam_norm_le_one hz0
  have hq2 : ‖q‖^2 ≤ ‖q‖ := by
    simpa using pow_le_pow_of_le_one hqn hq1 (by norm_num : 1 ≤ 2)
  have hq2one : ‖q‖^2 ≤ 1 := by
    simpa using pow_le_pow_of_le_one hqn hq1 (by norm_num : (0:ℕ) ≤ 2)
  set s2 : ℂ := Work.Kernels.E2Fun z - 1 + 24 * q with hs2
  set s4 : ℂ := Work.Kernels.E4Fun z - 1 - 240 * q with hs4
  set s6 : ℂ := Work.Kernels.E6Fun z - 1 + 504 * q with hs6
  have hs2b : ‖s2‖ ≤ C2 * ‖q‖^2 := by rw [hs2]; simpa [hq] using h2 z hz
  have hs4b : ‖s4‖ ≤ C4 * ‖q‖^2 := by rw [hs4]; simpa [hq] using h4 z hz
  have hs6b : ‖s6‖ ≤ C6 * ‖q‖^2 := by rw [hs6]; simpa [hq] using h6 z hz
  have hA2 : ‖(1:ℂ) - 24*q‖ ≤ 25 := by
    calc ‖(1:ℂ) - 24*q‖ ≤ ‖(1:ℂ)‖ + ‖24*q‖ := norm_sub_le _ _
      _ = 1 + 24*‖q‖ := by rw [norm_mul]; norm_num
      _ ≤ 25 := by linarith [hqn, hq1]
  have hA4 : ‖(1:ℂ) + 240*q‖ ≤ 241 := by
    calc ‖(1:ℂ) + 240*q‖ ≤ ‖(1:ℂ)‖ + ‖240*q‖ := norm_add_le _ _
      _ = 1 + 240*‖q‖ := by rw [norm_mul]; norm_num
      _ ≤ 241 := by linarith [hqn, hq1]
  have hA6 : ‖(1:ℂ) - 504*q‖ ≤ 505 := by
    calc ‖(1:ℂ) - 504*q‖ ≤ ‖(1:ℂ)‖ + ‖504*q‖ := norm_sub_le _ _
      _ = 1 + 504*‖q‖ := by rw [norm_mul]; norm_num
      _ ≤ 505 := by linarith [hqn, hq1]
  have hE2 : Work.Kernels.E2Fun z = (1 - 24*q) + s2 := by rw [hs2]; ring
  have hE4 : Work.Kernels.E4Fun z = (1 + 240*q) + s4 := by rw [hs4]; ring
  have hE6 : Work.Kernels.E6Fun z = (1 - 504*q) + s6 := by rw [hs6]; ring
  have hE2size : ‖Work.Kernels.E2Fun z‖ ≤ 25 + C2 := by
    rw [hE2]
    calc ‖(1 - 24*q) + s2‖ ≤ ‖(1:ℂ) - 24*q‖ + ‖s2‖ := norm_add_le _ _
      _ ≤ 25 + C2 := by
          have h : C2 * ‖q‖^2 ≤ C2 := by nlinarith [hq2one, hC2]
          linarith [hA2, hs2b]
  have hE4size : ‖Work.Kernels.E4Fun z‖ ≤ 241 + C4 := by
    rw [hE4]
    calc ‖(1 + 240*q) + s4‖ ≤ ‖(1:ℂ) + 240*q‖ + ‖s4‖ := norm_add_le _ _
      _ ≤ 241 + C4 := by
          have h : C4 * ‖q‖^2 ≤ C4 := by nlinarith [hq2one, hC4]
          linarith [hA4, hs4b]
  have hsum2 : ‖Work.Kernels.E2Fun z + (1-24*q)‖ ≤ 50 + C2 := by
    calc ‖Work.Kernels.E2Fun z + (1-24*q)‖
        ≤ ‖Work.Kernels.E2Fun z‖ + ‖(1:ℂ) - 24*q‖ := norm_add_le _ _
      _ ≤ 50 + C2 := by linarith
  have hsum4 : ‖Work.Kernels.E4Fun z + (1+240*q)‖ ≤ 482 + C4 := by
    calc ‖Work.Kernels.E4Fun z + (1+240*q)‖
        ≤ ‖Work.Kernels.E4Fun z‖ + ‖(1:ℂ) + 240*q‖ := norm_add_le _ _
      _ ≤ 482 + C4 := by linarith
  have hkey : 5 * Work.Kernels.E4Fun z ^ 2 - 7 * Work.Kernels.E4Fun z * Work.Kernels.E2Fun z ^ 2
        + 2 * Work.Kernels.E6Fun z * Work.Kernels.E2Fun z
      = ((388800:ℂ)*q^2 - (967680:ℂ)*q^3) + 5*s4*(Work.Kernels.E4Fun z + (1+240*q))
        - 7*s4*Work.Kernels.E2Fun z^2 - 7*(1+240*q)*s2*(Work.Kernels.E2Fun z + (1-24*q))
        + 2*s6*Work.Kernels.E2Fun z + 2*(1-504*q)*s2 := by
    rw [hE2, hE4, hE6]; ring
  have hb1 : ‖(388800:ℂ)*q^2 - (967680:ℂ)*q^3‖ ≤ (388800 + 967680) * ‖q‖^2 := by
    calc ‖(388800:ℂ)*q^2 - (967680:ℂ)*q^3‖ ≤ ‖(388800:ℂ)*q^2‖ + ‖(967680:ℂ)*q^3‖ := norm_sub_le _ _
      _ = 388800*‖q‖^2 + 967680*‖q‖^3 := by rw [norm_mul, norm_mul, norm_pow, norm_pow]; norm_num
      _ ≤ (388800 + 967680) * ‖q‖^2 := by
          have h32 : ‖q‖^3 ≤ ‖q‖^2 := by
            simpa using pow_le_pow_of_le_one hqn hq1 (by norm_num : 2 ≤ 3)
          linarith
  have hb2 : ‖(5:ℂ)*s4*(Work.Kernels.E4Fun z + (1+240*q))‖ ≤ 5*C4*(482+C4)*‖q‖^2 := by
    rw [norm_mul, norm_mul]
    calc ‖(5:ℂ)‖ * ‖s4‖ * ‖Work.Kernels.E4Fun z + (1+240*q)‖
        ≤ 5 * (C4*‖q‖^2) * (482 + C4) := by
          rw [show ‖(5:ℂ)‖ = 5 by norm_num]
          exact mul_le_mul (mul_le_mul_of_nonneg_left hs4b (by norm_num)) hsum4 (norm_nonneg _) (by positivity)
      _ = 5*C4*(482+C4)*‖q‖^2 := by ring
  have hb3 : ‖(7:ℂ)*s4*Work.Kernels.E2Fun z^2‖ ≤ 7*C4*(25+C2)^2*‖q‖^2 := by
    rw [norm_mul, norm_mul, norm_pow]
    calc ‖(7:ℂ)‖ * ‖s4‖ * ‖Work.Kernels.E2Fun z‖^2
        ≤ 7 * (C4*‖q‖^2) * (25+C2)^2 := by
          rw [show ‖(7:ℂ)‖ = 7 by norm_num]
          have h2s : ‖Work.Kernels.E2Fun z‖^2 ≤ (25+C2)^2 :=
            pow_le_pow_left₀ (norm_nonneg _) hE2size 2
          exact mul_le_mul (mul_le_mul_of_nonneg_left hs4b (by norm_num)) h2s (by positivity) (by positivity)
      _ = 7*C4*(25+C2)^2*‖q‖^2 := by ring
  have hb4 : ‖(7:ℂ)*(1+240*q)*s2*(Work.Kernels.E2Fun z + (1-24*q))‖
      ≤ 7*241*C2*(50+C2)*‖q‖^2 := by
    rw [norm_mul, norm_mul, norm_mul]
    have h7A4 : ‖(7:ℂ)‖ * ‖(1:ℂ) + 240*q‖ ≤ 7 * 241 := by
      have h7 : ‖(7:ℂ)‖ = 7 := by norm_num
      rw [h7]
      linarith [hA4]
    calc ‖(7:ℂ)‖ * ‖(1:ℂ) + 240*q‖ * ‖s2‖ * ‖Work.Kernels.E2Fun z + (1-24*q)‖
        ≤ (7*241) * (C2*‖q‖^2) * (50 + C2) :=
          mul_le_mul (mul_le_mul h7A4 hs2b (norm_nonneg _) (by norm_num)) hsum2 (norm_nonneg _) (by positivity)
      _ = 7*241*C2*(50+C2)*‖q‖^2 := by ring
  have hb5 : ‖(2:ℂ)*s6*Work.Kernels.E2Fun z‖ ≤ 2*C6*(25+C2)*‖q‖^2 := by
    rw [norm_mul, norm_mul]
    calc ‖(2:ℂ)‖ * ‖s6‖ * ‖Work.Kernels.E2Fun z‖
        ≤ 2 * (C6*‖q‖^2) * (25 + C2) := by
          rw [show ‖(2:ℂ)‖ = 2 by norm_num]
          exact mul_le_mul (mul_le_mul_of_nonneg_left hs6b (by norm_num)) hE2size (norm_nonneg _) (by positivity)
      _ = 2*C6*(25+C2)*‖q‖^2 := by ring
  have hb6 : ‖(2:ℂ)*(1-504*q)*s2‖ ≤ 2*505*C2*‖q‖^2 := by
    rw [norm_mul, norm_mul]
    have h2A6 : ‖(2:ℂ)‖ * ‖(1:ℂ) - 504*q‖ ≤ 2*505 := by
      have h2 : ‖(2:ℂ)‖ = 2 := by norm_num
      rw [h2]
      linarith [hA6]
    calc ‖(2:ℂ)‖ * ‖(1:ℂ) - 504*q‖ * ‖s2‖ ≤ (2*505) * (C2*‖q‖^2) :=
          mul_le_mul h2A6 hs2b (norm_nonneg _) (by norm_num)
      _ = 2*505*C2*‖q‖^2 := by ring
  have htri : ‖((388800:ℂ)*q^2 - (967680:ℂ)*q^3) + 5*s4*(Work.Kernels.E4Fun z + (1+240*q))
        - 7*s4*Work.Kernels.E2Fun z^2 - 7*(1+240*q)*s2*(Work.Kernels.E2Fun z + (1-24*q))
        + 2*s6*Work.Kernels.E2Fun z + 2*(1-504*q)*s2‖
      ≤ ‖(388800:ℂ)*q^2 - (967680:ℂ)*q^3‖ + ‖5*s4*(Work.Kernels.E4Fun z + (1+240*q))‖
        + ‖7*s4*Work.Kernels.E2Fun z^2‖ + ‖7*(1+240*q)*s2*(Work.Kernels.E2Fun z + (1-24*q))‖
        + ‖2*s6*Work.Kernels.E2Fun z‖ + ‖2*(1-504*q)*s2‖ := by
    have h1 : ‖((388800:ℂ)*q^2 - (967680:ℂ)*q^3) + 5*s4*(Work.Kernels.E4Fun z + (1+240*q))
        - 7*s4*Work.Kernels.E2Fun z^2 - 7*(1+240*q)*s2*(Work.Kernels.E2Fun z + (1-24*q))
        + 2*s6*Work.Kernels.E2Fun z + 2*(1-504*q)*s2‖
        ≤ ‖((388800:ℂ)*q^2 - (967680:ℂ)*q^3) + 5*s4*(Work.Kernels.E4Fun z + (1+240*q))
        - 7*s4*Work.Kernels.E2Fun z^2 - 7*(1+240*q)*s2*(Work.Kernels.E2Fun z + (1-24*q))
        + 2*s6*Work.Kernels.E2Fun z‖ + ‖2*(1-504*q)*s2‖ := norm_add_le _ _
    have h2' : ‖((388800:ℂ)*q^2 - (967680:ℂ)*q^3) + 5*s4*(Work.Kernels.E4Fun z + (1+240*q))
        - 7*s4*Work.Kernels.E2Fun z^2 - 7*(1+240*q)*s2*(Work.Kernels.E2Fun z + (1-24*q))
        + 2*s6*Work.Kernels.E2Fun z‖
        ≤ ‖((388800:ℂ)*q^2 - (967680:ℂ)*q^3) + 5*s4*(Work.Kernels.E4Fun z + (1+240*q))
        - 7*s4*Work.Kernels.E2Fun z^2 - 7*(1+240*q)*s2*(Work.Kernels.E2Fun z + (1-24*q))‖
        + ‖2*s6*Work.Kernels.E2Fun z‖ := norm_add_le _ _
    have h3 : ‖((388800:ℂ)*q^2 - (967680:ℂ)*q^3) + 5*s4*(Work.Kernels.E4Fun z + (1+240*q))
        - 7*s4*Work.Kernels.E2Fun z^2 - 7*(1+240*q)*s2*(Work.Kernels.E2Fun z + (1-24*q))‖
        ≤ ‖((388800:ℂ)*q^2 - (967680:ℂ)*q^3) + 5*s4*(Work.Kernels.E4Fun z + (1+240*q))
        - 7*s4*Work.Kernels.E2Fun z^2‖
        + ‖7*(1+240*q)*s2*(Work.Kernels.E2Fun z + (1-24*q))‖ := norm_sub_le _ _
    have h4 : ‖((388800:ℂ)*q^2 - (967680:ℂ)*q^3) + 5*s4*(Work.Kernels.E4Fun z + (1+240*q))
        - 7*s4*Work.Kernels.E2Fun z^2‖
        ≤ ‖((388800:ℂ)*q^2 - (967680:ℂ)*q^3) + 5*s4*(Work.Kernels.E4Fun z + (1+240*q))‖
        + ‖7*s4*Work.Kernels.E2Fun z^2‖ := norm_sub_le _ _
    have h5 : ‖((388800:ℂ)*q^2 - (967680:ℂ)*q^3) + 5*s4*(Work.Kernels.E4Fun z + (1+240*q))‖
        ≤ ‖(388800:ℂ)*q^2 - (967680:ℂ)*q^3‖ + ‖5*s4*(Work.Kernels.E4Fun z + (1+240*q))‖ :=
      norm_add_le _ _
    linarith
  rw [hkey]
  linarith [htri, hb1, hb2, hb3, hb4, hb5, hb6]

/-- **The four combinations are cusp forms at `i∞`.**  There is a constant `C > 0`
such that on `{Im τ ≥ 1/3}` the weight-`4`, `6`, `6` combinations `E₄ - E₂²`,
`E₂E₆ - E₄²`, `E₂E₄ - E₆` are `≤ C ‖q‖` and the weight-`8` combination
`5E₄² - 7E₄E₂² + 2E₆E₂` is `≤ C ‖q‖²`. -/
theorem cusp_forms :
    ∃ C : ℝ, 0 < C ∧
      (∀ z : UpperHalfPlane, 1 / 3 ≤ z.im →
        ‖Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2‖ ≤ C * ‖Work.Kernels.qParamFun z‖) ∧
      (∀ z : UpperHalfPlane, 1 / 3 ≤ z.im →
        ‖Work.Kernels.E2Fun z * Work.Kernels.E6Fun z - Work.Kernels.E4Fun z ^ 2‖ ≤ C * ‖Work.Kernels.qParamFun z‖) ∧
      (∀ z : UpperHalfPlane, 1 / 3 ≤ z.im →
        ‖Work.Kernels.E2Fun z * Work.Kernels.E4Fun z - Work.Kernels.E6Fun z‖ ≤ C * ‖Work.Kernels.qParamFun z‖) ∧
      (∀ z : UpperHalfPlane, 1 / 3 ≤ z.im →
        ‖5 * Work.Kernels.E4Fun z ^ 2 - 7 * Work.Kernels.E4Fun z * Work.Kernels.E2Fun z ^ 2
          + 2 * Work.Kernels.E6Fun z * Work.Kernels.E2Fun z‖ ≤ C * ‖Work.Kernels.qParamFun z‖ ^ 2) := by
  obtain ⟨C2, hC2pos, h2⟩ := E2Fun_two_term_third
  obtain ⟨C4, hC4pos, h4⟩ := E4Fun_two_term_third
  obtain ⟨C6, hC6pos, h6⟩ := E6Fun_two_term_third
  have hC2 : 0 ≤ C2 := hC2pos.le
  have hC4 : 0 ≤ C4 := hC4pos.le
  have hC6 : 0 ≤ C6 := hC6pos.le
  set K1 : ℝ := C4 + 864 + 50 * C2 + C2 ^ 2 with hK1
  set K2 : ℝ := 1008 + 45504 + C2 * (505 + C6) + 25 * C6 + C4 * (482 + C4) with hK2
  set K3 : ℝ := 720 + 5760 + C2 * (241 + C4) + 25 * C4 + C6 with hK3
  set K4 : ℝ := 388800 + 967680 + 5 * C4 * (482 + C4) + 7 * C4 * (25 + C2) ^ 2
      + 7 * 241 * C2 * (50 + C2) + 2 * C6 * (25 + C2) + 2 * 505 * C2 with hK4
  have hK1pos : 0 < K1 := by rw [hK1]; positivity
  have hK2pos : 0 < K2 := by rw [hK2]; positivity
  have hK3pos : 0 < K3 := by rw [hK3]; positivity
  have hK4pos : 0 < K4 := by rw [hK4]; positivity
  refine ⟨K1 + K2 + K3 + K4 + 1, by linarith, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have hb : ‖Work.Kernels.E4Fun z - Work.Kernels.E2Fun z ^ 2‖ ≤ K1 * ‖Work.Kernels.qParamFun z‖ := by
      rw [hK1]; exact bound_one hC2 hC4 h2 h4 z hz
    have hq : (0:ℝ) ≤ ‖Work.Kernels.qParamFun z‖ := norm_nonneg _
    have hmain : K1 * ‖Work.Kernels.qParamFun z‖
        ≤ (K1 + K2 + K3 + K4 + 1) * ‖Work.Kernels.qParamFun z‖ := by
      have h : (0:ℝ) ≤ (K2 + K3 + K4 + 1) * ‖Work.Kernels.qParamFun z‖ :=
        mul_nonneg (by linarith) hq
      nlinarith [h]
    linarith [hb, hmain]
  · intro z hz
    have hb : ‖Work.Kernels.E2Fun z * Work.Kernels.E6Fun z - Work.Kernels.E4Fun z ^ 2‖
        ≤ K2 * ‖Work.Kernels.qParamFun z‖ := by
      rw [hK2]; exact bound_two hC2 hC4 hC6 h2 h4 h6 z hz
    have hq : (0:ℝ) ≤ ‖Work.Kernels.qParamFun z‖ := norm_nonneg _
    have hmain : K2 * ‖Work.Kernels.qParamFun z‖
        ≤ (K1 + K2 + K3 + K4 + 1) * ‖Work.Kernels.qParamFun z‖ := by
      have h : (0:ℝ) ≤ (K1 + K3 + K4 + 1) * ‖Work.Kernels.qParamFun z‖ :=
        mul_nonneg (by linarith) hq
      nlinarith [h]
    linarith [hb, hmain]
  · intro z hz
    have hb : ‖Work.Kernels.E2Fun z * Work.Kernels.E4Fun z - Work.Kernels.E6Fun z‖
        ≤ K3 * ‖Work.Kernels.qParamFun z‖ := by
      rw [hK3]; exact bound_three hC2 hC4 hC6 h2 h4 h6 z hz
    have hq : (0:ℝ) ≤ ‖Work.Kernels.qParamFun z‖ := norm_nonneg _
    have hmain : K3 * ‖Work.Kernels.qParamFun z‖
        ≤ (K1 + K2 + K3 + K4 + 1) * ‖Work.Kernels.qParamFun z‖ := by
      have h : (0:ℝ) ≤ (K1 + K2 + K4 + 1) * ‖Work.Kernels.qParamFun z‖ :=
        mul_nonneg (by linarith) hq
      nlinarith [h]
    linarith [hb, hmain]
  · intro z hz
    have hb : ‖5 * Work.Kernels.E4Fun z ^ 2 - 7 * Work.Kernels.E4Fun z * Work.Kernels.E2Fun z ^ 2
          + 2 * Work.Kernels.E6Fun z * Work.Kernels.E2Fun z‖
        ≤ K4 * ‖Work.Kernels.qParamFun z‖ ^ 2 := by
      rw [hK4]; exact bound_four hC2 hC4 hC6 h2 h4 h6 z hz
    have hq : (0:ℝ) ≤ ‖Work.Kernels.qParamFun z‖ ^ 2 := by positivity
    have hmain : K4 * ‖Work.Kernels.qParamFun z‖ ^ 2
        ≤ (K1 + K2 + K3 + K4 + 1) * ‖Work.Kernels.qParamFun z‖ ^ 2 := by
      have h : (0:ℝ) ≤ (K1 + K2 + K3 + 1) * ‖Work.Kernels.qParamFun z‖ ^ 2 :=
        mul_nonneg (by linarith) hq
      nlinarith [h]
    linarith [hb, hmain]

end

end Work.Asymptotics.ZAtomsThird
