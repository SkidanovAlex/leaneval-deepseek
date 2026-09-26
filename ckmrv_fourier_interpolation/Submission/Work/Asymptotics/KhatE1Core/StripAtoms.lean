import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.zAtomDevEisensteinFourthOrder
import Submission.Work.Asymptotics.KhatE1Core.zAtomDevFourthOrder
import Submission.Work.Asymptotics.funnel_tauAtom_second_order
import Submission.Work.Asymptotics.Compact.kminus_tail_core

/-!
# The cusp truncations of the `z`-atoms on the strip `3 ≤ Im z`

This module packages, as a single statement, the *explicit truncations* of the `z`-atoms of the
funnel bracket together with the size of the remainder.  Writing `q = qParamFun z` (so that
`‖q‖ = exp (-2 π Im z)` and `q = (Ept z)²`), the atoms are

  `E₂ = E2tr q + O(q³)`, `E₄ = E4tr q + O(q³)`, `E₆ = E6tr q + O(q³)`,
  `E₈ = E8tr q + O(q³)`, `E₁₀ = E10tr q + O(q³)`, `Δ = Dtr q + O(q⁴)`,

with the explicit polynomials below.  The product truncations are *consistent*: `E8tr` is the
`q²`-truncation of `E4tr²` and `E10tr` that of `E4tr·E6tr`, the remainders being the explicit
low-degree polynomials recorded in `E4tr_sq` / `E4tr_mul_E6tr`.

These are the data from which the `q`-order of every monomial of the cleared residual is read
off; the remainders are dominated by the weight calculus of the companion modules, the weights
being those of `Wt p q` with `e = Ept z` of weight `Wt 1 0` and `q` of weight `Wt 2 0`. -/

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane

noncomputable section

/-- Truncation of `E₂` to order `q²`. -/
def E2tr (q : ℂ) : ℂ := 1 - 24 * q - 72 * q ^ 2

/-- Truncation of `E₄` to order `q²`. -/
def E4tr (q : ℂ) : ℂ := 1 + 240 * q + 2160 * q ^ 2

/-- Truncation of `E₆` to order `q²`. -/
def E6tr (q : ℂ) : ℂ := 1 - 504 * q - 16632 * q ^ 2

/-- Truncation of `E₈ = E₄²` to order `q²`. -/
def E8tr (q : ℂ) : ℂ := 1 + 480 * q + 61920 * q ^ 2

/-- Truncation of `E₁₀ = E₄E₆` to order `q²`. -/
def E10tr (q : ℂ) : ℂ := 1 - 264 * q - 135432 * q ^ 2

/-- Truncation of `E₁₄ = E₄²E₆` to order `q²`. -/
def E14tr (q : ℂ) : ℂ := 1 - 24 * q - 196632 * q ^ 2

/-- Truncation of `Δ` to order `q³`. -/
def Dtr (q : ℂ) : ℂ := q - 24 * q ^ 2 + 252 * q ^ 3

/-- Truncation of `E₄³` to order `q²`. -/
def E4cuber (q : ℂ) : ℂ := 1 + 720 * q + 179280 * q ^ 2

/-! ## Consistency of the product truncations (`ring`) -/

lemma E4tr_sq (q : ℂ) : E4tr q ^ 2 = E8tr q + 1036800 * q ^ 3 + 4665600 * q ^ 4 := by
  rw [E4tr, E8tr]; ring

lemma E4tr_mul_E6tr (q : ℂ) : E4tr q * E6tr q
    = E10tr q - 5080320 * q ^ 3 - 35925120 * q ^ 4 := by
  rw [E4tr, E6tr, E10tr]; ring

lemma E4tr_sq_mul_E6tr (q : ℂ) : E4tr q ^ 2 * E6tr q
    = E14tr q - 38154240 * q ^ 3 - 1547735040 * q ^ 4 - 19595520000 * q ^ 5
      - 77598259200 * q ^ 6 := by
  rw [E4tr, E6tr, E14tr]; ring

lemma E4tr_cube (q : ℂ) : E4tr q ^ 3
    = E4cuber q + 16934400 * q ^ 3 + 387244800 * q ^ 4 + 3359232000 * q ^ 5
      + 10077696000 * q ^ 6 := by
  rw [E4tr, E4cuber]; ring

/-! ## Elementary norm bounds -/

lemma E4tr_norm_le {q : ℂ} (hq : ‖q‖ ≤ 1) : ‖E4tr q‖ ≤ 2401 := by
  have h2 : ‖(240 : ℂ) * q‖ = 240 * ‖q‖ := by rw [norm_mul, Complex.norm_ofNat]
  have h3 : ‖(2160 : ℂ) * q ^ 2‖ = 2160 * ‖q‖ ^ 2 := by
    rw [norm_mul, Complex.norm_ofNat, norm_pow]
  have hp : ‖q‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg q) hq (n := 2)
  have a := norm_add_le ((1 : ℂ) + 240 * q) ((2160 : ℂ) * q ^ 2)
  have b := norm_add_le (1 : ℂ) ((240 : ℂ) * q)
  rw [norm_one, h2] at b
  rw [h3] at a
  rw [E4tr]
  nlinarith [a, b, hp, norm_nonneg q, hq]

lemma E6tr_norm_le {q : ℂ} (hq : ‖q‖ ≤ 1) : ‖E6tr q‖ ≤ 17300 := by
  have h2 : ‖(504 : ℂ) * q‖ = 504 * ‖q‖ := by rw [norm_mul, Complex.norm_ofNat]
  have h3 : ‖(16632 : ℂ) * q ^ 2‖ = 16632 * ‖q‖ ^ 2 := by
    rw [norm_mul, Complex.norm_ofNat, norm_pow]
  have hp : ‖q‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg q) hq (n := 2)
  have b : ‖(1 : ℂ) - 504 * q‖ ≤ 1 + 504 * ‖q‖ := by
    have h := norm_sub_le (1 : ℂ) ((504 : ℂ) * q)
    rw [norm_one, h2] at h
    exact h
  have a : ‖(1 : ℂ) - 504 * q - (16632 : ℂ) * q ^ 2‖
      ≤ (1 + 504 * ‖q‖) + 16632 * ‖q‖ ^ 2 := by
    have h := norm_sub_le ((1 : ℂ) - 504 * q) ((16632 : ℂ) * q ^ 2)
    rw [h3] at h
    exact le_trans h (add_le_add b le_rfl)
  rw [E6tr]
  nlinarith [a, b, hp, norm_nonneg q, hq]

lemma qpow_le_one {q : ℂ} (hq : ‖q‖ ≤ 1) (n : ℕ) : ‖q‖ ^ n ≤ 1 :=
  pow_le_one₀ (norm_nonneg q) hq

/-- `‖A²‖ ≤ c²‖q‖³` when `‖A‖ ≤ c‖q‖³` and `‖q‖ ≤ 1`. -/
lemma norm_sq_dev {A q : ℂ} {c : ℝ} (hc : 0 ≤ c) (hq : ‖q‖ ≤ 1) (hA : ‖A‖ ≤ c * ‖q‖ ^ 3) :
    ‖A ^ 2‖ ≤ c ^ 2 * ‖q‖ ^ 3 := by
  rw [norm_pow]
  have h3 : (0 : ℝ) ≤ ‖q‖ ^ 3 := by positivity
  have h6 : ‖q‖ ^ 6 ≤ ‖q‖ ^ 3 := by
    have h : ‖q‖ ^ 6 = ‖q‖ ^ 3 * ‖q‖ ^ 3 := by ring
    rw [h]
    nlinarith [pow_le_one₀ (norm_nonneg q) hq (n := 3)]
  calc ‖A‖ ^ 2 ≤ (c * ‖q‖ ^ 3) ^ 2 := pow_le_pow_left₀ (norm_nonneg A) hA 2
    _ = c ^ 2 * ‖q‖ ^ 6 := by ring
    _ ≤ c ^ 2 * ‖q‖ ^ 3 := mul_le_mul_of_nonneg_left h6 (by positivity)

/-- `‖A·B‖ ≤ c·c'·‖q‖³` when `‖A‖ ≤ c‖q‖³`, `‖B‖ ≤ c'‖q‖³`, `‖q‖ ≤ 1`. -/
lemma norm_mul_dev {A B q : ℂ} {c c' : ℝ} (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hq : ‖q‖ ≤ 1) (hA : ‖A‖ ≤ c * ‖q‖ ^ 3) (hB : ‖B‖ ≤ c' * ‖q‖ ^ 3) :
    ‖A * B‖ ≤ c * c' * ‖q‖ ^ 3 := by
  rw [norm_mul]
  have h3 : (0 : ℝ) ≤ ‖q‖ ^ 3 := by positivity
  have h6 : ‖q‖ ^ 6 ≤ ‖q‖ ^ 3 := by
    have h : ‖q‖ ^ 6 = ‖q‖ ^ 3 * ‖q‖ ^ 3 := by ring
    rw [h]
    nlinarith [pow_le_one₀ (norm_nonneg q) hq (n := 3)]
  have h0 : (0 : ℝ) ≤ c * ‖q‖ ^ 3 := mul_nonneg hc h3
  calc ‖A‖ * ‖B‖ ≤ (c * ‖q‖ ^ 3) * (c' * ‖q‖ ^ 3) :=
        mul_le_mul hA hB (norm_nonneg _) h0
    _ = c * c' * ‖q‖ ^ 6 := by ring
    _ ≤ c * c' * ‖q‖ ^ 3 := mul_le_mul_of_nonneg_left h6 (by positivity)

/-- `‖B·A‖ ≤ c·B₀·‖q‖³` when `‖A‖ ≤ c‖q‖³` and `‖B‖ ≤ B₀`. -/
lemma norm_mul_dev_left {A B q : ℂ} {c B0 : ℝ} (hc : 0 ≤ c) (hB0 : 0 ≤ B0)
    (hq : ‖q‖ ≤ 1) (hA : ‖A‖ ≤ c * ‖q‖ ^ 3) (hB : ‖B‖ ≤ B0) :
    ‖B * A‖ ≤ B0 * c * ‖q‖ ^ 3 := by
  rw [norm_mul]
  calc ‖B‖ * ‖A‖ ≤ B0 * (c * ‖q‖ ^ 3) := mul_le_mul hB hA (norm_nonneg _) hB0
    _ = B0 * c * ‖q‖ ^ 3 := by ring

/-- `‖c·q^m‖ ≤ ‖c‖·‖q‖` for `m ≥ 1`, `‖q‖ ≤ 1`. -/
lemma norm_const_qpow_le_one {c q : ℂ} {m : ℕ} (hm : 1 ≤ m) (hq : ‖q‖ ≤ 1) :
    ‖c * q ^ m‖ ≤ ‖c‖ * ‖q‖ := by
  rw [norm_mul, norm_pow]
  have hq0 : (0 : ℝ) ≤ ‖q‖ := norm_nonneg q
  obtain ⟨j, rfl⟩ : ∃ j, m = 1 + j := ⟨m - 1, by omega⟩
  rw [pow_add]
  simp only [pow_one]
  calc ‖c‖ * (‖q‖ * ‖q‖ ^ j) ≤ ‖c‖ * (‖q‖ * 1) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (pow_le_one₀ hq0 hq (n := j)) hq0)
          (norm_nonneg c)
    _ = ‖c‖ * ‖q‖ := by ring

/-- `‖q‖ ^ m ≤ ‖q‖` for `m ≥ 1`, `‖q‖ ≤ 1`. -/
lemma qpow_le_self {q : ℂ} {m : ℕ} (hm : 1 ≤ m) (hq : ‖q‖ ≤ 1) : ‖q‖ ^ m ≤ ‖q‖ := by
  have hq0 : (0 : ℝ) ≤ ‖q‖ := norm_nonneg q
  obtain ⟨j, rfl⟩ : ∃ j, m = 1 + j := ⟨m - 1, by omega⟩
  rw [pow_add]
  simp only [pow_one]
  calc ‖q‖ * ‖q‖ ^ j ≤ ‖q‖ * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hq0 hq (n := j)) hq0
    _ = ‖q‖ := by ring

/-- `‖a + b + c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖`. -/
lemma norm_add4_le (a b c d : ℂ) : ‖a + b + c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
  have h1 := norm_add_le (a + b + c) d
  have h2 := norm_add_le (a + b) c
  have h3 := norm_add_le a b
  linarith

/-- `‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖`. -/
lemma norm_add3_le (a b c : ℂ) : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
  have h1 := norm_add_le (a + b) c
  have h2 := norm_add_le a b
  linarith

/-- `‖a + b‖ ≤ ‖a‖ + ‖b‖` in the `c‖q‖³` shape. -/
lemma norm_add_dev {A B q : ℂ} {c c' : ℝ} (hA : ‖A‖ ≤ c * ‖q‖ ^ 3)
    (hB : ‖B‖ ≤ c' * ‖q‖ ^ 3) : ‖A + B‖ ≤ (c + c') * ‖q‖ ^ 3 := by
  calc ‖A + B‖ ≤ ‖A‖ + ‖B‖ := norm_add_le _ _
    _ ≤ c * ‖q‖ ^ 3 + c' * ‖q‖ ^ 3 := add_le_add hA hB
    _ = (c + c') * ‖q‖ ^ 3 := by ring

/-- A constant multiple of `q ^ m`, `m ≥ 3`, is `O(‖q‖³)`. -/
lemma norm_const_qpow_le {c : ℂ} {q : ℂ} {m : ℕ} (hm : 3 ≤ m) (hq : ‖q‖ ≤ 1) :
    ‖c * q ^ m‖ ≤ ‖c‖ * ‖q‖ ^ 3 := by
  rw [norm_mul, norm_pow]
  have h3 : (0 : ℝ) ≤ ‖q‖ ^ 3 := by positivity
  have hq0 : (0 : ℝ) ≤ ‖q‖ := norm_nonneg q
  obtain ⟨j, rfl⟩ : ∃ j, m = 3 + j := ⟨m - 3, by omega⟩
  have h : ‖q‖ ^ (3 + j) = ‖q‖ ^ 3 * ‖q‖ ^ j := by rw [pow_add]
  have hj : ‖q‖ ^ j ≤ 1 := pow_le_one₀ hq0 hq (n := j)
  rw [h]
  calc ‖c‖ * (‖q‖ ^ 3 * ‖q‖ ^ j) ≤ ‖c‖ * (‖q‖ ^ 3 * 1) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hj h3) (norm_nonneg c)
    _ = ‖c‖ * ‖q‖ ^ 3 := by ring



/-- **The `z`-atom truncations on the strip `3 ≤ Im z`.**  The atoms `E₂, E₄, E₆, E₈, E₁₀`
agree with their explicit `q`-truncations to order `q³`, and `Δ` to order `q⁴` (`q = qParamFun z`).
These are the atoms out of which the bracket `brMinus 8` and the `K₊`-correction `Φ` at the point
`z` are built. -/
theorem stripAtom_trunc (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ z : ℍ, 3 ≤ z.im →
      (‖Work.Kernels.E2Fun z - 1 + 24 * Work.Kernels.qParamFun z
          + 72 * (Work.Kernels.qParamFun z) ^ 2‖
        ≤ C * (Work.Kernels.scale z) ^ N * ‖Work.Kernels.qParamFun z‖ ^ 3) ∧
      (‖Work.Kernels.E4Fun z - 1 - 240 * Work.Kernels.qParamFun z
          - 2160 * (Work.Kernels.qParamFun z) ^ 2‖
        ≤ C * (Work.Kernels.scale z) ^ N * ‖Work.Kernels.qParamFun z‖ ^ 3) ∧
      (‖Work.Kernels.E6Fun z - 1 + 504 * Work.Kernels.qParamFun z
          + 16632 * (Work.Kernels.qParamFun z) ^ 2‖
        ≤ C * (Work.Kernels.scale z) ^ N * ‖Work.Kernels.qParamFun z‖ ^ 3) ∧
      (‖Work.Asymptotics.Compact.dE8 z
          - 61920 * (Work.Kernels.qParamFun z) ^ 2‖
        ≤ C * (Work.Kernels.scale z) ^ N * ‖Work.Kernels.qParamFun z‖ ^ 3) ∧
      (‖Work.Asymptotics.Compact.dE10 z
          + 135432 * (Work.Kernels.qParamFun z) ^ 2‖
        ≤ C * (Work.Kernels.scale z) ^ N * ‖Work.Kernels.qParamFun z‖ ^ 3) ∧
      (‖Work.Kernels.DeltaFun z - (Work.Kernels.qParamFun z
          - 24 * (Work.Kernels.qParamFun z) ^ 2
          + 252 * (Work.Kernels.qParamFun z) ^ 3)‖
        ≤ C * (Work.Kernels.scale z) ^ N * ‖Work.Kernels.qParamFun z‖ ^ 4) := by
  obtain ⟨C2, hC2, h2⟩ := Work.Asymptotics.E2Fun_second_order
  obtain ⟨C4, hC4, h4⟩ := Work.Asymptotics.E4Fun_second_order
  obtain ⟨C6, hC6, h6⟩ := Work.Asymptotics.E6Fun_second_order
  obtain ⟨CD, hCD, hD⟩ := Work.Asymptotics.DeltaFun_fourth_order
  obtain ⟨C8, hC8, h8, h6d, h10d⟩ := zAtomDevEisensteinFourthOrder
  set K : ℝ := C2 + C4 + C6 + CD + C8 + 1 with hKdef
  have hK0 : 0 < K := by rw [hKdef]; positivity
  have hKC2 : C2 ≤ K := by rw [hKdef]; linarith
  have hKC4 : C4 ≤ K := by rw [hKdef]; linarith
  have hKC6 : C6 ≤ K := by rw [hKdef]; linarith
  have hKCD : CD ≤ K := by rw [hKdef]; linarith
  have hKC8 : C8 ≤ K := by rw [hKdef]; linarith
  refine ⟨K, 0, hK0, le_rfl, fun z hz => ?_⟩
  have hz1 : (1 : ℝ) ≤ z.im := by linarith
  have hz2 : (2 : ℝ) ≤ z.im := by linarith
  have hq1 : ‖Work.Kernels.qParamFun z‖ ≤ 1 := by
    have h := Work.Asymptotics.norm_qParamFun_le z hz1
    have h2' : Real.exp (-(2 * Real.pi)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos]
    exact le_trans h h2'
  have hq3 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun z‖ ^ 3 := by positivity
  have hq4 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun z‖ ^ 4 := by positivity
  have hscale : (Work.Kernels.scale z) ^ (0 : ℝ) = 1 := Real.rpow_zero _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hscale, mul_one]; exact le_trans (h2 z hz1) (mul_le_mul_of_nonneg_right hKC2 hq3)
  · rw [hscale, mul_one]; exact le_trans (h4 z hz1) (mul_le_mul_of_nonneg_right hKC4 hq3)
  · rw [hscale, mul_one]; exact le_trans (h6 z hz1) (mul_le_mul_of_nonneg_right hKC6 hq3)
  · rw [hscale, mul_one]; exact le_trans (h8 z hz2) (mul_le_mul_of_nonneg_right hKC8 hq3)
  · rw [hscale, mul_one]; exact le_trans (h10d z hz2) (mul_le_mul_of_nonneg_right hKC8 hq3)
  · rw [hscale, mul_one]; exact le_trans (hD z hz1) (mul_le_mul_of_nonneg_right hKCD hq4)

end

end Work.Asymptotics.KhatE1Core
