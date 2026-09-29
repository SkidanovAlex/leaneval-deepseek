import Mathlib
import Submission.Work.C17.Bsubst_deps
import Submission.Work.C17.Js_bound
import Submission.Work.C17.B5_pullback
import Submission.Work.C17.B6_deriv
import Submission.Work.C17.B7_deriv
import Submission.Work.C7.g_form
import Submission.Work.C7.g67_deriv
import Submission.Work.C7.J_ode


/-!
# Area C17 — polynomial growth of the coefficients of `B_i ∘ y`

The seven pure functions `B₁,…,B₇` of Calagari–Dimitrov–Tang
(arXiv:2408.15403, eqs. `(defB)`, `(defB5)`, `(defB67)`) are power series in
the symmetrisation variable `y`; here we bound the growth of the coefficients
of their pullbacks `B_i(x²/(x−1))` along `y = x²/(x−1) = sympY`.

Mathematically these pullbacks are combinations of `log(1−x)`, `Li₂(x)`, the
`₃F₂`-type series `J` and the two integrals of `B₃/y`, `B₄/y` (the explicit
x-forms `Work.C7.g_form`, `Work.C7.g5_form`, `Work.C7.J_ode`,
`Work.C7.g67_deriv`), all of which have at most polynomially growing
coefficients (their singularities on the unit circle are
logarithmic/polynomial).  This module proves the coefficient-arithmetic half:
a toolbox for the predicate `BSubstBound f`, the bounds of the elementary
series, and the passage from the explicit x-forms to the bound of every
`B_i ∘ y`.
-/

open PowerSeries

namespace Work.C17

noncomputable section

/-- `0 ≤ n + 1` in `ℝ`, for `n : ℕ`. -/
lemma natCast_add_one_nonneg (n : ℕ) : (0 : ℝ) ≤ (n : ℝ) + 1 :=
  add_nonneg (Nat.cast_nonneg n) zero_le_one

/-- `0 < n + 1` in `ℝ`, for `n : ℕ`. -/
lemma natCast_add_one_pos (n : ℕ) : (0 : ℝ) < (n : ℝ) + 1 :=
  add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) one_pos

/-- `1 ≤ n + 1` in `ℝ`, for `n : ℕ`. -/
lemma one_le_natCast_add_one (n : ℕ) : (1 : ℝ) ≤ (n : ℝ) + 1 := by
  have h : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-! ## 1. The growth predicate and its algebra -/

/-- `BSubstBound f` says that the coefficients of `f : ℚ⟦x⟧`, viewed in `ℝ`,
grow at most polynomially. -/
def BSubstBound (f : PowerSeries ℚ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ, ∀ n : ℕ, |((PowerSeries.coeff n f : ℚ) : ℝ)| ≤ C * ((n : ℝ) + 1) ^ k

/-- The conclusion of the target theorem, for a single `f`. -/
lemma BSubstBound.weaken {f : PowerSeries ℚ} (h : BSubstBound f) :
    ∃ C : ℝ, ∃ k : ℕ, ∀ n : ℕ, |((PowerSeries.coeff n f : ℚ) : ℝ)| ≤ C * ((n : ℝ) + 1) ^ k := by
  obtain ⟨C, _, k, hk⟩ := h
  exact ⟨C, k, hk⟩

lemma BSubstBound.zero : BSubstBound (0 : PowerSeries ℚ) := by
  refine ⟨1, one_pos, 0, fun n => ?_⟩
  simp

lemma BSubstBound.one : BSubstBound (1 : PowerSeries ℚ) := by
  refine ⟨1, one_pos, 0, fun n => ?_⟩
  rw [PowerSeries.coeff_one]
  split_ifs with h <;> simp

lemma BSubstBound.add {f g : PowerSeries ℚ} (hf : BSubstBound f) (hg : BSubstBound g) :
    BSubstBound (f + g) := by
  obtain ⟨A, hA, k, hk⟩ := hf
  obtain ⟨B, hB, l, hl⟩ := hg
  refine ⟨A + B, add_pos hA hB, max k l, fun n => ?_⟩
  have hcoeff : ((PowerSeries.coeff n (f + g) : ℚ) : ℝ)
      = ((PowerSeries.coeff n f : ℚ) : ℝ) + ((PowerSeries.coeff n g : ℚ) : ℝ) := by
    rw [map_add, Rat.cast_add]
  rw [hcoeff]
  have hkn : |((PowerSeries.coeff n f : ℚ) : ℝ)| ≤ A * ((n : ℝ) + 1) ^ max k l :=
    le_trans (hk n) (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (one_le_natCast_add_one n) (le_max_left k l)) hA.le)
  have hln : |((PowerSeries.coeff n g : ℚ) : ℝ)| ≤ B * ((n : ℝ) + 1) ^ max k l :=
    le_trans (hl n) (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (one_le_natCast_add_one n) (le_max_right k l)) hB.le)
  calc |((PowerSeries.coeff n f : ℚ) : ℝ) + ((PowerSeries.coeff n g : ℚ) : ℝ)|
      ≤ _ + _ := abs_add_le _ _
    _ ≤ A * ((n : ℝ) + 1) ^ max k l + B * ((n : ℝ) + 1) ^ max k l := add_le_add hkn hln
    _ = (A + B) * ((n : ℝ) + 1) ^ max k l := by ring

lemma BSubstBound.neg {f : PowerSeries ℚ} (hf : BSubstBound f) : BSubstBound (-f) := by
  obtain ⟨A, hA, k, hk⟩ := hf
  refine ⟨A, hA, k, fun n => ?_⟩
  rw [map_neg, Rat.cast_neg, abs_neg]
  exact hk n

lemma BSubstBound.sub {f g : PowerSeries ℚ} (hf : BSubstBound f) (hg : BSubstBound g) :
    BSubstBound (f - g) := by
  rw [sub_eq_add_neg]
  exact BSubstBound.add hf (BSubstBound.neg hg)

/-- The constant series `C c` has polynomially bounded coefficients. -/
lemma BSubstBound.C (c : ℚ) : BSubstBound (PowerSeries.C c) := by
  have hmax : (0 : ℝ) < max |(c : ℝ)| 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨max |(c : ℝ)| 1, hmax, 0, fun n => ?_⟩
  rw [PowerSeries.coeff_C, pow_zero, mul_one]
  split_ifs with h
  · refine le_trans ?_ (le_max_left _ _)
    norm_num
  · rw [Rat.cast_zero, abs_zero]
    exact hmax.le

/-- Multiplication preserves polynomial coefficient growth. -/
lemma BSubstBound.mul {f g : PowerSeries ℚ} (hf : BSubstBound f) (hg : BSubstBound g) :
    BSubstBound (f * g) := by
  obtain ⟨A, hA, k, hk⟩ := hf
  obtain ⟨B, hB, l, hl⟩ := hg
  have hAB : (0 : ℝ) < A * B := mul_pos hA hB
  refine ⟨A * B, hAB, k + l + 1, fun n => ?_⟩
  have h1 : |((PowerSeries.coeff n (f * g) : ℚ) : ℝ)|
      ≤ ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
          A * (((p.1 : ℝ) + 1) ^ k) * (B * (((p.2 : ℝ) + 1) ^ l)) := by
    rw [PowerSeries.coeff_mul, Rat.cast_sum]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun p hp => ?_
    rw [Rat.cast_mul, abs_mul]
    exact mul_le_mul (hk p.1) (hl p.2) (abs_nonneg _)
      (mul_nonneg hA.le (pow_nonneg (natCast_add_one_nonneg p.1) k))
  have h2 : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
          A * (((p.1 : ℝ) + 1) ^ k) * (B * (((p.2 : ℝ) + 1) ^ l))
      ≤ (Finset.HasAntidiagonal.antidiagonal n).card
          • (A * B * ((n : ℝ) + 1) ^ (k + l)) := by
    refine Finset.sum_le_card_nsmul _ _ _ fun p hp => ?_
    have hpn : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    have hp1 : p.1 ≤ n := by omega
    have hp2 : p.2 ≤ n := by omega
    have h1n : (p.1 : ℝ) + 1 ≤ (n : ℝ) + 1 := by
      have h' : (p.1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hp1
      linarith
    have h2n : (p.2 : ℝ) + 1 ≤ (n : ℝ) + 1 := by
      have h' : (p.2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hp2
      linarith
    have e1 : ((p.1 : ℝ) + 1) ^ k ≤ ((n : ℝ) + 1) ^ k :=
      pow_le_pow_left₀ (natCast_add_one_nonneg p.1) h1n k
    have e2 : ((p.2 : ℝ) + 1) ^ l ≤ ((n : ℝ) + 1) ^ l :=
      pow_le_pow_left₀ (natCast_add_one_nonneg p.2) h2n l
    have e3 : A * ((p.1 : ℝ) + 1) ^ k ≤ A * ((n : ℝ) + 1) ^ k :=
      mul_le_mul_of_nonneg_left e1 hA.le
    have e5 : (0 : ℝ) ≤ A * ((n : ℝ) + 1) ^ k :=
      mul_nonneg hA.le (pow_nonneg (natCast_add_one_nonneg n) k)
    have e6 : (0 : ℝ) ≤ B * ((p.2 : ℝ) + 1) ^ l :=
      mul_nonneg hB.le (pow_nonneg (natCast_add_one_nonneg p.2) l)
    have e4 : B * ((p.2 : ℝ) + 1) ^ l ≤ B * ((n : ℝ) + 1) ^ l :=
      mul_le_mul_of_nonneg_left e2 hB.le
    calc A * (((p.1 : ℝ) + 1) ^ k) * (B * (((p.2 : ℝ) + 1) ^ l))
        ≤ A * ((n : ℝ) + 1) ^ k * (B * ((n : ℝ) + 1) ^ l) :=
          mul_le_mul e3 e4 e6 e5
      _ = A * B * ((n : ℝ) + 1) ^ (k + l) := by rw [pow_add]; ring
  refine le_trans h1 (le_trans h2 ?_)
  refine le_of_eq ?_
  rw [Finset.Nat.card_antidiagonal, nsmul_eq_mul]
  have hcast : (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [hcast, pow_succ]
  ring

lemma BSubstBound.const_mul {f : PowerSeries ℚ} (c : ℚ) (hf : BSubstBound f) :
    BSubstBound (PowerSeries.C c * f) :=
  BSubstBound.mul (BSubstBound.C c) hf

/-- Multiplication by `X` shifts coefficients down and preserves growth. -/
lemma BSubstBound.X_mul {f : PowerSeries ℚ} (hf : BSubstBound f) : BSubstBound (X * f) := by
  obtain ⟨A, hA, k, hk⟩ := hf
  refine ⟨A, hA, k, fun n => ?_⟩
  rw [show (X : PowerSeries ℚ) * f = X ^ 1 * f by rw [pow_one], PowerSeries.coeff_X_pow_mul']
  split_ifs with h
  · have hle : (((n - 1 : ℕ)) : ℝ) + 1 ≤ (n : ℝ) + 1 := by
      have hsub : (n - 1 : ℕ) ≤ n := Nat.sub_le n 1
      have h' : (((n - 1 : ℕ)) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hsub
      linarith
    calc |(((PowerSeries.coeff (n - 1) f : ℚ)) : ℝ)|
        ≤ A * ((((n - 1 : ℕ)) : ℝ) + 1) ^ k := hk (n - 1)
      _ ≤ A * ((n : ℝ) + 1) ^ k :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (natCast_add_one_nonneg (n - 1)) hle k) hA.le
  · rw [Rat.cast_zero, abs_zero]
    exact mul_nonneg hA.le (pow_nonneg (natCast_add_one_nonneg n) k)

/-- Powers preserve polynomial coefficient growth. -/
lemma BSubstBound.pow {f : PowerSeries ℚ} (hf : BSubstBound f) (m : ℕ) :
    BSubstBound (f ^ m) := by
  induction m with
  | zero => simpa using BSubstBound.one
  | succ m ih => rw [pow_succ]; exact BSubstBound.mul ih hf




/-! ## 2. Bounds for the elementary series -/

lemma BSubstBound.X_bound : BSubstBound (PowerSeries.X : PowerSeries ℚ) := by
  refine ⟨1, one_pos, 0, fun n => ?_⟩
  rw [PowerSeries.coeff_X, pow_zero, mul_one]
  split_ifs with h <;> simp

/-- Multiplication by a natural-constant series. -/
lemma BSubstBound.ofNat_mul (m : ℕ) {f : PowerSeries ℚ} (hf : BSubstBound f) :
    BSubstBound ((m : PowerSeries ℚ) * f) := by
  rw [show ((m : PowerSeries ℚ)) = PowerSeries.C (m : ℚ) from map_natCast PowerSeries.C m]
  exact BSubstBound.const_mul _ hf

/-- Multiplication by a rational constant. -/
lemma BSubstBound.smul {f : PowerSeries ℚ} (c : ℚ) (hf : BSubstBound f) :
    BSubstBound (c • f) := by
  rw [Algebra.smul_def]
  exact BSubstBound.const_mul c hf

/-- `X ^ m` has polynomially bounded coefficients. -/
lemma BSubstBound.X_pow (m : ℕ) : BSubstBound ((PowerSeries.X : PowerSeries ℚ) ^ m) := by
  induction m with
  | zero => simpa using BSubstBound.one
  | succ m ih => rw [pow_succ]; exact BSubstBound.mul ih BSubstBound.X_bound

/-- `2 - X` has polynomially bounded coefficients. -/
lemma BSubstBound.two_sub_X : BSubstBound ((2 : PowerSeries ℚ) - PowerSeries.X) := by
  have h : ((2 : PowerSeries ℚ) - PowerSeries.X) = (2 : PowerSeries ℚ) * 1 - PowerSeries.X := by
    ring
  rw [h]
  exact BSubstBound.sub (BSubstBound.ofNat_mul 2 BSubstBound.one) BSubstBound.X_bound

/-- `X - 2` has polynomially bounded coefficients. -/
lemma BSubstBound.X_sub_two : BSubstBound (PowerSeries.X - (2 : PowerSeries ℚ)) := by
  have h : (PowerSeries.X - (2 : PowerSeries ℚ)) = -((2 : PowerSeries ℚ) - PowerSeries.X) := by
    ring
  rw [h]
  exact BSubstBound.neg BSubstBound.two_sub_X

/-! ### The geometric series `(1 - X)⁻¹` and `(X - 1)⁻¹` -/

lemma coeff_inv_one_sub (n : ℕ) :
    PowerSeries.coeff n (((1 : PowerSeries ℚ) - PowerSeries.X)⁻¹) = 1 := by
  have hconst : PowerSeries.constantCoeff ((1 : PowerSeries ℚ) - PowerSeries.X) ≠ 0 := by
    rw [map_sub, PowerSeries.constantCoeff_one, PowerSeries.constantCoeff_X]
    norm_num
  have hw : ((1 : PowerSeries ℚ) - PowerSeries.X) * (((1 : PowerSeries ℚ) - PowerSeries.X)⁻¹) = 1 :=
    PowerSeries.mul_inv_cancel _ hconst
  have hrec : (((1 : PowerSeries ℚ) - PowerSeries.X)⁻¹)
      = 1 + PowerSeries.X * (((1 : PowerSeries ℚ) - PowerSeries.X)⁻¹) := by
    rw [sub_mul, one_mul] at hw
    linear_combination hw
  induction n with
  | zero =>
      have h := congrArg (fun f : PowerSeries ℚ => PowerSeries.coeff 0 f) hrec
      rw [map_add, PowerSeries.coeff_one, if_pos rfl, PowerSeries.coeff_zero_X_mul, add_zero] at h
      exact h
  | succ n ih =>
      have h := congrArg (fun f : PowerSeries ℚ => PowerSeries.coeff (n + 1) f) hrec
      rw [map_add, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_one,
        if_neg (Nat.succ_ne_zero n), zero_add, ih] at h
      exact h

lemma BSubstBound.inv_one_sub : BSubstBound (((1 : PowerSeries ℚ) - PowerSeries.X)⁻¹) := by
  refine ⟨1, one_pos, 0, fun n => ?_⟩
  rw [coeff_inv_one_sub n]
  norm_num

lemma coeff_inv_X_sub_one (n : ℕ) :
    PowerSeries.coeff n (((PowerSeries.X : PowerSeries ℚ) - 1)⁻¹) = -1 := by
  have hconst : PowerSeries.constantCoeff ((PowerSeries.X : PowerSeries ℚ) - 1) ≠ 0 := by
    rw [map_sub, PowerSeries.constantCoeff_X, PowerSeries.constantCoeff_one]
    norm_num
  have hw : ((PowerSeries.X : PowerSeries ℚ) - 1) * (((PowerSeries.X : PowerSeries ℚ) - 1)⁻¹) = 1 :=
    PowerSeries.mul_inv_cancel _ hconst
  have hrec : (((PowerSeries.X : PowerSeries ℚ) - 1)⁻¹)
      = PowerSeries.X * (((PowerSeries.X : PowerSeries ℚ) - 1)⁻¹) - 1 := by
    rw [sub_mul, one_mul] at hw
    linear_combination -hw
  induction n with
  | zero =>
      have h := congrArg (fun f : PowerSeries ℚ => PowerSeries.coeff 0 f) hrec
      rw [map_sub, PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_one, if_pos rfl,
        zero_sub] at h
      exact h
  | succ n ih =>
      have h := congrArg (fun f : PowerSeries ℚ => PowerSeries.coeff (n + 1) f) hrec
      rw [map_sub, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_one,
        if_neg (Nat.succ_ne_zero n), sub_zero, ih] at h
      exact h

lemma BSubstBound.inv_X_sub_one : BSubstBound ((PowerSeries.X - (1 : PowerSeries ℚ))⁻¹) := by
  refine ⟨1, one_pos, 0, fun n => ?_⟩
  rw [coeff_inv_X_sub_one n]
  norm_num

/-! ### The symplectic coordinate, the function `c`, `log(1-x)` and `Li₂` -/

lemma yps_eq_X_sq : Work.C7.yps = (PowerSeries.X : PowerSeries ℚ) ^ 2 *
    ((PowerSeries.X : PowerSeries ℚ) - 1)⁻¹ := by
  rw [Work.C7.yps, Submission.CDT.sympY, Submission.CDT.sympPhi]
  ring

lemma BSubstBound.yps : BSubstBound Work.C7.yps := by
  rw [yps_eq_X_sq]
  exact BSubstBound.mul (BSubstBound.X_pow 2) BSubstBound.inv_X_sub_one

lemma BSubstBound.cfun : BSubstBound Work.C7.cfun := by
  have h : Work.C7.cfun = (PowerSeries.X : PowerSeries ℚ) * (PowerSeries.X - 2) *
      ((PowerSeries.X : PowerSeries ℚ) - 1)⁻¹ := rfl
  rw [h]
  exact BSubstBound.mul (BSubstBound.mul BSubstBound.X_bound BSubstBound.X_sub_two)
    BSubstBound.inv_X_sub_one

lemma BSubstBound.Lps : BSubstBound Work.C7.Lps := by
  refine ⟨1, one_pos, 0, fun n => ?_⟩
  rw [Work.C7.coeff_Lps, pow_zero, mul_one]
  by_cases hn : n = 0
  · rw [if_pos hn]; simp
  · rw [if_neg hn]
    have hn1 : (1 : ℚ) ≤ (n : ℚ) := by
      have : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      exact_mod_cast this
    have h0 : (0 : ℚ) ≤ (n : ℚ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg n)
    have h1 : (n : ℚ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hn1
    have hq : |(-(n : ℚ)⁻¹ : ℚ)| ≤ 1 := by
      rw [abs_le]; exact ⟨by linarith, by linarith⟩
    calc |((( -(n : ℚ)⁻¹ : ℚ)) : ℝ)| = ((( |(-(n : ℚ)⁻¹ : ℚ)| : ℚ)) : ℝ) := (Rat.cast_abs _).symm
      _ ≤ ((1 : ℚ) : ℝ) := by exact_mod_cast hq
      _ = 1 := by norm_num

lemma BSubstBound.Li2ps : BSubstBound Work.C7.Li2ps := by
  refine ⟨1, one_pos, 0, fun n => ?_⟩
  rw [Work.C7.coeff_Li2ps, pow_zero, mul_one]
  by_cases hn : n = 0
  · rw [if_pos hn]; simp
  · rw [if_neg hn]
    have hn1 : (1 : ℚ) ≤ ((n : ℚ)) ^ 2 := by
      have h' : (1 : ℚ) ≤ (n : ℚ) := by
        have : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
        exact_mod_cast this
      have hc : (0 : ℚ) ≤ (n : ℚ) := Nat.cast_nonneg n
      nlinarith
    have h0 : (0 : ℚ) ≤ (((n : ℚ)) ^ 2)⁻¹ := inv_nonneg.mpr (by positivity)
    have h1 : (((n : ℚ)) ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hn1
    have hq : |((((n : ℚ)) ^ 2)⁻¹ : ℚ)| ≤ 1 := by
      rw [abs_le]; exact ⟨by linarith, by linarith⟩
    calc |(((((n : ℚ)) ^ 2)⁻¹ : ℚ) : ℝ)| = ((( |((((n : ℚ)) ^ 2)⁻¹ : ℚ)| : ℚ)) : ℝ) :=
          (Rat.cast_abs _).symm
      _ ≤ ((1 : ℚ) : ℝ) := by exact_mod_cast hq
      _ = 1 := by norm_num

/-! ## 3. Coefficient extraction: derivatives sitting under `X` or a unit -/

/-- If `X * d = W` and `W` grows at most polynomially, so does `d`. -/
lemma BSubstBound.of_X_mul {d W : PowerSeries ℚ} (h : PowerSeries.X * d = W)
    (hW : BSubstBound W) : BSubstBound d := by
  obtain ⟨C, hC, k, hk⟩ := hW
  refine ⟨C * 2 ^ k, by positivity, k, fun n => ?_⟩
  have hcoeff : (((PowerSeries.coeff n d : ℚ)) : ℝ)
      = (((PowerSeries.coeff (n + 1) W : ℚ)) : ℝ) := by
    have h1 := congrArg (fun z : PowerSeries ℚ => PowerSeries.coeff (n + 1) z) h
    rw [PowerSeries.coeff_succ_X_mul] at h1
    exact congrArg (fun q : ℚ => (q : ℝ)) h1
  rw [hcoeff]
  calc |(((PowerSeries.coeff (n + 1) W : ℚ)) : ℝ)|
      ≤ C * ((((n + 1 : ℕ)) : ℝ) + 1) ^ k := hk (n + 1)
    _ = C * ((n : ℝ) + 2) ^ k := by push_cast; ring
    _ ≤ C * 2 ^ k * ((n : ℝ) + 1) ^ k := by
        have h1 : (n : ℝ) + 2 ≤ 2 * ((n : ℝ) + 1) := by
          have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          linarith
        have h2 : ((n : ℝ) + 2) ^ k ≤ (2 * ((n : ℝ) + 1)) ^ k :=
          pow_le_pow_left₀ (by positivity) h1 k
        calc C * ((n : ℝ) + 2) ^ k ≤ C * (2 * ((n : ℝ) + 1)) ^ k :=
              mul_le_mul_of_nonneg_left h2 hC.le
          _ = C * 2 ^ k * ((n : ℝ) + 1) ^ k := by rw [mul_pow]; ring

/-- If `u * d = W` with `u` invertible in `ℚ⟦x⟧` and `u⁻¹` polynomially bounded, then so is `d`. -/
lemma BSubstBound.of_mul_unit {u d W : PowerSeries ℚ} (hu : PowerSeries.constantCoeff u ≠ 0)
    (h : u * d = W) (huinv : BSubstBound u⁻¹) (hW : BSubstBound W) : BSubstBound d := by
  have hd : d = u⁻¹ * W := by
    rw [← h, ← mul_assoc, PowerSeries.inv_mul_cancel u hu, one_mul]
  rw [hd]
  exact BSubstBound.mul huinv hW

/-- A series with zero constant term whose derivative grows polynomially does too. -/
lemma BSubstBound.of_deriv {f : PowerSeries ℚ} (h0 : PowerSeries.coeff 0 f = 0)
    (hf : BSubstBound (PowerSeries.derivative (R := ℚ) f)) : BSubstBound f := by
  obtain ⟨C, hC, k, hk⟩ := hf
  refine ⟨C, hC, k, fun n => ?_⟩
  rcases n with _ | m
  · rw [h0, Rat.cast_zero, abs_zero]
    positivity
  · have hrel : (((PowerSeries.coeff (m + 1) f : ℚ)) : ℝ) * ((m : ℝ) + 1)
        = (((PowerSeries.coeff m (PowerSeries.derivative (R := ℚ) f) : ℚ)) : ℝ) := by
      rw [PowerSeries.coeff_derivative]
      push_cast
      ring
    have hpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have habs : |(((PowerSeries.coeff (m + 1) f : ℚ)) : ℝ)| * ((m : ℝ) + 1)
        = |(((PowerSeries.coeff m (PowerSeries.derivative (R := ℚ) f) : ℚ)) : ℝ)| := by
      rw [← hrel, abs_mul, abs_of_nonneg hpos.le]
    have hkey : |(((PowerSeries.coeff (m + 1) f : ℚ)) : ℝ)| ≤ C * ((m : ℝ) + 1) ^ k := by
      have h2 : |(((PowerSeries.coeff (m + 1) f : ℚ)) : ℝ)| * ((m : ℝ) + 1)
          ≤ C * ((m : ℝ) + 1) ^ k := by
        rw [habs]; exact hk m
      calc |(((PowerSeries.coeff (m + 1) f : ℚ)) : ℝ)|
          = (|(((PowerSeries.coeff (m + 1) f : ℚ)) : ℝ)| * ((m : ℝ) + 1)) / ((m : ℝ) + 1) := by
            rw [mul_div_cancel_right₀ _ (ne_of_gt hpos)]
        _ ≤ (C * ((m : ℝ) + 1) ^ k) / ((m : ℝ) + 1) := div_le_div_of_nonneg_right h2 hpos.le
        _ ≤ C * ((m : ℝ) + 1) ^ k := by
            rw [div_le_iff₀ hpos]
            have h1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by
              have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
              linarith
            exact le_mul_of_one_le_right (mul_nonneg hC.le (pow_nonneg hpos.le k)) h1
    calc |(((PowerSeries.coeff (m + 1) f : ℚ)) : ℝ)| ≤ C * ((m : ℝ) + 1) ^ k := hkey
      _ ≤ C * ((((m + 1 : ℕ)) : ℝ) + 1) ^ k := by
          have hle : (m : ℝ) + 1 ≤ (((m + 1 : ℕ)) : ℝ) + 1 := by push_cast; linarith
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hle k) hC.le

lemma X_sub_one_ne_zero' : ((PowerSeries.X : PowerSeries ℚ) - 1) ≠ 0 := by
  intro h
  have hc := congrArg (fun f : PowerSeries ℚ => PowerSeries.coeff 0 f) h
  rw [map_sub, PowerSeries.coeff_X, PowerSeries.coeff_one] at hc
  norm_num at hc

lemma inv_X_sub_one_mul' :
    (((PowerSeries.X : PowerSeries ℚ) - 1)⁻¹) * ((PowerSeries.X : PowerSeries ℚ) - 1) = 1 :=
  PowerSeries.inv_mul_cancel _ (by
    rw [map_sub, PowerSeries.constantCoeff_X, PowerSeries.constantCoeff_one]; norm_num)

/-- `C (1/2) * 2 = 1`. -/
lemma C_half_mul_two : (PowerSeries.C (1/2 : ℚ)) * (2 : PowerSeries ℚ) = 1 := by
  rw [show (2 : PowerSeries ℚ) = PowerSeries.C (2 : ℚ) from (map_ofNat PowerSeries.C 2).symm,
    ← map_mul]
  norm_num

lemma coeff_zero_yps : PowerSeries.coeff 0 Work.C7.yps = 0 := by
  rw [yps_eq_X_sq, PowerSeries.coeff_X_pow_mul']
  simp

lemma coeff_zero_g (j : Fin 7) (hj : PowerSeries.coeff 0 (Submission.CDTPlan.pureB j) = 0) :
    PowerSeries.coeff 0 (Work.C7.g j) = 0 := by
  show PowerSeries.coeff 0 ((Submission.CDTPlan.pureB j).subst Work.C7.yps) = 0
  have hcc : PowerSeries.constantCoeff (Submission.CDTPlan.pureB j) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact hj
  have hcy : PowerSeries.constantCoeff Work.C7.yps = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact coeff_zero_yps
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact PowerSeries.constantCoeff_subst_eq_zero hcy _ hcc

/-! ## 4. The bound for each of the seven pure functions -/

lemma BSubstBound.sympPhi : BSubstBound Submission.CDT.sympPhi := by
  have h : Submission.CDT.sympPhi = (PowerSeries.X : PowerSeries ℚ) *
      ((PowerSeries.X : PowerSeries ℚ) - 1)⁻¹ := rfl
  rw [h]
  exact BSubstBound.mul BSubstBound.X_bound BSubstBound.inv_X_sub_one

lemma bound_g0 : BSubstBound (Work.C7.g 0) := by
  have h : Work.C7.g 0 = 1 := by
    show (Submission.CDTPlan.pureB 0).subst Work.C7.yps = 1
    have hp : Submission.CDTPlan.pureB 0 = (1 : PowerSeries ℚ) := rfl
    rw [hp, ← PowerSeries.coe_substAlgHom Submission.CDT.sympY_hasSubst]
    exact map_one _
  rw [h]
  exact BSubstBound.one

lemma bound_g1 (h1 : Work.C7.g 1 = 2 * Work.C7.yps - Work.C7.cfun * Work.C7.Lps) :
    BSubstBound (Work.C7.g 1) := by
  rw [h1]
  exact BSubstBound.sub (BSubstBound.ofNat_mul 2 BSubstBound.yps)
    (BSubstBound.mul BSubstBound.cfun BSubstBound.Lps)

lemma bound_g2 (h2 : Work.C7.g 2 = -(PowerSeries.C (1/2 : ℚ)) * Work.C7.Lps ^ 2) :
    BSubstBound (Work.C7.g 2) := by
  rw [h2, neg_mul]
  exact BSubstBound.neg (BSubstBound.const_mul (1/2) (BSubstBound.pow BSubstBound.Lps 2))

lemma bound_g3 (h3 : Work.C7.g 3 = (PowerSeries.X - Submission.CDT.sympPhi) *
    (2 * Work.C7.Li2ps + (PowerSeries.C (1/2 : ℚ)) * Work.C7.Lps ^ 2)) :
    BSubstBound (Work.C7.g 3) := by
  rw [h3]
  refine BSubstBound.mul (BSubstBound.sub BSubstBound.X_bound BSubstBound.sympPhi) ?_
  exact BSubstBound.add (BSubstBound.ofNat_mul 2 BSubstBound.Li2ps)
    (BSubstBound.const_mul (1/2) (BSubstBound.pow BSubstBound.Lps 2))

lemma bound_g4 (h4 : Work.C7.g 4 = (PowerSeries.X * (PowerSeries.X - 1)⁻¹) * Work.C7.Jps)
    (hJ : BSubstBound Work.C7.Jps) : BSubstBound (Work.C7.g 4) := by
  rw [h4]
  exact BSubstBound.mul (BSubstBound.mul BSubstBound.X_bound BSubstBound.inv_X_sub_one) hJ

lemma bound_g5 (h5 : 2 * PowerSeries.X * (PowerSeries.X - 1) *
      PowerSeries.derivative (R := ℚ) (Work.C7.g 5) = -(PowerSeries.X - 2) * Work.C7.Lps ^ 2) :
    BSubstBound (Work.C7.g 5) := by
  set d : PowerSeries ℚ := PowerSeries.derivative (R := ℚ) (Work.C7.g 5) with hd
  set R : PowerSeries ℚ := -(PowerSeries.X - 2) * Work.C7.Lps ^ 2 with hR
  have hR' : BSubstBound R := by
    rw [hR, neg_mul]
    exact BSubstBound.neg (BSubstBound.mul BSubstBound.X_sub_two
      (BSubstBound.pow BSubstBound.Lps 2))
  have h2 : (2 : PowerSeries ℚ) * (PowerSeries.X * ((PowerSeries.X - 1) * d)) = R := by
    rw [hR, hd] at h5 ⊢
    rw [← h5]; ring
  have h3 : PowerSeries.X * ((PowerSeries.X - 1) * d) = (PowerSeries.C (1/2 : ℚ)) * R := by
    rw [← h2]
    conv_rhs => rw [← mul_assoc, C_half_mul_two, one_mul]
  have hstep : BSubstBound ((PowerSeries.X - 1) * d) :=
    BSubstBound.of_X_mul h3 (BSubstBound.const_mul (1/2) hR')
  have hd' : BSubstBound d := by
    have := BSubstBound.mul BSubstBound.inv_X_sub_one hstep
    rwa [← mul_assoc, inv_X_sub_one_mul', one_mul] at this
  exact BSubstBound.of_deriv (coeff_zero_g 5 (by
    rw [show Submission.CDTPlan.pureB 5 = Submission.CDTPlan.B6 from rfl]
    simp [Submission.CDTPlan.B6])) hd'

lemma bound_g6 (h6 : (PowerSeries.X - 1) ^ 2 * PowerSeries.derivative (R := ℚ) (Work.C7.g 6) =
      (PowerSeries.X - 2) ^ 2 * (2 * Work.C7.Li2ps +
        (PowerSeries.C (1/2 : ℚ)) * Work.C7.Lps ^ 2)) :
    BSubstBound (Work.C7.g 6) := by
  set d : PowerSeries ℚ := PowerSeries.derivative (R := ℚ) (Work.C7.g 6) with hd
  set R : PowerSeries ℚ := (PowerSeries.X - 2) ^ 2 * (2 * Work.C7.Li2ps +
    (PowerSeries.C (1/2 : ℚ)) * Work.C7.Lps ^ 2) with hR
  have hR' : BSubstBound R := by
    rw [hR]
    refine BSubstBound.mul (BSubstBound.pow BSubstBound.X_sub_two 2) ?_
    exact BSubstBound.add (BSubstBound.ofNat_mul 2 BSubstBound.Li2ps)
      (BSubstBound.const_mul (1/2) (BSubstBound.pow BSubstBound.Lps 2))
  have h2 : (PowerSeries.X - 1) * ((PowerSeries.X - 1) * d) = R := by
    rw [hR, hd] at h6 ⊢
    rw [show (PowerSeries.X - 1) * ((PowerSeries.X - 1) * d)
        = (PowerSeries.X - 1) ^ 2 * d by ring]
    exact h6
  have h3 : (PowerSeries.X - 1) * d = ((PowerSeries.X : PowerSeries ℚ) - 1)⁻¹ * R := by
    rw [← h2, ← mul_assoc, inv_X_sub_one_mul', one_mul]
  have hstep : BSubstBound ((PowerSeries.X - 1) * d) :=
    BSubstBound.of_mul_unit (u := (PowerSeries.X : PowerSeries ℚ) - 1)
      (by rw [map_sub, PowerSeries.constantCoeff_X, PowerSeries.constantCoeff_one]; norm_num)
      h2 BSubstBound.inv_X_sub_one hR'
  have hd' : BSubstBound d := by
    have := BSubstBound.mul BSubstBound.inv_X_sub_one hstep
    rwa [← mul_assoc, inv_X_sub_one_mul', one_mul] at this
  exact BSubstBound.of_deriv (coeff_zero_g 6 (by
    rw [show Submission.CDTPlan.pureB 6 = Submission.CDTPlan.B7 from rfl]
    simp [Submission.CDTPlan.B7])) hd'


/-! ## 5. The fifth pullback `B₅ ∘ y = (x/(x−1))·J` -/

lemma B5_eq_X_K5 : Submission.CDTPlan.B5 = (PowerSeries.X : PowerSeries ℚ) * Work.C7.K5 := by
  apply PowerSeries.ext
  intro n
  rw [show (PowerSeries.X : PowerSeries ℚ) * Work.C7.K5 = PowerSeries.X ^ 1 * Work.C7.K5 by
      rw [pow_one],
    PowerSeries.coeff_X_pow_mul']
  rcases n with _ | n
  · rw [if_neg (by omega : ¬ (1 : ℕ) ≤ 0)]
    simp [Work.C7.K5, Submission.CDTPlan.B5]
  · rw [if_pos (by omega : (1 : ℕ) ≤ n + 1), show (n + 1 - 1) = n by omega,
      Work.C7.K5, PowerSeries.coeff_mk]

lemma g4_form : Work.C7.g 4 = (PowerSeries.X * (PowerSeries.X - 1)⁻¹) * Work.C7.Jps := by
  have hL : Work.C7.g 4 = Work.C7.yps * (Work.C7.K5.subst Work.C7.yps) := by
    show (Submission.CDTPlan.pureB 4).subst Work.C7.yps = _
    rw [show Submission.CDTPlan.pureB 4 = Submission.CDTPlan.B5 from rfl, B5_eq_X_K5,
      PowerSeries.subst_mul (a := Submission.CDT.sympY) Submission.CDT.sympY_hasSubst,
      PowerSeries.subst_X (a := Submission.CDT.sympY) Submission.CDT.sympY_hasSubst]
  rw [hL, Work.C7.Jps,
    show (PowerSeries.X * (PowerSeries.X - 1)⁻¹)
        * (PowerSeries.X * Work.C7.K5.subst Work.C7.yps)
        = Work.C7.yps * (Work.C7.K5.subst Work.C7.yps) by rw [yps_eq_X_sq]; ring]

/-! ## 6. The target theorem -/


lemma BSubstBound.of_bound {f : PowerSeries ℚ}
    (h : ∃ C : ℝ, ∃ k : ℕ, ∀ n : ℕ,
      |((PowerSeries.coeff n f : ℚ) : ℝ)| ≤ C * ((n : ℝ) + 1) ^ k) : BSubstBound f := by
  obtain ⟨C, k, hk⟩ := h
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), k, fun n => ?_⟩
  refine le_trans (hk n) ?_
  exact mul_le_mul_of_nonneg_right (le_max_left C 1)
    (pow_nonneg (by positivity) k)

/-- **Polynomial growth of the coefficients of the pullbacks `B_i(x²/(x−1))`.** -/
theorem Bsubst_poly_growth : ∀ i : Fin 7, ∃ C : ℝ, ∃ k : ℕ, ∀ n : ℕ,
    |((PowerSeries.coeff n ((Submission.CDTPlan.pureB i).subst Submission.CDT.sympY) : ℚ) : ℝ)|
      ≤ C * ((n : ℝ) + 1) ^ k := by
  have h1 := Work.C7.g_form.1
  have h2 := Work.C7.g_form.2.1
  have h3 := Work.C7.g_form.2.2
  have h67 := Work.C7.g67_deriv h2 h3 B6_deriv B7_deriv
  have hJode := Work.C7.J_ode h1 g4_form B5_pullback
  have hJs : BSubstBound Work.C7.Jps := BSubstBound.of_bound (Js_bound hJode)
  intro i
  fin_cases i
  · exact BSubstBound.weaken bound_g0
  · exact BSubstBound.weaken (bound_g1 h1)
  · exact BSubstBound.weaken (bound_g2 h2)
  · exact BSubstBound.weaken (bound_g3 h3)
  · exact BSubstBound.weaken (bound_g4 g4_form hJs)
  · exact BSubstBound.weaken (bound_g5 h67.1)
  · exact BSubstBound.weaken (bound_g6 h67.2)

end
end Work.C17
