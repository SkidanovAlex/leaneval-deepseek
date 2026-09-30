import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.norm_cpow_neg_I_mul

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Dirichlet Parseval on a short interval (`dirichlet_parseval_shortint`)

For `a : ℕ → ℂ` with `‖a n‖ ≤ 1/n`, the Dirichlet polynomial

`D t = ∑_{n ∈ [Y,3Y]} a n · n^{-it}`

is bounded uniformly in `t`: each summand has norm at most `1/n` (the factor `n^{-it}` has
modulus one), so `‖D t‖ ≤ ∑_{n ∈ [Y,3Y]} 1/n`, and the latter is `O(1)` -- not `O(log Y)` --
because the coefficients already decay like `1/n`. Indeed `∑_{n ∈ [Y,3Y]} 1/n ≤ 4` for `Y ≥ 1`
(the index set has `≤ 2Y+1` elements and each term is `≤ 1/Y`).

Consequently `∫_{-2T}^{2T} ‖D t‖² ≤ 16·(4T) = 64 T`, which the right-hand side of
`dirichlet_parseval_shortint` provides through its `C·T` term (the sum over `k` of squares is
nonnegative and can simply be discarded).

Auxiliary facts established here:

* `shortintDirPoly_inv_sum_le` : `∑_{n ∈ [Y,3Y]} 1/n ≤ 4` for `Y ≥ 1`;
* `shortintDirPoly_norm_le_sum` : `‖D t‖ ≤ ∑_{n ∈ [Y,3Y]} 1/n`;
* `shortintDirPoly_norm_le` : the uniform sup bound `‖D t‖ ≤ 4`;
* `shortintDirPoly_integral_bound` : `∫_{-2T}^{2T} ‖D t‖² ≤ 64 T` for `T ≥ 1`.
-/

namespace Work.BMF

open MeasureTheory Real Complex Finset

/-- The Dirichlet polynomial of the short-interval Parseval estimate has coefficients `a n`
with `‖a n‖ ≤ 1/n` on `[Y, 3Y]`; the trivial sup bound therefore only costs the harmonic-type
sum `∑_{n ∈ [Y,3Y]} 1/n`, which is bounded independently of `Y`. -/
theorem shortintDirPoly_inv_sum_le (Y : ℝ) (hY : 1 ≤ Y) :
    ∑ n ∈ natIcc Y (3 * Y), (1 : ℝ) / (n : ℝ) ≤ 4 := by
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hcard : (((natIcc Y (3 * Y)).card : ℕ) : ℝ) ≤ 2 * Y + 1 := by
    rw [natIcc, Nat.card_Icc]
    have hb : ((⌊3 * Y⌋₊ : ℕ) : ℝ) ≤ 3 * Y := Nat.floor_le (by linarith)
    have ha : Y ≤ ((⌈Y⌉₊ : ℕ) : ℝ) := Nat.le_ceil Y
    by_cases h : ⌈Y⌉₊ ≤ ⌊3 * Y⌋₊ + 1
    · rw [Nat.cast_sub h, Nat.cast_add, Nat.cast_one]
      linarith
    · have hlt : ⌊3 * Y⌋₊ + 1 < ⌈Y⌉₊ := Nat.lt_of_not_le h
      have hzero : ⌊3 * Y⌋₊ + 1 - ⌈Y⌉₊ = 0 := by omega
      rw [hzero, Nat.cast_zero]
      linarith
  have hterm : ∀ n ∈ natIcc Y (3 * Y), (1 : ℝ) / (n : ℝ) ≤ 1 / Y := by
    intro n hn
    have hmem : (⌈Y⌉₊ : ℕ) ≤ n := (Finset.mem_Icc.mp (by simpa only [natIcc] using hn)).1
    have hle : Y ≤ (n : ℝ) := le_trans (Nat.le_ceil Y) (by exact_mod_cast hmem)
    exact one_div_le_one_div_of_le hYpos hle
  calc ∑ n ∈ natIcc Y (3 * Y), (1 : ℝ) / (n : ℝ)
      ≤ (natIcc Y (3 * Y)).card • (1 / Y) :=
        Finset.sum_le_card_nsmul (s := natIcc Y (3 * Y))
          (f := fun n => (1 : ℝ) / (n : ℝ)) (1 / Y) hterm
    _ = ((natIcc Y (3 * Y)).card : ℝ) * (1 / Y) := by rw [nsmul_eq_mul]
    _ ≤ (2 * Y + 1) * (1 / Y) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ ≤ 4 := by
        rw [mul_one_div, div_le_iff₀ hYpos]
        linarith

/-- Uniform bound for the Dirichlet polynomial `D t = ∑_{n ∈ [Y,3Y]} a n · n^{-it}`:
`‖D t‖ ≤ ∑_{n ∈ [Y,3Y]} 1/n` whenever `‖a n‖ ≤ 1/n` and `Y ≥ 1`. -/
theorem shortintDirPoly_norm_le_sum (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1 / n)
    (Y : ℝ) (hY : 1 ≤ Y) :
    ∀ t : ℝ, ‖∑ n ∈ natIcc Y (3 * Y), a n * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖
      ≤ ∑ n ∈ natIcc Y (3 * Y), (1 : ℝ) / (n : ℝ) := by
  have hn1 : ∀ n ∈ natIcc Y (3 * Y), 1 ≤ n := by
    intro n hn
    have hmem : (⌈Y⌉₊ : ℕ) ≤ n := (Finset.mem_Icc.mp (by simpa only [natIcc] using hn)).1
    have hle : (1 : ℝ) ≤ (n : ℝ) :=
      le_trans (by linarith : (1 : ℝ) ≤ Y) (le_trans (Nat.le_ceil Y) (by exact_mod_cast hmem))
    exact_mod_cast hle
  intro t
  calc ‖∑ n ∈ natIcc Y (3 * Y), a n * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖
      ≤ ∑ n ∈ natIcc Y (3 * Y), ‖a n * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ n ∈ natIcc Y (3 * Y), (1 : ℝ) / (n : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        have h1 : ‖(n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ = 1 := norm_cpow_neg_I_mul t (hn1 n hn)
        rw [norm_mul, h1, mul_one]
        exact ha n

/-- Uniform sup bound `‖D t‖ ≤ 4` for the Dirichlet polynomial
`D t = ∑_{n ∈ [Y,3Y]} a n · n^{-it}`, valid when `Y ≥ 1` and `‖a n‖ ≤ 1/n`. -/
theorem shortintDirPoly_norm_le (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1 / n)
    (Y : ℝ) (hY : 1 ≤ Y) :
    ∀ t : ℝ, ‖∑ n ∈ natIcc Y (3 * Y), a n * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ≤ 4 :=
  fun t => le_trans (shortintDirPoly_norm_le_sum a ha Y hY t) (shortintDirPoly_inv_sum_le Y hY)

/-- `L²` bound over the short interval `[-2T, 2T]` for the Dirichlet polynomial of
`dirichlet_parseval_shortint`: `∫_{-2T}^{2T} ‖∑_{n ∈ [Y,3Y]} a n n^{-it}‖² ≤ 64 T`. -/
theorem shortintDirPoly_integral_bound (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1 / n)
    (Y T : ℝ) (hY : 1 ≤ Y) (hT : 1 ≤ T) :
    (∫ t in -(2 * T)..(2 * T),
        ‖∑ n ∈ natIcc Y (3 * Y), a n * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ^ 2) ≤ 64 * T := by
  have hDle : ∀ t : ℝ,
      ‖∑ n ∈ natIcc Y (3 * Y), a n * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ≤ 4 :=
    shortintDirPoly_norm_le a ha Y hY
  have hab : -(2 * T) ≤ 2 * T := by linarith
  have hpt : ∀ x ∈ Set.Icc (-(2 * T)) (2 * T),
      ‖∑ n ∈ natIcc Y (3 * Y), a n * (n : ℂ) ^ (-(Complex.I * (x : ℂ)))‖ ^ 2 ≤ (16 : ℝ) := by
    intro x _
    have h1 := hDle x
    have h2 : ‖∑ n ∈ natIcc Y (3 * Y),
        a n * (n : ℂ) ^ (-(Complex.I * (x : ℂ)))‖ ^ 2 ≤ (4 : ℝ) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    rwa [show (4 : ℝ) ^ 2 = (16 : ℝ) by norm_num] at h2
  have hb : ‖∫ x in -(2 * T)..(2 * T),
      ‖∑ n ∈ natIcc Y (3 * Y), a n * (n : ℂ) ^ (-(Complex.I * (x : ℂ)))‖ ^ 2‖
      ≤ (16 : ℝ) * |2 * T - (-(2 * T))| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have hxI : x ∈ Set.Icc (-(2 * T)) (2 * T) := by
      have h := hx
      rw [Set.uIoc_of_le hab] at h
      exact Set.Ioc_subset_Icc_self h
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hpt x hxI
  have hnn : 0 ≤ ∫ x in -(2 * T)..(2 * T),
      ‖∑ n ∈ natIcc Y (3 * Y), a n * (n : ℂ) ^ (-(Complex.I * (x : ℂ)))‖ ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall hab (fun x => by positivity)
  rw [Real.norm_eq_abs, abs_of_nonneg hnn] at hb
  have h4 : |2 * T - (-(2 * T))| = 4 * T := by
    rw [abs_of_nonneg (by linarith)]
    ring
  rw [h4] at hb
  linarith

theorem dirichlet_parseval_shortint :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → ℂ), (∀ n, ‖a n‖ ≤ 1 / n) →
      ∀ (Y T : ℝ), 4 ≤ Y → 1 ≤ T → T ≤ Y →
        (∫ t in -(2 * T)..(2 * T),
            ‖∑ n ∈ Work.BMF.natIcc Y (3 * Y), a n * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ^ 2)
          ≤ C * T ^ 2 * (∑ k ∈ Finset.range ⌈9 * T⌉₊,
                ‖∑ n ∈ Work.BMF.natIcc (Y + (k : ℝ) * (Y / (4 * T)))
                    (Y + ((k : ℝ) + 1) * (Y / (4 * T))), a n‖ ^ 2)
            + C * T := by
  refine ⟨64, by norm_num, ?_⟩
  intro a ha Y T hY hT hTY
  have hY1 : 1 ≤ Y := by linarith
  have hS : 0 ≤ ∑ k ∈ Finset.range ⌈9 * T⌉₊,
      ‖∑ n ∈ natIcc (Y + (k : ℝ) * (Y / (4 * T)))
          (Y + ((k : ℝ) + 1) * (Y / (4 * T))), a n‖ ^ 2 :=
    Finset.sum_nonneg (fun k _ => by positivity)
  have hI : (∫ t in -(2 * T)..(2 * T),
      ‖∑ n ∈ natIcc Y (3 * Y), a n * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ^ 2) ≤ 64 * T :=
    shortintDirPoly_integral_bound a ha Y T hY1 hT
  have hbig : 0 ≤ 64 * T ^ 2 * (∑ k ∈ Finset.range ⌈9 * T⌉₊,
      ‖∑ n ∈ natIcc (Y + (k : ℝ) * (Y / (4 * T)))
          (Y + ((k : ℝ) + 1) * (Y / (4 * T))), a n‖ ^ 2) :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg T)) hS
  linarith

end Work.BMF
