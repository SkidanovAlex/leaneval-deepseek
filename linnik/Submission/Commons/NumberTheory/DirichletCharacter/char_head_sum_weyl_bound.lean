import Mathlib
import Submission.Commons.Analysis.ExponentialSums.log_phase_shifted_head_sum_weyl
import Submission.Commons.Analysis.ExpLog.logPhase_sqrt_mul
import Submission.Commons.NumberTheory.DirichletCharacter.residue_block_sum_decomp

open Complex
open scoped Real BigOperators

namespace Commons.NumberTheory.DirichletCharacter

noncomputable section

set_option maxHeartbeats 4000000

/-! ## The weighted log-phase summand and its algebra -/

/-- The weighted log-phase summand `x ↦ e^{2πi((−t/2π)·log x)}/√x = x^{−1/2−it}`. -/
def wsum (t : ℝ) (x : ℝ) : ℂ :=
  Complex.exp ((((2 * Real.pi * (-(t / (2 * Real.pi)) * Real.log x)) : ℝ) : ℂ) * Complex.I)
    / ((Real.sqrt x : ℝ) : ℂ)

/-- Multiplicativity of `wsum`. -/
lemma wsum_mul (t x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    wsum t (x * y) = wsum t x * wsum t y :=
  Commons.Analysis.ExpLog.logPhase_sqrt_mul t x y hx hy

/-- `‖wsum t x‖ = 1/√x`. -/
lemma norm_wsum {t x : ℝ} (hx : 0 < x) : ‖wsum t x‖ = (Real.sqrt x)⁻¹ := by
  have hsq : ‖((Real.sqrt x : ℝ) : ℂ)‖ = Real.sqrt x := by
    simp [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg x)]
  unfold wsum
  rw [norm_div, Complex.norm_exp_ofReal_mul_I, hsq, one_div]

/-- The summand appearing in the target statement is `χ n * wsum t n`. -/
lemma target_summand {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (n : ℕ) :
    (χ n) * Complex.exp ((((2 * Real.pi * (-(t / (2 * Real.pi)) * Real.log (n : ℝ))) : ℝ) : ℂ) * Complex.I)
      / Real.sqrt (n : ℝ) = χ n * wsum t n := by
  rw [wsum, div_eq_mul_inv, div_eq_mul_inv]
  ring

/-- `wsum t (m + c)` rewritten in the shape of the shifted-log-phase summand used by
`log_phase_shifted_head_sum_weyl` (with shift `c`). -/
lemma wsum_shift (t c : ℝ) (m : ℕ) :
    wsum t ((m : ℝ) + c) =
      Complex.exp ((((-(t * Real.log (c + (m : ℝ)))) : ℝ) : ℂ) * Complex.I)
        / ((Real.sqrt (c + (m : ℝ)) : ℝ) : ℂ) := by
  have hcm : (m : ℝ) + c = c + (m : ℝ) := add_comm _ _
  have hphase :
      2 * Real.pi * (-(t / (2 * Real.pi)) * Real.log (c + (m : ℝ)))
        = -(t * Real.log (c + (m : ℝ))) := by
    field_simp
  unfold wsum
  rw [hcm, hphase]

/-- A Dirichlet character is periodic with period its level. -/
lemma char_period {q : ℕ} (χ : DirichletCharacter ℂ q) (a m : ℕ) : χ ((a + m*q : ℕ) : ZMod q) = χ a := by
  apply congrArg χ
  simp

/-- The block `∑_{m} wsum t (m + a/q)` over the arithmetic progression with shift `a/q`. -/
def blk (q X₀ : ℕ) (t : ℝ) (a : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc 0 ((X₀ - a)/q), wsum t ((m:ℝ) + (a:ℝ)/(q:ℝ))

/-- Termwise factorization of the character-twisted block summand. -/
lemma block_term {q : ℕ} (hq : 1 ≤ q) (χ : DirichletCharacter ℂ q) (t : ℝ)
    {a m : ℕ} (ha : 1 ≤ a) :
    χ ((a + m*q : ℕ) : ZMod q) * wsum t ((a + m*q : ℕ) : ℝ) =
      χ a * wsum t (q:ℝ) * wsum t ((m:ℝ) + (a:ℝ)/(q:ℝ)) := by
  have hq0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hshift : (0:ℝ) < (m:ℝ) + (a:ℝ)/(q:ℝ) := by positivity
  have hchar : χ ((a + m*q : ℕ) : ZMod q) = χ a := char_period χ a m
  have hgt : ((a + m*q : ℕ) : ℝ) = (q:ℝ) * ((m:ℝ) + (a:ℝ)/(q:ℝ)) := by
    push_cast
    field_simp
    ring
  rw [hchar, hgt, wsum_mul t (q:ℝ) ((m:ℝ)+(a:ℝ)/(q:ℝ)) hq0 hshift]
  ring

/-- The character-twisted block sum factors as `χ a · wsum t q · blk`. -/
lemma blk_eq_factor {q : ℕ} (hq : 1 ≤ q) (χ : DirichletCharacter ℂ q) (t : ℝ)
    {X₀ a : ℕ} (ha : 1 ≤ a) :
    (∑ m ∈ Finset.Icc 0 ((X₀ - a)/q), χ ((a + m*q : ℕ) : ZMod q) * wsum t ((a + m*q : ℕ) : ℝ))
      = χ a * wsum t (q:ℝ) * blk q X₀ t a := by
  unfold blk
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  exact block_term hq χ t ha

/-! ## Scalar arithmetic helpers -/

/-- The bracket `t^{1/6}(1+log(2Y)) + t^{-1/6}√Y` from the target statement. -/
def brk (Y : ℕ) (t : ℝ) : ℝ :=
  t ^ (1/6:ℝ) * (1 + Real.log (2*(Y:ℝ))) + t^(-(1/6):ℝ) * Real.sqrt (Y:ℝ)

lemma brk_nonneg {Y : ℕ} (hY : 1 ≤ Y) {t : ℝ} (ht : 1 ≤ t) : 0 ≤ brk Y t := by
  unfold brk
  have ht0 : (0:ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  have hY1 : (1:ℝ) ≤ (Y:ℝ) := by exact_mod_cast hY
  have hlogY : 0 ≤ Real.log (2*(Y:ℝ)) := Real.log_nonneg (by linarith)
  exact add_nonneg (mul_nonneg (Real.rpow_nonneg ht0.le _) (by linarith))
    (mul_nonneg (Real.rpow_nonneg ht0.le _) (Real.sqrt_nonneg _))

lemma log_two_mul_le {M Y : ℕ} (hY : 1 ≤ Y) (h : M ≤ Y) :
    Real.log (2*(M:ℝ)) ≤ Real.log (2*(Y:ℝ)) := by
  rcases Nat.eq_zero_or_pos M with hM0 | hMpos
  · rw [hM0]; simp only [Nat.cast_zero, mul_zero, Real.log_zero]
    exact Real.log_nonneg (by
      have : (1:ℝ) ≤ (Y:ℝ) := by exact_mod_cast hY
      linarith)
  · refine Real.log_le_log (by positivity) ?_
    have : (M:ℝ) ≤ (Y:ℝ) := by exact_mod_cast h
    linarith

lemma inv_sqrt_mul_self {x : ℝ} (hx : 0 < x) : (Real.sqrt x)⁻¹ * x = Real.sqrt x := by
  field_simp
  rw [Real.sq_sqrt hx.le]

/-- `(√a)⁻¹ ≤ 2(√a − √(a−1))`. -/
lemma inv_sqrt_le_two_diff {a : ℕ} (ha : 1 ≤ a) :
    (Real.sqrt (a:ℝ))⁻¹ ≤ 2 * (Real.sqrt (a:ℝ) - Real.sqrt ((a-1 : ℕ):ℝ)) := by
  have ha0 : (0:ℝ) < (a:ℝ) := by exact_mod_cast (by omega : 0 < a)
  have ham : ((a-1:ℕ):ℝ) = (a:ℝ) - 1 := by
    rw [Nat.cast_sub ha]; norm_num
  have hm0 : (0:ℝ) ≤ ((a-1:ℕ):ℝ) := Nat.cast_nonneg _
  have hma : ((a-1:ℕ):ℝ) ≤ (a:ℝ) := by
    have h := Nat.sub_le a 1
    exact_mod_cast h
  have hdiff :
      (Real.sqrt (a:ℝ) - Real.sqrt ((a-1:ℕ):ℝ))
        * (Real.sqrt (a:ℝ) + Real.sqrt ((a-1:ℕ):ℝ)) = 1 := by
    have h1 : (Real.sqrt ((a:ℝ))) ^ 2 = (a:ℝ) := Real.sq_sqrt ha0.le
    have h2 : (Real.sqrt (((a-1:ℕ):ℝ))) ^ 2 = ((a-1:ℕ):ℝ) := Real.sq_sqrt hm0
    nlinarith [h1, h2, ham]
  have hpos : 0 < Real.sqrt (a:ℝ) + Real.sqrt ((a-1:ℕ):ℝ) :=
    add_pos_of_pos_of_nonneg (Real.sqrt_pos.mpr ha0) (Real.sqrt_nonneg _)
  have hval : Real.sqrt (a:ℝ) - Real.sqrt ((a-1:ℕ):ℝ)
      = 1 / (Real.sqrt (a:ℝ) + Real.sqrt ((a-1:ℕ):ℝ)) := by
    rw [eq_div_iff (ne_of_gt hpos), hdiff]
  rw [hval, mul_one_div, le_div_iff₀ hpos]
  have hstep : (Real.sqrt (a:ℝ))⁻¹ * (Real.sqrt (a:ℝ) + Real.sqrt ((a-1:ℕ):ℝ))
      = 1 + (Real.sqrt (a:ℝ))⁻¹ * Real.sqrt ((a-1:ℕ):ℝ) := by
    rw [mul_add, inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr ha0))]
  rw [hstep]
  have hle : (Real.sqrt (a:ℝ))⁻¹ * Real.sqrt ((a-1:ℕ):ℝ) ≤ 1 := by
    calc (Real.sqrt (a:ℝ))⁻¹ * Real.sqrt ((a-1:ℕ):ℝ)
        ≤ (Real.sqrt (a:ℝ))⁻¹ * Real.sqrt (a:ℝ) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hma)
            (inv_nonneg.mpr (Real.sqrt_nonneg _))
      _ = 1 := inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr ha0))
  linarith

lemma sum_Icc_one_eq_sum_range (k : ℕ) (g : ℕ → ℝ) :
    (∑ a ∈ Finset.Icc 1 k, g a) = ∑ i ∈ Finset.range k, g (i+1) := by
  rw [← Finset.Ico_succ_right_eq_Icc (1:ℕ) k, Finset.sum_Ico_eq_sum_range]
  have hk : Order.succ k - 1 = k := by simp
  rw [hk]
  apply Finset.sum_congr rfl
  intro i hi
  rw [add_comm]

lemma sum_inv_sqrt_Icc_le (k : ℕ) :
    ∑ a ∈ Finset.Icc 1 k, (Real.sqrt (a:ℝ))⁻¹ ≤ 2 * Real.sqrt (k:ℝ) := by
  have h : ∑ a ∈ Finset.Icc 1 k, (Real.sqrt (a:ℝ))⁻¹
      ≤ ∑ a ∈ Finset.Icc 1 k, 2 * (Real.sqrt (a:ℝ) - Real.sqrt ((a-1:ℕ):ℝ)) :=
    Finset.sum_le_sum (fun a ha => inv_sqrt_le_two_diff (Finset.mem_Icc.mp ha).1)
  refine le_trans h ?_
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  rw [sum_Icc_one_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  rw [Finset.sum_range_sub (fun i => Real.sqrt (i:ℝ)) k]
  simp [Real.sqrt_zero]

lemma sqrt_sum_div_le (q k : ℕ) (hk : k ≤ q) :
    ∑ a ∈ Finset.Icc 1 k, Real.sqrt ((q:ℝ)/(a:ℝ)) ≤ 2 * (q:ℝ) := by
  have hterm : ∀ a ∈ Finset.Icc 1 k,
      Real.sqrt ((q:ℝ)/(a:ℝ)) = Real.sqrt (q:ℝ) * (Real.sqrt (a:ℝ))⁻¹ := by
    intro a ha
    have ha0 : (0:ℝ) < (a:ℝ) := by
      have : 1 ≤ a := (Finset.mem_Icc.mp ha).1
      exact_mod_cast (by omega : 0 < a)
    rw [Real.sqrt_div (by positivity), div_eq_mul_inv]
  calc ∑ a ∈ Finset.Icc 1 k, Real.sqrt ((q:ℝ)/(a:ℝ))
      = ∑ a ∈ Finset.Icc 1 k, Real.sqrt (q:ℝ) * (Real.sqrt (a:ℝ))⁻¹ :=
        Finset.sum_congr rfl hterm
    _ = Real.sqrt (q:ℝ) * (∑ a ∈ Finset.Icc 1 k, (Real.sqrt (a:ℝ))⁻¹) := by
        rw [Finset.mul_sum]
    _ ≤ Real.sqrt (q:ℝ) * (2 * Real.sqrt (k:ℝ)) :=
        mul_le_mul_of_nonneg_left (sum_inv_sqrt_Icc_le k) (Real.sqrt_nonneg _)
    _ ≤ 2 * (q:ℝ) := by
        have hkq : Real.sqrt (k:ℝ) ≤ Real.sqrt (q:ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hk)
        have hprod : Real.sqrt (q:ℝ) * Real.sqrt (k:ℝ) ≤ Real.sqrt (q:ℝ) * Real.sqrt (q:ℝ) :=
          mul_le_mul_of_nonneg_left hkq (Real.sqrt_nonneg _)
        rw [Real.mul_self_sqrt (by positivity)] at hprod
        nlinarith [hprod]

/-! ## Main theorem -/

/-- Splitting off the `m = 0` term of a block sum: `Icc 0 M = {0} ∪ Icc 1 M`. -/
lemma Icc_zero_eq_insert (M : ℕ) : Finset.Icc 0 M = insert 0 (Finset.Icc 1 M) := by
  ext x
  simp only [Finset.mem_Icc, Finset.mem_insert]
  constructor <;> intro h <;> omega

theorem char_head_sum_weyl_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) (hq : 1 ≤ q) (χ : DirichletCharacter ℂ q)
        (X₀ Y : ℕ) (hXY : X₀ ≤ q * Y) (hY : 1 ≤ Y)
        (t : ℝ) (ht : 1 ≤ t) (hYt : (q : ℝ) * (Y : ℝ) ^ 2 ≤ t),
        ‖∑ n ∈ Finset.Icc 1 X₀,
            (χ n) *
              Complex.exp ((((2 * Real.pi * (-(t / (2 * Real.pi)) * Real.log (n : ℝ))) : ℝ) : ℂ)
                * Complex.I) / Real.sqrt (n : ℝ)‖
          ≤ C * Real.sqrt (q : ℝ) *
              (t ^ (1 / 6 : ℝ) * (1 + Real.log (2 * (Y : ℝ))) +
                t ^ (-(1 / 6 : ℝ)) * Real.sqrt (Y : ℝ)) := by
  obtain ⟨Cs, hCs, hshift⟩ :=
    Commons.Analysis.ExponentialSums.log_phase_shifted_head_sum_weyl
  have hlog2n : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  refine ⟨Cs + 2, by positivity, ?_⟩
  intro q hq χ X₀ Y hXY hY t ht hYt
  have hbrk : t ^ (1/6:ℝ) * (1 + Real.log (2*(Y:ℝ))) + t^(-(1/6):ℝ) * Real.sqrt (Y:ℝ)
      = brk Y t := rfl
  rw [hbrk]
  rcases Nat.eq_zero_or_pos X₀ with hX0 | hX0
  · subst hX0
    rw [Finset.Icc_eq_empty (by norm_num : ¬ ((1:ℕ) ≤ 0)), Finset.sum_empty, norm_zero]
    exact mul_nonneg (mul_nonneg (by positivity) (Real.sqrt_nonneg _)) (brk_nonneg hY ht)
  · have hqpos : 0 < q := by omega
    have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hqpos
    have ht0 : (0:ℝ) < t := lt_of_lt_of_le zero_lt_one ht
    have hY1 : (1:ℝ) ≤ (Y:ℝ) := by exact_mod_cast hY
    have hYsq : (Y:ℝ)^2 ≤ t := by
      have hq1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
      nlinarith [hYt, hq1, sq_nonneg ((Y:ℝ))]
    have hrewrite : (∑ n ∈ Finset.Icc 1 X₀,
            (χ n) * Complex.exp ((((2 * Real.pi * (-(t / (2 * Real.pi)) * Real.log (n : ℝ))) : ℝ) : ℂ) * Complex.I)
              / Real.sqrt (n : ℝ))
        = ∑ n ∈ Finset.Icc 1 X₀, χ n * wsum t (n:ℝ) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact target_summand χ t n
    rw [hrewrite]
    rw [residue_block_sum_decomp q X₀ hq (fun n => χ n * wsum t (n:ℝ))]
    have hinvq : (0:ℝ) ≤ (Real.sqrt (q:ℝ))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
    have hstep1 : ‖∑ a ∈ Finset.Icc 1 (min q X₀),
          ∑ m ∈ Finset.Icc 0 ((X₀ - a)/q), χ ((a + m*q : ℕ) : ZMod q) * wsum t ((a + m*q : ℕ) : ℝ)‖
        ≤ (Real.sqrt (q:ℝ))⁻¹ * (∑ a ∈ Finset.Icc 1 (min q X₀), ‖blk q X₀ t a‖) := by
      calc ‖∑ a ∈ Finset.Icc 1 (min q X₀),
              (∑ m ∈ Finset.Icc 0 ((X₀ - a)/q), χ ((a + m*q : ℕ) : ZMod q) * wsum t ((a + m*q : ℕ) : ℝ))‖
          ≤ ∑ a ∈ Finset.Icc 1 (min q X₀),
              ‖∑ m ∈ Finset.Icc 0 ((X₀ - a)/q), χ ((a + m*q : ℕ) : ZMod q) * wsum t ((a + m*q : ℕ) : ℝ)‖ :=
            norm_sum_le _ _
        _ = ∑ a ∈ Finset.Icc 1 (min q X₀), ‖χ a * wsum t (q:ℝ) * blk q X₀ t a‖ := by
              apply Finset.sum_congr rfl
              intro a ha
              rw [blk_eq_factor hq χ t (Finset.mem_Icc.mp ha).1]
        _ ≤ ∑ a ∈ Finset.Icc 1 (min q X₀), (Real.sqrt (q:ℝ))⁻¹ * ‖blk q X₀ t a‖ := by
              apply Finset.sum_le_sum
              intro a ha
              simp only [norm_mul]
              have hcha : ‖χ a‖ ≤ 1 := χ.norm_le_one a
              have hqw : ‖wsum t (q:ℝ)‖ = (Real.sqrt (q:ℝ))⁻¹ := norm_wsum hqR
              rw [hqw]
              have hb0 : (0:ℝ) ≤ ‖blk q X₀ t a‖ := norm_nonneg _
              have h1 : ‖χ a‖ * (Real.sqrt (q:ℝ))⁻¹ ≤ 1 * (Real.sqrt (q:ℝ))⁻¹ :=
                mul_le_mul_of_nonneg_right hcha hinvq
              calc ‖χ a‖ * (Real.sqrt (q:ℝ))⁻¹ * ‖blk q X₀ t a‖
                  ≤ 1 * (Real.sqrt (q:ℝ))⁻¹ * ‖blk q X₀ t a‖ :=
                    mul_le_mul_of_nonneg_right h1 hb0
                _ = (Real.sqrt (q:ℝ))⁻¹ * ‖blk q X₀ t a‖ := by ring
        _ = (Real.sqrt (q:ℝ))⁻¹ * (∑ a ∈ Finset.Icc 1 (min q X₀), ‖blk q X₀ t a‖) := by
              rw [Finset.mul_sum]
    have hcardIcc : (Finset.Icc 1 (min q X₀)).card = min q X₀ := by
      rw [Nat.card_Icc]; omega
    have hblk_bound : ∀ a ∈ Finset.Icc 1 (min q X₀),
        ‖blk q X₀ t a‖ ≤ Real.sqrt ((q:ℝ)/(a:ℝ)) + Cs * brk Y t := by
      intro a ha
      have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
      have haR : (0:ℝ) < (a:ℝ) := by exact_mod_cast (by omega : 0 < a)
      set M := (X₀ - a)/q with hM
      have hMle : M ≤ Y := by
        rw [hM]
        exact le_trans (Nat.div_le_div_right (Nat.sub_le X₀ a)) (Nat.div_le_of_le_mul hXY)
      have hsplit : blk q X₀ t a
          = wsum t ((0:ℝ) + (a:ℝ)/(q:ℝ))
            + ∑ m ∈ Finset.Icc 1 M, wsum t ((m:ℝ) + (a:ℝ)/(q:ℝ)) := by
        unfold blk
        rw [← hM]
        rw [Icc_zero_eq_insert M]
        rw [Finset.sum_insert (by simp [Finset.mem_Icc] : (0:ℕ) ∉ Finset.Icc 1 M)]
        simp only [Nat.cast_zero]
      have hnorm0 : ‖wsum t ((0:ℝ) + (a:ℝ)/(q:ℝ))‖ = Real.sqrt ((q:ℝ)/(a:ℝ)) := by
        have hpos : (0:ℝ) < (a:ℝ)/(q:ℝ) := div_pos haR hqR
        rw [zero_add, norm_wsum hpos, ← Real.sqrt_inv, inv_div]
      have htail : ‖∑ m ∈ Finset.Icc 1 M, wsum t ((m:ℝ) + (a:ℝ)/(q:ℝ))‖
          ≤ Cs * (t^(1/6:ℝ)*(1+Real.log (2*(M:ℝ))) + t^(-(1/6):ℝ)*Real.sqrt (M:ℝ)) := by
        rcases Nat.eq_zero_or_pos M with hM0 | hMpos
        · rw [hM0, Finset.Icc_eq_empty (by norm_num : ¬ ((1:ℕ) ≤ 0)), Finset.sum_empty, norm_zero]
          simp only [Nat.cast_zero, mul_zero, Real.log_zero, Real.sqrt_zero, mul_one, add_zero]
          exact mul_nonneg hCs.le (Real.rpow_nonneg ht0.le _)
        · have hc : (0:ℝ) < (a:ℝ)/(q:ℝ) := div_pos haR hqR
          have hMY : (M:ℝ) ≤ (Y:ℝ) := by exact_mod_cast hMle
          have hMt : (M:ℝ)^2 ≤ t := by
            nlinarith [hMY, hYsq, (Nat.cast_nonneg M : (0:ℝ) ≤ (M:ℝ))]
          have hres := hshift ((a:ℝ)/(q:ℝ)) hc M hMpos t ht hMt
          have hsum_eq : (∑ m ∈ Finset.Icc 1 M, wsum t ((m:ℝ)+(a:ℝ)/(q:ℝ)))
              = ∑ m ∈ Finset.Icc 1 M,
                  Complex.exp ((((-(t * Real.log ((a:ℝ)/(q:ℝ) + (m:ℝ)))) : ℝ) : ℂ) * Complex.I)
                    / ((Real.sqrt ((a:ℝ)/(q:ℝ) + (m:ℝ)) : ℝ) : ℂ) := by
            apply Finset.sum_congr rfl
            intro m hm
            exact wsum_shift t ((a:ℝ)/(q:ℝ)) m
          rw [hsum_eq]
          exact hres
      have hBr : t^(1/6:ℝ)*(1+Real.log (2*(M:ℝ))) + t^(-(1/6):ℝ)*Real.sqrt (M:ℝ)
          ≤ brk Y t := by
        have hlogM : Real.log (2*(M:ℝ)) ≤ Real.log (2*(Y:ℝ)) := log_two_mul_le hY hMle
        have hsqrtM : Real.sqrt (M:ℝ) ≤ Real.sqrt (Y:ℝ) :=
          Real.sqrt_le_sqrt (by exact_mod_cast hMle)
        have h1 : t^(1/6:ℝ)*(1+Real.log (2*(M:ℝ)))
            ≤ t^(1/6:ℝ)*(1+Real.log (2*(Y:ℝ))) :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg ht0.le _)
        have h2 : t^(-(1/6):ℝ)*Real.sqrt (M:ℝ) ≤ t^(-(1/6):ℝ)*Real.sqrt (Y:ℝ) :=
          mul_le_mul_of_nonneg_left hsqrtM (Real.rpow_nonneg ht0.le _)
        unfold brk
        linarith
      calc ‖blk q X₀ t a‖
          = ‖wsum t ((0:ℝ)+(a:ℝ)/(q:ℝ))
              + ∑ m ∈ Finset.Icc 1 M, wsum t ((m:ℝ)+(a:ℝ)/(q:ℝ))‖ := by rw [hsplit]
        _ ≤ ‖wsum t ((0:ℝ)+(a:ℝ)/(q:ℝ))‖
              + ‖∑ m ∈ Finset.Icc 1 M, wsum t ((m:ℝ)+(a:ℝ)/(q:ℝ))‖ := norm_add_le _ _
        _ ≤ Real.sqrt ((q:ℝ)/(a:ℝ))
              + Cs*(t^(1/6:ℝ)*(1+Real.log (2*(M:ℝ))) + t^(-(1/6):ℝ)*Real.sqrt (M:ℝ)) := by
              rw [hnorm0]; exact add_le_add (le_refl _) htail
        _ ≤ Real.sqrt ((q:ℝ)/(a:ℝ)) + Cs * brk Y t :=
              add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hBr hCs.le)
    have hsum_sqrt : (∑ a ∈ Finset.Icc 1 (min q X₀), Real.sqrt ((q:ℝ)/(a:ℝ))) ≤ 2*(q:ℝ) :=
      sqrt_sum_div_le q (min q X₀) (min_le_left q X₀)
    have hcard : (((min q X₀ : ℕ)) : ℝ) ≤ (q:ℝ) := by exact_mod_cast min_le_left q X₀
    have hbrkY : (0:ℝ) ≤ brk Y t := brk_nonneg hY ht
    have hsum_blk : (∑ a ∈ Finset.Icc 1 (min q X₀), ‖blk q X₀ t a‖)
        ≤ 2*(q:ℝ) + Cs*(q:ℝ)*brk Y t := by
      calc (∑ a ∈ Finset.Icc 1 (min q X₀), ‖blk q X₀ t a‖)
          ≤ ∑ a ∈ Finset.Icc 1 (min q X₀), (Real.sqrt ((q:ℝ)/(a:ℝ)) + Cs * brk Y t) :=
            Finset.sum_le_sum hblk_bound
        _ = (∑ a ∈ Finset.Icc 1 (min q X₀), Real.sqrt ((q:ℝ)/(a:ℝ)))
              + (((min q X₀ : ℕ)) : ℝ) * (Cs * brk Y t) := by
            rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hcardIcc]
        _ ≤ 2*(q:ℝ) + (q:ℝ)*(Cs * brk Y t) :=
            add_le_add hsum_sqrt (mul_le_mul_of_nonneg_right hcard (mul_nonneg hCs.le hbrkY))
        _ = 2*(q:ℝ) + Cs*(q:ℝ)*brk Y t := by ring
    have hBge : 1 + Real.log 2 ≤ brk Y t := by
      unfold brk
      have ht6 : (1:ℝ) ≤ t^(1/6:ℝ) := Real.one_le_rpow ht (by norm_num)
      have hlog2Y : Real.log 2 ≤ Real.log (2*(Y:ℝ)) := by
        apply Real.log_le_log (by norm_num); linarith
      have h1 : (1:ℝ)*(1+Real.log 2) ≤ t^(1/6:ℝ)*(1+Real.log (2*(Y:ℝ))) :=
        mul_le_mul ht6 (by linarith) (by linarith) (Real.rpow_nonneg ht0.le _)
      have h2 : (0:ℝ) ≤ t^(-(1/6):ℝ)*Real.sqrt (Y:ℝ) := by positivity
      linarith
    have hfinal : ‖∑ a ∈ Finset.Icc 1 (min q X₀),
          ∑ m ∈ Finset.Icc 0 ((X₀ - a)/q), χ ((a + m*q : ℕ) : ZMod q) * wsum t ((a + m*q : ℕ) : ℝ)‖
        ≤ (Cs + 2) * Real.sqrt (q:ℝ) * brk Y t := by
      have hsq : (Real.sqrt (q:ℝ))⁻¹ * (q:ℝ) = Real.sqrt (q:ℝ) := inv_sqrt_mul_self hqR
      have hmid : (Real.sqrt (q:ℝ))⁻¹ * (2*(q:ℝ) + Cs*(q:ℝ)*brk Y t)
          = 2*Real.sqrt (q:ℝ) + Cs*Real.sqrt (q:ℝ)*brk Y t := by
        calc (Real.sqrt (q:ℝ))⁻¹ * (2*(q:ℝ) + Cs*(q:ℝ)*brk Y t)
            = 2 * ((Real.sqrt (q:ℝ))⁻¹ * (q:ℝ))
                + Cs * ((Real.sqrt (q:ℝ))⁻¹ * (q:ℝ)) * brk Y t := by ring
          _ = 2*Real.sqrt (q:ℝ) + Cs*Real.sqrt (q:ℝ)*brk Y t := by rw [hsq]
      have hB1 : (1:ℝ) ≤ brk Y t := by linarith
      have hs0 : (0:ℝ) ≤ Real.sqrt (q:ℝ) := Real.sqrt_nonneg _
      have he1 : 2*Real.sqrt (q:ℝ) ≤ 2*Real.sqrt (q:ℝ)*brk Y t := by nlinarith [hs0, hB1]
      have hlast : 2*Real.sqrt (q:ℝ) + Cs*Real.sqrt (q:ℝ)*brk Y t
          ≤ (Cs + 2) * Real.sqrt (q:ℝ) * brk Y t := by
        calc 2*Real.sqrt (q:ℝ) + Cs*Real.sqrt (q:ℝ)*brk Y t
            = 2*Real.sqrt (q:ℝ) + Cs*(Real.sqrt (q:ℝ)*brk Y t) := by ring
          _ ≤ 2*(Real.sqrt (q:ℝ)*brk Y t) + Cs*(Real.sqrt (q:ℝ)*brk Y t) := by linarith
          _ = (Cs + 2) * Real.sqrt (q:ℝ) * brk Y t := by ring
      calc ‖∑ a ∈ Finset.Icc 1 (min q X₀),
            ∑ m ∈ Finset.Icc 0 ((X₀ - a)/q), χ ((a + m*q : ℕ) : ZMod q) * wsum t ((a + m*q : ℕ) : ℝ)‖
          ≤ (Real.sqrt (q:ℝ))⁻¹ * (∑ a ∈ Finset.Icc 1 (min q X₀), ‖blk q X₀ t a‖) := hstep1
        _ ≤ (Real.sqrt (q:ℝ))⁻¹ * (2*(q:ℝ) + Cs*(q:ℝ)*brk Y t) :=
              mul_le_mul_of_nonneg_left hsum_blk hinvq
        _ = 2*Real.sqrt (q:ℝ) + Cs*Real.sqrt (q:ℝ)*brk Y t := hmid
        _ ≤ (Cs + 2) * Real.sqrt (q:ℝ) * brk Y t := hlast
    exact hfinal

end

end Commons.NumberTheory.DirichletCharacter
