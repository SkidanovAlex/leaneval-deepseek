import Mathlib
import Submission.Work.Diff.STE.B3.SymCalcStep8.CSqZ
import Submission.Work.Diff.STE.B3.SymCalcStep5.conjCut_lapPow
import Submission.Work.Diff.STE.B3.SymCalcStep1.laplacian_pow_mul_comm_le
import Submission.Work.Diff.STE.B3.SymCalcStep6.conjLapPow_mul_comm_le
import Submission.Work.Diff.STE.B3.SymCalcStep6.lapPow_toolbox
import Submission.Work.Diff.STE.B3.flat_diag_pairing_le
import Submission.Work.Diff.STE.B3.SymCalcStep8.lapPow_CSqZ_le
import Submission.Work.Diff.STE.summable_conv_nonneg_tsum
import Submission.Work.Diff.STE.tsum_mul_sq_le
import Submission.Work.Diff.STE.wt_pow_le
import Submission.Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `[Λ^k, M_b]` loses exactly `2k − 1` derivatives, at **integer** exponents

This file proves `Work.Diff.STE.B3.SymCalcStep8.lapPow_mul_comm_CSqZ_le`: for a smooth
`1`-periodic multiplier `b` and every integer exponent `t`,

  `CSqZ t (fourierCoeff ([Λ^k, M_b] G)) ≤ C · CSqZ (t + 2k − 1) (fourierCoeff G)`,

uniformly in the smooth `1`-periodic `G`.  At `t ≥ 0` this is `SymCalcStep6.dB3_flat_comm_le`
(the classical order-`2k−1` Leibniz estimate); the point of the present file is the **negative**
range `t < 0`, which the `SymCalcStep8` pairing estimates need (`CSqZ (-(k-1)) [Λ^k, Φ]`).

## Route

Everything is done on the coefficient side.  With `β = fourierCoeff b`, `c = fourierCoeff G` and
the symbol `λ = flatLam`, the coefficient family of `[Λ^k, M_b] G` is

  `m ↦ λ(m)^k (β * c)(m) − (β * (λ^k c))(m) = Σ_l β l (λ(m)^k − λ(m−l)^k) c (m−l)`

(`dB3_fourierCoeff_lapPow_comm` identifies it with the first form).

The estimate is proved by the **difference-quotient decomposition of the symbol**, which is
uniform in the sign of `t`:

* `k = 1` ("one step"): `λ(m) − λ(m−l) = Σᵢ (2π)² (lᵢ² + 2 lᵢ (m−l)ᵢ)`.  The first piece is a
  convolution with the rapidly decaying kernel `l ↦ ‖β l‖ ⟨l⟩`, hence bounded on every `CSqZ t`
  (`kernel_abs_CSqZ_le`); the second carries the *extra* factor `(m−l)ᵢ` on the *input* family,
  which is worth exactly one `⟨·⟩`.  Hence `CSqZ t ([Λ, M_b] c) ≤ C CSqZ (t+1) c` for **every**
  integer `t`.
* General `k`: `λ^k − μ^k = Σ_{i<k} λ^i (λ − μ) μ^{k−1−i}`, i.e.
  `[Λ^k, M_b] = Σ_{i<k} Λ^i [Λ, M_b] Λ^{k−1−i}` (telescoping): `Λ^i` costs `2i` and `Λ^{k−1−i}`
  costs `2(k−1−i)`, so the orders add up to `2k−1`.

The key point is that no `H^t`-index of the intermediate families has to be nonnegative: the kernel
bounds and the `⟨j⟩`-shift are stated for arbitrary integer exponents, with Peetre's inequality in
the two-sided form `⟨m⟩^t ≤ 2^{|t|} ⟨l⟩^{|t|} ⟨m−l⟩^t`, which is valid for `t < 0` as well (the
naive one-sided version is in the wrong direction there).
-/

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 4000000

namespace Work.Diff.STE.B3.SymCalcStep8

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "wt" => Work.Diff.STE.wt
local notation "lam" => Work.Diff.STE.B3.SymCalc.flatLam

/-- The complexified symbol `λ(m)` of the flat Laplacian. -/
def lamC (m : ι → ℤ) : ℂ := ((lam m : ℝ) : ℂ)

lemma lamC_sub (m l : ι → ℤ) : lamC m - lamC (m - l) = (((lam m - lam (m - l) : ℝ)) : ℂ) := by
  simp only [lamC, Complex.ofReal_sub]

lemma lamC_pow (k : ℕ) (m : ι → ℤ) : lamC m ^ k = ((((lam m) ^ k : ℝ)) : ℂ) := by
  simp only [lamC, Complex.ofReal_pow]

lemma norm_lamC_sub (m l : ι → ℤ) : ‖lamC m - lamC (m - l)‖ = |lam m - lam (m - l)| := by
  rw [lamC_sub, Complex.norm_real, Real.norm_eq_abs]

lemma norm_lamC_pow_sub (k : ℕ) (m l : ι → ℤ) :
    ‖lamC m ^ k - lamC (m - l) ^ k‖ = |(lam m) ^ k - (lam (m - l)) ^ k| := by
  rw [lamC_pow, lamC_pow, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

/-! ## 1. Rapidly decaying coefficient families -/

/-- Rapid decay in the weighted `ℓ²` scale: all moments `Σ ⟨m⟩^N ‖c m‖²` converge. -/
def Rapid (c : (ι → ℤ) → ℂ) : Prop :=
  ∀ N : ℕ, Summable (fun m : ι → ℤ => (wt m) ^ N * ‖c m‖ ^ 2)

/-- Rapid decay in the weighted `ℓ¹` scale: all moments `Σ ⟨m⟩^N ‖a m‖` converge. -/
def RapidL1 (a : (ι → ℤ) → ℂ) : Prop :=
  ∀ N : ℕ, Summable (fun m : ι → ℤ => (wt m) ^ N * ‖a m‖)

lemma wt_neg' (l : ι → ℤ) : wt (-l) = wt l := by
  simp only [Work.Diff.STE.wt, Pi.neg_apply, Int.cast_neg, neg_sq]

/-- **Peetre's inequality for integer powers** (two-sided form): for *every* integer `t`,
`⟨m⟩^t ≤ 2^{|t|} ⟨l⟩^{|t|} ⟨m−l⟩^t`. -/
lemma wt_zpow_le (m l : ι → ℤ) (τ : ℤ) :
    (wt m) ^ τ ≤ (2 : ℝ) ^ (Int.natAbs τ) * ((wt l) ^ (Int.natAbs τ) * (wt (m - l)) ^ τ) := by
  rcases lt_or_ge τ 0 with hτ | hτ
  · set n : ℕ := Int.natAbs τ with hn
    have hτn : τ = -((n : ℕ) : ℤ) := by
      have h : ((n : ℕ) : ℤ) = -τ := by
        rw [hn, ← Int.natAbs_neg τ]
        exact Int.natAbs_of_nonneg (by omega)
      linarith
    have hbase : wt (m - l) ≤ 2 * wt l * wt m := by
      have h := Work.Diff.STE.wt_le_two_mul (m - l) m
      have h' : (m - l) - m = -l := by abel
      rw [h', wt_neg'] at h
      linarith
    have hbase' : (wt m)⁻¹ ≤ (2 * wt l) * (wt (m - l))⁻¹ := by
      have h1 : (wt m)⁻¹ = (2 * wt l) * (1 / (2 * wt l * wt m)) := by
        rw [one_div, mul_inv, ← mul_assoc,
          mul_inv_cancel₀ (mul_ne_zero (by norm_num) (ne_of_gt (Work.Diff.STE.wt_pos l))),
          one_mul]
      have h2 : (2 * wt l) * (1 / (2 * wt l * wt m)) ≤ (2 * wt l) * (1 / wt (m - l)) :=
        mul_le_mul_of_nonneg_left
          (one_div_le_one_div_of_le (Work.Diff.STE.wt_pos (m-l)) hbase)
          (mul_nonneg (by norm_num) (le_of_lt (Work.Diff.STE.wt_pos l)))
      have h3 : (2 * wt l) * (1 / wt (m - l)) = (2 * wt l) * (wt (m - l))⁻¹ := by rw [one_div]
      calc (wt m)⁻¹ = (2 * wt l) * (1 / (2 * wt l * wt m)) := h1
        _ ≤ (2 * wt l) * (1 / wt (m - l)) := h2
        _ = (2 * wt l) * (wt (m - l))⁻¹ := h3
    calc (wt m) ^ τ = ((wt m)⁻¹) ^ n := by rw [hτn, zpow_neg, zpow_natCast, inv_pow]
      _ ≤ ((2 * wt l) * (wt (m - l))⁻¹) ^ n :=
          pow_le_pow_left₀ (inv_nonneg.mpr (le_of_lt (Work.Diff.STE.wt_pos m))) hbase' n
      _ = (2 : ℝ) ^ n * ((wt l) ^ n * (wt (m - l)) ^ τ) := by
          rw [mul_pow, mul_pow, hτn, zpow_neg, zpow_natCast, inv_pow]
          ring_nf
  · have h1 : (wt m) ^ τ ≤ (2 * (wt l * wt (m - l))) ^ τ :=
      zpow_le_zpow_left₀ hτ (le_of_lt (Work.Diff.STE.wt_pos m))
        (Work.Diff.STE.wt_le_two_mul m l)
    rw [mul_zpow, mul_zpow] at h1
    have h2 : (2 : ℝ) ^ τ ≤ (2 : ℝ) ^ (Int.natAbs τ) :=
      zpow_le_zpow_right₀ (by norm_num) Int.le_natAbs
    have h3 : (wt l) ^ τ ≤ (wt l) ^ (Int.natAbs τ) :=
      zpow_le_zpow_right₀ (Work.Diff.STE.wt_one_le l) Int.le_natAbs
    have h4 : (0 : ℝ) ≤ (wt (m-l)) ^ τ :=
      zpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos _)) τ
    have h5 : (0 : ℝ) ≤ (wt l) ^ τ :=
      zpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos l)) τ
    calc (wt m) ^ τ ≤ (2 : ℝ) ^ τ * ((wt l) ^ τ * (wt (m - l)) ^ τ) := h1
      _ ≤ (2 : ℝ) ^ (Int.natAbs τ) * ((wt l) ^ (Int.natAbs τ) * (wt (m - l)) ^ τ) :=
          mul_le_mul h2 (mul_le_mul_of_nonneg_right h3 h4) (mul_nonneg h5 h4) (by positivity)

/-- Peetre for natural powers, weight on the `l`-side: `⟨l⟩^A ≤ 2^A ⟨m⟩^A ⟨m−l⟩^A`. -/
lemma wt_pow_le_left (m l : ι → ℤ) (A : ℕ) :
    (wt l) ^ A ≤ 2 ^ A * (wt m) ^ A * (wt (m - l)) ^ A := by
  have h : wt l ≤ 2 * (wt m * wt (m - l)) := by
    have h := Work.Diff.STE.wt_le_two_mul l m
    have h' : l - m = -(m - l) := by abel
    rw [h', wt_neg'] at h
    linarith
  calc (wt l) ^ A ≤ (2 * (wt m * wt (m - l))) ^ A :=
        pow_le_pow_left₀ (le_of_lt (Work.Diff.STE.wt_pos l)) h A
    _ = 2 ^ A * (wt m) ^ A * (wt (m - l)) ^ A := by rw [mul_pow, mul_pow]; ring_nf

/-- Peetre for natural powers, weight on the `(m−l)`-side. -/
lemma wt_pow_le_right (m l : ι → ℤ) (B : ℕ) :
    (wt (m - l)) ^ B ≤ 2 ^ B * (wt m) ^ B * (wt l) ^ B := by
  have h : wt (m - l) ≤ 2 * (wt m * wt l) := by
    have h := Work.Diff.STE.wt_le_two_mul (m - l) m
    have h' : (m - l) - m = -l := by abel
    rw [h', wt_neg'] at h
    linarith
  calc (wt (m - l)) ^ B ≤ (2 * (wt m * wt l)) ^ B :=
        pow_le_pow_left₀ (le_of_lt (Work.Diff.STE.wt_pos _)) h B
    _ = 2 ^ B * (wt m) ^ B * (wt l) ^ B := by rw [mul_pow, mul_pow]; ring_nf

/-- An integer power of the weight is summable against a rapidly decaying `ℓ²` family. -/
lemma Rapid.summable_zpow (c : (ι → ℤ) → ℂ) (hc : Rapid c) (τ : ℤ) :
    Summable (fun m : ι → ℤ => (wt m) ^ τ * ‖c m‖ ^ 2) := by
  rcases lt_or_ge τ 0 with hτ | hτ
  · have h0 : Summable (fun m : ι → ℤ => ‖c m‖ ^ 2) := by simpa using hc 0
    refine Summable.of_nonneg_of_le
      (fun m => mul_nonneg (zpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos m)) τ) (sq_nonneg _))
      (fun m => ?_) h0
    have h : (wt m) ^ τ ≤ 1 :=
      zpow_le_one_of_nonpos₀ (Work.Diff.STE.wt_one_le m) (le_of_lt hτ)
    exact mul_le_of_le_one_left (sq_nonneg _) h
  · have h := hc (Int.natAbs τ)
    refine h.congr (fun m => ?_)
    rw [← zpow_natCast, Int.natAbs_of_nonneg hτ]

/-- The same for the weighted `ℓ¹` scale. -/
lemma RapidL1.summable_zpow (a : (ι → ℤ) → ℂ) (ha : RapidL1 a) (τ : ℤ) :
    Summable (fun m : ι → ℤ => (wt m) ^ τ * ‖a m‖) := by
  rcases lt_or_ge τ 0 with hτ | hτ
  · have h0 : Summable (fun m : ι → ℤ => ‖a m‖) := by simpa using ha 0
    refine Summable.of_nonneg_of_le
      (fun m => mul_nonneg (zpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos m)) τ) (norm_nonneg _))
      (fun m => ?_) h0
    have h : (wt m) ^ τ ≤ 1 :=
      zpow_le_one_of_nonpos₀ (Work.Diff.STE.wt_one_le m) (le_of_lt hτ)
    exact mul_le_of_le_one_left (norm_nonneg _) h
  · have h := ha (Int.natAbs τ)
    refine h.congr (fun m => ?_)
    rw [← zpow_natCast, Int.natAbs_of_nonneg hτ]

/-- A rapidly decaying weighted-`ℓ¹` family is square-summable with any weight. -/
lemma RapidL1.summable_nat_mul_sq (a : (ι → ℤ) → ℂ) (ha : RapidL1 a) (N : ℕ) :
    Summable (fun m : ι → ℤ => (wt m) ^ N * ‖a m‖ ^ 2) := by
  have ha0 : Summable (fun m : ι → ℤ => ‖a m‖) := by simpa using ha 0
  refine Summable.of_nonneg_of_le
    (fun m => mul_nonneg (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos m)) N) (sq_nonneg _))
    (fun m => ?_) ((ha N).mul_left (∑' m : ι → ℤ, ‖a m‖))
  have hs : ‖a m‖ ^ 2 ≤ (∑' m : ι → ℤ, ‖a m‖) * ‖a m‖ := by
    rw [sq]
    exact mul_le_mul_of_nonneg_right (ha0.le_tsum m (fun _ _ => norm_nonneg _)) (norm_nonneg _)
  calc (wt m) ^ N * ‖a m‖ ^ 2 ≤ (wt m) ^ N * ((∑' m : ι → ℤ, ‖a m‖) * ‖a m‖) :=
        mul_le_mul_of_nonneg_left hs (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos m)) N)
    _ = (∑' m : ι → ℤ, ‖a m‖) * ((wt m) ^ N * ‖a m‖) := by ring_nf

/-- Summability is invariant under the reflection `l ↦ m - l`. -/
lemma summable_sub_reflect (f : (ι → ℤ) → ℝ) (m : ι → ℤ) :
    Summable (fun l => f (m - l)) ↔ Summable f := by
  have hinj : Function.Injective (fun l : ι → ℤ => m - l) := by
    intro a b hab
    have h := congrArg (fun x : ι → ℤ => (x + m)) (congrArg Neg.neg hab)
    simpa using h
  refine ⟨fun h => ?_, fun h => by
    simpa only [Function.comp_def] using h.comp_injective hinj⟩
  have h2 : Summable (fun l : ι → ℤ => f (m - (m - l))) := by
    simpa only [Function.comp_def] using h.comp_injective hinj
  refine h2.congr (fun l => ?_)
  simp

/-- **Weighted Young-type domination.**  If `a` is rapidly decaying in `ℓ¹` and `c` in weighted
`ℓ²`, then for every `m` and all natural weights `A`, `B` the family
`l ↦ ⟨l⟩^A ⟨m−l⟩^B ‖a l‖ ‖c (m−l)‖` is summable. -/
lemma summable_conv_rapid (a c : (ι → ℤ) → ℂ) (ha : RapidL1 a) (hc : Rapid c)
    (m : ι → ℤ) (A B : ℕ) :
    Summable (fun l : ι → ℤ => (wt l) ^ A * (wt (m - l)) ^ B * ‖a l‖ * ‖c (m - l)‖) := by
  classical
  set A0 : ℝ := ∑' l : ι → ℤ, ‖a l‖ with hA0def
  have ha0 : Summable (fun l : ι → ℤ => ‖a l‖) := by simpa using ha 0
  have hA0 : 0 ≤ A0 := tsum_nonneg (fun _ => norm_nonneg _)
  have hAsup : ∀ l : ι → ℤ, ‖a l‖ ≤ A0 :=
    fun l => ha0.le_tsum l (fun _ _ => norm_nonneg _)
  -- the two half-domination bounds
  have hp1 : ∀ l : ι → ℤ, (wt l) ^ A * (wt (m - l)) ^ B * ‖a l‖
      ≤ 2 ^ B * (wt m) ^ B * ((wt l) ^ (A + B) * ‖a l‖) := by
    intro l
    have h := wt_pow_le_right m l B
    calc (wt l) ^ A * (wt (m - l)) ^ B * ‖a l‖
        ≤ (wt l) ^ A * (2 ^ B * (wt m) ^ B * (wt l) ^ B) * ‖a l‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left h (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos l)) A))
            (norm_nonneg _)
      _ = 2 ^ B * (wt m) ^ B * ((wt l) ^ (A + B) * ‖a l‖) := by rw [pow_add]; ring_nf
  have hp2 : ∀ l : ι → ℤ, (wt l) ^ A * (wt (m - l)) ^ B * ‖a l‖ * ‖c (m - l)‖ ^ 2
      ≤ A0 * 2 ^ A * (wt m) ^ A * ((wt (m - l)) ^ (A + B) * ‖c (m - l)‖ ^ 2) := by
    intro l
    have h := wt_pow_le_left m l A
    have h5 : (wt l) ^ A * (wt (m - l)) ^ B * ‖a l‖
        ≤ A0 * 2 ^ A * (wt m) ^ A * (wt (m - l)) ^ (A + B) := by
      have h1 : (wt l) ^ A * (wt (m - l)) ^ B
          ≤ (2 ^ A * (wt m) ^ A * (wt (m - l)) ^ A) * (wt (m - l)) ^ B :=
        mul_le_mul_of_nonneg_right h (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos _)) B)
      calc (wt l) ^ A * (wt (m - l)) ^ B * ‖a l‖
          ≤ ((2 ^ A * (wt m) ^ A * (wt (m - l)) ^ A) * (wt (m - l)) ^ B) * A0 :=
            mul_le_mul h1 (hAsup l) (norm_nonneg _)
              (mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
                (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos m)) A))
                (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos (m - l))) A))
                (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos (m - l))) B))
        _ = A0 * 2 ^ A * (wt m) ^ A * (wt (m - l)) ^ (A + B) := by rw [pow_add]; ring_nf
    calc (wt l) ^ A * (wt (m - l)) ^ B * ‖a l‖ * ‖c (m - l)‖ ^ 2
        ≤ (A0 * 2 ^ A * (wt m) ^ A * (wt (m - l)) ^ (A + B)) * ‖c (m - l)‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h5 (sq_nonneg _)
      _ = A0 * 2 ^ A * (wt m) ^ A * ((wt (m - l)) ^ (A + B) * ‖c (m - l)‖ ^ 2) := by ring_nf
  -- summability of the two half-domination families
  have hm1 : Summable (fun l : ι → ℤ => 2 ^ B * (wt m) ^ B * ((wt l) ^ (A + B) * ‖a l‖)) :=
    (ha (A + B)).mul_left _
  have hm2 : Summable (fun l : ι → ℤ =>
      A0 * 2 ^ A * (wt m) ^ A * ((wt (m - l)) ^ (A + B) * ‖c (m - l)‖ ^ 2)) :=
    (((summable_sub_reflect (fun j => (wt j) ^ (A + B) * ‖c j‖ ^ 2) m).mpr (hc (A + B))).mul_left _)
  have h3 : ∀ l : ι → ℤ, ‖c (m - l)‖ ≤ 1 + ‖c (m - l)‖ ^ 2 :=
    fun l => by nlinarith [norm_nonneg (c (m - l))]
  have hmaj : Summable (fun l : ι → ℤ =>
      2 ^ B * (wt m) ^ B * ((wt l) ^ (A + B) * ‖a l‖)
        + A0 * 2 ^ A * (wt m) ^ A * ((wt (m - l)) ^ (A + B) * ‖c (m - l)‖ ^ 2)) :=
    (hm1.add hm2).congr (fun l => by ring_nf)
  refine Summable.of_nonneg_of_le
    (fun l => mul_nonneg (mul_nonneg (mul_nonneg
      (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos l)) A)
      (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos (m - l))) B)) (norm_nonneg _)) (norm_nonneg _))
    (fun l => ?_) hmaj
  calc (wt l) ^ A * (wt (m - l)) ^ B * ‖a l‖ * ‖c (m - l)‖
      ≤ (wt l) ^ A * (wt (m - l)) ^ B * ‖a l‖ * (1 + ‖c (m - l)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (h3 l)
          (mul_nonneg (mul_nonneg (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos l)) A)
            (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos (m - l))) B)) (norm_nonneg _))
    _ = (wt l) ^ A * (wt (m - l)) ^ B * ‖a l‖
        + (wt l) ^ A * (wt (m - l)) ^ B * ‖a l‖ * ‖c (m - l)‖ ^ 2 := by ring_nf
    _ ≤ 2 ^ B * (wt m) ^ B * ((wt l) ^ (A + B) * ‖a l‖)
        + A0 * 2 ^ A * (wt m) ^ A * ((wt (m - l)) ^ (A + B) * ‖c (m - l)‖ ^ 2) :=
        add_le_add (hp1 l) (hp2 l)

/-! ## 2. The weighted convolution bound at integer exponents -/

/-- **The kernel bound at integer exponents** (absolute-value form, with the summability of the
majorant).  For a nonnegative kernel `k` with all weighted `ℓ¹` moments finite and every integer
`t`, the convolution `m ↦ Σ_l k l ‖c (m−l)‖` is bounded on the weighted `ℓ²` space `CSqZ t`. -/
theorem kernel_abs_CSqZ_le (k : (ι → ℤ) → ℝ) (hk : ∀ l, 0 ≤ k l)
    (hkN : ∀ N : ℕ, Summable (fun l : ι → ℤ => (wt l) ^ N * k l)) (τ : ℤ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : (ι → ℤ) → ℂ, Rapid c →
      (Summable (fun m : ι → ℤ => (wt m) ^ τ * (∑' l, k l * ‖c (m - l)‖) ^ 2)) ∧
      CSqZ τ (fun m : ι → ℤ => ((∑' l, k l * ‖c (m - l)‖ : ℝ) : ℂ))
        ≤ C * CSqZ τ c := by
  classical
  set n : ℕ := Int.natAbs τ with hn
  set K : ℝ := ∑' l : ι → ℤ, k l with hK
  set W : ℝ := ∑' l : ι → ℤ, (wt l) ^ n * k l with hW
  have hKnn : 0 ≤ K := tsum_nonneg hk
  have hWnn : 0 ≤ W :=
    tsum_nonneg fun l => mul_nonneg (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos l)) n) (hk l)
  have hkS : Summable k := by simpa using hkN 0
  have hkSl : Summable (fun l : ι → ℤ => (wt l) ^ n * k l) := hkN n
  refine ⟨(2 : ℝ) ^ n * K * W, by positivity, fun c hc => ?_⟩
  have hc0 : Summable (fun j : ι → ℤ => ‖c j‖ ^ 2) := by simpa using hc 0
  -- the kernel is bounded by its total mass
  have hbd : ∀ l : ι → ℤ, k l ≤ K := fun l => hkS.le_tsum l (fun j _ => hk j)
  have hSsq : ∀ m : ι → ℤ, Summable (fun l => k l * ‖c (m - l)‖ ^ 2) := by
    intro m
    refine Summable.of_nonneg_of_le (fun l => mul_nonneg (hk l) (sq_nonneg _)) (fun l => ?_)
      (((summable_sub_reflect (fun j => ‖c j‖ ^ 2) m).mpr hc0).mul_left K)
    exact mul_le_mul_of_nonneg_right (hbd l) (sq_nonneg _)
  -- Cauchy–Schwarz at each frequency
  have hCS : ∀ m : ι → ℤ,
      (∑' l, k l * ‖c (m - l)‖) ^ 2 ≤ K * ∑' l, k l * ‖c (m - l)‖ ^ 2 := by
    intro m
    have h := Work.Diff.STE.tsum_mul_sq_le k (fun l => ‖c (m - l)‖) hk
      (fun _ => norm_nonneg _) hkS (hSsq m)
    rwa [← hK] at h
  -- the pointwise weighted estimate
  have hptl : ∀ m l : ι → ℤ, (wt m) ^ τ * (k l * ‖c (m - l)‖ ^ 2)
      ≤ 2 ^ n * ((wt l) ^ n * k l * ((wt (m - l)) ^ τ * ‖c (m - l)‖ ^ 2)) := by
    intro m l
    have h1 := wt_zpow_le m l τ
    rw [← hn] at h1
    calc (wt m) ^ τ * (k l * ‖c (m - l)‖ ^ 2)
        ≤ (2 ^ n * ((wt l) ^ n * (wt (m - l)) ^ τ)) * (k l * ‖c (m - l)‖ ^ 2) :=
          mul_le_mul_of_nonneg_right h1 (mul_nonneg (hk l) (sq_nonneg _))
      _ = 2 ^ n * ((wt l) ^ n * k l * ((wt (m - l)) ^ τ * ‖c (m - l)‖ ^ 2)) := by ring_nf
  have hRsum : ∀ m : ι → ℤ, Summable (fun l =>
      2 ^ n * ((wt l) ^ n * k l * ((wt (m - l)) ^ τ * ‖c (m - l)‖ ^ 2))) := by
    intro m
    have hb : ∀ l : ι → ℤ, (wt l) ^ n * k l * ((wt (m - l)) ^ τ * ‖c (m - l)‖ ^ 2)
        ≤ W * ((wt (m - l)) ^ τ * ‖c (m - l)‖ ^ 2) := by
      intro l
      have hle : (wt l) ^ n * k l ≤ W := hkSl.le_tsum l (fun j _ =>
        mul_nonneg (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos j)) n) (hk j))
      exact mul_le_mul_of_nonneg_right hle
        (mul_nonneg (zpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos _)) τ) (sq_nonneg _))
    refine Summable.of_nonneg_of_le
      (fun l => mul_nonneg (by positivity) (mul_nonneg (mul_nonneg
        (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos l)) n) (hk l))
        (mul_nonneg (zpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos _)) τ) (sq_nonneg _))))
      (fun l => ?_)
      (((summable_sub_reflect (fun j => (wt j) ^ τ * ‖c j‖ ^ 2) m).mpr
        (Rapid.summable_zpow c hc τ)).mul_left (2 ^ n * W))
    calc 2 ^ n * ((wt l) ^ n * k l * ((wt (m - l)) ^ τ * ‖c (m - l)‖ ^ 2))
        ≤ 2 ^ n * (W * ((wt (m - l)) ^ τ * ‖c (m - l)‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left (hb l) (by positivity)
      _ = 2 ^ n * W * ((wt (m - l)) ^ τ * ‖c (m - l)‖ ^ 2) := by ring_nf
  have hpt2 : ∀ m : ι → ℤ, (wt m) ^ τ * (∑' l, k l * ‖c (m - l)‖) ^ 2
      ≤ 2 ^ n * K * (∑' l, (wt l) ^ n * k l * ((wt (m - l)) ^ τ * ‖c (m - l)‖ ^ 2)) := by
    intro m
    calc (wt m) ^ τ * (∑' l, k l * ‖c (m - l)‖) ^ 2
        ≤ (wt m) ^ τ * (K * ∑' l, k l * ‖c (m - l)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (hCS m) (zpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos m)) τ)
      _ = K * ((wt m) ^ τ * ∑' l, k l * ‖c (m - l)‖ ^ 2) := by ring_nf
      _ = K * ∑' l, (wt m) ^ τ * (k l * ‖c (m - l)‖ ^ 2) := by rw [tsum_mul_left]
      _ ≤ K * ∑' l, 2 ^ n * ((wt l) ^ n * k l
            * ((wt (m - l)) ^ τ * ‖c (m - l)‖ ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ hKnn
          exact Summable.tsum_le_tsum (fun l => hptl m l) ((hSsq m).mul_left _) (hRsum m)
      _ = 2 ^ n * K * (∑' l, (wt l) ^ n * k l * ((wt (m - l)) ^ τ * ‖c (m - l)‖ ^ 2)) := by
          rw [tsum_mul_left]; ring_nf
  -- discrete Tonelli
  have hbsum : Summable (fun j : ι → ℤ => (wt j) ^ τ * ‖c j‖ ^ 2) := Rapid.summable_zpow c hc τ
  have htot := Work.Diff.STE.summable_conv_nonneg_tsum
    (fun j : ι → ℤ => (wt j) ^ τ * ‖c j‖ ^ 2) (fun l : ι → ℤ => (wt l) ^ n * k l)
    (fun j => mul_nonneg (zpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos j)) τ) (sq_nonneg _))
    (fun l => mul_nonneg (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos l)) n) (hk l))
    hbsum hkSl
  have hbS : Summable (fun m : ι → ℤ =>
      ∑' l, (wt l) ^ n * k l * ((wt (m - l)) ^ τ * ‖c (m - l)‖ ^ 2)) :=
    htot.2.1.congr (fun m => tsum_congr fun l => by ring_nf)
  have hSum : Summable (fun m : ι → ℤ =>
      (wt m) ^ τ * (∑' l, k l * ‖c (m - l)‖) ^ 2) := by
    refine Summable.of_nonneg_of_le
      (fun m => mul_nonneg (zpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos m)) τ)
        (sq_nonneg _)) (fun m => hpt2 m) (hbS.mul_left (2 ^ n * K))
  refine ⟨hSum, ?_⟩
  have hfin : (∑' m : ι → ℤ, (wt m) ^ τ * (∑' l, k l * ‖c (m - l)‖) ^ 2)
      ≤ 2 ^ n * K * W * CSqZ τ c := by
    calc (∑' m : ι → ℤ, (wt m) ^ τ * (∑' l, k l * ‖c (m - l)‖) ^ 2)
        ≤ ∑' m : ι → ℤ, 2 ^ n * K
            * (∑' l, (wt l) ^ n * k l * ((wt (m - l)) ^ τ * ‖c (m - l)‖ ^ 2)) :=
          Summable.tsum_le_tsum (fun m => hpt2 m) hSum (hbS.mul_left _)
      _ = 2 ^ n * K * (∑' m : ι → ℤ,
            ∑' l, (wt l) ^ n * k l * ((wt (m - l)) ^ τ * ‖c (m - l)‖ ^ 2)) := by
          rw [tsum_mul_left]
      _ = 2 ^ n * K * (W * CSqZ τ c) := by
          congr 1
          have hswap : (∑' m : ι → ℤ,
                ∑' l, (wt l) ^ n * k l * ((wt (m - l)) ^ τ * ‖c (m - l)‖ ^ 2))
              = ∑' m : ι → ℤ, ∑' l,
                  ((wt (m - l)) ^ τ * ‖c (m - l)‖ ^ 2) * ((wt l) ^ n * k l) :=
            tsum_congr fun m => tsum_congr fun l => by ring_nf
          rw [hswap, htot.2.2, hW]
          simp only [CSqZ]
          ring_nf
      _ = 2 ^ n * K * W * CSqZ τ c := by ring_nf
  simpa only [CSqZ, Complex.norm_real, Real.norm_eq_abs, sq_abs] using hfin


/-! ## 3. The symbol arithmetic -/

/-- The flat symbol difference, in the form used for the one-step commutator:
`λ(m) − λ(m−l) = Σᵢ (2π)² (lᵢ² + 2 lᵢ (m−l)ᵢ)`. -/
lemma flatLam_sub_decomp (m l : ι → ℤ) :
    lam m - lam (m - l)
      = ∑ i, (2 * Real.pi) ^ 2
          * (((l i : ℤ) : ℝ) ^ 2 + 2 * ((l i : ℤ) : ℝ) * (((m - l) i : ℤ) : ℝ)) := by
  simp only [Work.Diff.STE.B3.SymCalc.flatLam]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.sub_apply]
  push_cast
  ring_nf

/-- The sharp bound for the symbol difference, with a square root:
`|λ(m) − λ(m−l)| ≤ (2π)² (⟨l⟩ + 2 √⟨l⟩ √⟨m−l⟩)`. -/
lemma flatLam_sub_abs_le (m l : ι → ℤ) :
    |lam m - lam (m - l)|
      ≤ (2 * Real.pi) ^ 2 * (wt l + 2 * Real.sqrt (wt l) * Real.sqrt (wt (m - l))) := by
  have hs : ∑ i, (((l i : ℤ) : ℝ)) ^ 2 ≤ wt l := by
    have h := Work.Diff.STE.wt_one_le l
    simp only [Work.Diff.STE.wt] at h ⊢
    linarith
  have ht : ∑ i, ((((m - l) i : ℤ)) : ℝ) ^ 2 ≤ wt (m - l) := by
    have h := Work.Diff.STE.wt_one_le (m - l)
    simp only [Work.Diff.STE.wt] at h ⊢
    linarith
  have hcs : (∑ i, |((l i : ℤ) : ℝ)| * |(((m - l) i : ℤ) : ℝ)|)
      ≤ Real.sqrt (wt l) * Real.sqrt (wt (m - l)) := by
    set S : ℝ := ∑ i, |((l i : ℤ) : ℝ)| * |(((m - l) i : ℤ) : ℝ)| with hS
    have hSnn : 0 ≤ S := by
      rw [hS]; exact Finset.sum_nonneg fun i _ => by positivity
    have hsq : S ^ 2 ≤ wt l * wt (m - l) := by
      have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι)
        (fun i => |((l i : ℤ) : ℝ)|) (fun i => |(((m - l) i : ℤ) : ℝ)|)
      have e1 : (∑ i, |((l i : ℤ) : ℝ)| ^ 2) = ∑ i, (((l i : ℤ) : ℝ)) ^ 2 :=
        Finset.sum_congr rfl fun i _ => by rw [sq_abs]
      have e2 : (∑ i, |(((m - l) i : ℤ) : ℝ)| ^ 2) = ∑ i, ((((m - l) i : ℤ)) : ℝ) ^ 2 :=
        Finset.sum_congr rfl fun i _ => by rw [sq_abs]
      rw [← hS, e1, e2] at h
      exact h.trans (mul_le_mul hs ht (Finset.sum_nonneg fun i _ => sq_nonneg _)
        (le_of_lt (Work.Diff.STE.wt_pos l)))
    have h5 : Real.sqrt (S ^ 2) ≤ Real.sqrt (wt l * wt (m - l)) := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq hSnn, Real.sqrt_mul (le_of_lt (Work.Diff.STE.wt_pos l))] at h5
    exact h5
  rw [flatLam_sub_decomp]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i, |(2 * Real.pi) ^ 2
        * (((l i : ℤ) : ℝ) ^ 2 + 2 * ((l i : ℤ) : ℝ) * (((m - l) i : ℤ) : ℝ))|
      ≤ ∑ i, (2 * Real.pi) ^ 2
          * (((l i : ℤ) : ℝ) ^ 2 + 2 * |((l i : ℤ) : ℝ)| * |(((m - l) i : ℤ) : ℝ)|) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (2 * Real.pi) ^ 2)]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc |((l i : ℤ) : ℝ) ^ 2 + 2 * ((l i : ℤ) : ℝ) * (((m - l) i : ℤ) : ℝ)|
            ≤ |((l i : ℤ) : ℝ) ^ 2| + |2 * ((l i : ℤ) : ℝ) * (((m - l) i : ℤ) : ℝ)| :=
              abs_add_le _ _
          _ = ((l i : ℤ) : ℝ) ^ 2 + 2 * |((l i : ℤ) : ℝ)| * |(((m - l) i : ℤ) : ℝ)| := by
              rw [abs_of_nonneg (sq_nonneg _), abs_mul, abs_mul,
                abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    _ = (2 * Real.pi) ^ 2 * ((∑ i, ((l i : ℤ) : ℝ) ^ 2)
          + 2 * ∑ i, |((l i : ℤ) : ℝ)| * |(((m - l) i : ℤ) : ℝ)|) := by
        have h1 : (∑ i, 2 * |((l i : ℤ) : ℝ)| * |(((m - l) i : ℤ) : ℝ)|)
            = 2 * ∑ i, |((l i : ℤ) : ℝ)| * |(((m - l) i : ℤ) : ℝ)| := by
          have e : (∑ i, 2 * |((l i : ℤ) : ℝ)| * |(((m - l) i : ℤ) : ℝ)|)
              = ∑ i, 2 * (|((l i : ℤ) : ℝ)| * |(((m - l) i : ℤ) : ℝ)|) :=
            Finset.sum_congr rfl fun i _ => by ring_nf
          rw [e, ← Finset.mul_sum]
        rw [← Finset.mul_sum, Finset.sum_add_distrib, h1]
    _ ≤ (2 * Real.pi) ^ 2 * (wt l + 2 * (Real.sqrt (wt l) * Real.sqrt (wt (m - l)))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith
    _ = (2 * Real.pi) ^ 2 * (wt l + 2 * Real.sqrt (wt l) * Real.sqrt (wt (m - l))) := by
        ring_nf

/-- The cruder polynomial form of `flatLam_sub_abs_le`, used for summability. -/
lemma flatLam_sub_abs_le' (m l : ι → ℤ) :
    |lam m - lam (m - l)| ≤ 3 * (2 * Real.pi) ^ 2 * (wt l * wt (m - l)) := by
  refine (flatLam_sub_abs_le m l).trans ?_
  have hl : (1 : ℝ) ≤ wt l := Work.Diff.STE.wt_one_le l
  have hp : (1 : ℝ) ≤ wt (m - l) := Work.Diff.STE.wt_one_le (m - l)
  have hlm : (0 : ℝ) < wt l := Work.Diff.STE.wt_pos l
  have hpm : (0 : ℝ) < wt (m - l) := Work.Diff.STE.wt_pos (m - l)
  have hs : Real.sqrt (wt l) ≤ wt l := by
    have h := Real.sqrt_le_sqrt (show wt l ≤ (wt l) ^ 2 by nlinarith)
    rwa [Real.sqrt_sq (le_of_lt hlm)] at h
  have hsp : Real.sqrt (wt (m - l)) ≤ wt (m - l) := by
    have h := Real.sqrt_le_sqrt (show wt (m - l) ≤ (wt (m - l)) ^ 2 by nlinarith)
    rwa [Real.sqrt_sq (le_of_lt hpm)] at h
  have hsqrt : Real.sqrt (wt l) * Real.sqrt (wt (m - l)) ≤ wt l * wt (m - l) :=
    mul_le_mul hs hsp (Real.sqrt_nonneg _) (by linarith)
  have hprod : (0 : ℝ) ≤ wt l * wt (m - l) := le_of_lt (mul_pos hlm hpm)
  have h1 : wt l ≤ wt l * wt (m - l) := by nlinarith
  have h2π : (0 : ℝ) ≤ (2 * Real.pi) ^ 2 := by positivity
  nlinarith [hsqrt, h1, h2π, hprod]

/-- The polynomial growth bound for the `k`-th power of the symbol. -/
lemma flatLam_pow_sub_abs_le (k : ℕ) (m l : ι → ℤ) :
    |(lam m) ^ k - (lam (m - l)) ^ k|
      ≤ (4 * Real.pi ^ 2) ^ k * 2 ^ (k + 1) * (wt m) ^ k * (wt l) ^ k := by
  have hlam : ∀ x : ι → ℤ, (lam x) ^ k ≤ (4 * Real.pi ^ 2) ^ k * (wt x) ^ k := by
    intro x
    calc (lam x) ^ k ≤ ((4 * Real.pi ^ 2) * wt x) ^ k :=
          pow_le_pow_left₀ (Work.Diff.STE.B3.SymCalcStep6.flatLam_nonneg x)
            (Work.Diff.STE.B3.SymCalcStep6.flatLam_le_wt x) k
      _ = (4 * Real.pi ^ 2) ^ k * (wt x) ^ k := by rw [mul_pow]
  have habs : |(lam m) ^ k - (lam (m - l)) ^ k| ≤ (lam m) ^ k + (lam (m - l)) ^ k := by
    rcases le_total ((lam m) ^ k) ((lam (m - l)) ^ k) with h | h
    · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr h)]
      linarith [pow_nonneg (Work.Diff.STE.B3.SymCalcStep6.flatLam_nonneg m) k]
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]
      linarith [pow_nonneg (Work.Diff.STE.B3.SymCalcStep6.flatLam_nonneg (m - l)) k]
  have hwm : (0 : ℝ) ≤ (wt m) ^ k := pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos m)) k
  have hwl1 : (1 : ℝ) ≤ (wt l) ^ k := one_le_pow₀ (Work.Diff.STE.wt_one_le l)
  have hcombo : (wt m) ^ k + (wt (m - l)) ^ k
      ≤ 2 ^ (k + 1) * ((wt m) ^ k * (wt l) ^ k) := by
    have h1 : (wt m) ^ k ≤ (wt m) ^ k * (wt l) ^ k := le_mul_of_one_le_right hwm hwl1
    have h2 : (wt (m - l)) ^ k ≤ 2 ^ k * ((wt m) ^ k * (wt l) ^ k) := by
      calc (wt (m - l)) ^ k ≤ 2 ^ k * (wt m) ^ k * (wt l) ^ k := wt_pow_le_right m l k
        _ = 2 ^ k * ((wt m) ^ k * (wt l) ^ k) := by ring_nf
    have h3 : (2 : ℝ) ^ k + 1 ≤ 2 ^ (k + 1) := by
      rw [pow_succ]
      linarith [show (1 : ℝ) ≤ 2 ^ k from one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)]
    calc (wt m) ^ k + (wt (m - l)) ^ k
        ≤ (wt m) ^ k * (wt l) ^ k + 2 ^ k * ((wt m) ^ k * (wt l) ^ k) := add_le_add h1 h2
      _ = (2 ^ k + 1) * ((wt m) ^ k * (wt l) ^ k) := by ring_nf
      _ ≤ 2 ^ (k + 1) * ((wt m) ^ k * (wt l) ^ k) :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
  refine habs.trans ?_
  calc (lam m) ^ k + (lam (m - l)) ^ k
      ≤ (4 * Real.pi ^ 2) ^ k * (wt m) ^ k + (4 * Real.pi ^ 2) ^ k * (wt (m - l)) ^ k :=
        add_le_add (hlam m) (hlam (m - l))
    _ = (4 * Real.pi ^ 2) ^ k * ((wt m) ^ k + (wt (m - l)) ^ k) := by ring_nf
    _ ≤ (4 * Real.pi ^ 2) ^ k * (2 ^ (k + 1) * ((wt m) ^ k * (wt l) ^ k)) :=
        mul_le_mul_of_nonneg_left hcombo (by positivity)
    _ = (4 * Real.pi ^ 2) ^ k * 2 ^ (k + 1) * (wt m) ^ k * (wt l) ^ k := by ring_nf

/-! ## 4. The `CSqZ` calculus -/

lemma CSqZ_smul (r : ℝ) (τ : ℤ) (F : (ι → ℤ) → ℂ) :
    CSqZ τ (fun m => ((r : ℝ) : ℂ) * F m) = r ^ 2 * CSqZ τ F := by
  simp only [CSqZ]
  rw [← tsum_mul_left]
  exact tsum_congr fun m => by
    rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    ring_nf

lemma CSqZ_real (τ : ℤ) (f : (ι → ℤ) → ℝ) :
    CSqZ τ (fun m => ((f m : ℝ) : ℂ)) = ∑' m, (wt m) ^ τ * f m ^ 2 := by
  simp only [CSqZ]
  exact tsum_congr fun m => by rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

lemma CSqZ_add_le (τ : ℤ) {F G : (ι → ℤ) → ℂ}
    (hF : Summable (fun m => (wt m) ^ τ * ‖F m‖ ^ 2))
    (hG : Summable (fun m => (wt m) ^ τ * ‖G m‖ ^ 2)) :
    CSqZ τ (F + G) ≤ 2 * (CSqZ τ F + CSqZ τ G) := by
  have hpt : ∀ m : ι → ℤ, (wt m) ^ τ * ‖(F + G) m‖ ^ 2
      ≤ 2 * ((wt m) ^ τ * ‖F m‖ ^ 2 + (wt m) ^ τ * ‖G m‖ ^ 2) := by
    intro m
    have h1 : ‖(F + G) m‖ ≤ ‖F m‖ + ‖G m‖ := norm_add_le _ _
    have h2 : (‖F m‖ + ‖G m‖) ^ 2 ≤ 2 * ‖F m‖ ^ 2 + 2 * ‖G m‖ ^ 2 := by
      nlinarith [sq_nonneg (‖F m‖ - ‖G m‖)]
    calc (wt m) ^ τ * ‖(F + G) m‖ ^ 2
        ≤ (wt m) ^ τ * (‖F m‖ + ‖G m‖) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h1 2)
            (zpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos m)) τ)
      _ ≤ (wt m) ^ τ * (2 * ‖F m‖ ^ 2 + 2 * ‖G m‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (zpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos m)) τ)
      _ = 2 * ((wt m) ^ τ * ‖F m‖ ^ 2 + (wt m) ^ τ * ‖G m‖ ^ 2) := by ring_nf
  have hsum : Summable (fun m => (wt m) ^ τ * ‖(F + G) m‖ ^ 2) :=
    Summable.of_nonneg_of_le
      (fun m => mul_nonneg (zpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos m)) τ) (sq_nonneg _))
      hpt ((hF.add hG).mul_left 2)
  simp only [CSqZ]
  calc ∑' m, (wt m) ^ τ * ‖(F + G) m‖ ^ 2
      ≤ ∑' m, 2 * ((wt m) ^ τ * ‖F m‖ ^ 2 + (wt m) ^ τ * ‖G m‖ ^ 2) :=
        Summable.tsum_le_tsum hpt hsum ((hF.add hG).mul_left 2)
    _ = 2 * ((∑' m, (wt m) ^ τ * ‖F m‖ ^ 2) + ∑' m, (wt m) ^ τ * ‖G m‖ ^ 2) := by
        rw [tsum_mul_left, Summable.tsum_add hF hG]

/-- Summability of the weighted `ℓ²` series of a sum, from summability of the two summands. -/
lemma summable_CSqZ_add {τ : ℤ} {F G : (ι → ℤ) → ℂ}
    (hF : Summable (fun m => (wt m) ^ τ * ‖F m‖ ^ 2))
    (hG : Summable (fun m => (wt m) ^ τ * ‖G m‖ ^ 2)) :
    Summable (fun m => (wt m) ^ τ * ‖(F + G) m‖ ^ 2) := by
  refine Summable.of_nonneg_of_le
    (fun m => mul_nonneg (zpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos m)) τ) (sq_nonneg _))
    (fun m => ?_) ((hF.add hG).mul_left 2)
  have h1 : ‖(F + G) m‖ ≤ ‖F m‖ + ‖G m‖ := norm_add_le _ _
  have h2 : (‖F m‖ + ‖G m‖) ^ 2 ≤ 2 * ‖F m‖ ^ 2 + 2 * ‖G m‖ ^ 2 := by
    nlinarith [sq_nonneg (‖F m‖ - ‖G m‖)]
  calc (wt m) ^ τ * ‖(F + G) m‖ ^ 2
      ≤ (wt m) ^ τ * (‖F m‖ + ‖G m‖) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h1 2)
          (zpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos m)) τ)
    _ ≤ (wt m) ^ τ * (2 * ‖F m‖ ^ 2 + 2 * ‖G m‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (zpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos m)) τ)
    _ = 2 * ((wt m) ^ τ * ‖F m‖ ^ 2 + (wt m) ^ τ * ‖G m‖ ^ 2) := by ring_nf

lemma CSqZ_le_of_norm_le {F G : (ι → ℤ) → ℂ} (h : ∀ m, ‖F m‖ ≤ ‖G m‖) (τ : ℤ)
    (hG : Summable (fun m => (wt m) ^ τ * ‖G m‖ ^ 2)) : CSqZ τ F ≤ CSqZ τ G := by
  have hpt : ∀ m : ι → ℤ, (wt m) ^ τ * ‖F m‖ ^ 2 ≤ (wt m) ^ τ * ‖G m‖ ^ 2 := fun m =>
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (h m) 2)
      (zpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos m)) τ)
  have hF : Summable (fun m => (wt m) ^ τ * ‖F m‖ ^ 2) :=
    Summable.of_nonneg_of_le
      (fun m => mul_nonneg (zpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos m)) τ) (sq_nonneg _))
      hpt hG
  simp only [CSqZ]
  exact Summable.tsum_le_tsum hpt hF hG

/-! ## 5. The commutator families -/

/-- The coefficient family of the one-step commutator `[Λ, M_b] c`. -/
def stepFam (β c : (ι → ℤ) → ℂ) : (ι → ℤ) → ℂ :=
  fun m => ∑' l, β l * (lamC m - lamC (m - l)) * c (m - l)

/-- The coefficient family of the `k`-step commutator `[Λ^k, M_b] c`. -/
def bigFam (k : ℕ) (β c : (ι → ℤ) → ℂ) : (ι → ℤ) → ℂ :=
  fun m => ∑' l, β l * (lamC m ^ k - lamC (m - l) ^ k) * c (m - l)

/-- The multiplier family `Λ^a c`. -/
def multFam (a : ℕ) (c : (ι → ℤ) → ℂ) : (ι → ℤ) → ℂ := fun m => lamC m ^ a * c m

lemma sqrt_le_wt (x : ι → ℤ) : Real.sqrt (wt x) ≤ wt x := by
  have h := Real.sqrt_le_sqrt (show wt x ≤ (wt x) ^ 2 by nlinarith [Work.Diff.STE.wt_one_le x])
  rwa [Real.sqrt_sq (le_of_lt (Work.Diff.STE.wt_pos x))] at h

lemma multFam_norm (a : ℕ) (c : (ι → ℤ) → ℂ) (m : ι → ℤ) :
    ‖multFam a c m‖ ≤ (4 * Real.pi ^ 2) ^ a * (wt m) ^ a * ‖c m‖ := by
  rw [multFam, norm_mul, norm_pow, lamC, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Work.Diff.STE.B3.SymCalcStep6.flatLam_nonneg m)]
  calc (Work.Diff.STE.B3.SymCalc.flatLam m) ^ a * ‖c m‖
      ≤ ((4 * Real.pi ^ 2) * wt m) ^ a * ‖c m‖ :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (Work.Diff.STE.B3.SymCalcStep6.flatLam_nonneg m)
            (Work.Diff.STE.B3.SymCalcStep6.flatLam_le_wt m) a) (norm_nonneg _)
    _ = (4 * Real.pi ^ 2) ^ a * (wt m) ^ a * ‖c m‖ := by rw [mul_pow]

lemma mult_sq_le (a : ℕ) (τ : ℤ) (c : (ι → ℤ) → ℂ) (m : ι → ℤ) :
    (wt m) ^ τ * ‖multFam a c m‖ ^ 2
      ≤ (4 * Real.pi ^ 2) ^ (2 * a) * ((wt m) ^ (τ + 2 * (a : ℤ)) * ‖c m‖ ^ 2) := by
  have h2 : ‖multFam a c m‖ ^ 2
      ≤ ((4 * Real.pi ^ 2) ^ a * (wt m) ^ a) ^ 2 * ‖c m‖ ^ 2 := by
    refine (pow_le_pow_left₀ (norm_nonneg _) (multFam_norm a c m) 2).trans (le_of_eq ?_)
    rw [mul_pow]
  have e1 : ((4 * Real.pi ^ 2) ^ a) ^ 2 = (4 * Real.pi ^ 2) ^ (2 * a) := by
    rw [← pow_mul, Nat.mul_comm]
  have e2 : ((wt m) ^ a) ^ 2 = (wt m) ^ (2 * a) := by rw [← pow_mul, Nat.mul_comm]
  have e3 : (wt m) ^ τ * (wt m) ^ (2 * a) = (wt m) ^ (τ + 2 * (a : ℤ)) :=
    Work.Diff.STE.B3.SymCalcStep8.wt_zpow_mul_nat m τ a
  calc (wt m) ^ τ * ‖multFam a c m‖ ^ 2
      ≤ (wt m) ^ τ * (((4 * Real.pi ^ 2) ^ a * (wt m) ^ a) ^ 2 * ‖c m‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (zpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos m)) τ)
    _ = (4 * Real.pi ^ 2) ^ (2 * a) * ((wt m) ^ (τ + 2 * (a : ℤ)) * ‖c m‖ ^ 2) := by
        rw [mul_pow, e1, e2]
        rw [show (wt m) ^ τ * ((4 * Real.pi ^ 2) ^ (2 * a) * (wt m) ^ (2 * a) * ‖c m‖ ^ 2)
            = (4 * Real.pi ^ 2) ^ (2 * a) * ((wt m) ^ τ * (wt m) ^ (2 * a)) * ‖c m‖ ^ 2
            from by ring]
        rw [e3]
        ring_nf

lemma Rapid_sqrt (c : (ι → ℤ) → ℂ) (hc : Rapid c) :
    Rapid (fun j => ((Real.sqrt (wt j) : ℝ) : ℂ) * c j) := by
  intro N
  refine (hc (N + 1)).congr (fun m => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    mul_pow, Real.sq_sqrt (le_of_lt (Work.Diff.STE.wt_pos m)), pow_succ]
  ring_nf

lemma Rapid_mult (a : ℕ) (c : (ι → ℤ) → ℂ) (hc : Rapid c) : Rapid (multFam a c) := by
  intro N
  have hcast : ((N : ℤ) + 2 * (a : ℤ)) = ((N + 2 * a : ℕ) : ℤ) := by push_cast; ring
  refine Summable.of_nonneg_of_le
    (fun m => mul_nonneg (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos m)) N) (sq_nonneg _))
    (fun m => ?_) ((hc (N + 2 * a)).mul_left ((4 * Real.pi ^ 2) ^ (2 * a)))
  have h := mult_sq_le a (N : ℤ) c m
  rw [hcast] at h
  exact h

/-! ## 6. The one-step estimate -/

lemma summable_k1 (β c : (ι → ℤ) → ℂ) (hβ : RapidL1 β) (hc : Rapid c) (m : ι → ℤ) :
    Summable (fun l => (‖β l‖ * wt l) * ‖c (m - l)‖) := by
  refine Summable.of_nonneg_of_le
    (fun l => mul_nonneg (mul_nonneg (norm_nonneg _) (le_of_lt (Work.Diff.STE.wt_pos l)))
      (norm_nonneg _)) (fun l => ?_) (summable_conv_rapid β c hβ hc m 1 0)
  exact le_of_eq (by ring_nf)

lemma summable_k1' (β c : (ι → ℤ) → ℂ) (hβ : RapidL1 β) (hc : Rapid c) (m : ι → ℤ) :
    Summable (fun l => (‖β l‖ * wt l) * (wt (m - l) * ‖c (m - l)‖)) := by
  refine Summable.of_nonneg_of_le
    (fun l => mul_nonneg (mul_nonneg (norm_nonneg _) (le_of_lt (Work.Diff.STE.wt_pos l)))
      (mul_nonneg (le_of_lt (Work.Diff.STE.wt_pos _)) (norm_nonneg _))) (fun l => ?_)
    (summable_conv_rapid β c hβ hc m 1 1)
  exact le_of_eq (by ring_nf)

lemma summable_k2 (β c : (ι → ℤ) → ℂ) (hβ : RapidL1 β) (hc : Rapid c) (m : ι → ℤ) :
    Summable (fun l =>
      (‖β l‖ * Real.sqrt (wt l)) * (Real.sqrt (wt (m - l)) * ‖c (m - l)‖)) := by
  refine Summable.of_nonneg_of_le
    (fun l => mul_nonneg (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))) (fun l => ?_)
    (summable_k1' β c hβ hc m)
  have h1 : Real.sqrt (wt l) ≤ wt l := sqrt_le_wt l
  have h2 : Real.sqrt (wt (m - l)) ≤ wt (m - l) := sqrt_le_wt (m - l)
  exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (norm_nonneg _))
    (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    (mul_nonneg (norm_nonneg _) (le_of_lt (Work.Diff.STE.wt_pos l)))

theorem step_CSqZ_le (β : (ι → ℤ) → ℂ) (hβ : RapidL1 β) (τ : ℤ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : (ι → ℤ) → ℂ, Rapid c →
      Summable (fun m => (wt m) ^ τ * ‖stepFam β c m‖ ^ 2) ∧
      CSqZ τ (stepFam β c) ≤ C * CSqZ (τ + 1) c := by
  classical
  have hβ1 : ∀ N : ℕ, Summable (fun l : ι → ℤ => (wt l) ^ N * (‖β l‖ * wt l)) := by
    intro N
    refine Summable.of_nonneg_of_le
      (fun l => mul_nonneg (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos l)) N)
        (mul_nonneg (norm_nonneg _) (le_of_lt (Work.Diff.STE.wt_pos l))))
      (fun l => ?_) (hβ (N + 1))
    exact le_of_eq (by ring_nf)
  have hβ2 : ∀ N : ℕ, Summable (fun l : ι → ℤ => (wt l) ^ N * (‖β l‖ * Real.sqrt (wt l))) := by
    intro N
    refine Summable.of_nonneg_of_le
      (fun l => mul_nonneg (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos l)) N)
        (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)))
      (fun l => ?_) (hβ (N + 1))
    have hs : Real.sqrt (wt l) ≤ wt l := sqrt_le_wt l
    calc (wt l) ^ N * (‖β l‖ * Real.sqrt (wt l)) ≤ (wt l) ^ N * (‖β l‖ * wt l) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs (norm_nonneg _))
            (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos l)) N)
      _ = (wt l) ^ (N + 1) * ‖β l‖ := by ring_nf
  obtain ⟨C1, hC1, hC1b⟩ := kernel_abs_CSqZ_le (fun l => ‖β l‖ * wt l)
    (fun l => mul_nonneg (norm_nonneg _) (le_of_lt (Work.Diff.STE.wt_pos l))) hβ1 τ
  obtain ⟨C2, hC2, hC2b⟩ := kernel_abs_CSqZ_le (fun l => ‖β l‖ * Real.sqrt (wt l))
    (fun l => mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) hβ2 τ
  refine ⟨(2 * Real.pi) ^ 4 * 2 * (C1 + 4 * C2), by positivity, fun c hc => ?_⟩
  set d : (ι → ℤ) → ℂ := fun j => ((Real.sqrt (wt j) : ℝ) : ℂ) * c j with hd
  have hdR : Rapid d := Rapid_sqrt c hc
  set A1 : (ι → ℤ) → ℝ := fun m => ∑' l, (‖β l‖ * wt l) * ‖c (m - l)‖ with hA1
  set A2 : (ι → ℤ) → ℝ := fun m => ∑' l, (‖β l‖ * Real.sqrt (wt l)) * ‖d (m - l)‖ with hA2
  have hA1S : Summable (fun m => (wt m) ^ τ * A1 m ^ 2) := by
    simpa only [hA1] using (hC1b c hc).1
  have hA2S : Summable (fun m => (wt m) ^ τ * A2 m ^ 2) := by
    simpa only [hA2] using (hC2b d hdR).1
  have hCS1 : CSqZ τ (fun m => ((A1 m : ℝ) : ℂ)) ≤ C1 * CSqZ τ c := by
    simpa only [hA1] using (hC1b c hc).2
  have hCS2 : CSqZ τ (fun m => ((A2 m : ℝ) : ℂ)) ≤ C2 * CSqZ τ d := by
    simpa only [hA2] using (hC2b d hdR).2
  have hA2val : CSqZ τ d = CSqZ (τ + 1) c := by
    simp only [CSqZ]
    refine tsum_congr fun m => ?_
    rw [hd, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      mul_pow, Real.sq_sqrt (le_of_lt (Work.Diff.STE.wt_pos m)),
      zpow_add₀ (ne_of_gt (Work.Diff.STE.wt_pos m)), zpow_one]
    ring_nf
  have hmaj : ∀ m : ι → ℤ, Summable (fun l => (2 * Real.pi) ^ 2
      * ((‖β l‖ * wt l) * ‖c (m - l)‖
        + 2 * ((‖β l‖ * Real.sqrt (wt l)) * (Real.sqrt (wt (m - l)) * ‖c (m - l)‖)))) := by
    intro m
    exact Summable.mul_left _ (Summable.add (summable_k1 β c hβ hc m)
      ((summable_k2 β c hβ hc m).mul_left 2))
  have hpt : ∀ m l : ι → ℤ, ‖β l * (lamC m - lamC (m - l)) * c (m - l)‖
      ≤ (2 * Real.pi) ^ 2 * ((‖β l‖ * wt l) * ‖c (m - l)‖
        + 2 * ((‖β l‖ * Real.sqrt (wt l)) * (Real.sqrt (wt (m - l)) * ‖c (m - l)‖))) := by
    intro m l
    have h := flatLam_sub_abs_le m l
    rw [lamC, lamC, ← Complex.ofReal_sub, norm_mul, norm_mul,
      Complex.norm_real, Real.norm_eq_abs]
    calc ‖β l‖ * |(Work.Diff.STE.B3.SymCalc.flatLam m : ℝ)
            - (Work.Diff.STE.B3.SymCalc.flatLam (m - l) : ℝ)| * ‖c (m - l)‖
        ≤ ‖β l‖ * ((2 * Real.pi) ^ 2 * (wt l + 2 * Real.sqrt (wt l) * Real.sqrt (wt (m - l))))
            * ‖c (m - l)‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left h (norm_nonneg _)) (norm_nonneg _)
      _ = (2 * Real.pi) ^ 2 * ((‖β l‖ * wt l) * ‖c (m - l)‖
          + 2 * ((‖β l‖ * Real.sqrt (wt l)) * (Real.sqrt (wt (m - l)) * ‖c (m - l)‖))) := by
          ring_nf
  have hnorm : ∀ m, ‖stepFam β c m‖ ≤ (2 * Real.pi) ^ 2 * (A1 m + 2 * A2 m) := by
    intro m
    have hsuml : Summable (fun l => ‖β l * (lamC m - lamC (m - l)) * c (m - l)‖) :=
      Summable.of_nonneg_of_le (fun l => norm_nonneg _) (fun l => hpt m l) (hmaj m)
    have hA1eq : A1 m = ∑' l, (‖β l‖ * wt l) * ‖c (m - l)‖ := by rw [hA1]
    have hA2eq : A2 m = ∑' l, (‖β l‖ * Real.sqrt (wt l)) * ‖d (m - l)‖ := by rw [hA2]
    have hA2inner : (∑' l, (‖β l‖ * Real.sqrt (wt l))
          * (Real.sqrt (wt (m - l)) * ‖c (m - l)‖)) = A2 m := by
      rw [hA2]
      exact tsum_congr fun l => by
        rw [hd, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg _)]
    calc ‖stepFam β c m‖ = ‖∑' l, β l * (lamC m - lamC (m - l)) * c (m - l)‖ := rfl
      _ ≤ ∑' l, ‖β l * (lamC m - lamC (m - l)) * c (m - l)‖ := norm_tsum_le_tsum_norm hsuml
      _ ≤ ∑' l, (2 * Real.pi) ^ 2 * ((‖β l‖ * wt l) * ‖c (m - l)‖
            + 2 * ((‖β l‖ * Real.sqrt (wt l)) * (Real.sqrt (wt (m - l)) * ‖c (m - l)‖))) :=
          Summable.tsum_le_tsum (fun l => hpt m l) hsuml (hmaj m)
      _ = (2 * Real.pi) ^ 2 * (A1 m + 2 * A2 m) := by
          rw [tsum_mul_left]
          congr 1
          rw [Summable.tsum_add (summable_k1 β c hβ hc m)
            ((summable_k2 β c hβ hc m).mul_left 2), tsum_mul_left, hA1eq, hA2inner]
  have hA1nn : ∀ m : ι → ℤ, 0 ≤ A1 m := fun m => by
    rw [hA1]
    exact tsum_nonneg fun l => mul_nonneg
      (mul_nonneg (norm_nonneg _) (le_of_lt (Work.Diff.STE.wt_pos l))) (norm_nonneg _)
  have hA2nn : ∀ m : ι → ℤ, 0 ≤ A2 m := fun m => by
    rw [hA2]
    exact tsum_nonneg fun l => mul_nonneg
      (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) (norm_nonneg _)
  have hmajSum : Summable (fun m => (wt m) ^ τ * ‖(((2 * Real.pi) ^ 2
      * (A1 m + 2 * A2 m) : ℝ) : ℂ)‖ ^ 2) := by
    refine Summable.of_nonneg_of_le
      (fun m => mul_nonneg (zpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos m)) τ) (sq_nonneg _))
      (fun m => ?_)
      (((hA1S.mul_left 2).add (hA2S.mul_left 8)).mul_left ((2 * Real.pi) ^ 4))
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have h1 : (A1 m + 2 * A2 m) ^ 2 ≤ 2 * A1 m ^ 2 + 8 * A2 m ^ 2 := by
      nlinarith [sq_nonneg (A1 m - 2 * A2 m)]
    calc (wt m) ^ τ * ((2 * Real.pi) ^ 2 * (A1 m + 2 * A2 m)) ^ 2
        = ((2 * Real.pi) ^ 4) * ((wt m) ^ τ * (A1 m + 2 * A2 m) ^ 2) := by ring_nf
      _ ≤ ((2 * Real.pi) ^ 4) * ((wt m) ^ τ * (2 * A1 m ^ 2 + 8 * A2 m ^ 2)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left h1 (zpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos m)) τ))
            (by positivity)
      _ = ((2 * Real.pi) ^ 4) * (2 * ((wt m) ^ τ * A1 m ^ 2)
            + 8 * ((wt m) ^ τ * A2 m ^ 2)) := by ring_nf
  have hstepm : Summable (fun m => (wt m) ^ τ * ‖stepFam β c m‖ ^ 2) :=
    Summable.of_nonneg_of_le
      (fun m => mul_nonneg (zpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos m)) τ) (sq_nonneg _))
      (fun m => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hnorm m) 2)
        (zpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos m)) τ))
      (by
        refine Summable.of_nonneg_of_le
          (fun m => mul_nonneg (zpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos m)) τ) (sq_nonneg _))
          (fun m => ?_)
          (((hA1S.mul_left 2).add (hA2S.mul_left 8)).mul_left ((2 * Real.pi) ^ 4))
        have h1 : (A1 m + 2 * A2 m) ^ 2 ≤ 2 * A1 m ^ 2 + 8 * A2 m ^ 2 := by
          nlinarith [sq_nonneg (A1 m - 2 * A2 m)]
        calc (wt m) ^ τ * (((2 * Real.pi) ^ 2 * (A1 m + 2 * A2 m)) ^ 2)
            = ((2 * Real.pi) ^ 4) * ((wt m) ^ τ * (A1 m + 2 * A2 m) ^ 2) := by ring_nf
          _ ≤ ((2 * Real.pi) ^ 4) * ((wt m) ^ τ * (2 * A1 m ^ 2 + 8 * A2 m ^ 2)) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left h1
                  (zpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos m)) τ))
                (by positivity)
          _ = ((2 * Real.pi) ^ 4) * (2 * ((wt m) ^ τ * A1 m ^ 2)
                + 8 * ((wt m) ^ τ * A2 m ^ 2)) := by ring_nf)
  refine ⟨hstepm, ?_⟩
  have hCSa : CSqZ τ (fun m => ((A1 m + 2 * A2 m : ℝ) : ℂ))
      ≤ 2 * (CSqZ τ (fun m => ((A1 m : ℝ) : ℂ))
        + CSqZ τ (fun m => ((2 * A2 m : ℝ) : ℂ))) := by
    have heq : (fun m => ((A1 m + 2 * A2 m : ℝ) : ℂ))
        = (fun m => ((A1 m : ℝ) : ℂ)) + (fun m => ((2 * A2 m : ℝ) : ℂ)) := by
      funext m; simp only [Pi.add_apply, Complex.ofReal_add]
    rw [heq]
    refine CSqZ_add_le τ ?_ ?_
    · simpa only [CSqZ_real, Complex.norm_real, Real.norm_eq_abs, sq_abs] using hA1S
    · refine (hA2S.mul_left 4).congr (fun m => ?_)
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow]
      ring
  have hC1nn : 0 ≤ C1 := hC1
  have hC2nn : 0 ≤ C2 := hC2
  have hcm : CSqZ τ c ≤ CSqZ (τ + 1) c :=
    CSqZ_mono (by omega) c (Rapid.summable_zpow c hc (τ + 1))
  have hscal : (fun m => (((2 * Real.pi) ^ 2 * (A1 m + 2 * A2 m) : ℝ) : ℂ))
      = fun m => ((((2 * Real.pi) ^ 2 : ℝ)) : ℂ) * ((A1 m + 2 * A2 m : ℝ) : ℂ) :=
    funext fun m => by rw [Complex.ofReal_mul]
  have hscal2 : (fun m => ((2 * A2 m : ℝ) : ℂ))
      = fun m => (((2 : ℝ)) : ℂ) * ((A2 m : ℝ) : ℂ) :=
    funext fun m => by rw [Complex.ofReal_mul, Complex.ofReal_ofNat]
  calc CSqZ τ (stepFam β c)
      ≤ CSqZ τ (fun m => (((2 * Real.pi) ^ 2 * (A1 m + 2 * A2 m) : ℝ) : ℂ)) :=
        CSqZ_le_of_norm_le (fun m => by
          rw [Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (mul_nonneg (by positivity) (by linarith [hA1nn m, hA2nn m]))]
          exact hnorm m) τ hmajSum
    _ = ((2 * Real.pi) ^ 2) ^ 2 * CSqZ τ (fun m => ((A1 m + 2 * A2 m : ℝ) : ℂ)) := by
        rw [hscal, CSqZ_smul]
    _ ≤ ((2 * Real.pi) ^ 2) ^ 2 * (2 * (CSqZ τ (fun m => ((A1 m : ℝ) : ℂ))
          + CSqZ τ (fun m => ((2 * A2 m : ℝ) : ℂ)))) :=
        mul_le_mul_of_nonneg_left hCSa (by positivity)
    _ = ((2 * Real.pi) ^ 2) ^ 2 * 2 * (CSqZ τ (fun m => ((A1 m : ℝ) : ℂ))
          + 4 * CSqZ τ (fun m => ((A2 m : ℝ) : ℂ))) := by
        rw [hscal2, CSqZ_smul]
        ring_nf
    _ ≤ ((2 * Real.pi) ^ 2) ^ 2 * 2 * (C1 * CSqZ (τ + 1) c + 4 * (C2 * CSqZ (τ + 1) c)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine add_le_add (le_trans hCS1 (mul_le_mul_of_nonneg_left hcm hC1nn)) ?_
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        refine le_trans hCS2 ?_
        rw [hA2val]
    _ = ((2 * Real.pi) ^ 4 * 2 * (C1 + 4 * C2)) * CSqZ (τ + 1) c := by ring_nf

/-! ## 7. The multiplier gain -/

theorem mult_CSqZ_le (a : ℕ) (τ : ℤ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : (ι → ℤ) → ℂ, Rapid c →
      CSqZ τ (multFam a c) ≤ C * CSqZ (τ + 2 * (a : ℤ)) c := by
  refine ⟨(4 * Real.pi ^ 2) ^ (2 * a), by positivity, fun c hc => ?_⟩
  have hsumR : Summable (fun m => (4 * Real.pi ^ 2) ^ (2 * a)
      * ((wt m) ^ (τ + 2 * (a : ℤ)) * ‖c m‖ ^ 2)) :=
    (Rapid.summable_zpow c hc (τ + 2 * (a : ℤ))).mul_left _
  have hL : Summable (fun m => (wt m) ^ τ * ‖multFam a c m‖ ^ 2) :=
    Summable.of_nonneg_of_le
      (fun m => mul_nonneg (zpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos m)) τ) (sq_nonneg _))
      (fun m => mult_sq_le a τ c m) hsumR
  simp only [CSqZ]
  calc ∑' m, (wt m) ^ τ * ‖multFam a c m‖ ^ 2
      ≤ ∑' m, (4 * Real.pi ^ 2) ^ (2 * a) * ((wt m) ^ (τ + 2 * (a : ℤ)) * ‖c m‖ ^ 2) :=
        Summable.tsum_le_tsum (fun m => mult_sq_le a τ c m) hL hsumR
    _ = (4 * Real.pi ^ 2) ^ (2 * a)
          * ∑' m, (wt m) ^ (τ + 2 * (a : ℤ)) * ‖c m‖ ^ 2 := tsum_mul_left

/-! ## 8. The `k`-step estimate by telescoping -/

lemma summable_stepFam (β c : (ι → ℤ) → ℂ) (hβ : RapidL1 β) (hc : Rapid c)
    (m : ι → ℤ) :
    Summable (fun l => β l * (lamC m - lamC (m - l)) * c (m - l)) := by
  refine Summable.of_norm_bounded
    ((summable_conv_rapid β c hβ hc m 1 1).mul_left (3 * (2 * Real.pi) ^ 2))
    (fun l => ?_)
  have h := flatLam_sub_abs_le' m l
  rw [norm_mul, norm_mul, norm_lamC_sub]
  calc ‖β l‖ * |lam m - lam (m - l)| * ‖c (m - l)‖
      ≤ ‖β l‖ * (3 * (2 * Real.pi) ^ 2 * (wt l * wt (m - l))) * ‖c (m - l)‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left h (norm_nonneg _)) (norm_nonneg _)
    _ = 3 * (2 * Real.pi) ^ 2
          * ((wt l) ^ 1 * (wt (m - l)) ^ 1 * ‖β l‖ * ‖c (m - l)‖) := by ring_nf

lemma summable_bigFam (k : ℕ) (β c : (ι → ℤ) → ℂ) (hβ : RapidL1 β) (hc : Rapid c)
    (m : ι → ℤ) :
    Summable (fun l => β l * (lamC m ^ k - lamC (m - l) ^ k) * c (m - l)) := by
  refine Summable.of_norm_bounded
    ((summable_conv_rapid β c hβ hc m k 0).mul_left
      ((4 * Real.pi ^ 2) ^ k * 2 ^ (k + 1) * (wt m) ^ k)) (fun l => ?_)
  have h := flatLam_pow_sub_abs_le k m l
  rw [norm_mul, norm_mul]
  rw [show ‖lamC m ^ k - lamC (m - l) ^ k‖ = |(lam m) ^ k - (lam (m - l)) ^ k|
    from norm_lamC_pow_sub k m l]
  calc ‖β l‖ * |(lam m) ^ k - (lam (m - l)) ^ k| * ‖c (m - l)‖ 
      ≤ ‖β l‖ * ((4 * Real.pi ^ 2) ^ k * 2 ^ (k + 1) * (wt m) ^ k * (wt l) ^ k)
          * ‖c (m - l)‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left h (norm_nonneg _)) (norm_nonneg _)
    _ = (4 * Real.pi ^ 2) ^ k * 2 ^ (k + 1) * (wt m) ^ k
          * ((wt l) ^ k * (wt (m - l)) ^ 0 * ‖β l‖ * ‖c (m - l)‖) := by ring_nf

/-- Summability of the weighted `ℓ²` series of `Λ^a c`, from that of `c` at the shifted exponent. -/
lemma summable_multFam (a : ℕ) (τ : ℤ) {c : (ι → ℤ) → ℂ}
    (h : Summable (fun m => (wt m) ^ (τ + 2 * (a : ℤ)) * ‖c m‖ ^ 2)) :
    Summable (fun m => (wt m) ^ τ * ‖multFam a c m‖ ^ 2) :=
  Summable.of_nonneg_of_le
    (fun m => mul_nonneg (zpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos m)) τ) (sq_nonneg _))
    (fun m => mult_sq_le a τ c m) (h.mul_left ((4 * Real.pi ^ 2) ^ (2 * a)))

/-- **The telescoping step** of the `k`-fold commutator:
`[Λ^{n+1}, M_β] c = Λ^n ([Λ, M_β] c) + [Λ^n, M_β] (Λ c)`. -/
lemma bigFam_succ (n : ℕ) (β c : (ι → ℤ) → ℂ) (hβ : RapidL1 β) (hc : Rapid c) :
    bigFam (n + 1) β c = multFam n (stepFam β c) + bigFam n β (multFam 1 c) := by
  funext m
  have hc1 : Rapid (multFam 1 c) := Rapid_mult 1 c hc
  have hstep1 : Summable (fun l => β l * (lamC m - lamC (m - l)) * c (m - l)) :=
    summable_stepFam β c hβ hc m
  have hbig1 : Summable (fun l =>
      β l * (lamC m ^ n - lamC (m - l) ^ n) * (lamC (m - l) * c (m - l))) := by
    refine (summable_bigFam n β (multFam 1 c) hβ hc1 m).congr (fun l => ?_)
    simp only [multFam, pow_one]
  have hA : Summable (fun l =>
      lamC m ^ n * (β l * (lamC m - lamC (m - l)) * c (m - l))) := hstep1.mul_left _
  have hstep : multFam n (stepFam β c) m
      = ∑' l, lamC m ^ n * (β l * (lamC m - lamC (m - l)) * c (m - l)) := by
    rw [show multFam n (stepFam β c) m = lamC m ^ n * stepFam β c m from rfl]
    rw [show stepFam β c m = ∑' l, β l * (lamC m - lamC (m - l)) * c (m - l) from rfl]
    rw [← tsum_mul_left]
  have hbign : bigFam n β (multFam 1 c) m
      = ∑' l, β l * (lamC m ^ n - lamC (m - l) ^ n) * (lamC (m - l) * c (m - l)) := by
    rw [show bigFam n β (multFam 1 c) m
        = ∑' l, β l * (lamC m ^ n - lamC (m - l) ^ n) * (multFam 1 c (m - l)) from rfl]
    exact tsum_congr fun l => by rw [multFam, pow_one]
  rw [Pi.add_apply]
  rw [show bigFam (n + 1) β c m
      = ∑' l, β l * (lamC m ^ (n + 1) - lamC (m - l) ^ (n + 1)) * c (m - l) from rfl,
    hstep, hbign, ← Summable.tsum_add hA hbig1]
  refine tsum_congr fun l => ?_
  rw [pow_succ, pow_succ]
  ring

/-- The `k`-step commutator family in its difference-quotient form. -/
lemma bigFam_eq_conv_sub (k : ℕ) (β c : (ι → ℤ) → ℂ) (hβ : RapidL1 β) (hc : Rapid c)
    (m : ι → ℤ) :
    (((lam m) ^ k : ℝ) : ℂ) * Work.Diff.STE.conv β c m
      - Work.Diff.STE.conv β (fun j : ι → ℤ => (((lam j) ^ k : ℝ) : ℂ) * c j) m
      = bigFam k β c m := by
  have hbase : Summable (fun l : ι → ℤ => ‖β l‖ * ‖c (m - l)‖) := by
    simpa only [pow_zero, mul_one, one_mul] using summable_conv_rapid β c hβ hc m 0 0
  have hA0 : Summable (fun l : ι → ℤ => lamC m ^ k * (β l * c (m - l))) := by
    refine Summable.of_norm_bounded
      (hbase.mul_left ((4 * Real.pi ^ 2) ^ k * (wt m) ^ k)) (fun l => ?_)
    rw [norm_mul, norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    simpa only [lamC_pow] using
      Work.Diff.STE.B3.SymCalcStep6.norm_flatLam_pow_cast_le k m
  have hBbase : Summable (fun l : ι → ℤ => (wt l) ^ k * ‖β l‖ * ‖c (m - l)‖) := by
    simpa only [pow_zero, mul_one] using summable_conv_rapid β c hβ hc m k 0
  have hB0 : Summable (fun l : ι → ℤ => β l * (lamC (m - l) ^ k * c (m - l))) := by
    refine Summable.of_norm_bounded
      (hBbase.mul_left ((4 * Real.pi ^ 2) ^ k * 2 ^ k * (wt m) ^ k)) (fun l => ?_)
    rw [norm_mul, norm_mul]
    have hwt := wt_pow_le_right m l k
    have hbr : (0 : ℝ) ≤ ‖β l‖ * ‖c (m - l)‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have hnorm : ‖lamC (m - l) ^ k‖ ≤ (4 * Real.pi ^ 2) ^ k * (wt (m - l)) ^ k := by
      simpa only [lamC_pow] using
        Work.Diff.STE.B3.SymCalcStep6.norm_flatLam_pow_cast_le k (m - l)
    calc ‖β l‖ * (‖lamC (m - l) ^ k‖ * ‖c (m - l)‖)
        ≤ ‖β l‖ * (((4 * Real.pi ^ 2) ^ k * (wt (m - l)) ^ k) * ‖c (m - l)‖) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)) (norm_nonneg _)
      _ = (4 * Real.pi ^ 2) ^ k * ((wt (m - l)) ^ k * (‖β l‖ * ‖c (m - l)‖)) := by ring
      _ ≤ (4 * Real.pi ^ 2) ^ k
            * ((2 ^ k * (wt m) ^ k * (wt l) ^ k) * (‖β l‖ * ‖c (m - l)‖)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hwt hbr) (by positivity)
      _ = ((4 * Real.pi ^ 2) ^ k * 2 ^ k * (wt m) ^ k)
            * ((wt l) ^ k * ‖β l‖ * ‖c (m - l)‖) := by ring
  have key : lamC m ^ k * Work.Diff.STE.conv β c m
      - Work.Diff.STE.conv β (fun j : ι → ℤ => lamC j ^ k * c j) m
      = bigFam k β c m := by
    rw [show Work.Diff.STE.conv β c m = ∑' l : ι → ℤ, β l * c (m - l) from rfl]
    rw [show Work.Diff.STE.conv β (fun j : ι → ℤ => lamC j ^ k * c j) m
        = ∑' l : ι → ℤ, β l * (lamC (m - l) ^ k * c (m - l)) from rfl]
    rw [show bigFam k β c m
        = ∑' l : ι → ℤ, β l * (lamC m ^ k - lamC (m - l) ^ k) * c (m - l) from rfl]
    rw [← tsum_mul_left, ← Summable.tsum_sub hA0 hB0]
    exact tsum_congr fun l => by ring
  simpa only [lamC_pow] using key


theorem big_CSqZ_le (k : ℕ) (hk : 1 ≤ k) (β : (ι → ℤ) → ℂ) (hβ : RapidL1 β) (τ : ℤ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : (ι → ℤ) → ℂ, Rapid c →
      Summable (fun m => (wt m) ^ τ * ‖bigFam k β c m‖ ^ 2) ∧
      CSqZ τ (bigFam k β c) ≤ C * CSqZ (τ + 2 * (k : ℤ) - 1) c := by
  classical
  refine Nat.le_induction (m := 1)
    (P := fun k _ => ∃ C : ℝ, 0 ≤ C ∧ ∀ c : (ι → ℤ) → ℂ, Rapid c →
      Summable (fun m => (wt m) ^ τ * ‖bigFam k β c m‖ ^ 2) ∧
      CSqZ τ (bigFam k β c) ≤ C * CSqZ (τ + 2 * (k : ℤ) - 1) c) ?_ ?_ k hk
  · obtain ⟨C, hC, hCb⟩ := step_CSqZ_le β hβ τ
    have hkey : τ + 2 * ((1 : ℕ) : ℤ) - 1 = τ + 1 := by push_cast; ring
    refine ⟨C, hC, fun c hc => ?_⟩
    have hfun : bigFam 1 β c = stepFam β c := by
      funext m
      show (∑' l, β l * (lamC m ^ 1 - lamC (m - l) ^ 1) * c (m - l))
        = ∑' l, β l * (lamC m - lamC (m - l)) * c (m - l)
      exact tsum_congr fun l => by simp only [pow_one]
    rw [hkey, hfun]
    exact hCb c hc
  · intro n hn ih
    obtain ⟨C0, hC0, ihb⟩ := ih
    obtain ⟨Cm, hCm, hm⟩ := mult_CSqZ_le (ι := ι) n τ
    obtain ⟨Cs, hCs, hs⟩ := step_CSqZ_le β hβ (τ + 2 * (n : ℤ))
    obtain ⟨Cm1, hCm1, hm1⟩ := mult_CSqZ_le (ι := ι) 1 (τ + 2 * (n : ℤ) - 1)
    refine ⟨2 * (Cm * Cs + C0 * Cm1),
      mul_nonneg (by norm_num) (add_nonneg (mul_nonneg hCm hCs) (mul_nonneg hC0 hCm1)),
      fun c hc => ?_⟩
    have hc1 : Rapid (multFam 1 c) := Rapid_mult 1 c hc
    have hstepR : Rapid (stepFam β c) := by
      intro N
      obtain ⟨_, _, hN⟩ := step_CSqZ_le β hβ (N : ℤ)
      exact (hN c hc).1
    have hF : Summable (fun m => (wt m) ^ τ * ‖multFam n (stepFam β c) m‖ ^ 2) :=
      summable_multFam n τ (hs c hc).1
    have hG : Summable (fun m => (wt m) ^ τ * ‖bigFam n β (multFam 1 c) m‖ ^ 2) :=
      (ihb (multFam 1 c) hc1).1
    have hid : bigFam (n + 1) β c
        = multFam n (stepFam β c) + bigFam n β (multFam 1 c) := bigFam_succ n β c hβ hc
    have hA : CSqZ τ (multFam n (stepFam β c))
        ≤ (Cm * Cs) * CSqZ (τ + 2 * (n : ℤ) + 1) c := by
      have h1 := (hm (stepFam β c) hstepR).trans
        (mul_le_mul_of_nonneg_left (hs c hc).2 hCm)
      exact h1.trans (le_of_eq (by ring))
    have hB : CSqZ τ (bigFam n β (multFam 1 c))
        ≤ (C0 * Cm1) * CSqZ (τ + 2 * (n : ℤ) + 1) c := by
      have hkey1 : (τ + 2 * (n : ℤ) - 1) + 2 * ((1 : ℕ) : ℤ) = τ + 2 * (n : ℤ) + 1 := by
        push_cast; ring
      have h3 : CSqZ (τ + 2 * (n : ℤ) - 1) (multFam 1 c)
          ≤ Cm1 * CSqZ (τ + 2 * (n : ℤ) + 1) c := by
        simpa only [hkey1] using hm1 c hc
      have h1 := ((ihb (multFam 1 c) hc1).2).trans (mul_le_mul_of_nonneg_left h3 hC0)
      exact h1.trans (le_of_eq (by ring))
    have hsum : CSqZ τ (multFam n (stepFam β c) + bigFam n β (multFam 1 c))
        ≤ 2 * (Cm * Cs + C0 * Cm1) * CSqZ (τ + 2 * (n : ℤ) + 1) c := by
      refine (CSqZ_add_le τ hF hG).trans ?_
      have h3 : CSqZ τ (multFam n (stepFam β c)) + CSqZ τ (bigFam n β (multFam 1 c))
          ≤ (Cm * Cs + C0 * Cm1) * CSqZ (τ + 2 * (n : ℤ) + 1) c := by
        rw [add_mul]
        exact add_le_add hA hB
      calc 2 * (CSqZ τ (multFam n (stepFam β c))
              + CSqZ τ (bigFam n β (multFam 1 c)))
          ≤ 2 * ((Cm * Cs + C0 * Cm1) * CSqZ (τ + 2 * (n : ℤ) + 1) c) :=
            mul_le_mul_of_nonneg_left h3 (by norm_num)
        _ = 2 * (Cm * Cs + C0 * Cm1) * CSqZ (τ + 2 * (n : ℤ) + 1) c := by ring
    have hkey2 : τ + 2 * ((n + 1 : ℕ) : ℤ) - 1 = τ + 2 * (n : ℤ) + 1 := by push_cast; ring
    exact ⟨by rw [hid]; exact summable_CSqZ_add hF hG,
      by rw [hid, hkey2]; exact hsum⟩

/-! ## 9. The target: the coefficient statement for `fourierCoeff` -/

theorem lapPow_mul_comm_CSqZ_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (hk : 1 ≤ k) (b : (ι → ℝ) → ℂ) (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hbp : Work.Diff.STE.Periodic1 b) (t : ℤ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ G : (ι → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) G → Work.Diff.STE.Periodic1 G →
      Work.Diff.STE.B3.SymCalcStep8.CSqZ t (Work.Diff.STE.fourierCoeff (fun z : ι → ℝ =>
          Work.Diff.STE.B3.SymCalcStep5.lapPow k (fun y => b y * G y) z
            - b z * Work.Diff.STE.B3.SymCalcStep5.lapPow k G z))
        ≤ C * Work.Diff.STE.B3.SymCalcStep8.CSqZ (t + 2 * (k : ℤ) - 1)
            (Work.Diff.STE.fourierCoeff G) := by
  classical
  obtain ⟨C, hC, hCb⟩ := big_CSqZ_le k hk (Work.Diff.STE.fourierCoeff b)
    (fun N => Work.Diff.STE.B3.summable_wt_pow_mul_norm_fourierCoeff N b hb hbp) t
  refine ⟨C, hC, fun G hG hGp => ?_⟩
  have hβR : RapidL1 (Work.Diff.STE.fourierCoeff b) :=
    fun N => Work.Diff.STE.B3.summable_wt_pow_mul_norm_fourierCoeff N b hb hbp
  have hcR : Rapid (Work.Diff.STE.fourierCoeff G) :=
    fun N => Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff G hG hGp N
  rw [Work.Diff.STE.B3.SymCalcStep6.dB3_fourierCoeff_lapPow_comm k b G hb hbp hG hGp]
  have hid : (fun m : ι → ℤ => (((lam m) ^ k : ℝ) : ℂ)
        * Work.Diff.STE.conv (Work.Diff.STE.fourierCoeff b) (Work.Diff.STE.fourierCoeff G) m
      - Work.Diff.STE.conv (Work.Diff.STE.fourierCoeff b)
          (fun j : ι → ℤ => (((lam j) ^ k : ℝ) : ℂ) * Work.Diff.STE.fourierCoeff G j) m)
      = bigFam k (Work.Diff.STE.fourierCoeff b) (Work.Diff.STE.fourierCoeff G) :=
    funext fun m => bigFam_eq_conv_sub k (Work.Diff.STE.fourierCoeff b)
      (Work.Diff.STE.fourierCoeff G) hβR hcR m
  rw [hid]
  exact (hCb (Work.Diff.STE.fourierCoeff G) hcR).2

end Work.Diff.STE.B3.SymCalcStep8
