import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.B3.SymCalc
import Submission.Work.Diff.STE.B3.SymCalcStep5.conjCut_lapPow
import Submission.Work.Diff.STE.flat.seriesFun_fourierCoeff
import Submission.Work.Diff.STE.integral_seriesFun_mul_conj
import Submission.Work.Diff.STE.fourierCoeff_mul_seriesFun
import Submission.Work.Diff.STE.CSq_le_ENormSq
import Submission.Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff
import Submission.Work.Diff.STE.summable_wt_zpow
import Submission.Work.Diff.STE.l1_l2sq_conv_le
import Submission.Work.Diff.STE.contDiff_seriesFun
import Submission.Work.Diff.STE.B3.SymCalcStep1.Defs
import Submission.Work.Diff.STE.B3.flatLam_weighted_sub_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `flat_diag_pairing_le`: the flat diagonal pairing estimate

The pairing `⟨f, S_ε [Λ^k, M_c] u⟩` is bounded by `C ‖f‖_{H^{k-1}} ‖u‖_{H^k}`, uniformly in
`ε ∈ (0,1]`.  The route is Fourier: the commutator `[Λ^k,M_c]` is the operator with symbol
`λ(m)^k - λ(n)^k` (in the coefficients), which is of order `2k-1`, and the estimate is the
Cauchy–Schwarz/Schur pairing in the weighted coefficient spaces.
-/

noncomputable section

open MeasureTheory BigOperators

namespace Work.Diff.STE.B3

section Helpers

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## 1. The pointwise symbol difference bound

`λ = flatLam` is the symbol of the flat Laplacian (`λ m = Σⱼ (2π mⱼ)²`), and `wt` is the
slowly varying weight `⟨m⟩² = 1 + Σ mⱼ²`.  The elementary bound collected here is

  `|λ(m)^k − λ(n)^k| ≤ (2π)^{2k} (2⟨m−n⟩² + 1) ⟨m⟩^{2(k−1)} ⟨n⟩^{2k}`,

which is exactly what makes the commutator of order `2k − 1`: it carries the weight
`⟨m⟩^{k−1} ⟨n⟩^k = ⟨n⟩^{2k-1}·(essentially)` and a factor decaying in `m − n`. -/

/-- `flatLam` from `SymCalc` is the symbol `lam` of `SymCalcStep1`. -/
lemma flatLam_eq_lam (m : ι → ℤ) :
    SymCalc.flatLam m = SymCalcStep1.lam m := rfl

/-- `wt m ^ k + wt n ^ k ≤ (2 wt (m-n) + 1) * wt m ^ (k-1) * wt n ^ k` for `1 ≤ k`. -/
lemma wt_pow_add_le (k : ℕ) (hk : 1 ≤ k) (m n : ι → ℤ) :
    wt m ^ k + wt n ^ k
      ≤ (2 * wt (m - n) + 1) * wt m ^ (k - 1) * wt n ^ k := by
  have hm : wt m ≤ 2 * wt (m - n) * wt n := by
    have h := wt_le_two_mul m n
    linarith [h]
  have hpow : wt m ^ k = wt m ^ (k - 1) * wt m := by
    conv_lhs => rw [← Nat.sub_add_cancel hk, pow_succ]
  have hnk : wt n ≤ wt n ^ k := by
    calc wt n = wt n ^ 1 := (pow_one _).symm
      _ ≤ wt n ^ k := pow_le_pow_right₀ (wt_one_le n) hk
  have hXnn : (0 : ℝ) ≤ wt m ^ (k - 1) := pow_nonneg (le_of_lt (wt_pos m)) _
  have hAnn : (0 : ℝ) ≤ 2 * wt (m - n) := by
    have := wt_pos (m - n); linarith
  have hA : wt m ^ k ≤ 2 * wt (m - n) * (wt m ^ (k - 1) * wt n ^ k) := by
    rw [hpow]
    calc wt m ^ (k - 1) * wt m
        ≤ wt m ^ (k - 1) * (2 * wt (m - n) * wt n) :=
          mul_le_mul_of_nonneg_left hm hXnn
      _ = (2 * wt (m - n) * wt m ^ (k - 1)) * wt n := by ring
      _ ≤ (2 * wt (m - n) * wt m ^ (k - 1)) * wt n ^ k :=
          mul_le_mul_of_nonneg_left hnk (by positivity)
      _ = 2 * wt (m - n) * (wt m ^ (k - 1) * wt n ^ k) := by ring
  have hB : wt n ^ k ≤ 1 * (wt m ^ (k - 1) * wt n ^ k) := by
    have h1 : (1 : ℝ) ≤ wt m ^ (k - 1) := one_le_pow₀ (wt_one_le m)
    have h2 : (0 : ℝ) ≤ wt n ^ k := pow_nonneg (le_of_lt (wt_pos n)) _
    nlinarith [h1, h2]
  nlinarith [hA, hB]

/-- **The pointwise symbol-difference bound.** -/
lemma flatLam_pow_sub_le (k : ℕ) (hk : 1 ≤ k) (m n : ι → ℤ) :
    |SymCalc.flatLam m ^ k - SymCalc.flatLam n ^ k|
      ≤ (2 * Real.pi) ^ (2 * k) * (2 * wt (m - n) + 1)
          * wt m ^ (k - 1) * wt n ^ k := by
  have hm0 : 0 ≤ SymCalc.flatLam m := by
    rw [flatLam_eq_lam]; exact SymCalcStep1.lam_nonneg m
  have hn0 : 0 ≤ SymCalc.flatLam n := by
    rw [flatLam_eq_lam]; exact SymCalcStep1.lam_nonneg n
  have hml : SymCalc.flatLam m ≤ (2 * Real.pi) ^ 2 * wt m := by
    rw [flatLam_eq_lam]; exact SymCalcStep1.lam_le m
  have hnl : SymCalc.flatLam n ≤ (2 * Real.pi) ^ 2 * wt n := by
    rw [flatLam_eq_lam]; exact SymCalcStep1.lam_le n
  have h1 : |SymCalc.flatLam m ^ k - SymCalc.flatLam n ^ k|
      ≤ SymCalc.flatLam m ^ k + SymCalc.flatLam n ^ k := by
    rw [abs_sub_le_iff]
    constructor <;> linarith [pow_nonneg hm0 k, pow_nonneg hn0 k]
  have h2 : SymCalc.flatLam m ^ k ≤ (2 * Real.pi) ^ (2 * k) * wt m ^ k := by
    calc SymCalc.flatLam m ^ k ≤ ((2 * Real.pi) ^ 2 * wt m) ^ k :=
          pow_le_pow_left₀ hm0 hml k
      _ = (2 * Real.pi) ^ (2 * k) * wt m ^ k := by rw [mul_pow, pow_mul]
  have h3 : SymCalc.flatLam n ^ k ≤ (2 * Real.pi) ^ (2 * k) * wt n ^ k := by
    calc SymCalc.flatLam n ^ k ≤ ((2 * Real.pi) ^ 2 * wt n) ^ k :=
          pow_le_pow_left₀ hn0 hnl k
      _ = (2 * Real.pi) ^ (2 * k) * wt n ^ k := by rw [mul_pow, pow_mul]
  have h4 := wt_pow_add_le k hk m n
  have h5 : (0 : ℝ) ≤ (2 * Real.pi) ^ (2 * k) := by positivity
  calc |SymCalc.flatLam m ^ k - SymCalc.flatLam n ^ k|
      ≤ SymCalc.flatLam m ^ k + SymCalc.flatLam n ^ k := h1
    _ ≤ (2 * Real.pi) ^ (2 * k) * wt m ^ k + (2 * Real.pi) ^ (2 * k) * wt n ^ k :=
        add_le_add h2 h3
    _ = (2 * Real.pi) ^ (2 * k) * (wt m ^ k + wt n ^ k) := by ring
    _ ≤ (2 * Real.pi) ^ (2 * k) * ((2 * wt (m - n) + 1) * wt m ^ (k - 1) * wt n ^ k) :=
        mul_le_mul_of_nonneg_left h4 h5
    _ = (2 * Real.pi) ^ (2 * k) * (2 * wt (m - n) + 1) * wt m ^ (k - 1) * wt n ^ k := by
        ring

/-! ## 2. Weighted `ℓ¹` summability of the Fourier coefficients

Everything in the estimate is summed against `⟨k⟩^s ‖û(k)‖` for suitable `s`; smoothness makes
these sums converge. -/

/-- **Weighted `ℓ¹` summability of the Fourier coefficients** of a smooth periodic function:
`Σ_k ⟨k⟩^{2s} ‖û(k)‖ < ∞` (stated with `⟨k⟩^{2s}` on the `ℓ¹` scale, i.e. `wt k^s`). -/
lemma summable_wt_pow_mul_norm_fourierCoeff (s : ℕ) (g : (ι → ℝ) → ℂ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hper : Periodic1 g) :
    Summable (fun k : ι → ℤ => wt k ^ s * ‖fourierCoeff g k‖) := by
  set N : ℕ := Fintype.card ι + 1 with hNdef
  have hN : Fintype.card ι < 2 * N := by omega
  have hN2 : Fintype.card ι < 2 * (2 * N) := by omega
  have hbase : Summable (fun k : ι → ℤ => wt k ^ (2 * (s + N)) * ‖fourierCoeff g k‖ ^ 2) :=
    summable_weighted_fourierCoeff_of_contDiff g hg hper (2 * (s + N))
  have hinv : Summable (fun k : ι → ℤ => (wt k ^ N)⁻¹ ^ 2) := by
    refine (summable_wt_zpow (ι := ι) (2 * N) hN2).congr (fun k => ?_)
    rw [zpow_neg, zpow_natCast, inv_pow, ← pow_mul, mul_comm]
  have hkey : ∀ k : ι → ℤ, wt k ^ s * ‖fourierCoeff g k‖
      ≤ (1 / 2) * (wt k ^ (2 * (s + N)) * ‖fourierCoeff g k‖ ^ 2 + (wt k ^ N)⁻¹ ^ 2) := by
    intro k
    have hNpos : (0 : ℝ) < (wt k) ^ N := pow_pos (wt_pos k) N
    have hsplit : wt k ^ (s + N) * ‖fourierCoeff g k‖ * (wt k ^ N)⁻¹
        = wt k ^ s * ‖fourierCoeff g k‖ := by
      rw [pow_add]
      field_simp
    have hsqa : (wt k ^ (s + N) * ‖fourierCoeff g k‖) ^ 2
        = wt k ^ (2 * (s + N)) * ‖fourierCoeff g k‖ ^ 2 := by
      calc (wt k ^ (s + N) * ‖fourierCoeff g k‖) ^ 2
          = (wt k ^ (s + N)) ^ 2 * ‖fourierCoeff g k‖ ^ 2 := by rw [mul_pow]
        _ = wt k ^ ((s + N) * 2) * ‖fourierCoeff g k‖ ^ 2 := by rw [pow_mul]
        _ = wt k ^ (2 * (s + N)) * ‖fourierCoeff g k‖ ^ 2 := by rw [Nat.mul_comm]
    nlinarith [sq_nonneg (wt k ^ (s + N) * ‖fourierCoeff g k‖ - (wt k ^ N)⁻¹),
      hsplit, hsqa, hNpos]
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (pow_nonneg (le_of_lt (wt_pos k)) s) (norm_nonneg _)) hkey ?_
  exact (hbase.add hinv).mul_left (1 / 2)

/-- `ℓ¹`-summability of the Fourier coefficients of a smooth periodic function. -/
lemma summable_norm_fourierCoeff (g : (ι → ℝ) → ℂ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hper : Periodic1 g) :
    Summable (fun k : ι → ℤ => ‖fourierCoeff g k‖) := by
  have h := summable_wt_pow_mul_norm_fourierCoeff 0 g hg hper
  simpa using h

/-- The weighted `ℓ¹`-mass `Σ_l (2⟨l⟩² + 1) ‖ĉ(l)‖` of a smooth periodic function. -/
lemma summable_two_wt_add_one_mul_norm_fourierCoeff (g : (ι → ℝ) → ℂ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hper : Periodic1 g) :
    Summable (fun l : ι → ℤ => (2 * wt l + 1) * ‖fourierCoeff g l‖) := by
  have h1 := summable_wt_pow_mul_norm_fourierCoeff 1 g hg hper
  have h0 := summable_wt_pow_mul_norm_fourierCoeff 0 g hg hper
  have h2 : Summable (fun l : ι → ℤ =>
      2 * (wt l ^ 1 * ‖fourierCoeff g l‖) + 1 * (wt l ^ 0 * ‖fourierCoeff g l‖)) :=
    (h1.mul_left 2).add (h0.mul_left 1)
  refine h2.congr (fun l => ?_)
  ring

/-! ## 3. The Fourier coefficients of the truncated operator and of `Λ^k` -/

/-- The Fourier coefficients of the Friedrichs cutoff `S_ε = flatCut ρ ε`: multiplication of the
`k`-th coefficient by `ρ (ε • k)`. -/
lemma fourierCoeff_flatCut (ρ : (ι → ℝ) → ℝ) (hρ : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1) (ε : ℝ)
    (W : (ι → ℝ) → ℂ) (hW : Summable (fun k : ι → ℤ => ‖fourierCoeff W k‖)) (m : ι → ℤ) :
    fourierCoeff (SymCalc.flatCut ρ ε W) m
      = ((ρ (ε • fun i => (m i : ℝ)) : ℝ) : ℂ) * fourierCoeff W m := by
  have hsum : Summable (fun k : ι → ℤ => ‖trunc ρ ε (fourierCoeff W) k‖) := by
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) hW
    simp only [trunc]
    rw [norm_mul]
    have : ‖((ρ (ε • fun i => (k i : ℝ)) : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real]
      exact hρ _
    calc ‖((ρ (ε • fun i => (k i : ℝ)) : ℝ) : ℂ)‖ * ‖fourierCoeff W k‖
        ≤ 1 * ‖fourierCoeff W k‖ := mul_le_mul_of_nonneg_right this (norm_nonneg _)
      _ = ‖fourierCoeff W k‖ := one_mul _
  have h : fourierCoeff (seriesFun (trunc ρ ε (fourierCoeff W))) m
      = trunc ρ ε (fourierCoeff W) m := flat.fourierCoeff_seriesFun _ hsum m
  simpa only [SymCalc.flatCut, trunc] using h

/-- The Fourier coefficients of `Λ^k = lapPow k`: multiplication by `λ(m)^k`. -/
lemma fourierCoeff_lapPow (k : ℕ) (g : (ι → ℝ) → ℂ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hper : Periodic1 g) (m : ι → ℤ) :
    fourierCoeff (SymCalcStep5.lapPow k g) m
      = ((SymCalc.flatLam m ^ k : ℝ) : ℂ) * fourierCoeff g m := by
  have hsum : Summable (fun k' : ι → ℤ =>
      ‖((SymCalc.flatLam k' ^ k : ℝ) : ℂ) * fourierCoeff g k'‖) := by
    have hb := summable_wt_pow_mul_norm_fourierCoeff k g hg hper
    refine Summable.of_nonneg_of_le (fun k' => norm_nonneg _) (fun k' => ?_)
      (hb.mul_left ((2 * Real.pi) ^ (2 * k)))
    have hm0 : 0 ≤ SymCalc.flatLam k' := by
      rw [flatLam_eq_lam]; exact SymCalcStep1.lam_nonneg k'
    have hml : SymCalc.flatLam k' ≤ (2 * Real.pi) ^ 2 * wt k' := by
      rw [flatLam_eq_lam]; exact SymCalcStep1.lam_le k'
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hm0 k)]
    calc SymCalc.flatLam k' ^ k * ‖fourierCoeff g k'‖
        ≤ (((2 * Real.pi) ^ 2 * wt k') ^ k) * ‖fourierCoeff g k'‖ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hm0 hml k) (norm_nonneg _)
      _ = (2 * Real.pi) ^ (2 * k) * (wt k' ^ k * ‖fourierCoeff g k'‖) := by
          rw [mul_pow, pow_mul]; ring
  have hdef : SymCalcStep5.lapPow k g
      = seriesFun (fun m : ι → ℤ => ((SymCalc.flatLam m ^ k : ℝ) : ℂ) * fourierCoeff g m) := rfl
  rw [hdef, flat.fourierCoeff_seriesFun _ hsum m]

/-- `Λ^k = lapPow k` maps smooth periodic functions to smooth periodic functions. -/
lemma contDiff_lapPow (k : ℕ) (g : (ι → ℝ) → ℂ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hper : Periodic1 g) :
    ContDiff ℝ (⊤ : ℕ∞) (SymCalcStep5.lapPow k g) := by
  have hdef : SymCalcStep5.lapPow k g
      = seriesFun (fun m : ι → ℤ => ((SymCalc.flatLam m ^ k : ℝ) : ℂ) * fourierCoeff g m) := rfl
  rw [hdef]
  refine contDiff_seriesFun _ (fun N => ?_)
  have hb := summable_wt_pow_mul_norm_fourierCoeff (N + k) g hg hper
  refine Summable.of_nonneg_of_le
    (fun m => mul_nonneg (pow_nonneg (le_of_lt (wt_pos m)) N) (norm_nonneg _)) (fun m => ?_)
    (hb.mul_left ((2 * Real.pi) ^ (2 * k)))
  have hm0 : 0 ≤ SymCalc.flatLam m := by
    rw [flatLam_eq_lam]; exact SymCalcStep1.lam_nonneg m
  have hml : SymCalc.flatLam m ≤ (2 * Real.pi) ^ 2 * wt m := by
    rw [flatLam_eq_lam]; exact SymCalcStep1.lam_le m
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hm0 k)]
  calc wt m ^ N * (SymCalc.flatLam m ^ k * ‖fourierCoeff g m‖)
      ≤ wt m ^ N * (((2 * Real.pi) ^ 2 * wt m) ^ k * ‖fourierCoeff g m‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hm0 hml k) (norm_nonneg _))
          (pow_nonneg (le_of_lt (wt_pos m)) N)
    _ = (2 * Real.pi) ^ (2 * k) * (wt m ^ (N + k) * ‖fourierCoeff g m‖) := by
        rw [mul_pow, pow_mul]; ring

/-- `Λ^k = lapPow k` preserves `1`-periodicity. -/
lemma periodic1_lapPow (k : ℕ) (g : (ι → ℝ) → ℂ) :
    Periodic1 (SymCalcStep5.lapPow k g) := by
  have hdef : SymCalcStep5.lapPow k g
      = seriesFun (fun m : ι → ℤ => ((SymCalc.flatLam m ^ k : ℝ) : ℂ) * fourierCoeff g m) := rfl
  rw [hdef]
  exact flat.periodic1_seriesFun _

/-! ## 4. Cauchy–Schwarz for `tsum`, and the Euclidean norm on the lattice -/

/-- **Cauchy–Schwarz for `tsum`** of nonnegative families with finite `ℓ²`-mass. -/
lemma tsum_mul_le_sqrt_mul_sqrt {α : Type*} (X Z : α → ℝ) (hX0 : ∀ i, 0 ≤ X i)
    (hZ0 : ∀ i, 0 ≤ Z i) (hX : Summable fun i => X i ^ 2)
    (hZ : Summable fun i => Z i ^ 2) :
    ∑' i, X i * Z i
      ≤ Real.sqrt (∑' i, X i ^ 2) * Real.sqrt (∑' i, Z i ^ 2) := by
  have hsum : Summable fun i => X i * Z i :=
    Summable.of_nonneg_of_le (fun i => mul_nonneg (hX0 i) (hZ0 i))
      (fun i => by nlinarith [sq_nonneg (X i - Z i)]) ((hX.add hZ).mul_left (1 / 2))
  have key : ∀ t : Finset α, (∑ i ∈ t, X i * Z i)
      ≤ Real.sqrt (∑' i, X i ^ 2) * Real.sqrt (∑' i, Z i ^ 2) := by
    intro t
    have h1 : (∑ i ∈ t, X i * Z i) ^ 2 ≤ (∑ i ∈ t, X i ^ 2) * (∑ i ∈ t, Z i ^ 2) :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have h2 : (∑ i ∈ t, X i ^ 2) ≤ ∑' i, X i ^ 2 :=
      Summable.sum_le_tsum t (fun i _ => sq_nonneg _) hX
    have h3 : (∑ i ∈ t, Z i ^ 2) ≤ ∑' i, Z i ^ 2 :=
      Summable.sum_le_tsum t (fun i _ => sq_nonneg _) hZ
    have h4 : (0 : ℝ) ≤ ∑ i ∈ t, X i * Z i :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (hX0 i) (hZ0 i))
    calc (∑ i ∈ t, X i * Z i)
        ≤ Real.sqrt ((∑ i ∈ t, X i ^ 2) * (∑ i ∈ t, Z i ^ 2)) := by
          rw [← Real.sqrt_sq h4]; exact Real.sqrt_le_sqrt h1
      _ = Real.sqrt (∑ i ∈ t, X i ^ 2) * Real.sqrt (∑ i ∈ t, Z i ^ 2) :=
          Real.sqrt_mul (Finset.sum_nonneg (fun i _ => sq_nonneg _)) _
      _ ≤ Real.sqrt (∑' i, X i ^ 2) * Real.sqrt (∑' i, Z i ^ 2) :=
          mul_le_mul (Real.sqrt_le_sqrt h2) (Real.sqrt_le_sqrt h3)
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hlim : Filter.Tendsto (fun t : Finset α => (∑ i ∈ t, X i * Z i)) Filter.atTop
      (nhds (∑' i, X i * Z i)) := by
    have hh := hsum.hasSum
    simp only [HasSum, SummationFilter.unconditional_filter] at hh
    exact hh
  exact le_of_tendsto' hlim key

/-- The Euclidean norm of a lattice vector. -/
def euclid (l : ι → ℤ) : ℝ := Real.sqrt (∑ i, (((l i : ℤ)) : ℝ) ^ 2)

lemma euclid_nonneg (l : ι → ℤ) : 0 ≤ euclid l := Real.sqrt_nonneg _

/-- `1 + ‖l‖ ≤ 2 √(wt l)`. -/
lemma one_add_euclid_le_sqrt_wt (l : ι → ℤ) : 1 + euclid l ≤ 2 * Real.sqrt (wt l) := by
  have hS : (0 : ℝ) ≤ ∑ i, (((l i : ℤ)) : ℝ) ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hwt : (1 : ℝ) ≤ Real.sqrt (wt l) := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (wt_one_le l)
  have hSl : Real.sqrt (∑ i, (((l i : ℤ)) : ℝ) ^ 2) ≤ Real.sqrt (wt l) :=
    Real.sqrt_le_sqrt (SymCalcStep1.sum_sq_le_wt l)
  have he : euclid l = Real.sqrt (∑ i, (((l i : ℤ)) : ℝ) ^ 2) := rfl
  rw [he]
  linarith

/-- `(√(wt l)) ^ k` is the `k`-fold weight `⟨l⟩^k`. -/
lemma sqrt_wt_pow_sq (k : ℕ) (l : ι → ℤ) :
    (Real.sqrt (wt l) ^ k) ^ 2 = (wt l) ^ k := by
  rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (le_of_lt (wt_pos l))]

/-! ## 5. Fourier coefficients of a product, and of the diagonal commutator -/

/-- `λ^j · û` is `ℓ¹`-summable for a smooth periodic `u` (it is the coefficient family of
`Λ^j u`). -/
lemma summable_lapPow_coeff (k : ℕ) (g : (ι → ℝ) → ℂ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hper : Periodic1 g) :
    Summable (fun l : ι → ℤ => ‖((SymCalc.flatLam l ^ k : ℝ) : ℂ) * fourierCoeff g l‖) := by
  have hb := summable_wt_pow_mul_norm_fourierCoeff k g hg hper
  refine Summable.of_nonneg_of_le (fun l => norm_nonneg _) (fun l => ?_)
    (hb.mul_left ((2 * Real.pi) ^ (2 * k)))
  have hm0 : 0 ≤ SymCalc.flatLam l := by
    rw [flatLam_eq_lam]; exact SymCalcStep1.lam_nonneg l
  have hml : SymCalc.flatLam l ≤ (2 * Real.pi) ^ 2 * wt l := by
    rw [flatLam_eq_lam]; exact SymCalcStep1.lam_le l
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hm0 k)]
  calc SymCalc.flatLam l ^ k * ‖fourierCoeff g l‖
      ≤ (((2 * Real.pi) ^ 2 * wt l) ^ k) * ‖fourierCoeff g l‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hm0 hml k) (norm_nonneg _)
    _ = (2 * Real.pi) ^ (2 * k) * (wt l ^ k * ‖fourierCoeff g l‖) := by
        rw [mul_pow, pow_mul]; ring

/-- Fourier coefficients of a pointwise product: `(c·u)^(m) = û * ĉ (m)`. -/
lemma fourierCoeff_mul (c u : (ι → ℝ) → ℂ)
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (huper : Periodic1 u) (m : ι → ℤ) :
    fourierCoeff (fun x => c x * u x) m = conv (fourierCoeff u) (fourierCoeff c) m := by
  have hU : Summable (fun l : ι → ℤ => ‖fourierCoeff u l‖) :=
    summable_norm_fourierCoeff u hu huper
  have h := fourierCoeff_mul_seriesFun c (fourierCoeff u) m
    (integrableOn_unitCube_of_continuous hc.continuous) hU
  rw [show (fun x : ι → ℝ => c x * seriesFun (fourierCoeff u) x) = (fun x => c x * u x) from
    funext (fun x => by rw [flat.seriesFun_fourierCoeff u hu huper x])] at h
  exact h

/-- **The Fourier coefficients of the diagonal commutator** `[Λ^k, M_c]`:

  `([Λ^k,M_c]u)^(m) = Σ_l û(l) ĉ(m-l) (λ(m)^k − λ(l)^k)`. -/
lemma fourierCoeff_comm (k : ℕ) (c u : (ι → ℝ) → ℂ)
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hcper : Periodic1 c)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (huper : Periodic1 u) (m : ι → ℤ) :
    fourierCoeff (fun x => SymCalcStep5.lapPow k (fun y => c y * u y) x
        - c x * SymCalcStep5.lapPow k u x) m
      = ∑' l : ι → ℤ, fourierCoeff u l * fourierCoeff c (m - l)
          * (((SymCalc.flatLam m ^ k : ℝ) : ℂ) - ((SymCalc.flatLam l ^ k : ℝ) : ℂ)) := by
  have hcu : ContDiff ℝ (⊤ : ℕ∞) (fun y => c y * u y) := hc.mul hu
  have hcuper : Periodic1 (fun y => c y * u y) := by
    intro i x
    simp only [Pi.mul_apply]
    rw [hcper i x, huper i x]
  have hU : Summable (fun l : ι → ℤ => ‖fourierCoeff u l‖) :=
    summable_norm_fourierCoeff u hu huper
  have hCc : Summable (fun l : ι → ℤ => ‖fourierCoeff c l‖) :=
    summable_norm_fourierCoeff c hc hcper
  have hcontA : Continuous (SymCalcStep5.lapPow k (fun y => c y * u y)) :=
    (contDiff_lapPow k _ hcu hcuper).continuous
  have hcontB : Continuous (fun x : ι → ℝ => c x * SymCalcStep5.lapPow k u x) :=
    hc.continuous.mul (contDiff_lapPow k u hu huper).continuous
  have hA : fourierCoeff (SymCalcStep5.lapPow k (fun y => c y * u y)) m
      = ((SymCalc.flatLam m ^ k : ℝ) : ℂ) * conv (fourierCoeff u) (fourierCoeff c) m := by
    rw [fourierCoeff_lapPow k _ hcu hcuper m, fourierCoeff_mul c u hc hu huper m]
  have hB : fourierCoeff (fun x : ι → ℝ => c x * SymCalcStep5.lapPow k u x) m
      = conv (fun l : ι → ℤ => ((SymCalc.flatLam l ^ k : ℝ) : ℂ) * fourierCoeff u l)
          (fourierCoeff c) m :=
    fourierCoeff_mul_seriesFun c
      (fun l : ι → ℤ => ((SymCalc.flatLam l ^ k : ℝ) : ℂ) * fourierCoeff u l) m
      (integrableOn_unitCube_of_continuous hc.continuous)
      (summable_lapPow_coeff k u hu huper)
  -- summabilities of the two convolutions
  have hBU : ∀ l : ι → ℤ, ‖fourierCoeff u l‖ ≤ ∑' n : ι → ℤ, ‖fourierCoeff u n‖ :=
    fun l => hU.le_tsum l (fun n _ => norm_nonneg _)
  have hshiftC : Summable (fun l : ι → ℤ => ‖fourierCoeff c (m - l)‖) :=
    hCc.comp_injective (fun a b h => by
      have h1 : m - (m - a) = m - (m - b) := by rw [h]
      simpa using h1)
  have hsumU : Summable (fun l : ι → ℤ =>
      ‖fourierCoeff u l * fourierCoeff c (m - l)‖) := by
    refine Summable.of_nonneg_of_le (fun l => norm_nonneg _) (fun l => ?_)
      (hshiftC.mul_left (∑' n : ι → ℤ, ‖fourierCoeff u n‖))
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hBU l) (norm_nonneg _)
  have hterm : Summable (fun l : ι → ℤ =>
      ‖(((SymCalc.flatLam l ^ k : ℝ) : ℂ) * fourierCoeff u l) * fourierCoeff c (m - l)‖) := by
    refine Summable.of_nonneg_of_le (fun l => norm_nonneg _) (fun l => ?_)
      ((summable_lapPow_coeff k u hu huper).mul_right (∑' n : ι → ℤ, ‖fourierCoeff c n‖))
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (hCc.le_tsum (m - l) (fun n _ => norm_nonneg _))
      (norm_nonneg (((SymCalc.flatLam l ^ k : ℝ) : ℂ) * fourierCoeff u l))
  have hsumUc : Summable (fun l : ι → ℤ =>
      fourierCoeff u l * fourierCoeff c (m - l)) :=
    Summable.of_norm (by simpa [norm_mul] using hsumU)
  have htermc : Summable (fun l : ι → ℤ =>
      (((SymCalc.flatLam l ^ k : ℝ) : ℂ) * fourierCoeff u l) * fourierCoeff c (m - l)) :=
    Summable.of_norm (by simpa [norm_mul] using hterm)
  have hsub := flat.fourierCoeff_sub_of_continuous _ _ hcontA hcontB m
  rw [hsub, hA, hB]
  simp only [conv]
  rw [← Summable.tsum_mul_left (((SymCalc.flatLam m ^ k : ℝ) : ℂ)) hsumUc,
    ← Summable.tsum_sub (hsumUc.mul_left _) htermc]
  refine tsum_congr (fun l => ?_)
  ring

/-! ## 6. Parseval for a Fourier series against a smooth function -/

/-- The `L²` pairing of a smooth periodic function with the Fourier series of a coefficient
family `d`. -/
lemma L2re_seriesFun_eq (f : (ι → ℝ) → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfper : Periodic1 f)
    (d : (ι → ℤ) → ℂ) (hd : Summable (fun k : ι → ℤ => ‖d k‖)) :
    L2re f (seriesFun d) = (∑' m : ι → ℤ, fourierCoeff f m * star (d m)).re := by
  have hF : Summable (fun k : ι → ℤ => ‖fourierCoeff f k‖) :=
    summable_norm_fourierCoeff f hf hfper
  have h1 : (∫ x in unitCube, f x * star (seriesFun d x))
      = ∫ x in unitCube, seriesFun (fourierCoeff f) x * star (seriesFun d x) := by
    apply integral_congr_ae
    filter_upwards with x
    rw [flat.seriesFun_fourierCoeff f hf hfper x]
  rw [L2re, h1, integral_seriesFun_mul_conj _ _ hF hd]

/-! ## 7. The kernel bound for the diagonal commutator -/

/-- Reindexing a convolution sum (`l ↦ m − l`). -/
lemma tsum_conv_swap (F G : (ι → ℤ) → ℝ) (m : ι → ℤ) :
    (∑' l : ι → ℤ, F l * G (m - l)) = ∑' l : ι → ℤ, F (m - l) * G l := by
  have h := Equiv.tsum_eq (Equiv.subLeft m) (fun l : ι → ℤ => F (m - l) * G l)
  simp only [Equiv.subLeft_apply] at h
  have h2 : (fun c : ι → ℤ => F (m - (m - c)) * G (m - c))
      = fun c : ι → ℤ => F c * G (m - c) := by
    funext c
    rw [show m - (m - c) = c from by abel]
  rw [h2] at h
  exact h

/-- **Kernel bound for the diagonal commutator.**  From the sharp pointwise bound `hA` on
`λ(m)^k − λ(n)^k`, the Fourier coefficient of `[Λ^k, M_c] u` is bounded by the `ℓ¹`-convolution of
the weighted coefficient families of `c` and `u`. -/
lemma norm_fourierCoeff_comm_le (k : ℕ) (hk : 1 ≤ k)
    (hA : ∀ m n : ι → ℤ, |SymCalc.flatLam m ^ k - SymCalc.flatLam n ^ k|
        ≤ (2 * (k : ℝ) * (2 * Real.pi) ^ (2 * k) * 3 ^ k)
            * (1 + euclid (m - n)) ^ (2 * k)
            * Real.sqrt (wt m) ^ (k - 1) * Real.sqrt (wt n) ^ k)
    (c u : (ι → ℝ) → ℂ) (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hcper : Periodic1 c)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (huper : Periodic1 u) (m : ι → ℤ) :
    ‖fourierCoeff (fun x => SymCalcStep5.lapPow k (fun y => c y * u y) x
        - c x * SymCalcStep5.lapPow k u x) m‖
      ≤ (2 * (k : ℝ) * (2 * Real.pi) ^ (2 * k) * 3 ^ k) * Real.sqrt (wt m) ^ (k - 1)
          * ∑' l : ι → ℤ, ((1 + euclid l) ^ (2 * k) * ‖fourierCoeff c l‖)
              * (Real.sqrt (wt (m - l)) ^ k * ‖fourierCoeff u (m - l)‖) := by
  have hPhi2 : Summable (fun l : ι → ℤ =>
      ((1 + euclid l) ^ (2 * k) * ‖fourierCoeff c l‖) ^ 2) := by
    have hbase := summable_weighted_fourierCoeff_of_contDiff c hc hcper (2 * k)
    refine Summable.of_nonneg_of_le (fun l => sq_nonneg _) (fun l => ?_)
      (hbase.mul_left ((2 : ℝ) ^ (4 * k)))
    have h1 : ((1 + euclid l) ^ (2 * k)) ^ 2
        ≤ ((2 : ℝ) ^ (2 * k) * (wt l) ^ k) ^ 2 := by
      have h2 : (2 * Real.sqrt (wt l)) ^ (2 * k) = (2 : ℝ) ^ (2 * k) * (wt l) ^ k := by
        rw [mul_pow]
        congr 1
        rw [pow_mul, Real.sq_sqrt (le_of_lt (wt_pos l))]
      rw [← h2]
      exact pow_le_pow_left₀
        (pow_nonneg (add_nonneg zero_le_one (euclid_nonneg l)) _)
        (pow_le_pow_left₀ (add_nonneg zero_le_one (euclid_nonneg l))
          (one_add_euclid_le_sqrt_wt l) (2 * k)) 2
    have h3 : ((2 : ℝ) ^ (2 * k) * (wt l) ^ k) ^ 2
        = (2 : ℝ) ^ (4 * k) * (wt l) ^ (2 * k) := by
      rw [mul_pow, ← pow_mul, ← pow_mul, show (2 * k) * 2 = 4 * k from by ring,
        show k * 2 = 2 * k from by ring]
    calc ((1 + euclid l) ^ (2 * k) * ‖fourierCoeff c l‖) ^ 2
        = ((1 + euclid l) ^ (2 * k)) ^ 2 * ‖fourierCoeff c l‖ ^ 2 := by rw [mul_pow]
      _ ≤ ((2 : ℝ) ^ (2 * k) * (wt l) ^ k) ^ 2 * ‖fourierCoeff c l‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      _ = (2 : ℝ) ^ (4 * k) * ((wt l) ^ (2 * k) * ‖fourierCoeff c l‖ ^ 2) := by
          rw [h3]; ring
  have hY2 : Summable (fun l : ι → ℤ =>
      (Real.sqrt (wt l) ^ k * ‖fourierCoeff u l‖) ^ 2) := by
    refine Summable.of_nonneg_of_le (fun l => sq_nonneg _) (fun l => ?_)
      (summable_weighted_fourierCoeff_of_contDiff u hu huper k)
    rw [mul_pow, sqrt_wt_pow_sq]
  have hYPhi : Summable (fun l : ι → ℤ => Real.sqrt (wt l) ^ k * ‖fourierCoeff u l‖
      * ((1 + euclid (m - l)) ^ (2 * k) * ‖fourierCoeff c (m - l)‖)) := by
    have hP2 : Summable (fun l : ι → ℤ =>
        ((1 + euclid (m - l)) ^ (2 * k) * ‖fourierCoeff c (m - l)‖) ^ 2) :=
      hPhi2.comp_injective (sub_right_injective (b := m))
    refine Summable.of_nonneg_of_le
      (fun l => mul_nonneg (mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) (norm_nonneg _))
        (mul_nonneg (pow_nonneg (add_nonneg zero_le_one (euclid_nonneg (m - l))) _)
          (norm_nonneg _)))
      (fun l => ?_) ((hY2.add hP2).mul_left (1 / 2))
    nlinarith [sq_nonneg (Real.sqrt (wt l) ^ k * ‖fourierCoeff u l‖
      - ((1 + euclid (m - l)) ^ (2 * k) * ‖fourierCoeff c (m - l)‖))]
  have hbnd : ∀ l : ι → ℤ, ‖fourierCoeff u l * fourierCoeff c (m - l)
      * (((SymCalc.flatLam m ^ k : ℝ) : ℂ) - ((SymCalc.flatLam l ^ k : ℝ) : ℂ))‖
      ≤ (2 * (k : ℝ) * (2 * Real.pi) ^ (2 * k) * 3 ^ k) * Real.sqrt (wt m) ^ (k - 1)
        * ((Real.sqrt (wt l) ^ k * ‖fourierCoeff u l‖)
            * ((1 + euclid (m - l)) ^ (2 * k) * ‖fourierCoeff c (m - l)‖)) := by
    intro l
    rw [norm_mul, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have hle := hA m l
    have hp : 0 ≤ ‖fourierCoeff u l‖ * ‖fourierCoeff c (m - l)‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    calc ‖fourierCoeff u l‖ * ‖fourierCoeff c (m - l)‖
          * |SymCalc.flatLam m ^ k - SymCalc.flatLam l ^ k|
        ≤ ‖fourierCoeff u l‖ * ‖fourierCoeff c (m - l)‖
          * ((2 * (k : ℝ) * (2 * Real.pi) ^ (2 * k) * 3 ^ k)
              * (1 + euclid (m - l)) ^ (2 * k)
              * Real.sqrt (wt m) ^ (k - 1) * Real.sqrt (wt l) ^ k) :=
          mul_le_mul_of_nonneg_left hle hp
      _ = (2 * (k : ℝ) * (2 * Real.pi) ^ (2 * k) * 3 ^ k) * Real.sqrt (wt m) ^ (k - 1)
          * ((Real.sqrt (wt l) ^ k * ‖fourierCoeff u l‖)
              * ((1 + euclid (m - l)) ^ (2 * k) * ‖fourierCoeff c (m - l)‖)) := by ring
  have hsumGn : Summable (fun l : ι → ℤ => ‖fourierCoeff u l * fourierCoeff c (m - l)
      * (((SymCalc.flatLam m ^ k : ℝ) : ℂ) - ((SymCalc.flatLam l ^ k : ℝ) : ℂ))‖) :=
    Summable.of_nonneg_of_le (fun l => norm_nonneg _) hbnd
      (hYPhi.mul_left ((2 * (k : ℝ) * (2 * Real.pi) ^ (2 * k) * 3 ^ k)
        * Real.sqrt (wt m) ^ (k - 1)))
  have hsumG : Summable (fun l : ι → ℤ => fourierCoeff u l * fourierCoeff c (m - l)
      * (((SymCalc.flatLam m ^ k : ℝ) : ℂ) - ((SymCalc.flatLam l ^ k : ℝ) : ℂ))) :=
    Summable.of_norm hsumGn
  rw [fourierCoeff_comm k c u hc hcper hu huper m]
  calc ‖∑' l : ι → ℤ, fourierCoeff u l * fourierCoeff c (m - l)
        * (((SymCalc.flatLam m ^ k : ℝ) : ℂ) - ((SymCalc.flatLam l ^ k : ℝ) : ℂ))‖
      ≤ ∑' l : ι → ℤ, ‖fourierCoeff u l * fourierCoeff c (m - l)
        * (((SymCalc.flatLam m ^ k : ℝ) : ℂ) - ((SymCalc.flatLam l ^ k : ℝ) : ℂ))‖ :=
        norm_tsum_le_tsum_norm hsumGn
    _ ≤ ∑' l : ι → ℤ, (2 * (k : ℝ) * (2 * Real.pi) ^ (2 * k) * 3 ^ k) * Real.sqrt (wt m) ^ (k - 1)
        * ((Real.sqrt (wt l) ^ k * ‖fourierCoeff u l‖)
            * ((1 + euclid (m - l)) ^ (2 * k) * ‖fourierCoeff c (m - l)‖)) :=
        Summable.tsum_le_tsum hbnd hsumGn (hYPhi.mul_left _)
    _ = (2 * (k : ℝ) * (2 * Real.pi) ^ (2 * k) * 3 ^ k) * Real.sqrt (wt m) ^ (k - 1)
        * ∑' l : ι → ℤ, (Real.sqrt (wt l) ^ k * ‖fourierCoeff u l‖)
            * ((1 + euclid (m - l)) ^ (2 * k) * ‖fourierCoeff c (m - l)‖) := by
        rw [← tsum_mul_left (a := (2 * (k : ℝ) * (2 * Real.pi) ^ (2 * k) * 3 ^ k)
          * Real.sqrt (wt m) ^ (k - 1))]
    _ = (2 * (k : ℝ) * (2 * Real.pi) ^ (2 * k) * 3 ^ k) * Real.sqrt (wt m) ^ (k - 1)
        * ∑' l : ι → ℤ, ((1 + euclid l) ^ (2 * k) * ‖fourierCoeff c l‖)
            * (Real.sqrt (wt (m - l)) ^ k * ‖fourierCoeff u (m - l)‖) := by
        congr 1
        calc (∑' l : ι → ℤ, Real.sqrt (wt l) ^ k * ‖fourierCoeff u l‖
              * ((1 + euclid (m - l)) ^ (2 * k) * ‖fourierCoeff c (m - l)‖))
            = ∑' l : ι → ℤ, (Real.sqrt (wt (m - l)) ^ k * ‖fourierCoeff u (m - l)‖)
              * ((1 + euclid l) ^ (2 * k) * ‖fourierCoeff c l‖) :=
              tsum_conv_swap (fun l : ι → ℤ => Real.sqrt (wt l) ^ k * ‖fourierCoeff u l‖)
                (fun l : ι → ℤ => (1 + euclid l) ^ (2 * k) * ‖fourierCoeff c l‖) m
          _ = ∑' l : ι → ℤ, ((1 + euclid l) ^ (2 * k) * ‖fourierCoeff c l‖)
              * (Real.sqrt (wt (m - l)) ^ k * ‖fourierCoeff u (m - l)‖) :=
              tsum_congr (fun l => by ring)

end Helpers

theorem flat_diag_pairing_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (hk : 1 ≤ k)
    (c : (ι → ℝ) → ℝ) (hc : ContDiff ℝ (⊤ : ℕ∞) c)
    (hcper : Work.Diff.STE.Periodic1 c)
    (ρ : (ι → ℝ) → ℝ) (hρ : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ε : ℝ), 0 < ε → ε ≤ 1 →
        ∀ (f u : (ι → ℝ) → ℂ),
          ContDiff ℝ (⊤ : ℕ∞) f → Work.Diff.STE.Periodic1 f →
          ContDiff ℝ (⊤ : ℕ∞) u → Work.Diff.STE.Periodic1 u →
          |Work.Diff.STE.L2re f (Work.Diff.STE.B3.SymCalc.flatCut ρ ε
              (fun x => Work.Diff.STE.B3.SymCalcStep5.lapPow k
                  (fun y => ((c y : ℝ) : ℂ) * u y) x
                - ((c x : ℝ) : ℂ) * Work.Diff.STE.B3.SymCalcStep5.lapPow k u x))|
            ≤ C * Real.sqrt (Work.Diff.STE.ENormSq (k - 1) f + Work.Diff.STE.ENormSq 0 f)
                * Real.sqrt (Work.Diff.STE.ENormSq k u + Work.Diff.STE.ENormSq 0 u) := by
  obtain ⟨Cf, hCf0, hCf⟩ := CSq_le_ENormSq (ι := ι) (k - 1)
  obtain ⟨Cu, hCu0, hCu⟩ := CSq_le_ENormSq (ι := ι) k
  set cC : (ι → ℝ) → ℂ := fun x => ((c x : ℝ) : ℂ) with hcCdef
  have hcC : ContDiff ℝ (⊤ : ℕ∞) cC := Complex.ofRealCLM.contDiff.comp hc
  have hcCe : ∀ (i : ι) (x : ι → ℝ), cC (x + Pi.single i 1) = cC x := by
    intro i x
    show ((c (x + Pi.single i 1) : ℝ) : ℂ) = ((c x : ℝ) : ℂ)
    rw [hcper i x]
  have hΦsum : Summable (fun l : ι → ℤ => (1 + euclid l) ^ (2 * k) * ‖fourierCoeff cC l‖) := by
    have hbase := summable_wt_pow_mul_norm_fourierCoeff k cC hcC hcCe
    refine Summable.of_nonneg_of_le
      (fun l => mul_nonneg (pow_nonneg (add_nonneg zero_le_one (euclid_nonneg l)) _)
        (norm_nonneg _)) (fun l => ?_) (hbase.mul_left ((2 : ℝ) ^ (2 * k)))
    have h2 : (2 * Real.sqrt (wt l)) ^ (2 * k) = (2 : ℝ) ^ (2 * k) * (wt l) ^ k := by
      rw [mul_pow]
      congr 1
      rw [pow_mul, Real.sq_sqrt (le_of_lt (wt_pos l))]
    calc (1 + euclid l) ^ (2 * k) * ‖fourierCoeff cC l‖
        ≤ (2 * Real.sqrt (wt l)) ^ (2 * k) * ‖fourierCoeff cC l‖ :=
          mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (add_nonneg zero_le_one (euclid_nonneg l))
              (one_add_euclid_le_sqrt_wt l) _) (norm_nonneg _)
      _ = (2 : ℝ) ^ (2 * k) * (wt l ^ k * ‖fourierCoeff cC l‖) := by rw [h2]; ring
  have hSΦnn : (0 : ℝ) ≤ ∑' l : ι → ℤ, (1 + euclid l) ^ (2 * k) * ‖fourierCoeff cC l‖ :=
    tsum_nonneg (fun l => mul_nonneg (pow_nonneg (add_nonneg zero_le_one (euclid_nonneg l)) _)
      (norm_nonneg _))
  refine ⟨(2 * (k : ℝ) * (2 * Real.pi) ^ (2 * k) * 3 ^ k)
      * (∑' l : ι → ℤ, (1 + euclid l) ^ (2 * k) * ‖fourierCoeff cC l‖)
      * Real.sqrt Cf * Real.sqrt Cu, ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ 2 * (k : ℝ) * (2 * Real.pi) ^ (2 * k) * 3 ^ k := by positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg h1 hSΦnn) (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)
  · intro ε hε0 hε1 f u hf hfper hu huper
    have hfun : (fun x : ι → ℝ => SymCalcStep5.lapPow k (fun y => ((c y : ℝ) : ℂ) * u y) x
          - ((c x : ℝ) : ℂ) * SymCalcStep5.lapPow k u x)
        = fun x : ι → ℝ => SymCalcStep5.lapPow k (fun y => cC y * u y) x
          - cC x * SymCalcStep5.lapPow k u x := by
      funext x
      simp only [hcCdef]
    rw [hfun]
    set W : (ι → ℝ) → ℂ := fun x => SymCalcStep5.lapPow k (fun y => cC y * u y) x
      - cC x * SymCalcStep5.lapPow k u x with hWdef
    have hcuper : Periodic1 (fun y => cC y * u y) := by
      intro i x
      show cC (x + Pi.single i 1) * u (x + Pi.single i 1) = cC x * u x
      rw [hcCe i x, huper i x]
    have hcu : ContDiff ℝ (⊤ : ℕ∞) (fun y => cC y * u y) := hcC.mul hu
    have hWc : ContDiff ℝ (⊤ : ℕ∞) W :=
      (contDiff_lapPow k _ hcu hcuper).sub (hcC.mul (contDiff_lapPow k u hu huper))
    have hWper : Periodic1 W := by
      intro i x
      show SymCalcStep5.lapPow k (fun y => cC y * u y) (x + Pi.single i 1)
          - cC (x + Pi.single i 1) * SymCalcStep5.lapPow k u (x + Pi.single i 1)
        = SymCalcStep5.lapPow k (fun y => cC y * u y) x - cC x * SymCalcStep5.lapPow k u x
      rw [periodic1_lapPow k (fun y => cC y * u y) i x,
        periodic1_lapPow k u i x, hcCe i x]
    have hWsum : Summable (fun m : ι → ℤ => ‖fourierCoeff W m‖) :=
      summable_norm_fourierCoeff W hWc hWper
    have htrunc_le : ∀ m : ι → ℤ, ‖trunc ρ ε (fourierCoeff W) m‖ ≤ ‖fourierCoeff W m‖ := by
      intro m
      simp only [trunc]
      rw [norm_mul]
      have h1 : ‖((ρ (ε • fun i => (m i : ℝ)) : ℝ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real]; exact hρ _
      calc ‖((ρ (ε • fun i => (m i : ℝ)) : ℝ) : ℂ)‖ * ‖fourierCoeff W m‖
          ≤ 1 * ‖fourierCoeff W m‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ = ‖fourierCoeff W m‖ := one_mul _
    have htrunc : Summable (fun m : ι → ℤ => ‖trunc ρ ε (fourierCoeff W) m‖) :=
      Summable.of_nonneg_of_le (fun m => norm_nonneg _) htrunc_le hWsum
    have hpar : L2re f (SymCalc.flatCut ρ ε W)
        = (∑' m : ι → ℤ, fourierCoeff f m * star (trunc ρ ε (fourierCoeff W) m)).re :=
      L2re_seriesFun_eq f hf hfper _ htrunc
    set Ck : ℝ := 2 * (k : ℝ) * (2 * Real.pi) ^ (2 * k) * 3 ^ k with hCkdef
    have hCk0 : (0 : ℝ) ≤ Ck := by rw [hCkdef]; positivity
    have hker : ∀ m : ι → ℤ, ‖fourierCoeff W m‖
        ≤ Ck * Real.sqrt (wt m) ^ (k - 1)
          * ∑' l : ι → ℤ, ((1 + euclid l) ^ (2 * k) * ‖fourierCoeff cC l‖)
              * (Real.sqrt (wt (m - l)) ^ k * ‖fourierCoeff u (m - l)‖) :=
      fun m => norm_fourierCoeff_comm_le k hk (fun a b => flatLam_weighted_sub_le k hk a b)
        cC u hcC hcCe hu huper m
    set Φ : (ι → ℤ) → ℝ := fun l => (1 + euclid l) ^ (2 * k) * ‖fourierCoeff cC l‖ with hΦdef
    set Y : (ι → ℤ) → ℝ := fun n => Real.sqrt (wt n) ^ k * ‖fourierCoeff u n‖ with hYdef
    set Z : (ι → ℤ) → ℝ := fun m => ∑' l : ι → ℤ, Φ l * Y (m - l) with hZdef
    set X : (ι → ℤ) → ℝ := fun m => Real.sqrt (wt m) ^ (k - 1) * ‖fourierCoeff f m‖ with hXdef
    have hΦnn : ∀ l, 0 ≤ Φ l := fun l => mul_nonneg
      (pow_nonneg (add_nonneg zero_le_one (euclid_nonneg l)) _) (norm_nonneg _)
    have hYnn : ∀ n, 0 ≤ Y n := fun n => mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _)
      (norm_nonneg _)
    have hΦsum' : Summable Φ := hΦsum
    have hY2sum : Summable (fun n : ι → ℤ => Y n ^ 2) := by
      refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_)
        (summable_weighted_fourierCoeff_of_contDiff u hu huper k)
      simp only [hYdef]
      rw [mul_pow, sqrt_wt_pow_sq]
    have hZ := l1_l2sq_conv_le Φ Y hΦnn hYnn hΦsum' hY2sum
    have hZ2sum : Summable (fun m : ι → ℤ => Z m ^ 2) := by
      simpa only [hZdef] using hZ.1
    have hZ2le : ∑' m : ι → ℤ, Z m ^ 2
        ≤ (∑' l : ι → ℤ, Φ l) ^ 2 * ∑' n : ι → ℤ, Y n ^ 2 := by
      simpa only [hZdef] using hZ.2
    have hX2sum : Summable (fun m : ι → ℤ => X m ^ 2) := by
      refine Summable.of_nonneg_of_le (fun m => sq_nonneg _) (fun m => ?_)
        (summable_weighted_fourierCoeff_of_contDiff f hf hfper (k - 1))
      simp only [hXdef]
      rw [mul_pow, sqrt_wt_pow_sq]
    have hX2eq : ∑' m : ι → ℤ, X m ^ 2 = CSq (k - 1) (fourierCoeff f) := by
      simp only [CSq]
      refine tsum_congr (fun m => ?_)
      simp only [hXdef]
      rw [mul_pow, sqrt_wt_pow_sq]
    have hY2eq : ∑' n : ι → ℤ, Y n ^ 2 = CSq k (fourierCoeff u) := by
      simp only [CSq]
      refine tsum_congr (fun n => ?_)
      simp only [hYdef]
      rw [mul_pow, sqrt_wt_pow_sq]
    have hZnn : ∀ m, 0 ≤ Z m := fun m => tsum_nonneg (fun l => mul_nonneg (hΦnn l) (hYnn _))
    have hXnn : ∀ m, 0 ≤ X m := fun m => mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _)
      (norm_nonneg _)
    have hXZsum : Summable (fun m : ι → ℤ => X m * Z m) :=
      Summable.of_nonneg_of_le (fun m => mul_nonneg (hXnn m) (hZnn m))
        (fun m => by nlinarith [sq_nonneg (X m - Z m)]) ((hX2sum.add hZ2sum).mul_left (1 / 2))
    have hFFW : Summable (fun m : ι → ℤ => ‖fourierCoeff f m‖ * ‖fourierCoeff W m‖) := by
      refine Summable.of_nonneg_of_le (fun m => mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (fun m => ?_) (hXZsum.mul_left Ck)
      calc ‖fourierCoeff f m‖ * ‖fourierCoeff W m‖
          ≤ ‖fourierCoeff f m‖ * (Ck * Real.sqrt (wt m) ^ (k - 1) * Z m) :=
            mul_le_mul_of_nonneg_left (hker m) (norm_nonneg _)
        _ = Ck * (X m * Z m) := by
            simp only [hXdef]; ring
    have hFFWle : (∑' m : ι → ℤ, ‖fourierCoeff f m‖ * ‖fourierCoeff W m‖)
        ≤ ∑' m : ι → ℤ, Ck * (X m * Z m) := by
      refine Summable.tsum_le_tsum (fun m => ?_) hFFW (hXZsum.mul_left Ck)
      calc ‖fourierCoeff f m‖ * ‖fourierCoeff W m‖
          ≤ ‖fourierCoeff f m‖ * (Ck * Real.sqrt (wt m) ^ (k - 1) * Z m) :=
            mul_le_mul_of_nonneg_left (hker m) (norm_nonneg _)
        _ = Ck * (X m * Z m) := by
            simp only [hXdef]; ring
    have hprodn : Summable (fun m : ι → ℤ => ‖fourierCoeff f m‖ * ‖trunc ρ ε (fourierCoeff W) m‖) :=
      Summable.of_nonneg_of_le (fun m => mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (fun m => mul_le_mul_of_nonneg_left (htrunc_le m) (norm_nonneg _)) hFFW
    have hprod : Summable (fun m : ι → ℤ =>
        fourierCoeff f m * star (trunc ρ ε (fourierCoeff W) m)) :=
      Summable.of_norm (by simpa [norm_mul, norm_star] using hprodn)
    have hsX : Real.sqrt (∑' m : ι → ℤ, X m ^ 2) = Real.sqrt (CSq (k - 1) (fourierCoeff f)) := by
      rw [hX2eq]
    have hsY : Real.sqrt (∑' n : ι → ℤ, Y n ^ 2) = Real.sqrt (CSq k (fourierCoeff u)) := by
      rw [hY2eq]
    have hsZ : Real.sqrt (∑' m : ι → ℤ, Z m ^ 2) ≤
        (∑' l : ι → ℤ, Φ l) * Real.sqrt (∑' n : ι → ℤ, Y n ^ 2) := by
      have h1 := Real.sqrt_le_sqrt hZ2le
      rwa [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (tsum_nonneg hΦnn)] at h1
    have hf' : ContDiff ℝ ((k - 1 : ℕ) : WithTop ℕ∞) f := by
      refine hf.of_le ?_
      apply WithTop.coe_le_coe.mpr
      exact le_top
    have hs1 : Real.sqrt (CSq (k - 1) (fourierCoeff f))
        ≤ Real.sqrt Cf * Real.sqrt (ENormSq (k - 1) f + ENormSq 0 f) := by
      refine (Real.sqrt_le_sqrt (hCf f hf' hfper)).trans (le_of_eq ?_)
      rw [Real.sqrt_mul hCf0]
    have hu' : ContDiff ℝ ((k : ℕ) : WithTop ℕ∞) u := by
      refine hu.of_le ?_
      apply WithTop.coe_le_coe.mpr
      exact le_top
    have hs2 : Real.sqrt (CSq k (fourierCoeff u))
        ≤ Real.sqrt Cu * Real.sqrt (ENormSq k u + ENormSq 0 u) := by
      refine (Real.sqrt_le_sqrt (hCu u hu' huper)).trans (le_of_eq ?_)
      rw [Real.sqrt_mul hCu0]
    calc |L2re f (SymCalc.flatCut ρ ε W)|
        = |(∑' m : ι → ℤ, fourierCoeff f m * star (trunc ρ ε (fourierCoeff W) m)).re| := by
            rw [hpar]
      _ ≤ ‖∑' m : ι → ℤ, fourierCoeff f m * star (trunc ρ ε (fourierCoeff W) m)‖ :=
            Complex.abs_re_le_norm _
      _ ≤ ∑' m : ι → ℤ, ‖fourierCoeff f m * star (trunc ρ ε (fourierCoeff W) m)‖ :=
            norm_tsum_le_tsum_norm (by simpa [norm_mul, norm_star] using hprodn)
      _ = ∑' m : ι → ℤ, ‖fourierCoeff f m‖ * ‖trunc ρ ε (fourierCoeff W) m‖ := by
            refine tsum_congr (fun m => ?_)
            rw [norm_mul, norm_star]
      _ ≤ ∑' m : ι → ℤ, ‖fourierCoeff f m‖ * ‖fourierCoeff W m‖ :=
            Summable.tsum_le_tsum
              (fun m => mul_le_mul_of_nonneg_left (htrunc_le m) (norm_nonneg _)) hprodn hFFW
      _ ≤ ∑' m : ι → ℤ, Ck * (X m * Z m) := hFFWle
      _ = Ck * ∑' m : ι → ℤ, X m * Z m := by rw [← tsum_mul_left]
      _ ≤ Ck * (Real.sqrt (∑' m : ι → ℤ, X m ^ 2) * Real.sqrt (∑' m : ι → ℤ, Z m ^ 2)) := by
            refine mul_le_mul_of_nonneg_left ?_ hCk0
            exact tsum_mul_le_sqrt_mul_sqrt X Z hXnn hZnn hX2sum hZ2sum
      _ ≤ Ck * (Real.sqrt (CSq (k - 1) (fourierCoeff f))
            * ((∑' l : ι → ℤ, Φ l) * Real.sqrt (CSq k (fourierCoeff u)))) := by
            rw [hsX, ← hsY]
            refine mul_le_mul_of_nonneg_left ?_ hCk0
            exact mul_le_mul_of_nonneg_left hsZ (Real.sqrt_nonneg _)
      _ ≤ Ck * (∑' l : ι → ℤ, Φ l) * Real.sqrt Cf * Real.sqrt Cu
            * Real.sqrt (ENormSq (k - 1) f + ENormSq 0 f)
            * Real.sqrt (ENormSq k u + ENormSq 0 u) := by
            have h1 : Real.sqrt (CSq (k - 1) (fourierCoeff f))
                * ((∑' l : ι → ℤ, Φ l) * Real.sqrt (CSq k (fourierCoeff u)))
                ≤ (Real.sqrt Cf * Real.sqrt (ENormSq (k - 1) f + ENormSq 0 f))
                  * ((∑' l : ι → ℤ, Φ l)
                    * (Real.sqrt Cu * Real.sqrt (ENormSq k u + ENormSq 0 u))) :=
              mul_le_mul hs1 (mul_le_mul_of_nonneg_left hs2 hSΦnn)
                (mul_nonneg hSΦnn (Real.sqrt_nonneg _))
                (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
            calc Ck * (Real.sqrt (CSq (k - 1) (fourierCoeff f))
                  * ((∑' l : ι → ℤ, Φ l) * Real.sqrt (CSq k (fourierCoeff u))))
                ≤ Ck * ((Real.sqrt Cf * Real.sqrt (ENormSq (k - 1) f + ENormSq 0 f))
                    * ((∑' l : ι → ℤ, Φ l)
                      * (Real.sqrt Cu * Real.sqrt (ENormSq k u + ENormSq 0 u)))) :=
                  mul_le_mul_of_nonneg_left h1 hCk0
              _ = Ck * (∑' l : ι → ℤ, Φ l) * Real.sqrt Cf * Real.sqrt Cu
                    * Real.sqrt (ENormSq (k - 1) f + ENormSq 0 f)
                    * Real.sqrt (ENormSq k u + ENormSq 0 u) := by ring

end Work.Diff.STE.B3
