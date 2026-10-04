import Mathlib
import Submission.Work.Diff.STE.B3.SymCalcStep8.CSqZ
import Submission.Work.Diff.STE.integral_seriesFun_mul_conj
import Submission.Work.Diff.STE.flat.seriesFun_fourierCoeff
import Submission.Work.Diff.STE.summable_norm_of_CSq
import Submission.Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff
import Submission.Work.Diff.STE.tsum_sqrt_mul_sqrt_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Weighted Cauchy–Schwarz / Parseval for the `L²` pairing

The target of this file is the weighted Cauchy–Schwarz inequality

  `|L2re y W| ≤ √(CSqZ t (fourierCoeff y)) · √(CSqZ (-t) (fourierCoeff W))`

for smooth `1`-periodic `y W : (ι → ℝ) → ℂ` and an arbitrary integer exponent `t` (one of the two
indices in the product has to be allowed to be negative, which is why `CSqZ` is stated with `ℤ`
exponents).

The proof has two halves.

* **Parseval on the coefficient side.**  For smooth `1`-periodic functions the `L²` pairing is the
  pairing of the coefficient families,
  `L2re y W = re (Σ_k ŷ(k) · conj(ŵ(k)))`, (`L2re_eq_tsum_fourierCoeff`).  This is Parseval's
  identity, assembled from Fourier inversion (`seriesFun_fourierCoeff`) and the orthogonality of
  the characters (`integral_seriesFun_mul_conj`).
* **Weighted Cauchy–Schwarz on `ℓ²(ℤ^ι)`.**  Splitting
  `‖ŷ k‖·‖ŵ k‖ = √(wt k ^ t ‖ŷ k‖²) · √(wt k ^ (-t) ‖ŵ k‖²)` and applying the finite-set
  Cauchy–Schwarz `tsum_sqrt_mul_sqrt_le` gives the weighted bound; the two sums are precisely
  `CSqZ t (fourierCoeff y)` and `CSqZ (-t) (fourierCoeff W)`.

All summability inputs come from `summable_weighted_fourierCoeff_of_contDiff` (the `H^s` weighted
`ℓ²` summability of the coefficients of a smooth periodic function).
-/

noncomputable section

open scoped BigOperators

namespace Work.Diff.STE.B3.SymCalcStep8

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **`ℓ¹` summability of the Fourier coefficients of a smooth `1`-periodic function.** -/
lemma summable_norm_fourierCoeff_of_contDiff (f : (ι → ℝ) → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfp : Work.Diff.STE.Periodic1 f) :
    Summable (fun k : ι → ℤ => ‖Work.Diff.STE.fourierCoeff f k‖) := by
  obtain ⟨s, hs⟩ : ∃ s : ℕ, Fintype.card ι < 2 * s := ⟨Fintype.card ι + 1, by omega⟩
  exact Work.Diff.STE.summable_norm_of_CSq s hs (Work.Diff.STE.fourierCoeff f)
    (Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff f hf hfp s)

/-- **Parseval's identity for the `L2re` pairing.**  For smooth `1`-periodic `f`, `g`,

  `L2re f g = re (Σ_k f̂(k) · conj(ĝ(k)))`. -/
lemma L2re_eq_tsum_fourierCoeff (f g : (ι → ℝ) → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfp : Work.Diff.STE.Periodic1 f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgp : Work.Diff.STE.Periodic1 g) :
    Work.Diff.STE.L2re f g
      = (∑' k : ι → ℤ, Work.Diff.STE.fourierCoeff f k
          * star (Work.Diff.STE.fourierCoeff g k)).re := by
  have hf1 : Summable (fun k : ι → ℤ => ‖Work.Diff.STE.fourierCoeff f k‖) :=
    summable_norm_fourierCoeff_of_contDiff f hf hfp
  have hg1 : Summable (fun k : ι → ℤ => ‖Work.Diff.STE.fourierCoeff g k‖) :=
    summable_norm_fourierCoeff_of_contDiff g hg hgp
  have hL : Work.Diff.STE.L2re f g
      = Work.Diff.STE.L2re (Work.Diff.STE.seriesFun (Work.Diff.STE.fourierCoeff f))
          (Work.Diff.STE.seriesFun (Work.Diff.STE.fourierCoeff g)) := by
    simp only [Work.Diff.STE.L2re]
    congr 1
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => by
      simp only [Work.Diff.STE.flat.seriesFun_fourierCoeff f hf hfp x,
        Work.Diff.STE.flat.seriesFun_fourierCoeff g hg hgp x])
  rw [hL, Work.Diff.STE.L2re,
    Work.Diff.STE.integral_seriesFun_mul_conj _ _ hf1 hg1]

/-- **Summability of `wt^t ‖c‖²` from summability of `wt^s ‖c‖²` for an exponent `s ≥ t`.**
Since `wt ≥ 1`, the integer power `wt ^ t` is dominated by the natural power `wt ^ s`. -/
lemma summable_wt_zpow_mul_normSq (c : (ι → ℤ) → ℂ) (t : ℤ) (s : ℕ) (hts : t ≤ (s : ℤ))
    (h : Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ s * ‖c k‖ ^ 2)) :
    Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ t * ‖c k‖ ^ 2) := by
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (zpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) t) (sq_nonneg _))
    (fun k => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)) h
  calc (Work.Diff.STE.wt k) ^ t ≤ (Work.Diff.STE.wt k) ^ (s : ℤ) :=
        zpow_le_zpow_right₀ (Work.Diff.STE.wt_one_le k) hts
    _ = (Work.Diff.STE.wt k) ^ s := zpow_natCast (Work.Diff.STE.wt k) s

/-- `√(w^t) · √(w^{-t}) = 1` for `w > 0`. -/
lemma sqrt_zpow_mul_sqrt_zpow_neg (w : ℝ) (hw : 0 < w) (t : ℤ) :
    Real.sqrt (w ^ t) * Real.sqrt (w ^ (-t)) = 1 := by
  have h1 : 0 ≤ w ^ t := zpow_nonneg hw.le t
  have h2 : 0 ≤ w ^ (-t) := zpow_nonneg hw.le (-t)
  rw [← Real.sqrt_mul h1 (w ^ (-t))]
  have h3 : w ^ t * w ^ (-t) = 1 := by
    rw [← zpow_add₀ (ne_of_gt hw), add_neg_cancel, zpow_zero]
  rw [h3, Real.sqrt_one]

/-- The pointwise weight split: `√(wt^t ‖a‖²) · √(wt^{-t} ‖b‖²) = ‖a‖ · ‖b‖`. -/
lemma sqrt_wt_zpow_mul_sqrt_wt_zpow_neg (k : ι → ℤ) (a b : ℂ) (t : ℤ) :
    Real.sqrt ((Work.Diff.STE.wt k) ^ t * ‖a‖ ^ 2)
        * Real.sqrt ((Work.Diff.STE.wt k) ^ (-t) * ‖b‖ ^ 2) = ‖a‖ * ‖b‖ := by
  have hw : 0 < Work.Diff.STE.wt k := Work.Diff.STE.wt_pos k
  have h1 : 0 ≤ (Work.Diff.STE.wt k) ^ t := zpow_nonneg hw.le t
  have h2 : 0 ≤ (Work.Diff.STE.wt k) ^ (-t) := zpow_nonneg hw.le (-t)
  rw [Real.sqrt_mul h1 (‖a‖ ^ 2), Real.sqrt_mul h2 (‖b‖ ^ 2),
    Real.sqrt_sq (norm_nonneg a), Real.sqrt_sq (norm_nonneg b)]
  calc Real.sqrt ((Work.Diff.STE.wt k) ^ t) * ‖a‖
        * (Real.sqrt ((Work.Diff.STE.wt k) ^ (-t)) * ‖b‖)
      = (Real.sqrt ((Work.Diff.STE.wt k) ^ t) * Real.sqrt ((Work.Diff.STE.wt k) ^ (-t)))
          * (‖a‖ * ‖b‖) := by ring
    _ = ‖a‖ * ‖b‖ := by rw [sqrt_zpow_mul_sqrt_zpow_neg _ hw t, one_mul]

/-- **Weighted Cauchy–Schwarz on `ℓ²(ℤ^ι)`**: for a coefficient family `c` with summable
`Σ_k wt k ^ t ‖c k‖²` and `d` with summable `Σ_k wt k ^ (-t) ‖d k‖²`, the `ℓ¹` pairing is
controlled by the product of the two weighted `ℓ²` norms. -/
lemma tsum_norm_mul_le_sqrt_CSqZ (t : ℤ) (c d : (ι → ℤ) → ℂ)
    (hc : Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ t * ‖c k‖ ^ 2))
    (hd : Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ (-t) * ‖d k‖ ^ 2)) :
    (∑' k : ι → ℤ, ‖c k‖ * ‖d k‖)
      ≤ Real.sqrt (∑' k : ι → ℤ, (Work.Diff.STE.wt k) ^ t * ‖c k‖ ^ 2)
        * Real.sqrt (∑' k : ι → ℤ, (Work.Diff.STE.wt k) ^ (-t) * ‖d k‖ ^ 2) := by
  have h := Work.Diff.STE.tsum_sqrt_mul_sqrt_le (A := fun k : ι → ℤ =>
        (Work.Diff.STE.wt k) ^ t * ‖c k‖ ^ 2)
      (B := fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ (-t) * ‖d k‖ ^ 2) hc hd
      (fun k => mul_nonneg (zpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) t) (sq_nonneg _))
      (fun k => mul_nonneg (zpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) (-t)) (sq_nonneg _))
  calc (∑' k : ι → ℤ, ‖c k‖ * ‖d k‖)
      = ∑' k : ι → ℤ, Real.sqrt ((Work.Diff.STE.wt k) ^ t * ‖c k‖ ^ 2)
          * Real.sqrt ((Work.Diff.STE.wt k) ^ (-t) * ‖d k‖ ^ 2) :=
        tsum_congr fun k => (sqrt_wt_zpow_mul_sqrt_wt_zpow_neg k (c k) (d k) t).symm
    _ ≤ Real.sqrt (∑' k : ι → ℤ, (Work.Diff.STE.wt k) ^ t * ‖c k‖ ^ 2)
        * Real.sqrt (∑' k : ι → ℤ, (Work.Diff.STE.wt k) ^ (-t) * ‖d k‖ ^ 2) := h

theorem L2re_le_sqrt_CSqZ {ι : Type*} [Fintype ι] [DecidableEq ι] (t : ℤ)
    (y W : (ι → ℝ) → ℂ) (hy : ContDiff ℝ (⊤ : ℕ∞) y) (hyp : Work.Diff.STE.Periodic1 y)
    (hW : ContDiff ℝ (⊤ : ℕ∞) W) (hWp : Work.Diff.STE.Periodic1 W) :
    |Work.Diff.STE.L2re y W|
      ≤ Real.sqrt (Work.Diff.STE.B3.SymCalcStep8.CSqZ t (Work.Diff.STE.fourierCoeff y))
        * Real.sqrt (Work.Diff.STE.B3.SymCalcStep8.CSqZ (-t) (Work.Diff.STE.fourierCoeff W)) := by
  have hy1 : Summable (fun k : ι → ℤ => ‖Work.Diff.STE.fourierCoeff y k‖) :=
    summable_norm_fourierCoeff_of_contDiff y hy hyp
  have hW1 : Summable (fun k : ι → ℤ => ‖Work.Diff.STE.fourierCoeff W k‖) :=
    summable_norm_fourierCoeff_of_contDiff W hW hWp
  -- Parseval: the `L²` pairing is the coefficient pairing.
  have hL := L2re_eq_tsum_fourierCoeff y W hy hyp hW hWp
  -- Summability of the pointwise product of the two coefficient families.
  have hprod : Summable (fun k : ι → ℤ => ‖Work.Diff.STE.fourierCoeff y k
      * star (Work.Diff.STE.fourierCoeff W k)‖) := by
    have hB : ∀ k : ι → ℤ,
        ‖Work.Diff.STE.fourierCoeff y k‖ ≤ ∑' l, ‖Work.Diff.STE.fourierCoeff y l‖ :=
      fun k => hy1.le_tsum k (fun l _ => norm_nonneg _)
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
      (hW1.mul_left (∑' l, ‖Work.Diff.STE.fourierCoeff y l‖))
    rw [norm_mul, norm_star]
    exact mul_le_mul_of_nonneg_right (hB k) (norm_nonneg _)
  -- Step 1: `|L2re y W| ≤ Σ_k ‖ŷ k‖ ‖ŵ k‖`.
  have hbound1 : |Work.Diff.STE.L2re y W|
      ≤ ∑' k : ι → ℤ, ‖Work.Diff.STE.fourierCoeff y k‖ * ‖Work.Diff.STE.fourierCoeff W k‖ := by
    rw [hL]
    calc |(∑' k : ι → ℤ, Work.Diff.STE.fourierCoeff y k
            * star (Work.Diff.STE.fourierCoeff W k)).re|
        ≤ ‖∑' k : ι → ℤ, Work.Diff.STE.fourierCoeff y k
            * star (Work.Diff.STE.fourierCoeff W k)‖ := Complex.abs_re_le_norm _
      _ ≤ ∑' k : ι → ℤ, ‖Work.Diff.STE.fourierCoeff y k
            * star (Work.Diff.STE.fourierCoeff W k)‖ := norm_tsum_le_tsum_norm hprod
      _ = ∑' k : ι → ℤ, ‖Work.Diff.STE.fourierCoeff y k‖
            * ‖Work.Diff.STE.fourierCoeff W k‖ :=
          tsum_congr fun k => by rw [norm_mul, norm_star]
  -- The two weighted `ℓ²` sums are summable.
  have hCsqA : Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ t
      * ‖Work.Diff.STE.fourierCoeff y k‖ ^ 2) :=
    summable_wt_zpow_mul_normSq (Work.Diff.STE.fourierCoeff y) t t.natAbs Int.le_natAbs
      (Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff y hy hyp t.natAbs)
  have hCsqB : Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ (-t)
      * ‖Work.Diff.STE.fourierCoeff W k‖ ^ 2) :=
    summable_wt_zpow_mul_normSq (Work.Diff.STE.fourierCoeff W) (-t) t.natAbs
      (by have h := Int.le_natAbs (a := -t); rwa [Int.natAbs_neg] at h)
      (Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff W hW hWp t.natAbs)
  -- Step 2: weighted Cauchy–Schwarz.
  refine hbound1.trans ((tsum_norm_mul_le_sqrt_CSqZ t _ _ hCsqA hCsqB).trans (le_of_eq ?_))
  simp only [Work.Diff.STE.B3.SymCalcStep8.CSqZ]

end Work.Diff.STE.B3.SymCalcStep8
