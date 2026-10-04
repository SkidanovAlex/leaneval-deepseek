import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.flat.limit_aux
import Submission.Work.Diff.STE.flat.seriesFun_fourierCoeff
import Submission.Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff
import Submission.Work.Diff.STE.ENormSq_seriesFun_le
import Submission.Work.Diff.STE.summable_norm_of_CSq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Pointwise bounds for iterated partial derivatives of a smooth function on the torus

This file proves the general-`ι` Sobolev sup bound for iterated partial derivatives of a smooth,
`1`-periodic function on the flat torus `(ι → ℝ)/(ℤ^ι)`:

  `‖pdList l f x‖ ≤ C · √(CSq k (fourierCoeff f))`

for every list of directions `l` of length `≤ m` and every `x`, provided `k` is above the critical
Sobolev order for `m` derivatives in `card ι` dimensions, i.e. `card ι + 2 m < 2 k`.

The proof is the standard Fourier argument, assembled from the Layer-A toolkit:

* **Fourier inversion** `flat.seriesFun_fourierCoeff`: a smooth `1`-periodic `f` is the Fourier
  series of its coefficients; and `pdList_seriesFun`: the iterated derivative of a series is the
  series of the differentiated coefficients, `dmulV l c` (multiplication of the `k`-th coefficient
  by `∏_{i ∈ l} 2πi kᵢ`).
* **Sobolev embedding step** `norm_seriesFun_le`: for `card ι < 2 s` the series `seriesFun c` is
  bounded pointwise by `C √(CSq s c)`, by Cauchy–Schwarz against the summable dual weight
  `⟨k⟩^{-2s}`.
* **Weight accounting**: the derivative multiplier of a list of length `≤ m` raises the required
  weight from `⟨k⟩^{k}` to `⟨k⟩^{k-m}` (each `|kᵢ| ≤ ⟨k⟩`, and `2m ≤ 2k - card ι` leaves room for
  the embedding), giving the constant `((2π)²)^m`.

The two ingredient lemmas `summable_CSq_dmulV_gen`, `CSq_dmulV_le_gen` and `sup_pdList_le_gen` are
the general-`ι` forms of `Work.Diff.STE.flat.summable_CSq_dmulV`, `flat.lim_CSq_dmulV_le` and
`flat.sup_pdList_le` (which are stated for `Fin n`).
-/

noncomputable section

namespace Work.Diff.STE.B3

open Work.Diff.STE

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Elementary norm computations -/

private lemma norm_ofReal_cast' (x : ℝ) : ‖((x : ℝ) : ℂ)‖ = |x| := by
  have h : ‖((x : ℝ) : ℂ)‖ ^ 2 = x ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
    ring
  calc ‖((x : ℝ) : ℂ)‖ = Real.sqrt (‖((x : ℝ) : ℂ)‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (x ^ 2) := by rw [h]
    _ = |x| := Real.sqrt_sq_eq_abs x

/-- `‖⟨k⟩^N · z‖ = ⟨k⟩^N ‖z‖` for the real weight `⟨k⟩ = wt k ≥ 1 > 0`. -/
private lemma norm_wt_pow_mul' (N : ℕ) (k : ι → ℤ) (z : ℂ) :
    ‖(wt k) ^ N * z‖ = (wt k) ^ N * ‖z‖ := by
  rw [norm_mul, norm_pow, norm_ofReal_cast', abs_of_nonneg (wt_pos k).le]

/-- The weight shift: multiplying the coefficient by `⟨k⟩^N` shifts the `CSq`-weight up by `2N`. -/
private lemma wt_pow_mul_norm_sq' (s N : ℕ) (k : ι → ℤ) (z : ℂ) :
    (wt k) ^ s * ‖(wt k) ^ N * z‖ ^ 2 = (wt k) ^ (s + 2 * N) * ‖z‖ ^ 2 := by
  have hexp : s + N * 2 = s + 2 * N := by omega
  rw [norm_wt_pow_mul', mul_pow, ← pow_mul, ← mul_assoc, ← pow_add, hexp]

/-- **Weighted `ℓ¹` summability of the Fourier coefficients of a smooth `1`-periodic
function.**  Every weight `⟨k⟩^N` times the modulus of the `k`-th Fourier coefficient is
summable: this is the rapid decay hypothesis required by `pdList_seriesFun`. -/
private lemma summable_wt_pow_norm_fourierCoeff (f : (ι → ℝ) → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hper : Periodic1 f) (N : ℕ) :
    Summable (fun k : ι → ℤ => (wt k) ^ N * ‖fourierCoeff f k‖) := by
  obtain ⟨s, hs⟩ : ∃ s : ℕ, Fintype.card ι < 2 * s := ⟨Fintype.card ι + 1, by omega⟩
  have hcsq : Summable (fun k : ι → ℤ => (wt k) ^ s * ‖(wt k) ^ N * fourierCoeff f k‖ ^ 2) := by
    refine (summable_weighted_fourierCoeff_of_contDiff f hf hper (s + 2 * N)).congr
      (fun k => ?_)
    exact (wt_pow_mul_norm_sq' s N k (fourierCoeff f k)).symm
  have hnorm := summable_norm_of_CSq s hs (fun k : ι → ℤ => (wt k) ^ N * fourierCoeff f k) hcsq
  refine hnorm.congr (fun k => ?_)
  exact norm_wt_pow_mul' N k (fourierCoeff f k)

/-! ## The differentiated family and its weighted mass -/

/-- `CSq` is nonnegative. -/
private lemma CSq_nonneg' (s : ℕ) (γ : (ι → ℤ) → ℂ) : 0 ≤ CSq s γ := by
  rw [CSq]
  exact tsum_nonneg fun k => mul_nonneg (pow_nonneg (wt_pos k).le s) (sq_nonneg _)

/-- The `CSq`-summability of a differentiated family, in general dimension. -/
private lemma summable_CSq_dmulV_gen (l : List ι) (γ : (ι → ℤ) → ℂ) (s : ℕ)
    (hmom : ∀ N : ℕ, Summable (fun k : ι → ℤ => (wt k) ^ N * ‖γ k‖)) :
    Summable (fun k : ι → ℤ => (wt k) ^ s * ‖dmulV l γ k‖ ^ 2) := by
  have hdom : Summable (fun k : ι → ℤ =>
      (wt k) ^ s * ((((2 * Real.pi) ^ 2) * wt k) ^ l.length * ‖γ k‖ ^ 2)) :=
    ((summable_wt_pow_mul_norm_sq γ hmom (s + l.length)).mul_left
      (((2 * Real.pi) ^ 2) ^ l.length)).congr fun k => by rw [mul_pow, pow_add]; ring
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (pow_nonneg (wt_pos k).le s) (sq_nonneg _))
    (fun k => ?_) hdom
  exact mul_le_mul_of_nonneg_left (norm_sq_dmulV_le l γ k) (pow_nonneg (wt_pos k).le s)

/-- The `CSq` norm of a differentiated family, in general dimension. -/
private lemma CSq_dmulV_le_gen (l : List ι) (γ : (ι → ℤ) → ℂ) (s : ℕ)
    (hmom : ∀ N : ℕ, Summable (fun k : ι → ℤ => (wt k) ^ N * ‖γ k‖)) :
    CSq s (dmulV l γ) ≤ ((2 * Real.pi) ^ 2) ^ l.length * CSq (s + l.length) γ := by
  have hdom : Summable (fun k : ι → ℤ =>
      (wt k) ^ s * ((((2 * Real.pi) ^ 2) * wt k) ^ l.length * ‖γ k‖ ^ 2)) :=
    ((summable_wt_pow_mul_norm_sq γ hmom (s + l.length)).mul_left
      (((2 * Real.pi) ^ 2) ^ l.length)).congr fun k => by rw [mul_pow, pow_add]; ring
  rw [CSq, CSq]
  refine (Summable.tsum_le_tsum (fun k => ?_) (summable_CSq_dmulV_gen l γ s hmom) hdom).trans
    (le_of_eq ?_)
  · exact mul_le_mul_of_nonneg_left (norm_sq_dmulV_le l γ k)
      (pow_nonneg (wt_pos k).le s)
  · rw [← tsum_mul_left]
    exact tsum_congr fun k => by rw [mul_pow, pow_add]; ring

/-! ## The sup bound for iterated derivatives of a Fourier series -/

/-- Sup bound for an iterated derivative of a Fourier series in terms of a weighted `ℓ²` norm,
in general dimension. -/
private lemma sup_pdList_le_gen (s K : ℕ) (hs : Fintype.card ι < 2 * s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (γ : (ι → ℤ) → ℂ),
      (∀ N : ℕ, Summable (fun k : ι → ℤ => (wt k) ^ N * ‖γ k‖)) →
      ∀ (l : List ι), l.length ≤ K → ∀ x : ι → ℝ,
        ‖pdList l (seriesFun γ) x‖ ≤ C * Real.sqrt (CSq (s + K) γ) := by
  obtain ⟨C₁, hC₁, hC₁b⟩ := norm_seriesFun_le (ι := ι) s hs
  refine ⟨C₁ * ((2 * Real.pi) ^ 2) ^ K, by positivity, fun γ hmom l hl x => ?_⟩
  rw [pdList_seriesFun l γ hmom x]
  have hK1 : 1 ≤ ((2 * Real.pi) ^ 2 : ℝ) ^ K := by
    refine one_le_pow₀ ?_
    nlinarith [Real.pi_gt_three]
  have hKnn : (0 : ℝ) ≤ ((2 * Real.pi) ^ 2) ^ K := by positivity
  have h1 : ‖seriesFun (dmulV l γ) x‖
      ≤ C₁ * Real.sqrt (CSq s (dmulV l γ)) :=
    hC₁b _ (summable_CSq_dmulV_gen l γ s hmom) x
  have h2 : CSq s (dmulV l γ) ≤ ((2 * Real.pi) ^ 2) ^ K * CSq (s + K) γ := by
    refine (CSq_dmulV_le_gen l γ s hmom).trans ?_
    have hpow : ((2 * Real.pi) ^ 2) ^ l.length ≤ ((2 * Real.pi) ^ 2) ^ K :=
      pow_le_pow_right₀ (by nlinarith [Real.pi_gt_three]) hl
    have hmono : CSq (s + l.length) γ ≤ CSq (s + K) γ :=
      flat.CSq_mono (by omega) hmom
    exact mul_le_mul hpow hmono (CSq_nonneg' (s + l.length) γ) hKnn
  have h4 : Real.sqrt (CSq s (dmulV l γ))
      ≤ ((2 * Real.pi) ^ 2) ^ K * Real.sqrt (CSq (s + K) γ) := by
    have h5 : Real.sqrt (CSq s (dmulV l γ))
        ≤ Real.sqrt (((2 * Real.pi) ^ 2) ^ K * CSq (s + K) γ) :=
      Real.sqrt_le_sqrt h2
    rw [Real.sqrt_mul hKnn] at h5
    exact h5.trans (mul_le_mul_of_nonneg_right (flat.sqrt_le_self_of_one_le hK1)
      (Real.sqrt_nonneg _))
  have h5 : C₁ * Real.sqrt (CSq s (dmulV l γ))
      ≤ C₁ * ((2 * Real.pi) ^ 2) ^ K * Real.sqrt (CSq (s + K) γ) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left h4 hC₁
  exact h1.trans h5

/-! ## The target -/

theorem pdList_le_sqrt_CSq {ι : Type*} [Fintype ι] [DecidableEq ι] (k m : ℕ)
    (hm : Fintype.card ι + 2 * m < 2 * k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : (ι → ℝ) → ℂ), ContDiff ℝ (⊤ : ℕ∞) f → Work.Diff.STE.Periodic1 f →
      ∀ (l : List ι), l.length ≤ m → ∀ x : ι → ℝ,
        ‖Work.Diff.STE.pdList l f x‖ ≤ C * Real.sqrt (Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff f)) := by
  have hs : Fintype.card ι < 2 * (k - m) := by omega
  obtain ⟨C, hC, hCb⟩ := sup_pdList_le_gen (ι := ι) (k - m) m hs
  refine ⟨C, hC, fun f hf hper l hl x => ?_⟩
  have hmom : ∀ N : ℕ, Summable (fun kk : ι → ℤ => (wt kk) ^ N * ‖fourierCoeff f kk‖) :=
    summable_wt_pow_norm_fourierCoeff f hf hper
  have hser : seriesFun (fourierCoeff f) = f :=
    funext fun y => flat.seriesFun_fourierCoeff f hf hper y
  have h1 := hCb (fourierCoeff f) hmom l hl x
  rw [show k - m + m = k from by omega] at h1
  rw [hser] at h1
  exact h1

end Work.Diff.STE.B3
