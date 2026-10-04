import Mathlib
import Submission.Work.Diff.STE.FlatPDE
import Submission.Work.Diff.STE.flat.fourierCoeff_seriesFun
import Submission.Work.Diff.STE.CSq_le_ENormSq_seriesFun
import Submission.Work.Diff.STE.ENormSq_seriesFun_le
import Submission.Work.Diff.STE.norm_seriesFun_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Auxiliary coefficient estimates for the flat limit step of `limit_solves`

Reusable Layer-A estimates for `Work.Diff.STE.flat.limit_solves` (and for the lemmas it rests on):
the decay of coefficients from a weighted `ℓ²` bound, the `ℓ²` bound of a differentiated family,
and the sup bound for an iterated spatial derivative of a Fourier series.  Nothing here mentions
the tower or the limit; this module is meant to be imported freely.
-/

namespace Work.Diff.STE.flat

open Work.Diff.STE.Flat
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-- The energy is nonnegative. -/
lemma ENormSq_nonneg' (m : ℕ) (f : (Fin n → ℝ) → ℂ) : 0 ≤ Work.Diff.STE.ENormSq m f := by
  rw [Work.Diff.STE.ENormSq]
  exact Finset.sum_nonneg fun l _ => MeasureTheory.integral_nonneg fun x => by positivity

/-- The weighted `ℓ²` norm is nonnegative. -/
lemma limit_CSq_nonneg (s : ℕ) (γ : (Fin n → ℤ) → ℂ) : 0 ≤ Work.Diff.STE.CSq s γ := by
  rw [Work.Diff.STE.CSq]
  exact tsum_nonneg fun k => mul_nonneg (pow_nonneg (Work.Diff.STE.wt_pos k).le s) (sq_nonneg _)

/-- Entrywise Fourier inversion: the Fourier coefficients of the series of `c` are `c`. -/
lemma fourierCoeff_seriesFunM_apply {n : ℕ} {c : (Fin n → ℤ) → MatC n}
    (hs : ∀ i j : Fin n, Summable (fun k : (Fin n → ℤ) => ‖c k i j‖))
    (k : Fin n → ℤ) (i j : Fin n) :
    Work.Diff.STE.fourierCoeff (fun x : Fin n → ℝ => seriesFunM c x i j) k = c k i j := by
  have hfun : (fun x : Fin n → ℝ => seriesFunM c x i j)
      = Work.Diff.STE.seriesFun (fun k : Fin n → ℤ => c k i j) := by
    funext x; rw [seriesFunM_apply]
  rw [hfun]
  exact fourierCoeff_seriesFun (fun k => c k i j) (hs i j) k

/-- The level-`0` energy dominates each coefficient (squared). -/
lemma coeff_norm_sq_le_energy {n : ℕ} {c : (Fin n → ℤ) → MatC n}
    (hs : ∀ i j : Fin n, Summable (fun k : (Fin n → ℤ) => ‖c k i j‖))
    (k : Fin n → ℤ) (i j : Fin n) :
    ‖c k i j‖ ^ 2 ≤ ENormSqFull 0 (seriesFunM c) := by
  have hfun : Work.Diff.STE.seriesFun (fun m : Fin n → ℤ => c m i j)
      = fun x : Fin n → ℝ => seriesFunM c x i j := by
    funext x; rw [seriesFunM_apply]
  have h0 : ∑' m : Fin n → ℤ, ‖c m i j‖ ^ 2
      = Work.Diff.STE.ENormSq 0 (fun x : Fin n → ℝ => seriesFunM c x i j) := by
    rw [← Work.Diff.STE.ENormSq_zero_seriesFun (fun m => c m i j) (hs i j), hfun]
  have hsq : Summable (fun l : Fin n → ℤ => ‖c l i j‖ ^ 2) := by
    have hbdd : ∀ l, ‖c l i j‖ ≤ ∑' m : Fin n → ℤ, ‖c m i j‖ :=
      fun l => (hs i j).le_tsum l (fun _ _ => norm_nonneg _)
    have hdom : Summable (fun l : Fin n → ℤ => (∑' m : Fin n → ℤ, ‖c m i j‖) * ‖c l i j‖) :=
      (hs i j).mul_left _
    refine Summable.of_nonneg_of_le (fun l => sq_nonneg _) (fun l => ?_) hdom
    calc ‖c l i j‖ ^ 2 = ‖c l i j‖ * ‖c l i j‖ := by ring
      _ ≤ (∑' m : Fin n → ℤ, ‖c m i j‖) * ‖c l i j‖ :=
          mul_le_mul_of_nonneg_right (hbdd l) (norm_nonneg _)
  have hle : ‖c k i j‖ ^ 2 ≤ Work.Diff.STE.ENormSq 0 (fun x : Fin n → ℝ => seriesFunM c x i j) := by
    rw [← h0]
    exact hsq.le_tsum k (fun _ _ => sq_nonneg _)
  have h2 : Work.Diff.STE.ENormSq 0 (fun x : Fin n → ℝ => seriesFunM c x i j)
      ≤ ENormSqM 0 (seriesFunM c) := by
    rw [ENormSqM]
    refine le_trans (Finset.single_le_sum
      (f := fun j' : Fin n => Work.Diff.STE.ENormSq 0 (fun x : Fin n → ℝ => seriesFunM c x i j'))
      (fun j' _ => ENormSq_nonneg' 0 _) (Finset.mem_univ j)) ?_
    exact Finset.single_le_sum
      (f := fun i' : Fin n => ∑ j' : Fin n,
        Work.Diff.STE.ENormSq 0 (fun x : Fin n → ℝ => seriesFunM c x i' j'))
      (fun i' _ => Finset.sum_nonneg (fun j' _ => ENormSq_nonneg' 0 _))
      (Finset.mem_univ i)
  have h3 : ENormSqM 0 (seriesFunM c) ≤ ENormSqFull 0 (seriesFunM c) := by
    simp only [ENormSqFull]
    linarith [show (0 : ℝ) ≤ ENormSqM 0 (seriesFunM c) from by
      simp only [ENormSqM]
      exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ENormSq_nonneg' 0 _]
  linarith [hle, h2, h3]

/-- Pointwise decay of the coefficients from a weighted `ℓ²` bound. -/
lemma coeff_le_of_CSq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {c : (ι → ℤ) → ℂ} {M : ℕ} {B : ℝ}
    (hmom : ∀ N : ℕ, Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ N * ‖c k‖))
    (hB : 0 ≤ B)
    (h : Work.Diff.STE.CSq (2 * M) c ≤ B) :
    ∀ k : ι → ℤ, ‖c k‖ * (Work.Diff.STE.wt k) ^ M ≤ 1 + B := by
  intro k
  have hsum : Summable (fun l : ι → ℤ =>
      (Work.Diff.STE.wt l) ^ (2 * M) * ‖c l‖ ^ 2) :=
    Work.Diff.STE.summable_wt_pow_mul_norm_sq c hmom (2 * M)
  have hk : (Work.Diff.STE.wt k) ^ (2 * M) * ‖c k‖ ^ 2 ≤ B :=
    (hsum.le_tsum k (fun _ _ =>
      mul_nonneg (pow_nonneg (Work.Diff.STE.wt_pos _).le _) (sq_nonneg _))).trans h
  have h3 : (‖c k‖ * (Work.Diff.STE.wt k) ^ M) ^ 2 ≤ B := by
    rw [mul_pow, ← pow_mul]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hk
  nlinarith [sq_nonneg (‖c k‖ * (Work.Diff.STE.wt k) ^ M), h3, hB]

/-- `√a ≤ a` for `a ≥ 1`. -/
lemma sqrt_le_self_of_one_le {a : ℝ} (ha : 1 ≤ a) : Real.sqrt a ≤ a := by
  have h0 : 0 ≤ a := le_trans zero_le_one ha
  calc Real.sqrt a ≤ Real.sqrt (a ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    _ = a := Real.sqrt_sq h0

/-- `CSq` is monotone in the level. -/
lemma CSq_mono {ι : Type*} [Fintype ι] [DecidableEq ι] {γ : (ι → ℤ) → ℂ} {r r' : ℕ}
    (h : r ≤ r')
    (hs : ∀ N : ℕ, Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ N * ‖γ k‖)) :
    Work.Diff.STE.CSq r γ ≤ Work.Diff.STE.CSq r' γ := by
  rw [Work.Diff.STE.CSq, Work.Diff.STE.CSq]
  refine Summable.tsum_le_tsum (fun k => ?_)
    (Work.Diff.STE.summable_wt_pow_mul_norm_sq γ hs r)
    (Work.Diff.STE.summable_wt_pow_mul_norm_sq γ hs r')
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (Work.Diff.STE.wt_one_le k) h)
    (by positivity)

/-- The `CSq`-summability of a differentiated family. -/
lemma summable_CSq_dmulV (l : List (Fin n)) (γ : (Fin n → ℤ) → ℂ) (s : ℕ)
    (hmom : ∀ N : ℕ, Summable (fun k : (Fin n → ℤ) => (Work.Diff.STE.wt k) ^ N * ‖γ k‖)) :
    Summable (fun k : Fin n → ℤ =>
      (Work.Diff.STE.wt k) ^ s * ‖Work.Diff.STE.dmulV l γ k‖ ^ 2) := by
  have hdom : Summable (fun k : Fin n → ℤ =>
      (Work.Diff.STE.wt k) ^ s
        * ((((2 * Real.pi) ^ 2) * Work.Diff.STE.wt k) ^ l.length * ‖γ k‖ ^ 2)) :=
    ((Work.Diff.STE.summable_wt_pow_mul_norm_sq γ hmom (s + l.length)).mul_left
      (((2 * Real.pi) ^ 2) ^ l.length)).congr fun k => by rw [mul_pow, pow_add]; ring
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (pow_nonneg (Work.Diff.STE.wt_pos k).le s) (sq_nonneg _))
    (fun k => ?_) hdom
  exact mul_le_mul_of_nonneg_left (Work.Diff.STE.norm_sq_dmulV_le l γ k)
    (pow_nonneg (Work.Diff.STE.wt_pos k).le s)

/-- The `CSq` norm of a differentiated family. -/
lemma lim_CSq_dmulV_le (l : List (Fin n)) (γ : (Fin n → ℤ) → ℂ) (s : ℕ)
    (hmom : ∀ N : ℕ, Summable (fun k : (Fin n → ℤ) => (Work.Diff.STE.wt k) ^ N * ‖γ k‖)) :
    Work.Diff.STE.CSq s (Work.Diff.STE.dmulV l γ)
      ≤ ((2 * Real.pi) ^ 2) ^ l.length * Work.Diff.STE.CSq (s + l.length) γ := by
  have hdom : Summable (fun k : Fin n → ℤ =>
      (Work.Diff.STE.wt k) ^ s
        * ((((2 * Real.pi) ^ 2) * Work.Diff.STE.wt k) ^ l.length * ‖γ k‖ ^ 2)) :=
    ((Work.Diff.STE.summable_wt_pow_mul_norm_sq γ hmom (s + l.length)).mul_left
      (((2 * Real.pi) ^ 2) ^ l.length)).congr fun k => by rw [mul_pow, pow_add]; ring
  rw [Work.Diff.STE.CSq, Work.Diff.STE.CSq]
  refine (Summable.tsum_le_tsum (fun k => ?_) (summable_CSq_dmulV l γ s hmom) hdom).trans
    (le_of_eq ?_)
  · exact mul_le_mul_of_nonneg_left (Work.Diff.STE.norm_sq_dmulV_le l γ k)
      (pow_nonneg (Work.Diff.STE.wt_pos k).le s)
  · rw [← tsum_mul_left]
    exact tsum_congr fun k => by rw [mul_pow, pow_add]; ring

/-- Sup bound for an iterated derivative of a Fourier series in terms of a weighted `ℓ²` norm. -/
lemma sup_pdList_le (s K : ℕ) (hs : n < 2 * s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (γ : (Fin n → ℤ) → ℂ),
      (∀ N : ℕ, Summable (fun k : (Fin n → ℤ) => (Work.Diff.STE.wt k) ^ N * ‖γ k‖)) →
      ∀ (l : List (Fin n)), l.length ≤ K → ∀ x : Fin n → ℝ,
        ‖Work.Diff.STE.pdList l (Work.Diff.STE.seriesFun γ) x‖
          ≤ C * Real.sqrt (Work.Diff.STE.CSq (s + K) γ) := by
  obtain ⟨C₁, hC₁, hC₁b⟩ := Work.Diff.STE.norm_seriesFun_le (ι := Fin n) s (by simpa using hs)
  refine ⟨C₁ * ((2 * Real.pi) ^ 2) ^ K, by positivity, fun γ hmom l hl x => ?_⟩
  rw [Work.Diff.STE.pdList_seriesFun l γ hmom x]
  have hK1 : 1 ≤ ((2 * Real.pi) ^ 2 : ℝ) ^ K := by
    refine one_le_pow₀ ?_
    nlinarith [Real.pi_gt_three]
  have hKnn : (0 : ℝ) ≤ ((2 * Real.pi) ^ 2) ^ K := by positivity
  have h1 : ‖Work.Diff.STE.seriesFun (Work.Diff.STE.dmulV l γ) x‖
      ≤ C₁ * Real.sqrt (Work.Diff.STE.CSq s (Work.Diff.STE.dmulV l γ)) :=
    hC₁b _ (summable_CSq_dmulV l γ s hmom) x
  have h2 : Work.Diff.STE.CSq s (Work.Diff.STE.dmulV l γ)
      ≤ ((2 * Real.pi) ^ 2) ^ K * Work.Diff.STE.CSq (s + K) γ := by
    refine (lim_CSq_dmulV_le l γ s hmom).trans ?_
    have hpow : ((2 * Real.pi) ^ 2) ^ l.length ≤ ((2 * Real.pi) ^ 2) ^ K :=
      pow_le_pow_right₀ (by nlinarith [Real.pi_gt_three]) hl
    have hmono : Work.Diff.STE.CSq (s + l.length) γ ≤ Work.Diff.STE.CSq (s + K) γ :=
      CSq_mono (by omega) hmom
    exact mul_le_mul hpow hmono (limit_CSq_nonneg (s + l.length) γ) hKnn
  have h4 : Real.sqrt (Work.Diff.STE.CSq s (Work.Diff.STE.dmulV l γ))
      ≤ ((2 * Real.pi) ^ 2) ^ K * Real.sqrt (Work.Diff.STE.CSq (s + K) γ) := by
    have h5 : Real.sqrt (Work.Diff.STE.CSq s (Work.Diff.STE.dmulV l γ))
        ≤ Real.sqrt (((2 * Real.pi) ^ 2) ^ K * Work.Diff.STE.CSq (s + K) γ) :=
      Real.sqrt_le_sqrt h2
    rw [Real.sqrt_mul hKnn] at h5
    exact h5.trans (mul_le_mul_of_nonneg_right (sqrt_le_self_of_one_le hK1)
      (Real.sqrt_nonneg _))
  have h5 : C₁ * Real.sqrt (Work.Diff.STE.CSq s (Work.Diff.STE.dmulV l γ))
      ≤ C₁ * ((2 * Real.pi) ^ 2) ^ K * Real.sqrt (Work.Diff.STE.CSq (s + K) γ) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left h4 hC₁
  exact h1.trans h5

end

end Work.Diff.STE.flat
