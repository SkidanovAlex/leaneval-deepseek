import Mathlib
import Submission.Hypercube.Resample
import Submission.Commons.Analysis.Walsh.sum_norm_sq_chi_orthogonal
import Submission.Commons.Analysis.Walsh.sum_norm_sq_chi_orthogonal_index

/-!
# The involutions/Parseval layer for the `𝔽₂ⁿ` warm-up chapter (Lemma 2.10)

This file collects the `mu`-Parseval lemma and Lemma 2.10 of arXiv:2209.04243; it is split
off while the commons lemma `sum_norm_sq_chi_orthogonal_index` is being proved.
-/

open Finset BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Hypercube

noncomputable section

variable {n : ℕ}

/-- **Parseval for `mu`** on sums of multiples of distinct characters. -/
theorem mu_sum_smul_chi (s : Finset (Finset (Fin n))) (a : Finset (Fin n) → ℂ)
    (R : Finset (Fin n) → Finset (Fin n))
    (hinj : ∀ T ∈ s, ∀ U ∈ s, R T = R U → T = U) :
    mu (∑ T ∈ s, a T • chi (R T)) = ∑ T ∈ s, ‖a T‖ ^ 2 := by
  have hpw : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  rw [mu]
  have hpt : ∀ x : Fin n → ZMod 2,
      ‖(∑ T ∈ s, a T • chi (R T)) x‖
        = ‖∑ T ∈ s, a T * ∏ i ∈ R T, ZMod.stdAddChar (x i)‖ := by
    intro x
    congr 1
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun T _ => by rw [Pi.smul_apply, smul_eq_mul, chi]
  rw [show (∑ x : Fin n → ZMod 2, ‖(∑ T ∈ s, a T • chi (R T)) x‖ ^ 2)
      = ∑ x : Fin n → ZMod 2,
          ‖∑ T ∈ s, a T * ∏ i ∈ R T, ZMod.stdAddChar (x i)‖ ^ 2 from
    Finset.sum_congr rfl fun x _ => by rw [hpt x]]
  rw [Commons.Analysis.Walsh.sum_norm_sq_chi_orthogonal_index s a R hinj]
  rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hpw), one_mul]

/-- **Lemma 2.10 of arXiv:2209.04243**: the influence of `(S, x)` decomposes over the
Efron--Stein components above `S`. -/
theorem inflPair_efronStein_sum (S : Finset (Fin n)) (x : Fin n → ZMod 2)
    (f : (Fin n → ZMod 2) → ℂ) :
    inflPair S x f = ∑ T ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun T => S ⊆ T),
      inflPair S x (efronStein f T) := by
  have hR : ∀ T ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun T => S ⊆ T),
      Dfun S x (efronStein f T) = (efronCoeff f T * chi S x) • chi (T \ S) := by
    intro T hT
    have hST : S ⊆ T := (Finset.mem_filter.mp hT).2
    rw [Dfun_eq_sum]
    rw [Finset.sum_eq_single T]
    · rw [efronCoeff_efronStein, if_pos rfl]
    · intro U hU hUT
      rw [efronCoeff_efronStein, if_neg (fun h => hUT h), zero_mul, zero_smul]
    · intro hmem
      exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp hT).2⟩) hmem
  rw [inflPair, Dfun_eq_sum]
  rw [mu_sum_smul_chi _ _ (fun T => T \ S)]
  · rw [show (∑ T ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun T => S ⊆ T),
          inflPair S x (efronStein f T))
        = ∑ T ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun T => S ⊆ T),
            ‖efronCoeff f T * chi S x‖ ^ 2 from
      Finset.sum_congr rfl fun T hT => by rw [inflPair, hR T hT, mu_smul_chi]]
  · intro T hT U hU h
    exact sdiff_inj_of_subset (Finset.mem_filter.mp hT).2 (Finset.mem_filter.mp hU).2 h


/-! ## The degree-`d` truncation, and the conditional hypercontractivity of global functions -/

/-- The degree-`d` truncation of `f`. -/
def trunc (d : ℕ) (f : (Fin n → ZMod 2) → ℂ) : (Fin n → ZMod 2) → ℂ :=
  ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun S => S.card ≤ d), efronStein f S

lemma trunc_eq_sum_smul (d : ℕ) (f : (Fin n → ZMod 2) → ℂ) :
    trunc d f = ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun S => S.card ≤ d),
      efronCoeff f S • chi S := by
  rw [trunc]
  exact Finset.sum_congr rfl fun S _ => efronStein_eq_smul f S

lemma walshFourier_trunc (d : ℕ) (f : (Fin n → ZMod 2) → ℂ) (R : Finset (Fin n)) :
    walshFourier (trunc d f) R = if R.card ≤ d then walshFourier f R else 0 := by
  rw [trunc, walshFourier_sum]
  rw [Finset.sum_congr rfl (fun S _ => walshFourier_efronStein f S R)]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

lemma deg_trunc (d : ℕ) (f : (Fin n → ZMod 2) → ℂ) : Deg d (trunc d f) := by
  intro S hS
  rw [walshFourier_trunc, if_neg (by omega)]

lemma mu_eq_sum_efronCoeff (f : (Fin n → ZMod 2) → ℂ) :
    mu f = ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))), ‖efronCoeff f S‖ ^ 2 := by
  have hf : f = ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))), efronCoeff f S • chi S := by
    conv_lhs => rw [← sum_efronStein f]
    exact Finset.sum_congr rfl fun S _ => efronStein_eq_smul f S
  conv_lhs => rw [hf]
  exact mu_sum_smul_chi _ _ (fun S => S) (fun _ _ _ _ h => h)

lemma mu_trunc_eq (d : ℕ) (f : (Fin n → ZMod 2) → ℂ) :
    mu (trunc d f) = ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun S => S.card ≤ d),
      ‖efronCoeff f S‖ ^ 2 := by
  rw [trunc_eq_sum_smul]
  exact mu_sum_smul_chi _ _ (fun S => S) (fun _ _ _ _ h => h)

lemma mu_trunc_le (d : ℕ) (f : (Fin n → ZMod 2) → ℂ) : mu (trunc d f) ≤ mu f := by
  rw [mu_trunc_eq, mu_eq_sum_efronCoeff]
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
  intro S _ _; positivity

lemma mu_le_of_global {d : ℕ} {ε : ℝ} {f : (Fin n → ZMod 2) → ℂ} (h : Global d ε f) :
    mu f ≤ ε := by simpa [restr_empty] using h ∅ (by simp)

/-- **Corollary 2.13 of arXiv:2209.04243**: a global function satisfies a conditional
hypercontractive inequality for its degree-`d` truncation. -/
theorem trunc_hyp (d : ℕ) (f : (Fin n → ZMod 2) → ℂ) {ε : ℝ} (hglob : Global d ε f) :
    mu4 (trunc d f) ≤ (800 * d : ℝ) ^ d * ε * mu (trunc d f) := by
  have h1 := mu4_le_of_deg d (trunc d f) (deg_trunc d f)
  have h2 : mu (trunc d f) ≤ ε := le_trans (mu_trunc_le d f) (mu_le_of_global hglob)
  have h3 : (mu (trunc d f)) ^ 2 ≤ ε * mu (trunc d f) := by
    nlinarith [h2, mu_nonneg (trunc d f)]
  have h9 : (9 : ℝ) ^ d ≤ (800 * d : ℝ) ^ d := by
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd; norm_num
    · have h2' : (9 : ℝ) ≤ 800 * d := by
        have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
        nlinarith
      exact pow_le_pow_left₀ (by norm_num) h2' d
  calc mu4 (trunc d f) ≤ (9 : ℝ) ^ d * (mu (trunc d f)) ^ 2 := h1
    _ ≤ (9 : ℝ) ^ d * (ε * mu (trunc d f)) := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ ≤ (800 * d : ℝ) ^ d * (ε * mu (trunc d f)) :=
        mul_le_mul_of_nonneg_right h9 (by nlinarith [mu_nonneg (trunc d f)])
    _ = (800 * d : ℝ) ^ d * ε * mu (trunc d f) := by ring

end

end Submission.Hypercube
