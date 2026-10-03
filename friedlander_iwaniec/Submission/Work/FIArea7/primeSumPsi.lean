/-
# `Work.FIArea7.primeSumPsi` — prime sums of quadratic eigenvalues from Theorem 2ψ

`Σ_{p ≤ L, p prime} P (c₀ p) λ(c₀ p)` is bounded by `C c₀ d (|k|+1) L^{76/77} (K|b-a|+1)`,
where `P` is a `C¹` weight, `0 ≤ P ≤ 1`, supported in `(a,b]` with `|P'| ≤ K`, and
`h2psi : Theorem2psi` is the input bound `Σ_{n ≤ x} Λ(n) λ(c n) ≪ c d (|k|+1) x^{76/77}`.

Method: write the prime sum as the von Mangoldt sum with the weight `1/log n` (correcting by the
prime powers), sum by parts against the partial sums of `Λ(n) λ(c₀ n)` — which `h2psi` bounds —
and estimate the total variation of the weight `w m = P(c₀ m)/log m` (module `psiWDefs`) and the
prime-power correction (`Λ m/log m = 1/k` at `m = p^k`, `k ≥ 2`, together with the Chebyshev bound
`ψ - θ ≪ √x`).
-/
import Mathlib
import Submission.Work.FIArea7.Classical172Defs
import Submission.Work.FIArea7.psiWDefs
import Submission.Work.FIArea7.normQuadEigenLe
import Submission.Work.FIArea7.KSDefs
import Submission.Work.FIArea7.psiAbel
import Submission.Work.FIArea7.psiLogDiff
import Submission.Work.FIArea7.psiLogSeries
import Submission.Work.FIArea7.psiLipschitz
import Submission.Work.FIArea7.psiCardInt
import Submission.Work.FIArea7.psiVonMangoldtPrime
import Submission.Work.FIArea7.psiTauMul
import Submission.Work.FIArea7.psiTauPP
import Submission.Commons.NumberTheory.Chebyshev.cumulativePrimePowerLeSqrt

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section


/-- Per-term bound for the Abel weight `psiW`, for `m ≥ 2`. -/
lemma psiW_step_le {P : ℝ → ℝ} {c₀ K : ℝ} (hc₀ : 0 < c₀) (hP : ContDiff ℝ 1 P)
    (hK : ∀ u : ℝ, |deriv P u| ≤ K) (hnn : ∀ u : ℝ, 0 ≤ P u) (h1 : ∀ u : ℝ, P u ≤ 1)
    {m : ℕ} (hm : 2 ≤ m) :
    ‖psiW P c₀ (m + 1) - psiW P c₀ m‖
      ≤ (if P (c₀ * (m : ℝ)) ≠ 0 ∨ P (c₀ * ((m : ℝ) + 1)) ≠ 0 then
            min (K * c₀) 1 / Real.log 2 else 0)
        + 1 / ((m : ℝ) * Real.log (m : ℝ) ^ 2) := by
  have hKnn : 0 ≤ K := le_trans (abs_nonneg (deriv P 0)) (hK 0)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos (by linarith)
  have hlogm1 : 0 < Real.log ((m : ℝ) + 1) := Real.log_pos (by linarith)
  have hlogm1ge : Real.log 2 ≤ Real.log ((m : ℝ) + 1) := Real.log_le_log (by norm_num) (by linarith)
  have hm1 : 2 ≤ m + 1 := by omega
  rw [psiW_of_two_le hm, psiW_of_two_le hm1]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have habs : |P (c₀ * ((m : ℝ) + 1)) - P (c₀ * (m : ℝ))| ≤ min (K * c₀) 1 := by
    refine le_min ?_ ?_
    · have h := psiLipschitz hP hK (c₀ * ((m : ℝ) + 1)) (c₀ * (m : ℝ))
      have h2 : |c₀ * ((m : ℝ) + 1) - c₀ * (m : ℝ)| = c₀ := by
        rw [abs_of_nonneg (by nlinarith : (0 : ℝ) ≤ c₀ * ((m : ℝ) + 1) - c₀ * (m : ℝ))]
        ring
      rw [h2] at h
      exact h
    · have h2 := h1 (c₀ * ((m : ℝ) + 1))
      have h3 := hnn (c₀ * (m : ℝ))
      have h4 := hnn (c₀ * ((m : ℝ) + 1))
      have h5 := h1 (c₀ * (m : ℝ))
      rw [abs_le]
      constructor <;> linarith
  have hlogdiff := psiLogDiff (n := m) hm
  have hPm_le : |P (c₀ * (m : ℝ))| ≤ 1 := by
    rw [abs_of_nonneg (hnn _)]; exact h1 _
  have hmain : |P (c₀ * ((m : ℝ) + 1)) / Real.log ((m : ℝ) + 1)
      - P (c₀ * (m : ℝ)) / Real.log (m : ℝ)|
      ≤ (if P (c₀ * (m : ℝ)) ≠ 0 ∨ P (c₀ * ((m : ℝ) + 1)) ≠ 0 then
            min (K * c₀) 1 / Real.log 2 else 0)
        + 1 / ((m : ℝ) * Real.log (m : ℝ) ^ 2) := by
    have hdecomp : P (c₀ * ((m : ℝ) + 1)) / Real.log ((m : ℝ) + 1)
        - P (c₀ * (m : ℝ)) / Real.log (m : ℝ)
        = (P (c₀ * ((m : ℝ) + 1)) - P (c₀ * (m : ℝ))) / Real.log ((m : ℝ) + 1)
          + P (c₀ * (m : ℝ)) * (1 / Real.log ((m : ℝ) + 1) - 1 / Real.log (m : ℝ)) := by
      field_simp
      ring
    rw [hdecomp]
    refine le_trans (abs_add_le _ _) ?_
    rw [abs_div, abs_mul, abs_of_pos hlogm1]
    by_cases hcond : P (c₀ * (m : ℝ)) ≠ 0 ∨ P (c₀ * ((m : ℝ) + 1)) ≠ 0
    · rw [if_pos hcond]
      have hA : |P (c₀ * ((m : ℝ) + 1)) - P (c₀ * (m : ℝ))| / Real.log ((m : ℝ) + 1)
          ≤ min (K * c₀) 1 / Real.log 2 := by
        rw [div_le_div_iff₀ hlogm1 hlog2]
        exact mul_le_mul habs hlogm1ge (le_of_lt hlog2) (le_trans (abs_nonneg _) habs)
      have hB : |P (c₀ * (m : ℝ))| * |1 / Real.log ((m : ℝ) + 1) - 1 / Real.log (m : ℝ)|
          ≤ 1 / ((m : ℝ) * Real.log (m : ℝ) ^ 2) := by
        have h1' : |1 / Real.log ((m : ℝ) + 1) - 1 / Real.log (m : ℝ)|
            ≤ 1 / ((m : ℝ) * Real.log (m : ℝ) ^ 2) := by
          rw [abs_sub_comm]; exact hlogdiff
        calc |P (c₀ * (m : ℝ))| * |1 / Real.log ((m : ℝ) + 1) - 1 / Real.log (m : ℝ)|
            ≤ 1 * |1 / Real.log ((m : ℝ) + 1) - 1 / Real.log (m : ℝ)| :=
              mul_le_mul_of_nonneg_right hPm_le (abs_nonneg _)
          _ ≤ 1 * (1 / ((m : ℝ) * Real.log (m : ℝ) ^ 2)) :=
              mul_le_mul_of_nonneg_left h1' (by norm_num)
          _ = 1 / ((m : ℝ) * Real.log (m : ℝ) ^ 2) := by ring
      linarith
    · rw [if_neg hcond]
      have hPm0 : P (c₀ * (m : ℝ)) = 0 := by
        by_contra hc
        exact hcond (Or.inl hc)
      have hPm10 : P (c₀ * ((m : ℝ) + 1)) = 0 := by
        by_contra hc
        exact hcond (Or.inr hc)
      rw [hPm0, hPm10]
      simp only [sub_zero, abs_zero, zero_div, zero_mul, add_zero]
      positivity
  exact hmain

/-- The support set of the weight differences. -/
def psiWSupp (P : ℝ → ℝ) (c₀ : ℝ) (L : ℕ) : Finset ℕ :=
  (Finset.Icc 2 (L - 1)).filter
    (fun m => P (c₀ * (m : ℝ)) ≠ 0 ∨ P (c₀ * ((m : ℝ) + 1)) ≠ 0)

/-- `min (K c₀) 1 · (2 δ/c₀ + 2) ≤ 2 K δ + 2`. -/
lemma psi_var_key {K c₀ δ : ℝ} (hK : 0 ≤ K) (hc₀ : 0 < c₀) (hδ : 0 ≤ δ) :
    min (K * c₀) 1 * (2 * (δ / c₀) + 2) ≤ 2 * K * δ + 2 := by
  have h1 : min (K * c₀) 1 ≤ K * c₀ := min_le_left _ _
  have h2 : min (K * c₀) 1 ≤ 1 := min_le_right _ _
  have hA : min (K * c₀) 1 * (2 * (δ / c₀)) ≤ 2 * (K * δ) := by
    have := mul_le_mul_of_nonneg_right h1 (by positivity : (0:ℝ) ≤ 2 * (δ / c₀))
    have heq : (K * c₀) * (2 * (δ / c₀)) = 2 * (K * δ) := by field_simp
    linarith [this, heq.symm.le, heq.le]
  have hB : min (K * c₀) 1 * 2 ≤ 2 := by nlinarith [h2]
  nlinarith [hA, hB]

/-- Final numerical absorption for the variation bound. -/
lemma psi_var_arith {C₁ K δ : ℝ} (hC₁ : 0 < C₁) (hK : 0 ≤ K) (hδ : 0 < δ) :
    1 / Real.log 2 + (2 * K * δ + 2) / Real.log 2 + C₁
      ≤ (3 / Real.log 2 + C₁ + 2) * (K * δ + 1) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hX : 0 ≤ K * δ := mul_nonneg hK (le_of_lt hδ)
  have hrw : (3 / Real.log 2 + C₁ + 2) * (K * δ + 1)
      = (3 + C₁ * Real.log 2 + 2 * Real.log 2) * (K * δ + 1) / Real.log 2 := by
    field_simp
  have hrw2 : 1 / Real.log 2 + (2 * K * δ + 2) / Real.log 2 + C₁
      = (1 + (2 * K * δ + 2) + C₁ * Real.log 2) / Real.log 2 := by
    field_simp
  have hn2 : 0 < C₁ * Real.log 2 := mul_pos hC₁ hlog2
  have hn3 : 0 ≤ K * δ * (C₁ * Real.log 2) := mul_nonneg hX (le_of_lt hn2)
  have hn4 : 0 ≤ K * δ * Real.log 2 := mul_nonneg hX (le_of_lt hlog2)
  rw [hrw, hrw2, div_le_div_iff₀ hlog2 hlog2]
  nlinarith [hX, hC₁, hlog2, hn2, hn3, hn4]

/-- Total variation of the Abel weight `psiW`. -/
theorem psiVariation' : ∃ C : ℝ, 0 < C ∧
    ∀ (P : ℝ → ℝ) (a b K c₀ : ℝ) (L : ℕ),
      ContDiff ℝ 1 P → a < b → 1 ≤ c₀ →
      (∀ u : ℝ, 0 ≤ P u) → (∀ u : ℝ, P u ≤ 1) →
      (∀ u : ℝ, P u ≠ 0 → a < u ∧ u ≤ b) → (∀ u : ℝ, |deriv P u| ≤ K) →
      ∑ m ∈ Finset.Icc 1 (L - 1), ‖psiW P c₀ (m + 1) - psiW P c₀ m‖ ≤ C * (K * (b - a) + 1) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := psiLogSeries
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨3 / Real.log 2 + C₁ + 2, by positivity, ?_⟩
  intro P a b K c₀ L hP hab hc₀ hnn h1 hsup hK
  have hKnn : 0 ≤ K := le_trans (abs_nonneg (deriv P 0)) (hK 0)
  have hc₀pos : 0 < c₀ := by linarith
  have hba : 0 < b - a := by linarith
  have hone : ‖psiW P c₀ 2 - psiW P c₀ 1‖ ≤ 1 / Real.log 2 := by
    rw [psiW_of_not_two_le (by norm_num : ¬ (2 : ℕ) ≤ 1), sub_zero,
      psiW_of_two_le (by norm_num : (2 : ℕ) ≤ 2)]
    simp only [Nat.cast_ofNat]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hlog2]
    exact div_le_div_of_nonneg_right (by rw [abs_of_nonneg (hnn _)]; exact h1 _) (le_of_lt hlog2)
  have hsum2 : (∑ m ∈ Finset.Icc 2 (L - 1), ‖psiW P c₀ (m + 1) - psiW P c₀ m‖)
      ≤ (min (K * c₀) 1 / Real.log 2) * ((psiWSupp P c₀ L).card : ℝ) + C₁ := by
    have hstep : (∑ m ∈ Finset.Icc 2 (L - 1), ‖psiW P c₀ (m + 1) - psiW P c₀ m‖)
        ≤ ∑ m ∈ Finset.Icc 2 (L - 1),
            ((if P (c₀ * (m : ℝ)) ≠ 0 ∨ P (c₀ * ((m : ℝ) + 1)) ≠ 0 then
                min (K * c₀) 1 / Real.log 2 else 0)
              + 1 / ((m : ℝ) * Real.log (m : ℝ) ^ 2)) :=
      Finset.sum_le_sum (fun m hm =>
        psiW_step_le hc₀pos hP hK hnn h1 (Finset.mem_Icc.mp hm).1)
    rw [Finset.sum_add_distrib] at hstep
    have hfirst : (∑ m ∈ Finset.Icc 2 (L - 1),
          (if P (c₀ * (m : ℝ)) ≠ 0 ∨ P (c₀ * ((m : ℝ) + 1)) ≠ 0 then
            min (K * c₀) 1 / Real.log 2 else 0))
        = (min (K * c₀) 1 / Real.log 2) * ((psiWSupp P c₀ L).card : ℝ) := by
      rw [← Finset.sum_filter]
      simp [psiWSupp, Finset.sum_const, nsmul_eq_mul, mul_comm]
    have hsecond : (∑ m ∈ Finset.Icc 2 (L - 1), 1 / ((m : ℝ) * Real.log (m : ℝ) ^ 2)) ≤ C₁ :=
      hC₁ (L - 1)
    rw [hfirst] at hstep
    linarith
  have hcount : ((psiWSupp P c₀ L).card : ℝ) ≤ 2 * ((b - a) / c₀) + 2 := by
    have hab' : a / c₀ ≤ b / c₀ := div_le_div_of_nonneg_right (le_of_lt hab) (le_of_lt hc₀pos)
    have hab'' : a / c₀ - 1 ≤ b / c₀ - 1 := by linarith
    have hsub1 : psiWSupp P c₀ L ⊆
        ((Finset.Icc 1 (L - 1)).filter (fun m : ℕ => a / c₀ < (m : ℝ) ∧ (m : ℝ) ≤ b / c₀))
        ∪ ((Finset.Icc 1 (L - 1)).filter
            (fun m : ℕ => a / c₀ - 1 < (m : ℝ) ∧ (m : ℝ) ≤ b / c₀ - 1)) := by
      intro m hm
      rw [psiWSupp, Finset.mem_filter] at hm
      obtain ⟨hmI, hmcond⟩ := hm
      have hmI1 : m ∈ Finset.Icc 1 (L - 1) := by
        rw [Finset.mem_Icc] at hmI ⊢; omega
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      rcases hmcond with h | h
      · have h' := hsup (c₀ * (m : ℝ)) h
        left
        refine ⟨hmI1, ?_, ?_⟩
        · rw [div_lt_iff₀ hc₀pos]; nlinarith [h'.1]
        · rw [le_div_iff₀ hc₀pos]; nlinarith [h'.2]
      · have h' := hsup (c₀ * ((m : ℝ) + 1)) h
        right
        refine ⟨hmI1, ?_, ?_⟩
        · have : a / c₀ < (m : ℝ) + 1 := by
            rw [div_lt_iff₀ hc₀pos]; nlinarith [h'.1]
          linarith
        · have : (m : ℝ) + 1 ≤ b / c₀ := by
            rw [le_div_iff₀ hc₀pos]; nlinarith [h'.2]
          linarith
    have hcard1 := psiCardInt (a / c₀) (b / c₀) (L - 1) hab'
    have hcard2 := psiCardInt (a / c₀ - 1) (b / c₀ - 1) (L - 1) hab''
    have hcards : ((psiWSupp P c₀ L).card : ℝ)
        ≤ (((Finset.Icc 1 (L - 1)).filter (fun m : ℕ => a / c₀ < (m : ℝ) ∧ (m : ℝ) ≤ b / c₀)).card : ℝ)
          + (((Finset.Icc 1 (L - 1)).filter
              (fun m : ℕ => a / c₀ - 1 < (m : ℝ) ∧ (m : ℝ) ≤ b / c₀ - 1)).card : ℝ) := by
      calc ((psiWSupp P c₀ L).card : ℝ)
          ≤ (((((Finset.Icc 1 (L - 1)).filter (fun m : ℕ => a / c₀ < (m : ℝ) ∧ (m : ℝ) ≤ b / c₀))
              ∪ ((Finset.Icc 1 (L - 1)).filter
                  (fun m : ℕ => a / c₀ - 1 < (m : ℝ) ∧ (m : ℝ) ≤ b / c₀ - 1))).card : ℕ) : ℝ) := by
            exact_mod_cast Finset.card_le_card hsub1
        _ ≤ ((((Finset.Icc 1 (L - 1)).filter (fun m : ℕ => a / c₀ < (m : ℝ) ∧ (m : ℝ) ≤ b / c₀)).card
              + ((Finset.Icc 1 (L - 1)).filter
                  (fun m : ℕ => a / c₀ - 1 < (m : ℝ) ∧ (m : ℝ) ≤ b / c₀ - 1)).card : ℕ) : ℝ) := by
            exact_mod_cast Finset.card_union_le _ _
        _ = (((Finset.Icc 1 (L - 1)).filter (fun m : ℕ => a / c₀ < (m : ℝ) ∧ (m : ℝ) ≤ b / c₀)).card : ℝ)
          + (((Finset.Icc 1 (L - 1)).filter
              (fun m : ℕ => a / c₀ - 1 < (m : ℝ) ∧ (m : ℝ) ≤ b / c₀ - 1)).card : ℝ) := by
            rw [Nat.cast_add]
    have hval : b / c₀ - a / c₀ + 1 = (b - a) / c₀ + 1 := by rw [sub_div]
    have hval2 : b / c₀ - 1 - (a / c₀ - 1) + 1 = (b - a) / c₀ + 1 := by rw [sub_div]; ring
    rw [hval] at hcard1
    rw [hval2] at hcard2
    linarith
  have hsub : Finset.Icc 1 (L - 1) ⊆ insert 1 (Finset.Icc 2 (L - 1)) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    rcases eq_or_lt_of_le hm.1 with h | h
    · subst h; exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_Icc.mpr ⟨h, hm.2⟩)
  have hsplit : (∑ m ∈ Finset.Icc 1 (L - 1), ‖psiW P c₀ (m + 1) - psiW P c₀ m‖)
      ≤ ‖psiW P c₀ 2 - psiW P c₀ 1‖
        + ∑ m ∈ Finset.Icc 2 (L - 1), ‖psiW P c₀ (m + 1) - psiW P c₀ m‖ := by
    have h1' := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun x _ _ => norm_nonneg (psiW P c₀ (x + 1) - psiW P c₀ x))
    rw [Finset.sum_insert (by rw [Finset.mem_Icc]; omega)] at h1'
    exact h1'
  have hmin0 : 0 ≤ min (K * c₀) 1 := le_min (by positivity) (by norm_num)
  have hmin0div : 0 ≤ min (K * c₀) 1 / Real.log 2 := div_nonneg hmin0 (le_of_lt hlog2)
  have hcount' : (min (K * c₀) 1 / Real.log 2) * ((psiWSupp P c₀ L).card : ℝ)
      ≤ (min (K * c₀) 1 / Real.log 2) * (2 * ((b - a) / c₀) + 2) :=
    mul_le_mul_of_nonneg_left hcount hmin0div
  have hkey : (min (K * c₀) 1 / Real.log 2) * (2 * ((b - a) / c₀) + 2)
      ≤ (2 * K * (b - a) + 2) / Real.log 2 := by
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right
      (psi_var_key hKnn hc₀pos (le_of_lt hba)) (le_of_lt hlog2)
  calc (∑ m ∈ Finset.Icc 1 (L - 1), ‖psiW P c₀ (m + 1) - psiW P c₀ m‖)
      ≤ ‖psiW P c₀ 2 - psiW P c₀ 1‖
        + ∑ m ∈ Finset.Icc 2 (L - 1), ‖psiW P c₀ (m + 1) - psiW P c₀ m‖ := hsplit
    _ ≤ 1 / Real.log 2 + ((min (K * c₀) 1 / Real.log 2) * ((psiWSupp P c₀ L).card : ℝ) + C₁) :=
        add_le_add hone hsum2
    _ ≤ 1 / Real.log 2 + ((2 * K * (b - a) + 2) / Real.log 2 + C₁) := by
        linarith [hcount', hkey]
    _ ≤ (3 / Real.log 2 + C₁ + 2) * (K * (b - a) + 1) := by
        have := psi_var_arith hC₁pos hKnn hba
        linarith



/-- `√L · log (L+2) ≪ L^{76/77}` for `L ≥ 1`. -/
lemma sqrt_mul_log_le_rpow : ∃ C : ℝ, 0 < C ∧ ∀ L : ℕ, 1 ≤ L →
    Real.sqrt (L : ℝ) * Real.log ((L : ℝ) + 2) ≤ C * (L : ℝ) ^ ((76 : ℝ) / 77) := by
  refine ⟨(3 : ℝ) ^ ((1 : ℝ) / 8) / (1 / 8) + 1, by positivity, ?_⟩
  intro L hL
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hx : (0 : ℝ) < (L : ℝ) + 2 := by linarith
  have hδ : (0 : ℝ) < 1 / 8 := by norm_num
  have hlog : Real.log ((L : ℝ) + 2) ≤ ((L : ℝ) + 2) ^ ((1 : ℝ) / 8) / (1 / 8) :=
    Real.log_le_rpow_div (le_of_lt hx) hδ
  have hxle : (L : ℝ) + 2 ≤ 3 * (L : ℝ) := by linarith
  have hrpow : ((L : ℝ) + 2) ^ ((1 : ℝ) / 8) ≤ (3 * (L : ℝ)) ^ ((1 : ℝ) / 8) :=
    Real.rpow_le_rpow (le_of_lt hx) hxle (by norm_num)
  have hmul : (3 * (L : ℝ)) ^ ((1 : ℝ) / 8) = (3 : ℝ) ^ ((1 : ℝ) / 8) * (L : ℝ) ^ ((1 : ℝ) / 8) :=
    Real.mul_rpow (by norm_num) (le_of_lt (by linarith : (0:ℝ) < (L:ℝ)))
  have hsqrt : Real.sqrt (L : ℝ) = (L : ℝ) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
  have hexp : (1 : ℝ) / 2 + 1 / 8 = 5 / 8 := by norm_num
  have h5 : (5 : ℝ) / 8 ≤ 76 / 77 := by norm_num
  calc Real.sqrt (L : ℝ) * Real.log ((L : ℝ) + 2)
      ≤ (L : ℝ) ^ ((1 : ℝ) / 2) * (((L : ℝ) + 2) ^ ((1 : ℝ) / 8) / (1 / 8)) := by
        rw [hsqrt]
        exact mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg (by linarith) _)
    _ ≤ (L : ℝ) ^ ((1 : ℝ) / 2) * (((3 : ℝ) ^ ((1 : ℝ) / 8) * (L : ℝ) ^ ((1 : ℝ) / 8)) / (1 / 8)) := by
        have hpos : (0:ℝ) < 1 / 8 := by norm_num
        have h2 : ((L : ℝ) + 2) ^ ((1 : ℝ) / 8) / (1 / 8)
            ≤ ((3 : ℝ) ^ ((1 : ℝ) / 8) * (L : ℝ) ^ ((1 : ℝ) / 8)) / (1 / 8) := by
          rw [div_le_div_iff_of_pos_right hpos]
          rwa [hmul] at hrpow
        exact mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg (by linarith) _)
    _ = ((3 : ℝ) ^ ((1 : ℝ) / 8) / (1 / 8)) * ((L : ℝ) ^ ((1 : ℝ) / 2) * (L : ℝ) ^ ((1 : ℝ) / 8)) := by
        ring
    _ = ((3 : ℝ) ^ ((1 : ℝ) / 8) / (1 / 8)) * (L : ℝ) ^ ((5 : ℝ) / 8) := by
        rw [← Real.rpow_add (by linarith : (0:ℝ) < (L:ℝ)), hexp]
    _ ≤ ((3 : ℝ) ^ ((1 : ℝ) / 8) / (1 / 8)) * (L : ℝ) ^ ((76 : ℝ) / 77) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact Real.rpow_le_rpow_of_exponent_le hL1 h5
    _ ≤ ((3 : ℝ) ^ ((1 : ℝ) / 8) / (1 / 8) + 1) * (L : ℝ) ^ ((76 : ℝ) / 77) := by
        have := Real.rpow_nonneg (by linarith : (0:ℝ) ≤ (L:ℝ)) ((76:ℝ)/77)
        nlinarith [this]

/-- `log₂ L + 1 ≪ log (L+2)`. -/
lemma natLog_two_add_one_le (L : ℕ) (hL : 1 ≤ L) :
    ((Nat.log 2 L : ℕ) : ℝ) + 1 ≤ 2 / Real.log 2 * Real.log ((L : ℝ) + 2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  have hx2 : (2 : ℝ) ≤ (L : ℝ) + 2 := by linarith
  have hK : ((Nat.log 2 L : ℕ) : ℝ) * Real.log 2 ≤ Real.log (L : ℝ) := by
    have h1 : 2 ^ Nat.log 2 L ≤ L := Nat.pow_log_le_self 2 (by omega)
    have h2 : Real.log (((2 : ℕ) ^ Nat.log 2 L : ℕ) : ℝ) ≤ Real.log (L : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast h1)
    rwa [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at h2
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hlogL : Real.log (L : ℝ) ≤ Real.log ((L : ℝ) + 2) := Real.log_le_log (by linarith) (by linarith)
  have hK' : ((Nat.log 2 L : ℕ) : ℝ) ≤ Real.log ((L : ℝ) + 2) / Real.log 2 := by
    rw [le_div_iff₀ hlog2]; linarith
  have h1' : 1 ≤ Real.log ((L : ℝ) + 2) / Real.log 2 := by
    rw [le_div_iff₀ hlog2]
    have : Real.log 2 ≤ Real.log ((L : ℝ) + 2) := Real.log_le_log (by norm_num) hx2
    linarith
  calc ((Nat.log 2 L : ℕ) : ℝ) + 1
      ≤ Real.log ((L : ℝ) + 2) / Real.log 2 + Real.log ((L : ℝ) + 2) / Real.log 2 := by linarith
    _ = 2 / Real.log 2 * Real.log ((L : ℝ) + 2) := by ring

/-- The prime-power correction to the von Mangoldt sum. -/
theorem psiNonPrimeSum' : ∃ C : ℝ, 0 < C ∧
    ∀ (c₀ L : ℕ) (P : ℝ → ℝ) (lam : ℕ → ℂ),
      1 ≤ c₀ → 1 ≤ L → (∀ u : ℝ, |P u| ≤ 1) →
      (∀ n : ℕ, ‖lam n‖ ≤ 4 * ((n.divisors.card : ℕ) : ℝ)) →
      ‖∑ m ∈ (Finset.Icc 2 L).filter (fun m => ¬ m.Prime),
          ((ArithmeticFunction.vonMangoldt m / Real.log (m : ℝ) : ℝ) : ℂ) *
            ((P ((c₀ : ℝ) * (m : ℝ)) : ℝ) : ℂ) * lam (c₀ * m)‖
        ≤ C * ((c₀.divisors.card : ℕ) : ℝ) * (L : ℝ) ^ ((76 : ℝ) / 77) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Commons.NumberTheory.Chebyshev.cumulativePrimePowerLeSqrt
  obtain ⟨C₂, hC₂pos, hC₂⟩ := sqrt_mul_log_le_rpow
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨4 * (1 / Real.log 2) * (2 / Real.log 2) * C₁ * C₂ + 1, by positivity, ?_⟩
  intro c₀ L P lam hc₀ hL hP hlam
  set S : Finset ℕ := (Finset.Icc 2 L).filter (fun m => ¬ m.Prime) with hS
  set Q : Finset ℕ := S.filter (fun m => IsPrimePow m) with hQ
  have hzero : ∀ m : ℕ, ¬ IsPrimePow m →
      ((ArithmeticFunction.vonMangoldt m / Real.log (m : ℝ) : ℝ) : ℂ) *
        ((P ((c₀ : ℝ) * (m : ℝ)) : ℝ) : ℂ) * lam (c₀ * m) = 0 := by
    intro m hm
    rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hm]
    simp
  have hsum_eq' : (∑ m ∈ Q,
        ((ArithmeticFunction.vonMangoldt m / Real.log (m : ℝ) : ℝ) : ℂ) *
          ((P ((c₀ : ℝ) * (m : ℝ)) : ℝ) : ℂ) * lam (c₀ * m))
      = ∑ m ∈ S,
        ((ArithmeticFunction.vonMangoldt m / Real.log (m : ℝ) : ℝ) : ℂ) *
          ((P ((c₀ : ℝ) * (m : ℝ)) : ℝ) : ℂ) * lam (c₀ * m) := by
    rw [hQ]
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro m hm hmnot
    exact hzero m (fun h => hmnot (Finset.mem_filter.mpr ⟨hm, h⟩))
  have hsum_eq :
      (∑ m ∈ S,
        ((ArithmeticFunction.vonMangoldt m / Real.log (m : ℝ) : ℝ) : ℂ) *
          ((P ((c₀ : ℝ) * (m : ℝ)) : ℝ) : ℂ) * lam (c₀ * m))
      = ∑ m ∈ Q,
        ((ArithmeticFunction.vonMangoldt m / Real.log (m : ℝ) : ℝ) : ℂ) *
          ((P ((c₀ : ℝ) * (m : ℝ)) : ℝ) : ℂ) * lam (c₀ * m) := hsum_eq'.symm
  have hmemS : ∀ m, m ∈ S ↔ (2 ≤ m ∧ m ≤ L ∧ ¬ m.Prime) := by
    intro m; rw [hS, Finset.mem_filter, Finset.mem_Icc]; tauto
  have hmemQ : ∀ m, m ∈ Q ↔ (2 ≤ m ∧ m ≤ L ∧ ¬ m.Prime ∧ IsPrimePow m) := by
    intro m; rw [hQ, Finset.mem_filter, hmemS]; tauto
  have hpt : ∀ m ∈ Q,
      ‖((ArithmeticFunction.vonMangoldt m / Real.log (m : ℝ) : ℝ) : ℂ) *
          ((P ((c₀ : ℝ) * (m : ℝ)) : ℝ) : ℂ) * lam (c₀ * m)‖
      ≤ (4 * (((c₀.divisors.card : ℕ) : ℝ)) / Real.log 2 * (((Nat.log 2 L : ℕ) : ℝ) + 1))
        * ArithmeticFunction.vonMangoldt m := by
    intro m hm
    obtain ⟨hm2, hmL, hmp, hmpow⟩ := (hmemQ m).mp hm
    have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
    have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos (by linarith)
    have hlogm2 : Real.log 2 ≤ Real.log (m : ℝ) := Real.log_le_log (by norm_num) hmR
    have hA : ‖((ArithmeticFunction.vonMangoldt m / Real.log (m : ℝ) : ℝ) : ℂ)‖
        ≤ ArithmeticFunction.vonMangoldt m / Real.log 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (le_of_lt hlogm))]
      rw [div_le_div_iff₀ hlogm hlog2]
      nlinarith [ArithmeticFunction.vonMangoldt_nonneg (n := m), hlogm2]
    have hB : ‖((P ((c₀ : ℝ) * (m : ℝ)) : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact hP _
    have hC : ‖lam (c₀ * m)‖ ≤ 4 * (((c₀ * m).divisors.card : ℕ) : ℝ) := hlam (c₀ * m)
    have hD : (((c₀ * m).divisors.card : ℕ) : ℝ)
        ≤ ((c₀.divisors.card : ℕ) : ℝ) * ((m.divisors.card : ℕ) : ℝ) := by
      exact_mod_cast psiTauMul c₀ m
    have hE : ((m.divisors.card : ℕ) : ℝ) ≤ ((Nat.log 2 L : ℕ) : ℝ) + 1 := by
      exact_mod_cast psiTauPP hmpow hmL hmp
    have hnn : 0 ≤ ArithmeticFunction.vonMangoldt m := ArithmeticFunction.vonMangoldt_nonneg
    have hnn1 : (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt m / Real.log 2 := div_nonneg hnn (le_of_lt hlog2)
    have hnn2 : (0 : ℝ) ≤ ((c₀.divisors.card : ℕ) : ℝ) := Nat.cast_nonneg _
    have hnn3 : (0 : ℝ) ≤ ((m.divisors.card : ℕ) : ℝ) := Nat.cast_nonneg _
    have hnn4 : (0 : ℝ) ≤ ((Nat.log 2 L : ℕ) : ℝ) + 1 := by positivity
    rw [norm_mul, norm_mul]
    have hAB : ‖((ArithmeticFunction.vonMangoldt m / Real.log (m : ℝ) : ℝ) : ℂ)‖
          * ‖((P ((c₀ : ℝ) * (m : ℝ)) : ℝ) : ℂ)‖
        ≤ (ArithmeticFunction.vonMangoldt m / Real.log 2) * 1 :=
      mul_le_mul hA hB (norm_nonneg _) hnn1
    have hDE : (((c₀ * m).divisors.card : ℕ) : ℝ)
        ≤ ((c₀.divisors.card : ℕ) : ℝ) * (((Nat.log 2 L : ℕ) : ℝ) + 1) :=
      calc (((c₀ * m).divisors.card : ℕ) : ℝ)
          ≤ ((c₀.divisors.card : ℕ) : ℝ) * ((m.divisors.card : ℕ) : ℝ) := hD
        _ ≤ ((c₀.divisors.card : ℕ) : ℝ) * (((Nat.log 2 L : ℕ) : ℝ) + 1) :=
            mul_le_mul_of_nonneg_left hE hnn2
    calc ‖((ArithmeticFunction.vonMangoldt m / Real.log (m : ℝ) : ℝ) : ℂ)‖
          * ‖((P ((c₀ : ℝ) * (m : ℝ)) : ℝ) : ℂ)‖ * ‖lam (c₀ * m)‖
        ≤ ((ArithmeticFunction.vonMangoldt m / Real.log 2) * 1)
            * (4 * (((c₀ * m).divisors.card : ℕ) : ℝ)) :=
          mul_le_mul hAB hC (norm_nonneg _) (mul_nonneg hnn1 zero_le_one)
      _ ≤ ((ArithmeticFunction.vonMangoldt m / Real.log 2) * 1)
            * (4 * (((c₀.divisors.card : ℕ) : ℝ) * (((Nat.log 2 L : ℕ) : ℝ) + 1))) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hnn1 zero_le_one)
          exact mul_le_mul_of_nonneg_left hDE (by norm_num)
      _ = (4 * (((c₀.divisors.card : ℕ) : ℝ)) / Real.log 2
            * (((Nat.log 2 L : ℕ) : ℝ) + 1)) * ArithmeticFunction.vonMangoldt m := by
          ring
  have hΛsum : (∑ m ∈ Q, ArithmeticFunction.vonMangoldt m) ≤ C₁ * Real.sqrt (L : ℝ) := by
    have hsub : Q ⊆ (Finset.Icc 0 L).filter
        (fun n => ∃ p e : ℕ, p.Prime ∧ 2 ≤ e ∧ n = p ^ e) := by
      intro m hm
      obtain ⟨hm2, hmL, hmp, hmpow⟩ := (hmemQ m).mp hm
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨Nat.zero_le _, hmL⟩, ?_⟩
      obtain ⟨p, k, hp, hk0, hpk⟩ := hmpow
      have hk1 : 1 < k := by
        rcases lt_or_ge 1 k with h | h
        · exact h
        · exfalso
          have hk1' : k = 1 := by omega
          have hm : m = p := by rw [← hpk, hk1', pow_one]
          exact hmp (by rw [hm]; exact hp.nat_prime)
      exact ⟨p, k, hp.nat_prime, by omega, hpk.symm⟩
    calc (∑ m ∈ Q, ArithmeticFunction.vonMangoldt m)
        ≤ ∑ n ∈ (Finset.Icc 0 L).filter (fun n => ∃ p e : ℕ, p.Prime ∧ 2 ≤ e ∧ n = p ^ e),
            ArithmeticFunction.vonMangoldt n :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun x _ _ => ArithmeticFunction.vonMangoldt_nonneg)
      _ = ∑ n ∈ Finset.Icc 0 ⌊(L : ℝ)⌋₊,
            (if ∃ p e : ℕ, p.Prime ∧ 2 ≤ e ∧ n = p ^ e
              then ArithmeticFunction.vonMangoldt n else 0) := by
          rw [Nat.floor_natCast, ← Finset.sum_filter]
      _ ≤ C₁ * Real.sqrt (L : ℝ) := hC₁ (L : ℝ) (by positivity)
  have hbound : ‖∑ m ∈ S,
        ((ArithmeticFunction.vonMangoldt m / Real.log (m : ℝ) : ℝ) : ℂ) *
          ((P ((c₀ : ℝ) * (m : ℝ)) : ℝ) : ℂ) * lam (c₀ * m)‖
      ≤ (4 * (((c₀.divisors.card : ℕ) : ℝ)) / Real.log 2 * (((Nat.log 2 L : ℕ) : ℝ) + 1))
        * (C₁ * Real.sqrt (L : ℝ)) := by
    rw [hsum_eq]
    refine le_trans (norm_sum_le _ _) ?_
    calc (∑ m ∈ Q, ‖((ArithmeticFunction.vonMangoldt m / Real.log (m : ℝ) : ℝ) : ℂ) *
          ((P ((c₀ : ℝ) * (m : ℝ)) : ℝ) : ℂ) * lam (c₀ * m)‖)
        ≤ ∑ m ∈ Q, (4 * (((c₀.divisors.card : ℕ) : ℝ)) / Real.log 2
            * (((Nat.log 2 L : ℕ) : ℝ) + 1)) * ArithmeticFunction.vonMangoldt m :=
          Finset.sum_le_sum hpt
      _ = (4 * (((c₀.divisors.card : ℕ) : ℝ)) / Real.log 2
            * (((Nat.log 2 L : ℕ) : ℝ) + 1)) * (∑ m ∈ Q, ArithmeticFunction.vonMangoldt m) := by
          rw [Finset.mul_sum]
      _ ≤ (4 * (((c₀.divisors.card : ℕ) : ℝ)) / Real.log 2
            * (((Nat.log 2 L : ℕ) : ℝ) + 1)) * (C₁ * Real.sqrt (L : ℝ)) := by
          refine mul_le_mul_of_nonneg_left hΛsum ?_
          have := Nat.cast_nonneg (α := ℝ) c₀.divisors.card
          positivity
  have hK := natLog_two_add_one_le L hL
  have hC₂L := hC₂ L hL
  have hτ : (0 : ℝ) ≤ ((c₀.divisors.card : ℕ) : ℝ) := Nat.cast_nonneg _
  have hC₁nn : (0 : ℝ) ≤ C₁ := le_of_lt hC₁pos
  have hC₂nn : (0 : ℝ) ≤ C₂ := le_of_lt hC₂pos
  have hLr72 : (0 : ℝ) ≤ (L : ℝ) ^ ((76 : ℝ) / 77) := Real.rpow_nonneg (Nat.cast_nonneg L) _
  have hlogx : (0 : ℝ) ≤ Real.log ((L : ℝ) + 2) := Real.log_nonneg (by linarith)
  have hsqrtL : (0 : ℝ) ≤ Real.sqrt (L : ℝ) := Real.sqrt_nonneg _
  refine le_trans hbound ?_
  have h0 : (0 : ℝ) ≤ 4 * (((c₀.divisors.card : ℕ) : ℝ)) / Real.log 2 :=
    div_nonneg (by positivity) (le_of_lt hlog2)
  have h0' : (0 : ℝ) ≤ C₁ * Real.sqrt (L : ℝ) := mul_nonneg hC₁nn hsqrtL
  calc (4 * (((c₀.divisors.card : ℕ) : ℝ)) / Real.log 2 * (((Nat.log 2 L : ℕ) : ℝ) + 1))
        * (C₁ * Real.sqrt (L : ℝ))
      ≤ (4 * (((c₀.divisors.card : ℕ) : ℝ)) / Real.log 2
          * (2 / Real.log 2 * Real.log ((L : ℝ) + 2))) * (C₁ * Real.sqrt (L : ℝ)) := by
        refine mul_le_mul_of_nonneg_right ?_ h0'
        exact mul_le_mul_of_nonneg_left hK h0
    _ = (4 * (1 / Real.log 2) * (2 / Real.log 2) * C₁ * ((c₀.divisors.card : ℕ) : ℝ))
          * (Real.sqrt (L : ℝ) * Real.log ((L : ℝ) + 2)) := by ring
    _ ≤ (4 * (1 / Real.log 2) * (2 / Real.log 2) * C₁ * ((c₀.divisors.card : ℕ) : ℝ))
          * (C₂ * (L : ℝ) ^ ((76 : ℝ) / 77)) := by
        refine mul_le_mul_of_nonneg_left hC₂L ?_
        have h2 : (0:ℝ) < 1 / Real.log 2 := by positivity
        have h3 : (0:ℝ) < 2 / Real.log 2 := by positivity
        positivity
    _ = (4 * (1 / Real.log 2) * (2 / Real.log 2) * C₁ * C₂)
          * ((c₀.divisors.card : ℕ) : ℝ) * (L : ℝ) ^ ((76 : ℝ) / 77) := by ring
    _ ≤ (4 * (1 / Real.log 2) * (2 / Real.log 2) * C₁ * C₂ + 1)
          * ((c₀.divisors.card : ℕ) : ℝ) * (L : ℝ) ^ ((76 : ℝ) / 77) := by
        have h1 : (0 : ℝ) ≤ ((c₀.divisors.card : ℕ) : ℝ) * (L : ℝ) ^ ((76 : ℝ) / 77) :=
          mul_nonneg hτ hLr72
        nlinarith [h1]

/-- The final numerical absorption: the Abel bound plus the prime-power correction are dominated
by `(C₂ (1/log 2 + Cv) + Cn + 1) · c·d·kk·Lr·Δ` when `τ ≤ c`, `1 ≤ d`, `1 ≤ kk`, `1 ≤ Δ`. -/
private lemma psiFinal_absorb (C₂ Cv Cn c d kk Lr Δ τ : ℝ)
    (hC₂ : 0 < C₂) (hCv : 0 < Cv) (hCn : 0 < Cn) (hc : 0 ≤ c) (hd : 1 ≤ d)
    (hkk : 1 ≤ kk) (hLr : 0 ≤ Lr) (hΔ : 1 ≤ Δ) (hτ : τ ≤ c) :
    C₂ * c * d * kk * Lr * (1 / Real.log 2 + Cv * Δ) + Cn * τ * Lr
      ≤ (C₂ * (1 / Real.log 2 + Cv) + Cn + 1) * c * d * kk * Lr * Δ := by
  have hh : 0 < 1 / Real.log 2 := by positivity
  have hA : 1 / Real.log 2 + Cv * Δ ≤ (1 / Real.log 2 + Cv) * Δ := by
    nlinarith [hCv, hΔ, hh]
  have hprod1 : C₂ * c * d * kk * Lr * (1 / Real.log 2 + Cv * Δ)
      ≤ C₂ * (1 / Real.log 2 + Cv) * c * d * kk * Lr * Δ := by
    have h0 : 0 ≤ C₂ * c * d * kk * Lr :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hC₂) hc) (by linarith)) (by linarith)) hLr
    calc C₂ * c * d * kk * Lr * (1 / Real.log 2 + Cv * Δ)
        ≤ C₂ * c * d * kk * Lr * ((1 / Real.log 2 + Cv) * Δ) :=
          mul_le_mul_of_nonneg_left hA h0
      _ = C₂ * (1 / Real.log 2 + Cv) * c * d * kk * Lr * Δ := by ring
  have hprod2 : Cn * τ * Lr ≤ Cn * c * d * kk * Lr * Δ := by
    have h1 : τ * Lr ≤ c * d * kk * Lr * Δ := by
      have hcd : c * 1 ≤ c * d := mul_le_mul_of_nonneg_left hd hc
      have hcdk : c * d * 1 ≤ c * d * kk :=
        mul_le_mul_of_nonneg_left hkk (mul_nonneg hc (by linarith))
      have hcdkΔ : c * d * kk * 1 ≤ c * d * kk * Δ :=
        mul_le_mul_of_nonneg_left hΔ (mul_nonneg (mul_nonneg hc (by linarith)) (by linarith))
      rw [mul_one] at hcd hcdk hcdkΔ
      have h2 : τ ≤ c * d * kk * Δ := by linarith
      calc τ * Lr ≤ (c * d * kk * Δ) * Lr := mul_le_mul_of_nonneg_right h2 hLr
        _ = c * d * kk * Lr * Δ := by ring
    calc Cn * τ * Lr = Cn * (τ * Lr) := by ring
      _ ≤ Cn * (c * d * kk * Lr * Δ) := mul_le_mul_of_nonneg_left h1 (le_of_lt hCn)
      _ = Cn * c * d * kk * Lr * Δ := by ring
  have hM : 0 ≤ c * d * kk * Lr * Δ :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hc (by linarith)) (by linarith)) hLr) (by linarith)
  nlinarith [hprod1, hprod2, hM]

/-- **Prime sums of quadratic eigenvalues, from Theorem 2ψ.**  From `h2psi : Theorem2psi` (i.e.
`Σ_{n ≤ x} Λ(n) λ(c n) ≪ c·d(|k|+1)·x^{76/77}`) we obtain the same bound for a sum over *primes*,
summed by parts against a smooth weight `u ↦ P (c₀ u)`:
`Σ_{p ≤ L} P(c₀ p) λ(c₀ p) ≪ c₀ d(|k|+1) L^{76/77} (K|b-a| + 1)`.

Method: write `Σ_p P(c₀p)λ(c₀p) = Σ_{n ≤ L} Λ(n) P(c₀n)/log n · λ(c₀n)` minus the prime-power
part; Abel-summation over `n` against the partial sums `Σ_{n≤y} Λ(n)λ(c₀n)`, which `h2psi` bounds
(this removes `log n` and the weight), and bound the prime-power correction by `‖λ(m)‖ ≤ 4τ(m)`
(proved from the definition of `quadEigen`: at most `r₂(m) ≤ 4 τ(m)` Gaussian integers have norm
`m`). -/
theorem primeSumPsi (h2psi : Theorem2psi) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (chi : GaussianInt → ℂ) (k : ℤ) (d c0 L : ℕ) (P : ℝ → ℝ) (a b K : ℝ),
        1 ≤ d → 1 ≤ c0 → 1 ≤ L →
        (∀ z, ‖chi z‖ ≤ 1) →
        (∀ z1 z2 : GaussianInt, IsCoprime z1 z2 → chi (z1 * z2) = chi z1 * chi z2) →
        (∀ (a' b' : ℤ), chi (⟨a' + 4 * (d : ℤ), b'⟩ : GaussianInt) = chi ⟨a', b'⟩) →
        (∀ (a' b' : ℤ), chi (⟨a', b' + 4 * (d : ℤ)⟩ : GaussianInt) = chi ⟨a', b'⟩) →
        ContDiff ℝ 1 P → 0 ≤ a →
        (∀ u, 0 ≤ P u) → (∀ u, P u ≤ 1) →
        (∀ u, P u ≠ 0 → a < u ∧ u ≤ b) → (∀ u, |deriv P u| ≤ K) →
        ‖∑ p ∈ (Finset.Icc 1 L).filter (fun p => p.Prime),
            (P ((c0 : ℝ) * p) : ℂ) * quadEigen (grossenChar chi k) (c0 * p)‖
          ≤ C * (c0 : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1) * (L : ℝ) ^ ((76 : ℝ) / 77)
              * (K * |b - a| + 1) := by
  obtain ⟨C₂, hC₂pos, hC₂⟩ := h2psi
  obtain ⟨Cv, hCvpos, hCv⟩ := psiVariation'
  obtain ⟨Cn, hCnpos, hCn⟩ := psiNonPrimeSum'
  refine ⟨C₂ * (1 / Real.log 2 + Cv) + Cn + 1, by positivity, ?_⟩
  intro chi k d c0 L P a b K hd hc0 hL hchi hmul h4d1 h4d2 hP ha hnn h1 hsup hK
  have hKnn : 0 ≤ K := le_trans (abs_nonneg (deriv P 0)) (hK 0)
  have hc0R : (1 : ℝ) ≤ (c0 : ℝ) := by exact_mod_cast hc0
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hLr : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hPabs : ∀ u : ℝ, |P u| ≤ 1 := fun u => by rw [abs_of_nonneg (hnn u)]; exact h1 u
  by_cases hba : b ≤ a
  · -- degenerate case: P vanishes identically
    have hPzero : ∀ u : ℝ, P u = 0 := by
      intro u
      by_contra hu
      obtain ⟨h1', h2'⟩ := hsup u hu
      exact absurd (le_trans h2' hba) (not_le.mpr h1')
    have hsum0 : (∑ p ∈ (Finset.Icc 1 L).filter (fun p => p.Prime),
        (P ((c0 : ℝ) * p) : ℂ) * quadEigen (grossenChar chi k) (c0 * p)) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      rw [hPzero, Complex.ofReal_zero, zero_mul]
    rw [hsum0, norm_zero]
    positivity
  · -- main case b > a
    have hab : a < b := not_le.mp hba
    have hbda : 0 < b - a := by linarith
    set B : ℝ := C₂ * (c0 : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1) * (L : ℝ) ^ ((76 : ℝ) / 77) with hBdef
    have hBnn : 0 ≤ B := by
      rw [hBdef]
      have hLrp : 0 < (L : ℝ) ^ ((76 : ℝ) / 77) := Real.rpow_pos_of_pos (by linarith) _
      positivity
    have hbound : ∀ t : ℕ, t ≤ L → ‖∑ m ∈ Finset.Icc 1 t,
        (((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) * quadEigen (grossenChar chi k) (c0 * m))‖ ≤ B := by
      intro t ht
      rcases Nat.eq_zero_or_pos t with h0 | h0
      · subst h0
        have hempty : Finset.Icc 1 (0 : ℕ) = ∅ := Finset.Icc_eq_empty_of_lt (by norm_num)
        rw [hempty, Finset.sum_empty, norm_zero]
        exact hBnn
      · have ht1 : (1 : ℕ) ≤ t := h0
        have h2psi_t := hC₂ t c0 d k chi hc0 hd ht1 hchi hmul h4d1 h4d2
        calc ‖∑ m ∈ Finset.Icc 1 t,
              (((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) * quadEigen (grossenChar chi k) (c0 * m))‖
            ≤ C₂ * (c0 : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1) * (t : ℝ) ^ ((76 : ℝ) / 77) := h2psi_t
          _ ≤ C₂ * (c0 : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1) * (L : ℝ) ^ ((76 : ℝ) / 77) := by
              have htL : (t : ℝ) ≤ (L : ℝ) := by exact_mod_cast ht
              have hpow : (t : ℝ) ^ ((76 : ℝ) / 77) ≤ (L : ℝ) ^ ((76 : ℝ) / 77) :=
                Real.rpow_le_rpow (Nat.cast_nonneg t) htL (by norm_num)
              exact mul_le_mul_of_nonneg_left hpow (by positivity)
          _ = B := hBdef.symm
    have hAbel := psiAbel
      (fun m => ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) * quadEigen (grossenChar chi k) (c0 * m))
      (psiW P (c0 : ℝ)) L B hBnn hbound
    have hwL : ‖psiW P (c0 : ℝ) L‖ ≤ 1 / Real.log 2 := by
      rcases lt_or_ge L 2 with hlt | hge
      · have hL1 : L = 1 := by omega
        rw [hL1, psiW_of_not_two_le (by norm_num : ¬ (2 : ℕ) ≤ 1)]
        simp only [norm_zero]
        positivity
      · exact norm_psiW_le hge hPabs
    have hVar : (∑ m ∈ Finset.Icc 1 (L - 1),
        ‖psiW P (c0 : ℝ) (m + 1) - psiW P (c0 : ℝ) m‖) ≤ Cv * (K * (b - a) + 1) :=
      hCv P a b K (c0 : ℝ) L hP hab hc0R hnn h1 hsup hK
    have hMain : ‖∑ m ∈ Finset.Icc 1 L,
          (((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) * quadEigen (grossenChar chi k) (c0 * m))
            * psiW P (c0 : ℝ) m‖ ≤ B * (1 / Real.log 2 + Cv * (K * (b - a) + 1)) := by
      refine le_trans hAbel ?_
      refine mul_le_mul_of_nonneg_left ?_ hBnn
      linarith
    have hterm : ∀ m ∈ Finset.Icc 1 L,
        (((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) * quadEigen (grossenChar chi k) (c0 * m))
            * psiW P (c0 : ℝ) m
          = if 2 ≤ m then
              ((ArithmeticFunction.vonMangoldt m / Real.log (m : ℝ) : ℝ) : ℂ)
                * ((P ((c0 : ℝ) * (m : ℝ)) : ℝ) : ℂ) * quadEigen (grossenChar chi k) (c0 * m)
            else 0 := by
      intro m hm
      rw [Finset.mem_Icc] at hm
      by_cases h2 : 2 ≤ m
      · rw [if_pos h2, psiW_of_two_le h2]
        have hcast : ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ)
              * ((P ((c0 : ℝ) * (m : ℝ)) / Real.log (m : ℝ) : ℝ) : ℂ)
            = ((ArithmeticFunction.vonMangoldt m / Real.log (m : ℝ) : ℝ) : ℂ)
              * ((P ((c0 : ℝ) * (m : ℝ)) : ℝ) : ℂ) := by
          rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
          congr 1
          ring
        calc (((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) * quadEigen (grossenChar chi k) (c0 * m))
              * ((P ((c0 : ℝ) * (m : ℝ)) / Real.log (m : ℝ) : ℝ) : ℂ)
            = (((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ)
                * ((P ((c0 : ℝ) * (m : ℝ)) / Real.log (m : ℝ) : ℝ) : ℂ))
              * quadEigen (grossenChar chi k) (c0 * m) := by ring
          _ = (((ArithmeticFunction.vonMangoldt m / Real.log (m : ℝ) : ℝ) : ℂ)
                * ((P ((c0 : ℝ) * (m : ℝ)) : ℝ) : ℂ))
              * quadEigen (grossenChar chi k) (c0 * m) := by rw [hcast]
          _ = ((ArithmeticFunction.vonMangoldt m / Real.log (m : ℝ) : ℝ) : ℂ)
                * ((P ((c0 : ℝ) * (m : ℝ)) : ℝ) : ℂ)
                * quadEigen (grossenChar chi k) (c0 * m) := by ring
      · have hm1 : m = 1 := by omega
        rw [hm1, if_neg (by norm_num : ¬ (2 : ℕ) ≤ 1), ArithmeticFunction.vonMangoldt_apply_one]
        simp
    have hsum_eq : (∑ m ∈ Finset.Icc 1 L,
          (((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) * quadEigen (grossenChar chi k) (c0 * m))
            * psiW P (c0 : ℝ) m)
        = ∑ m ∈ Finset.Icc 2 L,
          ((ArithmeticFunction.vonMangoldt m / Real.log (m : ℝ) : ℝ) : ℂ)
            * ((P ((c0 : ℝ) * (m : ℝ)) : ℝ) : ℂ) * quadEigen (grossenChar chi k) (c0 * m) := by
      rw [Finset.sum_congr rfl hterm]
      rw [← Finset.sum_filter]
      have hfilt : (Finset.Icc 1 L).filter (fun m => 2 ≤ m) = Finset.Icc 2 L := by
        ext m
        simp only [Finset.mem_filter, Finset.mem_Icc]
        omega
      rw [hfilt]
    have hsplit : (∑ m ∈ Finset.Icc 2 L,
          ((ArithmeticFunction.vonMangoldt m / Real.log (m : ℝ) : ℝ) : ℂ)
            * ((P ((c0 : ℝ) * (m : ℝ)) : ℝ) : ℂ) * quadEigen (grossenChar chi k) (c0 * m))
        = (∑ m ∈ (Finset.Icc 2 L).filter (fun m => m.Prime),
              ((ArithmeticFunction.vonMangoldt m / Real.log (m : ℝ) : ℝ) : ℂ)
                * ((P ((c0 : ℝ) * (m : ℝ)) : ℝ) : ℂ) * quadEigen (grossenChar chi k) (c0 * m))
          + ∑ m ∈ (Finset.Icc 2 L).filter (fun m => ¬ m.Prime),
              ((ArithmeticFunction.vonMangoldt m / Real.log (m : ℝ) : ℝ) : ℂ)
                * ((P ((c0 : ℝ) * (m : ℝ)) : ℝ) : ℂ) * quadEigen (grossenChar chi k) (c0 * m) :=
      (Finset.sum_filter_add_sum_filter_not (s := Finset.Icc 2 L) (p := fun m => m.Prime)
        (f := fun m => ((ArithmeticFunction.vonMangoldt m / Real.log (m : ℝ) : ℝ) : ℂ)
                * ((P ((c0 : ℝ) * (m : ℝ)) : ℝ) : ℂ)
                * quadEigen (grossenChar chi k) (c0 * m))).symm
    have hprime : (∑ m ∈ (Finset.Icc 2 L).filter (fun m => m.Prime),
              ((ArithmeticFunction.vonMangoldt m / Real.log (m : ℝ) : ℝ) : ℂ)
                * ((P ((c0 : ℝ) * (m : ℝ)) : ℝ) : ℂ) * quadEigen (grossenChar chi k) (c0 * m))
        = ∑ p ∈ (Finset.Icc 1 L).filter (fun p => p.Prime),
            (P ((c0 : ℝ) * p) : ℂ) * quadEigen (grossenChar chi k) (c0 * p) := by
      have hfilt : (Finset.Icc 2 L).filter (fun m => m.Prime)
          = (Finset.Icc 1 L).filter (fun p => p.Prime) := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_Icc]
        constructor
        · rintro ⟨⟨-, h2⟩, hp⟩; exact ⟨⟨hp.one_lt.le, h2⟩, hp⟩
        · rintro ⟨⟨-, h2⟩, hp⟩; exact ⟨⟨hp.two_le, h2⟩, hp⟩
      rw [hfilt]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mem_filter] at hp
      have hΛ : ArithmeticFunction.vonMangoldt p / Real.log (p : ℝ) = 1 := psiVonMangoldtPrime hp.2
      rw [hΛ]
      simp
    have hlam4 : ∀ n : ℕ, ‖quadEigen (grossenChar chi k) n‖ ≤ 4 * ((n.divisors.card : ℕ) : ℝ) :=
      fun n => normQuadEigenLe (grossenChar chi k)
        (fun z => norm_grossenChar_le_one chi k hchi z) n
    have hnp := hCn c0 L P (fun n => quadEigen (grossenChar chi k) n) hc0 hL hPabs hlam4
    have hId : (∑ m ∈ Finset.Icc 1 L,
          (((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) * quadEigen (grossenChar chi k) (c0 * m))
            * psiW P (c0 : ℝ) m)
        = (∑ p ∈ (Finset.Icc 1 L).filter (fun p => p.Prime),
              (P ((c0 : ℝ) * p) : ℂ) * quadEigen (grossenChar chi k) (c0 * p))
          + ∑ m ∈ (Finset.Icc 2 L).filter (fun m => ¬ m.Prime),
              ((ArithmeticFunction.vonMangoldt m / Real.log (m : ℝ) : ℝ) : ℂ)
                * ((P ((c0 : ℝ) * (m : ℝ)) : ℝ) : ℂ) * quadEigen (grossenChar chi k) (c0 * m) := by
      rw [hsum_eq, hsplit, hprime]
    have htri : ‖∑ p ∈ (Finset.Icc 1 L).filter (fun p => p.Prime),
            (P ((c0 : ℝ) * p) : ℂ) * quadEigen (grossenChar chi k) (c0 * p)‖
        ≤ B * (1 / Real.log 2 + Cv * (K * (b - a) + 1))
          + Cn * ((c0.divisors.card : ℕ) : ℝ) * (L : ℝ) ^ ((76 : ℝ) / 77) := by
      have hsub : (∑ p ∈ (Finset.Icc 1 L).filter (fun p => p.Prime),
              (P ((c0 : ℝ) * p) : ℂ) * quadEigen (grossenChar chi k) (c0 * p))
            = (∑ m ∈ Finset.Icc 1 L,
                (((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ)
                    * quadEigen (grossenChar chi k) (c0 * m))
                  * psiW P (c0 : ℝ) m)
              - ∑ m ∈ (Finset.Icc 2 L).filter (fun m => ¬ m.Prime),
                  ((ArithmeticFunction.vonMangoldt m / Real.log (m : ℝ) : ℝ) : ℂ)
                    * ((P ((c0 : ℝ) * (m : ℝ)) : ℝ) : ℂ)
                    * quadEigen (grossenChar chi k) (c0 * m) := by
        rw [hId]
        ring
      rw [hsub]
      refine le_trans (norm_sub_le _ _) ?_
      exact add_le_add hMain hnp
    rw [abs_of_pos hbda]
    refine le_trans htri ?_
    rw [hBdef]
    have hkk1 : (1 : ℝ) ≤ |(k : ℝ)| + 1 := by
      have := abs_nonneg (k : ℝ); linarith
    exact psiFinal_absorb C₂ Cv Cn (c0 : ℝ) (d : ℝ) (|(k : ℝ)| + 1)
      ((L : ℝ) ^ ((76 : ℝ) / 77)) (K * (b - a) + 1) (((c0.divisors.card : ℕ)) : ℝ)
      hC₂pos hCvpos hCnpos (Nat.cast_nonneg c0) hdR hkk1
      (Real.rpow_nonneg (Nat.cast_nonneg L) _) (by nlinarith [hKnn, hbda])
      (by exact_mod_cast Nat.card_divisors_le_self c0)

end

end Work.FIArea7
