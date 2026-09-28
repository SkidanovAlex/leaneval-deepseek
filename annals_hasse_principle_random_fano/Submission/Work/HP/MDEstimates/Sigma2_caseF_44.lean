import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MDCommon
import Submission.Work.HP.Sig2.Sigma2_caseF
import Submission.Work.HP.Sig2.caseF_arith

/-!
# The `(4,4)` case of the case-F estimate for the large-`μ` part of the second moment

Browning--Le Boudec--Sawin, *The Hasse principle for random Fano hypersurfaces*, Annals 2023:
the `(4,4)` case (`d = n = 4`, the quartic threefold) of the estimate
`Σ_{𝓕} pairS₀ ≤ K A^{N-2-1/3} B²` for the "case F" pairs of the large-`μ` half of the
second moment.

`Work.HP.Sig2.Sigma2_caseF` states exactly this for all `2 ≤ d ≤ n` with
`(d,n) ∉ {(2,2),(3,3),(4,4)}`.  Its hypothesis `(d,n) ≠ (4,4)` is used only to feed the
final real-variable arithmetic `Work.HP.Sig2.caseF_arith`, and that arithmetic lemma does
not in fact use the hypothesis: at `(4,4)` one has `m = n + 1 - d = 1` and the two
exponents occurring in `caseF_exp_neg` are `4/3 - 4 + 2 = -2/3 < 0` and
`(5-36)/6 + 7 - 2 = -1/6 < 0`, so `caseF_master` applies and the bound is valid.

This file therefore repeats (i) the arithmetic without the `(4,4)` exclusion
(`caseF_arith_no44`) and (ii) the assembly of `Sigma2_caseF` without it
(`Sigma2_caseF_no44`), and then specialises to `(d,n) = (4,4)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MvPolynomial Finset
open scoped BigOperators

namespace Work.HP.Sig2

open Work.HP

/-! ## The real-variable arithmetic without the `(4,4)` exclusion -/

theorem caseF_arith_no44 (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) (h22 : (d, n) ≠ (2, 2))
    (h33 : (d, n) ≠ (3, 3)) (C : ℝ) (hC : 0 ≤ C) :
    ∃ K B₀ : ℝ, 0 < K ∧ 0 < B₀ ∧ ∀ A B : ℝ, B₀ ≤ B → B / Real.log B ≤ A → A ≤ B ^ 2 →
      C * (A ^ ((NN d n : ℝ) - (n : ℝ) - 1) * (B ^ (1 / ((n : ℝ) + 1 - d))) ^ (2 * ((n : ℝ) - d))
              * B ^ (4 / ((n : ℝ) + 1 - d))
          + A ^ ((NN d n : ℝ) - (n : ℝ) - 2 - ((n : ℝ) - 1) / 2)
              * (B ^ (1 / ((n : ℝ) + 1 - d))) ^ ((n : ℝ) - 1)
              * B ^ (4 / ((n : ℝ) + 1 - d)))
          * (Real.log B + 1) ^ 3
      ≤ K * A ^ ((NN d n : ℝ) - 2 - (1 : ℝ) / 3) * B ^ 2 := by
  obtain ⟨hmpos, hexp1, hexp2⟩ := caseF_exp_neg d n hd hdn h22 h33
  have hmcast : (((n + 1 - d : ℕ)) : ℝ) = (n : ℝ) + 1 - d := by
    rw [Nat.cast_sub (by omega : d ≤ n + 1), Nat.cast_add, Nat.cast_one]
  have hexp1' : 4 / 3 - (n : ℝ) + 2 / ((n : ℝ) + 1 - d) < 0 := by
    rw [← hmcast]; exact hexp1
  have hexp2' : (5 - 9 * (n : ℝ)) / 6 + (((n : ℝ) + 3) / ((n : ℝ) + 1 - d) - 2) < 0 := by
    rw [← hmcast]; linarith [hexp2]
  have hd2n : (2 : ℝ) ≤ (n : ℝ) := by
    have h : 2 ≤ n := le_trans hd hdn
    exact_mod_cast h
  have hne1 : 4 / 3 - (n : ℝ) < 0 := by linarith
  have hne2 : (5 - 9 * (n : ℝ)) / 6 < 0 := by linarith
  obtain ⟨K₁, B₁, hK₁, hB₁, hb₁⟩ :=
    caseF_master (4 / 3 - (n : ℝ)) (2 / ((n : ℝ) + 1 - d)) 3 hne1 hexp1'
  obtain ⟨K₂, B₂, hK₂, hB₂, hb₂⟩ :=
    caseF_master ((5 - 9 * (n : ℝ)) / 6) (((n : ℝ) + 3) / ((n : ℝ) + 1 - d) - 2) 3 hne2 hexp2'
  refine ⟨max (C * (K₁ + K₂)) 1, max B₁ (max B₂ (Real.exp 2)), ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le one_pos (le_max_right _ _)
  · exact lt_of_lt_of_le hB₁ (le_max_left _ _)
  · intro A B hB hAle hAge
    have hB₁le : B₁ ≤ B := le_trans (le_max_left _ _) hB
    have hB₂le : B₂ ≤ B := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hB
    have hexpB : Real.exp 2 ≤ B := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hB
    have hexp2gt1 : (1 : ℝ) < Real.exp 2 := by
      have h := Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 2)
      rwa [Real.exp_zero] at h
    have hB1gt : (1 : ℝ) < B := lt_of_lt_of_le hexp2gt1 hexpB
    have hBpos : 0 < B := by linarith
    have hlogpos : 0 < Real.log B := Real.log_pos hB1gt
    have hApos : 0 < A := lt_of_lt_of_le (div_pos hBpos hlogpos) hAle
    obtain ⟨hd1, hd2⟩ := caseF_decomp d n hdn A B hApos hBpos
    have h1 := hb₁ A B hB₁le hAle hAge
    have h2 := hb₂ A B hB₂le hAle hAge
    have hPnn : (0 : ℝ) ≤ A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2 :=
      mul_nonneg (Real.rpow_nonneg (le_of_lt hApos) _) (sq_nonneg B)
    have hCnn : (0 : ℝ) ≤ C * (A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2) := mul_nonneg hC hPnn
    have hKle : C * (K₁ + K₂) ≤ max (C * (K₁ + K₂)) 1 := le_max_left _ _
    set T1 : ℝ := A ^ ((NN d n : ℝ) - (n : ℝ) - 1)
      * (B ^ (1 / ((n : ℝ) + 1 - d))) ^ (2 * ((n : ℝ) - d)) * B ^ (4 / ((n : ℝ) + 1 - d)) with hT1
    set T2 : ℝ := A ^ ((NN d n : ℝ) - (n : ℝ) - 2 - ((n : ℝ) - 1) / 2)
      * (B ^ (1 / ((n : ℝ) + 1 - d))) ^ ((n : ℝ) - 1) * B ^ (4 / ((n : ℝ) + 1 - d)) with hT2
    calc C * (T1 + T2) * (Real.log B + 1) ^ 3
        = C * (A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2)
              * (A ^ (4 / 3 - (n : ℝ)) * B ^ (2 / ((n : ℝ) + 1 - d)) * (Real.log B + 1) ^ 3)
          + C * (A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2)
              * (A ^ ((5 - 9 * (n : ℝ)) / 6)
                  * B ^ (((n : ℝ) + 3) / ((n : ℝ) + 1 - d) - 2) * (Real.log B + 1) ^ 3) := by
          rw [hd1, hd2]
          ring
      _ ≤ C * (A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2) * K₁
          + C * (A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2) * K₂ := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left h1 hCnn
          · exact mul_le_mul_of_nonneg_left h2 hCnn
      _ = C * (K₁ + K₂) * (A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2) := by ring
      _ ≤ max (C * (K₁ + K₂)) 1 * (A ^ ((NN d n : ℝ) - 7 / 3) * B ^ 2) :=
          mul_le_mul_of_nonneg_right hKle hPnn
      _ = max (C * (K₁ + K₂)) 1 * A ^ ((NN d n : ℝ) - 2 - (1 : ℝ) / 3) * B ^ 2 := by
          have hN : A ^ ((NN d n : ℝ) - 2 - (1 : ℝ) / 3) = A ^ ((NN d n : ℝ) - 7 / 3) := by
            congr 1
            ring
          rw [hN]
          ring

/-! ## The case-F estimate without the `(4,4)` exclusion -/

theorem Sigma2_caseF_no44 (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) (h22 : (d, n) ≠ (2, 2))
    (h33 : (d, n) ≠ (3, 3)) :
    ∃ K B₀ : ℝ, 0 < K ∧ ∀ A B : ℝ, B₀ ≤ B → B / Real.log B ≤ A → A ≤ B ^ 2 →
      (∑ᶠ p ∈ {p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ) | p ∈ Omega d n B ∧
          ¬ (muXY n p.1 p.2 ≤ A) ∧
          dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) * dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ^ 2
            ≤ dmin 3 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) * (eNorm p.1 * eNorm p.2)},
        pairS0 d n A p)
        ≤ K * A ^ ((NN d n : ℝ) - 2 - (1 : ℝ) / 3) * B ^ 2 := by
  have hn2 : 2 ≤ n := le_trans hd hdn
  have hn3 : 3 ≤ n := by
    rcases Nat.lt_or_ge n 3 with h | h
    · have hn : n = 2 := by omega
      have hd2 : d = 2 := by omega
      exact absurd (by simp [hn, hd2]) h22
    · exact h
  have hn2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hN : n + 2 ≤ NN d n := NN_ge_add_two d n hd hdn
  obtain ⟨Cdet, hCdetpos, hCdet⟩ := MDEstimates.detGam_lower d n hd hn2
  obtain ⟨KF, hKFpos, hKF⟩ := per_pair_sum_bound_F d n hd hdn hN Cdet hCdetpos hCdet
  obtain ⟨Kd, hKdpos, hKd⟩ := cf_sum_dmin_rpow_le d n hd hn3
  set C : ℝ := KF * max 1 Kd * max 1 ((3 * (n : ℝ) ^ 2) ^ (((n : ℝ) - 1) / 2)) with hCdef
  have hCnn : 0 ≤ C := by rw [hCdef]; positivity
  obtain ⟨Kar, Bor, hKar, hBor, harith⟩ := caseF_arith_no44 d n hd hdn h22 h33 C hCnn
  refine ⟨Kar, max Bor 8, hKar, ?_⟩
  intro A B hB hA hA2
  have hB8 : (8 : ℝ) ≤ B := le_trans (le_max_right _ _) hB
  have hB1 : (1 : ℝ) ≤ B := by linarith
  have hBpos : (0 : ℝ) < B := by linarith
  have hlogB1 : 1 ≤ Real.log B := by
    rw [Real.le_log_iff_exp_le hBpos]
    linarith [Real.exp_one_lt_d9]
  have hlogBpos : 0 < Real.log B := by linarith
  have hA1 : 1 ≤ A := by
    have h1 : (1 : ℝ) ≤ B / Real.log B := by
      rw [le_div_iff₀ hlogBpos]
      have := Real.log_le_self (le_of_lt hBpos)
      linarith
    linarith
  have hApos : 0 < A := by linarith
  set S := caseFset d n A B with hSdef
  have hSfin : S.Finite := caseFset_finite d n A B
  set T : Finset ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) := hSfin.toFinset with hTdef
  have hTmem : ∀ p, p ∈ T ↔ p ∈ S := fun p => Set.Finite.mem_toFinset hSfin
  have hsum_eq : (∑ᶠ p ∈ S, pairS0 d n A p) = ∑ p ∈ T, pairS0 d n A p := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hSfin, hTdef]
  change (∑ᶠ p ∈ S, pairS0 d n A p) ≤ Kar * A ^ ((NN d n : ℝ) - 2 - (1 : ℝ) / 3) * B ^ 2
  rw [hsum_eq]
  have hST : ∀ p ∈ T, p ∈ caseFset d n A B := fun p hp => (hTmem p).mp hp
  have hΩT : ∀ p ∈ T, p ∈ Omega d n B := fun p hp => (caseF_facts d n (hST p hp)).1
  have hμT : ∀ p ∈ T, A < muXY n p.1 p.2 := fun p hp =>
    lt_of_not_ge (caseF_facts d n (hST p hp)).2.2.2.2.2.2.1
  have hFT : ∀ p ∈ T, dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ))
      * dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ^ 2
      ≤ dmin 3 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) * (eNorm p.1 * eNorm p.2) := fun p hp =>
    (caseF_facts d n (hST p hp)).2.2.2.2.2.2.2
  have h1 := hKF A B T hA1 hB1 hΩT hμT hFT
  have hΩfin : (Omega d n B).Finite := (MDBasic.finite_sets d n A B (fun _ => True)).2.2
  have hTsubO : T ⊆ hΩfin.toFinset := fun p hp => (Set.Finite.mem_toFinset hΩfin).mpr (hΩT p hp)
  have hsum1Ω : (∑ p ∈ hΩfin.toFinset,
      (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ))) ^ (-(2 * (n : ℝ) - 1)))
      ≤ Kd * B ^ (4 / ((n : ℝ) + 1 - d)) * (Real.log B + 1) ^ 3 := by
    have hh := hKd 2 le_rfl (by omega : 2 ≤ n + 1) (2 * (n : ℝ) - 1) B (by linarith [hn2R]) hB1
    rw [finsum_mem_eq_finite_toFinset_sum _ hΩfin] at hh
    rw [show (2 : ℝ) * (↑(2 : ℕ) : ℝ) / ((n : ℝ) + 1 - d) = 4 / ((n : ℝ) + 1 - d) by norm_num] at hh
    exact hh
  have hT1 : (∑ p ∈ T, (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ))) ^ (-(2 * (n : ℝ) - 1)))
      ≤ Kd * B ^ (4 / ((n : ℝ) + 1 - d)) * (Real.log B + 1) ^ 3 :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg hTsubO
      (fun i _ _ => Real.rpow_nonneg (dmin_nonneg 2 _) _)) hsum1Ω
  have hsum2Ω : (∑ p ∈ hΩfin.toFinset,
      (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ))) ^ (-((n : ℝ) - 1)))
      ≤ Kd * B ^ (4 / ((n : ℝ) + 1 - d)) * (Real.log B + 1) ^ 3 := by
    have hh := hKd 2 le_rfl (by omega : 2 ≤ n + 1) ((n : ℝ) - 1) B le_rfl hB1
    rw [finsum_mem_eq_finite_toFinset_sum _ hΩfin] at hh
    rw [show (2 : ℝ) * (↑(2 : ℕ) : ℝ) / ((n : ℝ) + 1 - d) = 4 / ((n : ℝ) + 1 - d) by norm_num] at hh
    exact hh
  have hT2 : (∑ p ∈ T, (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ))) ^ (-((n : ℝ) - 1)))
      ≤ Kd * B ^ (4 / ((n : ℝ) + 1 - d)) * (Real.log B + 1) ^ 3 :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg hTsubO
      (fun i _ _ => Real.rpow_nonneg (dmin_nonneg 2 _) _)) hsum2Ω
  set W : ℝ := B ^ (1 / ((n : ℝ) + 1 - d)) with hWdef
  have hWnn : 0 ≤ W := by rw [hWdef]; exact Real.rpow_nonneg (le_of_lt hBpos) _
  set K2 : ℝ := (3 * (n : ℝ) ^ 2) ^ (((n : ℝ) - 1) / 2) * W ^ ((n : ℝ) - 1)
      * A ^ (-(((n : ℝ) - 1) / 2)) with hK2def
  have hK2nn : 0 ≤ K2 := by rw [hK2def]; positivity
  have hcard := card_le_dmin2 d n hd hdn hApos hB1 T hST
  have hcard' : (T.card : ℝ) ≤ K2 * (Kd * B ^ (4 / ((n : ℝ) + 1 - d)) * (Real.log B + 1) ^ 3) :=
    le_trans hcard (mul_le_mul_of_nonneg_left hT2 hK2nn)
  have hA2nn : (0 : ℝ) ≤ A ^ ((NN d n : ℝ) - (n : ℝ) - 2) := by positivity
  have hQnn : (0 : ℝ) ≤ B ^ (4 / ((n : ℝ) + 1 - d)) * (Real.log B + 1) ^ 3 := by positivity
  have hA2K2 : A ^ ((NN d n : ℝ) - (n : ℝ) - 2) * K2
      = (3 * (n : ℝ) ^ 2) ^ (((n : ℝ) - 1) / 2)
        * A ^ ((NN d n : ℝ) - (n : ℝ) - 2 - ((n : ℝ) - 1) / 2) * W ^ ((n : ℝ) - 1) := by
    rw [hK2def,
      show A ^ ((NN d n : ℝ) - (n : ℝ) - 2)
          * ((3 * (n : ℝ) ^ 2) ^ (((n : ℝ) - 1) / 2) * W ^ ((n : ℝ) - 1)
            * A ^ (-(((n : ℝ) - 1) / 2)))
        = (3 * (n : ℝ) ^ 2) ^ (((n : ℝ) - 1) / 2) * W ^ ((n : ℝ) - 1)
          * (A ^ ((NN d n : ℝ) - (n : ℝ) - 2) * A ^ (-(((n : ℝ) - 1) / 2))) by ring,
      ← Real.rpow_add hApos]
    ring_nf
  have hcoef1 : KF * Kd ≤ C := by
    rw [hCdef]
    calc KF * Kd ≤ KF * max 1 Kd :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) (le_of_lt hKFpos)
      _ ≤ KF * max 1 Kd * max 1 ((3 * (n : ℝ) ^ 2) ^ (((n : ℝ) - 1) / 2)) := by
          rw [mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact le_mul_of_one_le_right (show (0 : ℝ) ≤ max 1 Kd from by positivity) (le_max_left _ _)
  have hcoef2 : KF * Kd * (3 * (n : ℝ) ^ 2) ^ (((n : ℝ) - 1) / 2) ≤ C := by
    rw [hCdef]
    calc KF * Kd * (3 * (n : ℝ) ^ 2) ^ (((n : ℝ) - 1) / 2)
        ≤ KF * max 1 Kd * (3 * (n : ℝ) ^ 2) ^ (((n : ℝ) - 1) / 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_max_right _ _)
            (le_of_lt hKFpos)) (by positivity)
      _ ≤ KF * max 1 Kd * max 1 ((3 * (n : ℝ) ^ 2) ^ (((n : ℝ) - 1) / 2)) :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
  have hmain : ∑ p ∈ T, pairS0 d n A p
      ≤ C * (A ^ ((NN d n : ℝ) - (n : ℝ) - 1) * W ^ (2 * ((n : ℝ) - d))
            + A ^ ((NN d n : ℝ) - (n : ℝ) - 2 - ((n : ℝ) - 1) / 2) * W ^ ((n : ℝ) - 1))
          * (B ^ (4 / ((n : ℝ) + 1 - d)) * (Real.log B + 1) ^ 3) := by
    have hstep1 : ∑ p ∈ T, pairS0 d n A p
        ≤ KF * (A ^ ((NN d n : ℝ) - (n : ℝ) - 1) * W ^ (2 * ((n : ℝ) - d))
              * (Kd * B ^ (4 / ((n : ℝ) + 1 - d)) * (Real.log B + 1) ^ 3)
            + A ^ ((NN d n : ℝ) - (n : ℝ) - 2)
              * (K2 * (Kd * B ^ (4 / ((n : ℝ) + 1 - d)) * (Real.log B + 1) ^ 3))) := by
      refine le_trans h1 ?_
      refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hKFpos)
      exact add_le_add
        (mul_le_mul_of_nonneg_left hT1 (by positivity))
        (mul_le_mul_of_nonneg_left hcard' hA2nn)
    have hstep2 : KF * (A ^ ((NN d n : ℝ) - (n : ℝ) - 1) * W ^ (2 * ((n : ℝ) - d))
              * (Kd * B ^ (4 / ((n : ℝ) + 1 - d)) * (Real.log B + 1) ^ 3)
            + A ^ ((NN d n : ℝ) - (n : ℝ) - 2)
              * (K2 * (Kd * B ^ (4 / ((n : ℝ) + 1 - d)) * (Real.log B + 1) ^ 3)))
        = KF * Kd * ((A ^ ((NN d n : ℝ) - (n : ℝ) - 1) * W ^ (2 * ((n : ℝ) - d))
              + (3 * (n : ℝ) ^ 2) ^ (((n : ℝ) - 1) / 2)
                * A ^ ((NN d n : ℝ) - (n : ℝ) - 2 - ((n : ℝ) - 1) / 2) * W ^ ((n : ℝ) - 1))
            * (B ^ (4 / ((n : ℝ) + 1 - d)) * (Real.log B + 1) ^ 3)) := by
      rw [show A ^ ((NN d n : ℝ) - (n : ℝ) - 2)
            * (K2 * (Kd * B ^ (4 / ((n : ℝ) + 1 - d)) * (Real.log B + 1) ^ 3))
          = (A ^ ((NN d n : ℝ) - (n : ℝ) - 2) * K2)
            * (Kd * B ^ (4 / ((n : ℝ) + 1 - d)) * (Real.log B + 1) ^ 3) by ring, hA2K2]
      ring
    have hstep3 : KF * Kd * ((A ^ ((NN d n : ℝ) - (n : ℝ) - 1) * W ^ (2 * ((n : ℝ) - d))
              + (3 * (n : ℝ) ^ 2) ^ (((n : ℝ) - 1) / 2)
                * A ^ ((NN d n : ℝ) - (n : ℝ) - 2 - ((n : ℝ) - 1) / 2) * W ^ ((n : ℝ) - 1))
            * (B ^ (4 / ((n : ℝ) + 1 - d)) * (Real.log B + 1) ^ 3))
        ≤ C * ((A ^ ((NN d n : ℝ) - (n : ℝ) - 1) * W ^ (2 * ((n : ℝ) - d))
              + A ^ ((NN d n : ℝ) - (n : ℝ) - 2 - ((n : ℝ) - 1) / 2) * W ^ ((n : ℝ) - 1))
            * (B ^ (4 / ((n : ℝ) + 1 - d)) * (Real.log B + 1) ^ 3)) := by
      have hX : (0 : ℝ) ≤ A ^ ((NN d n : ℝ) - (n : ℝ) - 1) * W ^ (2 * ((n : ℝ) - d)) := by
        positivity
      have hY : (0 : ℝ) ≤ A ^ ((NN d n : ℝ) - (n : ℝ) - 2 - ((n : ℝ) - 1) / 2)
          * W ^ ((n : ℝ) - 1) := by positivity
      have hZ : (0 : ℝ) ≤ B ^ (4 / ((n : ℝ) + 1 - d)) * (Real.log B + 1) ^ 3 := hQnn
      have e1 : (KF * Kd) * (A ^ ((NN d n : ℝ) - (n : ℝ) - 1) * W ^ (2 * ((n : ℝ) - d)))
          * (B ^ (4 / ((n : ℝ) + 1 - d)) * (Real.log B + 1) ^ 3)
          ≤ C * (A ^ ((NN d n : ℝ) - (n : ℝ) - 1) * W ^ (2 * ((n : ℝ) - d)))
          * (B ^ (4 / ((n : ℝ) + 1 - d)) * (Real.log B + 1) ^ 3) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef1 hX) hZ
      have e2 : (KF * Kd * (3 * (n : ℝ) ^ 2) ^ (((n : ℝ) - 1) / 2))
            * (A ^ ((NN d n : ℝ) - (n : ℝ) - 2 - ((n : ℝ) - 1) / 2) * W ^ ((n : ℝ) - 1))
          * (B ^ (4 / ((n : ℝ) + 1 - d)) * (Real.log B + 1) ^ 3)
          ≤ C * (A ^ ((NN d n : ℝ) - (n : ℝ) - 2 - ((n : ℝ) - 1) / 2) * W ^ ((n : ℝ) - 1))
          * (B ^ (4 / ((n : ℝ) + 1 - d)) * (Real.log B + 1) ^ 3) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef2 hY) hZ
      linarith [e1, e2]
    calc ∑ p ∈ T, pairS0 d n A p
        ≤ KF * (A ^ ((NN d n : ℝ) - (n : ℝ) - 1) * W ^ (2 * ((n : ℝ) - d))
              * (Kd * B ^ (4 / ((n : ℝ) + 1 - d)) * (Real.log B + 1) ^ 3)
            + A ^ ((NN d n : ℝ) - (n : ℝ) - 2)
              * (K2 * (Kd * B ^ (4 / ((n : ℝ) + 1 - d)) * (Real.log B + 1) ^ 3))) := hstep1
      _ = KF * Kd * ((A ^ ((NN d n : ℝ) - (n : ℝ) - 1) * W ^ (2 * ((n : ℝ) - d))
              + (3 * (n : ℝ) ^ 2) ^ (((n : ℝ) - 1) / 2)
                * A ^ ((NN d n : ℝ) - (n : ℝ) - 2 - ((n : ℝ) - 1) / 2) * W ^ ((n : ℝ) - 1))
            * (B ^ (4 / ((n : ℝ) + 1 - d)) * (Real.log B + 1) ^ 3)) := hstep2
      _ ≤ C * ((A ^ ((NN d n : ℝ) - (n : ℝ) - 1) * W ^ (2 * ((n : ℝ) - d))
              + A ^ ((NN d n : ℝ) - (n : ℝ) - 2 - ((n : ℝ) - 1) / 2) * W ^ ((n : ℝ) - 1))
            * (B ^ (4 / ((n : ℝ) + 1 - d)) * (Real.log B + 1) ^ 3)) := hstep3
      _ = C * (A ^ ((NN d n : ℝ) - (n : ℝ) - 1) * W ^ (2 * ((n : ℝ) - d))
            + A ^ ((NN d n : ℝ) - (n : ℝ) - 2 - ((n : ℝ) - 1) / 2) * W ^ ((n : ℝ) - 1))
          * (B ^ (4 / ((n : ℝ) + 1 - d)) * (Real.log B + 1) ^ 3) := by ring
  calc ∑ p ∈ T, pairS0 d n A p
      ≤ C * (A ^ ((NN d n : ℝ) - (n : ℝ) - 1) * W ^ (2 * ((n : ℝ) - d))
            + A ^ ((NN d n : ℝ) - (n : ℝ) - 2 - ((n : ℝ) - 1) / 2) * W ^ ((n : ℝ) - 1))
          * (B ^ (4 / ((n : ℝ) + 1 - d)) * (Real.log B + 1) ^ 3) := hmain
    _ = C * (A ^ ((NN d n : ℝ) - (n : ℝ) - 1) * (B ^ (1 / ((n : ℝ) + 1 - d))) ^ (2 * ((n : ℝ) - d))
            * B ^ (4 / ((n : ℝ) + 1 - d))
          + A ^ ((NN d n : ℝ) - (n : ℝ) - 2 - ((n : ℝ) - 1) / 2)
            * (B ^ (1 / ((n : ℝ) + 1 - d))) ^ ((n : ℝ) - 1)
            * B ^ (4 / ((n : ℝ) + 1 - d)))
          * (Real.log B + 1) ^ 3 := by rw [← hWdef]; ring
    _ ≤ Kar * A ^ ((NN d n : ℝ) - 2 - (1 : ℝ) / 3) * B ^ 2 :=
        harith A B (le_trans (le_max_left _ _) hB) hA hA2
end Work.HP.Sig2

namespace Work.HP.MDEstimates

/-! ## The `(4,4)` specialisation -/

theorem Sigma2_caseF_44 :
    ∃ K B₀ : ℝ, 0 < K ∧ ∀ A B : ℝ, B₀ ≤ B → B / Real.log B ≤ A → A ≤ B ^ 2 →
      (∑ᶠ p ∈ {p : (Fin 5 → ℤ) × (Fin 5 → ℤ) | p ∈ Omega 4 4 B ∧
          ¬ (muXY 4 p.1 p.2 ≤ A) ∧
          dmin 2 ({p.1, p.2} : Set (Fin 5 → ℤ)) * dmin 2 ({p.1, p.2} : Set (Fin 5 → ℤ)) ^ 2
            ≤ dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)) * (eNorm p.1 * eNorm p.2)},
        pairS0 4 4 A p)
        ≤ K * A ^ ((NN 4 4 : ℝ) - 2 - (1 : ℝ) / 3) * B ^ 2 := by
  exact Sig2.Sigma2_caseF_no44 4 4 (by norm_num) (by norm_num) (by decide) (by decide)

end Work.HP.MDEstimates
