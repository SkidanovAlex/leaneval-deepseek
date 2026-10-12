import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.Int.Star
import Mathlib.Data.Int.SuccPred
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.UBBInputs3.MatLoc.ProfileSupport
import Submission.Work.UBBInputs3.MatLoc.Rcorr_eq_one_sub_gamma
import Submission.Work.UBBInputs3.MatLoc.dSup_zero_add_dk_eq_qform
import Submission.Work.UBBInputs3.MatLoc.gamma_le_shift
import Submission.Work.UBBInputs3.MatLoc.gamma_le_two
import Submission.Work.UBBInputs3.MatLoc.normSq_winVec_sum
import Submission.Work.UBBInputs3.MatLoc.profG_eq
import Submission.Work.UBBInputs3.MatLoc.sum_winVec_qform
import Submission.Work.UBBInputs3.MatLoc.triMass_eq
import Submission.Work.UBBInputs3.MatLoc.winVec_support_mRange
import Submission.Work.UBBInputs3.MatLoc.window_clamp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.UBBInputs3.MatLoc.Main` — the Lieb–Solovej matrix localisation, assembled

This file assembles the chapter's pieces into the theorem FS §7 cite from the literature:

* `ls_localisation` — the general Lieb–Solovej `thm:Localizing large matrices`, with the
  universal constant `100`;
* `ls_localisation_band2` — the *band ≤ 2* corollary, the form FS and Brietzke–Solovej
  apply (their `A^{(k)} = 0` for `k ≥ 3`, so the error term is `100 M⁻²(|d₁| + 4|d₂|)`).

The two profile estimates that feed the constant are proved here from the delegated
bricks: `profG_le` (`G = 6/(2p²+4p+3) ≤ 12/M²`) and `gamma_le_ratio`
(`γ_k ≤ 100 k²/(k²+M²)`), the latter from `gamma_le_shift` + `gamma_le_two` + `profG_le`.
-/

noncomputable section

open scoped BigOperators
open Finset

namespace Work.UBBInputs3

open MatLoc

/-- **The first-difference energy of the triangle profile is `≤ 12/M²`.** -/
theorem profG_le (M p : ℕ) (hp : p = (M - 1) / 2) (hM : 1 ≤ M) :
    profG p ≤ 12 / (M : ℝ) ^ 2 := by
  rw [profG_eq]
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hXpos : (0 : ℝ) < 2 * (p : ℝ) ^ 2 + 4 * (p : ℝ) + 3 := by positivity
  have hq : (M : ℝ) - 2 ≤ 2 * (p : ℝ) := by
    have h2 : M - 1 ≤ 2 * p + 1 := by
      have hmod : (M - 1) % 2 ≤ 1 := by
        have := Nat.mod_lt (M - 1) (by norm_num : 0 < 2)
        omega
      have hd := Nat.div_add_mod (M - 1) 2
      rw [hp]
      omega
    have h2' : ((M - 1 : ℕ) : ℝ) ≤ 2 * (p : ℝ) + 1 := by exact_mod_cast h2
    have hcast : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
      rw [Nat.cast_sub hM]; norm_num
    rw [hcast] at h2'
    linarith
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := by positivity
  by_cases hM4 : 4 ≤ M
  · have hM4R : (4 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM4
    have hp4 : (M : ℝ) / 4 ≤ (p : ℝ) := by linarith
    have hden : (M : ℝ) ^ 2 / 2 ≤ 2 * (p : ℝ) ^ 2 + 4 * (p : ℝ) + 3 := by
      nlinarith [hp4, hp0, sq_nonneg ((p : ℝ) - (M : ℝ) / 4)]
    rw [div_le_iff₀ hXpos, div_mul_eq_mul_div,
      le_div_iff₀ (by positivity : (0 : ℝ) < (M : ℝ) ^ 2)]
    linarith
  · have hM4' : M < 4 := not_le.mp hM4
    have hp1 : p ≤ 1 := by rw [hp]; omega
    have hp1R : (p : ℝ) ≤ 1 := by exact_mod_cast hp1
    have hM3 : (M : ℝ) ≤ 3 := by
      have : M ≤ 3 := by omega
      exact_mod_cast this
    have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    rw [div_le_iff₀ hXpos, div_mul_eq_mul_div,
      le_div_iff₀ (by positivity : (0 : ℝ) < (M : ℝ) ^ 2)]
    nlinarith

/-- **The Lieb–Solovej deficit estimate** `γ_k ≤ 100 k²/(k²+M²)` for the triangle profile
of window length `M`. -/
theorem gamma_le_ratio (M p : ℕ) (hp : p = (M - 1) / 2) (hM : 1 ≤ M) (k : ℤ) :
    gamma p k ≤ 100 * (k : ℝ) ^ 2 / ((k : ℝ) ^ 2 + (M : ℝ) ^ 2) := by
  have hG : profG p ≤ 12 / (M : ℝ) ^ 2 := profG_le M p hp hM
  rcases eq_or_ne k 0 with hk | hk
  · subst hk
    have h : gamma p 0 = 0 := by
      unfold gamma
      simp
    rw [h]
    positivity
  · have hk2 : 0 < (k : ℝ) ^ 2 := by
      have : (k : ℝ) ≠ 0 := by exact_mod_cast hk
      positivity
    have h1 : gamma p k ≤ ((k : ℝ) ^ 2 / 2) * (12 / (M : ℝ) ^ 2) :=
      le_trans (gamma_le_shift p k) (mul_le_mul_of_nonneg_left hG (by positivity))
    have h2 : gamma p k ≤ 2 := gamma_le_two p k
    have h1' : gamma p k ≤ 6 * (k : ℝ) ^ 2 / (M : ℝ) ^ 2 := by
      have heq : ((k : ℝ) ^ 2 / 2) * (12 / (M : ℝ) ^ 2) = 6 * (k : ℝ) ^ 2 / (M : ℝ) ^ 2 := by
        field_simp
        ring_nf
      rw [← heq]
      exact h1
    rcases lt_or_ge (2 * (M : ℝ) ^ 2) (6 * (k : ℝ) ^ 2) with hcase | hcase
    · rw [le_div_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) ^ 2 + (M : ℝ) ^ 2)]
      have h3 : gamma p k * ((k : ℝ) ^ 2 + (M : ℝ) ^ 2) ≤ 2 * ((k : ℝ) ^ 2 + (M : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
      nlinarith [h3, hcase, sq_nonneg (k : ℝ)]
    · rw [le_div_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) ^ 2 + (M : ℝ) ^ 2)]
      have h3 : gamma p k * ((k : ℝ) ^ 2 + (M : ℝ) ^ 2)
          ≤ (6 * (k : ℝ) ^ 2 / (M : ℝ) ^ 2) * ((k : ℝ) ^ 2 + (M : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right h1' (by positivity)
      have h4 : (6 * (k : ℝ) ^ 2 / (M : ℝ) ^ 2) * ((k : ℝ) ^ 2 + (M : ℝ) ^ 2)
          ≤ 100 * (k : ℝ) ^ 2 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0 : ℝ) < (M : ℝ) ^ 2)]
        nlinarith [hcase, sq_nonneg (k : ℝ), sq_nonneg (M : ℝ)]
      linarith

/-- **The Lieb–Solovej matrix localisation theorem** (`thm:Localizing large matrices`,
Lieb–Solovej CMP 217 (2001); LSSY/Brietzke–Solovej).  `A` is a Hermitian matrix supported
on `iRange n × iRange n`, `ψ` a unit vector.  For every `1 ≤ M ≤ n` there is a unit vector
`φ` supported in a window of `M` consecutive indices, with

    ⟪φ, Aφ⟫ ≤ ⟪ψ, Aψ⟫ + (100/M²)Σ_{1≤k<M} k²|d_k| + 100 Σ_{M≤k} |d_k| .
-/
theorem ls_localisation (A : ℤ → ℤ → ℂ) (n M : ℕ) (ψ : ℤ → ℂ)
    (hM : 1 ≤ M) (hMn : M ≤ n)
    (hAsupp : ∀ i j, A i j ≠ 0 → i ∈ iRange n ∧ j ∈ iRange n)
    (hAherm : ∀ i j, A j i = star (A i j))
    (hψsupp : ∀ j, ψ j ≠ 0 → j ∈ iRange n)
    (hψnorm : normSq (iRange n) ψ = 1) :
    ∃ n₀ : ℤ, 0 ≤ n₀ ∧ n₀ + (M : ℤ) ≤ (n : ℤ) ∧
      ∃ φ : ℤ → ℂ, (∀ j, φ j ≠ 0 → n₀ ≤ j ∧ j < n₀ + (M : ℤ)) ∧
        normSq (iRange n) φ = 1 ∧
        qform A (iRange n) φ φ ≤ qform A (iRange n) ψ ψ
            + (100 / (M : ℝ) ^ 2) * ∑ k ∈ Finset.Icc 1 ((M : ℤ) - 1),
                (k : ℝ) ^ 2 * |dk A n ψ k|
            + 100 * ∑ k ∈ Finset.Icc (M : ℤ) ((n : ℤ) - 1), |dk A n ψ k| := by
  classical
  set p : ℕ := (M - 1) / 2 with hp
  set lam : ℝ := qform A (iRange n) ψ ψ with hlam
  set sg : ℝ := -∑ k ∈ Finset.Icc 1 ((n : ℤ) - 1), gamma p k * dk A n ψ k with hsg
  have hp2 : 2 * p + 1 ≤ M := by omega
  -- (1) the Lieb–Solovej sum identity : Σ_m K_m = 0
  have hsum : ∑ m ∈ mRange p n,
      (qform A (iRange n) (winVec p ψ m) (winVec p ψ m)
        - (lam + sg) * normSq (iRange n) (winVec p ψ m)) = 0 := by
    rw [Finset.sum_sub_distrib]
    rw [sum_winVec_qform A n p ψ hAsupp hAherm hψsupp]
    rw [← Finset.mul_sum, normSq_winVec_sum n p ψ hψsupp, hψnorm, mul_one]
    have h3 : ∀ k ∈ Finset.Icc (1 : ℤ) ((n : ℤ) - 1),
        Rcorr p k * dk A n ψ k = (1 - gamma p k) * dk A n ψ k := by
      intro k hk
      rw [Rcorr_eq_one_sub_gamma]
    rw [Finset.sum_congr rfl h3]
    have h4 : ∑ k ∈ Finset.Icc (1 : ℤ) ((n : ℤ) - 1), (1 - gamma p k) * dk A n ψ k
        = (∑ k ∈ Finset.Icc (1 : ℤ) ((n : ℤ) - 1), dk A n ψ k)
          - ∑ k ∈ Finset.Icc (1 : ℤ) ((n : ℤ) - 1), gamma p k * dk A n ψ k := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [h4]
    have e1 : dSup A n ψ 0 + ((∑ k ∈ Finset.Icc (1 : ℤ) ((n : ℤ) - 1), dk A n ψ k)
          - ∑ k ∈ Finset.Icc (1 : ℤ) ((n : ℤ) - 1), gamma p k * dk A n ψ k)
        = (dSup A n ψ 0 + ∑ k ∈ Finset.Icc (1 : ℤ) ((n : ℤ) - 1), dk A n ψ k)
          - ∑ k ∈ Finset.Icc (1 : ℤ) ((n : ℤ) - 1), gamma p k * dk A n ψ k := by ring_nf
    rw [e1, dSup_zero_add_dk_eq_qform A n ψ hAsupp hAherm hψsupp, hlam, hsg]
    ring
  -- (2) some window vector has `K_m ≤ 0`
  have hne : ∃ m ∈ mRange p n, winVec p ψ m ≠ 0 := by
    have hψex : ∃ j ∈ iRange n, ψ j ≠ 0 := by
      by_contra h
      have h0 : normSq (iRange n) ψ = 0 := by
        rw [normSq_eq_zero_iff]
        intro j hj
        by_contra hj0
        exact h ⟨j, hj, hj0⟩
      rw [hψnorm] at h0
      exact one_ne_zero h0
    obtain ⟨j, hj, hj0⟩ := hψex
    have hwj_pt : winVec p ψ j j ≠ 0 := by
      rw [winVec, sub_self]
      exact mul_ne_zero (by exact_mod_cast prof_zero_ne_zero p) hj0
    have hwj : winVec p ψ j ≠ 0 := fun h => hwj_pt (by simpa using congrFun h j)
    refine ⟨j, ?_, hwj⟩
    rw [mRange, Finset.mem_Icc]
    obtain ⟨hj0, hj1⟩ : (0 : ℤ) ≤ j ∧ j ≤ (n : ℤ) - 1 := by
      simpa [iRange, Finset.mem_Icc] using hj
    constructor <;> omega
  have hex : ∃ m ∈ mRange p n, winVec p ψ m ≠ 0 ∧
      qform A (iRange n) (winVec p ψ m) (winVec p ψ m)
        ≤ (lam + sg) * normSq (iRange n) (winVec p ψ m) := by
    by_contra hcon
    have hc : ∀ m, m ∈ mRange p n → winVec p ψ m ≠ 0 →
        (lam + sg) * normSq (iRange n) (winVec p ψ m)
          < qform A (iRange n) (winVec p ψ m) (winVec p ψ m) := by
      intro m hm hw
      by_contra hle
      exact hcon ⟨m, hm, hw, not_lt.mp hle⟩
    set Sf : Finset ℤ := (mRange p n).filter (fun m => winVec p ψ m ≠ 0) with hSf
    have hSf_ne : Sf.Nonempty := by
      obtain ⟨m, hm, hw⟩ := hne
      exact ⟨m, by simp [hSf, hm, hw]⟩
    have hzero : ∀ m ∈ mRange p n, m ∉ Sf →
        (qform A (iRange n) (winVec p ψ m) (winVec p ψ m)
          - (lam + sg) * normSq (iRange n) (winVec p ψ m)) = 0 := by
      intro m hm hms
      have hw : winVec p ψ m = 0 := by
        by_contra hw
        exact hms (by simp [hSf, hm, hw])
      rw [hw]
      simp [qform, normSq]
    have hsumS : ∑ m ∈ mRange p n,
        (qform A (iRange n) (winVec p ψ m) (winVec p ψ m)
          - (lam + sg) * normSq (iRange n) (winVec p ψ m))
        = ∑ m ∈ Sf, (qform A (iRange n) (winVec p ψ m) (winVec p ψ m)
          - (lam + sg) * normSq (iRange n) (winVec p ψ m)) :=
      (Finset.sum_subset (Finset.filter_subset (fun m => winVec p ψ m ≠ 0) (mRange p n))
        hzero).symm
    have hposS : 0 < ∑ m ∈ Sf, (qform A (iRange n) (winVec p ψ m) (winVec p ψ m)
          - (lam + sg) * normSq (iRange n) (winVec p ψ m)) := by
      apply Finset.sum_pos'
      · intro m hm
        have hm' : m ∈ mRange p n ∧ winVec p ψ m ≠ 0 := by
          simpa [hSf, Finset.mem_filter] using hm
        have := hc m hm'.1 hm'.2
        linarith
      · obtain ⟨m, hm⟩ := hSf_ne
        have hm' : m ∈ mRange p n ∧ winVec p ψ m ≠ 0 := by
          simpa [hSf, Finset.mem_filter] using hm
        have := hc m hm'.1 hm'.2
        exact ⟨m, hm, by linarith⟩
    rw [hsumS] at hsum
    rw [hsum] at hposS
    exact lt_irrefl 0 hposS
  -- (3) σ is bounded by the profile estimates
  have hsigle : sg ≤ (100 / (M : ℝ) ^ 2) * ∑ k ∈ Finset.Icc (1 : ℤ) ((M : ℤ) - 1),
        (k : ℝ) ^ 2 * |dk A n ψ k|
      + 100 * ∑ k ∈ Finset.Icc (M : ℤ) ((n : ℤ) - 1), |dk A n ψ k| := by
    rw [hsg]
    have h1 : -(∑ k ∈ Finset.Icc (1 : ℤ) ((n : ℤ) - 1), gamma p k * dk A n ψ k)
        ≤ ∑ k ∈ Finset.Icc (1 : ℤ) ((n : ℤ) - 1), gamma p k * |dk A n ψ k| := by
      rw [neg_le_iff_add_nonneg, ← Finset.sum_add_distrib]
      apply Finset.sum_nonneg
      intro k hk
      have h2 := neg_abs_le (dk A n ψ k)
      have h3 : 0 ≤ gamma p k * (dk A n ψ k + |dk A n ψ k|) :=
        mul_nonneg (gamma_nonneg p k) (by linarith)
      linarith
    refine le_trans h1 ?_
    have hsplit : ∑ k ∈ Finset.Icc (1 : ℤ) ((n : ℤ) - 1), gamma p k * |dk A n ψ k|
        = (∑ k ∈ Finset.Icc (1 : ℤ) ((M : ℤ) - 1), gamma p k * |dk A n ψ k|)
          + ∑ k ∈ Finset.Icc (M : ℤ) ((n : ℤ) - 1), gamma p k * |dk A n ψ k| := by
      rw [← Finset.sum_union (s₁ := Finset.Icc (1 : ℤ) ((M : ℤ) - 1))
        (s₂ := Finset.Icc (M : ℤ) ((n : ℤ) - 1))
        (Finset.disjoint_left.mpr (fun k h1 h2 => by
          simp only [Finset.mem_Icc] at h1 h2
          omega))]
      congr 1
      ext k
      simp only [Finset.mem_union, Finset.mem_Icc]
      omega
    rw [hsplit]
    refine add_le_add ?_ ?_
    · have hpw : ∀ k ∈ Finset.Icc (1 : ℤ) ((M : ℤ) - 1),
          gamma p k * |dk A n ψ k| ≤ ((100 / (M : ℝ) ^ 2) * (k : ℝ) ^ 2) * |dk A n ψ k| := by
        intro k hk
        have hkM : (k : ℝ) ^ 2 + (M : ℝ) ^ 2 ≥ (M : ℝ) ^ 2 := by
          have : (0 : ℝ) ≤ (k : ℝ) ^ 2 := sq_nonneg _
          linarith
        have hgr : gamma p k ≤ 100 * (k : ℝ) ^ 2 / ((k : ℝ) ^ 2 + (M : ℝ) ^ 2) :=
          gamma_le_ratio M p hp hM k
        have h2 : 100 * (k : ℝ) ^ 2 / ((k : ℝ) ^ 2 + (M : ℝ) ^ 2)
            ≤ 100 * (k : ℝ) ^ 2 / (M : ℝ) ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hkM
        have h3 : gamma p k ≤ (100 / (M : ℝ) ^ 2) * (k : ℝ) ^ 2 := by
          refine le_trans hgr (le_trans h2 ?_)
          rw [div_mul_eq_mul_div]
        exact mul_le_mul_of_nonneg_right h3 (abs_nonneg _)
      calc ∑ k ∈ Finset.Icc (1 : ℤ) ((M : ℤ) - 1), gamma p k * |dk A n ψ k|
          ≤ ∑ k ∈ Finset.Icc (1 : ℤ) ((M : ℤ) - 1),
              ((100 / (M : ℝ) ^ 2) * (k : ℝ) ^ 2) * |dk A n ψ k| := Finset.sum_le_sum hpw
        _ = (100 / (M : ℝ) ^ 2) * ∑ k ∈ Finset.Icc (1 : ℤ) ((M : ℤ) - 1),
              (k : ℝ) ^ 2 * |dk A n ψ k| := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k hk
            ring
    · have hpw : ∀ k ∈ Finset.Icc (M : ℤ) ((n : ℤ) - 1),
          gamma p k * |dk A n ψ k| ≤ 100 * |dk A n ψ k| := by
        intro k hk
        have hgr : gamma p k ≤ 100 * (k : ℝ) ^ 2 / ((k : ℝ) ^ 2 + (M : ℝ) ^ 2) :=
          gamma_le_ratio M p hp hM k
        have h3 : gamma p k ≤ 100 := by
          refine le_trans hgr ?_
          rw [div_le_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) ^ 2 + (M : ℝ) ^ 2)]
          nlinarith [sq_nonneg (k : ℝ), sq_nonneg (M : ℝ)]
        exact mul_le_mul_of_nonneg_right h3 (abs_nonneg _)
      calc ∑ k ∈ Finset.Icc (M : ℤ) ((n : ℤ) - 1), gamma p k * |dk A n ψ k|
          ≤ ∑ k ∈ Finset.Icc (M : ℤ) ((n : ℤ) - 1), 100 * |dk A n ψ k| := Finset.sum_le_sum hpw
        _ = 100 * ∑ k ∈ Finset.Icc (M : ℤ) ((n : ℤ) - 1), |dk A n ψ k| := by
            rw [Finset.mul_sum]
  -- (4) normalise
  obtain ⟨m, hm, hw, hQ⟩ := hex
  have hc₀ : 0 < normSq (iRange n) (winVec p ψ m) := by
    obtain ⟨j, hj⟩ : ∃ j, winVec p ψ m j ≠ 0 := by
      by_contra h
      push_neg at h
      exact hw (funext h)
    have hψj : ψ j ≠ 0 := by
      intro h
      exact hj (by simp [winVec, h])
    exact normSq_pos_of_ne_zero ⟨j, hψsupp j hψj, hj⟩
  set c : ℝ := (Real.sqrt (normSq (iRange n) (winVec p ψ m)))⁻¹ with hcdef
  have hcsq : c ^ 2 * normSq (iRange n) (winVec p ψ m) = 1 := by
    rw [hcdef, inv_pow, Real.sq_sqrt (le_of_lt hc₀)]
    exact inv_mul_cancel₀ (ne_of_gt hc₀)
  have hwinsupp : ∀ j, winVec p ψ m j ≠ 0 → j ∈ iRange n := by
    intro j hj
    have hψj : ψ j ≠ 0 := by
      intro h
      exact hj (by simp [winVec, h])
    exact hψsupp j hψj
  have hwinwin : ∀ j, winVec p ψ m j ≠ 0 → m - (p : ℤ) ≤ j ∧ j ≤ m + (p : ℤ) := by
    intro j hj
    have h1 : prof p (j - m) ≠ 0 := by
      intro h
      exact hj (by simp [winVec, h])
    have h2 : |j - m| ≤ (p : ℤ) := abs_le_of_prof_ne_zero h1
    rw [abs_le] at h2
    exact ⟨by linarith [h2.1], by linarith [h2.2]⟩
  obtain ⟨n₀, hn₀0, hn₀M, hn₀w⟩ :=
    window_clamp n M hM hMn (winVec p ψ m) m p hp2 hwinsupp hwinwin
  refine ⟨n₀, hn₀0, hn₀M, (fun j => (c : ℂ) * winVec p ψ m j), ?_, ?_, ?_⟩
  · intro j hj
    exact hn₀w j (fun h => hj (by simp [h]))
  · rw [normSq_smul, hcsq]
  · rw [qform_smul]
    calc c ^ 2 * qform A (iRange n) (winVec p ψ m) (winVec p ψ m)
        ≤ c ^ 2 * ((lam + sg) * normSq (iRange n) (winVec p ψ m)) :=
          mul_le_mul_of_nonneg_left hQ (sq_nonneg c)
      _ = (lam + sg) * (c ^ 2 * normSq (iRange n) (winVec p ψ m)) := by ring_nf
      _ = lam + sg := by rw [hcsq]; ring_nf
      _ ≤ qform A (iRange n) ψ ψ
            + (100 / (M : ℝ) ^ 2) * ∑ k ∈ Finset.Icc 1 ((M : ℤ) - 1),
                (k : ℝ) ^ 2 * |dk A n ψ k|
            + 100 * ∑ k ∈ Finset.Icc (M : ℤ) ((n : ℤ) - 1), |dk A n ψ k| := by
          rw [hlam]
          linarith [hsigle]

/-- **The band ≤ 2 corollary** — the form FS §7 and Brietzke–Solovej apply: for
`d_k = 0` (`k ≥ 3`) and `M ≥ 3` the error term collapses to `100 M⁻²(|d₁| + 4|d₂|)`. -/
theorem ls_localisation_band2 (A : ℤ → ℤ → ℂ) (n M : ℕ) (ψ : ℤ → ℂ)
    (hM : 3 ≤ M) (hMn : M ≤ n)
    (hAsupp : ∀ i j, A i j ≠ 0 → i ∈ iRange n ∧ j ∈ iRange n)
    (hAherm : ∀ i j, A j i = star (A i j))
    (hψsupp : ∀ j, ψ j ≠ 0 → j ∈ iRange n)
    (hψnorm : normSq (iRange n) ψ = 1)
    (hband : ∀ k : ℤ, 3 ≤ k → dk A n ψ k = 0) :
    ∃ n₀ : ℤ, 0 ≤ n₀ ∧ n₀ + (M : ℤ) ≤ (n : ℤ) ∧
      ∃ φ : ℤ → ℂ, (∀ j, φ j ≠ 0 → n₀ ≤ j ∧ j < n₀ + (M : ℤ)) ∧
        normSq (iRange n) φ = 1 ∧
        qform A (iRange n) φ φ ≤ qform A (iRange n) ψ ψ
          + (100 / (M : ℝ) ^ 2) * (|dk A n ψ 1| + 4 * |dk A n ψ 2|) := by
  obtain ⟨n₀, h0, h1, φ, hsupp, hnorm, hineq⟩ :=
    ls_localisation A n M ψ (by omega) hMn hAsupp hAherm hψsupp hψnorm
  refine ⟨n₀, h0, h1, φ, hsupp, hnorm, ?_⟩
  have hsum1 : ∑ k ∈ Finset.Icc (1 : ℤ) ((M : ℤ) - 1), (k : ℝ) ^ 2 * |dk A n ψ k|
      = |dk A n ψ 1| + 4 * |dk A n ψ 2| := by
    have hsub : ({1, 2} : Finset ℤ) ⊆ Finset.Icc (1 : ℤ) ((M : ℤ) - 1) := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      simp only [Finset.mem_Icc]
      rcases hk with rfl | rfl <;> (constructor <;> omega)
    have hzero : ∀ k ∈ Finset.Icc (1 : ℤ) ((M : ℤ) - 1), k ∉ ({1, 2} : Finset ℤ) →
        (k : ℝ) ^ 2 * |dk A n ψ k| = 0 := by
      intro k hk hk'
      have hk3 : (3 : ℤ) ≤ k := by
        have hk1 : (1 : ℤ) ≤ k := by
          have := hk
          simp only [Finset.mem_Icc] at this
          exact this.1
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk'
        omega
      rw [hband k hk3, abs_zero, mul_zero]
    rw [← Finset.sum_subset hsub hzero]
    rw [Finset.sum_insert (by decide), Finset.sum_singleton]
    norm_num
  have hsum2 : ∑ k ∈ Finset.Icc (M : ℤ) ((n : ℤ) - 1), |dk A n ψ k| = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hk3 : (3 : ℤ) ≤ k := by
      simp only [Finset.mem_Icc] at hk
      omega
    rw [hband k hk3, abs_zero]
  rw [hsum1, hsum2, mul_zero, add_zero] at hineq
  exact hineq

end Work.UBBInputs3
