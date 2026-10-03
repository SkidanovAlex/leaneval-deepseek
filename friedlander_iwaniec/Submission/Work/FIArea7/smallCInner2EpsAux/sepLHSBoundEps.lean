import Mathlib
import Submission.Work.FIArea7.smallCInner2EpsAux.sepLHSDefs
import Submission.Work.FIArea7.smallCInner2EpsAux.smoothBilinEps
import Submission.Work.FIArea7.smallCInner2EpsAux.hyperbolaBilinEps
import Submission.Work.FIArea7.smallCInner2EpsAux.cTermFactor
import Submission.Work.FIArea7.smallCInner2EpsAux.sumTauMulDivRpowLe
import Submission.Work.FIArea7.smallCInner2EpsAux.cardDivisorsMulLe
import Submission.Work.FIArea7.smallCInner2EpsAux.isSepPairKTwoPowLe
import Submission.Work.FIArea7.smallCInner2EpsAux.isSepPairKKUnique
import Submission.Work.FIArea7.sum_eq_sepPairSum
import Submission.Work.FIArea7.sqfreeSum_eq_sepPair_add_peel
import Submission.Work.FIArea7.sepPair_bounds
import Submission.Work.FIArea7.isSepPairK_product
import Submission.Work.FIArea7.sepPair_eq_of_prod_eq
import Submission.Work.FIArea7.smallCInnerAux.sumTauRpow

set_option autoImplicit false

namespace Work.FIArea7.smallCInner2EpsAux

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section






theorem natLogTwoLe (u : ℕ) (hu : 1 ≤ u) :
    ((Nat.log 2 u : ℕ) : ℝ) + 1 ≤ 4 * Real.log ((u : ℝ) + 2) := by
  have hu0 : u ≠ 0 := by omega
  have hlog3 : (1 : ℝ) ≤ Real.log ((u : ℝ) + 2) := by
    have h3 : (3 : ℝ) ≤ (u : ℝ) + 2 := by
      have h1 : (1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu
      linarith
    have hexp : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
    have h13 : (1 : ℝ) ≤ Real.log 3 :=
      (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 3)).mpr (le_of_lt hexp)
    exact le_trans h13 (Real.log_le_log (by norm_num) h3)
  have hk : ((Nat.log 2 u : ℕ) : ℝ) * Real.log 2 ≤ Real.log ((u : ℝ) + 2) := by
    have hpow : 2 ^ Nat.log 2 u ≤ u := Nat.pow_log_le_self 2 hu0
    have hpowR : ((2 : ℝ)) ^ (Nat.log 2 u) ≤ (u : ℝ) := by exact_mod_cast hpow
    have h1 : Real.log (((2:ℝ)) ^ (Nat.log 2 u)) ≤ Real.log ((u : ℝ) + 2) :=
      Real.log_le_log (by positivity) (by linarith)
    rwa [Real.log_pow] at h1
  have hlog2pos : (1/2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hk2 : ((Nat.log 2 u : ℕ) : ℝ) ≤ 2 * Real.log ((u : ℝ) + 2) := by
    have hkn : (0:ℝ) ≤ ((Nat.log 2 u : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith [hk, hlog2pos, hlog3]
  linarith

theorem sqrtTwoRpow12Le (u : ℕ) (hu : 1 ≤ u) :
    (((Nat.sqrt u : ℕ) : ℝ) + ((Nat.sqrt u : ℕ) : ℝ)) ^ ((1 : ℝ) / 12)
      ≤ (2 : ℝ) ^ ((1 : ℝ) / 12) * (u : ℝ) ^ ((1 : ℝ) / 24) := by
  set s : ℝ := ((Nat.sqrt u : ℕ) : ℝ) with hs
  have hsnn : 0 ≤ s := by rw [hs]; positivity
  have hss : s * s ≤ (u : ℝ) := by
    rw [hs]
    have h := Nat.sqrt_le u
    have h' : (((Nat.sqrt u * Nat.sqrt u : ℕ)) : ℝ) ≤ (u : ℝ) := by exact_mod_cast h
    rwa [Nat.cast_mul] at h'
  have hsu : s ≤ (u : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow]
    rw [Real.le_sqrt' (by rw [hs]; positivity)]
    rw [pow_two]
    exact hss
  have h2 : s + s ≤ 2 * ((u : ℝ) ^ ((1 : ℝ) / 2)) := by linarith
  calc (s + s) ^ ((1 : ℝ) / 12) ≤ (2 * ((u : ℝ) ^ ((1 : ℝ) / 2))) ^ ((1 : ℝ) / 12) :=
        Real.rpow_le_rpow (by linarith) h2 (by norm_num)
    _ = (2 : ℝ) ^ ((1 : ℝ) / 12) * (((u : ℝ) ^ ((1 : ℝ) / 2)) ^ ((1 : ℝ) / 12)) :=
        Real.mul_rpow (by norm_num) (Real.rpow_nonneg (by positivity) _)
    _ = (2 : ℝ) ^ ((1 : ℝ) / 12) * (u : ℝ) ^ ((1 : ℝ) / 24) := by
        rw [← Real.rpow_mul (x := (u : ℝ)) (by positivity),
          show (1 : ℝ)/2 * ((1 : ℝ)/12) = (1 : ℝ)/24 by norm_num]

theorem rpowLogMono (c D u d : ℕ) (ε As : ℝ) (hε : 0 < ε) (hAs : 0 < As) (hd : 1 ≤ d)
    (hdD : d ≤ D) :
    (Real.log (((u / d : ℕ) : ℝ) + 2)) ^ As * ((((u / d : ℕ) : ℝ) + ((c * d : ℕ) : ℝ) + 2) ^ ε)
      ≤ (Real.log ((u : ℝ) + 2)) ^ As * (((u : ℝ) + (c : ℝ) * (D : ℝ) + 2) ^ ε) := by
  have h1 : ((u / d : ℕ) : ℝ) ≤ (u : ℝ) := by
    have h := Nat.cast_div_le (α := ℝ) (m := u) (n := d)
    have h2 : (u : ℝ) / (d : ℝ) ≤ (u : ℝ) :=
      div_le_self (Nat.cast_nonneg u) (by exact_mod_cast hd)
    linarith [h, h2]
  have h2 : ((c * d : ℕ) : ℝ) ≤ (c : ℝ) * (D : ℝ) := by
    rw [Nat.cast_mul]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hdD) (by positivity)
  refine mul_le_mul ?_ ?_ ?_ ?_
  · exact Real.rpow_le_rpow (Real.log_nonneg (by linarith))
      (Real.log_le_log (by linarith) (by linarith)) (le_of_lt hAs)
  · exact Real.rpow_le_rpow (by positivity) (by linarith) (le_of_lt hε)
  · exact Real.rpow_nonneg (by positivity) ε
  · exact Real.rpow_nonneg (Real.log_nonneg (by linarith)) As

theorem sepSumLHS_eq_tripleSum {r u z D : ℕ} (hr : 2 ≤ r)
    (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (k : ℤ) (c : ℕ) (P : ℝ → ℝ)
    (hD : ∀ l d m n, Squarefree l → l ≤ u → (∀ p : ℕ, p.Prime → p ∣ l → p ≤ z) →
            Work.FIArea7.IsSepPair r d m n → d * m * n = l → d ≤ D) :
    Work.FIArea7.sepSumLHS u z (Work.FIArea7.smallCInner2EpsAux.cTerm Pa chi k c P)
      = Finset.sum (Finset.Icc 1 D) (fun d => Finset.sum (Finset.Icc 1 u) (fun m =>
          Finset.sum (Finset.Icc 1 u) (fun n =>
          Work.FIArea7.smallCInner2EpsAux.ind (Work.FIArea7.IsSepPair r d m n
              ∧ (∀ p : ℕ, p.Prime → p ∣ d * m * n → p ≤ z) ∧ d * m * n ≤ u)
            * Work.FIArea7.smallCInner2EpsAux.cTerm Pa chi k c P (d * m * n)))) := by
  rw [← sepSumLHS_sqfreeTrunc u z (cTerm Pa chi k c P),
    sum_eq_sepPairSum r u z D hr (sqfreeTrunc u z (cTerm Pa chi k c P))
      (fun l hl => sqfreeTrunc_ne_zero hl) hD, sepPairSum]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro n _
  by_cases hI : Work.FIArea7.IsSepPair r d m n
  · by_cases hq : (∀ p : ℕ, p.Prime → p ∣ d * m * n → p ≤ z)
    · have hsf : Squarefree (d * m * n) := sepPair_squarefree hI
      by_cases hle : d * m * n ≤ u
      · rw [if_pos ⟨hI, hq⟩, ind_pos ⟨hI, hq, hle⟩, one_mul]
        unfold sqfreeTrunc
        rw [if_pos ⟨hsf, hle, hq⟩]
      · rw [if_pos ⟨hI, hq⟩, ind_neg (fun h => hle h.2.2), zero_mul]
        unfold sqfreeTrunc
        rw [if_neg (fun h => hle h.2.1)]
    · rw [if_neg (fun h => hq h.2), ind_neg (fun h => hq h.2.1), zero_mul]
  · rw [if_neg (fun h => hI h.1), ind_neg (fun h => hI h.1), zero_mul]

theorem bilinReduction {r k d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (A B : ℕ → Prop)
    (hAB : ∀ m n : ℕ, Work.FIArea7.IsSepPairK r k d m n ↔ A m ∧ B n)
    (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (k0 : ℤ) (c z u : ℕ) (P : ℝ → ℝ) :
    Finset.sum (Finset.Icc 1 u) (fun m => Finset.sum (Finset.Icc 1 u) (fun n =>
        Work.FIArea7.smallCInner2EpsAux.ind (Work.FIArea7.IsSepPairK r k d m n
            ∧ (∀ p : ℕ, p.Prime → p ∣ d * m * n → p ≤ z) ∧ d * m * n ≤ u)
          * Work.FIArea7.smallCInner2EpsAux.cTerm Pa chi k0 c P (d * m * n)))
      = Finset.sum (Finset.Icc 1 (Nat.sqrt u)) (fun m => Finset.sum (Finset.Icc 1 (Nat.sqrt u)) (fun n =>
          Work.FIArea7.smallCInner2EpsAux.ind (m * n ≤ u / d)
            * ((Work.FIArea7.smallCInner2EpsAux.cCoeff Pa c z d
                  * Work.FIArea7.smallCInner2EpsAux.ind (A m)
                  * Work.FIArea7.smallCInner2EpsAux.cCoeff Pa c z m)
                * (Work.FIArea7.smallCInner2EpsAux.ind (B n)
                  * Work.FIArea7.smallCInner2EpsAux.cCoeff Pa c z n)
                * ((P (((c * d : ℕ) : ℝ) * ((m * n : ℕ) : ℝ)) : ℝ) : ℂ)
                * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k0) ((c * d) * (m * n))))) := by
  have hdpos : 0 < d := by omega
  have hR : ∀ m n : ℕ, (d * m * n ≤ u) = (m * n ≤ u / d) := by
    intro m n
    have h1 : (d * m * n) = (m * n) * d := by ring
    rw [h1]
    exact propext (Nat.le_div_iff_mul_le hdpos).symm
  have hParg : ∀ m n : ℕ,
      (c : ℝ) * ((d * m * n : ℕ) : ℝ) = ((c * d : ℕ) : ℝ) * ((m * n : ℕ) : ℝ) := by
    intro m n
    push_cast
    ring
  have hQarg : ∀ m n : ℕ, c * (d * m * n) = (c * d) * (m * n) := by
    intro m n; ring
  have hpt : ∀ m n : ℕ,
      Work.FIArea7.smallCInner2EpsAux.ind (Work.FIArea7.IsSepPairK r k d m n
            ∧ (∀ p : ℕ, p.Prime → p ∣ d * m * n → p ≤ z) ∧ d * m * n ≤ u)
          * Work.FIArea7.smallCInner2EpsAux.cTerm Pa chi k0 c P (d * m * n)
        = Work.FIArea7.smallCInner2EpsAux.ind (m * n ≤ u / d)
          * ((Work.FIArea7.smallCInner2EpsAux.cCoeff Pa c z d
                * Work.FIArea7.smallCInner2EpsAux.ind (A m)
                * Work.FIArea7.smallCInner2EpsAux.cCoeff Pa c z m)
              * (Work.FIArea7.smallCInner2EpsAux.ind (B n)
                * Work.FIArea7.smallCInner2EpsAux.cCoeff Pa c z n)
              * ((P (((c * d : ℕ) : ℝ) * ((m * n : ℕ) : ℝ)) : ℝ) : ℂ)
              * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k0) ((c * d) * (m * n))) := by
    intro m n
    by_cases hK : Work.FIArea7.IsSepPairK r k d m n
    · have hI : Work.FIArea7.IsSepPair r d m n :=
        (Work.FIArea7.isSepPair_iff_exists_isSepPairK r d m n).mpr ⟨k, hK⟩
      have hfac := cTermFactor hr hI Pa chi k0 c z P
      have hAB1 : Work.FIArea7.smallCInner2EpsAux.ind (A m)
            * Work.FIArea7.smallCInner2EpsAux.ind (B n) = 1 := by
        rw [← ind_and, ← hAB m n]
        exact ind_pos hK
      have hcoef : (Work.FIArea7.smallCInner2EpsAux.cCoeff Pa c z d
                * Work.FIArea7.smallCInner2EpsAux.ind (A m)
                * Work.FIArea7.smallCInner2EpsAux.cCoeff Pa c z m)
              * (Work.FIArea7.smallCInner2EpsAux.ind (B n)
                * Work.FIArea7.smallCInner2EpsAux.cCoeff Pa c z n)
            = Work.FIArea7.smallCInner2EpsAux.cCoeff Pa c z d
              * Work.FIArea7.smallCInner2EpsAux.cCoeff Pa c z m
              * Work.FIArea7.smallCInner2EpsAux.cCoeff Pa c z n := by
        have h1 : (Work.FIArea7.smallCInner2EpsAux.cCoeff Pa c z d
                * Work.FIArea7.smallCInner2EpsAux.ind (A m)
                * Work.FIArea7.smallCInner2EpsAux.cCoeff Pa c z m)
              * (Work.FIArea7.smallCInner2EpsAux.ind (B n)
                * Work.FIArea7.smallCInner2EpsAux.cCoeff Pa c z n)
            = Work.FIArea7.smallCInner2EpsAux.cCoeff Pa c z d
              * Work.FIArea7.smallCInner2EpsAux.cCoeff Pa c z m
              * Work.FIArea7.smallCInner2EpsAux.cCoeff Pa c z n
              * (Work.FIArea7.smallCInner2EpsAux.ind (A m)
                * Work.FIArea7.smallCInner2EpsAux.ind (B n)) := by ring
        rw [h1, hAB1, mul_one]
      rw [ind_and_and, ind_pos hK, one_mul, hR m n]
      rw [show Work.FIArea7.smallCInner2EpsAux.ind
              (∀ p : ℕ, p.Prime → p ∣ d * m * n → p ≤ z)
            * Work.FIArea7.smallCInner2EpsAux.ind (m * n ≤ u / d)
            * Work.FIArea7.smallCInner2EpsAux.cTerm Pa chi k0 c P (d * m * n)
          = Work.FIArea7.smallCInner2EpsAux.ind (m * n ≤ u / d)
            * (Work.FIArea7.smallCInner2EpsAux.ind
                (∀ p : ℕ, p.Prime → p ∣ d * m * n → p ≤ z)
              * Work.FIArea7.smallCInner2EpsAux.cTerm Pa chi k0 c P (d * m * n)) by ring]
      rw [hfac, hParg m n, hQarg m n, hcoef]
    · have h0 : Work.FIArea7.smallCInner2EpsAux.ind (Work.FIArea7.IsSepPairK r k d m n
            ∧ (∀ p : ℕ, p.Prime → p ∣ d * m * n → p ≤ z) ∧ d * m * n ≤ u) = 0 := by
        rw [ind_neg]; intro h; exact hK h.1
      rw [h0, zero_mul]
      by_cases hA : A m
      · rw [ind_pos hA]
        have hBn : ¬ B n := fun hb => hK ((hAB m n).mpr ⟨hA, hb⟩)
        rw [ind_neg hBn]
        ring
      · rw [ind_neg hA]
        ring
  have hGzero : ∀ m n : ℕ, Nat.sqrt u < m ∨ Nat.sqrt u < n →
      Work.FIArea7.smallCInner2EpsAux.ind (m * n ≤ u / d)
        * ((Work.FIArea7.smallCInner2EpsAux.cCoeff Pa c z d
              * Work.FIArea7.smallCInner2EpsAux.ind (A m)
              * Work.FIArea7.smallCInner2EpsAux.cCoeff Pa c z m)
            * (Work.FIArea7.smallCInner2EpsAux.ind (B n)
              * Work.FIArea7.smallCInner2EpsAux.cCoeff Pa c z n)
            * ((P (((c * d : ℕ) : ℝ) * ((m * n : ℕ) : ℝ)) : ℝ) : ℂ)
            * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k0) ((c * d) * (m * n))) = 0 := by
    intro m n hlt
    by_cases hmn : m * n ≤ u / d
    · rw [ind_pos hmn]
      by_cases hA : A m
      · rw [ind_pos hA]
        by_cases hB : B n
        · rw [ind_pos hB]
          have hK : Work.FIArea7.IsSepPairK r k d m n := (hAB m n).mpr ⟨hA, hB⟩
          have hI : Work.FIArea7.IsSepPair r d m n :=
            (Work.FIArea7.isSepPair_iff_exists_isSepPairK r d m n).mpr ⟨k, hK⟩
          obtain ⟨-, hmn2, hmm, hnn⟩ := sepPair_bounds hr hI
          have hdmnu : d * (m * n) ≤ u := by
            have h1 : (m * n) * d ≤ u := (Nat.le_div_iff_mul_le hdpos).mp hmn
            rwa [Nat.mul_comm (m * n) d] at h1
          have h1 : m * m ≤ d * (m * n) := by rw [← Nat.mul_assoc]; exact hmm
          have h2 : n * n ≤ d * (m * n) := by rw [← Nat.mul_assoc]; exact hnn
          rcases hlt with hlt | hlt
          · exact absurd (Nat.le_sqrt.mpr (le_trans h1 hdmnu)) (not_le.mpr hlt)
          · exact absurd (Nat.le_sqrt.mpr (le_trans h2 hdmnu)) (not_le.mpr hlt)
        · rw [ind_neg hB]; ring
      · rw [ind_neg hA]; ring
    · rw [ind_neg hmn]; ring
  have hsub : Finset.Icc 1 (Nat.sqrt u) ⊆ Finset.Icc 1 u :=
    Finset.Icc_subset_Icc_right (Nat.sqrt_le_self u)
  have hpt_sum : Finset.sum (Finset.Icc 1 u) (fun m => Finset.sum (Finset.Icc 1 u) (fun n =>
        Work.FIArea7.smallCInner2EpsAux.ind (Work.FIArea7.IsSepPairK r k d m n
            ∧ (∀ p : ℕ, p.Prime → p ∣ d * m * n → p ≤ z) ∧ d * m * n ≤ u)
          * Work.FIArea7.smallCInner2EpsAux.cTerm Pa chi k0 c P (d * m * n)))
      = Finset.sum (Finset.Icc 1 u) (fun m => Finset.sum (Finset.Icc 1 u) (fun n =>
        Work.FIArea7.smallCInner2EpsAux.ind (m * n ≤ u / d)
          * ((Work.FIArea7.smallCInner2EpsAux.cCoeff Pa c z d
                * Work.FIArea7.smallCInner2EpsAux.ind (A m)
                * Work.FIArea7.smallCInner2EpsAux.cCoeff Pa c z m)
              * (Work.FIArea7.smallCInner2EpsAux.ind (B n)
                * Work.FIArea7.smallCInner2EpsAux.cCoeff Pa c z n)
              * ((P (((c * d : ℕ) : ℝ) * ((m * n : ℕ) : ℝ)) : ℝ) : ℂ)
              * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k0) ((c * d) * (m * n))))) := by
    apply Finset.sum_congr rfl
    intro m _
    apply Finset.sum_congr rfl
    intro n _
    exact hpt m n
  have h1 : Finset.sum (Finset.Icc 1 u) (fun m => Finset.sum (Finset.Icc 1 u) (fun n =>
        Work.FIArea7.smallCInner2EpsAux.ind (m * n ≤ u / d)
          * ((Work.FIArea7.smallCInner2EpsAux.cCoeff Pa c z d
                * Work.FIArea7.smallCInner2EpsAux.ind (A m)
                * Work.FIArea7.smallCInner2EpsAux.cCoeff Pa c z m)
              * (Work.FIArea7.smallCInner2EpsAux.ind (B n)
                * Work.FIArea7.smallCInner2EpsAux.cCoeff Pa c z n)
              * ((P (((c * d : ℕ) : ℝ) * ((m * n : ℕ) : ℝ)) : ℝ) : ℂ)
              * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k0) ((c * d) * (m * n)))))
      = Finset.sum (Finset.Icc 1 (Nat.sqrt u)) (fun m => Finset.sum (Finset.Icc 1 (Nat.sqrt u)) (fun n =>
        Work.FIArea7.smallCInner2EpsAux.ind (m * n ≤ u / d)
          * ((Work.FIArea7.smallCInner2EpsAux.cCoeff Pa c z d
                * Work.FIArea7.smallCInner2EpsAux.ind (A m)
                * Work.FIArea7.smallCInner2EpsAux.cCoeff Pa c z m)
              * (Work.FIArea7.smallCInner2EpsAux.ind (B n)
                * Work.FIArea7.smallCInner2EpsAux.cCoeff Pa c z n)
              * ((P (((c * d : ℕ) : ℝ) * ((m * n : ℕ) : ℝ)) : ℝ) : ℂ)
              * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k0) ((c * d) * (m * n))))) := by
    rw [← Finset.sum_subset hsub (fun m hm hmn => by
      refine Finset.sum_eq_zero (fun n _ => ?_)
      exact hGzero m n (Or.inl (by
        simp only [Finset.mem_Icc] at hm hmn
        omega)))]
    apply Finset.sum_congr rfl
    intro m hm
    refine (Finset.sum_subset hsub ?_).symm
    intro n hn hns
    exact hGzero m n (Or.inr (by
      simp only [Finset.mem_Icc] at hn hns
      omega))
  rw [hpt_sum, h1]

theorem isSepPair_indicator_decomp {r d m n u : ℕ}
    (h : d * m * n ≤ u) :
    Work.FIArea7.smallCInner2EpsAux.ind (Work.FIArea7.IsSepPair r d m n)
      = Finset.sum (Finset.range (Nat.log 2 u + 1))
          (fun k => Work.FIArea7.smallCInner2EpsAux.ind (Work.FIArea7.IsSepPairK r k d m n)) := by
  rw [Work.FIArea7.isSepPair_iff_exists_isSepPairK r d m n]
  by_cases hE : ∃ k, Work.FIArea7.IsSepPairK r k d m n
  · obtain ⟨k0, hk0⟩ := hE
    have hle : k0 ≤ Nat.log 2 u :=
      Nat.le_log_of_pow_le (by norm_num) (le_trans (isSepPairKTwoPowLe hk0) h)
    rw [ind_pos (show ∃ k, Work.FIArea7.IsSepPairK r k d m n from ⟨k0, hk0⟩)]
    rw [Finset.sum_eq_single k0]
    · rw [ind_pos hk0]
    · intro kk _ hkk
      rw [ind_neg]
      intro hk
      exact absurd (isSepPairKKUnique hk hk0) hkk
    · intro hnot
      exact absurd (Finset.mem_range.mpr (by omega)) hnot
  · rw [ind_neg hE]
    refine (Finset.sum_eq_zero (fun kk _ => ?_)).symm
    rw [ind_neg]
    intro hk
    exact hE ⟨kk, hk⟩

theorem sepLHSBoundEps (h31 : Work.FIArea7.Prop231) :
    ∀ ε : ℝ, 0 < ε → ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      ∀ (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (k : ℤ) (c D r u z : ℕ)
        (P : ℝ → ℝ) (a b K : ℝ),
        1 ≤ c → 1 ≤ D → 2 ≤ r → 2 ≤ z → z ^ (r * r) ≤ u →
        (∀ z', ‖chi z'‖ ≤ 1) →
        (∀ z1 z2 : GaussianInt, IsCoprime z1 z2 → chi (z1 * z2) = chi z1 * chi z2) →
        ContDiff ℝ 1 P → 0 ≤ a → (∀ u, 0 ≤ P u) → (∀ u, P u ≤ 1) →
        (∀ u, P u ≠ 0 → a < u ∧ u ≤ b) → (∀ u, |deriv P u| ≤ K) →
        (∀ l d m n, Squarefree l → l ≤ u → (∀ p, p.Prime → p ∣ l → p ≤ z) →
            Work.FIArea7.IsSepPair r d m n → d * m * n = l → d ≤ D) →
        ‖Work.FIArea7.sepSumLHS u z (Work.FIArea7.smallCInner2EpsAux.cTerm Pa chi k c P)‖
          ≤ C * ((c.divisors.card : ℕ) : ℝ) * (u : ℝ) ^ ((23 : ℝ) / 24)
              * ((D : ℝ) ^ ((1 : ℝ) / 12)) * (Real.log ((u : ℝ) + 2)) ^ A
              * (((u : ℝ) + (c : ℝ) * (D : ℝ) + 2) ^ ε)
              * (K * |b - a| + 1) := by
  intro ε hε
  obtain ⟨Cs, As, hCs, hAs, hsmooth⟩ := smoothBilinEps h31 ε hε
  refine ⟨Cs * (2 : ℝ) ^ ((1 : ℝ) / 12) * 96, As + 2, by positivity, by linarith, ?_⟩
  intro Pa chi k c D r u z P a b K hc hD hr hz hzr hchi hmul hP hPa hP0 hP1 hPsupp hPder hDbound
  have hu : 1 ≤ u := by
    have h1 : 2 ^ (r * r) ≤ z ^ (r * r) := Nat.pow_le_pow_left hz (r * r)
    have h2 : 1 ≤ 2 ^ (r * r) := Nat.one_le_two_pow
    omega
  have huR : (1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu
  have hLGpos : 0 < Real.log ((u : ℝ) + 2) := Real.log_pos (by linarith)
  have hLGnn : 0 ≤ Real.log ((u : ℝ) + 2) := le_of_lt hLGpos
  set Bd : ℕ → ℝ := fun d =>
      Cs * (((c * d).divisors.card : ℕ) : ℝ) * ((((Nat.sqrt u : ℕ) : ℝ) + ((Nat.sqrt u : ℕ) : ℝ)) ^ ((1 : ℝ) / 12))
        * (((u / d : ℕ) : ℝ) ^ ((11 : ℝ) / 12)) * (Real.log (((u / d : ℕ) : ℝ) + 2)) ^ As
        * ((((u / d : ℕ) : ℝ) + ((c * d : ℕ) : ℝ) + 2) ^ ε) * (K * |b - a| + 1) with hBd
  -- ### Step 1: the pointwise decomposition of the `IsSepPair` indicator over `k`
  have hpoint : ∀ d m n : ℕ,
      ind (Work.FIArea7.IsSepPair r d m n
          ∧ (∀ p : ℕ, p.Prime → p ∣ d * m * n → p ≤ z) ∧ d * m * n ≤ u)
        * cTerm Pa chi k c P (d * m * n)
      = ∑ kk ∈ Finset.range (Nat.log 2 u + 1),
          ind (Work.FIArea7.IsSepPairK r kk d m n
              ∧ (∀ p : ℕ, p.Prime → p ∣ d * m * n → p ≤ z) ∧ d * m * n ≤ u)
            * cTerm Pa chi k c P (d * m * n) := by
    intro d m n
    by_cases hle : d * m * n ≤ u
    · have hL : ind (Work.FIArea7.IsSepPair r d m n
            ∧ (∀ p : ℕ, p.Prime → p ∣ d * m * n → p ≤ z) ∧ d * m * n ≤ u)
          = ind (Work.FIArea7.IsSepPair r d m n)
            * ind (∀ p : ℕ, p.Prime → p ∣ d * m * n → p ≤ z) := by
        rw [ind_and_and, ind_pos hle, mul_one]
      have hR : ∀ kk : ℕ,
          ind (Work.FIArea7.IsSepPairK r kk d m n
              ∧ (∀ p : ℕ, p.Prime → p ∣ d * m * n → p ≤ z) ∧ d * m * n ≤ u)
            = ind (Work.FIArea7.IsSepPairK r kk d m n)
              * ind (∀ p : ℕ, p.Prime → p ∣ d * m * n → p ≤ z) := by
        intro kk
        rw [ind_and_and, ind_pos hle, mul_one]
      rw [hL]
      have hRsum : (∑ kk ∈ Finset.range (Nat.log 2 u + 1),
            ind (Work.FIArea7.IsSepPairK r kk d m n
                ∧ (∀ p : ℕ, p.Prime → p ∣ d * m * n → p ≤ z) ∧ d * m * n ≤ u)
              * cTerm Pa chi k c P (d * m * n))
          = ∑ kk ∈ Finset.range (Nat.log 2 u + 1),
              ind (Work.FIArea7.IsSepPairK r kk d m n)
                * (ind (∀ p : ℕ, p.Prime → p ∣ d * m * n → p ≤ z)
                    * cTerm Pa chi k c P (d * m * n)) := by
        apply Finset.sum_congr rfl
        intro kk _
        rw [hR kk]
        ring
      rw [hRsum, ← Finset.sum_mul, isSepPair_indicator_decomp (r := r) (d := d) (m := m) (n := n)
        (u := u) hle]
      ring
    · have hz1 : ind (Work.FIArea7.IsSepPair r d m n
            ∧ (∀ p : ℕ, p.Prime → p ∣ d * m * n → p ≤ z) ∧ d * m * n ≤ u) = 0 := by
        rw [ind_neg]; intro hh; exact hle hh.2.2
      rw [hz1, zero_mul]
      refine Eq.symm ?_
      refine Finset.sum_eq_zero (fun kk _ => ?_)
      have h0 : ind (Work.FIArea7.IsSepPairK r kk d m n
            ∧ (∀ p : ℕ, p.Prime → p ∣ d * m * n → p ≤ z) ∧ d * m * n ≤ u) = 0 := by
        rw [ind_neg]; intro hh; exact hle hh.2.2
      rw [h0, zero_mul]
  -- ### Step 2: the reduction of the triple sum to a sum of bilinear forms
  have htriple := sepSumLHS_eq_tripleSum (r := r) (u := u) (z := z) (D := D) hr Pa chi k c P hDbound
  rw [htriple]
  -- ### Step 3: bound each `(d,k)`-summand
  have hinner : ∀ d ∈ Finset.Icc 1 D, ∀ kk ∈ Finset.range (Nat.log 2 u + 1),
      ‖∑ m ∈ Finset.Icc 1 u, ∑ n ∈ Finset.Icc 1 u,
          ind (Work.FIArea7.IsSepPairK r kk d m n
              ∧ (∀ p : ℕ, p.Prime → p ∣ d * m * n → p ≤ z) ∧ d * m * n ≤ u)
            * cTerm Pa chi k c P (d * m * n)‖ ≤ Bd d := by
    intro d hd kk hkk
    obtain ⟨A, B, hAB⟩ := isSepPairK_product r kk hr d
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hdD : d ≤ D := (Finset.mem_Icc.mp hd).2
    rw [bilinReduction hr hd1 A B hAB Pa chi k c z u P]
    set α : ℕ → ℂ := fun m => cCoeff Pa c z d * ind (A m) * cCoeff Pa c z m with hαdef
    set β : ℕ → ℂ := fun n => ind (B n) * cCoeff Pa c z n with hβdef
    have hα1 : ∀ m ∈ Finset.Icc 1 (Nat.sqrt u), ‖α m‖ ≤ 1 := by
      intro m _
      have h1 := norm_cCoeff_le_one Pa c z d
      have h2 := norm_ind_le_one (A m)
      have h3 := norm_cCoeff_le_one Pa c z m
      change ‖cCoeff Pa c z d * ind (A m) * cCoeff Pa c z m‖ ≤ 1
      calc ‖cCoeff Pa c z d * ind (A m) * cCoeff Pa c z m‖
          = ‖cCoeff Pa c z d‖ * ‖ind (A m)‖ * ‖cCoeff Pa c z m‖ := by rw [norm_mul, norm_mul]
        _ ≤ 1 * 1 * 1 :=
            mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)) h3 (norm_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    have hβ1 : ∀ n ∈ Finset.Icc 1 (Nat.sqrt u), ‖β n‖ ≤ 1 := by
      intro n _
      have h2 := norm_ind_le_one (B n)
      have h3 := norm_cCoeff_le_one Pa c z n
      change ‖ind (B n) * cCoeff Pa c z n‖ ≤ 1
      calc ‖ind (B n) * cCoeff Pa c z n‖ = ‖ind (B n)‖ * ‖cCoeff Pa c z n‖ := by rw [norm_mul]
        _ ≤ 1 * 1 := mul_le_mul h2 h3 (norm_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    have hc0 : 1 ≤ c * d := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    have hest := hsmooth chi k (c * d) (Nat.sqrt u) (Nat.sqrt u) (u / d) α β P a b K hc0 hchi hmul
      hα1 hβ1 hP hPa hP0 hP1 hPsupp hPder
    have heq : (∑ m ∈ Finset.Icc 1 (Nat.sqrt u), ∑ n ∈ Finset.Icc 1 (Nat.sqrt u),
          ind (m * n ≤ u / d)
            * ((cCoeff Pa c z d * ind (A m) * cCoeff Pa c z m)
              * (ind (B n) * cCoeff Pa c z n)
              * ((P (((c * d : ℕ) : ℝ) * ((m * n : ℕ) : ℝ)) : ℝ) : ℂ)
              * quadEigen (grossenChar chi k) ((c * d) * (m * n))))
        = (∑ m ∈ Finset.Icc 1 (Nat.sqrt u), ∑ n ∈ Finset.Icc 1 (Nat.sqrt u),
          (if m * n ≤ u / d
            then α m * β n * ((P (((c * d : ℕ) : ℝ) * ((m * n : ℕ) : ℝ)) : ℝ) : ℂ)
              * quadEigen (grossenChar chi k) ((c * d) * (m * n))
            else 0)) := by
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro n _
      rw [ind_mul_eq, hαdef, hβdef]
      by_cases hh : m * n ≤ u / d <;> simp [hh]
    rw [hBd]
    refine le_trans (le_of_eq (by rw [heq])) hest
  -- ### Step 4: assemble
  have hY : (∑ d ∈ Finset.Icc 1 D, ∑ m ∈ Finset.Icc 1 u, ∑ n ∈ Finset.Icc 1 u,
        ind (Work.FIArea7.IsSepPair r d m n
          ∧ (∀ p : ℕ, p.Prime → p ∣ d * m * n → p ≤ z) ∧ d * m * n ≤ u)
          * cTerm Pa chi k c P (d * m * n))
      = ∑ d ∈ Finset.Icc 1 D, ∑ kk ∈ Finset.range (Nat.log 2 u + 1),
          ∑ m ∈ Finset.Icc 1 u, ∑ n ∈ Finset.Icc 1 u,
        ind (Work.FIArea7.IsSepPairK r kk d m n
          ∧ (∀ p : ℕ, p.Prime → p ∣ d * m * n → p ≤ z) ∧ d * m * n ≤ u)
          * cTerm Pa chi k c P (d * m * n) := by
    rw [Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun m _ =>
      Finset.sum_congr rfl (fun n _ => hpoint d m n)))]
    rw [Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun m _ => Finset.sum_comm))]
    rw [Finset.sum_congr rfl (fun d _ => Finset.sum_comm)]
  rw [hY]
  have hbound1 : ‖(∑ d ∈ Finset.Icc 1 D, ∑ kk ∈ Finset.range (Nat.log 2 u + 1),
        ∑ m ∈ Finset.Icc 1 u, ∑ n ∈ Finset.Icc 1 u,
        ind (Work.FIArea7.IsSepPairK r kk d m n
          ∧ (∀ p : ℕ, p.Prime → p ∣ d * m * n → p ≤ z) ∧ d * m * n ≤ u)
          * cTerm Pa chi k c P (d * m * n))‖
      ≤ ∑ d ∈ Finset.Icc 1 D, ∑ kk ∈ Finset.range (Nat.log 2 u + 1), Bd d := by
    refine le_trans (norm_sum_le _ _) ?_
    apply Finset.sum_le_sum
    intro d hd
    refine le_trans (norm_sum_le _ _) ?_
    apply Finset.sum_le_sum
    intro kk hkk
    exact hinner d hd kk hkk
  refine le_trans hbound1 ?_
  rw [Finset.sum_congr rfl (fun d _ => by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul])]
  -- the final arithmetic
  set LG : ℝ := Real.log ((u : ℝ) + 2) with hLGdef
  set Ee : ℝ := ((u : ℝ) + (c : ℝ) * (D : ℝ) + 2) ^ ε with hEedef
  set Ff : ℝ := K * |b - a| + 1 with hFfdef
  set St : ℝ := Cs * (2 : ℝ) ^ ((1 : ℝ) / 12) * (u : ℝ) ^ ((1 : ℝ) / 24) * LG ^ As * Ee * Ff
    with hStdef
  have hKk_le : ((Nat.log 2 u + 1 : ℕ) : ℝ) ≤ 4 * LG := by
    rw [hLGdef]
    push_cast
    exact natLogTwoLe u hu
  have hK0 : 0 ≤ K := le_trans (abs_nonneg (deriv P 0)) (hPder 0)
  have hEenn : 0 ≤ Ee := by rw [hEedef]; exact Real.rpow_nonneg (by positivity) ε
  have hFfnn : 0 ≤ Ff := by rw [hFfdef]; nlinarith [abs_nonneg (b - a), hK0]
  have hStnn : 0 ≤ St := by
    rw [hStdef]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hCs)
      (Real.rpow_nonneg (by norm_num) _)) (Real.rpow_nonneg (by positivity) _))
      (Real.rpow_nonneg hLGnn _)) hEenn) hFfnn
  have hBdle : ∀ d ∈ Finset.Icc 1 D, Bd d
      ≤ St * ((((c * d).divisors.card : ℕ) : ℝ) * (((u / d : ℕ) : ℝ) ^ ((11 : ℝ) / 12))) := by
    intro d hd
    obtain ⟨hd1, hdD⟩ := Finset.mem_Icc.mp hd
    have h1 : ((((Nat.sqrt u : ℕ) : ℝ) + ((Nat.sqrt u : ℕ) : ℝ)) ^ ((1 : ℝ) / 12))
        ≤ (2 : ℝ) ^ ((1 : ℝ) / 12) * (u : ℝ) ^ ((1 : ℝ) / 24) := sqrtTwoRpow12Le u hu
    have h2 : (Real.log (((u / d : ℕ) : ℝ) + 2)) ^ As
          * ((((u / d : ℕ) : ℝ) + ((c * d : ℕ) : ℝ) + 2) ^ ε)
        ≤ LG ^ As * Ee := by
      rw [hLGdef, hEedef]
      exact rpowLogMono c D u d ε As hε hAs hd1 hdD
    have h3 : 0 ≤ (Real.log (((u / d : ℕ) : ℝ) + 2)) ^ As
        * ((((u / d : ℕ) : ℝ) + ((c * d : ℕ) : ℝ) + 2) ^ ε) :=
      mul_nonneg (Real.rpow_nonneg (Real.log_nonneg (by
        have h : (0 : ℝ) ≤ ((u / d : ℕ) : ℝ) := Nat.cast_nonneg _
        linarith)) As)
        (Real.rpow_nonneg (by positivity) ε)
    rw [hBd, hStdef]
    calc Cs * (((c * d).divisors.card : ℕ) : ℝ)
            * ((((Nat.sqrt u : ℕ) : ℝ) + ((Nat.sqrt u : ℕ) : ℝ)) ^ ((1 : ℝ) / 12))
            * (((u / d : ℕ) : ℝ) ^ ((11 : ℝ) / 12))
            * (Real.log (((u / d : ℕ) : ℝ) + 2)) ^ As
            * ((((u / d : ℕ) : ℝ) + ((c * d : ℕ) : ℝ) + 2) ^ ε) * (K * |b - a| + 1)
        = Cs * (((c * d).divisors.card : ℕ) : ℝ) * (((u / d : ℕ) : ℝ) ^ ((11 : ℝ) / 12))
            * (((((Nat.sqrt u : ℕ) : ℝ) + ((Nat.sqrt u : ℕ) : ℝ)) ^ ((1 : ℝ) / 12))
              * ((Real.log (((u / d : ℕ) : ℝ) + 2)) ^ As
                * ((((u / d : ℕ) : ℝ) + ((c * d : ℕ) : ℝ) + 2) ^ ε)))
            * (K * |b - a| + 1) := by ring
      _ ≤ Cs * (((c * d).divisors.card : ℕ) : ℝ) * (((u / d : ℕ) : ℝ) ^ ((11 : ℝ) / 12))
            * ((((2 : ℝ) ^ ((1 : ℝ) / 12) * (u : ℝ) ^ ((1 : ℝ) / 24)) * (LG ^ As * Ee)))
            * (K * |b - a| + 1) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul h1 h2 h3 (by positivity)
      _ = (Cs * (2 : ℝ) ^ ((1 : ℝ) / 12) * (u : ℝ) ^ ((1 : ℝ) / 24) * LG ^ As * Ee
            * (K * |b - a| + 1))
          * ((((c * d).divisors.card : ℕ) : ℝ) * (((u / d : ℕ) : ℝ) ^ ((11 : ℝ) / 12))) := by ring
  have hsumBd : (∑ d ∈ Finset.Icc 1 D, Bd d)
      ≤ St * (24 * (((c.divisors.card : ℕ) : ℝ)) * (D : ℝ) ^ ((1 : ℝ) / 12)
          * (u : ℝ) ^ ((11 : ℝ) / 12) * LG) := by
    refine le_trans (Finset.sum_le_sum hBdle) ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hStnn
    have h := sumTauMulDivRpowLe c u D hu cardDivisorsMulLe
    rw [hLGdef]
    exact h
  rw [← Finset.mul_sum]
  refine le_trans (mul_le_mul_of_nonneg_left hsumBd
    (by positivity : (0 : ℝ) ≤ ((Nat.log 2 u + 1 : ℕ) : ℝ))) ?_
  -- final product manipulation
  have hpow : (u : ℝ) ^ ((1 : ℝ) / 24) * (u : ℝ) ^ ((11 : ℝ) / 12) = (u : ℝ) ^ ((23 : ℝ) / 24) := by
    rw [← Real.rpow_add (by positivity : (0 : ℝ) < (u : ℝ))]
    norm_num
  have hLGpos' : 0 < LG := by rw [hLGdef]; exact hLGpos
  have hlog1 : LG ^ As * LG = LG ^ (As + 1) := by
    have h := Real.rpow_add hLGpos' As 1
    rw [Real.rpow_one] at h
    exact h.symm
  have hlog2 : LG ^ (As + 1) * LG = LG ^ (As + 2) := by
    have h := Real.rpow_add hLGpos' (As + 1) 1
    rw [Real.rpow_one] at h
    rw [← h]
    congr 1
    ring
  have hlog : ((Nat.log 2 u + 1 : ℕ) : ℝ) * LG ^ As * LG ≤ 4 * LG ^ (As + 2) := by
    have h1 := hKk_le
    calc ((Nat.log 2 u + 1 : ℕ) : ℝ) * LG ^ As * LG
        = ((Nat.log 2 u + 1 : ℕ) : ℝ) * (LG ^ As * LG) := by ring
      _ = ((Nat.log 2 u + 1 : ℕ) : ℝ) * LG ^ (As + 1) := by rw [hlog1]
      _ ≤ (4 * LG) * LG ^ (As + 1) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (by rw [hLGdef]; exact hLGnn) _)
      _ = 4 * (LG ^ (As + 1) * LG) := by ring
      _ = 4 * LG ^ (As + 2) := by rw [hlog2]
  calc ((Nat.log 2 u + 1 : ℕ) : ℝ)
        * (St * (24 * (((c.divisors.card : ℕ) : ℝ)) * (D : ℝ) ^ ((1 : ℝ) / 12)
          * (u : ℝ) ^ ((11 : ℝ) / 12) * LG))
      = (Cs * (2 : ℝ) ^ ((1 : ℝ) / 12) * 24) * (((c.divisors.card : ℕ) : ℝ))
          * (D : ℝ) ^ ((1 : ℝ) / 12) * Ee * Ff
          * (((Nat.log 2 u + 1 : ℕ) : ℝ) * LG ^ As * LG)
          * ((u : ℝ) ^ ((1 : ℝ) / 24) * (u : ℝ) ^ ((11 : ℝ) / 12)) := by
        rw [hStdef]; ring
    _ ≤ (Cs * (2 : ℝ) ^ ((1 : ℝ) / 12) * 24) * (((c.divisors.card : ℕ) : ℝ))
          * (D : ℝ) ^ ((1 : ℝ) / 12) * Ee * Ff
          * (4 * LG ^ (As + 2)) * ((u : ℝ) ^ ((23 : ℝ) / 24)) := by
        rw [hpow]
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (by positivity : (0:ℝ) ≤ (u:ℝ)) _)
        exact mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = (Cs * (2 : ℝ) ^ ((1 : ℝ) / 12) * 96) * (((c.divisors.card : ℕ) : ℝ))
          * (u : ℝ) ^ ((23 : ℝ) / 24) * (D : ℝ) ^ ((1 : ℝ) / 12) * LG ^ (As + 2)
          * Ee * Ff := by ring

end

end Work.FIArea7.smallCInner2EpsAux
