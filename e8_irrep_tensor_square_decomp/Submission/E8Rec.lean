import Submission.E8Star
import Submission.E8Regroup
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_qZ_add_nsmul_posRoot_dominant

/-!
# The Freudenthal recursion for the candidate characters

This file proves hypothesis (d) of `Submission.E8Character.eq_of_freudenthal` for the candidate
multipity functions `Mnu i` of `Submission.E8Cert`: the dominant-chamber Freudenthal recursion at
every dominant weight `ν` below `ord40 i`.

The route is

* `Mnu_sum_core` -- the regrouping: the ungrouped Freudenthal sum over the terms equals
  `∑_e ctab d e * Mtab i e` (using `Submission.E8Regroup.sum_regroup`, the certificate `cert_sid`
  and `ctab_eq`);
* `Mnu_freud` -- the recursion itself, using `E8Extract.freud_star`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

noncomputable section
open scoped BigOperators

namespace Submission.E8Star

open Submission.E8Extract Submission.E8Orbit Submission.E8Character Submission.E8Casimir
open Submission.E8Enum Submission.E8Numerics Submission.E8Engine Submission.E8Cert
open Submission.WeylReflect Submission.WeylWeights

/-- **The regrouping step.**  The ungrouped sum of the c-table terms, weighted by `Mtab i`
evaluated at the dominant conjugate, equals the c-table sum. -/
theorem Mnu_sum_core (i d : Fin 40) :
    (∑ j : Fin 120, ∑ k : Fin 4, brkTab d j k *
        (if h : sidTab d j k < 40 then Mtab i ⟨sidTab d j k, h⟩ else 0))
      = ∑ e : Fin 40, ctab d e * Mtab i e := by
  rw [Submission.E8Regroup.sum_regroup (fun j k => brkTab d j k) (fun j k => sidTab d j k)
    (fun e => stList d e) (fun e => Mtab i e)
    (fun j k h => st_mem d j k h) (fun e p hp => st_sid d e hp) (fun e => st_nodup d e)]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [ctab_eq d e]
  rfl

/-- The candidate character at a c-table term is the table value at its dominant conjugate. -/
theorem Mnu_term (i d : Fin 40) (j : Fin 120) (k : Fin 4) :
    Mnu i (term d j k)
      = (if h : sidTab d j k < 40 then Mtab i ⟨sidTab d j k, h⟩ else 0) := by
  simp only [Mnu]
  rw [cert_sid d j k]
  split <;> rfl

/-- The `brk` value of a surviving c-table term. -/
theorem brk_term (d : Fin 40) (j : Fin 120) (k : Fin 4) (h : sidTab d j k < 40) :
    brk (term d j k) j = brkTab d j k := by
  rw [← brkF_eq]
  exact brk_eq d j k h

/-- The weight of a c-table term, as a multiple of a positive root. -/
theorem term_eq_smul (d : Fin 40) (j : Fin 120) (k : Fin 4) :
    term d j k = ord40get d + (k.1 + 1) • pR j := by
  rw [term, smulE_eq, pRn_eq]

/-! ## The roots are positive roots -/

theorem qE_pR : ∀ j : Fin 120, qE (pR j) = 2 := by decide

theorem pR_ne_zero : ∀ j : Fin 120, pR j ≠ 0 := by decide

theorem posF_pR : ∀ j : Fin 120, posF (pR j) = true := by decide

theorem pR_memP : ∀ j : Fin 120, pR j ∈ Commons.LinearAlgebra.Matrix.Cartan.E8posRoots.P := by
  intro j
  rw [Commons.LinearAlgebra.Matrix.Cartan.E8posRoots.memP]
  refine ⟨?_, pR_ne_zero j, posF_true.mp (posF_pR j)⟩
  show qq (pR j) = 2
  rw [← qE_eq_qq]
  exact qE_pR j

theorem ord40_dom : ∀ d : Fin 40, ∀ i, 0 ≤ ord40get d i := by decide

theorem qZ_ord40_nonneg : ∀ d : Fin 40, 0 ≤ Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.qZ
    (ord40get d) := by decide

/-- **The `k ≥ 5` vanishing**: the shift leaves the norm sphere of the forty weights. -/
theorem Mnu_eq_zero_of_five_le (i d : Fin 40) (j : Fin 120) {k : ℕ} (hk : 5 ≤ k) :
    Mnu i (ord40get d + k • pR j) = 0 := by
  have hq := Commons.LinearAlgebra.Matrix.Cartan.E8_qZ_add_nsmul_posRoot_dominant
    (ord40get d) (pR j) (ord40_dom d) (pR_memP j) k
  have hbig : 50 ≤ Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.qZ (ord40get d + k • pR j) := by
    have hk2 : (50 : ℤ) ≤ 2 * (k : ℤ) ^ 2 := by
      have : (5 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
      nlinarith [sq_nonneg ((k : ℤ) - 5), this]
    linarith [qZ_ord40_nonneg d, hq]
  have hgt : ¬ (qE (ord40get d + k • pR j) ≤ 40) := by
    rw [qE_eq_qq]
    exact not_le.mpr (by linarith [hbig])
  show (domIdx (ord40get d + k • pR j)).elim 0 (fun e => Mtab i e) = 0
  rw [domIdx, if_neg hgt]
  rfl

/-- **The height vanishing**: a shift that leaves the cone below the top weight contributes `0`. -/
theorem Mnu_eq_zero_of_height (i : Fin 40) {ν : Fin 8 → ℤ} {j : Fin 120} {k : ℕ}
    (h : htOf (ord40get i - ν) < (k : ℤ) * htOf (pR j)) :
    Mnu i (ν + k • pR j) = 0 := by
  by_contra hne
  have hkey : htOf (ord40get i - (ν + k • pR j))
      = htOf (ord40get i - ν) - (k : ℤ) * htOf (pR j) := by
    rw [show ord40get i - (ν + k • pR j) = (ord40get i - ν) - k • pR j by abel, htOf_sub,
      htOf_nsmul]
  rcases Mnu_support i hne with h1 | h1
  · rw [h1, htOf_zero] at hkey
    omega
  · have := htOf_nonneg h1
    omega

/-! ## The `k`-range reduction -/

/-- Pruning a `k`-sum: if the summand vanishes above `4`, and between `N` and `4`, then the sum
over `Icc 1 N` is the sum over `Icc 1 4`. -/
theorem sum_Icc_eq_four (f : ℕ → ℤ) (N : ℕ)
    (h1 : ∀ k, 5 ≤ k → f k = 0) (h2 : ∀ k, N < k → k ≤ 4 → f k = 0) :
    (∑ k ∈ Finset.Icc 1 N, f k) = ∑ k ∈ Finset.Icc 1 4, f k := by
  by_cases hN : N ≤ 4
  · exact (Submission.E8Checks.sum_Icc_eq_of_gt hN (fun k hk => by
      by_cases hk5 : 5 ≤ k
      · exact h1 k hk5
      · exact h2 k hk (by omega))).symm
  · exact Submission.E8Checks.sum_Icc_eq_of_gt (by omega) (fun k hk => h1 k (by omega))

/-- **The Freudenthal sum at `ν = ord40get d`**, rewritten with the certificate. -/
theorem Mnu_sum_eq (i d : Fin 40) :
    (∑ j : Fin 120, ∑ k ∈ Finset.Icc 1 (htOf (ord40get i - ord40get d)).toNat,
        brk (ord40get d + k • pR j) j * Mnu i (ord40get d + k • pR j))
      = ∑ j : Fin 120, ∑ k : Fin 4, brkTab d j k *
          (if h : sidTab d j k < 40 then Mtab i ⟨sidTab d j k, h⟩ else 0) := by
  refine Finset.sum_congr rfl fun j _ => ?_
  have hgt : ∀ k : ℕ, 5 ≤ k →
      brk (ord40get d + k • pR j) j * Mnu i (ord40get d + k • pR j) = 0 := fun k hk => by
    rw [Mnu_eq_zero_of_five_le i d j hk, mul_zero]
  have hlt : ∀ k : ℕ, (htOf (ord40get i - ord40get d)).toNat < k → k ≤ 4 →
      brk (ord40get d + k • pR j) j * Mnu i (ord40get d + k • pR j) = 0 := fun k hk _ => by
    have h1 := Submission.E8Checks.htOf_le_toNat (ord40get i - ord40get d)
    have h2 : ((htOf (ord40get i - ord40get d)).toNat : ℤ) < (k : ℤ) := by exact_mod_cast hk
    have h3 : (1 : ℤ) ≤ htOf (pR j) := htOf_pR j
    have hk0 : (0 : ℤ) ≤ (k : ℤ) := by positivity
    have h4 : (k : ℤ) ≤ (k : ℤ) * htOf (pR j) := by nlinarith [h3, hk0]
    rw [Mnu_eq_zero_of_height i (by linarith), mul_zero]
  rw [sum_Icc_eq_four (fun k => brk (ord40get d + k • pR j) j *
    Mnu i (ord40get d + k • pR j)) (htOf (ord40get i - ord40get d)).toNat hgt hlt]
  rw [Submission.E8Regroup.sum_Icc_one_four]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← term_eq_smul]
  by_cases hs : sidTab d j k < 40
  · rw [Mnu_term i d j k, dif_pos hs, brk_term d j k hs]
  · rw [Mnu_term i d j k, dif_neg hs]
    simp

/-! ## The forty weights -/

theorem exists_ord40_of_mem_the40 :
    ∀ ν ∈ Submission.E8Enum.the40, ∃ d : Fin 40, ord40get d = ν := by decide

theorem posF_two_lam_sub_ord40 :
    ∀ i : Fin 40, posF (2 • Submission.E8Enum.lam - ord40get i) = true := by decide

/-- Every dominant weight in the cone below `ord40 i` is one of the forty. -/
theorem exists_ord40 {i : Fin 40} {ν : Fin 8 → ℤ} (hν : Dominant ν)
    (hcon : posCon (ord40get i - ν)) : ∃ d : Fin 40, ord40get d = ν := by
  apply exists_ord40_of_mem_the40
  apply Submission.E8Enum.mem_the40
  · exact Submission.E8Enum.allNonneg_true.mpr hν
  · apply Submission.E8Enum.posB_true.mpr
    have h2 : posCon (2 • Submission.E8Enum.lam - ord40get i) :=
      posF_true.mp (posF_two_lam_sub_ord40 i)
    have heq : 2 • Submission.E8Enum.lam - ν = (2 • Submission.E8Enum.lam - ord40get i)
        + (ord40get i - ν) := by abel
    rw [heq]
    exact posCon_add h2 hcon

/-- **Hypothesis (d) of `eq_of_freudenthal` for the candidate characters.** -/
theorem Mnu_freud (i : Fin 40) {ν : Fin 8 → ℤ} (hν : Dominant ν)
    (hcon : posCon (ord40get i - ν)) :
    (Bint (ord40get i) - Bint ν) * Mnu i ν
      = 2 * ∑ j : Fin 120, ∑ k ∈ Finset.Icc 1 (htOf (ord40get i - ν)).toNat,
          brk (ν + k • pR j) j * Mnu i (ν + k • pR j) := by
  obtain ⟨d, hd⟩ := Submission.E8Star.exists_ord40 (i := i) hν hcon
  subst hd
  have hcon' : posCon (ord40get i - ord40get d) := hcon
  rw [Mnu_dom i d, Mnu_sum_eq i d, Mnu_sum_core i d]
  exact freud_star i d (Or.inr (Submission.E8Enum.posB_true.mpr hcon'))

end Submission.E8Star
