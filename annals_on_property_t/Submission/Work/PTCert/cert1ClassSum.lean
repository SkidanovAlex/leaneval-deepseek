import Mathlib
import Submission.Work.PTCert.cert1Aux

/-!
# `Work.PTCert.cert1ClassSum` — the exact class sums of certificate 1

The kernel checks `cs_ok0, …, cs_ok14` assert `classSumOK valT multT resT qC1 20 SC kl{j} tl{j} (500·j)`:
for every class `i` of the `j`-th class chunk, `20 · u(i) − 2^80 · tq(i) + res(i) = 0`, where `u` is
the `multE`-weighted sum of the value table over `kl{j}[i]` and `tq` is the `qC1`-sum over `tl{j}[i]`.

This file packages the 15 kernel facts into the pointwise statement `cert1ClassSum` for *every* class
index `cl < ncls = 7229`, using the chunk structure `klist = kl0 ++ ⋯ ++ kl14` of the class lists
(`klist_chunk_lt`, `klist_chunk_ge` of `cert1Aux`).
-/

namespace Work.PTCert

open Submission.PTCert Submission.PTCert.G Submission.PTCert.D Submission.PTCert.D1
open Submission.PTCert.C1K
open scoped BigOperators

noncomputable section

/-- The `j`-th class chunk of certificate 1 (group-key lists).  For `j ≤ 14` this is `kl{j}`. -/
def klChunk (j : ℕ) : List (List ℕ) := klList.getD j []

/-- The `j`-th class chunk of certificate 1 (target-pair lists).  For `j ≤ 14` this is `tl{j}`. -/
def tlChunk (j : ℕ) : List (List ℕ) := tlList.getD j []

lemma klList14_getD_eq (j : ℕ) (hj : j < 14) : klList14.getD j [] = klChunk j := by
  interval_cases j <;> rfl

lemma tlList14_getD_eq (j : ℕ) (hj : j < 14) : tlList14.getD j [] = tlChunk j := by
  interval_cases j <;> rfl

lemma klChunk_len (j : ℕ) (hj : j < 14) : (klChunk j).length = 500 := by
  interval_cases j <;> decide +kernel

lemma tlChunk_len (j : ℕ) (hj : j < 14) : (tlChunk j).length = 500 := by
  interval_cases j <;> decide +kernel

lemma klChunk14_len : (klChunk 14).length = 229 := by decide +kernel

lemma tlChunk14_len : (tlChunk 14).length = 229 := by decide +kernel

/-- Locating the chunk of `klist` at an index `< 7000`. -/
lemma klist_getD_lt (j i : ℕ) (hj : j < 14) (hi : i < 500) :
    klist.getD (500 * j + i) [] = (klChunk j).getD i [] := by
  rw [klist_chunk_lt j i hj hi, klList14_getD_eq j hj]

lemma tlist_getD_lt (j i : ℕ) (hj : j < 14) (hi : i < 500) :
    tlist.getD (500 * j + i) [] = (tlChunk j).getD i [] := by
  rw [tlist_chunk_lt j i hj hi, tlList14_getD_eq j hj]

/-- Locating the last chunk of `klist` at an index `≥ 7000`. -/
lemma klist_getD_ge (i : ℕ) (hi : i < 229) :
    klist.getD (7000 + i) [] = (klChunk 14).getD i [] := by
  rw [klist_chunk_ge i hi]
  rfl

lemma tlist_getD_ge (i : ℕ) (hi : i < 229) :
    tlist.getD (7000 + i) [] = (tlChunk 14).getD i [] := by
  rw [tlist_chunk_ge i hi]
  rfl

lemma cert1u_eq_of_lt (j i : ℕ) (hj : j < 14) (hi : i < 500) :
    cert1u (500 * j + i)
      = (((klChunk j).getD i []).map (fun k => (multE k : ℤ) * cert1pv k)).sum := by
  unfold cert1u
  rw [klist_getD_lt j i hj hi]

lemma cert1tq_eq_of_lt (j i : ℕ) (hj : j < 14) (hi : i < 500) :
    cert1tq (500 * j + i) = (((tlChunk j).getD i []).map qC1).sum := by
  unfold cert1tq
  rw [tlist_getD_lt j i hj hi]

lemma cert1u_eq_of_ge (i : ℕ) (hi : i < 229) :
    cert1u (7000 + i)
      = (((klChunk 14).getD i []).map (fun k => (multE k : ℤ) * cert1pv k)).sum := by
  unfold cert1u
  rw [klist_getD_ge i hi]

lemma cert1tq_eq_of_ge (i : ℕ) (hi : i < 229) :
    cert1tq (7000 + i) = (((tlChunk 14).getD i []).map qC1).sum := by
  unfold cert1tq
  rw [tlist_getD_ge i hi]

/-- The content of a single `classSumOK` check, in the `List.sum` form used by `cert1u`/`cert1tq`. -/
lemma classSumOK_chunk_eq {kl tl : List (List ℕ)} {c0 : ℕ}
    (h : classSumOK valT multT resT qC1 20 cert1SC kl tl c0 = true)
    {i : ℕ} (hi : i < kl.length) :
    20 * ((kl.getD i []).map (fun k => (multE k : ℤ) * cert1pv k)).sum
      - cert1SC * ((tl.getD i []).map qC1).sum + cert1res (c0 + i) = 0 := by
  have h' := (classSumOK_iff kl tl c0).mp h i hi
  rwa [foldr_add_eq_sum, foldr_add_eq_sum] at h'

/-- The class-sum identity on one whole chunk `j ≤ 14`. -/
lemma cert1_classSum_chunk (j : ℕ) (hj : j < 15) (i : ℕ) (hi : i < (klChunk j).length) :
    20 * (((klChunk j).getD i []).map (fun k => (multE k : ℤ) * cert1pv k)).sum
      - cert1SC * (((tlChunk j).getD i []).map qC1).sum + cert1res (500 * j + i) = 0 := by
  interval_cases j
  · exact classSumOK_chunk_eq cs_ok0 hi
  · exact classSumOK_chunk_eq cs_ok1 hi
  · exact classSumOK_chunk_eq cs_ok2 hi
  · exact classSumOK_chunk_eq cs_ok3 hi
  · exact classSumOK_chunk_eq cs_ok4 hi
  · exact classSumOK_chunk_eq cs_ok5 hi
  · exact classSumOK_chunk_eq cs_ok6 hi
  · exact classSumOK_chunk_eq cs_ok7 hi
  · exact classSumOK_chunk_eq cs_ok8 hi
  · exact classSumOK_chunk_eq cs_ok9 hi
  · exact classSumOK_chunk_eq cs_ok10 hi
  · exact classSumOK_chunk_eq cs_ok11 hi
  · exact classSumOK_chunk_eq cs_ok12 hi
  · exact classSumOK_chunk_eq cs_ok13 hi
  · exact classSumOK_chunk_eq cs_ok14 hi

theorem cert1ClassSum (cl : ℕ) (hcl : cl < Submission.PTCert.G.ncls) : 20 * Work.PTCert.cert1u cl - Work.PTCert.cert1SC * Work.PTCert.cert1tq cl + Work.PTCert.cert1res cl = 0 := by
  have hncls : Submission.PTCert.G.ncls = 7229 := rfl
  rw [hncls] at hcl
  by_cases h : cl < 7000
  · have hj : cl / 500 < 14 := by omega
    have hi : cl % 500 < 500 := Nat.mod_lt _ (by norm_num)
    have hcl_eq : cl = 500 * (cl / 500) + cl % 500 := by
      have := Nat.div_add_mod cl 500
      omega
    have hlen : cl % 500 < (klChunk (cl / 500)).length := by
      rw [klChunk_len (cl / 500) hj]; exact hi
    rw [hcl_eq, cert1u_eq_of_lt (cl / 500) (cl % 500) hj hi,
      cert1tq_eq_of_lt (cl / 500) (cl % 500) hj hi]
    exact cert1_classSum_chunk (cl / 500) (by omega) (cl % 500) hlen
  · have hge : 7000 ≤ cl := by omega
    have hi : cl - 7000 < 229 := by omega
    have hcl_eq : cl = 7000 + (cl - 7000) := by omega
    have hlen : cl - 7000 < (klChunk 14).length := by
      rw [klChunk14_len]; exact hi
    rw [hcl_eq, cert1u_eq_of_ge (cl - 7000) hi, cert1tq_eq_of_ge (cl - 7000) hi]
    exact cert1_classSum_chunk 14 (by norm_num) (cl - 7000) hlen

end

end Work.PTCert
