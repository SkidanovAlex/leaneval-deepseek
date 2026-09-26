import Mathlib
import Submission.Work.PTCert.Cert2.Setup

namespace Work.PTCert.Cert2

open Submission.PTCert Submission.PTCert.G Submission.PTCert.D Submission.PTCert.D2 Submission.PTCert.C2K

/-! ## Per-class-chunk coefficient identities

Each kernel check `cs_ok{j}` (namespace `Submission.PTCert.C2K`) is the statement that the class-sum
identity holds for every class of the `j`-th chunk `kl{j}` / `tl{j}` starting at class `500*j`.
`classSumOK_iff_c2` turns it into a `∀ i < (kl{j}).length` statement, and `foldr_add_eq_sum` passes
from the `foldr` form produced by `classSumOK` to the `.map … |>.sum` form of the target. -/

lemma cid0 (i : ℕ) (hi : i < 500) :
    denZ * ((kl0.getD i []).map (fun k => (multE k : ℤ) * sv (p8 valT k))).sum
      - scZ * ((tl0.getD i []).map (fun p => sv (p8 qT p))).sum
      + sv (p8 resT (500 * 0 + i)) = 0 := by
  have hlen : kl0.length = 500 := by decide +kernel
  have h := (classSumOK_iff_c2 kl0 tl0 0).mp cs_ok0 i (by rw [hlen]; exact hi)
  simpa [foldr_add_eq_sum] using h

lemma cid1 (i : ℕ) (hi : i < 500) :
    denZ * ((kl1.getD i []).map (fun k => (multE k : ℤ) * sv (p8 valT k))).sum
      - scZ * ((tl1.getD i []).map (fun p => sv (p8 qT p))).sum
      + sv (p8 resT (500 * 1 + i)) = 0 := by
  have hlen : kl1.length = 500 := by decide +kernel
  have h := (classSumOK_iff_c2 kl1 tl1 500).mp cs_ok1 i (by rw [hlen]; exact hi)
  simpa [foldr_add_eq_sum] using h

lemma cid2 (i : ℕ) (hi : i < 500) :
    denZ * ((kl2.getD i []).map (fun k => (multE k : ℤ) * sv (p8 valT k))).sum
      - scZ * ((tl2.getD i []).map (fun p => sv (p8 qT p))).sum
      + sv (p8 resT (500 * 2 + i)) = 0 := by
  have hlen : kl2.length = 500 := by decide +kernel
  have h := (classSumOK_iff_c2 kl2 tl2 1000).mp cs_ok2 i (by rw [hlen]; exact hi)
  simpa [foldr_add_eq_sum] using h

lemma cid3 (i : ℕ) (hi : i < 500) :
    denZ * ((kl3.getD i []).map (fun k => (multE k : ℤ) * sv (p8 valT k))).sum
      - scZ * ((tl3.getD i []).map (fun p => sv (p8 qT p))).sum
      + sv (p8 resT (500 * 3 + i)) = 0 := by
  have hlen : kl3.length = 500 := by decide +kernel
  have h := (classSumOK_iff_c2 kl3 tl3 1500).mp cs_ok3 i (by rw [hlen]; exact hi)
  simpa [foldr_add_eq_sum] using h

lemma cid4 (i : ℕ) (hi : i < 500) :
    denZ * ((kl4.getD i []).map (fun k => (multE k : ℤ) * sv (p8 valT k))).sum
      - scZ * ((tl4.getD i []).map (fun p => sv (p8 qT p))).sum
      + sv (p8 resT (500 * 4 + i)) = 0 := by
  have hlen : kl4.length = 500 := by decide +kernel
  have h := (classSumOK_iff_c2 kl4 tl4 2000).mp cs_ok4 i (by rw [hlen]; exact hi)
  simpa [foldr_add_eq_sum] using h

lemma cid5 (i : ℕ) (hi : i < 500) :
    denZ * ((kl5.getD i []).map (fun k => (multE k : ℤ) * sv (p8 valT k))).sum
      - scZ * ((tl5.getD i []).map (fun p => sv (p8 qT p))).sum
      + sv (p8 resT (500 * 5 + i)) = 0 := by
  have hlen : kl5.length = 500 := by decide +kernel
  have h := (classSumOK_iff_c2 kl5 tl5 2500).mp cs_ok5 i (by rw [hlen]; exact hi)
  simpa [foldr_add_eq_sum] using h

lemma cid6 (i : ℕ) (hi : i < 500) :
    denZ * ((kl6.getD i []).map (fun k => (multE k : ℤ) * sv (p8 valT k))).sum
      - scZ * ((tl6.getD i []).map (fun p => sv (p8 qT p))).sum
      + sv (p8 resT (500 * 6 + i)) = 0 := by
  have hlen : kl6.length = 500 := by decide +kernel
  have h := (classSumOK_iff_c2 kl6 tl6 3000).mp cs_ok6 i (by rw [hlen]; exact hi)
  simpa [foldr_add_eq_sum] using h

lemma cid7 (i : ℕ) (hi : i < 500) :
    denZ * ((kl7.getD i []).map (fun k => (multE k : ℤ) * sv (p8 valT k))).sum
      - scZ * ((tl7.getD i []).map (fun p => sv (p8 qT p))).sum
      + sv (p8 resT (500 * 7 + i)) = 0 := by
  have hlen : kl7.length = 500 := by decide +kernel
  have h := (classSumOK_iff_c2 kl7 tl7 3500).mp cs_ok7 i (by rw [hlen]; exact hi)
  simpa [foldr_add_eq_sum] using h

lemma cid8 (i : ℕ) (hi : i < 500) :
    denZ * ((kl8.getD i []).map (fun k => (multE k : ℤ) * sv (p8 valT k))).sum
      - scZ * ((tl8.getD i []).map (fun p => sv (p8 qT p))).sum
      + sv (p8 resT (500 * 8 + i)) = 0 := by
  have hlen : kl8.length = 500 := by decide +kernel
  have h := (classSumOK_iff_c2 kl8 tl8 4000).mp cs_ok8 i (by rw [hlen]; exact hi)
  simpa [foldr_add_eq_sum] using h

lemma cid9 (i : ℕ) (hi : i < 500) :
    denZ * ((kl9.getD i []).map (fun k => (multE k : ℤ) * sv (p8 valT k))).sum
      - scZ * ((tl9.getD i []).map (fun p => sv (p8 qT p))).sum
      + sv (p8 resT (500 * 9 + i)) = 0 := by
  have hlen : kl9.length = 500 := by decide +kernel
  have h := (classSumOK_iff_c2 kl9 tl9 4500).mp cs_ok9 i (by rw [hlen]; exact hi)
  simpa [foldr_add_eq_sum] using h

lemma cid10 (i : ℕ) (hi : i < 500) :
    denZ * ((kl10.getD i []).map (fun k => (multE k : ℤ) * sv (p8 valT k))).sum
      - scZ * ((tl10.getD i []).map (fun p => sv (p8 qT p))).sum
      + sv (p8 resT (500 * 10 + i)) = 0 := by
  have hlen : kl10.length = 500 := by decide +kernel
  have h := (classSumOK_iff_c2 kl10 tl10 5000).mp cs_ok10 i (by rw [hlen]; exact hi)
  simpa [foldr_add_eq_sum] using h

lemma cid11 (i : ℕ) (hi : i < 500) :
    denZ * ((kl11.getD i []).map (fun k => (multE k : ℤ) * sv (p8 valT k))).sum
      - scZ * ((tl11.getD i []).map (fun p => sv (p8 qT p))).sum
      + sv (p8 resT (500 * 11 + i)) = 0 := by
  have hlen : kl11.length = 500 := by decide +kernel
  have h := (classSumOK_iff_c2 kl11 tl11 5500).mp cs_ok11 i (by rw [hlen]; exact hi)
  simpa [foldr_add_eq_sum] using h

lemma cid12 (i : ℕ) (hi : i < 500) :
    denZ * ((kl12.getD i []).map (fun k => (multE k : ℤ) * sv (p8 valT k))).sum
      - scZ * ((tl12.getD i []).map (fun p => sv (p8 qT p))).sum
      + sv (p8 resT (500 * 12 + i)) = 0 := by
  have hlen : kl12.length = 500 := by decide +kernel
  have h := (classSumOK_iff_c2 kl12 tl12 6000).mp cs_ok12 i (by rw [hlen]; exact hi)
  simpa [foldr_add_eq_sum] using h

lemma cid13 (i : ℕ) (hi : i < 500) :
    denZ * ((kl13.getD i []).map (fun k => (multE k : ℤ) * sv (p8 valT k))).sum
      - scZ * ((tl13.getD i []).map (fun p => sv (p8 qT p))).sum
      + sv (p8 resT (500 * 13 + i)) = 0 := by
  have hlen : kl13.length = 500 := by decide +kernel
  have h := (classSumOK_iff_c2 kl13 tl13 6500).mp cs_ok13 i (by rw [hlen]; exact hi)
  simpa [foldr_add_eq_sum] using h

lemma cid14 (i : ℕ) (hi : i < 229) :
    denZ * ((kl14.getD i []).map (fun k => (multE k : ℤ) * sv (p8 valT k))).sum
      - scZ * ((tl14.getD i []).map (fun p => sv (p8 qT p))).sum
      + sv (p8 resT (7000 + i)) = 0 := by
  have hlen : kl14.length = 229 := by decide +kernel
  have h := (classSumOK_iff_c2 kl14 tl14 7000).mp cs_ok14 i (by rw [hlen]; exact hi)
  simpa [foldr_add_eq_sum] using h

/-- **Class-sum identity of the `C2` certificate.**  For every class `cl < ncls = 7229` the exact
coefficient identity of `FinalStep` holds: `denZ · Σ multE·valZ − scZ · Σ qZ + resZ = 0`. -/
theorem classEqC2 : ∀ cl < Submission.PTCert.G.ncls,
    Work.PTCert.Cert2.denZ * (((Submission.PTCert.G.klist.getD cl []).map
        (fun k => (Submission.PTCert.G.multE k : ℤ) * Work.PTCert.Cert2.valZ k)).sum)
      - Work.PTCert.Cert2.scZ * (((Submission.PTCert.G.tlist.getD cl []).map
        Work.PTCert.Cert2.qZ).sum) + Work.PTCert.Cert2.resZ cl = 0 := by
  intro cl hcl
  have hcl7229 : cl < 7229 := hcl
  rcases lt_or_ge cl 7000 with hlt | hge
  · -- `cl < 7000`: the chunk is `cl / 500`, the offset `cl % 500`.
    obtain ⟨j, hj, i, hi, hcl_eq⟩ : ∃ j, j < 14 ∧ ∃ i, i < 500 ∧ 500 * j + i = cl := by
      refine ⟨cl / 500, ?_, cl % 500, Nat.mod_lt _ (by norm_num), Nat.div_add_mod cl 500⟩
      rw [Nat.div_lt_iff_lt_mul (by norm_num : (0 : ℕ) < 500)]
      omega
    rw [← hcl_eq, klist_chunk_lt j i hj hi, tlist_chunk_lt j i hj hi]
    interval_cases j
    · exact cid0 i hi
    · exact cid1 i hi
    · exact cid2 i hi
    · exact cid3 i hi
    · exact cid4 i hi
    · exact cid5 i hi
    · exact cid6 i hi
    · exact cid7 i hi
    · exact cid8 i hi
    · exact cid9 i hi
    · exact cid10 i hi
    · exact cid11 i hi
    · exact cid12 i hi
    · exact cid13 i hi
  · -- `7000 ≤ cl < 7229`: the last chunk, offset `cl - 7000 < 229`.
    obtain ⟨i, hi, hcl_eq⟩ : ∃ i, i < 229 ∧ 7000 + i = cl := by
      refine ⟨cl - 7000, ?_, ?_⟩ <;> omega
    rw [← hcl_eq, klist_chunk_ge i hi, tlist_chunk_ge i hi]
    exact cid14 i hi

end Work.PTCert.Cert2
