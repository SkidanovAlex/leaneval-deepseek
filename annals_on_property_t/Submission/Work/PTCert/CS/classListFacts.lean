import Mathlib
import Submission.Work.PTCert.CSAux
import Submission.Work.PTCert.cert1Aux

/-!
# The list-level facts of `ClassSem`

The two subdivided families of the class data (`klist`, `tlist`) are checked, chunk by chunk, by the
kernel checks `C.kl_ok{j}` / `C.tl_ok{j}` (`classKeysOK`) and `C.kl_perm` / `C.tl_perm`
(`isPermOf`).  Here those checks are turned into the plain list statements:

* the total lengths are `ncls = 7229` (the fourteen chunks of width `500` plus the last of width `229`);
* the flattened lists are permutations of `allKeys ngL`, resp. of `List.range 6561`;
* every key of the entry of `klist` at a class `c < ncls` has class `c` (and likewise for `tlist`).

The chunk structure of the `klist`/`tlist` definitions is recorded in
`Work.PTCert.cert1Aux` (`klist_eq`, `klist_chunk_lt`, `klist_chunk_ge`, `klList14_getD_len`, …); the
subdivision of an index `c < 7229` into `(c / 500, c % 500)` (resp. `(14, c - 7000)`) is what makes the
per-chunk checks applicable.
-/

set_option maxRecDepth 100000

namespace Work.PTCert.CS

open Submission.PTCert Submission.PTCert.G Submission.PTCert.D

/-! ## Soundness of `classKeysOK` -/

/-- `classKeysOK clT kl c0 ncls = true` says: for the `i`-th chunk `kl[i]` (class `c0 + i`), that class
is `< ncls` and every key of the chunk has `clT`-class `c0 + i`. -/
private theorem classKeysOK_iff (clT : NT) (kl : List (List ℕ)) (c0 ncls : ℕ) :
    classKeysOK clT kl c0 ncls = true ↔
      ∀ i < kl.length, c0 + i < ncls ∧
        ∀ k ∈ kl.getD i [], w34 clT k / 1048576 = c0 + i := by
  induction kl generalizing c0 with
  | nil => simp [classKeysOK]
  | cons l t ih =>
    have hstep : classKeysOK clT (l :: t) c0 ncls =
        (Nat.blt c0 ncls && allL l (fun k => Nat.beq (w34 clT k / 1048576) c0)
          && classKeysOK clT t (c0 + 1) ncls) := rfl
    rw [hstep, Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq, allL_iff_CSAux, ih]
    constructor
    · rintro ⟨⟨hlt, hall⟩, ht⟩ i hi
      rcases i with _ | j
      · rw [List.length_cons] at hi
        refine ⟨by simpa using hlt, ?_⟩
        intro k hk
        rw [List.getD_cons_zero] at hk
        have hh := hall k hk
        simpa [Nat.beq_eq] using hh
      · have hj : j < t.length := by simpa using hi
        have h := ht j hj
        rw [List.getD_cons_succ]
        refine ⟨by rw [show c0 + (j + 1) = (c0 + 1) + j by omega]; exact h.1, ?_⟩
        intro k hk
        rw [show c0 + (j + 1) = (c0 + 1) + j by omega]
        exact h.2 k hk
    · intro h
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simpa using (h 0 (by simp)).1
      · intro a ha
        have h0 := (h 0 (by simp)).2 a (by simpa using ha)
        simpa [Nat.beq_eq] using h0
      · intro j hj
        have hh := h (j + 1) (by simpa using hj)
        rw [List.getD_cons_succ] at hh
        refine ⟨by rw [show c0 + 1 + j = c0 + (j + 1) by omega]; exact hh.1, ?_⟩
        intro k hk
        rw [show c0 + 1 + j = c0 + (j + 1) by omega]
        exact hh.2 k hk

/-! ## The per-chunk checks of the first fourteen chunks -/

/-- The class check of the `j`-th class chunk (`j < 14`), with class offset `500 * j`. -/
private theorem klList14_classKeysOK (j : ℕ) (hj : j < 14) :
    classKeysOK gclT (klList14.getD j []) (500 * j) 7229 = true := by
  interval_cases j
  · exact Submission.PTCert.C.kl_ok0
  · exact Submission.PTCert.C.kl_ok1
  · exact Submission.PTCert.C.kl_ok2
  · exact Submission.PTCert.C.kl_ok3
  · exact Submission.PTCert.C.kl_ok4
  · exact Submission.PTCert.C.kl_ok5
  · exact Submission.PTCert.C.kl_ok6
  · exact Submission.PTCert.C.kl_ok7
  · exact Submission.PTCert.C.kl_ok8
  · exact Submission.PTCert.C.kl_ok9
  · exact Submission.PTCert.C.kl_ok10
  · exact Submission.PTCert.C.kl_ok11
  · exact Submission.PTCert.C.kl_ok12
  · exact Submission.PTCert.C.kl_ok13

/-- The target-pair check of the `j`-th target chunk (`j < 14`), with class offset `500 * j`. -/
private theorem tlList14_classKeysOK (j : ℕ) (hj : j < 14) :
    classKeysOK tclT (tlList14.getD j []) (500 * j) 7229 = true := by
  interval_cases j
  · exact Submission.PTCert.C.tl_ok0
  · exact Submission.PTCert.C.tl_ok1
  · exact Submission.PTCert.C.tl_ok2
  · exact Submission.PTCert.C.tl_ok3
  · exact Submission.PTCert.C.tl_ok4
  · exact Submission.PTCert.C.tl_ok5
  · exact Submission.PTCert.C.tl_ok6
  · exact Submission.PTCert.C.tl_ok7
  · exact Submission.PTCert.C.tl_ok8
  · exact Submission.PTCert.C.tl_ok9
  · exact Submission.PTCert.C.tl_ok10
  · exact Submission.PTCert.C.tl_ok11
  · exact Submission.PTCert.C.tl_ok12
  · exact Submission.PTCert.C.tl_ok13

/-! ## The classes of the keys and of the target pairs -/

/-- Every key of the entry of `klist` at the class `c < 7229` has class `c`. -/
private theorem klist_gcls_of_mem (c : ℕ) (hc : c < 7229) (k : ℕ) (hk : k ∈ klist.getD c []) :
    w34 gclT k / 1048576 = c := by
  by_cases hlt : c < 7000
  · -- the index lies in the `(c / 500)`-th chunk of width `500`
    have hj : c / 500 < 14 := by omega
    have hi : c % 500 < 500 := Nat.mod_lt _ (by norm_num)
    have hci : 500 * (c / 500) + c % 500 = c := Nat.div_add_mod c 500
    have hck := klList14_classKeysOK (c / 500) hj
    have hspec := (classKeysOK_iff gclT (klList14.getD (c / 500) [])
      (500 * (c / 500)) 7229).mp hck (c % 500)
      (by rw [klList14_getD_len (c / 500) hj]; exact hi)
    rw [hci] at hspec
    have hk' : k ∈ (klList14.getD (c / 500) []).getD (c % 500) [] := by
      have h := klist_chunk_lt (c / 500) (c % 500) hj hi
      rw [hci] at h
      rw [← h]; exact hk
    exact hspec.2 k hk'
  · -- the index lies in the last chunk `kl14` of width `229`
    have hge : 7000 ≤ c := by omega
    have hi : c - 7000 < 229 := by omega
    have hci : 7000 + (c - 7000) = c := by omega
    have hlen14 : (kl14 : List (List ℕ)).length = 229 := klList_len_last
    have hck : classKeysOK gclT kl14 7000 7229 = true := Submission.PTCert.C.kl_ok14
    have hspec := (classKeysOK_iff gclT kl14 7000 7229).mp hck (c - 7000)
      (by rw [hlen14]; exact hi)
    rw [hci] at hspec
    have hk' : k ∈ kl14.getD (c - 7000) [] := by
      have h := klist_chunk_ge (c - 7000) hi
      rw [hci] at h
      rw [← h]; exact hk
    exact hspec.2 k hk'

/-- Every target pair of the entry of `tlist` at the class `c < 7229` has class `c`. -/
private theorem tlist_tcls_of_mem (c : ℕ) (hc : c < 7229) (p : ℕ) (hp : p ∈ tlist.getD c []) :
    w34 tclT p / 1048576 = c := by
  by_cases hlt : c < 7000
  · have hj : c / 500 < 14 := by omega
    have hi : c % 500 < 500 := Nat.mod_lt _ (by norm_num)
    have hci : 500 * (c / 500) + c % 500 = c := Nat.div_add_mod c 500
    have hck := tlList14_classKeysOK (c / 500) hj
    have hspec := (classKeysOK_iff tclT (tlList14.getD (c / 500) [])
      (500 * (c / 500)) 7229).mp hck (c % 500)
      (by rw [tlList14_getD_len (c / 500) hj]; exact hi)
    rw [hci] at hspec
    have hk' : p ∈ (tlList14.getD (c / 500) []).getD (c % 500) [] := by
      have h := tlist_chunk_lt (c / 500) (c % 500) hj hi
      rw [hci] at h
      rw [← h]; exact hp
    exact hspec.2 p hk'
  · have hge : 7000 ≤ c := by omega
    have hi : c - 7000 < 229 := by omega
    have hci : 7000 + (c - 7000) = c := by omega
    have hlen14 : (tl14 : List (List ℕ)).length = 229 := tlList_len_last
    have hck : classKeysOK tclT tl14 7000 7229 = true := Submission.PTCert.C.tl_ok14
    have hspec := (classKeysOK_iff tclT tl14 7000 7229).mp hck (c - 7000)
      (by rw [hlen14]; exact hi)
    rw [hci] at hspec
    have hk' : p ∈ tl14.getD (c - 7000) [] := by
      have h := tlist_chunk_ge (c - 7000) hi
      rw [hci] at h
      rw [← h]; exact hp
    exact hspec.2 p hk'

/-! ## The list facts -/

theorem classListFacts :
    Submission.PTCert.G.klist.length = Submission.PTCert.G.ncls ∧
    Submission.PTCert.G.tlist.length = Submission.PTCert.G.ncls ∧
    Submission.PTCert.G.klist.flatten.Perm (Submission.PTCert.allKeys Submission.PTCert.D.ngL) ∧
    Submission.PTCert.G.tlist.flatten.Perm (List.range 6561) ∧
    (∀ c < Submission.PTCert.G.ncls, ∀ k ∈ Submission.PTCert.G.klist.getD c [],
        Submission.PTCert.G.gcls k = c) ∧
    (∀ c < Submission.PTCert.G.ncls, ∀ p ∈ Submission.PTCert.G.tlist.getD c [],
        Submission.PTCert.G.tcls p = c) := by
  have h14k : (kl14 : List (List ℕ)).length = 229 := klList_len_last
  have h14t : (tl14 : List (List ℕ)).length = 229 := tlList_len_last
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [klist_eq, List.length_append, klList14_flatten_len, h14k]; decide
  · rw [tlist_eq, List.length_append, tlList14_flatten_len, h14t]; decide
  · exact permCheckKSound _ _ Submission.PTCert.C.kl_perm
  · exact permCheckKSound _ _ Submission.PTCert.C.tl_perm
  · intro c hc k hk
    exact klist_gcls_of_mem c (by simpa [ncls] using hc) k hk
  · intro c hc p hp
    exact tlist_tcls_of_mem c (by simpa [ncls] using hc) p hp

end Work.PTCert.CS
