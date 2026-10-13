/-
  WilE5.Bounds — the number of *preceding valid tests* of a test.

  `prec M NΦ σ t` is the list of tests `t'` that are valid for the state `σ`, belong to the
  nominal test list `testL q M NΦ`, and are `testLt`-below `t`.  Its length is the number of
  conditions that a child of `σ` at `t` appends (through `childΞ`), so it must be bounded by a
  polynomial — and the point of the statement is that the bound uses the *actual* size
  `σ.Φ.length` of the flatness family, not the nominal source bound `NΦ`.

  The proof is a containment argument: `prec` is a duplicate-free list of valid tests, every valid
  test has source index `< σ.Φ.length`, so `prec ⊆ testL q M (σ.Φ.length)`; and
  `testL q M L` is a sublist of `range L × (mList q M × finRange q)`, of length `L * (M+1)^q * q`.
-/
import Mathlib
import Submission.Work.WilE5.Sys

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilE5.Bounds

variable {p q r : ℕ}

/-! ## §1. `mList` and `testL`: length, duplication and membership -/

/-- `mList q M` enumerates `Fin q → Fin (M+1)`, so it has no duplicates. -/
theorem mList_nodup (q M : ℕ) : (Work.WilE5.mList q M).Nodup := by
  unfold Work.WilE5.mList
  refine List.Nodup.map ?_ (Finset.nodup_toList _)
  intro a b h
  funext i
  exact Fin.ext (by simpa using congrFun h i)

/-- `mList q M` has exactly `(M+1)^q` elements. -/
theorem mList_length (q M : ℕ) : (Work.WilE5.mList q M).length = (M + 1) ^ q := by
  have h : (Work.WilE5.mList q M).length
      = (Finset.univ : Finset (Fin q → Fin (M + 1))).card := by
    rw [Work.WilE5.mList, List.length_map, Multiset.length_toList, Finset.card_def]
  rw [h, Finset.card_univ, Fintype.card_fun]
  simp

/-- The test list has no duplicates. -/
theorem testL_nodup (q M NΦ : ℕ) : (Work.WilE5.testL q M NΦ).Nodup := by
  unfold Work.WilE5.testL
  refine List.Nodup.filter _ (List.Nodup.map ?_ ?_)
  · intro a b h
    exact Prod.ext (congrArg (fun t : Work.WilE5.Test q => t.i) h)
      (Prod.ext (congrArg (fun t : Work.WilE5.Test q => t.m) h)
        (congrArg (fun t : Work.WilE5.Test q => t.l) h))
  · exact (List.nodup_range).product ((mList_nodup q M).product (List.nodup_finRange q))

/-- The test list has at most `L * (M+1)^q * q` elements. -/
theorem testL_length_le (q M L : ℕ) :
    (Work.WilE5.testL q M L).length ≤ L * (M + 1) ^ q * q := by
  have h1 : (Work.WilE5.testL q M L).length
      ≤ ((List.range L) ×ˢ ((Work.WilE5.mList q M) ×ˢ (List.finRange q))).length := by
    unfold Work.WilE5.testL
    exact (List.length_filter_le _ _).trans (le_of_eq (List.length_map _))
  rw [List.length_product, List.length_product, List.length_range, List.length_finRange,
    mList_length] at h1
  exact h1.trans (le_of_eq (Nat.mul_assoc _ _ _).symm)

/-- Membership in the test list: source index `< NΦ`, multi-index with entries `≤ M`, and a
nonzero entry in the peeled direction. -/
theorem mem_testL_iff' {q M NΦ : ℕ} (t : Work.WilE5.Test q) :
    t ∈ Work.WilE5.testL q M NΦ ↔
      t.i < NΦ ∧ t.m ∈ Work.WilE5.mList q M ∧ t.m t.l ≠ 0 := by
  rw [Work.WilE5.testL, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨hmem, hne⟩
    obtain ⟨⟨a, b, c⟩, hp, rfl⟩ := List.mem_map.mp hmem
    have hp1 : a ∈ List.range NΦ := (List.mem_product.mp hp).1
    have hp2 : (b, c) ∈ (Work.WilE5.mList q M).product (List.finRange q) :=
      (List.mem_product.mp hp).2
    have hb : b ∈ Work.WilE5.mList q M := (List.mem_product.mp hp2).1
    exact ⟨List.mem_range.mp hp1, hb, hne⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨List.mem_map.mpr ⟨(t.i, (t.m, t.l)), ?_, rfl⟩, h3⟩
    exact List.mem_product.mpr ⟨List.mem_range.mpr h1,
      List.mem_product.mpr ⟨h2, List.mem_finRange t.l⟩⟩

/-! ## §2. The bound -/

/-- The number of *preceding valid* tests of `t` is bounded by the size of the flatness family
(not by the nominal source bound `NΦ`): every element of `prec` is valid, hence has source index
`< σ.Φ.length`, and for each source index there are at most `(M+1)^q * q` tests. -/
theorem prec_length_le {p q r : ℕ} (M NΦ : ℕ) (σ : Work.WilE5.St p q r)
    (t : Work.WilE5.Test q) :
    (Work.WilE5.prec M NΦ σ t).length ≤ σ.Φ.length * (M + 1) ^ q * q := by
  have hnodup : (Work.WilE5.prec M NΦ σ t).Nodup := by
    rw [Work.WilE5.prec]
    exact (testL_nodup q M NΦ).filter _
  have hsub : ∀ u ∈ Work.WilE5.prec M NΦ σ t, u ∈ Work.WilE5.testL q M (σ.Φ.length) := by
    intro u hu
    rw [Work.WilE5.prec] at hu
    obtain ⟨huL, hup⟩ := List.mem_filter.mp hu
    have hvv : Work.WilE5.valid σ u := by
      have h : (decide (Work.WilE5.valid σ u) && Work.WilE5.testLt u t) = true :=
        of_decide_eq_true hup
      exact of_decide_eq_true (Bool.and_eq_true_iff.mp h).1
    have hui : u.i < σ.Φ.length := hvv.1
    have htm := (mem_testL_iff' (M := M) (NΦ := NΦ) u).mp huL
    exact (mem_testL_iff' (M := M) (NΦ := σ.Φ.length) u).mpr ⟨hui, htm.2.1, htm.2.2⟩
  exact (List.subperm_of_subset hnodup hsub).length_le.trans
    (testL_length_le q M (σ.Φ.length))

end Work.WilE5.Bounds
