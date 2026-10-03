import Mathlib
import Submission.Work.OROneRel.tlLowCycStep

namespace Work.OROneRel

/-!
# The cycle prefix of a multiple of the window size

The low window of the two-letter band `a^p b^q` is a single cycle of length `p+q`, whose word is
`cycWord p q`.  This file shows that the forward cycle prefix of length `(p+q) * c` is exactly the
`c`-th power of `cycWord p q`, and that the backward cycle prefix of length `(p+q) * c` is its
`(-c)`-th power.

The proof has three ingredients, all elementary:

* the cycle letter `cycLetter p q` is periodic with period `p+q` (`cycLetter_add_mul`);
* therefore a forward prefix of length `(p+q) * (c+1)` is the forward prefix of length `(p+q) * c`
  followed by the full cycle word (`cycFwdList_succ_mul`), and the first statement follows by
  induction using `FreeGroup.mul_mk`;
* the backward prefix is literally the `invRev` of the forward prefix started `m` steps earlier
  (`cycBwdList_eq_invRev`); the second statement then follows from `FreeGroup.inv_mk` and the
  forward result.
-/

/-! ## Periodicity of the cycle letters -/

/-- The cycle letter is periodic with period `(p+q) * c` in the index. -/
theorem cycLetter_add_mul (p q c : ℕ) (i : ℤ) :
    cycLetter p q (i + (((p + q) * c : ℕ) : ℤ)) = cycLetter p q i := by
  apply cycLetter_eq_of_dvd_sub
  rw [tlN_cast]
  exact ⟨(c : ℤ), by push_cast; ring⟩

/-- A forward cycle prefix depends on its starting index only modulo `(p+q) * c`. -/
theorem cycFwdList_add_mul (p q c : ℕ) (k : ℤ) (m : ℕ) :
    cycFwdList p q (k + (((p + q) * c : ℕ) : ℤ)) m = cycFwdList p q k m := by
  simp only [cycFwdList]
  apply List.map_congr_left
  intro j hj
  apply congrArg (fun a => (a, true))
  rw [show k + ↑((p + q) * c) + ↑j = (k + ↑j) + ↑((p + q) * c) by ring]
  exact cycLetter_add_mul p q c (k + (j : ℤ))

/-! ## The forward prefix of a multiple of the cycle -/

/-- Splitting a forward prefix of length `(p+q) * (c+1)` into the prefix of length `(p+q) * c`
followed by the full cycle `cycList p q`. -/
theorem cycFwdList_succ_mul (p q c : ℕ) :
    cycFwdList p q 0 ((p + q) * (c + 1)) =
      cycFwdList p q 0 ((p + q) * c) ++ cycList p q := by
  have h : (p + q) * (c + 1) = (p + q) * c + (p + q) := by ring
  rw [h]
  simp only [cycFwdList, cycList]
  rw [List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro x hx
  simp only [Function.comp_apply]
  rw [show (0 : ℤ) + (((p + q) * c + x : ℕ) : ℤ)
      = (x : ℤ) + (((p + q) * c : ℕ) : ℤ) by push_cast; ring]
  exact congrArg (fun a => (a, true)) (cycLetter_add_mul p q c (x : ℤ))

/-- **The forward prefix of length `(p+q) * c` spells the `c`-th power of the cycle word.** -/
theorem cycFwdWord_eq_pow (p q c : ℕ) :
    FreeGroup.mk (cycFwdList p q 0 ((p + q) * c)) = cycWord p q ^ c := by
  induction c with
  | zero =>
    simp only [Nat.mul_zero, cycFwdList, List.range_zero, List.map_nil,
      FreeGroup.one_eq_mk, pow_zero]
  | succ c ih =>
    rw [cycFwdList_succ_mul p q c, ← FreeGroup.mul_mk, ih]
    show cycWord p q ^ c * FreeGroup.mk (cycList p q) = cycWord p q ^ (c + 1)
    rw [show FreeGroup.mk (cycList p q) = cycWord p q from rfl, pow_succ]

/-! ## The backward prefix as the inverse of the forward one -/

/-- The backward cycle prefix of length `m` is the `invRev` of the forward cycle prefix of length
`m` started `m` steps earlier: reading the forward prefix backwards reverts the order of the
letters and inverts them. -/
theorem cycBwdList_eq_invRev (p q : ℕ) (k : ℤ) (m : ℕ) :
    cycBwdList p q k m = FreeGroup.invRev (cycFwdList p q (k - (m : ℤ)) m) := by
  rw [FreeGroup.invRev]
  apply List.ext_getElem
  · simp [cycBwdList, cycFwdList]
  · intro i h1 h2
    have hi : i < m := by simpa [cycBwdList] using h1
    simp only [cycBwdList, cycFwdList, List.getElem_map, List.getElem_reverse, List.length_map,
      List.length_range, List.getElem_range, Bool.not_true]
    apply congrArg (fun a => (a, false))
    congr 1
    omega

/-- **The backward prefix of length `(p+q) * c` spells the `(-c)`-th power of the cycle word.** -/
theorem cycBwdWord_eq_zpow (p q c : ℕ) :
    FreeGroup.mk (cycBwdList p q 0 ((p + q) * c)) = cycWord p q ^ (-(c : ℤ)) := by
  rw [cycBwdList_eq_invRev p q 0 ((p + q) * c)]
  have hfst : cycFwdList p q (0 - (((p + q) * c : ℕ) : ℤ)) ((p + q) * c)
      = cycFwdList p q 0 ((p + q) * c) := by
    have h := cycFwdList_add_mul p q c (0 - (((p + q) * c : ℕ) : ℤ)) ((p + q) * c)
    rw [show (0 : ℤ) - (((p + q) * c : ℕ) : ℤ) + (((p + q) * c : ℕ) : ℤ) = 0 by ring] at h
    exact h.symm
  rw [hfst, ← FreeGroup.inv_mk, cycFwdWord_eq_pow]
  rw [← zpow_natCast, zpow_neg]

theorem tlLowCyc_prefix_pow (p q c : ℕ) :
    FreeGroup.mk (Work.OROneRel.cycFwdList p q 0 ((p + q) * c)) = Work.OROneRel.cycWord p q ^ c ∧
    FreeGroup.mk (Work.OROneRel.cycBwdList p q 0 ((p + q) * c))
      = Work.OROneRel.cycWord p q ^ (-(c : ℤ)) :=
  ⟨cycFwdWord_eq_pow p q c, cycBwdWord_eq_zpow p q c⟩

end Work.OROneRel
