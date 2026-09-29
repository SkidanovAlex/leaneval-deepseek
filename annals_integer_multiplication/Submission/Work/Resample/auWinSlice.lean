import Mathlib
import Submission.Work.Resample.auIdx
import Submission.Work.Resample.auSizes

namespace Work.Resample

open HvdH

/-!
# Slicing the extended input array into the windows of `auWin` (paper Lemma 4.9)

The `k`-th window `auWin p α s t u k` is, by definition, the list of the `auL p α` entries
`auExt p α s u [auK s t k + i]` for `i < auL p α`.  This module proves that this is nothing but
the slice `(auExt p α s u).drop (auK s t k) |>.take (auL p α)` of the extended array, so that the
window is available to a program as a `take`/`drop` of the (one) extended array, and that mapping
`cfxVal` over the window commutes with that slicing.

The only real input is that the window fits inside the extended array, which follows from
`auCop p α s * s - auOff p α s ≥ s + 2·auM p α + 1` (`auM`, `auCop`, `auOff` as in the paper) and
`auK s t k ≤ s` for `k < t`.
-/

/-- `(l.drop K).take n` is the pointwise map over `List.range n` of the entries `l[K + i]`,
whenever the slice `[K, K+n)` stays inside `l`. -/
lemma auList_drop_take_map_getD {α : Type*} (l : List α) (d : α) (K n : ℕ)
    (h : K + n ≤ l.length) :
    (l.drop K).take n = (List.range n).map (fun i => l.getD (K + i) d) := by
  apply List.ext_getElem?
  intro j
  by_cases hj : j < n
  · rw [List.getElem?_take, if_pos hj, List.getElem?_drop, List.getElem?_map,
      List.getElem?_range hj]
    simp only [Option.map_some]
    rw [List.getD_eq_getElem l d (n := K + j) (by omega),
      List.getElem?_eq_getElem (by omega)]
  · rw [List.getElem?_take, if_neg hj, List.getElem?_map]
    have hnone : (List.range n)[j]? = none := by
      apply List.getElem?_eq_none_iff.mpr
      rw [List.length_range]; omega
    rw [hnone]; rfl

/-- Length of the extended input array: `auCop p α s` copies of `u`, dropped by `auOff p α s`. -/
lemma auExt_length (p α s : ℕ) (u : List (ℤ × ℤ)) :
    (auExt p α s u).length = auCop p α s * u.length - auOff p α s := by
  simp [auExt]

/-- The extended array is long enough for a whole window beyond any centre `≤ s`:
`auOff + s + 2·auM + 1 ≤ auCop·s`.  Indeed `auCop·s = s·⌊X/s⌋ ≥ X - (s-1)` with
`X = auOff + 2s + 2·auM`. -/
lemma auCop_mul_ge (p α s : ℕ) (hs : 1 ≤ s) :
    auOff p α s + s + 2 * auM p α + 1 ≤ auCop p α s * s := by
  have hs0 : 0 < s := hs
  set X : ℕ := auOff p α s + 2 * s + 2 * auM p α with hX
  have hmod : X % s ≤ s - 1 := by have := Nat.mod_lt X hs0; omega
  have hdiv : (X / s) * s + X % s = X := by
    rw [mul_comm (X / s) s]; exact Nat.div_add_mod X s
  have hcop : auCop p α s * s = (X / s) * s := by
    simp only [auCop]; rw [← hX]
  omega

/-- The window of output `k` is the slice of the extended array of length `auL p α` starting at
the centre `auK s t k`. -/
lemma auWin_slice (p α s t : ℕ) (hs : 2 ≤ s) (u : List (ℤ × ℤ)) (hu : u.length = s)
    (k : ℕ) (hk : k < t) :
    auWin p α s t u k = ((auExt p α s u).drop (auK s t k)).take (auL p α) := by
  have hcop : auOff p α s + s + 2 * auM p α + 1 ≤ auCop p α s * s :=
    auCop_mul_ge p α s (by omega)
  have hK : auK s t k ≤ s := auIdx_aux_auK_le_s s t k hk
  have hlen : (auExt p α s u).length = auCop p α s * s - auOff p α s := by
    rw [auExt_length p α s u, hu]
  have hbound : auK s t k + auL p α ≤ (auExt p α s u).length := by
    rw [hlen]; simp only [auL]; omega
  rw [auWin]
  exact (auList_drop_take_map_getD (auExt p α s u) (0, 0) (auK s t k) (auL p α) hbound).symm

theorem auWinSlice (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (u : List (ℤ × ℤ))
    (hu : u.length = s) :
    (Work.Resample.auExt p α s u).length = Work.Resample.auCop p α s * s - Work.Resample.auOff p α s ∧
    (∀ k < t, Work.Resample.auWin p α s t u k =
      ((Work.Resample.auExt p α s u).drop (Work.Resample.auK s t k)).take (Work.Resample.auL p α)) ∧
    (∀ k < t, HvdH.ofList ((Work.Resample.auWin p α s t u k).map HvdH.cfxVal)
      = HvdH.ofList ((((Work.Resample.auExt p α s u).map HvdH.cfxVal).drop (Work.Resample.auK s t k)).take (Work.Resample.auL p α))) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [auExt_length p α s u, hu]
  · intro k hk
    exact auWin_slice p α s t hs u hu k hk
  · intro k hk
    rw [auWin_slice p α s t hs u hu k hk, List.map_take, List.map_drop]

end Work.Resample
