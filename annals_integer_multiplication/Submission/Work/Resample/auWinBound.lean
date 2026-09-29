import Mathlib
import Submission.Work.Resample.pbDefs

set_option linter.unusedVariables false

namespace Work.Resample

/-- Every value has encoding size at least `1` (`vsz .nil = 1`). -/
lemma auVsz_pos (v : HvdH.Val) : 1 ≤ HvdH.vsz v := by
  cases v with
  | int z => simp [HvdH.vsz, HvdH.Val.enc]
  | nil => simp [HvdH.vsz, HvdH.Val.enc]
  | cons a b => simp [HvdH.vsz, HvdH.Val.enc]

/-- The window entries stay within the size bound `B` along the recurrence: the new window
`((W k).drop (g k) ++ [ELEM.getD (Σ_{j<k} g j) .nil]).take L` only ever inserts an entry of `ELEM`
(or, when the element run is exhausted, the value `.nil`, which is in a window only if `L ≥ 1`,
hence `B ≥ 1` because `W 0` then has an entry).  Induction on `k`; note `vsz v ≥ 1` for every
`HvdH.Val`. -/
theorem auWinBound (t L B : ℕ) (g : ℕ → ℕ) (ELEM : List HvdH.Val) (W : ℕ → List HvdH.Val)
    (hg : ∀ k, g k ≤ 1)
    (hrec : ∀ k < t, W (k+1) = ((W k).drop (g k) ++
      [ELEM.getD (((List.range k).map g).sum) HvdH.Val.nil]).take L)
    (hlen : ∀ k ≤ t, (W k).length = L)
    (hW0 : ∀ v ∈ W 0, HvdH.vsz v ≤ B)
    (hE : ∀ v ∈ ELEM, HvdH.vsz v ≤ B) :
    ∀ k ≤ t, ∀ v ∈ W k, HvdH.vsz v ≤ B := by
  by_cases hL : L = 0
  · -- all windows are empty
    intro k hk v hv
    have hlen0 := hlen k hk
    rw [hL] at hlen0
    rw [List.length_eq_zero_iff] at hlen0
    rw [hlen0] at hv
    simp at hv
  · -- `L ≥ 1`, so `W 0` has an entry and hence `B ≥ 1 = vsz .nil`
    have hB1 : 1 ≤ B := by
      have hne : W 0 ≠ [] := by
        intro h
        have h0 := hlen 0 (Nat.zero_le t)
        rw [h] at h0
        simp at h0
        omega
      obtain ⟨v0, hv0⟩ := List.exists_mem_of_ne_nil _ hne
      have h1 : HvdH.vsz v0 ≤ B := hW0 v0 hv0
      have h2 : 1 ≤ HvdH.vsz v0 := auVsz_pos v0
      omega
    have hnil : HvdH.vsz HvdH.Val.nil ≤ B := by
      have h1 : HvdH.vsz HvdH.Val.nil = 1 := by simp [HvdH.vsz, HvdH.Val.enc]
      omega
    intro k
    induction k with
    | zero => intro _; exact hW0
    | succ k ih =>
      intro hk v hv
      have hkt : k ≤ t := by omega
      have hklt : k < t := by omega
      rw [hrec k hklt] at hv
      -- the new window entry is either an old window entry or the freshly inserted value
      have hv' : v ∈ (W k).drop (g k) ++
          [ELEM.getD (((List.range k).map g).sum) HvdH.Val.nil] :=
        List.mem_of_mem_take hv
      rcases List.mem_append.mp hv' with h1 | h2
      · exact ih hkt v (List.mem_of_mem_drop h1)
      · rw [List.mem_singleton] at h2
        subst h2
        by_cases hs : (((List.range k).map g).sum) < ELEM.length
        · rw [List.getD_eq_getElem ELEM HvdH.Val.nil hs]
          exact hE _ (List.getElem_mem hs)
        · rw [List.getD_eq_default ELEM HvdH.Val.nil (by omega)]
          exact hnil

end Work.Resample
