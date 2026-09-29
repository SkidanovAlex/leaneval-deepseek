import Mathlib
import Submission.Work.Resample.auWinSlice
import Submission.Work.Resample.auSlideList
import Submission.Work.Resample.auSizes

namespace Work.Resample

open HvdH

/-- Sliding a `List.range`-indexed window by `0` or `1`.

The list `(List.range L).map (fun i => f (K + i))` is the "window" `[f K, …, f (K+L-1)]`; the
identity says that moving the base point `K` forward by `d ∈ {0,1}` is obtained by dropping the
first `d` entries and re-appending the single new entry `f (K+L)`, then cutting back to length
`L`.  (For `d ≥ 2` the two sides have different lengths, so the hypothesis `d ≤ 1` is sharp.) -/
lemma auSlideMap {β : Type*} (f : ℕ → β) (K L d : ℕ) (hd : d ≤ 1) :
    (List.range L).map (fun i => f (K + d + i))
      = (((List.range L).map (fun i => f (K + i))).drop d ++ [f (K + L)]).take L := by
  have hd' : d = 0 ∨ d = 1 := by omega
  rcases hd' with rfl | rfl
  · simp only [Nat.add_zero]
    rw [List.drop_zero, List.take_append_of_le_length (by simp),
      List.take_of_length_le (by simp)]
  · set A := (List.range L).map (fun i => f (K + i)) with hA
    have hAlen : A.length = L := by rw [hA]; simp
    have hAget : ∀ j, A[j]? = if j < L then some (f (K + j)) else none := by
      intro j
      rw [hA, List.getElem?_map]
      by_cases h : j < L
      · rw [List.getElem?_range h, if_pos h]; rfl
      · rw [List.getElem?_eq_none_iff.mpr (by simpa using h), if_neg h]; rfl
    have hLHS : ∀ j, ((List.range L).map (fun i => f (K + 1 + i)))[j]?
        = if j < L then some (f (K + 1 + j)) else none := by
      intro j
      rw [List.getElem?_map]
      by_cases h : j < L
      · rw [List.getElem?_range h, if_pos h]; rfl
      · rw [List.getElem?_eq_none_iff.mpr (by simpa using h), if_neg h]; rfl
    apply List.ext_getElem?
    intro j
    rw [hLHS j]
    by_cases hj : j < L
    · rw [if_pos hj]
      rw [List.getElem?_take, if_pos hj]
      rw [List.getElem?_append]
      have hdlen : (A.drop 1).length = L - 1 := by rw [List.length_drop, hAlen]
      rw [hdlen]
      by_cases h2 : j < L - 1
      · rw [if_pos h2]
        rw [List.getElem?_drop, hAget (1 + j)]
        rw [if_pos (by omega : 1 + j < L)]
        rw [Nat.add_assoc]
      · rw [if_neg h2]
        have hj' : j = L - 1 := by omega
        subst hj'
        rw [Nat.sub_self, List.getElem?_cons_zero]
        simp only [Option.some.injEq]
        congr 1
        omega
    · rw [if_neg hj]
      rw [List.getElem?_take, if_neg hj]

theorem auWinRec (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (u : List (ℤ × ℤ))
    (hu : u.length = s) (k : ℕ) (hk : k + 1 < t) :
    (Work.Resample.auWin p α s t u (k+1)).map HvdH.cfxVal
      = (((Work.Resample.auWin p α s t u k).map HvdH.cfxVal).drop
            (Work.Resample.auK s t (k+1) - Work.Resample.auK s t k)
          ++ [HvdH.cfxVal ((Work.Resample.auExt p α s u).getD
                (Work.Resample.auK s t k + Work.Resample.auL p α) (0,0))]).take
        (Work.Resample.auL p α) := by
  have ht : 0 < t := by omega
  have hd : auK s t (k + 1) - auK s t k ≤ 1 := auK_step_sub hst ht
  have hK : auK s t k + (auK s t (k + 1) - auK s t k) = auK s t (k + 1) := by
    have hmono : auK s t k ≤ auK s t (k + 1) := auKArith_mono s t (Nat.le_succ k)
    omega
  have hwin : ∀ m : ℕ, (auWin p α s t u m).map HvdH.cfxVal
      = (List.range (auL p α)).map (fun i =>
          HvdH.cfxVal ((auExt p α s u).getD (auK s t m + i) (0,0))) := by
    intro m
    rw [auWin, List.map_map]
    rfl
  have hkey : (fun i => HvdH.cfxVal ((auExt p α s u).getD (auK s t (k+1) + i) (0,0)))
      = (fun i => HvdH.cfxVal ((auExt p α s u).getD
          (auK s t k + (auK s t (k+1) - auK s t k) + i) (0,0))) := by
    funext i
    rw [hK]
  rw [hwin (k+1), hwin k, hkey]
  exact auSlideMap (fun j => HvdH.cfxVal ((auExt p α s u).getD j (0,0))) (auK s t k)
    (auL p α) (auK s t (k + 1) - auK s t k) hd

end Work.Resample
