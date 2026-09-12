import Mathlib
import Submission.DirCycle
import Submission.DirSet

/-!
# Window separation for the direction list (isolated geometry lemma)

For the E2b cell instantiation (`Submission/E2bCells.lean`) one needs: if the
spike directions `(dirList S).get i` (a strictly increasing list of the
`dirSet S` directions, `Submission.DirCycle`) satisfy that every consecutive
gap exceeds `2δ` (this is exactly the output shape of
`Submission.E2bParam.exists_delta`), then the closed `δ`-window around the
direction `i` contains *no other direction*:

    dirList_window_separated :  θ ∈ dirSet S, θ ∈ [x_i − δ, x_i + δ]
                                ⟹ θ = x_i .

PROOF GUIDE (use the verified machinery; all index arithmetic is routine
`omega`):
1. `θ ∈ dirSet S` means `θ = (dirList S).get k` for some index `k`
   (`Submission.DirCycle.dirList_mem_iff` + `List.mem_iff_get`).
2. Suppose `k ≠ i`.  Then `k < i` or `i < k` (natural values).
   - Case `k < i`: the directions are strictly increasing
     (`dirList_get_mono`/`dirList_get_strict`), `x_0 < … < x_i`, and every
     consecutive gap exceeds `2δ`.  If `i = 0` this case is impossible.  If
     `i ≥ 1`, then `x_{i−1} < x_i − 2δ < x_i − δ ≤ θ` (gap bound at
     `j := i−1`) while `θ < x_i`, so `θ` lies strictly between the
     consecutive entries `x_{i−1}` and `x_i`, contradicting
     `Submission.DirCycle.no_dir_between_get S ⟨i−1, _⟩` (no direction
     strictly between consecutive entries).
   - Case `i < k`: if `i` is the last index this is impossible; otherwise
     `θ > x_i` while `x_{i+1} > x_i + 2δ > x_i + δ ≥ θ` (gap bound at
     `j := i`), so `θ` lies strictly between `x_i` and `x_{i+1}`,
     contradicting `no_dir_between_get S i`.
3. Conclude `k = i` (indices equal ⟹ entries equal).

NOTES: `hsep` is stated in exactly the shape produced by
`Submission.E2bParam.exists_delta` (consecutive-gap bounds with the awkward
`Nat.lt_trans (Nat.lt_succ_self j)` index proofs); you may restate it as a
private lemma with a cleaner `Fin`-free hypothesis if you prefer, as long as
the public statement below keeps this shape.  All entries of `dirList S`
lie in `(-π, π]` (`Submission.SpineGaps.dirList_get_mem_Ioc`).  Do not
change the public statement.
-/

noncomputable section
open scoped Real
namespace Submission.SepLemma

open Submission.DirCycle
open Submission.DirSet

/-- The closed `δ`-window around a direction contains no other direction
(consecutive dirList gaps all exceed `2δ`). -/
lemma dirList_window_separated {S : Finset ℂ} {δ : ℝ}
    (hsep : ∀ (j : ℕ) (hj : j + 1 < (dirList S).length),
      (dirList S).get ⟨j + 1, hj⟩ -
        (dirList S).get ⟨j, Nat.lt_trans (Nat.lt_succ_self j) hj⟩ > 2 * δ)
    (i : Fin (dirList S).length) {θ : ℝ} (hθ : θ ∈ dirSet S)
    (hwin : θ ∈ Set.Icc ((dirList S).get i - δ) ((dirList S).get i + δ)) :
    θ = (dirList S).get i := by
  classical
  -- `θ` is a dirList entry: `θ = (dirList S).get k` for some index `k`.
  rcases List.mem_iff_get.mp ((dirList_mem_iff S θ).mpr hθ) with ⟨k, rfl⟩
  -- Nonemptiness of the window forces `δ ≥ 0` (used to compare `2δ ≥ δ`).
  have hδ0 : 0 ≤ δ := by
    have hlo : (dirList S).get i - δ ≤ (dirList S).get k := hwin.1
    have hhi : (dirList S).get k ≤ (dirList S).get i + δ := hwin.2
    linarith
  -- Show the indices agree.
  have hk_eq : k = i := by
    apply Fin.ext
    by_contra hne
    have htri := Nat.lt_trichotomy k.val i.val
    rcases htri with hlt | heq | hgt
    · -- Case `k.val < i.val`: `θ` lies strictly between `x_{i−1}` and `x_i`.
      exfalso
      have hi1 : 1 ≤ i.val := by omega
      let p : Fin (dirList S).length := ⟨i.val - 1, by omega⟩
      have hp_succ : p.val + 1 = i.val := by
        dsimp [p]
        omega
      have hp_succ_lt : p.val + 1 < (dirList S).length := by
        rw [hp_succ]
        exact i.isLt
      -- Gap bound at `j := p.val`: `x_i − x_{i−1} > 2δ`.
      have hg_raw := hsep p.val hp_succ_lt
      have hf1 : (⟨p.val + 1, hp_succ_lt⟩ : Fin (dirList S).length) = i := by
        apply Fin.ext
        exact hp_succ
      have hf2 : (⟨p.val, Nat.lt_trans (Nat.lt_succ_self p.val) hp_succ_lt⟩ :
            Fin (dirList S).length) = p := by
        apply Fin.ext
        rfl
      rw [hf1, hf2] at hg_raw
      -- `x_{i−1} < θ` from the gap plus the window, and `θ < x_i` by sortedness.
      have hp_lt_k : (dirList S).get p < (dirList S).get k := by
        have hlo : (dirList S).get i - δ ≤ (dirList S).get k := hwin.1
        linarith
      have hk_lt_i : (dirList S).get k < (dirList S).get i := by
        exact dirList_get_strict S (i := k) (j := i) hlt
      -- No direction lies strictly between consecutive entries.
      have hno := no_dir_between_get S p hp_succ_lt ((dirList S).get k) hθ
      have hconj : (dirList S).get p < (dirList S).get k ∧
          (dirList S).get k < (dirList S).get ⟨p.val + 1, hp_succ_lt⟩ := by
        constructor
        · exact hp_lt_k
        · simpa [hf1] using hk_lt_i
      exact hno hconj
    · exact False.elim (hne heq)
    · -- Case `i.val < k.val`: `θ` lies strictly between `x_i` and `x_{i+1}`.
      exfalso
      have hq_lt : i.val + 1 < (dirList S).length := by
        have hklt : k.val < (dirList S).length := k.isLt
        omega
      -- Gap bound at `j := i.val`: `x_{i+1} − x_i > 2δ`.
      have hg_raw := hsep i.val hq_lt
      have hf2 : (⟨i.val, Nat.lt_trans (Nat.lt_succ_self i.val) hq_lt⟩ :
            Fin (dirList S).length) = i := by
        apply Fin.ext
        rfl
      rw [hf2] at hg_raw
      -- `θ < x_{i+1}` from the gap plus the window, and `x_i < θ` by sortedness.
      have hk_lt_q : (dirList S).get k < (dirList S).get ⟨i.val + 1, hq_lt⟩ := by
        have hhi : (dirList S).get k ≤ (dirList S).get i + δ := hwin.2
        linarith
      have hi_lt_k : (dirList S).get i < (dirList S).get k := by
        exact dirList_get_strict S (i := i) (j := k) hgt
      -- No direction lies strictly between consecutive entries.
      have hno := no_dir_between_get S i hq_lt ((dirList S).get k) hθ
      exact hno ⟨hi_lt_k, hk_lt_q⟩
  subst hk_eq
  rfl

end Submission.SepLemma

end
