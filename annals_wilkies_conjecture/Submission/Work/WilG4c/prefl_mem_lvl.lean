import Mathlib
import Submission.Work.WilG4c.CellParamDefs

namespace Work.WilG4c

/-!
  `prefl m hm z` is the prefix (first `p+m` coordinates) of `z : ℝ^{p+N}`, and `lvl p N κ m` is
  the projection of `κ` to the first `p+m` coordinates, defined by the downward recursion
  `lvl p N κ m = projLast (lvl p N κ (m+1))` for `m < N`.  The two statements `prefl m hm z`
  and `lvl p N κ m` are matched by the recursion: the prefix at level `m+1` is the prefix at
  level `m` with the next coordinate appended (`prefl_succ`), which is exactly the fibre
  coordinate produced by `projLast`.  We perform the downward induction on `N - m`.
-/

/-- `prefl` does not depend on its proof argument. -/
private lemma prefl_congr {p N m : ℕ} (h1 h2 : m ≤ N) (z : Fin (p+N) → ℝ) :
    prefl m h1 z = prefl m h2 z := by
  funext i
  exact congrArg z (Fin.ext rfl)

/-- At level `N`, the prefix is the point itself. -/
private lemma prefl_eq_self {p N : ℕ} (hm : N ≤ N) (z : Fin (p+N) → ℝ) :
    prefl N hm z = z := by
  funext i
  exact congrArg z (Fin.ext rfl)

/-- The level-`(m+1)` prefix is the level-`m` prefix with the coordinate `p+m` appended. -/
private lemma snoc_prefl {p N m : ℕ} (h : m + 1 ≤ N) (hm : m ≤ N) (z : Fin (p+N) → ℝ) :
    Fin.snoc (prefl m hm z) (z ⟨p+m, by omega⟩) = prefl (m+1) h z := by
  rw [prefl_succ m h z, Fin.snoc_inj]
  exact ⟨prefl_congr hm (by omega) z, congrArg z (Fin.ext rfl)⟩

theorem prefl_mem_lvl (p N : ℕ) (κ : Set (Fin (p+N) → ℝ)) (m : ℕ) (hm : m ≤ N)
    (z : Fin (p+N) → ℝ) (hz : z ∈ κ) : Work.WilG4c.prefl m hm z ∈ Work.WilG4c.lvl p N κ m := by
  have key : ∀ j, ∀ m, N - m = j → ∀ (hm : m ≤ N) (z : Fin (p+N) → ℝ),
      z ∈ κ → prefl m hm z ∈ lvl p N κ m := by
    intro j
    induction j using Nat.strongRecOn with
    | ind j ih =>
      intro m hmj hm z hz
      rcases lt_or_ge m N with hlt | hge
      · -- `m < N`: `lvl` at `m` is the projection of `lvl` at `m+1`; feed it the prefix.
        have hm1 : m + 1 ≤ N := hlt
        have hdecr : N - (m+1) < j := by omega
        have h1 : prefl (m+1) hm1 z ∈ lvl p N κ (m+1) :=
          ih (N - (m+1)) hdecr (m+1) rfl hm1 z hz
        rw [lvl_succ κ hlt]
        refine ⟨z ⟨p+m, by omega⟩, ?_⟩
        have heq : Fin.snoc (prefl m hm z) (z ⟨p+m, by omega⟩) = prefl (m+1) hm1 z :=
          snoc_prefl hm1 hm z
        rw [heq]
        exact h1
      · -- `m ≥ N` together with `m ≤ N` forces `m = N`, where `lvl` is `κ` itself.
        have hmN : m = N := le_antisymm hm hge
        subst hmN
        rw [lvl_self]
        rw [prefl_eq_self]
        exact hz
  exact key (N-m) m rfl hm z hz

end Work.WilG4c
