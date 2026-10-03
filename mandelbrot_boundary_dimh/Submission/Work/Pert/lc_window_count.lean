import Mathlib
import Submission.Work.Pert.lc_step_sep

namespace Work.Pert

/-- Counting lemma for a decreasing ladder in a window.

Let `H : ℕ → ℝ` be nonnegative on `{0, …, n}` and drop by at least `15/16` at every step
`j < n`.  Then, for any `F ⊆ {0, …, n}` and any `L ≥ 0`, the number of indices `j ∈ F`
with `H j ≤ L` is at most `16 L / 15 + 1`.

Indeed, telescoping (`lc_step_sep`) with `H n ≥ 0` gives `(15/16) * (n - j) ≤ H j` for `j ≤ n`,
so `H j ≤ L` forces `n - j ≤ 16 L / 15`; the indices with `H j ≤ L` therefore all lie in the
integer window `[n - ⌊16 L / 15⌋, n]`, which has at most `⌊16 L / 15⌋ + 1 ≤ 16 L / 15 + 1`
elements. -/
theorem lc_window_count {H : ℕ → ℝ} {n : ℕ} {F : Finset ℕ}
    (hpos : ∀ j, j ≤ n → 0 ≤ H j)
    (hstep : ∀ j, j < n → H (j + 1) ≤ H j - 15 / 16)
    (hF : ∀ j ∈ F, j ≤ n) {L : ℝ} (hL : 0 ≤ L) :
    ((F.filter (fun j => H j ≤ L)).card : ℝ) ≤ 16 * L / 15 + 1 := by
  classical
  set m : ℕ := Nat.floor (16 * L / 15) with hm
  -- Every good index is within `16 L / 15` of `n`.
  have hmem : ∀ j ∈ F.filter (fun j => H j ≤ L), (n - j : ℕ) ≤ m := by
    intro j hj
    rw [Finset.mem_filter] at hj
    obtain ⟨hjF, hjL⟩ := hj
    have hjn : j ≤ n := hF j hjF
    have hsep := lc_step_sep hstep j n hjn le_rfl
    have hposn : 0 ≤ H n := hpos n le_rfl
    have hge : (15 / 16 : ℝ) * ((n - j : ℕ) : ℝ) ≤ H j := by linarith
    have hLbound : ((n - j : ℕ) : ℝ) ≤ 16 * L / 15 := by linarith
    rw [hm]
    exact Nat.le_floor hLbound
  -- Hence the good indices lie in an interval of length at most `m + 1`.
  have hcard : (F.filter (fun j => H j ≤ L)).card ≤ m + 1 := by
    have hsub : F.filter (fun j => H j ≤ L) ⊆ Finset.Icc (n - m) n := by
      intro j hj
      rw [Finset.mem_filter] at hj
      obtain ⟨hjF, hjL⟩ := hj
      have hjn : j ≤ n := hF j hjF
      have hle : (n - j : ℕ) ≤ m := hmem j (Finset.mem_filter.mpr ⟨hjF, hjL⟩)
      rw [Finset.mem_Icc]
      omega
    calc (F.filter (fun j => H j ≤ L)).card
        ≤ (Finset.Icc (n - m) n).card := Finset.card_le_card hsub
      _ = n + 1 - (n - m) := Nat.card_Icc (n - m) n
      _ ≤ m + 1 := by omega
  have hmle : (m : ℝ) ≤ 16 * L / 15 := by
    rw [hm]
    exact Nat.floor_le (by linarith)
  have hcast : ((F.filter (fun j => H j ≤ L)).card : ℝ) ≤ (m : ℝ) + 1 := by
    exact_mod_cast hcard
  linarith

end Work.Pert
