import Mathlib
import Submission.Work.WilG4a.f1affine1_defs

namespace Work.WilG4a

/-- A nonempty open interval is nondegenerate. -/
theorem Ioo_nonempty_lt {a b : ℝ} (h : (Set.Ioo a b).Nonempty) : a < b := by
  obtain ⟨x, hx⟩ := h
  exact lt_trans hx.1 hx.2

/-- An open interval contained in another one, and nondegenerate, is bounded by it. -/
theorem bounds_of_Ioo_subset_Ioo {a b c d : ℝ} (h : Set.Ioo a b ⊆ Set.Ioo c d) (hab : a < b) :
    c ≤ a ∧ b ≤ d := by
  constructor
  · by_contra hca
    rw [not_le] at hca
    have hlt : a < min b c := lt_min hab hca
    have h1 : a < (a + min b c) / 2 := by linarith
    have h2 : (a + min b c) / 2 < b := by linarith [min_le_left b c]
    have h3 : (a + min b c) / 2 < c := by linarith [min_le_right b c]
    have h4 : c < (a + min b c) / 2 := (h ⟨h1, h2⟩).1
    linarith
  · by_contra hdb
    rw [not_le] at hdb
    have hlt : max a d < b := max_lt hab hdb
    have h1 : a < (max a d + b) / 2 := by linarith [le_max_left a d]
    have h2 : (max a d + b) / 2 < b := by linarith
    have h3 : d < (max a d + b) / 2 := by linarith [le_max_right a d]
    have h4 : (max a d + b) / 2 < d := (h ⟨h1, h2⟩).2
    linarith

lemma fibre_endpoints_bounds {p : ℕ} {κ : Set (Fin (p + 1) → ℝ)} {lo hi : (Fin p → ℝ) → ℝ} {l : Fin p → ℝ} (hstrip : κ ⊆ strip p) (hne : ∃ x : ℝ, Fin.snoc l x ∈ κ) (hfib : fibre κ l = Set.Ioo (lo l) (hi l)) : lo l < hi l ∧ 0 ≤ lo l ∧ hi l ≤ 1 ∧ Set.Ioo (lo l) (hi l) ⊆ I := by
  -- the fibre sits inside the strip, hence inside `I = (0,1)`
  have hsub : fibre κ l ⊆ I := by
    intro y hy
    have hy' : Fin.snoc l y ∈ strip p := hstrip hy
    rwa [strip_mem_iff_snoc] at hy'
  -- the fibre is nonempty, hence so is the interval `(lo l, hi l)`
  have hne' : (fibre κ l).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨x, hx⟩
  have hneIoo : (Set.Ioo (lo l) (hi l)).Nonempty := by
    rw [← hfib]; exact hne'
  have hlt : lo l < hi l := Ioo_nonempty_lt hneIoo
  have hsubIoo : Set.Ioo (lo l) (hi l) ⊆ Set.Ioo 0 1 := by
    rw [← hfib]; exact hsub
  have hb := bounds_of_Ioo_subset_Ioo hsubIoo hlt
  exact ⟨hlt, hb.1, hb.2, hsubIoo⟩

end Work.WilG4a
