import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Dim2

/-- A continuous function that is strictly increasing "from the left" in a one-sided local
neighbourhood of every point is strictly increasing on the whole interval.  The hypothesis is
exactly what the first-variation formula gives: at every point `σ` of the trajectory of an ascent
field the length `d(p, ·)` decreases under the backward flow for a small positive time, i.e.
`m s < m σ` for `s` just below `σ`. -/
theorem local_left_strictMono
    {m : ℝ → ℝ} (hm : Continuous m) {a b : ℝ}
    (h : ∀ σ ∈ Set.Icc a b, ∃ δ > 0, ∀ s ∈ Set.Ioo (σ - δ) σ, m s < m σ) :
    StrictMonoOn m (Set.Icc a b) := by
  -- Step 1: `m` is non-decreasing on `[a,b]`.
  -- If `x < y` and `m y < m x`, then a minimizer `c` of `m` on `[x,y]` cannot be `x`
  -- (it would give `m x ≤ m y`), so `c > x`; but then, just to the left of `c`, the values of `m`
  -- are `≥ m c`, contradicting the one-sided strict increase at `c`.
  have mono : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, x ≤ y → m x ≤ m y := by
    intro x hx y hy hxy
    by_contra hcon
    rw [not_le] at hcon
    obtain ⟨c, hc_mem, hc_min⟩ :=
      (isCompact_Icc (a := x) (b := y)).exists_isMinOn ⟨y, hxy, le_rfl⟩ hm.continuousOn
    have hcx : x ≤ c := hc_mem.1
    have hcy : c ≤ y := hc_mem.2
    have hcy' : m c ≤ m y := hc_min ⟨hxy, le_rfl⟩
    have hc_gt : x < c := by
      rcases eq_or_lt_of_le hcx with h' | h'
      · exfalso; rw [← h'] at hcy'; linarith
      · exact h'
    have hc_in : c ∈ Set.Icc a b := ⟨le_trans hx.1 hcx, le_trans hcy hy.2⟩
    obtain ⟨δ, hδpos, hδ⟩ := h c hc_in
    have hmax_lt : max x (c - δ) < c := max_lt hc_gt (by linarith)
    set s : ℝ := (max x (c - δ) + c) / 2 with hs
    have hs_lt : s < c := by rw [hs]; linarith
    have hs_gt : max x (c - δ) < s := by rw [hs]; linarith
    have hs_cond : s ∈ Set.Ioo (c - δ) c :=
      ⟨lt_of_le_of_lt (le_max_right _ _) hs_gt, hs_lt⟩
    have hs_in : s ∈ Set.Icc x y :=
      ⟨le_of_lt (lt_of_le_of_lt (le_max_left _ _) hs_gt), le_trans (le_of_lt hs_lt) hcy⟩
    have h1 : m c ≤ m s := hc_min hs_in
    have h2 : m s < m c := hδ s hs_cond
    linarith
  -- Step 2: strictness.  If `m x = m y` for `x < y`, Step 1 forces `m` to be constant `m x` on
  -- `[x,y]`; at an interior point `σ` the one-sided strict increase then fails.
  intro x hx y hy hxy
  have hle : m x ≤ m y := mono x hx y hy (le_of_lt hxy)
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exfalso
    have hconst : ∀ σ ∈ Set.Icc x y, m σ = m x := by
      intro σ hσ
      have h1 : m x ≤ m σ := mono x hx σ ⟨le_trans hx.1 hσ.1, le_trans hσ.2 hy.2⟩ hσ.1
      have h2 : m σ ≤ m y := mono σ ⟨le_trans hx.1 hσ.1, le_trans hσ.2 hy.2⟩ y hy hσ.2
      linarith
    have hσ_lt : x < (x + y) / 2 := by linarith
    have hσ_gt : (x + y) / 2 < y := by linarith
    set σ : ℝ := (x + y) / 2 with hσ
    have hσ_in : σ ∈ Set.Icc a b :=
      ⟨le_trans hx.1 (le_of_lt hσ_lt), le_trans (le_of_lt hσ_gt) hy.2⟩
    obtain ⟨δ, hδpos, hδ⟩ := h σ hσ_in
    have hmax_lt : max x (σ - δ) < σ := max_lt hσ_lt (by linarith)
    set s : ℝ := (max x (σ - δ) + σ) / 2 with hs
    have hs_lt : s < σ := by rw [hs]; linarith
    have hs_gt : max x (σ - δ) < s := by rw [hs]; linarith
    have hs_cond : s ∈ Set.Ioo (σ - δ) σ :=
      ⟨lt_of_le_of_lt (le_max_right _ _) hs_gt, hs_lt⟩
    have hs_in : s ∈ Set.Icc x y :=
      ⟨le_of_lt (lt_of_le_of_lt (le_max_left _ _) hs_gt),
       le_trans (le_of_lt hs_lt) (le_of_lt hσ_gt)⟩
    have h1 : m s = m x := hconst s hs_in
    have h2 : m σ = m x := hconst σ ⟨le_of_lt hσ_lt, le_of_lt hσ_gt⟩
    have h3 : m s < m σ := hδ s hs_cond
    linarith

end Work.Diff.Dim2
