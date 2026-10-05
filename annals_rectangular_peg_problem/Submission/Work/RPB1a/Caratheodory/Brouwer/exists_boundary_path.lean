import Mathlib

namespace Work.RPB1a.Caratheodory.Brouwer

/-- In the vertical-side case, walking straight to the corner `{re := w.re, im := c}` at the
bottom (`c = -2`, when `w.im < 0`) or the top (`c = 2`, when `w.im > 0`) realises the required
path: the segment keeps the real part `w.re = ±1` and its imaginary part is a strictly signed
convex combination of `w.im` and `c`, hence stays in `[-2,2]` and never vanishes. -/
private lemma exists_path_vertical (w : ℂ) {c : ℝ}
    (hsgn : (c = -2 ∧ w.im < 0) ∨ (c = 2 ∧ 0 < w.im))
    (hwre1 : -1 ≤ w.re) (hwre2 : w.re ≤ 1) (hwim1 : -2 ≤ w.im) (hwim2 : w.im ≤ 2)
    (hwre : w.re = -1 ∨ w.re = 1) :
    ∃ γ : Path w ({ re := w.re, im := c } : ℂ),
      (∀ t, -1 ≤ (γ t).re ∧ (γ t).re ≤ 1 ∧ -2 ≤ (γ t).im ∧ (γ t).im ≤ 2) ∧
      (∀ t, (γ t).re = -1 ∨ (γ t).re = 1 ∨ (γ t).im = -2 ∨ (γ t).im = 2) ∧
      (∀ t, γ t ≠ -1 ∧ γ t ≠ 1) := by
  have hre : ∀ t : Set.Icc (0:ℝ) 1,
      (Path.segment w ({ re := w.re, im := c } : ℂ) t).re = w.re :=
    fun t => by rw [Path.segment_apply, AffineMap.lineMap_apply_module]; simp; ring
  have him : ∀ t : Set.Icc (0:ℝ) 1,
      (Path.segment w ({ re := w.re, im := c } : ℂ) t).im
        = (1 - (t:ℝ)) * w.im + (t:ℝ) * c :=
    fun t => by rw [Path.segment_apply, AffineMap.lineMap_apply_module]; simp
  refine ⟨Path.segment w ({ re := w.re, im := c } : ℂ), ?_, ?_, ?_⟩
  · intro t
    have ht0 : (0:ℝ) ≤ (t:ℝ) := t.2.1
    have ht1 : (t:ℝ) ≤ 1 := t.2.2
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hre t]; exact hwre1
    · rw [hre t]; exact hwre2
    · rw [him t]
      rcases hsgn with ⟨rfl, hlt⟩ | ⟨rfl, hgt⟩
      · nlinarith
      · nlinarith
    · rw [him t]
      rcases hsgn with ⟨rfl, hlt⟩ | ⟨rfl, hgt⟩
      · nlinarith
      · nlinarith
  · intro t
    rcases hwre with h | h
    · exact Or.inl (by rw [hre t, h])
    · exact Or.inr (Or.inl (by rw [hre t, h]))
  · intro t
    have ht0 : (0:ℝ) ≤ (t:ℝ) := t.2.1
    have ht1 : (t:ℝ) ≤ 1 := t.2.2
    have hne : (Path.segment w ({ re := w.re, im := c } : ℂ) t).im < 0 ∨
        0 < (Path.segment w ({ re := w.re, im := c } : ℂ) t).im := by
      rw [him t]
      rcases hsgn with ⟨rfl, hlt⟩ | ⟨rfl, hgt⟩
      · left; nlinarith
      · right; nlinarith
    have key : ∀ (h0 : (Path.segment w ({ re := w.re, im := c } : ℂ) t).im ≠ 0),
        Path.segment w ({ re := w.re, im := c } : ℂ) t ≠ -1 ∧
        Path.segment w ({ re := w.re, im := c } : ℂ) t ≠ 1 := by
      intro h0
      constructor
      · intro hc; apply h0; rw [hc]; simp
      · intro hc; apply h0; rw [hc]; simp
    rcases hne with hlt | hgt
    · exact key (by intro h0; linarith)
    · exact key (by intro h0; linarith)

/-- **Reaching the top or the bottom side of the rectangle from a boundary point.**

Let `w` be a point of the rectangle `[-1,1] × [-2,2]` lying on its boundary (`w.re = ±1` or
`w.im = ±2`) and different from the two points `-1`, `1`.  Then there is a point `z` of the boundary
with `z.im = -2` or `z.im = 2` (i.e. on the bottom or the top side) and a path `γ` from `w` to `z`
which stays on the boundary of the rectangle and avoids the two points `-1` and `1`.

Concretely, if `w` already has `w.im = ±2` take `z = w`; otherwise `w` lies on one of the two
vertical sides `re = ±1` with `w.im ∉ {0}` (because `w ≠ ±1`), and one takes `z` to be the corner of
the rectangle directly below `w` when `w.im < 0` (giving `z.im = -2`) or directly above `w` when
`w.im > 0` (giving `z.im = 2`), with `γ` the straight segment from `w` to `z`.  That segment lies on
the vertical side, hence avoids `-1` and `1` (the only points of the vertical sides with `im = 0`). -/
theorem exists_boundary_path (w : ℂ)
    (hwE : -1 ≤ w.re ∧ w.re ≤ 1 ∧ -2 ≤ w.im ∧ w.im ≤ 2)
    (hwbd : w.re = -1 ∨ w.re = 1 ∨ w.im = -2 ∨ w.im = 2)
    (hw1 : w ≠ -1) (hw2 : w ≠ 1) :
    ∃ z : ℂ, (z.im = -2 ∨ z.im = 2) ∧ ∃ γ : Path w z,
      (∀ t, -1 ≤ (γ t).re ∧ (γ t).re ≤ 1 ∧ -2 ≤ (γ t).im ∧ (γ t).im ≤ 2) ∧
      (∀ t, (γ t).re = -1 ∨ (γ t).re = 1 ∨ (γ t).im = -2 ∨ (γ t).im = 2) ∧
      (∀ t, γ t ≠ -1 ∧ γ t ≠ 1) := by
  obtain ⟨hwre1, hwre2, hwim1, hwim2⟩ := hwE
  by_cases h2 : w.im = 2
  · exact ⟨w, Or.inr h2, Path.refl w, (fun t => ⟨hwre1, hwre2, hwim1, hwim2⟩),
      (fun _ => hwbd), fun _ => ⟨hw1, hw2⟩⟩
  by_cases hm2 : w.im = -2
  · exact ⟨w, Or.inl hm2, Path.refl w, (fun t => ⟨hwre1, hwre2, hwim1, hwim2⟩),
      (fun _ => hwbd), fun _ => ⟨hw1, hw2⟩⟩
  have hwre : w.re = -1 ∨ w.re = 1 := by
    rcases hwbd with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hm2
    · exact absurd h h2
  have hwimne : w.im ≠ 0 := by
    intro h0
    rcases hwre with h | h
    · exact hw1 (by apply Complex.ext <;> simp [h, h0])
    · exact hw2 (by apply Complex.ext <;> simp [h, h0])
  rcases lt_or_gt_of_ne hwimne with hneg | hpos
  · obtain ⟨γ, h1, h2', h3⟩ :=
      exists_path_vertical w (c := -2) (Or.inl ⟨rfl, hneg⟩) hwre1 hwre2 hwim1 hwim2 hwre
    exact ⟨{ re := w.re, im := -2 }, Or.inl rfl, γ, h1, h2', h3⟩
  · obtain ⟨γ, h1, h2', h3⟩ :=
      exists_path_vertical w (c := 2) (Or.inr ⟨rfl, hpos⟩) hwre1 hwre2 hwim1 hwim2 hwre
    exact ⟨{ re := w.re, im := 2 }, Or.inr rfl, γ, h1, h2', h3⟩

end Work.RPB1a.Caratheodory.Brouwer
