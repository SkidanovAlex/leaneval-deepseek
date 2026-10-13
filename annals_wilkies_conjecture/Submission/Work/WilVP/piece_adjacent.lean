import Mathlib

namespace Work.WilVP

/-- Adjacent points of a finite set `P` around a point `x ∉ P`: the nearest point below and the
nearest point above, which bracket `x`, exclude every other point of `P` from the open interval,
give `min (x - p₁) (p₂ - x)` as a lower bound for all distances `|x - p|`, `p ∈ P`, and attain it.
(`p₁ := sSup {p ∈ P | p < x}`, `p₂ := sInf {p ∈ P | x < p}` — finite nonempty sets; `x ∉ P` is
needed for the "no point between" clause.) -/
theorem piece_adjacent {P : Set ℝ} (hP : P.Finite) {x : ℝ} (hx : x ∉ P)
    (hlo : ∃ p ∈ P, p < x) (hhi : ∃ p ∈ P, x < p) :
    ∃ p₁ p₂ : ℝ, p₁ ∈ P ∧ p₂ ∈ P ∧ p₁ < x ∧ x < p₂ ∧
      (∀ y ∈ P, p₁ < y → y < p₂ → False) ∧
      (∀ p ∈ P, min (x - p₁) (p₂ - x) ≤ |x - p|) ∧
      (min (x - p₁) (p₂ - x) = |x - p₁| ∨ min (x - p₁) (p₂ - x) = |x - p₂|) := by
  classical
  obtain ⟨a, haP, hax⟩ := hlo
  obtain ⟨b, hbP, hxb⟩ := hhi
  -- the finite set of points of `P` lying below (resp. above) `x`
  let S : Finset ℝ := hP.toFinset
  have hmem : ∀ y, y ∈ S ↔ y ∈ P := by
    intro y
    change y ∈ hP.toFinset ↔ y ∈ P
    exact hP.mem_toFinset
  have hne1 : (S.filter (fun q => q < x)).Nonempty :=
    ⟨a, Finset.mem_filter.mpr ⟨(hmem a).mpr haP, hax⟩⟩
  have hne2 : (S.filter (fun q => x < q)).Nonempty :=
    ⟨b, Finset.mem_filter.mpr ⟨(hmem b).mpr hbP, hxb⟩⟩
  -- the nearest point below `x` and the nearest point above `x`
  set p₁ : ℝ := (S.filter (fun q => q < x)).max' hne1 with hp₁
  set p₂ : ℝ := (S.filter (fun q => x < q)).min' hne2 with hp₂
  have hp₁mem : p₁ ∈ S.filter (fun q => q < x) := by rw [hp₁]; exact Finset.max'_mem _ _
  have hp₂mem : p₂ ∈ S.filter (fun q => x < q) := by rw [hp₂]; exact Finset.min'_mem _ _
  have hP₁ : p₁ ∈ P := (hmem p₁).mp (Finset.mem_filter.mp hp₁mem).1
  have hp₁x : p₁ < x := (Finset.mem_filter.mp hp₁mem).2
  have hP₂ : p₂ ∈ P := (hmem p₂).mp (Finset.mem_filter.mp hp₂mem).1
  have hxp₂ : x < p₂ := (Finset.mem_filter.mp hp₂mem).2
  -- `p₁` dominates every point of `P` below `x`; `p₂` is dominated by every point above `x`
  have hmax_eq : ∀ y ∈ S.filter (fun q => q < x), y ≤ p₁ := by
    intro y hy
    rw [hp₁]
    exact Finset.le_max' _ y hy
  have hmin_eq : ∀ y ∈ S.filter (fun q => x < q), p₂ ≤ y := by
    intro y hy
    rw [hp₂]
    exact Finset.min'_le _ y hy
  refine ⟨p₁, p₂, hP₁, hP₂, hp₁x, hxp₂, ?_, ?_, ?_⟩
  · -- nothing of `P` lies strictly between `p₁` and `p₂`
    intro y hyP hy₁ hy₂
    have hyx : y ≠ x := fun h => hx (h ▸ hyP)
    rcases lt_trichotomy y x with h | h | h
    · exact absurd (hmax_eq y (Finset.mem_filter.mpr ⟨(hmem y).mpr hyP, h⟩)) (by linarith)
    · exact hyx h
    · exact absurd (hmin_eq y (Finset.mem_filter.mpr ⟨(hmem y).mpr hyP, h⟩)) (by linarith)
  · -- the bound `min (x - p₁) (p₂ - x)` for every distance
    intro p hpP
    have hpx : p ≠ x := fun h => hx (h ▸ hpP)
    rcases lt_trichotomy p x with h | h | h
    · have hle : p ≤ p₁ := hmax_eq p (Finset.mem_filter.mpr ⟨(hmem p).mpr hpP, h⟩)
      have hgcd : |x - p| = x - p := abs_of_pos (by linarith)
      calc min (x - p₁) (p₂ - x) ≤ x - p₁ := min_le_left _ _
        _ ≤ x - p := by linarith
        _ = |x - p| := hgcd.symm
    · exact absurd h hpx
    · have hle : p₂ ≤ p := hmin_eq p (Finset.mem_filter.mpr ⟨(hmem p).mpr hpP, h⟩)
      have hgcd : |x - p| = p - x := by
        rw [abs_of_neg (by linarith)]
        ring
      calc min (x - p₁) (p₂ - x) ≤ p₂ - x := min_le_right _ _
        _ ≤ p - x := by linarith
        _ = |x - p| := hgcd.symm
  · -- the bound is attained at `p₁` or at `p₂`
    have h₁ : |x - p₁| = x - p₁ := abs_of_pos (by linarith)
    have h₂ : |x - p₂| = p₂ - x := by
      rw [abs_of_neg (by linarith)]
      ring
    rw [h₁, h₂]
    rcases le_total (x - p₁) (p₂ - x) with h | h
    · exact Or.inl (min_eq_left h)
    · exact Or.inr (min_eq_right h)

end Work.WilVP
