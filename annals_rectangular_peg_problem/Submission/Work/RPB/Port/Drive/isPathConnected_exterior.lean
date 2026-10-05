import Mathlib

namespace Work.RPB.Port.Drive

open Set

/-- On `ℝ × ℝ` the distance to the origin computed with the product (sup) metric is
`max |x.1| |x.2|`. -/
lemma dist_prod_zero (x : ℝ × ℝ) : dist x 0 = max |x.1| |x.2| := by
  rw [Prod.dist_eq]
  simp

/-- `R ≤ |a|` holds exactly when `a` lies outside the open interval `(-R, R)`. -/
lemma le_abs_iff (R a : ℝ) : R ≤ |a| ↔ R ≤ a ∨ a ≤ -R := by
  rw [le_abs]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by linarith)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by linarith)

/-- The exterior of the closed ball of radius `R` (with respect to the sup norm on `ℝ × ℝ`) is
path connected: it is the union of the four closed half-planes `x.1 ≥ R`, `x.2 ≥ R`,
`x.1 ≤ -R`, `x.2 ≤ -R`, each of which is convex (hence path connected), glued along the
non-empty intersections containing `(R, R)`, `(R, -R)`, `(-R, R)`. -/
theorem isPathConnected_exterior (R : ℝ) (hR : 0 ≤ R) :
    IsPathConnected {x : ℝ × ℝ | R ≤ dist x 0} := by
  have hA : IsPathConnected ({x : ℝ × ℝ | R ≤ x.1}) := by
    rw [show {x : ℝ × ℝ | R ≤ x.1} = Set.Ici R ×ˢ Set.univ by ext x; simp]
    exact ((convex_Ici R).isPathConnected ⟨R, le_refl R⟩).prod
      ((convex_univ : Convex ℝ (Set.univ : Set ℝ)).isPathConnected ⟨0, mem_univ 0⟩)
  have hC : IsPathConnected ({x : ℝ × ℝ | R ≤ x.2}) := by
    rw [show {x : ℝ × ℝ | R ≤ x.2} = Set.univ ×ˢ Set.Ici R by ext x; simp]
    exact ((convex_univ : Convex ℝ (Set.univ : Set ℝ)).isPathConnected ⟨0, mem_univ 0⟩).prod
      ((convex_Ici R).isPathConnected ⟨R, le_refl R⟩)
  have hB : IsPathConnected ({x : ℝ × ℝ | x.1 ≤ -R}) := by
    rw [show {x : ℝ × ℝ | x.1 ≤ -R} = Set.Iic (-R) ×ˢ Set.univ by ext x; simp]
    exact ((convex_Iic (-R)).isPathConnected ⟨-R, le_refl (-R)⟩).prod
      ((convex_univ : Convex ℝ (Set.univ : Set ℝ)).isPathConnected ⟨0, mem_univ 0⟩)
  have hD : IsPathConnected ({x : ℝ × ℝ | x.2 ≤ -R}) := by
    rw [show {x : ℝ × ℝ | x.2 ≤ -R} = Set.univ ×ˢ Set.Iic (-R) by ext x; simp]
    exact ((convex_univ : Convex ℝ (Set.univ : Set ℝ)).isPathConnected ⟨0, mem_univ 0⟩).prod
      ((convex_Iic (-R)).isPathConnected ⟨-R, le_refl (-R)⟩)
  have hX : IsPathConnected ({x : ℝ × ℝ | R ≤ x.1} ∪ {x : ℝ × ℝ | R ≤ x.2}) :=
    hA.union hC ⟨(R, R), by simp⟩
  have hY : IsPathConnected ({x : ℝ × ℝ | x.1 ≤ -R} ∪ {x : ℝ × ℝ | x.2 ≤ -R}) :=
    hB.union hD ⟨(-R, -R), by simp⟩
  have hXY : IsPathConnected
      (({x : ℝ × ℝ | R ≤ x.1} ∪ {x : ℝ × ℝ | R ≤ x.2}) ∪
       ({x : ℝ × ℝ | x.1 ≤ -R} ∪ {x : ℝ × ℝ | x.2 ≤ -R})) :=
    hX.union hY ⟨(R, -R), by simp⟩
  have hEq : {x : ℝ × ℝ | R ≤ dist x 0} =
      ({x : ℝ × ℝ | R ≤ x.1} ∪ {x : ℝ × ℝ | R ≤ x.2}) ∪
      ({x : ℝ × ℝ | x.1 ≤ -R} ∪ {x : ℝ × ℝ | x.2 ≤ -R}) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_union, dist_prod_zero]
    rw [le_max_iff, le_abs_iff, le_abs_iff]
    tauto
  rw [hEq]
  exact hXY

end Work.RPB.Port.Drive
