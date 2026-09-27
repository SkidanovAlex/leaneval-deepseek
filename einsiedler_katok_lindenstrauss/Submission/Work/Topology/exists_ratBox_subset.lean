import Mathlib

namespace Work.Topology

/-- Every open set in the space of `3 × 3` real matrices contains a box with rational
endpoints around any of its points. -/
theorem exists_ratBox_subset (x : Matrix (Fin 3) (Fin 3) ℝ) {U : Set (Matrix (Fin 3) (Fin 3) ℝ)}
    (hU : IsOpen U) (hx : x ∈ U) :
    ∃ a b : Matrix (Fin 3) (Fin 3) ℚ,
      x ∈ {M : Matrix (Fin 3) (Fin 3) ℝ | ∀ i j, (a i j : ℝ) ≤ M i j ∧ M i j ≤ (b i j : ℝ)} ∧
      {M : Matrix (Fin 3) (Fin 3) ℝ | ∀ i j, (a i j : ℝ) ≤ M i j ∧ M i j ≤ (b i j : ℝ)} ⊆ U := by
  -- The topology on `Matrix (Fin 3) (Fin 3) ℝ` is definitionally the product topology
  -- on `Fin 3 → Fin 3 → ℝ`; work with the latter so the metric structure is available.
  let x' : Fin 3 → Fin 3 → ℝ := x
  let U' : Set (Fin 3 → Fin 3 → ℝ) := U
  have hx'' : x' ∈ U' := hx
  have hU'' : IsOpen U' := hU
  obtain ⟨ε, εpos, hε⟩ := Metric.isOpen_iff.mp hU'' x' hx''
  -- choose rational lower and upper bounds which are close to the entries of `x`
  have hper : ∀ i j, ∃ a b : ℚ, (a:ℝ) < x i j ∧ x i j < (b:ℝ) ∧ (b:ℝ) - (a:ℝ) < ε/2 := by
    intro i j
    obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show x i j - ε/4 < x i j by linarith)
    obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (show x i j < x i j + ε/4 by linarith)
    exact ⟨a, b, ha2, hb1, by linarith⟩
  choose a b hab using hper
  refine ⟨a, b, ?_, ?_⟩
  · intro i j
    exact ⟨le_of_lt (hab i j).1, le_of_lt (hab i j).2.1⟩
  · intro M hM
    let M' : Fin 3 → Fin 3 → ℝ := M
    have hM' : ∀ i j, (a i j : ℝ) ≤ M' i j ∧ M' i j ≤ (b i j : ℝ) := hM
    show M' ∈ U'
    apply hε
    rw [Metric.mem_ball]
    have hr : (0:ℝ) ≤ ε/2 := by linarith
    apply lt_of_le_of_lt _ (by linarith : ε/2 < ε)
    rw [dist_pi_le_iff hr]
    intro i
    rw [dist_pi_le_iff hr]
    intro j
    apply le_of_lt
    rw [Real.dist_eq, abs_lt]
    have ha : (a i j : ℝ) < x i j := (hab i j).1
    have hb : x i j < (b i j : ℝ) := (hab i j).2.1
    have hw : (b i j : ℝ) - (a i j : ℝ) < ε/2 := (hab i j).2.2
    constructor <;> linarith [(hM' i j).1, (hM' i j).2]

end Work.Topology
