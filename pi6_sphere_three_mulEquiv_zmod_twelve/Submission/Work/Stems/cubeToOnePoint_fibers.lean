import Mathlib
import Submission.Work.Stems.CollapseDefs

set_option synthInstance.maxHeartbeats 400000

namespace Work.Stems

noncomputable section

/-! ## Injectivity of the coordinate function `t ↦ t/√(1-t²)` on `(-1,1)`

This is the one-dimensional collapse `t = y/√(1-y²)`, which is `tan ∘ arcsin`; `tan` is strictly
monotone on `(-π/2, π/2)` and `arcsin` is strictly monotone on `[-1,1]`, so the composite is
injective on `(-1,1)`. -/

private lemma injOn_div_sqrt_one_sub_sq :
    Set.InjOn (fun x : ℝ => x / Real.sqrt (1 - x ^ 2)) (Set.Ioo (-1) 1) := by
  intro x hx y hy hxy
  rw [Set.mem_Ioo] at hx hy
  have htan : Real.tan (Real.arcsin x) = Real.tan (Real.arcsin y) := by
    rw [Real.tan_arcsin, Real.tan_arcsin]; exact hxy
  have hxa : Real.arcsin x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨Real.neg_pi_div_two_lt_arcsin.2 hx.1, Real.arcsin_lt_pi_div_two.2 hx.2⟩
  have hya : Real.arcsin y ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨Real.neg_pi_div_two_lt_arcsin.2 hy.1, Real.arcsin_lt_pi_div_two.2 hy.2⟩
  have h1 : Real.arcsin x = Real.arcsin y := Real.strictMonoOn_tan.injOn hxa hya htan
  exact (Real.arcsin_inj hx.1.le hx.2.le hy.1.le hy.2.le).1 h1

/-! ## Coordinates of an interior point lie in `(-1,1)` -/

private lemma coord_mem_Ioo {n : ℕ} {q : CubeI n} (hq : q ∉ Cube.boundary (Fin n)) (i : Fin n) :
    2 * (q i : ℝ) - 1 ∈ Set.Ioo (-1 : ℝ) 1 := by
  rw [Set.mem_Ioo]
  have h0 : (q i : ℝ) ≠ 0 := fun h => hq ⟨i, Or.inl (Subtype.ext (by simpa using h))⟩
  have h1 : (q i : ℝ) ≠ 1 := fun h => hq ⟨i, Or.inr (Subtype.ext (by simpa using h))⟩
  have hgt : 0 < (q i : ℝ) := lt_of_le_of_ne (q i).2.1 (Ne.symm h0)
  have hlt : (q i : ℝ) < 1 := lt_of_le_of_ne (q i).2.2 h1
  exact ⟨by linarith, by linarith⟩

/-! ## `cubeCoords` is injective off the boundary

Two interior points of the cube with the same image in `ℝⁿ` have equal coordinates: read off each
coordinate through the linear isometry equivalence `EuclideanSpace.equiv (Fin n) ℝ` and use the
one-dimensional injectivity above. -/

private lemma cubeCoords_injOn (n : ℕ) :
    Set.InjOn (cubeCoords n) {q : CubeI n | q ∉ Cube.boundary (Fin n)} := by
  intro q hq q' hq' h
  have hF : (fun i => (2 * (q i : ℝ) - 1) / Real.sqrt (1 - (2 * (q i : ℝ) - 1) ^ 2))
      = (fun i => (2 * (q' i : ℝ) - 1) / Real.sqrt (1 - (2 * (q' i : ℝ) - 1) ^ 2)) := by
    have hh := congrArg (EuclideanSpace.equiv (Fin n) ℝ) h
    simpa only [cubeCoords, ContinuousLinearEquiv.apply_symm_apply] using hh
  ext i
  have hi := congrFun hF i
  have hc := injOn_div_sqrt_one_sub_sq (coord_mem_Ioo hq i) (coord_mem_Ioo hq' i) hi
  linarith

/-! ## The fibres of the collapse -/

theorem cubeToOnePoint_fibers (n : ℕ) {q q' : CubeI n} (h : cubeToOnePoint n q = cubeToOnePoint n q') :
    q = q' ∨ (q ∈ Cube.boundary (Fin n) ∧ q' ∈ Cube.boundary (Fin n)) := by
  by_cases hq : q ∈ Cube.boundary (Fin n)
  · by_cases hq' : q' ∈ Cube.boundary (Fin n)
    · exact Or.inr ⟨hq, hq'⟩
    · exfalso
      have h₁ : cubeToOnePoint n q = OnePoint.infty := by
        simp only [cubeToOnePoint, if_pos hq]
      have h₂ : cubeToOnePoint n q' = (cubeCoords n q' : OnePoint _) := by
        simp only [cubeToOnePoint, if_neg hq']
      rw [h₁, h₂] at h
      exact OnePoint.infty_ne_coe (cubeCoords n q') h
  · by_cases hq' : q' ∈ Cube.boundary (Fin n)
    · exfalso
      have h₁ : cubeToOnePoint n q = (cubeCoords n q : OnePoint _) := by
        simp only [cubeToOnePoint, if_neg hq]
      have h₂ : cubeToOnePoint n q' = OnePoint.infty := by
        simp only [cubeToOnePoint, if_pos hq']
      rw [h₁, h₂] at h
      exact OnePoint.coe_ne_infty (cubeCoords n q) h
    · left
      have h₁ : cubeToOnePoint n q = (cubeCoords n q : OnePoint _) := by
        simp only [cubeToOnePoint, if_neg hq]
      have h₂ : cubeToOnePoint n q' = (cubeCoords n q' : OnePoint _) := by
        simp only [cubeToOnePoint, if_neg hq']
      rw [h₁, h₂] at h
      exact cubeCoords_injOn n hq hq' (OnePoint.coe_injective h)

end

end Work.Stems
