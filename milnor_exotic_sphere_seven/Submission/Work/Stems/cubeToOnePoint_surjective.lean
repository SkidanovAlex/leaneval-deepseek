import Mathlib
import Submission.Work.Stems.CollapseDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Surjectivity of the collapse map `Iⁿ → Iⁿ/∂Iⁿ ≅ Sⁿ`

This file proves that the explicit collapse map `cubeToOnePoint n : Iⁿ → OnePoint ℝⁿ`
of `Submission.Work.Stems.exists_collapsingMap` is surjective for `n ≥ 1`.

The map sends the boundary `∂Iⁿ` of the cube to `∞` and the interior to `ℝⁿ` by the
coordinate formula `q ↦ (y_i/√(1-y_i²))_i`, `y_i = 2q_i - 1`. Its inverse on `ℝⁿ` is
given coordinatewise by `x_i ↦ (u_i + 1)/2` with `u_i = x_i/√(1 + x_i²) ∈ (-1,1)`;
the corresponding point of the cube is automatically in the interior, while `∞` is
the image of the boundary point `0` (here `n ≥ 1`).
-/

open scoped Topology unitInterval OnePoint

namespace Work.Stems

noncomputable section

/-- The auxiliary real map `t ↦ t/√(1+t²)`, the inverse of `t ↦ t/√(1-t²)`; it maps `ℝ`
into the open interval `(-1,1)`. -/
private def rInv (t : ℝ) : ℝ := t / Real.sqrt (1 + t^2)

private lemma rInv_abs_lt_one (t : ℝ) : |rInv t| < 1 := by
  have hpos : 0 < 1 + t^2 := by positivity
  have hs : 0 < Real.sqrt (1 + t^2) := Real.sqrt_pos.mpr hpos
  have ht : |t| < Real.sqrt (1 + t^2) := by
    rw [Real.lt_sqrt (abs_nonneg t), sq_abs]; linarith
  rw [rInv, abs_div, abs_of_pos hs, div_lt_one hs]
  exact ht

/-- `(rInv t + 1)/2` always lies in `[0,1]`, so it defines a point of the cube. -/
private lemma rInv_mem_Icc (t : ℝ) : (rInv t + 1) / 2 ∈ Set.Icc (0 : ℝ) 1 := by
  have h := abs_lt.mp (rInv_abs_lt_one t)
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- `(rInv t + 1)/2` lies in the open interval `(0,1)`: the corresponding cube point is
interior, i.e. off the boundary. -/
private lemma rInv_interior (t : ℝ) : 0 < (rInv t + 1) / 2 ∧ (rInv t + 1) / 2 < 1 := by
  have h := abs_lt.mp (rInv_abs_lt_one t)
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- The key cancellation: the coordinate formula of `cubeCoords` is inverted by
`t ↦ (rInv t + 1)/2`. -/
private lemma cubeCoords_rInv (t : ℝ) :
    (2 * ((rInv t + 1) / 2) - 1) /
      Real.sqrt (1 - (2 * ((rInv t + 1) / 2) - 1) ^ 2) = t := by
  unfold rInv
  set s := Real.sqrt (1 + t^2) with hsdef
  have hpos : 0 < 1 + t^2 := by positivity
  have hs : 0 < s := Real.sqrt_pos.mpr hpos
  have hs2 : s ^ 2 = 1 + t^2 := Real.sq_sqrt (le_of_lt hpos)
  have hsne : s ≠ 0 := ne_of_gt hs
  set r := t / s with hrdef
  have hsmall : 1 - r ^ 2 = (1 / s) ^ 2 := by
    rw [hrdef]; field_simp; nlinarith [hs2]
  have hsqrt : Real.sqrt (1 - r ^ 2) = 1 / s := by
    rw [hsmall, Real.sqrt_sq (by positivity)]
  have hthis : 2 * ((t / s + 1) / 2) - 1 = r := by rw [hrdef]; ring
  rw [hthis, hsqrt]
  field_simp
  rw [hrdef]; field_simp

/-- The coordinates of `cubeCoords` are recovered by `rInv`. -/
private lemma cubeCoords_apply (n : ℕ) (q : CubeI n) (i : Fin n) :
    EuclideanSpace.equiv (Fin n) ℝ (cubeCoords n q) i =
      (2 * (q i : ℝ) - 1) / Real.sqrt (1 - (2 * (q i : ℝ) - 1) ^ 2) := by
  rw [show EuclideanSpace.equiv (Fin n) ℝ (cubeCoords n q) =
      (fun i => (2 * (q i : ℝ) - 1) / Real.sqrt (1 - (2 * (q i : ℝ) - 1) ^ 2)) from by
    rw [cubeCoords]
    exact ContinuousLinearEquiv.apply_symm_apply (EuclideanSpace.equiv (Fin n) ℝ) _]

theorem cubeToOnePoint_surjective (n : ℕ) (hn : 1 ≤ n) : Function.Surjective (cubeToOnePoint n) := by
  intro y
  induction y using OnePoint.rec with
  | infty =>
    refine ⟨0, ?_⟩
    have hmem : (0 : CubeI n) ∈ Cube.boundary (Fin n) := by
      refine ⟨⟨0, hn⟩, ?_⟩
      left
      rfl
    simp only [cubeToOnePoint, if_pos hmem]
  | coe x =>
    let q : CubeI n := fun i =>
      ⟨(rInv (EuclideanSpace.equiv (Fin n) ℝ x i) + 1) / 2,
        rInv_mem_Icc (EuclideanSpace.equiv (Fin n) ℝ x i)⟩
    refine ⟨q, ?_⟩
    have hqval : ∀ i : Fin n,
        (q i : ℝ) = (rInv (EuclideanSpace.equiv (Fin n) ℝ x i) + 1) / 2 := fun i => rfl
    have hnotmem : q ∉ Cube.boundary (Fin n) := by
      rintro ⟨i, hi | hi⟩
      · have hpos := (rInv_interior (EuclideanSpace.equiv (Fin n) ℝ x i)).1
        have hz : (q i : ℝ) = 0 := by
          have := congrArg Subtype.val hi
          simpa using this
        rw [hqval i] at hz
        exact absurd hz (ne_of_gt hpos)
      · have hlt := (rInv_interior (EuclideanSpace.equiv (Fin n) ℝ x i)).2
        have hz : (q i : ℝ) = 1 := by
          have := congrArg Subtype.val hi
          simpa using this
        rw [hqval i] at hz
        exact absurd hz (ne_of_lt hlt)
    simp only [cubeToOnePoint, if_neg hnotmem]
    congr 1
    apply (EuclideanSpace.equiv (Fin n) ℝ).injective
    ext i
    rw [cubeCoords_apply n q i, hqval i, cubeCoords_rInv]

end

end Work.Stems
