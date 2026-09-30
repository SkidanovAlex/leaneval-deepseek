import Mathlib
import Submission.Work.Projective.Cover
import Submission.Work.Projective.nonempty_continuousLinearEquiv
import Submission.Work.Cohomology.sphereCohomologyTop
import Submission.Work.Cohomology.sphereCohomologyZero
import Submission.Work.Cohomology.punctured_homotopyEquiv_sphere
import Submission.Work.Cohomology.MVCohomology

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option synthInstance.maxHeartbeats 400000

/-!
# The cohomology of `U ∩ V` in `ℂP²`

Here `U = cp2U = chartSet 0` and `V = cp2V = chartSet 1 ∪ chartSet 2` are the standard open sets
of `ℂP²`.  The chart at `0` identifies `U` with `ℂ²`, and under this identification the points of
`V` correspond exactly to the nonzero vectors of `ℂ²`:

`U ∩ V ≅ ℂ² ∖ {0} ≃ₕ S³`.

Hence `H⁰(U ∩ V) = ℤ`, `H³(U ∩ V) = ℤ`, and all other cohomology groups vanish.
-/

open scoped Manifold ContDiff Topology
open CategoryTheory

namespace Work.Projective

noncomputable section

/-! ## The chart at `0` identifies `U ∩ V` with the punctured plane -/

/-- A point of `ℂP²` is in `chartSet 0` iff its `0`-th homogeneous coordinate is nonzero; its
image under the chart at `0` is `chartFun 0 p ∈ ℂ²`.  This point also lies in
`cp2V = chartSet 1 ∪ chartSet 2` precisely when its chart coordinates do not both vanish. -/
theorem cp2UV_chartInv_mem_iff (w : Fin 2 → ℂ) :
    chartInv 0 w ∈ cp2V ↔ w ≠ 0 := by
  have h1 : (Fin.insertNth (α := fun _ => ℂ) 0 (1 : ℂ) w) 1 = w 0 := by
    rw [show (1 : Fin 3) = Fin.succAbove (0 : Fin 3) (0 : Fin 2) from by decide]
    exact Fin.insertNth_apply_succAbove (α := fun _ => ℂ) 0 1 w 0
  have h2 : (Fin.insertNth (α := fun _ => ℂ) 0 (1 : ℂ) w) 2 = w 1 := by
    rw [show (2 : Fin 3) = Fin.succAbove (0 : Fin 3) (1 : Fin 2) from by decide]
    exact Fin.insertNth_apply_succAbove (α := fun _ => ℂ) 0 1 w 1
  have hmem1 : chartInv 0 w ∈ chartSet 1 ↔ w 0 ≠ 0 := by
    rw [chartInv_apply, mem_chartSet_iff 1 ⟨_, insertNth_one_ne_zero 0 w⟩]
    simp only [h1]
  have hmem2 : chartInv 0 w ∈ chartSet 2 ↔ w 1 ≠ 0 := by
    rw [chartInv_apply, mem_chartSet_iff 2 ⟨_, insertNth_one_ne_zero 0 w⟩]
    simp only [h2]
  rw [cp2V, Set.mem_union, hmem1, hmem2]
  constructor
  · rintro (h | h) hw
    · exact h (by simp [hw])
    · exact h (by simp [hw])
  · intro hw
    by_cases h0 : w 0 = 0
    · right
      intro hw1
      exact hw (funext fun i => by fin_cases i <;> simp [h0, hw1])
    · left
      exact h0

/-- A point of `U ∩ V` has non-vanishing chart coordinates in the chart at `0`: if `chartFun 0`
vanished at `p`, then `p` would be the origin `[1 : 0 : 0]`, which is not in `V`. -/
theorem chartFun_ne_zero_of_mem (p : ↥(cp2U ∩ cp2V)) : chartFun 0 p.1 ≠ 0 := by
  intro h
  have h1 : p.1 = cp2Origin := by
    have h2 := chartInv_chartFun 0 p.1 p.2.1
    rw [h] at h2
    exact h2.symm
  exact cp2Origin_notMem_cp2V (h1 ▸ p.2.2)

/-- **The chart at `0` identifies `U ∩ V` with the punctured plane `ℂ² ∖ {0}`.** -/
noncomputable def cp2UV_homeo : ↥(cp2U ∩ cp2V) ≃ₜ {z : Fin 2 → ℂ // z ≠ 0} where
  toFun p := ⟨chartFun 0 p.1, chartFun_ne_zero_of_mem p⟩
  invFun z := ⟨chartInv 0 z.1,
    ⟨chartInv_mem_chartSet 0 z.1, (cp2UV_chartInv_mem_iff z.1).mpr z.2⟩⟩
  left_inv p := Subtype.ext (chartInv_chartFun 0 p.1 p.2.1)
  right_inv z := Subtype.ext (chartFun_chartInv 0 z.1)
  continuous_toFun := Continuous.subtype_mk
    ((cp2U_homeo.continuous_invFun).comp
      (Continuous.subtype_mk continuous_subtype_val fun p => p.2.1))
    chartFun_ne_zero_of_mem
  continuous_invFun := Continuous.subtype_mk
    ((continuous_chartInv 0).comp continuous_subtype_val)
    (fun z => ⟨chartInv_mem_chartSet 0 z.1, (cp2UV_chartInv_mem_iff z.1).mpr z.2⟩)

/-! ## `U ∩ V` is homotopy equivalent to `S³` -/

/-- The punctured plane `ℂ² ∖ {0}` is homeomorphic to the punctured Euclidean space
`ℝ⁴ ∖ {0}` (both are four-dimensional real normed spaces). -/
theorem cp2UV_punctured_homeo :
    Nonempty ({z : Fin 2 → ℂ // z ≠ 0} ≃ₜ
      {v : EuclideanSpace ℝ (Fin 4) // v ≠ 0}) := by
  obtain ⟨L⟩ := nonempty_continuousLinearEquiv 2
  exact ⟨{ toFun := fun z => ⟨L z.1, fun h => z.2 (L.map_eq_zero_iff.mp h)⟩
           invFun := fun v => ⟨L.symm v.1, fun h => v.2 (by
             rw [← L.apply_symm_apply v.1, h, map_zero])⟩
           left_inv := fun z => Subtype.ext (L.symm_apply_apply z.1)
           right_inv := fun v => Subtype.ext (L.apply_symm_apply v.1)
           continuous_toFun := Continuous.subtype_mk
             (L.continuous.comp continuous_subtype_val) _
           continuous_invFun := Continuous.subtype_mk
             (L.symm.continuous.comp continuous_subtype_val) _ }⟩

/-- **`U ∩ V` is homotopy equivalent to `S³ ⊆ ℝ⁴`.** -/
theorem cp2UV_homotopyEquiv_sphere :
    Nonempty (ContinuousMap.HomotopyEquiv ↥(cp2U ∩ cp2V)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)) := by
  obtain ⟨hP⟩ := cp2UV_punctured_homeo
  obtain ⟨hsph⟩ := Work.Cohomology.punctured_homotopyEquiv_sphere (EuclideanSpace ℝ (Fin 4))
  exact ⟨cp2UV_homeo.toHomotopyEquiv.trans (hP.toHomotopyEquiv.trans hsph)⟩

/-! ## The cohomology computation -/

/-- The sphere `S³ ⊆ ℝ⁴` is path-connected. -/
instance pathConnectedSpace_sphere_four :
    PathConnectedSpace ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) := by
  have hrank : Module.rank ℝ (EuclideanSpace ℝ (Fin 4)) = (4 : Cardinal) := by
    have h2 := LinearEquiv.rank_eq (EuclideanSpace.equiv (Fin 4) ℝ).toLinearEquiv
    rw [h2]
    exact rank_fin_fun 4
  refine isPathConnected_iff_pathConnectedSpace.mp ?_
  refine isPathConnected_sphere ?_ 0 (by norm_num)
  rw [hrank]
  norm_num

/-- **The cohomology of `U ∩ V` in `ℂP²`**: the chart at `0` identifies
`U ∩ V = chartSet 0 ∩ (chartSet 1 ∪ chartSet 2)` with the punctured plane `ℂ² ∖ {0}`, which is
homotopy equivalent to `S³`, so `H⁰(U ∩ V) = ℤ`, `H³(U ∩ V) = ℤ` and `Hⁿ(U ∩ V) = 0` otherwise. -/
theorem cp2UV_cohomology (n : ℕ) :
    Nonempty (Work.Cohomology.singularCohomology ℤ n (TopCat.of ↥(cp2U ∩ cp2V)) ≅
      ModuleCat.of ℤ (Fin ((if n = 0 then 1 else 0) + (if n = 3 then 1 else 0)) → ℤ)) := by
  obtain ⟨e1⟩ := Work.Cohomology.cohomologyIso_of_homotopyEquiv
    cp2UV_homotopyEquiv_sphere.some n
  by_cases h0 : n = 0
  · subst h0
    have hk : (if (0 : ℕ) = 0 then 1 else 0) + (if (0 : ℕ) = 3 then 1 else 0) = 1 := by
      norm_num
    rw [hk]
    obtain ⟨e0⟩ := Work.Cohomology.singularCohomology_zero ℤ
      (TopCat.of ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))
    exact ⟨e1 ≪≫ e0 ≪≫ (LinearEquiv.funUnique (Fin 1) ℤ ℤ).toModuleIso.symm⟩
  · by_cases h3 : n = 3
    · subst h3
      have hk : (if (3 : ℕ) = 0 then 1 else 0) + (if (3 : ℕ) = 3 then 1 else 0) = 1 := by
        norm_num
      rw [hk]
      obtain ⟨e3⟩ := Work.Cohomology.sphereCohomologyTop 3 (by norm_num)
      exact ⟨e1 ≪≫ e3 ≪≫ (LinearEquiv.funUnique (Fin 1) ℤ ℤ).toModuleIso.symm⟩
    · have hk : (if n = 0 then 1 else 0) + (if n = 3 then 1 else 0) = 0 := by
        rw [if_neg h0, if_neg h3]
      rw [hk]
      exact ⟨e1 ≪≫ CategoryTheory.Limits.IsZero.iso
        (Work.Cohomology.sphereCohomologyZero 3 n (by norm_num) h0 h3)
        (ModuleCat.isZero_of_subsingleton (ModuleCat.of ℤ (Fin 0 → ℤ)))⟩

end

end Work.Projective
