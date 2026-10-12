import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBoxFock.latCubeSum_tendsto_L2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open scoped BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-!
# `Work.BoseBoxFock.latPer_bdd_global`

The periodisation `LatFourier.latPer ℓ W z = ∑'_m W (z + ℓ • latVec m)` of a bounded weight `W`
vanishing outside the ball of radius `R` is bounded **on all of `ℝ³`**, not only on the closed cube
`latBox ℓ`.  This is immediate from two facts that are both already in the corpus:

* `LatFourier.latPer_bdd` bounds `‖latPer ℓ W z‖` for `z` in the closed cube `[0,ℓ]³`;
* `latPer_add_latVec` says that `latPer ℓ W` is invariant under the lattice translations
  `z ↦ z + ℓ • latVec m`, so it suffices to find, for an arbitrary `z`, a lattice translate of `z`
  inside the cube.

The only new ingredient is that elementary rounding: for every real `y` and `ℓ > 0` there is an
integer `k` with `y + ℓ k ∈ [0,ℓ]` (`k = -⌊y/ℓ⌋`), whence coordinatewise every `z : ℝ³` has a
lattice translate in `latBox ℓ`.
-/

/-- **Rounding in one dimension**: for every `y : ℝ` and `ℓ > 0` there is an integer `k` with
`y + ℓ k ∈ [0, ℓ]` (take `k = -⌊y/ℓ⌋`). -/
lemma exists_int_add_mul_mem_Icc {ℓ y : ℝ} (hℓ : 0 < ℓ) :
    ∃ k : ℤ, y + ℓ * (k : ℝ) ∈ Set.Icc (0 : ℝ) ℓ := by
  refine ⟨-⌊y / ℓ⌋, ?_, ?_⟩
  · have h1 : (⌊y / ℓ⌋ : ℝ) ≤ y / ℓ := Int.floor_le _
    have hsplit : ℓ * (y / ℓ - (⌊y / ℓ⌋ : ℝ)) = y + ℓ * ((-⌊y / ℓ⌋ : ℤ) : ℝ) := by
      rw [mul_sub, mul_div_cancel₀ y (ne_of_gt hℓ)]
      push_cast
      ring
    rw [← hsplit]
    exact mul_nonneg hℓ.le (sub_nonneg.mpr h1)
  · have h2 : y / ℓ < (⌊y / ℓ⌋ : ℝ) + 1 := Int.lt_floor_add_one _
    have hsplit : ℓ * (y / ℓ - (⌊y / ℓ⌋ : ℝ)) = y + ℓ * ((-⌊y / ℓ⌋ : ℤ) : ℝ) := by
      rw [mul_sub, mul_div_cancel₀ y (ne_of_gt hℓ)]
      push_cast
      ring
    rw [← hsplit]
    have h3 : y / ℓ - (⌊y / ℓ⌋ : ℝ) ≤ 1 := by linarith
    calc ℓ * (y / ℓ - (⌊y / ℓ⌋ : ℝ)) ≤ ℓ * 1 := mul_le_mul_of_nonneg_left h3 hℓ.le
      _ = ℓ := mul_one ℓ

/-- **Rounding in `ℝ³`**: every point has a lattice translate in the closed cube `[0,ℓ]³`. -/
lemma exists_latVec_add_mem_latBox {ℓ : ℝ} (hℓ : 0 < ℓ) (z : E3) :
    ∃ m : Fin 3 → ℤ, z + ℓ • latVec m ∈ LatFourier.latBox ℓ := by
  classical
  choose k hk using fun i : Fin 3 => exists_int_add_mul_mem_Icc (ℓ := ℓ) (y := z i) hℓ
  refine ⟨k, ?_⟩
  rw [LatFourier.mem_latBox]
  intro i
  rw [show (z + ℓ • latVec k) i = z i + ℓ * (k i : ℝ) from by simp [latVec_apply]]
  exact hk i

/-- **The periodisation of a bounded, compactly supported weight is bounded on all of `ℝ³`.**

This is `LatFourier.latPer_bdd` (the bound on the closed cube `[0,ℓ]³`) combined with the lattice
periodicity `latPer_add_latVec` of the periodisation and the rounding lemma above. -/
theorem latPer_bdd_global {ℓ R : ℝ} (hℓ : 0 < ℓ) {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hWb : ∃ C : ℝ, ∀ x, ‖W x‖ ≤ C) (hWs : ∀ x, R < ‖x‖ → W x = 0) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ z : EuclideanSpace ℝ (Fin 3),
      ‖Work.BoseBoxFock.LatFourier.latPer ℓ W z‖ ≤ D := by
  obtain ⟨D, hD0, hD⟩ := LatFourier.latPer_bdd (ℓ := ℓ) (R := R) hℓ hWb hWs
  refine ⟨D, hD0, fun z => ?_⟩
  obtain ⟨m, hm⟩ := exists_latVec_add_mem_latBox hℓ z
  rw [← latPer_add_latVec hℓ W m z]
  exact hD _ hm

end Work.BoseBoxFock
