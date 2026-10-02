import Mathlib
import Submission.Work.Cohomology.SphDefs
import Submission.Work.Cohomology.sphereBandHomotopyEquiv

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The equatorial band of `Sᵐ` is path connected (`m ≥ 2`)

The equatorial band `band m = {x ∈ S^(m+1) | -1/2 < x_{m+1} < 1/2}` of the unit sphere
`S^(m+1) ⊆ ℝ^(m+2)` is homotopy equivalent to `S^m` (`Work.Cohomology.sphereBandHomotopyEquiv`,
through the homeomorphism `flatHomeo` identifying the nested subtype `↥(band m)` with the
"naive" band `Band m`).  For `m ≥ 2` the sphere `S^m` is path connected, and path connectedness
transfers backwards along a homotopy equivalence: if `X ≃ₕ Y` and `Y` is path connected, then so
is `X`.

Concretely, for `x y ∈ ↥(band m)` one joins `x` to `(e.invFun ∘ e.toFun) x` by the path
`t ↦ e.left_inv.some (t, x)` given by the homotopy `e.invFun ∘ e.toFun ≃ id`, then maps a path
from `e.toFun x` to `e.toFun y` in `S^m` through `e.invFun`, and finally joins
`(e.invFun ∘ e.toFun) y` to `y` by the same homotopy at `y`, reversed.

## Main result

* `Work.Cohomology.pathConnected_band`:
  `PathConnectedSpace ↥(band m)` for `m ≥ 2`.
-/

open ContinuousMap

noncomputable section

namespace Work.Cohomology

/-! ## Path connectedness of the unit sphere `Sᵐ` for `m ≥ 2` -/

/-- The two descriptions of the unit sphere of `ℝ^m` agree. -/
lemma sphere_eq_sphSet (m : ℕ) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 = sphSet m := by
  ext x
  simp [sphSet]

/-- `sphSet m ⊆ ℝ^m` is path connected for `m ≥ 2`. -/
lemma pathConnectedSpace_sphSet (m : ℕ) (hm : 2 ≤ m) : PathConnectedSpace ↥(sphSet m) := by
  have hrank : (1 : Cardinal) < Module.rank ℝ (EuclideanSpace ℝ (Fin m)) := by
    rw [show Module.rank ℝ (EuclideanSpace ℝ (Fin m)) = (m : Cardinal) from by
      rw [LinearEquiv.rank_eq (EuclideanSpace.equiv (Fin m) ℝ).toLinearEquiv, rank_fin_fun m]]
    norm_num; omega
  have h : IsPathConnected (sphSet m) := by
    have h' := isPathConnected_sphere hrank (0 : EuclideanSpace ℝ (Fin m))
      (by norm_num : (0 : ℝ) ≤ 1)
    rwa [sphere_eq_sphSet m] at h'
  exact isPathConnected_iff_pathConnectedSpace.mp h

/-! ## Path connectedness transfers along a homotopy equivalence -/

/-- A homotopy `H` from `f₀` to `f₁` gives, for every point `x`, the path `t ↦ H (t, x)` from
`f₀ x` to `f₁ x`. -/
def pathOfHomotopy {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f₀ f₁ : C(X, Y)} (H : ContinuousMap.Homotopy f₀ f₁) (x : X) : Path (f₀ x) (f₁ x) where
  toFun t := H (t, x)
  continuous_toFun := (map_continuous H).comp (continuous_id.prodMk continuous_const)
  source' := H.map_zero_left x
  target' := H.map_one_left x

/-- If `X` and `Y` are homotopy equivalent and `Y` is path connected, then so is `X`. -/
lemma pathConnectedSpace_of_homotopyEquiv {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (hY : PathConnectedSpace Y) : PathConnectedSpace X where
  nonempty := ⟨e.invFun (Classical.choice hY.nonempty)⟩
  joined x y := by
    have hx : Joined (e.invFun (e.toFun x)) x := ⟨pathOfHomotopy e.left_inv.some x⟩
    have hy : Joined (e.invFun (e.toFun y)) y := ⟨pathOfHomotopy e.left_inv.some y⟩
    have hmid : Joined (e.invFun (e.toFun x)) (e.invFun (e.toFun y)) :=
      (hY.joined (e.toFun x) (e.toFun y)).map (map_continuous e.invFun)
    exact hx.symm.trans (hmid.trans hy)

/-! ## The band -/

theorem pathConnected_band (m : ℕ) (hm : 2 ≤ m) :
    PathConnectedSpace ↥(Work.Cohomology.band m) := by
  have hm1 : 1 ≤ m := by omega
  obtain ⟨e⟩ := sphereBandHomotopyEquiv m hm1
  have he : ContinuousMap.HomotopyEquiv ↥(band m) ↥(sphSet m) :=
    (flatHomeo (q := sphSet (m+1))
      (P := fun x => x (Fin.last m) > -(1/2) ∧ x (Fin.last m) < 1/2)).toHomotopyEquiv.trans e
  exact pathConnectedSpace_of_homotopyEquiv he (pathConnectedSpace_sphSet m hm)

end Work.Cohomology
