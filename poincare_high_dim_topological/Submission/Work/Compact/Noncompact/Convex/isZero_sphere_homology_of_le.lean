import Mathlib
import Submission.Work.Cohomology.sphereVanishing
import Submission.Work.Cohomology.sphereHomologyZero
import Submission.Work.Cohomology.isZero_homology_of_homotopyEquiv

namespace Work.Compact.Noncompact.Convex

/-- The homeomorphism `x ↦ R⁻¹ • (x - c)` from the sphere of centre `c` and positive radius `R`
onto the unit sphere centred at the origin, with inverse `y ↦ c + R • y`. -/
noncomputable def sphereHomeomorph {n : ℕ} (c : EuclideanSpace ℝ (Fin n)) {R : ℝ}
    (hR : 0 < R) :
    Metric.sphere c R ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 where
  toFun x := ⟨R⁻¹ • ((x : EuclideanSpace ℝ (Fin n)) - c), by
    have hx : ‖(x : EuclideanSpace ℝ (Fin n)) - c‖ = R := by
      rw [← dist_eq_norm]; exact Metric.mem_sphere.mp x.2
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos hR, hx, inv_mul_cancel₀ (ne_of_gt hR)]⟩
  invFun y := ⟨c + R • (y : EuclideanSpace ℝ (Fin n)), by
    have hy : ‖(y : EuclideanSpace ℝ (Fin n))‖ = 1 := by
      rw [← dist_zero_right]; exact Metric.mem_sphere.mp y.2
    rw [Metric.mem_sphere, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos hR, hy, mul_one]⟩
  left_inv x := by
    apply Subtype.ext
    show c + R • (R⁻¹ • ((x : EuclideanSpace ℝ (Fin n)) - c)) = (x : EuclideanSpace ℝ (Fin n))
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hR), one_smul]
    abel
  right_inv y := by
    apply Subtype.ext
    show R⁻¹ • ((c + R • (y : EuclideanSpace ℝ (Fin n))) - c) = (y : EuclideanSpace ℝ (Fin n))
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ (ne_of_gt hR), one_smul]
  continuous_toFun := by
    apply Continuous.subtype_mk
    fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    fun_prop

/-- **The singular homology of the sphere `S^{n-1} ⊆ ℝⁿ` vanishes in degrees `≥ n`.**

For `n ≥ 1`, a centre `c : ℝⁿ` and radius `R > 0`, the sphere `S^{n-1} = Metric.sphere c R ⊆ ℝⁿ`
has `H_j(S^{n-1}; ℤ) = 0` for every `j ≥ n`.

Route: the translation/dilation homeomorphism `x ↦ R⁻¹ • (x - c)` identifies `Metric.sphere c R`
with `Metric.sphere (0 : ℝⁿ) 1`, and vanishing of singular homology is a homotopy invariant
(`Work.Cohomology.isZero_homology_of_homotopyEquiv`, `Work.Cohomology.homologyIso_of_homotopyEquiv`).
For `n ≥ 2`, `Metric.sphere (0 : ℝⁿ) 1 = Metric.sphere (0 : ℝ^((n-1)+1)) 1` and one applies
`Work.Cohomology.sphereVanishing (n - 1) j`: its hypotheses are `1 ≤ n - 1`, `j ≠ 0` (from `j ≥ n ≥ 1`)
and `j ≠ n - 1` (from `j ≥ n`); the type `Fin ((n-1)+1)` is converted to `Fin n` with
`Nat.sub_add_cancel` (as in `Submission/Work/Cohomology/diskPairHomologyZero.lean`).  For `n = 1` the
sphere is the two-point space `S⁰ = sphSet 1` and `Work.Cohomology.sphereVanishing_zero j` (with
`j ≠ 0`) applies; alternatively `AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace`. -/
theorem isZero_sphere_homology_of_le {n j : ℕ} (hn : 1 ≤ n)
    (c : EuclideanSpace ℝ (Fin n)) {R : ℝ} (hR : 0 < R) (hj : n ≤ j) :
    CategoryTheory.Limits.IsZero
      ((Work.Cohomology.singularChains ℤ (TopCat.of ↥(Metric.sphere c R))).homology j) := by
  -- Vanishing for the standard unit sphere `S^{n-1} = sphSet n`.
  have hbase : CategoryTheory.Limits.IsZero
      ((Work.Cohomology.singularChains ℤ (Work.Cohomology.sphTop n)).homology j) := by
    rcases eq_or_lt_of_le hn with h1 | h2
    · -- `n = 1`: the zero-dimensional sphere, a finite discrete space.
      subst h1
      exact Work.Cohomology.sphereVanishing_zero j (by omega)
    · -- `n ≥ 2`: apply the off-top vanishing for `S^(n-1) ⊆ ℝ^((n-1)+1)`.
      obtain h := Work.Cohomology.sphereVanishing_aux (n - 1) (by omega) j (by omega) (by omega)
      rw [Nat.sub_add_cancel hn] at h
      exact h
  -- Transport along the homeomorphism `Metric.sphere c R ≃ₜ sphSet n`.
  have hH : Metric.sphere c R ≃ₜ ↥(Work.Cohomology.sphSet n) :=
    (sphereHomeomorph c hR).trans (Homeomorph.setCongr (Work.Cohomology.sphereSet_eq n))
  exact Work.Cohomology.isZero_homology_of_homotopyEquiv hH.toHomotopyEquiv j hbase

end Work.Compact.Noncompact.Convex
