import Mathlib
import Submission.Work.Cohomology.DiskPairBasic
import Submission.Work.Cohomology.sphereInUnitHomologyIso

/-!
# The positive-degree singular homology of the zero-dimensional sphere

The sphere `S⁰ = Sⁿ⁻¹ ⊆ Dⁿ` for `n = 1` is the two-point space `{±1} ⊆ D¹`.  In particular it is a
finite discrete space, hence totally disconnected; and Mathlib's computation
`AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace` says that the
positive-degree singular homology of a totally disconnected space vanishes.

The only real work is to see that `S⁰` is finite: the sphere of radius `1` in the one-dimensional
Euclidean space `ℝ¹` is contained in the two points `±e₀` (`PiLp.norm_sq_eq_of_L2` computes the
norm from the single coordinate, and `sq_eq_one_iff` finishes).
-/

set_option linter.style.haveILetI false

open CategoryTheory Metric

namespace Work.Cohomology

noncomputable section

/-- **`S⁰` is finite.**  The unit sphere of `ℝ¹` is contained in the two points `±e₀`, because the
norm of a vector of `EuclideanSpace ℝ (Fin 1)` is the absolute value of its unique coordinate. -/
lemma finite_metricSphere_fin_one :
    (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1).Finite := by
  have hsub : Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 ⊆
      ({EuclideanSpace.single (0 : Fin 1) (1 : ℝ),
        EuclideanSpace.single (0 : Fin 1) (-1 : ℝ)} : Set (EuclideanSpace ℝ (Fin 1))) := by
    intro x hx
    rw [Metric.mem_sphere, dist_eq_norm] at hx
    have hnorm : ‖x‖ = 1 := by simpa using hx
    have hsq : (x.ofLp 0) ^ 2 = 1 := by
      have h := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 1 => ℝ) x
      rw [hnorm, one_pow, Fin.sum_univ_one, Real.norm_eq_abs, sq_abs] at h
      exact h.symm
    rcases sq_eq_one_iff.mp hsq with h | h
    · left
      apply PiLp.ext; intro i
      rw [PiLp.single_apply]
      obtain rfl : i = 0 := Subsingleton.elim i 0
      simp [h]
    · right
      apply PiLp.ext; intro i
      rw [PiLp.single_apply]
      obtain rfl : i = 0 := Subsingleton.elim i 0
      simp [h]
  exact Set.Finite.subset (Set.Finite.insert _ (Set.finite_singleton _)) hsub

/-- **`S⁰ ⊆ D¹` is finite**, since it is homeomorphic to the unit sphere of `ℝ¹`. -/
lemma finite_sphereInUnit_one : Finite ↥(Work.Cohomology.sphereInUnit 1) := by
  haveI : Fintype ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :=
    finite_metricSphere_fin_one.fintype
  exact (Equiv.finite_iff (sphereInUnitHomeomorph 1).toEquiv).mpr inferInstance

/-- **`S⁰ ⊆ D¹` is totally disconnected**: a finite `T₁` space is discrete, hence totally
disconnected. -/
theorem totallyDisconnected_sphereInUnit_one :
    TotallyDisconnectedSpace ↥(Work.Cohomology.sphereInUnit 1) := by
  haveI := finite_sphereInUnit_one
  infer_instance

/-- The positive-degree singular homology of `S⁰ = Sⁿ⁻¹ ⊆ Dⁿ` (for `n = 1`) vanishes. -/
theorem sphereInUnitOneHomologyZero (j : ℕ) (hj : 1 ≤ j) :
    CategoryTheory.Limits.IsZero
      ((Work.Cohomology.singularChains ℤ
        (TopCat.of (Work.Cohomology.sphereInUnit 1))).homology j) := by
  haveI := totallyDisconnected_sphereInUnit_one
  exact AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    (ModuleCat ℤ) j (ModuleCat.of ℤ ℤ) (TopCat.of (Work.Cohomology.sphereInUnit 1))
    (by omega)

end

end Work.Cohomology
