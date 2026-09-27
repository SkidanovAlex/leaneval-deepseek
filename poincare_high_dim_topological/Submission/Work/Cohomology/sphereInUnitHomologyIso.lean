import Mathlib
import Submission.Work.Cohomology.DiskPairBasic
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.homologyContractible

/-!
# The homology of the unit sphere inside the unit ball

The relative pair `(Dⁿ, Sⁿ⁻¹)` is modelled by the closed unit ball
`Dⁿ = closedBall 0 1 ⊆ EuclideanSpace ℝ (Fin n)` and the subspace
`sphereInUnit n = {x : Dⁿ | (x : EuclideanSpace ℝ (Fin n)) ∈ sphere 0 1}` carved out of it.
For computations it is convenient to replace `sphereInUnit n`, which is a subtype of a subtype,
by the more standard model `Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1`.

The two spaces are canonically homeomorphic — the homeomorphism is simply
`x ↦ ((x : Dⁿ) : EuclideanSpace ℝ (Fin n))`, with inverse obtained from
`Metric.sphere_subset_closedBall`.  Since a homeomorphism is a homotopy equivalence, it induces an
isomorphism on singular homology in every degree (`Work.Cohomology.homologyEquiv`), which is the
statement of `sphereInUnitHomologyIso` below.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory Metric

namespace Work.Cohomology

noncomputable section

/-- The canonical homeomorphism between the unit sphere of `ℝⁿ` viewed as a subspace of the closed
unit ball `Dⁿ` and the more standard model `Metric.sphere 0 1 ⊆ ℝⁿ`: it is induced by the
inclusion `Dⁿ ⊆ ℝⁿ`, which restricts to a bijection of the two spheres. -/
def sphereInUnitHomeomorph (n : ℕ) :
    TopCat.of (sphereInUnit n) ≃ₜ
      TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) where
  toFun x := ⟨((x.1 : diskUnit n) : EuclideanSpace ℝ (Fin n)), x.2⟩
  invFun y := ⟨⟨(y.1 : EuclideanSpace ℝ (Fin n)), Metric.sphere_subset_closedBall y.2⟩, y.2⟩
  left_inv x := by ext; rfl
  right_inv y := by ext; rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val

/-- **The singular homology of `Sⁿ⁻¹ ⊆ Dⁿ` agrees with that of `Metric.sphere 0 1 ⊆ ℝⁿ`** in every
degree, because the two spaces are homeomorphic and homology is a homotopy invariant. -/
theorem sphereInUnitHomologyIso (n k : ℕ) :
    Nonempty
      ((Work.Cohomology.singularChains ℤ
          (TopCat.of (Work.Cohomology.sphereInUnit n))).homology k ≅
        (Work.Cohomology.singularChains ℤ
          (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1))).homology k) := by
  -- The canonical homeomorphism of the two models of the sphere, as a homotopy equivalence.
  have he : ContinuousMap.HomotopyEquiv (TopCat.of (sphereInUnit n))
      (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) :=
    (sphereInUnitHomeomorph n).toHomotopyEquiv
  let f : TopCat.of (sphereInUnit n) ⟶
      TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) := TopCat.ofHom he.toFun
  let g : TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) ⟶
      TopCat.of (sphereInUnit n) := TopCat.ofHom he.invFun
  have h1 : TopCat.Homotopy (f ≫ g) (𝟙 (TopCat.of (sphereInUnit n))) := he.left_inv.some
  have h2 : TopCat.Homotopy (g ≫ f)
      (𝟙 (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1))) := he.right_inv.some
  -- hence an isomorphism on singular homology in every degree
  haveI : IsIso (HomologicalComplex.homologyMap
      (chainMap ℤ (TopCat.of (sphereInUnit n))
        (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) f) k) :=
    homologyEquiv ℤ _ _ f g h1 h2 k
  exact ⟨CategoryTheory.asIso (HomologicalComplex.homologyMap
    (chainMap ℤ (TopCat.of (sphereInUnit n))
      (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) f) k)⟩

end

end Work.Cohomology
