import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.Sphere.SphZeroDefs

set_option linter.style.haveILetI false

namespace Work.Sphere

/-- `S⁰` has at most the two points `polePt 0` and `negPolePt 0`, hence is finite. -/
lemma finite_sph_zero
    (hclass : ∀ x : Submission.Sphere.Sph 0,
      x = Submission.Sphere.polePt 0 ∨ x = Submission.Sphere.negPolePt 0) :
    Finite (Submission.Sphere.Sph 0) :=
  Finite.of_surjective
    (fun b : Bool => if b then Submission.Sphere.polePt 0 else Submission.Sphere.negPolePt 0)
    (by
      intro x
      rcases hclass x with h | h
      · exact ⟨true, h.symm⟩
      · exact ⟨false, h.symm⟩)

/-- If `S⁰` has at most two points then its topology is discrete (it is a `T₁` space with
finitely many points). -/
lemma discreteTopology_sph_zero
    (hclass : ∀ x : Submission.Sphere.Sph 0,
      x = Submission.Sphere.polePt 0 ∨ x = Submission.Sphere.negPolePt 0) :
    DiscreteTopology (Submission.Sphere.Sph 0) := by
  haveI : Finite (Submission.Sphere.Sph 0) := finite_sph_zero hclass
  exact DiscreteTopology.of_finite_of_isClosed_singleton fun _ => isClosed_singleton

/-- Every singular simplex of `S⁰` is constant: the standard simplex `Δⁿ` is preconnected
(it is convex) and `S⁰` is a discrete space, so a continuous map `Δⁿ → S⁰` is constant. -/
theorem SphZeroSimplexConst
    (hclass : ∀ x : Submission.Sphere.Sph 0,
      x = Submission.Sphere.polePt 0 ∨ x = Submission.Sphere.negPolePt 0)
    (n : ℕ) (σ : (Submission.Sphere.singSph 0).obj (Opposite.op (SimplexCategory.mk n))) :
    σ = Work.Sphere.constSimplex n (Work.Sphere.simplexVal n σ) := by
  haveI : DiscreteTopology (Submission.Sphere.Sph 0) := discreteTopology_sph_zero hclass
  have hpre : PreconnectedSpace (↑(stdSimplex ℝ (Fin (n + 1)))) :=
    isPreconnected_iff_preconnectedSpace.mp (convex_stdSimplex ℝ (Fin (n + 1))).isPreconnected
  have hval : Work.Sphere.simplexVal n σ =
      (TopCat.toSSetObjEquivT (Submission.Sphere.Sph 0)
        (Opposite.op (SimplexCategory.mk n))) σ (Work.Sphere.basepoint n) := rfl
  apply (TopCat.toSSetObjEquivT (Submission.Sphere.Sph 0)
    (Opposite.op (SimplexCategory.mk n))).injective
  rw [Work.Sphere.constSimplex, Equiv.apply_symm_apply, hval]
  apply ContinuousMap.ext
  intro t
  exact PreconnectedSpace.constant hpre
    ((TopCat.toSSetObjEquivT (Submission.Sphere.Sph 0)
      (Opposite.op (SimplexCategory.mk n))) σ).continuous

end Work.Sphere
