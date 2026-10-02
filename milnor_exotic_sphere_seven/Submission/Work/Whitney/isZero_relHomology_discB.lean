import Mathlib
import Submission.Work.Thom.stepDefs
import Submission.Work.Cohomology.diskPairHomologyZero
import Submission.Work.Cohomology.relChainsHomeomorphCompat

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The relative homology of the disc bundle over a point vanishes below and above the top degree

Let `Y` be a nonempty subsingleton, so that `Y × Dⁿ` is the closed unit disc `Dⁿ` and the "boundary"
`Work.Thom.DiscB Y n = {q | q.2 ∈ Sⁿ⁻¹}` is the unit sphere.  Then the relative singular homology
`H_k(Y × Dⁿ, Y × Sⁿ⁻¹; ℤ)` vanishes for every `k ≠ n`.

This is the (homological) companion of the fact that the disc pair `(Dⁿ, Sⁿ⁻¹)` computes the local
homology of an `n`-manifold.  The proof is a transport of
`Work.Cohomology.diskPairHomologyZero` (the statement for the metric disc pair `(Dⁿ, Sⁿ⁻¹)`) along
the homeomorphism of pairs `(Y × Dⁿ, Y × Sⁿ⁻¹) ≅ (Dⁿ, Sⁿ⁻¹)` given by forgetting the `Y`-coordinate
(inverse: choosing the base point `y₀ ∈ Y`), via
`Work.Cohomology.relChainsHomeomorphCompat`.
-/

namespace Work.Whitney

open CategoryTheory CategoryTheory.Limits

theorem isZero_relHomology_discB (Y : Type) [TopologicalSpace Y] [Subsingleton Y] [Nonempty Y]
    (n k : ℕ) (hn : 1 ≤ n) (hk : k ≠ n) :
    CategoryTheory.Limits.IsZero
      ((Work.Cohomology.relChains (TopCat.of (Y × Work.Thom.MBall n))
        (Work.Thom.DiscB Y n)).homology k) := by
  classical
  obtain ⟨y₀⟩ := ‹Nonempty Y›
  -- The two descriptions of the unit ball: `mBall n` (used for `MBall n`) and the metric
  -- `closedBall 0 1` (used for `diskUnit n`) are the same set.
  have hmem : ∀ x : EuclideanSpace ℝ (Fin n), x ∈ Work.Thom.mBall n ↔
      x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    intro x
    simp [Work.Thom.mBall, Metric.mem_closedBall, dist_zero_right]
  -- The homeomorphism of pairs `(Y × Dⁿ, Y × Sⁿ⁻¹) ≅ (Dⁿ, Sⁿ⁻¹)`: forget the `Y`-coordinate.
  let e : (Y × Work.Thom.MBall n) ≃ₜ ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    { toFun := fun p => ⟨p.2.1, (hmem p.2.1).mp p.2.2⟩
      invFun := fun x => (y₀, ⟨x.1, (hmem x.1).mpr x.2⟩)
      left_inv := fun p => Prod.ext (Subsingleton.elim _ _) rfl
      right_inv := fun x => rfl
      continuous_toFun := (continuous_subtype_val.comp continuous_snd).subtype_mk
        (fun p => (hmem p.2.1).mp p.2.2)
      continuous_invFun := Continuous.prodMk continuous_const
        (continuous_subtype_val.subtype_mk (fun x => (hmem x.1).mpr x.2)) }
  have hep : ∀ p : Y × Work.Thom.MBall n, (e p : EuclideanSpace ℝ (Fin n)) = p.2.1 :=
    fun p => rfl
  -- The homeomorphism carries the boundary `DiscB Y n` onto the sphere `sphereInUnit n`.
  have he : ∀ p : Y × Work.Thom.MBall n, p ∈ Work.Thom.DiscB Y n ↔
      e p ∈ Work.Cohomology.sphereInUnit n := by
    intro p
    simp only [Work.Thom.DiscB, Set.mem_ofPred_eq, Work.Cohomology.sphereInUnit,
      Work.Thom.mSph, Metric.mem_sphere, dist_zero_right, hep]
  -- Transport the vanishing of the homology of the disc pair along the homeomorphism of pairs.
  obtain ⟨iso⟩ := Work.Cohomology.relChainsHomeomorphCompat (Y × Work.Thom.MBall n)
    ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) (Work.Thom.DiscB Y n)
    (Work.Cohomology.sphereInUnit n) e he k
  exact IsZero.of_iso (Work.Cohomology.diskPairHomologyZero n k hn hk) iso

end Work.Whitney
