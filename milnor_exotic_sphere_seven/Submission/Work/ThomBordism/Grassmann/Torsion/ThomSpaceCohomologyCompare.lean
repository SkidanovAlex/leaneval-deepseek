import Submission.Work.ThomBordism.Grassmann.Torsion.ModelGeom
import Submission.Work.ThomBordism.Grassmann.Torsion.ExcisionCompat
import Submission.Work.ThomBordism.Grassmann.Torsion.DiscPairIso
import Submission.Work.Thom.ATools

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-!
# `H^{k+8}(Th γ; ℤ) ≅ H^{k+8}(D γ, S γ; ℤ)`: the comparison

The Thom space `T = OnePoint E` of the tautological bundle is compared with the **Thom pair**
`(E, E∖0)` in a chain of isomorphisms:

1. `H^n(T) ≅ H^n(T, far 1)`: `far 1 = {fibN > 1} ∪ {∞}` is a neighbourhood of the basepoint whose
   cohomology vanishes in the degrees needed (input `h1`, `h2`; obtained from the contractibility of
   `far 1`, `contractibleFar`);
2. `H^n(T, far 1) ≅ H^n(near 2, near 2 ∩ far 1)`: excision for the open cover
   `near 2 ∪ far 1 = T` (`relCohomology_iso_of_open_cover`);
3. `≅ H^n(D, {1 < fibN < 2})` with `D = {fibN < 2}`: transport along the homeomorphism of pairs
   induced by `OnePoint.some` (`homeoNear`);
4. `≅ H^n(D, {0 < fibN < 2})`: the annulus is a deformation retract of the punctured disc
   (`discPairIso`);
5. `≅ H^n(E, E∖0) = OpenThom`: the radial retraction of `E` onto `D` (`puncturedDiscPairIso`).
-/

open scoped Topology TensorProduct
open CategoryTheory

namespace Work.ThomBordism.Grassmann.Torsion

open Work.ThomBordism.Grassmann

noncomputable section

/-- **The comparison of the Thom space with the Thom pair**, in degree `(k+7)+1 = k+8`.

The two hypotheses are the vanishing of the cohomology of `far k m 1` in degrees `k+7` and `k+8`
(e.g. from `contractibleFar` and `subsingleton_cohomology_of_contractible`). -/
theorem thomSpaceCohomologyCompare (k m : ℕ)
    (h1 : Subsingleton (Work.Thom.Coh ℤ (k + 7) ↥(far k m 1)))
    (h2 : Subsingleton (Work.Thom.Coh ℤ ((k + 7) + 1) ↥(far k m 1))) :
    Nonempty (((Work.Cohomology.cochainC ℤ
        (sset (TautologicalThomSpace k m))).homology ((k + 7) + 1))
      ≃ₗ[ℤ] Work.Thom.OpenThom (tautologicalBundle k m) ((k + 7) + 1)) := by
  -- step 1: `H^n(T) ≅ H^n(T, far 1)`
  obtain ⟨e0⟩ := Work.ThomBordism.Grassmann.relCoh_equiv_cohomology_of_subsingleton
    (TautologicalThomSpace k m) (far k m 1) (k + 7) h1 h2
  -- step 2: excision with the open cover `near 2 ∪ far 1 = T`
  obtain ⟨e1⟩ := Work.ThomBordism.Grassmann.relCohomology_iso_of_open_cover
    (TopCat.of (TautologicalThomSpace k m)) (near k m 2) (far k m 1)
    (isOpen_near k m 2) (isOpen_far_one k m) (near_union_far k m (by norm_num)) ((k + 7) + 1)
  -- step 3: transport along the homeomorphism of pairs induced by `OnePoint.some`
  have he : ∀ x : ↥(discSet k m),
      x ∈ {x : ↥(discSet k m) | 1 < fibN k m x.val} ↔
        homeoNear k m 2 x ∈ {y : ↥(near k m 2) | (y : OnePoint (tautologicalBundle k m).TotalSpace)
          ∈ far k m 1} := by
    intro x
    simp only [Set.mem_ofPred_eq, homeoNear_apply_coe, some_mem_far_iff, x.property, and_true]
  have hbij := Work.Thom.bijective_relCohMap_of_homeomorphA
    {x : ↥(discSet k m) | 1 < fibN k m x.val}
    {y : ↥(near k m 2) | (y : OnePoint (tautologicalBundle k m).TotalSpace) ∈ far k m 1}
    (homeoNear k m 2) he ℤ ((k + 7) + 1)
  -- step 4 and 5
  obtain ⟨e3⟩ := discPairIso k m (k + 7)
  obtain ⟨e4⟩ := puncturedDiscPairIso k m ((k + 7) + 1)
  exact ⟨(e0.symm.trans e1.toLinearEquiv).trans
    ((LinearEquiv.ofBijective _ hbij).trans (e3.trans e4))⟩

end

end Work.ThomBordism.Grassmann.Torsion
