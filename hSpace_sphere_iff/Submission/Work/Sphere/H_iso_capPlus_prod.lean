/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# Cohomology of `capPlus p × S^q`

The positive cap `capPlus p` of `S^{p+1}` is contractible
(`Work.Sphere.contractibleSpace_sph_compl`), hence the projection
`capPlus p × S^q → S^q` is a homotopy equivalence.  By homotopy invariance of
our simplicial cohomology (`Submission.Sphere.H_iso_of_homotopyEquiv`) this
gives an isomorphism

  H^m(capPlus p × S^q; ℚ) ≅ H^m(S^q; ℚ).

This is the input that lets a product with a contractible factor be discarded
in the computation of the cohomology of a product of spheres.
-/
import Mathlib
import Submission.Work.Sphere.Suspension
import Submission.Work.Sphere.contractibleSpace_sph_compl

open CategoryTheory
open unitInterval

namespace Work.Sphere

/-- The positive cap `capPlus p` of `S^{p+1}` is contractible: it is the sphere with one point
(the pole) removed. -/
theorem capPlus_contractible (p : ℕ) :
    ContractibleSpace ↥(Submission.Sphere.capPlus p) := by
  rw [Submission.Sphere.capPlus_eq p]
  exact Classical.choice (Work.Sphere.contractibleSpace_sph_compl (n := p+1)
    (Submission.Sphere.polePt (p+1)))

/-- **A product with a contractible factor is homotopy equivalent to the other factor.**
If `X` is contractible then the projection `X × Y → Y` is a homotopy equivalence. -/
theorem nonempty_homotopyEquiv_prod_of_contractible (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] [ContractibleSpace X] :
    Nonempty (ContinuousMap.HomotopyEquiv (X × Y) Y) := by
  classical
  -- A homotopy from the identity of `X` to the constant map at a point `c`.
  obtain ⟨c, h⟩ := id_nullhomotopic X
  have F : ContinuousMap.Homotopy (ContinuousMap.id X) (ContinuousMap.const X c) :=
    Classical.choice h
  refine ⟨{
    toFun := ContinuousMap.snd
    invFun := (ContinuousMap.const Y c).prodMk (ContinuousMap.id Y)
    left_inv := ⟨{
      toFun := fun z : I × (X × Y) => (F.symm (z.1, z.2.1), z.2.2)
      continuous_toFun := ?_
      map_zero_left := ?_
      map_one_left := ?_ }⟩
    right_inv := ⟨{
      toFun := fun z : I × Y => z.2
      continuous_toFun := continuous_snd
      map_zero_left := ?_
      map_one_left := ?_ }⟩ }⟩
  · apply Continuous.prodMk
    · exact F.symm.continuous.comp
        (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
    · exact continuous_snd.comp continuous_snd
  · intro z
    -- the contracted factor does not depend on the point of `Y`
    simp
  · intro z
    simp
  · intro z
    simp
  · intro z
    simp

/-- **Cohomology does not see a contractible product factor.**  For every `m` the rational
cohomology of `capPlus p × S^q` in degree `m` is the rational cohomology of `S^q` in degree `m`. -/
theorem H_iso_capPlus_prod (p q m : ℕ) :
    Nonempty (Submission.Cohomology.H
        (TopCat.toSSet.obj (TopCat.of (↥(Submission.Sphere.capPlus p) × ↥(Submission.Sphere.Sph q)))) ℚ m
      ≃ₗ[ℚ] Submission.Cohomology.H (Submission.Sphere.singSph q) ℚ m) := by
  classical
  obtain ⟨e⟩ := @nonempty_homotopyEquiv_prod_of_contractible
    ↥(Submission.Sphere.capPlus p) ↥(Submission.Sphere.Sph q) _ _ (capPlus_contractible p)
  exact Submission.Sphere.H_iso_of_homotopyEquiv
    (TopCat.of (↥(Submission.Sphere.capPlus p) × ↥(Submission.Sphere.Sph q)))
    (Submission.Sphere.Sph q)
    (TopCat.ofHom e.toFun) (TopCat.ofHom e.invFun)
    (Classical.choice e.left_inv) (Classical.choice e.right_inv) m

end Work.Sphere
