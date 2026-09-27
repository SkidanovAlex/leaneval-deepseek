/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# `H^j(S⁰ × S^q) = 0` for `j ≥ 1`, `j ≠ q`

The zero sphere `S⁰` is the two point space `{polePt 0, negPolePt 0}`
(`Work.Sphere.SphZeroTwoPoints`).  Covering it by its two points and pulling this cover back to
`S⁰ × S^q` reduces the cohomology of the product to the cohomology of the pieces, each of which is
a product with a one point space, i.e. `S^q` itself.

Concretely, in the notation of `Work.Sphere.ProdSetup` the cover of `S⁰` by
`W₁ = {polePt 0}` and `W₂ = {negPolePt 0}` gives the subcomplexes `fstAsub`, `fstBsub` of the
"small" complex `fstSmall (Sph 0) (Sph q) W₁ W₂` of `Sing (S⁰ × S^q)`.  Their intersection is the
singular complex of `(W₁ ∩ W₂) × S^q = ∅`, which is acyclic, so the Mayer–Vietoris connecting map

`H^{j-1}(fstAsub ⊓ fstBsub) → H^j(fstSmall)`

is *surjective* (`Work.Cohomology.mvConnecting_surjective`), while its domain vanishes.  The two
pieces are products with the contractible one point spaces `W₁`, `W₂`, hence have the cohomology of
`S^q`, which vanishes in the relevant degrees (`Work.Sphere.sphere_subsingleton`).  Finally the
small-simplex theorem (`H_fstSmall_iso`) identifies `H^j(fstSmall)` with `H^j(S⁰ × S^q)`.

This is the `p = 0` case of the cohomology of a product of spheres, needed for the product formula
`H^*(S^p × S^q)` used in the even-dimensional part of Adams' theorem.
-/
import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.Sphere.ProdSetup
import Submission.Work.Sphere.ProdRec
import Submission.Work.Sphere.Values
import Submission.Work.Sphere.SphZeroTwoPoints
import Submission.Work.Cohomology.mvConnecting_surjective

namespace Work.Sphere

open CategoryTheory Simplicial Opposite
open scoped CategoryTheory.MonoidalCategory

noncomputable section

open Submission.Cohomology Submission.Sphere

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

/-- The cohomology of the singular complex of an empty topological space vanishes in every
degree: the complex of cochains is a complex of functions out of an empty type, hence every
cochain space is a subsingleton. -/
lemma subsingleton_H_of_isEmpty (Z : TopCat.{0}) [IsEmpty ↥Z] (m : ℕ) :
    Subsingleton (Submission.Cohomology.H (TopCat.toSSet.obj Z) ℚ m) := by
  have hZ : IsEmpty ((TopCat.toSSet.obj Z).obj (op ⦋m⦌)) := by
    refine ⟨fun g => ?_⟩
    exact isEmptyElim ((TopCat.toSSetObjEquivT Z (op ⦋m⦌)) g (basepoint m))
  have hC : Subsingleton (Cochain (TopCat.toSSet.obj Z) ℚ m) := inferInstance
  infer_instance

/-- **The vanishing of `H^j(S⁰ × S^q)` for `j ≥ 1`, `j ≠ q`.** -/
theorem H_prod_sph_zero (q j : ℕ) (hj : 1 ≤ j) (hjq : j ≠ q) :
    Subsingleton (Submission.Cohomology.H
      (TopCat.toSSet.obj (Work.Sphere.TopProd (Submission.Sphere.Sph 0) (Submission.Sphere.Sph q))) ℚ j) := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  -- The cover of `S⁰` by its two points.
  set W₁ : Set (Sph 0) := {polePt 0} with hW₁
  set W₂ : Set (Sph 0) := {negPolePt 0} with hW₂
  have hopen₁ : IsOpen W₁ := by
    rw [hW₁]
    have hD : DiscreteTopology (Sph 0) := discreteTopology_sph_zero SphZeroTwoPoints
    exact isOpen_discrete _
  have hopen₂ : IsOpen W₂ := by
    rw [hW₂]
    have hD : DiscreteTopology (Sph 0) := discreteTopology_sph_zero SphZeroTwoPoints
    exact isOpen_discrete _
  have hcov : ∀ x : ↥(Sph 0), x ∈ W₁ ∨ x ∈ W₂ := by
    intro x
    rcases SphZeroTwoPoints x with h | h
    · left; rw [hW₁]; exact h
    · right; rw [hW₂]; exact h
  -- The two points are distinct, so the two pieces of the cover are disjoint.
  have hdisj : W₁ ∩ W₂ = ∅ := by
    rw [hW₁, hW₂]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false,
      not_and]
    intro h1 h2
    exact polePt_ne_negPolePt 0 (h1.symm.trans h2)
  -- Each piece is a product with a one point space, hence has the cohomology of `S^q`.
  have hpiece₁ : Subsingleton (Submission.Cohomology.H (fstSub (Sph 0) (Sph q) W₁) ℚ (m+1)) := by
    have hC₁ : ContractibleSpace ↥W₁ := by rw [hW₁]; infer_instance
    exact subsingleton_of_linearEquiv
      (Classical.choice (H_fstSub_contractible_iso (X := Sph 0) (Y := Sph q) W₁ (m+1)))
      (sphere_subsingleton q (m+1) (by omega) hjq)
  have hpiece₂ : Subsingleton (Submission.Cohomology.H (fstSub (Sph 0) (Sph q) W₂) ℚ (m+1)) := by
    have hC₂ : ContractibleSpace ↥W₂ := by rw [hW₂]; infer_instance
    exact subsingleton_of_linearEquiv
      (Classical.choice (H_fstSub_contractible_iso (X := Sph 0) (Y := Sph q) W₂ (m+1)))
      (sphere_subsingleton q (m+1) (by omega) hjq)
  have hA : Subsingleton (Submission.Cohomology.H (fstAsub (Sph 0) (Sph q) W₁ W₂) ℚ (m+1)) :=
    subsingleton_of_linearEquiv
      (Classical.choice (H_fstAsub_iso (Sph 0) (Sph q) W₁ W₂ (m+1))) hpiece₁
  have hB : Subsingleton (Submission.Cohomology.H (fstBsub (Sph 0) (Sph q) W₁ W₂) ℚ (m+1)) :=
    subsingleton_of_linearEquiv
      (Classical.choice (H_fstBsub_iso (Sph 0) (Sph q) W₁ W₂ (m+1))) hpiece₂
  -- The Mayer–Vietoris connecting map of the pulled back cover is surjective.
  have hsurj : Function.Surjective (mvConnecting (fstSmall (Sph 0) (Sph q) W₁ W₂)
      (fstAsub (Sph 0) (Sph q) W₁ W₂) (fstBsub (Sph 0) (Sph q) W₁ W₂)
      (fstAsub_sup_fstBsub (Sph 0) (Sph q) W₁ W₂) m) :=
    Work.Cohomology.mvConnecting_surjective _ _ _ _ m hA hB
  -- Its source, the cohomology of the (empty) intersection, vanishes.
  have hdom : Subsingleton (Submission.Cohomology.H
      (↑(fstAsub (Sph 0) (Sph q) W₁ W₂ ⊓ fstBsub (Sph 0) (Sph q) W₁ W₂)) ℚ m) := by
    rw [fstAsub_inf_fstBsub]
    obtain ⟨e⟩ := H_fstCsub_homeo (Sph 0) (Sph q) W₁ W₂ m
    refine subsingleton_of_linearEquiv e ?_
    have hE : IsEmpty ↥(W₁ ∩ W₂) := by rw [hdisj]; infer_instance
    exact subsingleton_H_of_isEmpty _ m
  -- Hence the small complex is acyclic in degree `j`.
  have hsmall : Subsingleton (Submission.Cohomology.H (fstSmall (Sph 0) (Sph q) W₁ W₂) ℚ (m+1)) := by
    have hI := hdom
    exact hsurj.subsingleton
  -- The small-simplex theorem identifies it with the cohomology of `S⁰ × S^q`.
  obtain ⟨e⟩ := H_fstSmall_iso (Sph 0) (Sph q) W₁ W₂ hopen₁ hopen₂ hcov (m+1)
  exact subsingleton_of_linearEquiv e hsmall

end

end Work.Sphere
