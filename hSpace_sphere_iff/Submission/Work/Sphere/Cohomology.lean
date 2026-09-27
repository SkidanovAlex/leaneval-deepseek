/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: hSpace_sphere_iff team

# The cohomology of the two caps of `S^{n+1}`

The two open caps `capPlus n`, `capMinus n` of `Sph (n+1)` (`Sphere/Basic.lean`) are contractible
(`Work.Sphere.contractibleSpace_sph_compl`), so their rational cohomology vanishes in positive
degrees.  Here we transport this statement to the subcomplexes `singIn (Sph (n+1)) (capPlus n)` of
the singular complex of `S^{n+1}`, which are the two pieces of the Mayer–Vietoris cover.  The
transport uses the isomorphism `singIn X W ≅ Sing W` of `Work.Cohomology.singIn_iso`.
-/
import Mathlib
import Submission.Work.Cohomology.MVApply
import Submission.Work.Cohomology.singIn_iso
import Submission.Work.Cohomology.H_map_comp
import Submission.Work.Sphere.Basic
import Submission.Work.Sphere.contractibleSpace_sph_compl

open CategoryTheory Simplicial Opposite

set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Sphere

open Submission.Cohomology

/-! ## The two caps as punctured spheres -/

lemma capPlus_eq (n : ℕ) : (capPlus n : Set (Sph (n+1))) = {x | x ≠ polePt (n+1)} := by
  ext x
  constructor
  · intro h hx
    exact h (congrArg Subtype.val hx)
  · intro h hc
    exact h (Subtype.ext hc)

lemma capMinus_eq (n : ℕ) : (capMinus n : Set (Sph (n+1))) = {x | x ≠ negPolePt (n+1)} := by
  ext x
  constructor
  · intro h hx
    exact h (congrArg Subtype.val hx)
  · intro h hc
    exact h (Subtype.ext hc)

/-! ## Transport along the subspace identification -/

/-- If the cohomology of the subspace `W` vanishes in degree `m`, then so does the cohomology of
the subcomplex `singIn X W` of the singular complex of `X`. -/
theorem subsingleton_singIn {X : TopCat.{0}} {W : Set X} {m : ℕ}
    (h : Subsingleton (H (TopCat.toSSet.obj (TopCat.of W)) ℚ m)) :
    Subsingleton (H (singIn X W) ℚ m) := by
  obtain ⟨e⟩ := Work.Cohomology.singIn_iso X W
  have hsurj : Function.Surjective (H.map ℚ e.hom m) := by
    intro y
    refine ⟨H.map ℚ e.inv m y, ?_⟩
    rw [← Work.Cohomology.H_map_comp e.hom e.inv m y, Iso.hom_inv_id, H.map_id]
    rfl
  exact ⟨fun a b => by
    obtain ⟨a', rfl⟩ := hsurj a
    obtain ⟨b', rfl⟩ := hsurj b
    rw [Subsingleton.elim a' b']⟩

/-! ## Vanishing in positive degrees -/

/-- The cohomology of the cap `capPlus n` vanishes in positive degrees, as a subcomplex of the
singular complex of `Sph (n+1)`. -/
theorem subsingleton_H_capPlus_singIn (n m : ℕ) (hm : 0 < m) :
    Subsingleton (H (singIn (Sph (n+1)) (capPlus n)) ℚ m) := by
  refine subsingleton_singIn ?_
  have hcon : ContractibleSpace ↥(capPlus n) := by
    rw [capPlus_eq]
    exact Classical.choice (Work.Sphere.contractibleSpace_sph_compl (n := n+1) (polePt (n+1)))
  exact Work.Cohomology.H_subsingleton_of_contractible (TopCat.of ↥(capPlus n)) hcon ℚ hm

/-- The cohomology of the cap `capMinus n` vanishes in positive degrees, as a subcomplex of the
singular complex of `Sph (n+1)`. -/
theorem subsingleton_H_capMinus_singIn (n m : ℕ) (hm : 0 < m) :
    Subsingleton (H (singIn (Sph (n+1)) (capMinus n)) ℚ m) := by
  refine subsingleton_singIn ?_
  have hcon : ContractibleSpace ↥(capMinus n) := by
    rw [capMinus_eq]
    exact Classical.choice (Work.Sphere.contractibleSpace_sph_compl (n := n+1)
      (negPolePt (n+1)))
  exact Work.Cohomology.H_subsingleton_of_contractible (TopCat.of ↥(capMinus n)) hcon ℚ hm

end Submission.Sphere
