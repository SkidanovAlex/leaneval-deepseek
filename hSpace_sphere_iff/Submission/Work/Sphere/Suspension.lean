/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# The cohomology of the spheres: the degree-shift isomorphism

For `n ≥ 1` and `k ≥ 2` there is an isomorphism
`H (S^{n+1}; ℚ) k ≃ H (S^n; ℚ) (k-1)`.

It is assembled from four ingredients:

* the small-simplex theorem (`Work.Cohomology.small_simplex_injective`/`_surjective`), which
  identifies `H (Sing X)` with the cohomology of the subcomplex `small` of simplices lying in
  one of the two caps;
* the Mayer–Vietoris collapse (`Work.Cohomology.mvConnecting_injective`/`_surjective`) applied to
  the cover of `small` by the two preimages of the caps, which are acyclic in positive degrees;
* `Work.Cohomology.singIn_iso`, identifying the simplices of `Sing X` lying in a subset `W` with
  the singular complex of `W`, applied to `W` = the doubly punctured sphere;
* the homotopy equivalence `Work.Sphere.sphere_doublePunctured_homotopyEquiv` between the doubly
  punctured sphere and `S^n`.
-/
import Mathlib
import Submission.Work.Cohomology.MVApply
import Submission.Work.Cohomology.singIn_iso
import Submission.Work.Cohomology.H_map_comp
import Submission.Work.Cohomology.small_simplex_injective
import Submission.Work.Cohomology.small_simplex_surjective
import Submission.Work.Cohomology.mvConnecting_injective
import Submission.Work.Cohomology.mvConnecting_surjective
import Submission.Work.Sphere.Basic
import Submission.Work.Sphere.Cohomology
import Submission.Work.Sphere.sphere_doublePunctured_homotopyEquiv

open CategoryTheory Simplicial Opposite
open SSet

namespace Submission.Sphere

open Submission.Cohomology

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

/-! ## Plumbing

The two general facts about our cohomology used throughout: it is invariant under isomorphism of
simplicial sets and under homotopy equivalence of spaces, and a vanishing group transfers across
an isomorphism. -/

/-- The subcomplex `A.preimage B.ι` of `B` is isomorphic to `A` when `A ≤ B`. -/
noncomputable def preimageIso {X : SSet.{0}} (B A : X.Subcomplex) (h : A ≤ B) :
    (A.preimage B.ι : SSet.{0}) ≅ (A : SSet.{0}) := by
  have hf : SSet.Subcomplex.range (SSet.Subcomplex.homOfLE h) ≤ A.preimage B.ι := by
    intro n x hx
    obtain ⟨y, hy⟩ := hx
    subst hy
    change B.ι.app n ((SSet.Subcomplex.homOfLE h).app n y) ∈ A.obj n
    have h1 : B.ι.app n ((SSet.Subcomplex.homOfLE h).app n y) = (A.ι.app n) y := rfl
    rw [h1]
    exact y.2
  refine Iso.mk (A.fromPreimage B.ι) (SSet.Subcomplex.lift (SSet.Subcomplex.homOfLE h) hf) ?_ ?_
  · apply (cancel_mono (SSet.Subcomplex.ι (A.preimage B.ι))).mp
    rw [Category.assoc, SSet.Subcomplex.lift_ι, Category.id_comp]
    apply (cancel_mono B.ι).mp
    rw [Category.assoc, SSet.Subcomplex.homOfLE_ι]
    exact SSet.Subcomplex.fromPreimage_ι A B.ι
  · apply (cancel_mono (SSet.Subcomplex.ι A)).mp
    rw [Category.assoc, SSet.Subcomplex.fromPreimage_ι, ← Category.assoc,
      SSet.Subcomplex.lift_ι]
    rw [SSet.Subcomplex.homOfLE_ι, Category.id_comp]

/-- Our cohomology is invariant under isomorphism of simplicial sets. -/
theorem H_iso_of_iso {A B : SSet.{0}} (e : A ≅ B) (m : ℕ) :
    Nonempty (H A ℚ m ≃ₗ[ℚ] H B ℚ m) := by
  have h1 : ∀ y : H B ℚ m, H.map ℚ e.inv m (H.map ℚ e.hom m y) = y := by
    intro y
    rw [← Work.Cohomology.H_map_comp e.inv e.hom m y, Iso.inv_hom_id, H.map_id]
    rfl
  have h2 : ∀ x : H A ℚ m, H.map ℚ e.hom m (H.map ℚ e.inv m x) = x := by
    intro x
    rw [← Work.Cohomology.H_map_comp e.hom e.inv m x, Iso.hom_inv_id, H.map_id]
    rfl
  refine ⟨LinearEquiv.ofBijective (H.map ℚ e.inv m) ⟨?_, ?_⟩⟩
  · intro x y hxy
    rw [← h2 x, ← h2 y, hxy]
  · intro y
    exact ⟨H.map ℚ e.hom m y, h1 y⟩

/-- Our cohomology is invariant under homotopy equivalence of spaces. -/
theorem H_iso_of_homotopyEquiv (X Y : TopCat.{0}) (f : X ⟶ Y) (g : Y ⟶ X)
    (hfg : TopCat.Homotopy (CategoryTheory.CategoryStruct.comp f g)
      (CategoryTheory.CategoryStruct.id X))
    (hgf : TopCat.Homotopy (CategoryTheory.CategoryStruct.comp g f)
      (CategoryTheory.CategoryStruct.id Y)) (m : ℕ) :
    Nonempty (H (TopCat.toSSet.obj X) ℚ m ≃ₗ[ℚ] H (TopCat.toSSet.obj Y) ℚ m) := by
  have hmc₁ : TopCat.toSSet.map g ≫ TopCat.toSSet.map f
      = TopCat.toSSet.map (CategoryTheory.CategoryStruct.comp g f) :=
    (Functor.map_comp (self := TopCat.toSSet) g f).symm
  have hmc₂ : TopCat.toSSet.map f ≫ TopCat.toSSet.map g
      = TopCat.toSSet.map (CategoryTheory.CategoryStruct.comp f g) :=
    (Functor.map_comp (self := TopCat.toSSet) f g).symm
  have hgf' : SSet.Homotopy (TopCat.toSSet.map (CategoryTheory.CategoryStruct.comp g f))
      (CategoryTheory.CategoryStruct.id (TopCat.toSSet.obj Y)) := by
    simpa using (TopCat.Homotopy.toSSet hgf)
  have hfg' : SSet.Homotopy (TopCat.toSSet.map (CategoryTheory.CategoryStruct.comp f g))
      (CategoryTheory.CategoryStruct.id (TopCat.toSSet.obj X)) := by
    simpa using (TopCat.Homotopy.toSSet hfg)
  have h1 : ∀ x : H (TopCat.toSSet.obj Y) ℚ m,
      H.map ℚ (TopCat.toSSet.map g) m (H.map ℚ (TopCat.toSSet.map f) m x) = x := by
    intro x
    rw [← Work.Cohomology.H_map_comp (TopCat.toSSet.map g) (TopCat.toSSet.map f) m x, hmc₁,
      Work.Cohomology.H_map_homotopic hgf' m, H.map_id]
    rfl
  have h2 : ∀ y : H (TopCat.toSSet.obj X) ℚ m,
      H.map ℚ (TopCat.toSSet.map f) m (H.map ℚ (TopCat.toSSet.map g) m y) = y := by
    intro y
    rw [← Work.Cohomology.H_map_comp (TopCat.toSSet.map f) (TopCat.toSSet.map g) m y, hmc₂,
      Work.Cohomology.H_map_homotopic hfg' m, H.map_id]
    rfl
  refine ⟨(LinearEquiv.ofBijective (H.map ℚ (TopCat.toSSet.map f) m) ⟨?_, ?_⟩).symm⟩
  · intro x y hxy
    rw [← h1 x, ← h1 y, hxy]
  · intro y
    exact ⟨H.map ℚ (TopCat.toSSet.map g) m y, h2 y⟩

/-- A vanishing cohomology group transfers across an isomorphism of simplicial sets. -/
theorem subsingleton_H_of_iso {A B : SSet.{0}} (e : A ≅ B) {m : ℕ}
    (h : Subsingleton (H B ℚ m)) : Subsingleton (H A ℚ m) := by
  have hsurj : Function.Surjective (H.map ℚ e.hom m) := by
    intro y
    refine ⟨H.map ℚ e.inv m y, ?_⟩
    rw [← Work.Cohomology.H_map_comp e.hom e.inv m y, Iso.hom_inv_id, H.map_id]
    rfl
  exact ⟨fun a b => by
    obtain ⟨a', rfl⟩ := hsurj a
    obtain ⟨b', rfl⟩ := hsurj b
    rw [Subsingleton.elim a' b']⟩

/-! ## The two-cap cover of `S^{n+1}` and the Mayer–Vietoris comparison -/

/-- The singular complex of `Sⁿ`. -/
abbrev singSph (n : ℕ) : SSet.{0} := TopCat.toSSet.obj (Sph n)

/-- The subcomplex of simplices of `S^{n+1}` lying in the positive cap. -/
abbrev capPlusSub (n : ℕ) : (singSph (n+1)).Subcomplex := singIn (Sph (n+1)) (capPlus n)

/-- The subcomplex of simplices of `S^{n+1}` lying in the negative cap. -/
abbrev capMinusSub (n : ℕ) : (singSph (n+1)).Subcomplex := singIn (Sph (n+1)) (capMinus n)

/-- The subcomplex of "small" simplices: those lying in one of the two caps. -/
abbrev smallSub (n : ℕ) : (singSph (n+1)).Subcomplex := capPlusSub n ⊔ capMinusSub n

/-- The doubly punctured sphere, as a set of points of `S^{n+1}` (in the point form matching
`Work.Sphere.sphere_doublePunctured_homotopyEquiv`). -/
def DPset (n : ℕ) : Set (Sph (n+1)) :=
  {x | x ≠ polePt (n+1)} ∩ {x | x ≠ negPolePt (n+1)}

/-- The intersection of the two caps is the doubly punctured sphere. -/
theorem capPlus_inter_capMinus_eq_DPset (n : ℕ) : capPlus n ∩ capMinus n = DPset n := by
  rw [capPlus_eq, capMinus_eq]
  rfl

/-- The doubly punctured sphere, in the two equivalent descriptions. -/
theorem DPset_eq_doublePunctured (n : ℕ) : DPset n = doublePunctured n := by
  rw [← capPlus_inter_capMinus_eq_DPset]
  exact capPlus_inter_capMinus n

/-- The doubly punctured sphere is contained in the positive cap. -/
theorem DPset_subset_capPlus (n : ℕ) : DPset n ⊆ capPlus n := by
  intro x hx
  rw [← capPlus_inter_capMinus_eq_DPset] at hx
  exact hx.1

/-- The small complex, as a simplicial set (so that `Subcomplex` can be applied to it). -/
abbrev smallC (n : ℕ) : SSet.{0} := (smallSub n : SSet.{0})

/-- The first piece of the Mayer–Vietoris cover of the small complex of `S^{n+1}`. -/
abbrev capAsub (n : ℕ) : (smallC n).Subcomplex := (capPlusSub n).preimage (smallSub n).ι

/-- The second piece of the Mayer–Vietoris cover of the small complex of `S^{n+1}`. -/
abbrev capBsub (n : ℕ) : (smallC n).Subcomplex := (capMinusSub n).preimage (smallSub n).ι

/-- The intersection of the two pieces of the cover. -/
abbrev capCsub (n : ℕ) : (smallC n).Subcomplex :=
  (singIn (Sph (n+1)) (DPset n)).preimage (smallSub n).ι

/-- The two pieces of the cover of the small complex indeed cover it. -/
theorem capAsub_sup_capBsub (n : ℕ) : capAsub n ⊔ capBsub n = ⊤ := by
  rw [← SSet.Subcomplex.preimage_max, SSet.Subcomplex.preimage_ι]

/-- The intersection of the two pieces of the cover is the doubly punctured sphere. -/
theorem capAsub_inf_capBsub (n : ℕ) : capAsub n ⊓ capBsub n = capCsub n := by
  rw [← SSet.Subcomplex.preimage_min, ← singIn_inter, capPlus_inter_capMinus_eq_DPset]

/-- The positive cap is acyclic in positive degrees, as a piece of the cover. -/
theorem subsingleton_H_capAsub (n m : ℕ) (hm : 0 < m) : Subsingleton (H (capAsub n) ℚ m) :=
  subsingleton_H_of_iso (preimageIso (smallSub n) (capPlusSub n) le_sup_left)
    (subsingleton_H_capPlus_singIn n m hm)

/-- The negative cap is acyclic in positive degrees, as a piece of the cover. -/
theorem subsingleton_H_capBsub (n m : ℕ) (hm : 0 < m) : Subsingleton (H (capBsub n) ℚ m) :=
  subsingleton_H_of_iso (preimageIso (smallSub n) (capMinusSub n) le_sup_right)
    (subsingleton_H_capMinus_singIn n m hm)

/-- The small-simplex theorem: `H (Sing S^{n+1}) ≅ H (small)`. -/
noncomputable def smallSphereIso (n m : ℕ) :
    H (smallSub n) ℚ m ≃ₗ[ℚ] H (singSph (n+1)) ℚ m :=
  (LinearEquiv.ofBijective (H.map ℚ (smallSub n).ι m)
    ⟨Work.Cohomology.small_simplex_injective (Sph (n+1)) (capPlus n) (capMinus n)
        (isOpen_capPlus n) (isOpen_capMinus n)
        (fun x => Set.eq_univ_iff_forall.mp (capPlus_union_capMinus n) x) m,
     Work.Cohomology.small_simplex_surjective (Sph (n+1)) (capPlus n) (capMinus n)
        (isOpen_capPlus n) (isOpen_capMinus n)
        (fun x => Set.eq_univ_iff_forall.mp (capPlus_union_capMinus n) x) m⟩).symm

/-- The Mayer–Vietoris collapse: for `m ≥ 1` the connecting map is an isomorphism. -/
noncomputable def mvSphere (n m : ℕ) (hm : 1 ≤ m) :
    H (smallSub n) ℚ (m+1) ≃ₗ[ℚ] H (capAsub n ⊓ capBsub n : (smallC n).Subcomplex) ℚ m :=
  (LinearEquiv.ofBijective
    (mvConnecting (smallSub n) (capAsub n) (capBsub n) (capAsub_sup_capBsub n) m)
    ⟨Work.Cohomology.mvConnecting_injective (smallSub n) (capAsub n) (capBsub n)
        (capAsub_sup_capBsub n) m hm
        (subsingleton_H_capAsub n m (by omega)) (subsingleton_H_capBsub n m (by omega)),
     Work.Cohomology.mvConnecting_surjective (smallSub n) (capAsub n) (capBsub n)
        (capAsub_sup_capBsub n) m
        (subsingleton_H_capAsub n (m+1) (by omega))
        (subsingleton_H_capBsub n (m+1) (by omega))⟩).symm

/-- The intersection of the two pieces is the subcomplex of the doubly punctured sphere. -/
noncomputable def capCIso (n m : ℕ) :
    H (capAsub n ⊓ capBsub n : (smallC n).Subcomplex) ℚ m ≃ₗ[ℚ] H (capCsub n) ℚ m :=
  Classical.choice (H_iso_of_iso
    (SSet.Subcomplex.eqToIso (capAsub_inf_capBsub n)) m)

/-- The doubly punctured sphere, as a type in the form used by the homotopy equivalence. -/
abbrev DPtype (n : ℕ) : Type :=
  {x : ↥(Sph (n+1)) // x ≠ polePt (n+1) ∧ x ≠ negPolePt (n+1)}

/-- The two descriptions of the doubly punctured sphere give the same cohomology. -/
noncomputable def dpTypeIso (n m : ℕ) :
    H (TopCat.toSSet.obj (TopCat.of (↥(DPset n)))) ℚ m
      ≃ₗ[ℚ] H (TopCat.toSSet.obj (TopCat.of (DPtype n))) ℚ m :=
  LinearEquiv.refl ℚ _

/-- The doubly punctured sphere, as a subcomplex of the singular complex of `S^{n+1}`, is the
singular complex of the doubly punctured sphere as a space. -/
noncomputable def dpSpaceIso (n m : ℕ) :
    H (singIn (Sph (n+1)) (DPset n)) ℚ m ≃ₗ[ℚ]
      H (TopCat.toSSet.obj (TopCat.of (DPtype n))) ℚ m :=
  (Classical.choice (H_iso_of_iso
    (Classical.choice (Work.Cohomology.singIn_iso (Sph (n+1)) (DPset n))) m)).trans
    (dpTypeIso n m)

/-- The preimage piece is the doubly punctured sphere. -/
noncomputable def capPrimeIso (n m : ℕ) :
    H (capCsub n) ℚ m ≃ₗ[ℚ] H (singIn (Sph (n+1)) (DPset n)) ℚ m :=
  Classical.choice (H_iso_of_iso (preimageIso (smallSub n) (singIn (Sph (n+1)) (DPset n))
    (le_trans (singIn_mono (DPset_subset_capPlus n)) le_sup_left)) m)

/-- The doubly punctured sphere is homotopy equivalent to `Sⁿ`, so its cohomology agrees. -/
noncomputable def dpSphereIso (n m : ℕ) :
    H (TopCat.toSSet.obj (TopCat.of (DPtype n))) ℚ m ≃ₗ[ℚ] H (singSph n) ℚ m := by
  classical
  let e := Classical.choice (Work.Sphere.sphere_doublePunctured_homotopyEquiv n)
  let f : TopCat.of (DPtype n) ⟶ Sph n := TopCat.ofHom e.toFun
  let g : Sph n ⟶ TopCat.of (DPtype n) := TopCat.ofHom e.invFun
  have hfg : TopCat.Homotopy (CategoryTheory.CategoryStruct.comp f g)
      (CategoryTheory.CategoryStruct.id (TopCat.of (DPtype n))) :=
    Classical.choice e.left_inv
  have hgf : TopCat.Homotopy (CategoryTheory.CategoryStruct.comp g f)
      (CategoryTheory.CategoryStruct.id (Sph n)) :=
    Classical.choice e.right_inv
  exact Classical.choice (H_iso_of_homotopyEquiv _ _ f g hfg hgf m)

/-- **The degree-shift isomorphism for the cohomology of the spheres.**  For `m ≥ 1` the
cohomology of `S^{n+1}` in degree `m+1` is the cohomology of `Sⁿ` in degree `m`. -/
theorem sphere_shift (n m : ℕ) (hm : 1 ≤ m) :
    Nonempty (H (singSph (n+1)) ℚ (m+1) ≃ₗ[ℚ] H (singSph n) ℚ m) :=
  ⟨(smallSphereIso n (m+1)).symm.trans ((mvSphere n m hm).trans
    ((capCIso n m).trans ((capPrimeIso n m).trans ((dpSpaceIso n m).trans (dpSphereIso n m)))))⟩

end

end Submission.Sphere
