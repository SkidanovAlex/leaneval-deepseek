/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: hSpace_sphere_iff team

# The degree shifts for a product of spheres

The general cover computation `fst_shift`/`snd_shift` of `Submission/Work/Sphere/ProdSetup.lean`,
instantiated at the two-cap covers of `S^{n+1}` and of `S^{m+1}`, gives the two degree shifts

`H^{k+1}(S^{n+1} × Y) ≅ H^k(S^n × Y)`   (`prod_fst_shift`),

`H^{k+1}(X × S^{m+1}) ≅ H^k(X × S^m)`   (`prod_snd_shift`),

valid whenever the complementary factors have vanishing cohomology in degrees `k` and `k+1`.
These are the two recursion steps of the computation of the cohomology of `S^p × S^q`.
-/
import Mathlib
import Submission.Work.Sphere.ProdSetup
import Submission.Work.Sphere.Values
import Submission.Work.Sphere.H_iso_prod
import Submission.Work.Sphere.H_iso_capPlus_prod
import Submission.Work.Sphere.sphere_doublePunctured_homotopyEquiv

open CategoryTheory Simplicial Opposite
open scoped CategoryTheory.MonoidalCategory

namespace Work.Sphere

open Submission.Cohomology Submission.Sphere

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

/-- A homotopy equivalence of the underlying spaces of two `TopCat`s gives an isomorphism of the
cohomology of their singular complexes. -/
theorem H_iso_of_homotopyEquiv' {A B : TopCat.{0}} (e : ContinuousMap.HomotopyEquiv ↥A ↥B)
    (m : ℕ) :
    Nonempty (H (TopCat.toSSet.obj A) ℚ m ≃ₗ[ℚ] H (TopCat.toSSet.obj B) ℚ m) :=
  Submission.Sphere.H_iso_of_homotopyEquiv A B (TopCat.ofHom e.toFun) (TopCat.ofHom e.invFun)
    (Classical.choice e.left_inv) (Classical.choice e.right_inv) m

/-- A product with a contractible factor is homotopy equivalent to the other factor. -/
theorem H_contractible_prod_iso {A B : TopCat.{0}} [ContractibleSpace ↥A] (m : ℕ) :
    Nonempty (H (TopCat.toSSet.obj (TopProd A B)) ℚ m ≃ₗ[ℚ]
      H (TopCat.toSSet.obj B) ℚ m) := by
  obtain ⟨e⟩ := nonempty_homotopyEquiv_prod_of_contractible ↥A ↥B
  exact H_iso_of_homotopyEquiv' e m

/-- The negative cap of `S^{p+1}` is contractible. -/
theorem capMinus_contractible (p : ℕ) : ContractibleSpace ↥(capMinus p) := by
  rw [Submission.Sphere.capMinus_eq p]
  exact Classical.choice (Work.Sphere.contractibleSpace_sph_compl (n := p+1)
    (Submission.Sphere.negPolePt (p+1)))

/-- The doubly punctured sphere `S^{n+1} \ {±e}` is homotopy equivalent to `S^n`, so a product
with it may be replaced by a product with `S^n`. -/
theorem H_DPset_prod_iso (n : ℕ) (Y : TopCat.{0}) (m : ℕ) :
    Nonempty (H (TopCat.toSSet.obj (TopProd (TopCat.of ↥(DPset n)) Y)) ℚ m
      ≃ₗ[ℚ] H (TopCat.toSSet.obj (TopProd (Sph n) Y)) ℚ m) := by
  obtain ⟨e⟩ := sphere_doublePunctured_homotopyEquiv n
  let f : TopCat.of (DPtype n) ⟶ Sph n := TopCat.ofHom e.toFun
  let g : Sph n ⟶ TopCat.of (DPtype n) := TopCat.ofHom e.invFun
  have hfg : TopCat.Homotopy (f ≫ g) (𝟙 (TopCat.of (DPtype n))) :=
    Classical.choice e.left_inv
  have hgf : TopCat.Homotopy (g ≫ f) (𝟙 (Sph n)) := Classical.choice e.right_inv
  exact H_iso_prod f g hfg hgf (𝟙 Y) (𝟙 Y) (TopCat.Homotopy.refl _) (TopCat.Homotopy.refl _) m

/-- The second-factor version: a product with the doubly punctured sphere may be replaced by a
product with `S^n`. -/
theorem H_prod_DPset_iso (X : TopCat.{0}) (n : ℕ) (m : ℕ) :
    Nonempty (H (TopCat.toSSet.obj (TopProd X (TopCat.of ↥(DPset n)))) ℚ m
      ≃ₗ[ℚ] H (TopCat.toSSet.obj (TopProd X (Sph n))) ℚ m) := by
  obtain ⟨e⟩ := sphere_doublePunctured_homotopyEquiv n
  let f : TopCat.of (DPtype n) ⟶ Sph n := TopCat.ofHom e.toFun
  let g : Sph n ⟶ TopCat.of (DPtype n) := TopCat.ofHom e.invFun
  have hfg : TopCat.Homotopy (f ≫ g) (𝟙 (TopCat.of (DPtype n))) :=
    Classical.choice e.left_inv
  have hgf : TopCat.Homotopy (g ≫ f) (𝟙 (Sph n)) := Classical.choice e.right_inv
  exact H_iso_prod (𝟙 X) (𝟙 X) (TopCat.Homotopy.refl _) (TopCat.Homotopy.refl _) f g hfg hgf m

/-- A piece of the cover coming from a contractible subset `W` is the singular complex of the
other factor. -/
theorem H_fstSub_contractible_iso {X Y : TopCat.{0}} (W : Set X) [ContractibleSpace ↥W]
    (m : ℕ) :
    Nonempty (H (fstSub X Y W) ℚ m ≃ₗ[ℚ] H (TopCat.toSSet.obj Y) ℚ m) := by
  obtain ⟨e₁⟩ := H_fstSub_homeo X Y W m
  obtain ⟨e₂⟩ := H_contractible_prod_iso (A := TopCat.of ↥W) (B := Y) m
  exact ⟨e₁.trans e₂⟩

/-- The second-factor version: a piece of the cover of `X × Y` coming from a contractible subset
of `Y` is the singular complex of `X`. -/
theorem H_prod_fstSub_contractible_iso {X Y : TopCat.{0}} (W : Set Y) [ContractibleSpace ↥W]
    (m : ℕ) :
    Nonempty (H (TopCat.toSSet.obj (TopProd X (TopCat.of ↥W))) ℚ m
      ≃ₗ[ℚ] H (TopCat.toSSet.obj X) ℚ m) := by
  obtain ⟨e₁⟩ := H_iso_of_homeo (A := TopProd X (TopCat.of ↥W))
    (B := TopProd (TopCat.of ↥W) X) (swapHomeo X (TopCat.of ↥W)) m
  obtain ⟨e₂⟩ := H_contractible_prod_iso (A := TopCat.of ↥W) (B := X) m
  exact ⟨e₁.trans e₂⟩

/-- **The degree shift in the first factor.**  If `H^k` and `H^{k+1}` of `S^q` vanish (`k ≥ 1`),
then `H^{k+1}(S^{n+1} × S^q) ≅ H^k(S^n × S^q)`. -/
theorem prod_fst_shift (n q k : ℕ) (hk : 1 ≤ k)
    (hA : Subsingleton (H (singSph q) ℚ k))
    (hA' : Subsingleton (H (singSph q) ℚ (k+1))) :
    Nonempty (H (TopCat.toSSet.obj (TopProd (Sph (n+1)) (Sph q))) ℚ (k+1) ≃ₗ[ℚ]
      H (TopCat.toSSet.obj (TopProd (Sph n) (Sph q))) ℚ k) := by
  haveI hP := capPlus_contractible n
  haveI hM := capMinus_contractible n
  have hpiece : ∀ (W : Set ↥(Sph (n+1))) [ContractibleSpace ↥W] (j : ℕ),
      Subsingleton (H (singSph q) ℚ j) →
      Subsingleton (H (fstSub (Sph (n+1)) (Sph q) W) ℚ j) :=
    fun W _ j h => subsingleton_of_linearEquiv
      (Classical.choice (H_fstSub_contractible_iso (X := Sph (n+1)) (Y := Sph q) W j)) h
  obtain ⟨e⟩ := fst_shift (Sph (n+1)) (Sph q) (capPlus n) (capMinus n)
    (isOpen_capPlus n) (isOpen_capMinus n) (fun x => Set.eq_univ_iff_forall.mp
      (capPlus_union_capMinus n) x) k hk (hpiece _ k hA) (hpiece _ k hA)
    (hpiece _ (k+1) hA') (hpiece _ (k+1) hA')
  rw [capPlus_inter_capMinus_eq_DPset n] at e
  obtain ⟨e₂⟩ := H_DPset_prod_iso n (Sph q) k
  exact ⟨e.trans e₂⟩

/-- **The degree shift in the second factor.**  If `H^k` and `H^{k+1}` of `S^p` vanish (`k ≥ 1`),
then `H^{k+1}(S^p × S^{m+1}) ≅ H^k(S^p × S^m)`. -/
theorem prod_snd_shift (p m k : ℕ) (hk : 1 ≤ k)
    (hA : Subsingleton (H (singSph p) ℚ k))
    (hA' : Subsingleton (H (singSph p) ℚ (k+1))) :
    Nonempty (H (TopCat.toSSet.obj (TopProd (Sph p) (Sph (m+1)))) ℚ (k+1) ≃ₗ[ℚ]
      H (TopCat.toSSet.obj (TopProd (Sph p) (Sph m))) ℚ k) := by
  haveI hP := capPlus_contractible m
  haveI hM := capMinus_contractible m
  have hpiece : ∀ (W : Set ↥(Sph (m+1))) [ContractibleSpace ↥W] (j : ℕ),
      Subsingleton (H (singSph p) ℚ j) →
      Subsingleton (H (TopCat.toSSet.obj (TopProd (Sph p) (TopCat.of ↥W))) ℚ j) :=
    fun W _ j h => subsingleton_of_linearEquiv
      (Classical.choice (H_prod_fstSub_contractible_iso (X := Sph p) (Y := Sph (m+1)) W j)) h
  obtain ⟨e⟩ := snd_shift (Sph p) (Sph (m+1)) (capPlus m) (capMinus m)
    (isOpen_capPlus m) (isOpen_capMinus m) (fun x => Set.eq_univ_iff_forall.mp
      (capPlus_union_capMinus m) x) k hk (hpiece _ k hA) (hpiece _ k hA)
    (hpiece _ (k+1) hA') (hpiece _ (k+1) hA')
  rw [capPlus_inter_capMinus_eq_DPset m] at e
  obtain ⟨e₂⟩ := H_prod_DPset_iso (Sph p) m k
  exact ⟨e.trans e₂⟩

end

end Work.Sphere
