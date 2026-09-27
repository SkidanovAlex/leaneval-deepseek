/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: hSpace_sphere_iff team

# The two-piece cover of a product `X × Y` coming from one factor

This is the technical heart of the computation of the cohomology of a product of spheres.  For
topological spaces `X`, `Y` and a two-piece open cover `X = W₁ ∪ W₂` we consider the induced open
cover of `X × Y` by `{p | p.1 ∈ W₁}` and `{p | p.1 ∈ W₂}`.  The subcomplex

`small := singIn (X × Y) {p | p.1 ∈ W₁} ⊔ singIn (X × Y) {p | p.1 ∈ W₂}`

of the singular complex `Sing (X × Y)` has the same cohomology as `Sing (X × Y)` (the
small-simplex theorem, `small_simplex_injective`/`small_simplex_surjective`), and the two pieces of
its Mayer–Vietoris cover `A`, `B` are the singular complexes of `W₁ × Y` resp. `W₂ × Y`, while the
intersection `A ⊓ B` is the singular complex of `(W₁ ∩ W₂) × Y`.

Consequence (`fst_shift`): if `H^k` and `H^{k+1}` of the two pieces vanish (`k ≥ 1`), the
connecting map of the Mayer–Vietoris sequence of the cover of `small` is an isomorphism

`H^{k+1}(X × Y) ≅ H^k((W₁ ∩ W₂) × Y)`.

The dual statement for a cover of the *second* factor is derived from this one by the swap
homeomorphism `X × Y ≃ Y × X` (`snd_shift`).
-/
import Mathlib
import Submission.Work.Sphere.Suspension
import Submission.Work.Cohomology.singIn_iso
import Submission.Work.Cohomology.H_map_comp
import Submission.Work.Cohomology.small_simplex_injective
import Submission.Work.Cohomology.small_simplex_surjective
import Submission.Work.Cohomology.mvAlphaH_ker_eq_range
import Submission.Work.Cohomology.mvBetaH_ker_eq_range
import Submission.Work.Cohomology.mvConnecting_ker_eq_range
import Submission.Work.Cohomology.mvConnecting_injective
import Submission.Work.Cohomology.mvConnecting_surjective

open CategoryTheory Simplicial Opposite
open scoped CategoryTheory.MonoidalCategory

namespace Work.Sphere

open Submission.Cohomology

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

/-- The product of two topological spaces, as a `TopCat`, with its carrier written as the honest
product of carriers (so that projections `.1`, `.2` are available definitionally). -/
abbrev TopProd (X Y : TopCat.{0}) : TopCat := TopCat.of ((↥X) × (↥Y))

/-- Our cohomology is invariant under homeomorphism of spaces. -/
theorem H_iso_of_homeo {A B : TopCat.{0}} (e : ↥A ≃ₜ ↥B) (m : ℕ) :
    Nonempty (H (TopCat.toSSet.obj A) ℚ m ≃ₗ[ℚ] H (TopCat.toSSet.obj B) ℚ m) := by
  let f : A ⟶ B := TopCat.ofHom (⟨e, e.continuous_toFun⟩ : C(↥A, ↥B))
  let g : B ⟶ A := TopCat.ofHom (⟨e.symm, e.symm.continuous_toFun⟩ : C(↥B, ↥A))
  have h1 : f ≫ g = 𝟙 A := by ext x; simp [f, g]
  have h2 : g ≫ f = 𝟙 B := by ext x; simp [f, g]
  exact Submission.Sphere.H_iso_of_homotopyEquiv A B f g
    (by rw [h1]; exact TopCat.Homotopy.refl _)
    (by rw [h2]; exact TopCat.Homotopy.refl _) m

/-! ## The cover of `X × Y` pulled back from the first factor -/

section Cover

variable (X Y : TopCat.{0})

/-- The subset of `X × Y` whose first coordinate lies in `W`. -/
def fstSet (W : Set X) : Set (TopProd X Y) := {p | p.1 ∈ W}

lemma mem_fstSet {W : Set X} {p : ↥(TopProd X Y)} : p ∈ fstSet X Y W ↔ p.1 ∈ W := Iff.rfl

lemma fstSet_mono {W W' : Set X} (h : W ⊆ W') : fstSet X Y W ⊆ fstSet X Y W' :=
  fun _ hp => h hp

lemma fstSet_union (W₁ W₂ : Set X) :
    fstSet X Y (W₁ ∪ W₂) = fstSet X Y W₁ ∪ fstSet X Y W₂ := by
  ext p; exact ⟨fun h => h.elim Or.inl Or.inr, fun h => h.elim Or.inl Or.inr⟩

lemma fstSet_inter (W₁ W₂ : Set X) :
    fstSet X Y (W₁ ∩ W₂) = fstSet X Y W₁ ∩ fstSet X Y W₂ := by
  ext p; exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

lemma isOpen_fstSet {W : Set X} (h : IsOpen W) : IsOpen (fstSet X Y W) :=
  h.preimage continuous_fst

/-- The subcomplex of `Sing (X × Y)` of the simplices lying in `{p | p.1 ∈ W}`. -/
abbrev fstSub (W : Set X) : (TopCat.toSSet.obj (TopProd X Y)).Subcomplex :=
  singIn (TopProd X Y) (fstSet X Y W)

/-- The "small" subcomplex of `Sing (X × Y)` for the cover pulled back from the first factor. -/
abbrev fstSmall (W₁ W₂ : Set X) : (TopCat.toSSet.obj (TopProd X Y)).Subcomplex :=
  fstSub X Y W₁ ⊔ fstSub X Y W₂

/-- The first piece of the Mayer–Vietoris cover of the small complex. -/
abbrev fstAsub (W₁ W₂ : Set X) : ((fstSmall X Y W₁ W₂) : SSet.{0}).Subcomplex :=
  (fstSub X Y W₁).preimage (fstSmall X Y W₁ W₂).ι

/-- The second piece of the Mayer–Vietoris cover of the small complex. -/
abbrev fstBsub (W₁ W₂ : Set X) : ((fstSmall X Y W₁ W₂) : SSet.{0}).Subcomplex :=
  (fstSub X Y W₂).preimage (fstSmall X Y W₁ W₂).ι

/-- The intersection of the two pieces. -/
abbrev fstCsub (W₁ W₂ : Set X) : ((fstSmall X Y W₁ W₂) : SSet.{0}).Subcomplex :=
  (fstSub X Y (W₁ ∩ W₂)).preimage (fstSmall X Y W₁ W₂).ι

/-- The two pieces of the cover of the small complex cover it. -/
theorem fstAsub_sup_fstBsub (W₁ W₂ : Set X) : fstAsub X Y W₁ W₂ ⊔ fstBsub X Y W₁ W₂ = ⊤ := by
  rw [← SSet.Subcomplex.preimage_max, SSet.Subcomplex.preimage_ι]

/-- The intersection of the two pieces is the subcomplex of `(W₁ ∩ W₂) × Y`. -/
theorem fstAsub_inf_fstBsub (W₁ W₂ : Set X) :
    fstAsub X Y W₁ W₂ ⊓ fstBsub X Y W₁ W₂ = fstCsub X Y W₁ W₂ := by
  rw [← SSet.Subcomplex.preimage_min, ← singIn_inter, ← fstSet_inter]

/-- The homeomorphism underlying the identification of `{p | p.1 ∈ W}` with `W × Y`. -/
def fstHomeo (W : Set X) : ↥(fstSet X Y W) ≃ₜ ↥W × ↥Y where
  toFun p := (⟨p.1.1, p.2⟩, p.1.2)
  invFun q := ⟨(q.1.1, q.2), q.1.2⟩
  left_inv p := by ext <;> rfl
  right_inv q := by ext <;> rfl
  continuous_toFun := Continuous.prodMk
    (Continuous.subtype_mk (Continuous.fst continuous_subtype_val) _)
    (Continuous.snd continuous_subtype_val)
  continuous_invFun := Continuous.subtype_mk
    (Continuous.prodMk (continuous_subtype_val.comp continuous_fst) continuous_snd) _

/-- The realisation of a piece of the cover as the singular complex of `W × Y`. -/
theorem H_fstSub_homeo (W : Set X) (m : ℕ) :
    Nonempty (H (fstSub X Y W) ℚ m ≃ₗ[ℚ]
      H (TopCat.toSSet.obj (TopProd (TopCat.of ↥W) Y)) ℚ m) := by
  obtain ⟨e₁⟩ := Work.Cohomology.singIn_iso (TopProd X Y) (fstSet X Y W)
  obtain ⟨e₂⟩ := Submission.Sphere.H_iso_of_iso e₁ m
  obtain ⟨e₃⟩ := H_iso_of_homeo (A := TopCat.of ↥(fstSet X Y W))
    (B := TopProd (TopCat.of ↥W) Y) (fstHomeo X Y W) m
  exact ⟨e₂.trans e₃⟩

/-- The realisation of the intersection piece as the singular complex of `(W₁ ∩ W₂) × Y`. -/
theorem H_fstCsub_homeo (W₁ W₂ : Set X) (m : ℕ) :
    Nonempty (H (fstCsub X Y W₁ W₂) ℚ m ≃ₗ[ℚ]
      H (TopCat.toSSet.obj (TopProd (TopCat.of ↥(W₁ ∩ W₂)) Y)) ℚ m) := by
  have hle : fstSub X Y (W₁ ∩ W₂) ≤ fstSmall X Y W₁ W₂ :=
    le_trans (singIn_mono (fstSet_mono X Y Set.inter_subset_left)) le_sup_left
  obtain ⟨e₁⟩ := Submission.Sphere.H_iso_of_iso
    (Submission.Sphere.preimageIso (fstSmall X Y W₁ W₂) (fstSub X Y (W₁ ∩ W₂)) hle) m
  obtain ⟨e₂⟩ := H_fstSub_homeo X Y (W₁ ∩ W₂) m
  exact ⟨e₁.trans e₂⟩

/-- The first piece of the cover, as the singular complex of `W₁ × Y`. -/
theorem H_fstAsub_iso (W₁ W₂ : Set X) (m : ℕ) :
    Nonempty (H (fstAsub X Y W₁ W₂) ℚ m ≃ₗ[ℚ] H (fstSub X Y W₁) ℚ m) :=
  Submission.Sphere.H_iso_of_iso (Submission.Sphere.preimageIso (fstSmall X Y W₁ W₂) (fstSub X Y W₁) le_sup_left) m

/-- The second piece of the cover, as the singular complex of `W₂ × Y`. -/
theorem H_fstBsub_iso (W₁ W₂ : Set X) (m : ℕ) :
    Nonempty (H (fstBsub X Y W₁ W₂) ℚ m ≃ₗ[ℚ] H (fstSub X Y W₂) ℚ m) :=
  Submission.Sphere.H_iso_of_iso (Submission.Sphere.preimageIso (fstSmall X Y W₁ W₂) (fstSub X Y W₂) le_sup_right) m

/-- The small-simplex theorem for the cover of `X × Y`: the cohomology of the small complex is
that of `Sing (X × Y)`. -/
theorem H_fstSmall_iso (W₁ W₂ : Set X) (h₁ : IsOpen W₁) (h₂ : IsOpen W₂)
    (hcov : ∀ x : ↥X, x ∈ W₁ ∨ x ∈ W₂) (m : ℕ) :
    Nonempty (H (TopCat.toSSet.obj (TopProd X Y)) ℚ m ≃ₗ[ℚ] H (fstSmall X Y W₁ W₂) ℚ m) :=
  ⟨LinearEquiv.ofBijective (H.map ℚ (fstSmall X Y W₁ W₂).ι m)
    ⟨Work.Cohomology.small_simplex_injective (TopProd X Y) (fstSet X Y W₁) (fstSet X Y W₂)
        (isOpen_fstSet X Y h₁) (isOpen_fstSet X Y h₂)
        (fun p => (hcov p.1).elim Or.inl Or.inr) m,
     Work.Cohomology.small_simplex_surjective (TopProd X Y) (fstSet X Y W₁) (fstSet X Y W₂)
        (isOpen_fstSet X Y h₁) (isOpen_fstSet X Y h₂)
        (fun p => (hcov p.1).elim Or.inl Or.inr) m⟩⟩

end Cover

/-! ## The Mayer–Vietoris connecting map is an isomorphism for an acyclic cover -/

/-- If the two pieces of a covering pair are acyclic in degrees `k` and `k+1` (`k ≥ 1`), the
connecting map of the Mayer–Vietoris sequence is an isomorphism
`H^k(A ⊓ B) ≅ H^{k+1}(S)`. -/
theorem mvConnecting_iso (S : SSet.{0}) (A B : S.Subcomplex) (hAB : A ⊔ B = ⊤) (k : ℕ)
    (hk : 1 ≤ k) (hA : Subsingleton (H A ℚ k)) (hB : Subsingleton (H B ℚ k))
    (hA' : Subsingleton (H A ℚ (k+1))) (hB' : Subsingleton (H B ℚ (k+1))) :
    Nonempty (H (A ⊓ B : S.Subcomplex) ℚ k ≃ₗ[ℚ] H S ℚ (k+1)) :=
  ⟨LinearEquiv.ofBijective _
    ⟨Work.Cohomology.mvConnecting_injective S A B hAB k hk hA hB,
     Work.Cohomology.mvConnecting_surjective S A B hAB k hA' hB'⟩⟩

/-- `Subsingleton` transfers across a `ℚ`-linear equivalence. -/
theorem subsingleton_of_linearEquiv {V W : Type*} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W] (e : V ≃ₗ[ℚ] W) (h : Subsingleton W) : Subsingleton V :=
  ⟨fun x y => e.injective (Subsingleton.elim _ _)⟩

/-! ## The degree shift in the first factor -/

/-- **The degree shift for a product cover.**  If the two pieces `W₁ × Y` and `W₂ × Y` of the
cover of `X × Y` pulled back from a two-piece open cover `X = W₁ ∪ W₂` are acyclic in degrees `k`
and `k+1` (`k ≥ 1`), then `H^{k+1}(X × Y) ≅ H^k((W₁ ∩ W₂) × Y)`. -/
theorem fst_shift (X Y : TopCat.{0}) (W₁ W₂ : Set X) (h₁ : IsOpen W₁) (h₂ : IsOpen W₂)
    (hcov : ∀ x : ↥X, x ∈ W₁ ∨ x ∈ W₂) (k : ℕ) (hk : 1 ≤ k)
    (hA : Subsingleton (H (fstSub X Y W₁) ℚ k))
    (hB : Subsingleton (H (fstSub X Y W₂) ℚ k))
    (hA' : Subsingleton (H (fstSub X Y W₁) ℚ (k+1)))
    (hB' : Subsingleton (H (fstSub X Y W₂) ℚ (k+1))) :
    Nonempty (H (TopCat.toSSet.obj (TopProd X Y)) ℚ (k+1) ≃ₗ[ℚ]
      H (TopCat.toSSet.obj (TopProd (TopCat.of ↥(W₁ ∩ W₂)) Y)) ℚ k) := by
  have hA'' : Subsingleton (H (fstAsub X Y W₁ W₂) ℚ k) :=
    subsingleton_of_linearEquiv (Classical.choice (H_fstAsub_iso X Y W₁ W₂ k)) hA
  have hB'' : Subsingleton (H (fstBsub X Y W₁ W₂) ℚ k) :=
    subsingleton_of_linearEquiv (Classical.choice (H_fstBsub_iso X Y W₁ W₂ k)) hB
  have hA3 : Subsingleton (H (fstAsub X Y W₁ W₂) ℚ (k+1)) :=
    subsingleton_of_linearEquiv (Classical.choice (H_fstAsub_iso X Y W₁ W₂ (k+1))) hA'
  have hB3 : Subsingleton (H (fstBsub X Y W₁ W₂) ℚ (k+1)) :=
    subsingleton_of_linearEquiv (Classical.choice (H_fstBsub_iso X Y W₁ W₂ (k+1))) hB'
  obtain ⟨eSmall⟩ := H_fstSmall_iso X Y W₁ W₂ h₁ h₂ hcov (k+1)
  obtain ⟨eConn⟩ := mvConnecting_iso (fstSmall X Y W₁ W₂) (fstAsub X Y W₁ W₂)
    (fstBsub X Y W₁ W₂) (fstAsub_sup_fstBsub X Y W₁ W₂) k hk hA'' hB'' hA3 hB3
  obtain ⟨eEq⟩ := Submission.Sphere.H_iso_of_iso
    (SSet.Subcomplex.eqToIso (fstAsub_inf_fstBsub X Y W₁ W₂)) k
  obtain ⟨eC⟩ := H_fstCsub_homeo X Y W₁ W₂ k
  exact ⟨eSmall.trans (eConn.symm.trans (eEq.trans eC))⟩

/-! ## The degree shift in the second factor -/

/-- The swap homeomorphism `X × Y ≃ Y × X`. -/
def swapHomeo (X Y : TopCat.{0}) : ↥(TopProd X Y) ≃ₜ ↥(TopProd Y X) where
  toFun p := (p.2, p.1)
  invFun p := (p.2, p.1)
  left_inv p := by ext <;> rfl
  right_inv p := by ext <;> rfl
  continuous_toFun := Continuous.prodMk continuous_snd continuous_fst
  continuous_invFun := Continuous.prodMk continuous_snd continuous_fst

/-- **The degree shift for a product cover, second factor.**  If the two pieces `X × W₁` and
`X × W₂` of the cover of `X × Y` pulled back from a two-piece open cover `Y = W₁ ∪ W₂` are acyclic
in degrees `k` and `k+1` (`k ≥ 1`), then `H^{k+1}(X × Y) ≅ H^k(X × (W₁ ∩ W₂))`. -/
theorem snd_shift (X Y : TopCat.{0}) (W₁ W₂ : Set Y) (h₁ : IsOpen W₁) (h₂ : IsOpen W₂)
    (hcov : ∀ x : ↥Y, x ∈ W₁ ∨ x ∈ W₂) (k : ℕ) (hk : 1 ≤ k)
    (hA : Subsingleton (H (TopCat.toSSet.obj (TopProd X (TopCat.of ↥W₁))) ℚ k))
    (hB : Subsingleton (H (TopCat.toSSet.obj (TopProd X (TopCat.of ↥W₂))) ℚ k))
    (hA' : Subsingleton (H (TopCat.toSSet.obj (TopProd X (TopCat.of ↥W₁))) ℚ (k+1)))
    (hB' : Subsingleton (H (TopCat.toSSet.obj (TopProd X (TopCat.of ↥W₂))) ℚ (k+1))) :
    Nonempty (H (TopCat.toSSet.obj (TopProd X Y)) ℚ (k+1) ≃ₗ[ℚ]
      H (TopCat.toSSet.obj (TopProd X (TopCat.of ↥(W₁ ∩ W₂)))) ℚ k) := by
  have hA1 : Subsingleton (H (fstSub Y X W₁) ℚ k) :=
    subsingleton_of_linearEquiv (Classical.choice (H_fstSub_homeo Y X W₁ k))
      (subsingleton_of_linearEquiv
        (Classical.choice (H_iso_of_homeo (swapHomeo X (TopCat.of ↥W₁)) k)).symm hA)
  have hB1 : Subsingleton (H (fstSub Y X W₂) ℚ k) :=
    subsingleton_of_linearEquiv (Classical.choice (H_fstSub_homeo Y X W₂ k))
      (subsingleton_of_linearEquiv
        (Classical.choice (H_iso_of_homeo (swapHomeo X (TopCat.of ↥W₂)) k)).symm hB)
  have hA1' : Subsingleton (H (fstSub Y X W₁) ℚ (k+1)) :=
    subsingleton_of_linearEquiv (Classical.choice (H_fstSub_homeo Y X W₁ (k+1)))
      (subsingleton_of_linearEquiv
        (Classical.choice (H_iso_of_homeo (swapHomeo X (TopCat.of ↥W₁)) (k+1))).symm hA')
  have hB1' : Subsingleton (H (fstSub Y X W₂) ℚ (k+1)) :=
    subsingleton_of_linearEquiv (Classical.choice (H_fstSub_homeo Y X W₂ (k+1)))
      (subsingleton_of_linearEquiv
        (Classical.choice (H_iso_of_homeo (swapHomeo X (TopCat.of ↥W₂)) (k+1))).symm hB')
  obtain ⟨e1⟩ := fst_shift Y X W₁ W₂ h₁ h₂ hcov k hk hA1 hB1 hA1' hB1'
  obtain ⟨e0⟩ := H_iso_of_homeo (A := TopProd X Y) (B := TopProd Y X) (swapHomeo X Y) (k+1)
  obtain ⟨e2⟩ := H_iso_of_homeo (A := TopProd (TopCat.of ↥(W₁ ∩ W₂)) X)
    (B := TopProd X (TopCat.of ↥(W₁ ∩ W₂))) (swapHomeo (TopCat.of ↥(W₁ ∩ W₂)) X) k
  exact ⟨e0.trans (e1.trans e2)⟩

/-! ## The singular complex of a product of spheres -/

/-- The singular complex of a product of spaces is the product of the singular complexes: this is
the isomorphism through which the general statements about `singSph p ⊗ singSph q` are read. -/
theorem H_tensor_homeo (X Y : TopCat.{0}) (m : ℕ) :
    Nonempty (H (CategoryTheory.MonoidalCategoryStruct.tensorObj
        (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y)) ℚ m ≃ₗ[ℚ]
      H (TopCat.toSSet.obj (TopProd X Y)) ℚ m) :=
  Submission.Sphere.H_iso_of_iso
    (CategoryTheory.Functor.Monoidal.μIso TopCat.toSSet X Y) m

end

end Work.Sphere
