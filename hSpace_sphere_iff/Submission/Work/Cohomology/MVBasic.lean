/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: hSpace_sphere_iff team

# The algebra of the Mayer–Vietoris sequence, degreewise

For a simplicial set `S` and two subcomplexes `A, B ⊆ S` covering `S` (`A ⊔ B = ⊤`), the
sequence of cochain complexes

`0 ⟶ C^•(S) --α--> C^•(A) ⊕ C^•(B) --β--> C^•(A ∩ B) ⟶ 0`

is short exact.  This file contains the *degreewise* linear algebra: the two maps `mvAlpha`
(restriction to the two pieces) and `mvBeta` (difference of the restrictions), their exactness
(`mvAlpha` injective, `mvBeta` surjective, `ker mvBeta = range mvAlpha` when the cover is all of
`S`), and the compatibility with the coboundary, i.e. the fact that they are maps of cochain
complexes.  The homological consequences (the connecting map and its properties) are in
`MayerVietoris.lean`.
-/
import Mathlib
import Submission.Work.Cohomology.Chains

open CategoryTheory Simplicial Opposite

set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Cohomology

noncomputable section

variable {S : SSet.{0}}

/-! ## Pullback of cochains is a functor -/

/-- Pullback of cochains along a composite is the composite of the pullbacks. -/
lemma pullbackCo_comp {S T U : SSet.{0}} (R : Type) [CommRing R]
    (f : S ⟶ T) (g : T ⟶ U) (n : ℕ) (u : Cochain U R n) :
    pullbackCo R (f ≫ g) u = pullbackCo R f (pullbackCo R g u) := rfl

/-- The evaluation of the inclusion of a subcomplex at a simplex. -/
@[simp] lemma subcomplex_iota_apply {X : SSet.{0}} (A : X.Subcomplex) {n : ℕ}
    (σ : X.obj (op ⦋n⦌)) (h : σ ∈ A.obj (op ⦋n⦌)) :
    A.ι.app (op ⦋n⦌) ⟨σ, h⟩ = σ := rfl

/-- The dual of an injective map of `ℚ`-vector spaces is surjective. -/
lemma precomp_surjective_of_injective {α β : Type} (f : α → β) (hf : Function.Injective f) :
    Function.Surjective (precomp ℚ f) := by
  classical
  intro g
  refine ⟨fun b => if h : ∃ a, f a = b then g (Classical.choose h) else 0, ?_⟩
  funext a
  rw [precomp_apply, dif_pos (⟨a, rfl⟩ : ∃ a', f a' = f a)]
  exact congrArg g (hf (Classical.choose_spec (⟨a, rfl⟩ : ∃ a', f a' = f a)))

/-! ## The two maps of the Mayer–Vietoris sequence -/

/-- Restriction of a cochain on `S` to the two pieces `A` and `B`. -/
def mvAlpha (S : SSet.{0}) (A B : S.Subcomplex) (n : ℕ) :
    Cochain S ℚ n →ₗ[ℚ] (Cochain A ℚ n × Cochain B ℚ n) :=
  (precomp ℚ (A.ι.app (op ⦋n⦌))).prod (precomp ℚ (B.ι.app (op ⦋n⦌)))

/-- The difference of the restrictions of a pair of cochains on `A` and `B` to their
intersection. -/
def mvBeta (S : SSet.{0}) (A B : S.Subcomplex) (n : ℕ) :
    (Cochain A ℚ n × Cochain B ℚ n) →ₗ[ℚ] Cochain (A ⊓ B : S.Subcomplex) ℚ n :=
  (precomp ℚ (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A) |>.app (op ⦋n⦌))).comp
      (LinearMap.fst ℚ _ _)
    - (precomp ℚ (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B) |>.app (op ⦋n⦌))).comp
      (LinearMap.snd ℚ _ _)

/-- The differential of the product of the cochain complexes of the two pieces. -/
def mvD (S : SSet.{0}) (A B : S.Subcomplex) (n : ℕ) :
    (Cochain A ℚ n × Cochain B ℚ n) →ₗ[ℚ] (Cochain A ℚ (n+1) × Cochain B ℚ (n+1)) :=
  ((coboundary A ℚ n).comp (LinearMap.fst ℚ _ _)).prod
    ((coboundary B ℚ n).comp (LinearMap.snd ℚ _ _))

@[simp] lemma mvAlpha_fst (S : SSet.{0}) (A B : S.Subcomplex) (n : ℕ)
    (u : Cochain S ℚ n) : (mvAlpha S A B n u).1 = pullbackCo ℚ A.ι u := rfl

@[simp] lemma mvAlpha_snd (S : SSet.{0}) (A B : S.Subcomplex) (n : ℕ)
    (u : Cochain S ℚ n) : (mvAlpha S A B n u).2 = pullbackCo ℚ B.ι u := rfl

@[simp] lemma mvBeta_apply (S : SSet.{0}) (A B : S.Subcomplex) (n : ℕ)
    (p : Cochain A ℚ n × Cochain B ℚ n) :
    mvBeta S A B n p = pullbackCo ℚ (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A)) p.1 -
      pullbackCo ℚ (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B)) p.2 := rfl

@[simp] lemma mvD_fst (S : SSet.{0}) (A B : S.Subcomplex) (n : ℕ)
    (p : Cochain A ℚ n × Cochain B ℚ n) :
    (mvD S A B n p).1 = coboundary A ℚ n p.1 := rfl

@[simp] lemma mvD_snd (S : SSet.{0}) (A B : S.Subcomplex) (n : ℕ)
    (p : Cochain A ℚ n × Cochain B ℚ n) :
    (mvD S A B n p).2 = coboundary B ℚ n p.2 := rfl

/-! ## Exactness -/

/-- A cochain on `S` whose restrictions to both pieces vanish is zero, when the two pieces cover
`S`. -/
theorem mvAlpha_injective (S : SSet.{0}) (A B : S.Subcomplex) (hAB : A ⊔ B = ⊤) (n : ℕ) :
    Function.Injective (mvAlpha S A B n) := by
  intro u v huv
  funext σ
  have hσ : σ ∈ ((A ⊔ B).obj (op ⦋n⦌) : Set (S.obj (op ⦋n⦌))) := by
    rw [hAB]; trivial
  rw [Subfunctor.max_obj] at hσ
  have h1 : pullbackCo ℚ A.ι u = pullbackCo ℚ A.ι v := congrArg Prod.fst huv
  have h2 : pullbackCo ℚ B.ι u = pullbackCo ℚ B.ι v := congrArg Prod.snd huv
  rcases hσ with h | h
  · have := congrFun h1 ⟨σ, h⟩
    simpa using this
  · have := congrFun h2 ⟨σ, h⟩
    simpa using this

/-- A cochain on the intersection of the pieces glues to a pair of cochains on the pieces. -/
theorem mvBeta_surjective (S : SSet.{0}) (A B : S.Subcomplex) (n : ℕ) :
    Function.Surjective (mvBeta S A B n) := by
  intro c
  have hf : Function.Injective (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A) |>.app
      (op ⦋n⦌)) := by
    intro x y hxy
    exact Subtype.ext (by simpa using congrArg Subtype.val hxy)
  obtain ⟨u, hu⟩ := precomp_surjective_of_injective
    (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A) |>.app (op ⦋n⦌)) hf c
  refine ⟨(u, 0), ?_⟩
  rw [mvBeta_apply]
  rw [show pullbackCo ℚ (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A)) u
      = precomp ℚ (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A) |>.app (op ⦋n⦌)) u
        from rfl]
  rw [show pullbackCo ℚ (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B)) (0 : Cochain B ℚ n)
      = 0 from rfl]
  rw [hu, sub_zero]

/-- The composite of the two maps of the Mayer–Vietoris sequence is zero. -/
theorem mvBeta_comp_mvAlpha (S : SSet.{0}) (A B : S.Subcomplex) (n : ℕ) :
    (mvBeta S A B n).comp (mvAlpha S A B n) = 0 := by
  ext u σ
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, mvBeta_apply, mvAlpha_fst, mvAlpha_snd,
    Pi.sub_apply, pullbackCo_apply]
  have h1 : A.ι.app (op ⦋n⦌)
      (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A) |>.app (op ⦋n⦌) σ)
      = (A ⊓ B).ι.app (op ⦋n⦌) σ := rfl
  have h2 : B.ι.app (op ⦋n⦌)
      (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B) |>.app (op ⦋n⦌) σ)
      = (A ⊓ B).ι.app (op ⦋n⦌) σ := rfl
  rw [h1, h2, sub_self]
  rfl

/-! ## Compatibility with the coboundary -/

lemma mvAlpha_coboundary (S : SSet.{0}) (A B : S.Subcomplex) (n : ℕ) (u : Cochain S ℚ n) :
    mvAlpha S A B (n+1) (coboundary S ℚ n u) = mvD S A B n (mvAlpha S A B n u) := by
  apply Prod.ext
  · simp only [mvAlpha_fst, mvD_fst]
    rw [pullbackCo_coboundary]
  · simp only [mvAlpha_snd, mvD_snd]
    rw [pullbackCo_coboundary]

lemma mvBeta_coboundary (S : SSet.{0}) (A B : S.Subcomplex) (n : ℕ)
    (p : Cochain A ℚ n × Cochain B ℚ n) :
    mvBeta S A B (n+1) (mvD S A B n p)
      = coboundary (A ⊓ B : S.Subcomplex) ℚ n (mvBeta S A B n p) := by
  simp only [mvBeta_apply, mvD_fst, mvD_snd, pullbackCo_coboundary, map_sub]

/-- `∂² = 0` for the product of the two cochain complexes. -/
lemma mvD_mvD (S : SSet.{0}) (A B : S.Subcomplex) (n : ℕ)
    (p : Cochain A ℚ n × Cochain B ℚ n) :
    mvD S A B (n+1) (mvD S A B n p) = 0 := by
  apply Prod.ext <;> funext σ <;> simp [coboundary_coboundary]

end

end Submission.Cohomology
