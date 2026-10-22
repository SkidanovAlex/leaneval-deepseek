/-
# Restriction along an embedding `up ℤ → up ℤ` preserves quasi-isomorphisms

Let `e : ComplexShape.Embedding (up ℤ) (up ℤ)` satisfy `e.IsRelIff`.  The main result is
`Work.RESOL.quasiIso_restrictionMap`: if `φ : K ⟶ L` is a quasi-isomorphism of cochain
complexes of an abelian category `A`, then so is the restricted map
`HomologicalComplex.restrictionMap φ e : K.restriction e ⟶ L.restriction e`.

The mathematical content is that `e.IsRelIff` forces `e` to be a shift of the indexing:
`e.f (j - 1) = e.f j - 1` and `e.f (j + 1) = e.f j + 1` (lemmas `e_f_prev`/`e_f_next`
below).  Consequently the short complex `(K.restriction e).sc' i j k` is the short complex
`K.sc' (e.f i) (e.f j) (e.f k)` up to a re-indexing of the objects, and `restrictionMap`
is, under this identification, just `φ` itself.  Since `QuasiIsoAt` is defined through
`shortComplexFunctor'`, this reduces the statement to the fact that a quasi-isomorphism
stays a quasi-isomorphism after such a re-indexing.

The two `set_option`s below mirror `Mathlib/Algebra/Homology/Embedding/RestrictionHomology.lean`:
they are needed because `(K.restriction e).X i` is only *definitionally* equal to
`K.X (e.f i)`.
-/
import Mathlib

open CategoryTheory Limits HomologicalComplex

set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Work.RESOL

variable {A : Type*} [CategoryTheory.Category A] [CategoryTheory.Abelian A]
variable (e : ComplexShape.Embedding (ComplexShape.up ℤ) (ComplexShape.up ℤ)) [e.IsRelIff]

/-! ## The embedding `e` is a shift of the indices -/

lemma up_prev_eq (j : ℤ) : (ComplexShape.up ℤ).prev j = j - 1 :=
  (ComplexShape.up ℤ).prev_eq' (ComplexShape.up_mk (j - 1) j (by ring))

lemma up_next_eq (j : ℤ) : (ComplexShape.up ℤ).next j = j + 1 :=
  (ComplexShape.up ℤ).next_eq' (ComplexShape.up_mk j (j + 1) (by ring))

/-- An `IsRelIff` embedding of `up ℤ` into itself commutes with the predecessor. -/
lemma e_f_prev (j : ℤ) :
    e.f ((ComplexShape.up ℤ).prev j) = (ComplexShape.up ℤ).prev (e.f j) := by
  rw [up_prev_eq, up_prev_eq]
  have h2 : e.f (j - 1) + 1 = e.f j := by
    have := (e.rel_iff (j - 1) j).2 (ComplexShape.up_mk (j - 1) j (by ring))
    simpa [ComplexShape.up_Rel] using this
  omega

/-- An `IsRelIff` embedding of `up ℤ` into itself commutes with the successor. -/
lemma e_f_next (j : ℤ) :
    e.f ((ComplexShape.up ℤ).next j) = (ComplexShape.up ℤ).next (e.f j) := by
  rw [up_next_eq, up_next_eq]
  have h2 : e.f j + 1 = e.f (j + 1) := by
    have := (e.rel_iff j (j + 1)).2 (ComplexShape.up_mk j (j + 1) (by ring))
    simpa [ComplexShape.up_Rel] using this
  omega

/-! ## The re-indexing of the short complexes -/

/-- The short complex `(K.restriction e).sc' i j k` is the short complex
`K.sc' (e.f i) (e.f j) (e.f k)` with the objects re-indexed. -/
def scIso (K : CochainComplex A ℤ) (i j k : ℤ) :
    (K.restriction e).sc' i j k ≅ K.sc' (e.f i) (e.f j) (e.f k) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp)

/-- Under the re-indexing `scIso`, the map induced by `restrictionMap φ e` on a short
complex is the map induced by `φ`. -/
def arrowIso (K L : CochainComplex A ℤ) (φ : K ⟶ L) (i j k : ℤ) :
    Arrow.mk ((shortComplexFunctor' A (ComplexShape.up ℤ) i j k).map
        (HomologicalComplex.restrictionMap φ e)) ≅
      Arrow.mk ((shortComplexFunctor' A (ComplexShape.up ℤ) (e.f i) (e.f j) (e.f k)).map φ) :=
  Arrow.isoMk (scIso e K i j k) (scIso e L i j k) (by
    ext <;>
      simp only [Arrow.mk_hom,
        ShortComplex.comp_τ₁, ShortComplex.comp_τ₂, ShortComplex.comp_τ₃,
        HomologicalComplex.shortComplexFunctor'_map_τ₁,
        HomologicalComplex.shortComplexFunctor'_map_τ₂,
        HomologicalComplex.shortComplexFunctor'_map_τ₃,
        HomologicalComplex.restrictionMap_f,
        scIso, ShortComplex.isoMk_hom_τ₁, ShortComplex.isoMk_hom_τ₂, ShortComplex.isoMk_hom_τ₃,
        Iso.refl_hom]
    all_goals simp)

/-- Restricting cochain complexes of an abelian category along an embedding of the shape
`up ℤ` into itself (satisfying `IsRelIff`) preserves quasi-isomorphisms. -/
theorem quasiIso_restrictionMap {A : Type*} [CategoryTheory.Category A]
    [CategoryTheory.Abelian A]
    (e : ComplexShape.Embedding (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [e.IsRelIff] {K L : CochainComplex A ℤ} (φ : K ⟶ L) (hφ : QuasiIso φ) :
    QuasiIso (HomologicalComplex.restrictionMap φ e) := by
  refine ⟨fun j => ?_⟩
  refine (quasiIsoAt_iff' (HomologicalComplex.restrictionMap φ e) ((ComplexShape.up ℤ).prev j) j
    ((ComplexShape.up ℤ).next j) rfl rfl).2 ?_
  refine (ShortComplex.quasiIso_iff_of_arrow_mk_iso _ _
    (arrowIso e K L φ ((ComplexShape.up ℤ).prev j) j ((ComplexShape.up ℤ).next j))).2 ?_
  exact (quasiIsoAt_iff' φ (e.f ((ComplexShape.up ℤ).prev j)) (e.f j)
    (e.f ((ComplexShape.up ℤ).next j)) (e_f_prev e j).symm (e_f_next e j).symm).1
      (hφ.quasiIsoAt (e.f j))

end Work.RESOL
