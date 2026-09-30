import Mathlib
import Submission.Work.SSSR.serreE1Defs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open scoped Simplicial
open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
private lemma fin2_eq_one_of_ne_zero {a : Fin 2} (h : a ≠ 0) : a = 1 := by
  fin_cases a <;> simp_all

/-- The horn `Λ[1,0]` is the subcomplex of `Δ[1]` supported at the vertex `0`,
i.e. the `0`-th face `face {0}`. -/
lemma horn_one_zero_eq_face :
    (SSet.horn 1 0 : (Δ[1] : SSet).Subcomplex) =
      SSet.stdSimplex.face ({0} : Finset (Fin 2)) := by
  ext m x
  rw [SSet.mem_horn_iff_notMem_range, SSet.stdSimplex.mem_face_iff]
  constructor
  · rintro ⟨j, hj, hjr⟩ i
    have hj1 : j = 1 := by fin_cases j <;> simp_all
    subst hj1
    by_contra hne
    simp only [Finset.mem_singleton] at hne
    exact hjr ⟨i, fin2_eq_one_of_ne_zero hne⟩
  · intro h
    refine ⟨1, by decide, ?_⟩
    rintro ⟨i, hi⟩
    have := h i
    simp only [Finset.mem_singleton] at this
    rw [this] at hi
    exact absurd hi (by decide)

/-- The vertex `0` of `Δ[1]`, as a `0`-simplex. -/
abbrev hornV.{u} : (Δ[1] : SSet.{u}) _⦋0⦌ := (SSet.stdSimplex.obj₀Equiv (n := 1)).symm 0

/-- **The endpoint inclusion `X ⟶ X ⊗ Δ[1]` is an anodyne extension.**
In the category of simplicial sets (with its cartesian monoidal structure, so
`X ⊗ Δ[1]` is `X × Δ[1]`), the inclusion `SSet.ι₀ : X ⟶ X ⊗ Δ[1]` of the `0`-end of
the prism is an anodyne extension `SSet.anodyneExtensions` (i.e. has the left lifting
property against all Kan fibrations).  This is the `whiskering` of the horn inclusion
`Λ[1,0].ι : Λ[1,0] ⟶ Δ[1]` (which is the inclusion of the vertex `0`, so `Λ[1,0] ≅ Δ[0]`)
with `X`, using `SSet.anodyneExtensions.horn_ι` and
`SSet.anodyneExtensions.whiskerLeft`/`whiskerRight`, plus transport along the
isomorphism `X ⊗ Λ[1,0] ≅ X`. -/
theorem anodyneIota0 {X : SSet.{0}} :
    SSet.anodyneExtensions (SSet.ι₀ (X := X)) := by
  -- `Λ[1,0] ≅ Δ[0]`, and the composite `Λ[1,0] ⟶ Δ[1]` is the constant map at `0`:
  -- this identifies `X ◁ Λ[1,0].ι` with the whiskering of the constant map `Δ[0] ⟶ Δ[1]`.
  have he : (SSet.stdSimplex.faceSingletonIso (0 : Fin 2)).hom
      ≫ (SSet.stdSimplex.face ({0} : Finset (Fin 2))).ι
      = SSet.const (X := Δ[0]) hornV := by
    rw [SSet.stdSimplex.faceSingletonIso_zero_hom_comp_ι_eq_δ, SSet.stdSimplex.δ_one_eq_const]
  have hface : (SSet.stdSimplex.faceSingletonIso (0 : Fin 2)).inv
      ≫ SSet.const (X := Δ[0]) hornV
      = (SSet.stdSimplex.face ({0} : Finset (Fin 2))).ι := by
    rw [← he, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  -- `X ◁ horn.ι` is anodyne, and up to the isomorphism `X ◁ (faceSingletonIso 0).inv`
  -- it is the whiskering `X ◁ const 0`.
  have h1 : SSet.anodyneExtensions (X ◁ SSet.const (X := Δ[0]) hornV) := by
    rw [← MorphismProperty.cancel_left_of_respectsIso SSet.anodyneExtensions
      (X ◁ (SSet.stdSimplex.faceSingletonIso (0 : Fin 2)).inv)
      (X ◁ SSet.const (X := Δ[0]) hornV)]
    rw [← whiskerLeft_comp, hface, ← horn_one_zero_eq_face]
    exact SSet.anodyneExtensions.whiskerLeft (SSet.anodyneExtensions.horn_ι (0 : Fin 2)) X
  -- `X ◁ const 0` is `fst ≫ ι₀`, and `fst : X ⊗ Δ[0] ⟶ X` is an isomorphism because
  -- `Δ[0]` is terminal.
  have hXc : X ◁ SSet.const (X := Δ[0]) hornV
      = SemiCartesianMonoidalCategory.fst X (Δ[0] : SSet) ≫ SSet.ι₀ (X := X) := by
    apply NatTrans.ext
    funext m
    ext x
    obtain ⟨y, t⟩ := x
    simp only [SSet.comp_app]
    congr 1
  have hfst : IsIso (SemiCartesianMonoidalCategory.fst X (Δ[0] : SSet)) := by
    refine (BinaryFan.isLimit_iff_isIso_fst (SSet.stdSimplex.isTerminalObj₀)
      (BinaryFan.mk (SemiCartesianMonoidalCategory.fst X (Δ[0] : SSet))
        (SemiCartesianMonoidalCategory.snd X (Δ[0] : SSet)))).1 ⟨?_⟩
    exact CartesianMonoidalCategory.tensorProductIsBinaryProduct X (Δ[0] : SSet)
  have hkey : (asIso (SemiCartesianMonoidalCategory.fst X (Δ[0] : SSet))).inv
      ≫ (X ◁ SSet.const (X := Δ[0]) hornV) = SSet.ι₀ (X := X) := by
    rw [hXc, ← Category.assoc, asIso_inv, IsIso.inv_hom_id, Category.id_comp]
  have h2 : SSet.anodyneExtensions
      ((asIso (SemiCartesianMonoidalCategory.fst X (Δ[0] : SSet))).inv
        ≫ (X ◁ SSet.const (X := Δ[0]) hornV)) :=
    (MorphismProperty.cancel_left_of_respectsIso SSet.anodyneExtensions
      (asIso (SemiCartesianMonoidalCategory.fst X (Δ[0] : SSet))).inv
      (X ◁ SSet.const (X := Δ[0]) hornV)).2 h1
  rwa [hkey] at h2

end Work.SSSR
