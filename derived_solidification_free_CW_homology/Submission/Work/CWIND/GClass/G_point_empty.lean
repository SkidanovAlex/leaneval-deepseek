import Mathlib
import Submission.Work.CWIND.Basic

namespace Work.CWIND.GClass

open CategoryTheory CategoryTheory.Limits LightCondensed LightProfinite
open LightCondensed.Solid Submission.Blueprint

/-! ## Two auxiliary lemmas

The base cases of the CW induction are proved by showing that for a space with at most one point the
comparison map `b.app X` is an *isomorphism* of cochain complexes.  We record the two ingredients
separately: `solidEquiv_of_isIso` (an isomorphism of the derived category is a solid-equivalence,
proved here directly from the definition of `SolidEquiv`, i.e. the `of_iso` field of `ToolkitProp`)
and `isIso_b_app_of_subsingleton` (the comparison map is an isomorphism for a subsingleton space). -/

/-- A morphism `f` of the derived category that is an isomorphism is a solid-equivalence:
precomposition with `f` on morphisms into any object is a bijection, with inverse given by
precomposition with `inv f`.  This is the `of_iso` field of `Submission.Blueprint.ToolkitProp`,
proved directly from the definition of `SolidEquiv`. -/
theorem solidEquiv_of_isIso {X Y : DLightCondAb} (f : X ⟶ Y) [IsIso f] : SolidEquiv f := by
  intro N
  refine ⟨fun a b h ↦ ?_, fun v ↦ ⟨inv f ≫ v, ?_⟩⟩
  · have h' := congrArg (fun t ↦ inv f ≫ t) h
    simpa using h'
  · simp

/-- **CWIND/T11, the key step.**  For a space `X` with at most one point, the comparison map
`b.app X : C_sing(X) ⟶ A(X)` is an isomorphism of cochain complexes.  Every component is:

* in degree `-n` with `n : ℕ`, the composite `(CXIso X n).inv ≫ bLevel X n ≫ (AXIso X n).inv` of the
  canonical extension isomorphisms and the level-`n` comparison map `bLevel X n`, which is an
  isomorphism by `hL`;
* in positive degrees, a morphism between zero objects: the singular chain complex is the extension
  of an `ℕ`-indexed complex (hence vanishes in positive degrees) and `A X` is concentrated in
  degrees `≤ 0`. -/
theorem isIso_b_app_of_subsingleton
    (b : singularChainsLightCondAbComplexFunctor ⟶ AFunctor)
    (hb : ∀ (X : TopCat.{0}) (n : ℕ),
      (b.app X).f (-(n : ℤ)) = (CXIso X n).inv ≫ bLevel X n ≫ (AXIso X n).inv)
    (hL : ∀ (X : TopCat.{0}) [Subsingleton ↥X] (n : ℕ), IsIso (bLevel X n))
    (X : TopCat.{0}) [Subsingleton ↥X] : IsIso (b.app X) := by
  have hcomp : ∀ q : ℤ, IsIso ((b.app X).f q) := by
    intro q
    rcases lt_or_ge (0 : ℤ) q with hq | hq
    · -- positive degree: a map between zero objects
      refine IsZero.isIso ?_ ?_ ((b.app X).f q)
      · exact HomologicalComplex.isZero_extend_X (Work.CWIND.Csrc X) ComplexShape.embeddingDownNat q
          (by
            intro n hn
            rw [ComplexShape.embeddingDownNat_f] at hn
            omega)
      · exact isZero_A_X_of_pos X hq
    · -- non-positive degrees are of the form `-n` with `n : ℕ`
      have hn : ((((-q).toNat : ℕ)) : ℤ) = -q := Int.toNat_of_nonneg (by omega)
      have hq' : q = -((((-q).toNat : ℕ)) : ℤ) := by omega
      rw [hq', hb X (-q).toNat]
      exact IsIso.comp_isIso' (CXIso X (-q).toNat).isIso_inv
        (IsIso.comp_isIso' (hL X (-q).toNat) (AXIso X (-q).toNat).isIso_inv)
  exact HomologicalComplex.Hom.isIso_of_components (b.app X)

/-- For a space `X` with at most one point, `Q (b.app X)` is a solid-equivalence: `b.app X` is an
isomorphism of complexes by `isIso_b_app_of_subsingleton`, hence so is its image under the
localisation functor `Q`, and an isomorphism of the derived category is a solid-equivalence. -/
theorem solidEquiv_b_app_of_subsingleton
    (b : singularChainsLightCondAbComplexFunctor ⟶ AFunctor)
    (hb : ∀ (X : TopCat.{0}) (n : ℕ),
      (b.app X).f (-(n : ℤ)) = (CXIso X n).inv ≫ bLevel X n ≫ (AXIso X n).inv)
    (hL : ∀ (X : TopCat.{0}) [Subsingleton ↥X] (n : ℕ), IsIso (bLevel X n))
    (X : TopCat.{0}) [Subsingleton ↥X] :
    SolidEquiv ((DerivedCategory.Q).map (b.app X)) := by
  have hbIso : IsIso (b.app X) := isIso_b_app_of_subsingleton b hb hL X
  have hIso : IsIso ((DerivedCategory.Q).map (b.app X)) := Functor.map_isIso _ (b.app X)
  exact solidEquiv_of_isIso _

/-- **CWIND/T11 (the base cases of the CW induction).**  The one-point space and the empty space lie
in `GOf b` for any comparison map `b` whose components are the prescribed maps `bLevel`.  Both
spaces are Hausdorff; for a space with at most one point each component `bLevel X n` is an
isomorphism (`hL`), and the remaining components of `b.app X` are maps between zero objects, so
`Q (b.app X)` is an isomorphism and in particular a solid-equivalence. -/
theorem G_point_empty
    (b : singularChainsLightCondAbComplexFunctor ⟶ AFunctor)
    (hb : ∀ (X : TopCat.{0}) (n : ℕ),
      (b.app X).f (-(n : ℤ)) = (CXIso X n).inv ≫ bLevel X n ≫ (AXIso X n).inv)
    (hL : ∀ (X : TopCat.{0}) [Subsingleton ↥X] (n : ℕ), IsIso (bLevel X n)) :
    GOf b (TopCat.of PUnit) ∧ GOf b (TopCat.of PEmpty) := by
  constructor
  · exact ⟨inferInstance, solidEquiv_b_app_of_subsingleton b hb hL (TopCat.of PUnit)⟩
  · exact ⟨inferInstance, solidEquiv_b_app_of_subsingleton b hb hL (TopCat.of PEmpty)⟩

end Work.CWIND.GClass
