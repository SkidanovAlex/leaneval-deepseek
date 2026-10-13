import Mathlib
import Submission.Work.DSEQ0.bounded_free_model_of_triangle
import Submission.Work.DSEQ0.exists_bounded_free_model

/-!
# The one-step splicing lemma for bounded finite free models

Given a short exact sequence `0 → X₁ → X₂ → X₃ → 0` of `R`-modules in which the middle term
`X₂` is a finite free module, this file proves that a *bounded model by finite free modules* of
`X₁` placed in a single degree `i` (`q : G ⟶ (single i).obj X₁` a quasi-isomorphism, `G` bounded
with finite free terms) produces a bounded model by finite free modules of `X₃` placed in the
same degree `i`: there are `P` bounded with finite free terms and a quasi-isomorphism
`g : P ⟶ (single i).obj X₃`.

## Proof

Everything happens in the derived category `D(R)`.  Placing the short exact sequence in degree
`i` (`S.map (single i)`) and taking its associated distinguished triangle produces the triangle
`Q(X₁[i]) → Q(X₂[i]) → Q(X₃[i]) →⁺`.  Rotating it moves `X₃[i]` to the *middle* vertex:

`Q(X₂[i]) → Q(X₃[i]) → Q(X₁[i])⟦1⟧ →⁺`.

The middle vertex of a distinguished triangle has a bounded finite free model as soon as its two
outer neighbours do (`Work.DSEQ0.bounded_free_model_of_triangle`, whose proof takes the model to
be the mapping cone of a lift of the connecting map).  Here a model of the first vertex is
`(single i).obj X₂` itself — `X₂` is finite free, so this complex is a bounded complex of finite
free modules — and a model of the third vertex is `G⟦1⟧`, the shift of the given model of `X₁`.
This records the classical estimate `pd X₃ ≤ pd X₁ + 1` for `0 → X₁ → X₂ → X₃ → 0` with `X₂`
free, and no Noetherian hypothesis is needed.  Finally, `P` is bounded with free terms, hence
K-projective, so the isomorphism of the derived category between `Q P` and `Q (single i X₃)` is
represented by an honest quasi-isomorphism (`Work.DSEQ0.exists_quasiIso_of_iso_Q`).
-/

namespace Work.DSEQ0.FFR

universe u

open CategoryTheory Limits Pretriangulated

set_option linter.style.haveILetI false

section Helpers

variable {R : Type u} [CommRing R]

/-- A zero object of the category of `R`-modules is a finite module. -/
private theorem moduleFinite_of_isZero {X : ModuleCat.{u} R} (hX : IsZero X) :
    Module.Finite R X := by
  haveI : Subsingleton X := ModuleCat.isZero_iff_subsingleton.mp hX
  infer_instance

/-- A zero object of the category of `R`-modules is a free module. -/
private theorem moduleFree_of_isZero {X : ModuleCat.{u} R} (hX : IsZero X) :
    Module.Free R X := by
  haveI : Subsingleton X := ModuleCat.isZero_iff_subsingleton.mp hX
  infer_instance

/-- The single-object complex on a finite free module is a bounded complex whose terms are
finite and free: it is concentrated in degree `i`. -/
private theorem single_obj_bdd_finFree (M : ModuleCat.{u} R) [Module.Finite R M]
    [Module.Free R M] (i : ℤ) :
    (∀ j, Module.Finite R
        (((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) i).obj M).X j)) ∧
      (∀ j, Module.Free R
        (((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) i).obj M).X j)) ∧
      (∃ a b : ℤ, ∀ j, j < a ∨ b < j → IsZero
        (((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) i).obj M).X j)) := by
  refine ⟨?_, ?_, ⟨i, i, ?_⟩⟩
  · intro j
    by_cases h : j = i
    · subst h; rw [HomologicalComplex.single_obj_X_self]; infer_instance
    · exact moduleFinite_of_isZero (HomologicalComplex.isZero_single_obj_X _ i M j h)
  · intro j
    by_cases h : j = i
    · subst h; rw [HomologicalComplex.single_obj_X_self]; infer_instance
    · exact moduleFree_of_isZero (HomologicalComplex.isZero_single_obj_X _ i M j h)
  · intro j hj
    rcases hj with hj | hj
    · exact HomologicalComplex.isZero_single_obj_X _ i M j (by omega)
    · exact HomologicalComplex.isZero_single_obj_X _ i M j (by omega)

/-- Shifting a bounded complex with finite free terms gives again a bounded complex with finite
free terms: the term in degree `j` of `G⟦n⟧` is the term of `G` in degree `j + n`. -/
private theorem shift_obj_bdd_finFree (G : CochainComplex (ModuleCat.{u} R) ℤ)
    (hfin : ∀ j, Module.Finite R (G.X j)) (hfree : ∀ j, Module.Free R (G.X j))
    (hbdd : ∃ a b : ℤ, ∀ j, j < a ∨ b < j → IsZero (G.X j)) (n : ℤ) :
    (∀ j, Module.Finite R ((G⟦n⟧).X j)) ∧ (∀ j, Module.Free R ((G⟦n⟧).X j)) ∧
      (∃ a b : ℤ, ∀ j, j < a ∨ b < j → IsZero ((G⟦n⟧).X j)) := by
  obtain ⟨a, b, hb⟩ := hbdd
  refine ⟨fun j => hfin (j + n), fun j => hfree (j + n), ⟨a - n, b - n, fun j hj => ?_⟩⟩
  rcases hj with hj | hj
  · exact hb (j + n) (Or.inl (by omega))
  · exact hb (j + n) (Or.inr (by omega))

end Helpers

theorem oneStep_model_of_shortExact (R : Type u) [CommRing R]
    (S : CategoryTheory.ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (hX2fin : Module.Finite R S.X₂) (hX2free : Module.Free R S.X₂) (i : ℤ)
    (G : CochainComplex (ModuleCat.{u} R) ℤ)
    (hGfin : ∀ j, Module.Finite R (G.X j)) (hGfree : ∀ j, Module.Free R (G.X j))
    (hGbdd : ∃ a b : ℤ, ∀ j, j < a ∨ b < j → CategoryTheory.Limits.IsZero (G.X j))
    (q : G ⟶ (HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) i).obj S.X₁)
    (hq : QuasiIso q) :
    ∃ (P : CochainComplex (ModuleCat.{u} R) ℤ),
      (∀ j, Module.Finite R (P.X j)) ∧ (∀ j, Module.Free R (P.X j)) ∧
      (∃ a b : ℤ, ∀ j, j < a ∨ b < j → CategoryTheory.Limits.IsZero (P.X j)) ∧
      ∃ g : P ⟶ (HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) i).obj S.X₃,
        QuasiIso g := by
  -- We work in the derived category of `R`-modules (any instance will do).
  letI : HasDerivedCategory (ModuleCat.{u} R) := HasDerivedCategory.standard _
  haveI : Module.Finite R S.X₂ := hX2fin
  haveI : Module.Free R S.X₂ := hX2free
  -- The short exact sequence of complexes obtained by placing `S` in degree `i`.
  let F := HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) i
  have hS' : (S.map F).ShortExact := hS.map_of_exact F
  -- Its distinguished triangle, rotated so that its middle vertex is `(single i).obj S.X₃`.
  let T : Triangle (DerivedCategory (ModuleCat.{u} R)) := (DerivedCategory.triangleOfSES hS').rotate
  have hT : T ∈ distTriang (DerivedCategory (ModuleCat.{u} R)) :=
    rot_of_distTriang _ (DerivedCategory.triangleOfSES_distinguished hS')
  -- The model of the first vertex is `(single i).obj S.X₂` itself: `S.X₂` is finite free, so
  -- this complex is bounded with finite free terms.  The model of the third vertex is `G⟦1⟧`.
  have hQ₁ := single_obj_bdd_finFree (R := R) S.X₂ i
  have hQ₃ := shift_obj_bdd_finFree (R := R) G hGfin hGfree hGbdd (1 : ℤ)
  -- The identification of `G⟦1⟧` with the third vertex `(Q (single i S.X₁))⟦1⟧`, through the
  -- quasi-isomorphism `q` (which becomes an isomorphism in the derived category).
  haveI : IsIso (DerivedCategory.Q.map q) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{u} R) q).mpr hq
  have e₁ : DerivedCategory.Q.obj (F.obj S.X₂) ≅ T.obj₁ := Iso.refl _
  have e₃ : DerivedCategory.Q.obj (G⟦(1 : ℤ)⟧) ≅
      (DerivedCategory.Q.obj (F.obj S.X₁))⟦(1 : ℤ)⟧ :=
    (DerivedCategory.Q.commShiftIso (1 : ℤ)).app G ≪≫
      (shiftFunctor (DerivedCategory (ModuleCat.{u} R)) (1 : ℤ)).mapIso
        (asIso (DerivedCategory.Q.map q))
  -- The middle vertex of a distinguished triangle has a bounded finite free model.
  obtain ⟨P, hPfin, hPfree, hPbdd, ⟨eiso⟩⟩ :=
    bounded_free_model_of_triangle T hT (F.obj S.X₂) (G⟦(1 : ℤ)⟧)
      hQ₁.1 hQ₁.2.1 hQ₁.2.2 hQ₃.1 hQ₃.2.1 hQ₃.2.2 e₁ e₃
  -- `P` is bounded with free terms, hence K-projective, so the isomorphism in the derived
  -- category with `(single i).obj S.X₃` is represented by an honest quasi-isomorphism.
  haveI : P.IsKProjective := isKProjective_of_bounded_free P hPfree hPbdd
  have e₂ : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj (F.obj S.X₃) := eiso
  obtain ⟨g, hg⟩ := exists_quasiIso_of_iso_Q P (F.obj S.X₃) e₂
  exact ⟨P, hPfin, hPfree, hPbdd, g, hg⟩

end Work.DSEQ0.FFR
