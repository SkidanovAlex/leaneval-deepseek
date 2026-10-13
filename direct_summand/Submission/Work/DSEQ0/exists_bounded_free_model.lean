import Mathlib
import Submission.Work.DSEQ0.Model
import Submission.Work.DSEQ0.bounded_free_model_of_triangle
import Submission.Work.DSEQ0.bounded_free_model_of_shortExact

namespace Work.DSEQ0

universe u

open CategoryTheory Limits

section Helpers

variable {A : Type u} [CommRing A]

/-- A bounded complex of free `A`-modules is K-projective (bounded above with free, hence
projective, terms). -/
lemma isKProjective_of_bounded_free (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (hfree : ∀ j, Module.Free A (K.X j))
    (hbdd : ∃ a b : ℤ, ∀ j, j < a ∨ b < j → IsZero (K.X j)) :
    K.IsKProjective := by
  obtain ⟨a, b, hb⟩ := hbdd
  haveI : K.IsStrictlyLE b :=
    (CochainComplex.isStrictlyLE_iff K b).mpr (fun i hi => hb i (Or.inr hi))
  haveI : ∀ j, Projective (K.X j) := fun j => by
    haveI : Module.Free A (K.X j) := hfree j
    infer_instance
  exact CochainComplex.isKProjective_of_projective K b

/-- If `K` is K-projective, an isomorphism between the images of `K` and `L` in the derived
category is represented by an honest quasi-isomorphism `K ⟶ L`. -/
lemma exists_quasiIso_of_iso_Q [HasDerivedCategory (ModuleCat.{u} A)]
    (K L : CochainComplex (ModuleCat.{u} A) ℤ) [K.IsKProjective]
    (e : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj L) :
    ∃ f : K ⟶ L, QuasiIso f := by
  obtain ⟨f, hf⟩ := Q_map_surjective_of_isKProjective (A := A) (K := K) L e.hom
  refine ⟨f, (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{u} A) f).mp ?_⟩
  rw [hf]; infer_instance

end Helpers

/-- Auxiliary form of `Work.DSEQ0.exists_bounded_free_model`, with the resolutions `G i` only
required for `i` in the range `[0,N]` of the support of `C`.  This is the statement proved by
induction on `N`. -/
theorem exists_bounded_free_model_aux {A : Type u} [CommRing A]
    [HasDerivedCategory (ModuleCat.{u} A)] (N : ℕ) :
    ∀ (C : CochainComplex (ModuleCat.{u} A) ℤ)
      (hC : ∀ i : ℤ, i < 0 ∨ (N : ℤ) < i → CategoryTheory.Limits.IsZero (C.X i))
      (G : ℤ → CochainComplex (ModuleCat.{u} A) ℤ)
      (hGfin : ∀ i j, Module.Finite A ((G i).X j))
      (hGfree : ∀ i j, Module.Free A ((G i).X j))
      (hGbdd : ∀ i, ∃ a b : ℤ, ∀ j, j < a ∨ b < j → CategoryTheory.Limits.IsZero ((G i).X j))
      (hGres : ∀ i : ℤ, 0 ≤ i → i ≤ (N : ℤ) → ∃ f : G i ⟶
        (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) i).obj
          (C.homology i),
        QuasiIso f),
    ∃ (P : CochainComplex (ModuleCat.{u} A) ℤ),
      (∀ j, Module.Finite A (P.X j)) ∧ (∀ j, Module.Free A (P.X j)) ∧
      (∃ a b : ℤ, ∀ j, j < a ∨ b < j → CategoryTheory.Limits.IsZero (P.X j)) ∧
      ∃ q : P ⟶ C, QuasiIso q := by
  induction N with
  | zero =>
    intro C hC G hGfin hGfree hGbdd hGres
    haveI hCge : C.IsStrictlyGE 0 :=
      (CochainComplex.isStrictlyGE_iff C 0).mpr (fun i hi => hC i (Or.inl hi))
    haveI hCle : C.IsStrictlyLE 0 :=
      (CochainComplex.isStrictlyLE_iff C 0).mpr (fun i hi => hC i (Or.inr (by simpa using hi)))
    obtain ⟨M, ⟨eM⟩⟩ := CochainComplex.exists_iso_single C 0
    have hH : C.homology 0 ≅ M :=
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).mapIso eM ≪≫
        HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 M
    obtain ⟨f₀, hf₀⟩ := hGres 0 le_rfl (by norm_num)
    haveI : QuasiIso f₀ := hf₀
    haveI : IsIso (DerivedCategory.Q.map f₀) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{u} A) f₀).mpr inferInstance
    haveI : (G 0).IsKProjective := isKProjective_of_bounded_free (G 0) (hGfree 0) (hGbdd 0)
    exact ⟨G 0, hGfin 0, hGfree 0, hGbdd 0,
      exists_quasiIso_of_iso_Q (G 0) C
        (asIso (DerivedCategory.Q.map f₀) ≪≫
          DerivedCategory.Q.mapIso
            ((HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).mapIso hH) ≪≫
          (DerivedCategory.Q.mapIso eM).symm)⟩
  | succ m ih =>
    intro C hC G hGfin hGfree hGbdd hGres
    simp only [Nat.cast_add_one] at hC hGres
    haveI hCge : C.IsStrictlyGE 0 :=
      (CochainComplex.isStrictlyGE_iff C 0).mpr (fun i hi => hC i (Or.inl hi))
    -- (1) The truncated complex `C.truncLE m` with the transported resolutions.
    have hC₁ : ∀ i : ℤ, i < 0 ∨ (m : ℤ) < i → IsZero ((C.truncLE (m : ℤ)).X i) := by
      intro i hi
      rcases hi with hi | hi
      · exact CochainComplex.isZero_of_isStrictlyGE (C.truncLE (m : ℤ)) 0 i hi
      · exact CochainComplex.isZero_of_isStrictlyLE (C.truncLE (m : ℤ)) (m : ℤ) i hi
    have hGres₁ : ∀ i : ℤ, 0 ≤ i → i ≤ (m : ℤ) → ∃ f : G i ⟶
        (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) i).obj
          ((C.truncLE (m : ℤ)).homology i),
        QuasiIso f := by
      intro i _ him
      obtain ⟨f₀, hf₀⟩ := hGres i ‹_› (by omega)
      haveI : QuasiIso f₀ := hf₀
      haveI : IsIso (HomologicalComplex.homologyMap (C.ιTruncLE (m : ℤ)) i) :=
        (quasiIsoAt_iff_isIso_homologyMap _ _).mp
          (CochainComplex.quasiIsoAt_ιTruncLE C (m : ℤ) i him)
      exact ⟨f₀ ≫ ((HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) i).mapIso
          (asIso (HomologicalComplex.homologyMap (C.ιTruncLE (m : ℤ)) i))).inv, inferInstance⟩
    obtain ⟨P₁, hP₁fin, hP₁free, hP₁bdd, q₁, hq₁⟩ :=
      ih (C.truncLE (m : ℤ)) hC₁ G hGfin hGfree hGbdd hGres₁
    -- (2) The top term, via `C.truncGE (m+1) ≅ H^{m+1}(C)`.
    haveI hCle : C.IsStrictlyLE ((m : ℤ) + 1) :=
      (CochainComplex.isStrictlyLE_iff C ((m : ℤ) + 1)).mpr (fun i hi => hC i (Or.inr hi))
    obtain ⟨M, ⟨eM⟩⟩ := CochainComplex.exists_iso_single (C.truncGE ((m : ℤ) + 1)) ((m : ℤ) + 1)
    haveI : IsIso (HomologicalComplex.homologyMap (C.πTruncGE ((m : ℤ) + 1)) ((m : ℤ) + 1)) :=
      (quasiIsoAt_iff_isIso_homologyMap _ _).mp
        (CochainComplex.quasiIsoAt_πTruncGE C ((m : ℤ) + 1) ((m : ℤ) + 1) le_rfl)
    have hHom : M ≅ C.homology ((m : ℤ) + 1) :=
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) ((m : ℤ) + 1) M).symm ≪≫
        ((HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (ComplexShape.up ℤ)
          ((m : ℤ) + 1)).mapIso eM).symm ≪≫
        (asIso (HomologicalComplex.homologyMap (C.πTruncGE ((m : ℤ) + 1)) ((m : ℤ) + 1))).symm
    have hΨ : (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) ((m : ℤ) + 1)).obj
        (C.homology ((m : ℤ) + 1)) ≅ C.truncGE ((m : ℤ) + 1) :=
      (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) ((m : ℤ) + 1)).mapIso
        hHom.symm ≪≫ eM.symm
    obtain ⟨f₀, hf₀⟩ := hGres ((m : ℤ) + 1) (by omega) le_rfl
    haveI : QuasiIso f₀ := hf₀
    haveI : IsIso (DerivedCategory.Q.map f₀) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{u} A) f₀).mpr inferInstance
    have hδ : QuasiIso (C.shortComplexTruncLEX₃ToTruncGE (m : ℤ) ((m : ℤ) + 1) rfl :
        (C.shortComplexTruncLE (m : ℤ)).X₃ ⟶ C.truncGE ((m : ℤ) + 1)) := inferInstance
    haveI : IsIso (DerivedCategory.Q.map
        (C.shortComplexTruncLEX₃ToTruncGE (m : ℤ) ((m : ℤ) + 1) rfl)) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{u} A) _).mpr hδ
    haveI : (G ((m : ℤ) + 1)).IsKProjective :=
      isKProjective_of_bounded_free (G ((m : ℤ) + 1)) (hGfree _) (hGbdd _)
    obtain ⟨f, hf⟩ := exists_quasiIso_of_iso_Q (G ((m : ℤ) + 1))
      ((C.shortComplexTruncLE (m : ℤ)).X₃)
      (asIso (DerivedCategory.Q.map f₀) ≪≫ DerivedCategory.Q.mapIso hΨ ≪≫
        (asIso (DerivedCategory.Q.map
          (C.shortComplexTruncLEX₃ToTruncGE (m : ℤ) ((m : ℤ) + 1) rfl))).symm)
    -- (3) The short exact sequence `0 → C.truncLE m → C → X₃ → 0`.
    obtain ⟨P, hPfin, hPfree, hPbdd, q', hq'⟩ :=
      bounded_free_model_of_shortExact (C.shortComplexTruncLE (m : ℤ))
        (C.shortComplexTruncLE_shortExact (m : ℤ))
        P₁ q₁ hq₁ hP₁fin hP₁free hP₁bdd (G ((m : ℤ) + 1)) f hf
        (hGfin _) (hGfree _) (hGbdd _)
    exact ⟨P, hPfin, hPfree, hPbdd, q', hq'⟩

/-- **A complex whose cohomology has bounded finite free models has one.**  If `C` is a cochain
complex of `A`-modules concentrated in degrees `[0,N]` and, for every `i`, a bounded complex
`G i` of finite free modules is given together with a quasi-isomorphism onto the single-object
complex on `H^i(C)` (i.e. `G i` is a finite free resolution of `H^i(C)` placed in degree `i`),
then `C` itself is quasi-isomorphic to a bounded complex `P` of finite free `A`-modules.

This is the input that area `EQ0` needs (`DSMap.area_COH` supplies the finite generation and
boundedness of `Hⁱ(Č)`; finite projective dimension over a regular local ring supplies the
resolutions `G i`).  Proof: induction on `N`.  The induction step uses the distinguished triangle
of the canonical truncations `C.truncLE (N-1) ⟶ C ⟶ C.truncGE N ⟶⁺¹` in `D(A)` — see
`Mathlib/Algebra/Homology/DerivedCategory/TStructure.lean`, whose `exists_triangle_zero_one` is
the case `N = 1` of exactly this construction — together with
`Work.DSEQ0.bounded_free_model_of_triangle` for the induction step, the fact that `C.truncLE (N-1)`
has the same cohomology as `C` in degrees `≤ N-1` (`Mathlib/Algebra/Homology/Embedding/
TruncLEHomology.lean`), and the fact that `C.truncGE N` is quasi-isomorphic to `H^N(C)⟦-N⟧`
(`Embedding/TruncGEHomology.lean` + the hypothesis `hC` that `C` vanishes above `N`).
Note: base case `N = 0`; in the induction step one re-instantiates the induction hypothesis with
`G' i := (if i ≤ N-1 then G i else 0)`. -/
theorem exists_bounded_free_model {A : Type u} [CommRing A] [HasDerivedCategory (ModuleCat.{u} A)]
    (N : ℕ) (C : CochainComplex (ModuleCat.{u} A) ℤ)
    (hC : ∀ i : ℤ, i < 0 ∨ (N : ℤ) < i → CategoryTheory.Limits.IsZero (C.X i))
    (G : ℤ → CochainComplex (ModuleCat.{u} A) ℤ)
    (hGfin : ∀ i j, Module.Finite A ((G i).X j))
    (hGfree : ∀ i j, Module.Free A ((G i).X j))
    (hGbdd : ∀ i, ∃ a b : ℤ, ∀ j, j < a ∨ b < j → CategoryTheory.Limits.IsZero ((G i).X j))
    (hGres : ∀ i : ℤ, ∃ f : G i ⟶
        (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) i).obj
          ((HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (ComplexShape.up ℤ) i).obj C),
        QuasiIso f) :
    ∃ (P : CochainComplex (ModuleCat.{u} A) ℤ),
      (∀ j, Module.Finite A (P.X j)) ∧ (∀ j, Module.Free A (P.X j)) ∧
      (∃ a b : ℤ, ∀ j, j < a ∨ b < j → CategoryTheory.Limits.IsZero (P.X j)) ∧
      ∃ q : P ⟶ C, QuasiIso q :=
  exists_bounded_free_model_aux (A := A) N C hC G hGfin hGfree hGbdd
    (fun i _ _ => hGres i)

end Work.DSEQ0
