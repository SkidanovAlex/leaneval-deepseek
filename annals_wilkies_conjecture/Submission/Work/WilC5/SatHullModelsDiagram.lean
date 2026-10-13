/-
  WilC5 — the term hull of the canonical model of the total theory models the elementary diagram of
  `M` when the constants of `L[[M]]` are interpreted by the values of the seed constants
  `Sum.inl m`.

  The proof combines three ingredients:

  * `SatHull_expansion`: the `L[[M]]`-structure `SatEmbStruct` is the reduct of the canonical
    `L[[SatCTotal]]`-structure `SatHullExp` on the hull along `Sum.inl : M → SatCTotal`, so
    realization of an `L[[M]]`-sentence agrees with realization of its image;
  * `SatHull_isElementary`: the hull is an `L`-elementary substructure of the model `SatNC`
    (Tarski–Vaught, from `SatHullStrong`);
  * `SatTot_mem_diagram`: the image of a sentence of the elementary diagram of `M` at some level
    belongs to the total theory `SatTot`, hence is true in `SatNC` since `SatNC ⊨ SatTot`.
-/
import Mathlib
import Submission.Work.WilC5.SatEmb
import Submission.Work.WilC5.SatHull
import Submission.Work.WilC5.SatStrong
import Submission.Work.WilC5.IsElementary_of_finSat

open FirstOrder Language
open scoped FirstOrder

attribute [local implicit_reducible] FirstOrder.Language.withConstants Work.WilC5.SatC

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilC5

/-- The element of the term hull `SatHull N` given by the value in `N` of a constant of the total
language. -/
noncomputable def SatConHull (L : FirstOrder.Language.{0, 0}) (M : Type)
    (κ : Cardinal.{0}) (N : Type) [instN : (SatLang L (SatCt L M κ)).Structure N]
    (c : SatCt L M κ) : ↥(SatHull L M κ N) :=
  ⟨@SatConVal L (SatCt L M κ) N instN c,
    letI : L.Structure N := SatReduct L M κ N
    @FirstOrder.Language.Substructure.subset_closure L N (SatReduct L M κ N)
      (Set.range (fun c : SatCt L M κ => @SatConVal L (SatCt L M κ) N instN c))
      _ ⟨c, rfl⟩⟩

/-- The canonical `L[[SatCTotal]]`-structure on the term hull: the `L`-part is the induced
structure and each constant of the total language is interpreted by its value in `N`. -/
@[instance_reducible]
noncomputable def SatHullExp (L : FirstOrder.Language.{0, 0}) (M : Type)
    (κ : Cardinal.{0}) (N : Type) [instN : (SatLang L (SatCt L M κ)).Structure N] :
    (SatLang L (SatCt L M κ)).Structure ↥(SatHull L M κ N) :=
  letI : L.Structure N := SatReduct L M κ N
  letI : L.Structure ↥(SatHull L M κ N) :=
    FirstOrder.Language.Substructure.inducedStructure (S := SatHull L M κ N)
  letI : (FirstOrder.Language.constantsOn (SatCt L M κ)).Structure ↥(SatHull L M κ N) :=
    FirstOrder.Language.constantsOn.structure (SatConHull L M κ N)
  FirstOrder.Language.sumStructure L (FirstOrder.Language.constantsOn (SatCt L M κ))
    ↥(SatHull L M κ N)

/-- The index type of the construction is nonempty. -/
theorem SatIdx_nonempty (κ : Cardinal.{0}) : Nonempty (SatIdx κ) := by
  unfold SatIdx
  rw [Ordinal.nonempty_toType_iff]
  exact (Cardinal.ord_pos.mpr (lt_of_le_of_lt
    (zero_le : (0 : Cardinal.{0}) ≤ κ + Cardinal.aleph0)
    (Order.lt_succ _) |>.trans (Order.lt_succ _))).ne'

/-- `SatEmbStruct` is the reduct of the canonical `L[[SatCTotal]]`-structure `SatHullExp` on the
hull along the language map induced by `Sum.inl : M → SatCTotal`. -/
theorem SatHull_expansion (L : FirstOrder.Language.{0, 0}) (M : Type) [instM : L.Structure M]
    (κ : Cardinal.{0}) (hM : Nonempty M) :
    @FirstOrder.Language.LHom.IsExpansionOn (SatLang L M) (SatLang L (SatCt L M κ))
      (SatLangMap (Sum.inl : M → SatCt L M κ))
      ↥(@SatHull L M κ (SatNC L M κ hM) (SatNstruc L M κ hM))
      (SatEmbStruct L M κ hM)
      (@SatHullExp L M κ (SatNC L M κ hM) (SatNstruc L M κ hM)) := by
  refine @FirstOrder.Language.LHom.IsExpansionOn.mk (SatLang L M) (SatLang L (SatCt L M κ))
    (SatLangMap (Sum.inl : M → SatCt L M κ))
    ↥(@SatHull L M κ (SatNC L M κ hM) (SatNstruc L M κ hM))
    (SatEmbStruct L M κ hM) (@SatHullExp L M κ (SatNC L M κ hM) (SatNstruc L M κ hM)) ?_ ?_
  · intro n f x
    rcases f with g | c
    · simp only [SatLangMap, LHom.sumMap_onFunction, Sum.map_inl, LHom.id_onFunction, id_eq]
      rfl
    · cases n with
      | zero =>
        simp only [SatLangMap, LHom.sumMap_onFunction, LHom.constantsOnMap,
          FirstOrder.Language.constantsOn]
        exact Subtype.ext rfl
      | succ k => exact isEmptyElim c
  · intro n R x
    rcases R with r | e
    · simp only [SatLangMap, LHom.sumMap_onRelation, Sum.map_inl, LHom.id_onRelation, id_eq]
      rfl
    · exact isEmptyElim e

/-- The term hull of the canonical model of the total theory is an `L`-elementary substructure. -/
theorem SatHull_isElementary (L : FirstOrder.Language.{0, 0}) (M : Type) [instM : L.Structure M]
    (κ : Cardinal.{0}) (hM : Nonempty M) :
    @FirstOrder.Language.Substructure.IsElementary L (SatNC L M κ hM)
      (@SatReduct L M κ (SatNC L M κ hM) (SatNstruc L M κ hM))
      (@SatHull L M κ (SatNC L M κ hM) (SatNstruc L M κ hM)) := by
  letI : (SatLang L (SatCt L M κ)).Structure (SatNC L M κ hM) := SatNstruc L M κ hM
  letI : L.Structure (SatNC L M κ hM) := SatReduct L M κ (SatNC L M κ hM)
  refine IsElementary_of_finSat _ κ ?_
  intro A hA p hp
  exact SatHullStrong L M κ hM (SatNC L M κ hM) (SatNmodel L M κ hM) A hA p hp

/-- The image of a sentence of the elementary diagram of `M` under `Sum.inl : M → SatCTotal` lies
in the total theory `SatTot`. -/
theorem SatTot_mem_diagram (L : FirstOrder.Language.{0, 0}) (M : Type) [instM : L.Structure M]
    (κ : Cardinal.{0}) (hM : Nonempty M) (σ : (SatLang L M).Sentence)
    (hσ : σ ∈ L.elementaryDiagram M) :
    (SatLangMap (Sum.inl : M → SatCt L M κ)).onSentence σ ∈ SatTot L M κ := by
  obtain ⟨x⟩ := SatIdx_nonempty κ
  rw [SatTot]
  refine Set.mem_iUnion.mpr ⟨x, ?_⟩
  refine LHom.mem_onTheory.mpr
    ⟨(SatLangMap (Sum.inl : M → SatC L M κ x)).onSentence σ, ?_, ?_⟩
  · refine (mem_SatTh3_iff L M κ x _).mpr ((SatMain L M κ hM x).2 _ ?_)
    exact (mem_SatSpecG L M κ).mpr (Or.inl ⟨σ, hσ, rfl⟩)
  · rw [SatLangMap_compW5]
    have hcomp : (SatIncTotal L M κ x) ∘ (Sum.inl : M → SatC L M κ x)
        = (Sum.inl : M → SatCt L M κ) := by
      funext m; exact SatIncTotal_inl L M κ x m
    rw [hcomp]
    rfl

/-- Realization of a sentence of `L[[M]]` in the hull with the canonical structure `SatEmbStruct`
is equivalent to realization of its image in the model `SatNC` of the total theory. -/
theorem SatHull_realize_iff (L : FirstOrder.Language.{0, 0}) (M : Type) [instM : L.Structure M]
    (κ : Cardinal.{0}) (hM : Nonempty M) (σ : (SatLang L M).Sentence) :
    @Sentence.Realize (SatLang L M)
      ↥(@SatHull L M κ (SatNC L M κ hM) (SatNstruc L M κ hM))
      (SatEmbStruct L M κ hM) σ ↔
    @Sentence.Realize (SatLang L (SatCt L M κ)) (SatNC L M κ hM) (SatNstruc L M κ hM)
      ((SatLangMap (Sum.inl : M → SatCt L M κ)).onSentence σ) := by
  letI instN : (SatLang L (SatCt L M κ)).Structure (SatNC L M κ hM) := SatNstruc L M κ hM
  letI instL : L.Structure (SatNC L M κ hM) := @SatReduct L M κ (SatNC L M κ hM) instN
  letI instS : (SatLang L (SatCt L M κ)).Structure
      ↥(@SatHull L M κ (SatNC L M κ hM) (SatNstruc L M κ hM)) :=
    @SatHullExp L M κ (SatNC L M κ hM) instN
  letI instH : L.Structure ↥(@SatHull L M κ (SatNC L M κ hM) (SatNstruc L M κ hM)) :=
    @FirstOrder.Language.Substructure.inducedStructure L (SatNC L M κ hM) instL
      (@SatHull L M κ (SatNC L M κ hM) (SatNstruc L M κ hM))
  have hElem : @FirstOrder.Language.Substructure.IsElementary L (SatNC L M κ hM) instL
      (@SatHull L M κ (SatNC L M κ hM) (SatNstruc L M κ hM)) := SatHull_isElementary L M κ hM
  let e : ↥(@SatHull L M κ (SatNC L M κ hM) (SatNstruc L M κ hM)) ↪ₑ[L] (SatNC L M κ hM) :=
    (⟨@SatHull L M κ (SatNC L M κ hM) (SatNstruc L M κ hM), hElem⟩ :
      L.ElementarySubstructure (SatNC L M κ hM)).subtype
  have hExp : @LHom.IsExpansionOn (SatLang L M) (SatLang L (SatCt L M κ))
      (SatLangMap (Sum.inl : M → SatCt L M κ))
      ↥(@SatHull L M κ (SatNC L M κ hM) (SatNstruc L M κ hM))
      (SatEmbStruct L M κ hM) instS := SatHull_expansion L M κ hM
  have hEH : @LHom.IsExpansionOn L (SatLang L (SatCt L M κ)) (L.lhomWithConstants (SatCt L M κ))
      ↥(@SatHull L M κ (SatNC L M κ hM) (SatNstruc L M κ hM)) instH instS :=
    @LHom.IsExpansionOn.mk L (SatLang L (SatCt L M κ)) (L.lhomWithConstants (SatCt L M κ))
      ↥(@SatHull L M κ (SatNC L M κ hM) (SatNstruc L M κ hM)) instH instS
      (fun {n} f x => rfl) (fun {n} R x => rfl)
  have hEN : @LHom.IsExpansionOn L (SatLang L (SatCt L M κ)) (L.lhomWithConstants (SatCt L M κ))
      (SatNC L M κ hM) instL instN :=
    @LHom.isExpansionOn_reduct L (SatLang L (SatCt L M κ)) (L.lhomWithConstants (SatCt L M κ))
      (SatNC L M κ hM) instN
  have h1 : @Sentence.Realize (SatLang L M)
        ↥(@SatHull L M κ (SatNC L M κ hM) (SatNstruc L M κ hM)) (SatEmbStruct L M κ hM) σ ↔
      @Sentence.Realize (SatLang L (SatCt L M κ))
        ↥(@SatHull L M κ (SatNC L M κ hM) (SatNstruc L M κ hM)) instS
        ((SatLangMap (Sum.inl : M → SatCt L M κ)).onSentence σ) :=
    (@LHom.realize_onSentence (SatLang L M) (SatLang L (SatCt L M κ))
      ↥(@SatHull L M κ (SatNC L M κ hM) (SatNstruc L M κ hM))
      (SatEmbStruct L M κ hM) instS (SatLangMap (Sum.inl : M → SatCt L M κ)) hExp σ).symm
  let ψ : L.Formula (SatCt L M κ ⊕ Empty) :=
    BoundedFormula.constantsVarsEquiv ((SatLangMap (Sum.inl : M → SatCt L M κ)).onSentence σ)
  let vh : SatCt L M κ ⊕ Empty → ↥(@SatHull L M κ (SatNC L M κ hM) (SatNstruc L M κ hM)) :=
    Sum.elim (fun c => (↑(L.con c) :
      ↥(@SatHull L M κ (SatNC L M κ hM) (SatNstruc L M κ hM)))) default
  let vn : SatCt L M κ ⊕ Empty → (SatNC L M κ hM) :=
    Sum.elim (fun c => (↑(L.con c) : SatNC L M κ hM)) default
  have hcH : ψ.Realize vh ↔
      @Sentence.Realize (SatLang L (SatCt L M κ))
        ↥(@SatHull L M κ (SatNC L M κ hM) (SatNstruc L M κ hM)) instS
        ((SatLangMap (Sum.inl : M → SatCt L M κ)).onSentence σ) := by
    have h := @BoundedFormula.realize_constantsVarsEquiv L
      ↥(@SatHull L M κ (SatNC L M κ hM) (SatNstruc L M κ hM)) instH (SatCt L M κ) Empty
      instS hEH 0 ((SatLangMap (Sum.inl : M → SatCt L M κ)).onSentence σ)
      (default : Empty → ↥(@SatHull L M κ (SatNC L M κ hM) (SatNstruc L M κ hM)))
      (default : Fin 0 → ↥(@SatHull L M κ (SatNC L M κ hM) (SatNstruc L M κ hM)))
    simpa only [ψ, vh, Formula.Realize, Sentence.Realize] using h
  have hcN : ψ.Realize vn ↔
      @Sentence.Realize (SatLang L (SatCt L M κ)) (SatNC L M κ hM) instN
        ((SatLangMap (Sum.inl : M → SatCt L M κ)).onSentence σ) := by
    have h := @BoundedFormula.realize_constantsVarsEquiv L (SatNC L M κ hM) instL (SatCt L M κ)
      Empty instN hEN 0 ((SatLangMap (Sum.inl : M → SatCt L M κ)).onSentence σ)
      (default : Empty → (SatNC L M κ hM)) (default : Fin 0 → (SatNC L M κ hM))
    simpa only [ψ, vn, Formula.Realize, Sentence.Realize] using h
  have hmf := e.map_boundedFormula ψ vh
    (default : Fin 0 → ↥(@SatHull L M κ (SatNC L M κ hM) (SatNstruc L M κ hM)))
  have hv : ⇑e ∘ vh = vn := by
    funext i
    rcases i with c | x
    · rfl
    · exact x.elim
  have hd : ⇑e ∘ (default : Fin 0 → ↥(@SatHull L M κ (SatNC L M κ hM) (SatNstruc L M κ hM)))
      = (default : Fin 0 → (SatNC L M κ hM)) := by
    funext i; exact i.elim0
  rw [hv, hd] at hmf
  exact h1.trans (hcH.symm.trans (hmf.symm.trans hcN))

theorem SatHullModelsDiagram {L : FirstOrder.Language.{0, 0}} {M : Type} [instM : L.Structure M]
    {κ : Cardinal.{0}} (hM : Nonempty M) :
    @FirstOrder.Language.Theory.Model (SatLang L M)
      ↥(@SatHull L M κ (SatNC L M κ hM) (SatNstruc L M κ hM))
      (SatEmbStruct L M κ hM) (L.elementaryDiagram M) := by
  refine @FirstOrder.Language.Theory.Model.mk (SatLang L M)
    ↥(@SatHull L M κ (SatNC L M κ hM) (SatNstruc L M κ hM))
    (SatEmbStruct L M κ hM) (L.elementaryDiagram M) ?_
  intro σ hσ
  exact (SatHull_realize_iff L M κ hM σ).mpr
    ((SatNmodel L M κ hM).realize_of_mem ((SatLangMap (Sum.inl : M → SatCt L M κ)).onSentence σ)
      (SatTot_mem_diagram L M κ hM σ hσ))

end Work.WilC5
