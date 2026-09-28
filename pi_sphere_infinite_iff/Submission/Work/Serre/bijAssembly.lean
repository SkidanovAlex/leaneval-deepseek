import Submission.Work.Serre.mvLadder

/-!
# The five-lemma assembly of the local-to-global cup bijectivity

This file reduces `Work.Serre.bijective_mixedCup_of_openCover` to the `δ`-square of the
Mayer–Vietoris ladder (`Work.Serre.mvDeltaCupMixed`), which is the only genuinely hard input.

Given the local bijectivity hypotheses on `U`, `V` and `U ∩ V`, the verticals `vertP` and `vertQ`
of the ladder are isomorphisms in the relevant degrees (the `Coh`-flavoured cup map is the second
factor of the corresponding vertical, the first factor being the isomorphism `relToAbs` for the
empty relative part), and `ladder_vertM_isIso` then gives `IsIso (vertM X A n₀ U₀ m)`.  The
conclusion `Function.Bijective` is the iso-ness of the `Coh`-flavoured cup map, again read off from
`IsIso (vertM …)` by cancelling the isomorphism `relToAbs ℚ (∅ : Set X) m`.
-/

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

/-- Bijectivity of the `Coh`-flavoured cup map gives the iso-ness of the `ModuleCat`-version. -/
theorem isIso_cupVert_of_bijective {B : Type} [TopologicalSpace B] (A : Set B) (m n : ℕ)
    (z : Work.Thom.RelCoh ℚ n B A)
    (h : Function.Bijective (fun x : Work.Thom.Coh ℚ m B => (Work.Thom.mixedCupC ℚ A m n) x z)) :
    IsIso (cupVert A m n z) :=
  (CategoryTheory.ConcreteCategory.isIso_iff_bijective (cupVert A m n z)).mpr h

/-- The restriction of `U₀` to the overlap, spelled as a single `relCohMap`. -/
theorem U₀ovl_eq_relCohMapAux (X : TopCat) (A U V : Set X) (n₀ : ℕ)
    (U₀ : Work.Thom.RelCoh ℚ n₀ X A) :
    U₀ovl X A U V n₀ U₀
      = (Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(U ∩ V), X))
          {y : ↥(U ∩ V) | (y : X) ∈ A} A (fun _ hy => hy) ℚ n₀).hom U₀ := by
  have hU : mvRestrU X A U n₀ ≫ mvRestrUVU X A U V n₀
      = Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(U ∩ V), X))
          {y : ↥(U ∩ V) | (y : X) ∈ A} A (fun _ hx => hx) ℚ n₀ := by
    rw [show mvRestrUVU X A U V n₀ = Work.Thom.relCohMap
          (⟨fun x => ⟨x.1, x.2.1⟩, by continuity⟩ : C(↥(U ∩ V), ↥U))
          {y : ↥(U ∩ V) | (y : X) ∈ A} {x : ↥U | (x : X) ∈ A} (fun _ hx => hx) ℚ n₀ from rfl,
      show mvRestrU X A U n₀ = Work.Thom.relCohMap
          (⟨Subtype.val, continuous_subtype_val⟩ : C(↥U, X))
          {x : ↥U | (x : X) ∈ A} A (fun _ hy => hy) ℚ n₀ from rfl,
      Work.Thom.relCohMap_compA {y : ↥(U ∩ V) | (y : X) ∈ A} {x : ↥U | (x : X) ∈ A} A
          (⟨fun x => ⟨x.1, x.2.1⟩, by continuity⟩ : C(↥(U ∩ V), ↥U))
          (⟨Subtype.val, continuous_subtype_val⟩ : C(↥U, X))
          (fun _ hx => hx) (fun _ hx => hx) (fun _ hx => hx) ℚ n₀]
    exact (Work.Thom.relCohMap_congrA _ _ (by ext x; rfl) (fun x hx => hx) (fun x hx => hx)
        ℚ n₀).trans
      (Work.Thom.relCohMap_hcongrA _ _ _ (fun x hx => hx) (fun x hx => hx) ℚ n₀)
  have h := congrArg (fun (f : Work.Thom.RelCoh ℚ n₀ X A ⟶ mvCohUV X A U V n₀) =>
      ModuleCat.Hom.hom f U₀) hU
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, U₀ovl] using h

/-- **The five-lemma assembly.**  If the ladder square for the connecting maps holds
(`Hdelta`), then the local bijectivity of the cup maps implies the global one. -/
theorem bijective_mixedCup_of_openCover_aux {X : Type} [TopologicalSpace X] (A : Set X)
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    (n₀ K : ℕ) (U₀ : Work.Thom.RelCoh ℚ n₀ X A)
    (hlocU : ∀ m : ℕ, m + n₀ ≤ K → Function.Bijective (fun x : Work.Thom.Coh ℚ m ↥U =>
      (Work.Thom.mixedCupC ℚ {y : ↥U | (y : X) ∈ A} m n₀) x
        ((Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥U, X))
          {y : ↥U | (y : X) ∈ A} A (fun _ hy => hy) ℚ n₀).hom U₀)))
    (hlocV : ∀ m : ℕ, m + n₀ ≤ K → Function.Bijective (fun x : Work.Thom.Coh ℚ m ↥V =>
      (Work.Thom.mixedCupC ℚ {y : ↥V | (y : X) ∈ A} m n₀) x
        ((Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥V, X))
          {y : ↥V | (y : X) ∈ A} A (fun _ hy => hy) ℚ n₀).hom U₀)))
    (hlocUV : ∀ m : ℕ, m + n₀ ≤ K → Function.Bijective (fun x : Work.Thom.Coh ℚ m ↥(U ∩ V) =>
      (Work.Thom.mixedCupC ℚ {y : ↥(U ∩ V) | (y : X) ∈ A} m n₀) x
        ((Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(U ∩ V), X))
          {y : ↥(U ∩ V) | (y : X) ∈ A} A (fun _ hy => hy) ℚ n₀).hom U₀)))
    (Hdelta : ∀ m : ℕ,
      CategoryTheory.CategoryStruct.comp
          (mvDelta (TopCat.of X) (∅ : Set X) U V hU hV hcov m)
          (vertM (TopCat.of X) A n₀ U₀ (m + 1))
      = CategoryTheory.CategoryStruct.comp
          (vertQ (TopCat.of X) A U V n₀ U₀ m)
          (mvDeltaShift (TopCat.of X) A U V hU hV hcov n₀ m)) :
    ∀ m : ℕ, 1 ≤ m → m + n₀ ≤ K → Function.Bijective (fun x : Work.Thom.Coh ℚ m X =>
      (Work.Thom.mixedCupC ℚ A m n₀) x U₀) := by
  intro m hm hK
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  -- the degree `m'` is admissible
  have hm' : m' + n₀ ≤ K := by omega
  -- the `U`-component of the `P`-vertical
  haveI hU' : IsIso (cupVertRelU (TopCat.of X) A U n₀ U₀ m') := by
    haveI : IsIso (Work.Thom.relToAbs ℚ {x : ↥U | (x : TopCat.of X) ∈ (∅ : Set X)} m') := by
      rw [show ({x : ↥U | (x : TopCat.of X) ∈ (∅ : Set X)} : Set ↥U) = (∅ : Set ↥U) from rfl]
      exact isIso_relToAbs_empty_rat m'
    haveI : IsIso (cupVert {y : ↥U | (y : TopCat.of X) ∈ A} m' n₀
        (mvRestrU (TopCat.of X) A U n₀ U₀)) :=
      isIso_cupVert_of_bijective _ _ _ _ (hlocU m' hm')
    rw [show cupVertRelU (TopCat.of X) A U n₀ U₀ m'
        = Work.Thom.relToAbs ℚ {x : ↥U | (x : TopCat.of X) ∈ (∅ : Set X)} m'
          ≫ cupVert {y : ↥U | (y : TopCat.of X) ∈ A} m' n₀
              (mvRestrU (TopCat.of X) A U n₀ U₀) from rfl]
    infer_instance
  -- the `V`-component of the `P`-vertical
  haveI hV' : IsIso (cupVertRelV (TopCat.of X) A V n₀ U₀ m') := by
    haveI : IsIso (Work.Thom.relToAbs ℚ {x : ↥V | (x : TopCat.of X) ∈ (∅ : Set X)} m') := by
      rw [show ({x : ↥V | (x : TopCat.of X) ∈ (∅ : Set X)} : Set ↥V) = (∅ : Set ↥V) from rfl]
      exact isIso_relToAbs_empty_rat m'
    haveI : IsIso (cupVert {y : ↥V | (y : TopCat.of X) ∈ A} m' n₀
        (mvRestrV (TopCat.of X) A V n₀ U₀)) :=
      isIso_cupVert_of_bijective _ _ _ _ (hlocV m' hm')
    rw [show cupVertRelV (TopCat.of X) A V n₀ U₀ m'
        = Work.Thom.relToAbs ℚ {x : ↥V | (x : TopCat.of X) ∈ (∅ : Set X)} m'
          ≫ cupVert {y : ↥V | (y : TopCat.of X) ∈ A} m' n₀
              (mvRestrV (TopCat.of X) A V n₀ U₀) from rfl]
    infer_instance
  -- the `Q`-vertical
  haveI hQ' : IsIso (vertQ (TopCat.of X) A U V n₀ U₀ m') := by
    haveI : IsIso (Work.Thom.relToAbs ℚ {x : ↥(U ∩ V) | (x : TopCat.of X) ∈ (∅ : Set X)} m') := by
      rw [show ({x : ↥(U ∩ V) | (x : TopCat.of X) ∈ (∅ : Set X)} : Set ↥(U ∩ V))
          = (∅ : Set ↥(U ∩ V)) from rfl]
      exact isIso_relToAbs_empty_rat m'
    haveI : IsIso (cupVert {y : ↥(U ∩ V) | (y : TopCat.of X) ∈ A} m' n₀
        (U₀ovl (TopCat.of X) A U V n₀ U₀)) := by
      rw [show U₀ovl (TopCat.of X) A U V n₀ U₀
          = (Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ :
              C(↥(U ∩ V), TopCat.of X)) {y : ↥(U ∩ V) | (y : TopCat.of X) ∈ A} A
              (fun _ hy => hy) ℚ n₀).hom U₀ from
        U₀ovl_eq_relCohMapAux (TopCat.of X) A U V n₀ U₀]
      exact isIso_cupVert_of_bijective _ _ _ _ (hlocUV m' hm')
    rw [show vertQ (TopCat.of X) A U V n₀ U₀ m'
        = Work.Thom.relToAbs ℚ {x : ↥(U ∩ V) | (x : TopCat.of X) ∈ (∅ : Set X)} m'
          ≫ cupVert {y : ↥(U ∩ V) | (y : TopCat.of X) ∈ A} m' n₀
              (U₀ovl (TopCat.of X) A U V n₀ U₀) from rfl]
    infer_instance
  -- the `P`-vertical
  haveI hP' : IsIso (vertP (TopCat.of X) A U V n₀ U₀ m') := by
    rw [show vertP (TopCat.of X) A U V n₀ U₀ m'
        = biprod.map (cupVertRelU (TopCat.of X) A U n₀ U₀ m')
            (cupVertRelV (TopCat.of X) A V n₀ U₀ m') from rfl]
    exact (CategoryTheory.Limits.biprod.mapIso (asIso (cupVertRelU (TopCat.of X) A U n₀ U₀ m'))
      (asIso (cupVertRelV (TopCat.of X) A V n₀ U₀ m'))).isIso_hom
  -- the same at degree `m' + 1`
  have hm1 : m' + 1 + n₀ ≤ K := by omega
  haveI hU'' : IsIso (cupVertRelU (TopCat.of X) A U n₀ U₀ (m' + 1)) := by
    haveI : IsIso (Work.Thom.relToAbs ℚ {x : ↥U | (x : TopCat.of X) ∈ (∅ : Set X)} (m' + 1)) := by
      rw [show ({x : ↥U | (x : TopCat.of X) ∈ (∅ : Set X)} : Set ↥U) = (∅ : Set ↥U) from rfl]
      exact isIso_relToAbs_empty_rat (m' + 1)
    haveI : IsIso (cupVert {y : ↥U | (y : TopCat.of X) ∈ A} (m' + 1) n₀
        (mvRestrU (TopCat.of X) A U n₀ U₀)) :=
      isIso_cupVert_of_bijective _ _ _ _ (hlocU (m' + 1) hm1)
    rw [show cupVertRelU (TopCat.of X) A U n₀ U₀ (m' + 1)
        = Work.Thom.relToAbs ℚ {x : ↥U | (x : TopCat.of X) ∈ (∅ : Set X)} (m' + 1)
          ≫ cupVert {y : ↥U | (y : TopCat.of X) ∈ A} (m' + 1) n₀
              (mvRestrU (TopCat.of X) A U n₀ U₀) from rfl]
    infer_instance
  haveI hV'' : IsIso (cupVertRelV (TopCat.of X) A V n₀ U₀ (m' + 1)) := by
    haveI : IsIso (Work.Thom.relToAbs ℚ {x : ↥V | (x : TopCat.of X) ∈ (∅ : Set X)} (m' + 1)) := by
      rw [show ({x : ↥V | (x : TopCat.of X) ∈ (∅ : Set X)} : Set ↥V) = (∅ : Set ↥V) from rfl]
      exact isIso_relToAbs_empty_rat (m' + 1)
    haveI : IsIso (cupVert {y : ↥V | (y : TopCat.of X) ∈ A} (m' + 1) n₀
        (mvRestrV (TopCat.of X) A V n₀ U₀)) :=
      isIso_cupVert_of_bijective _ _ _ _ (hlocV (m' + 1) hm1)
    rw [show cupVertRelV (TopCat.of X) A V n₀ U₀ (m' + 1)
        = Work.Thom.relToAbs ℚ {x : ↥V | (x : TopCat.of X) ∈ (∅ : Set X)} (m' + 1)
          ≫ cupVert {y : ↥V | (y : TopCat.of X) ∈ A} (m' + 1) n₀
              (mvRestrV (TopCat.of X) A V n₀ U₀) from rfl]
    infer_instance
  haveI hQ'' : IsIso (vertQ (TopCat.of X) A U V n₀ U₀ (m' + 1)) := by
    haveI : IsIso (Work.Thom.relToAbs ℚ {x : ↥(U ∩ V) | (x : TopCat.of X) ∈ (∅ : Set X)} (m' + 1)) := by
      rw [show ({x : ↥(U ∩ V) | (x : TopCat.of X) ∈ (∅ : Set X)} : Set ↥(U ∩ V))
          = (∅ : Set ↥(U ∩ V)) from rfl]
      exact isIso_relToAbs_empty_rat (m' + 1)
    haveI : IsIso (cupVert {y : ↥(U ∩ V) | (y : TopCat.of X) ∈ A} (m' + 1) n₀
        (U₀ovl (TopCat.of X) A U V n₀ U₀)) := by
      rw [show U₀ovl (TopCat.of X) A U V n₀ U₀
          = (Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ :
              C(↥(U ∩ V), TopCat.of X)) {y : ↥(U ∩ V) | (y : TopCat.of X) ∈ A} A
              (fun _ hy => hy) ℚ n₀).hom U₀ from
        U₀ovl_eq_relCohMapAux (TopCat.of X) A U V n₀ U₀]
      exact isIso_cupVert_of_bijective _ _ _ _ (hlocUV (m' + 1) hm1)
    rw [show vertQ (TopCat.of X) A U V n₀ U₀ (m' + 1)
        = Work.Thom.relToAbs ℚ {x : ↥(U ∩ V) | (x : TopCat.of X) ∈ (∅ : Set X)} (m' + 1)
          ≫ cupVert {y : ↥(U ∩ V) | (y : TopCat.of X) ∈ A} (m' + 1) n₀
              (U₀ovl (TopCat.of X) A U V n₀ U₀) from rfl]
    infer_instance
  haveI hP'' : IsIso (vertP (TopCat.of X) A U V n₀ U₀ (m' + 1)) := by
    rw [show vertP (TopCat.of X) A U V n₀ U₀ (m' + 1)
        = biprod.map (cupVertRelU (TopCat.of X) A U n₀ U₀ (m' + 1))
            (cupVertRelV (TopCat.of X) A V n₀ U₀ (m' + 1)) from rfl]
    exact (CategoryTheory.Limits.biprod.mapIso
      (asIso (cupVertRelU (TopCat.of X) A U n₀ U₀ (m' + 1)))
      (asIso (cupVertRelV (TopCat.of X) A V n₀ U₀ (m' + 1)))).isIso_hom
  -- the five lemma
  haveI hrel : IsIso (Work.Thom.relToAbs ℚ (∅ : Set X) (m' + 1)) :=
    isIso_relToAbs_empty_rat (m' + 1)
  haveI hvM : IsIso (Work.Thom.relToAbs ℚ (∅ : Set X) (m' + 1) ≫ cupVert A (m' + 1) n₀ U₀) := by
    rw [← show vertM (TopCat.of X) A n₀ U₀ (m' + 1)
        = Work.Thom.relToAbs ℚ (∅ : Set X) (m' + 1) ≫ cupVert A (m' + 1) n₀ U₀ from rfl]
    exact ladder_vertM_isIso (TopCat.of X) A U V hU hV hcov n₀ U₀ Hdelta m' hP' hQ' hP'' hQ''
  -- cancel the isomorphism `relToAbs`
  haveI hcup : IsIso (cupVert A (m' + 1) n₀ U₀) :=
    IsIso.of_isIso_comp_left (Work.Thom.relToAbs ℚ (∅ : Set X) (m' + 1))
      (cupVert A (m' + 1) n₀ U₀)
  exact (CategoryTheory.ConcreteCategory.isIso_iff_bijective (cupVert A (m' + 1) n₀ U₀)).mp hcup

end

end Work.Serre
