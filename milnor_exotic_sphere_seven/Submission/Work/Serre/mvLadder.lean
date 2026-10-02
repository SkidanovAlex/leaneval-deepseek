import Mathlib
import Submission.Work.Serre.relCohMV_les_rat
import Submission.Work.Serre.MVCohRatDefs
import Submission.Work.Serre.relToAbsEmptyIso
import Submission.Work.Serre.fiveLemma_LES_first
import Submission.Work.Serre.CellMultiplicativity
import Submission.Work.Thom.ATools
import Submission.Work.Thom.step_natural

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The Mayer–Vietoris ladder for the mixed cup product

For a space `X`, a subset `A ⊆ X` and an open cover `X = U ∪ V`, this file sets up the ladder
between the two rational relative Mayer–Vietoris long exact sequences (over the cover `{U,V}`, for
the relative parts `∅` and `A`) whose vertical maps are "cup with a fixed class `U₀ ∈ H^{n₀}(X,A)`".

The verticals are written as `relToAbs ≫ (cup with …)`: the absolute cohomology of the pieces is
identified with the `∅`-relative one so that the ladders of `Work.Serre.relCohMV_les_rat` (which
are indexed by the `∅`-relative groups) can be used directly, while the *hypotheses* of the
five-lemma application are the honest `Coh`-flavoured cup maps.

The three squares are `Fsquare`, `Gsquare` (naturality of the cup, from
`Work.Serre.mixedCupC_pairNatural_R` and `Work.Cohomology.relCohMap_relToAbs`) and `Hdelta`
(the crux, `Work.Serre.mvDelta_cup_mixed`, delegated separately).
-/

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

/-! ## The verticals -/

/-- The cup map with a fixed relative class, as a linear map. -/
def cupVertL {B : Type} [TopologicalSpace B] (A : Set B) (m n : ℕ)
    (z : Work.Thom.RelCoh ℚ n B A) :
    Work.Thom.Coh ℚ m B →ₗ[ℚ] Work.Thom.RelCoh ℚ (m + n) B A where
  toFun x := (Work.Thom.mixedCupC ℚ A m n) x z
  map_add' x y := by simp
  map_smul' c x := by simp

/-- The cup map with a fixed relative class, as a morphism of `ModuleCat ℚ`. -/
def cupVert {B : Type} [TopologicalSpace B] (A : Set B) (m n : ℕ)
    (z : Work.Thom.RelCoh ℚ n B A) :
    Work.Thom.Coh ℚ m B ⟶ Work.Thom.RelCoh ℚ (m + n) B A :=
  ModuleCat.ofHom (cupVertL A m n z)

/-- The `M`-vertical: `H^k(X,∅) ⟶ H^{k+n₀}(X,A)` by cupping with `U₀`. -/
def vertM (X : TopCat) (A : Set X) (n₀ : ℕ) (U₀ : Work.Thom.RelCoh ℚ n₀ X A) (k : ℕ) :
    Work.Thom.RelCoh ℚ k X (∅ : Set X) ⟶ Work.Thom.RelCoh ℚ (k + n₀) X A :=
  Work.Thom.relToAbs ℚ (∅ : Set X) k ≫ cupVert A k n₀ U₀

/-- The `U`-component of the `P`-vertical. -/
def cupVertRelU (X : TopCat) (A U : Set X) (n₀ : ℕ) (U₀ : Work.Thom.RelCoh ℚ n₀ X A) (k : ℕ) :
    mvCohU X (∅ : Set X) U k ⟶ mvCohU X A U (k + n₀) :=
  Work.Thom.relToAbs ℚ {x : ↥U | (x : X) ∈ (∅ : Set X)} k ≫
    cupVert {x : ↥U | (x : X) ∈ A} k n₀ (mvRestrU X A U n₀ U₀)

/-- The `V`-component of the `P`-vertical. -/
def cupVertRelV (X : TopCat) (A V : Set X) (n₀ : ℕ) (U₀ : Work.Thom.RelCoh ℚ n₀ X A) (k : ℕ) :
    mvCohV X (∅ : Set X) V k ⟶ mvCohV X A V (k + n₀) :=
  Work.Thom.relToAbs ℚ {x : ↥V | (x : X) ∈ (∅ : Set X)} k ≫
    cupVert {x : ↥V | (x : X) ∈ A} k n₀ (mvRestrV X A V n₀ U₀)

/-- The `P`-vertical: the biproduct of the two piecewise verticals. -/
def vertP (X : TopCat) (A U V : Set X) (n₀ : ℕ) (U₀ : Work.Thom.RelCoh ℚ n₀ X A) (k : ℕ) :
    (mvCohU X (∅ : Set X) U k ⊞ mvCohV X (∅ : Set X) V k) ⟶
      (mvCohU X A U (k + n₀) ⊞ mvCohV X A V (k + n₀)) :=
  biprod.map (cupVertRelU X A U n₀ U₀ k) (cupVertRelV X A V n₀ U₀ k)

/-- The degree identification `(k + n₀) + 1 = k + 1 + n₀` used to reindex the connecting map of
the relative Mayer–Vietoris sequence. -/
theorem mvShiftEq (k n₀ : ℕ) : (k + n₀) + 1 = k + 1 + n₀ := by omega

/-- The connecting map of the relative Mayer–Vietoris sequence, reindexed so that its target
carries the degree `k + 1 + n₀` (the shift `n₀` of the ladder). -/
def mvDeltaShift (X : TopCat) (A U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (n₀ : ℕ) (k : ℕ) :
    mvCohUV X A U V (k + n₀) ⟶ Work.Thom.RelCoh ℚ (k + 1 + n₀) X A :=
  mvDelta X A U V hU hV hcov (k + n₀) ≫
    CategoryTheory.eqToHom (congrArg (fun j => Work.Thom.RelCoh ℚ j X A)
      (mvShiftEq k n₀))

/-- The restriction of `U₀` to the overlap, as a relative class of `(U ∩ V, U ∩ V ∩ A)`. -/
abbrev U₀ovl (X : TopCat) (A U V : Set X) (n₀ : ℕ) (U₀ : Work.Thom.RelCoh ℚ n₀ X A) :
    Work.Thom.RelCoh ℚ n₀ ↥(U ∩ V) {y : ↥(U ∩ V) | (y : X) ∈ A} :=
  (mvRestrUVU X A U V n₀).hom ((mvRestrU X A U n₀).hom U₀)

/-- The `Q`-vertical: on the overlap, `H^k(U∩V,∅) ⟶ H^{k+n₀}(U∩V, U∩V∩A)`. -/
def vertQ (X : TopCat) (A U V : Set X) (n₀ : ℕ) (U₀ : Work.Thom.RelCoh ℚ n₀ X A) (k : ℕ) :
    mvCohUV X (∅ : Set X) U V k ⟶ mvCohUV X A U V (k + n₀) :=
  Work.Thom.relToAbs ℚ {y : ↥(U ∩ V) | (y : X) ∈ (∅ : Set X)} k ≫
    cupVert {y : ↥(U ∩ V) | (y : X) ∈ A} k n₀ (U₀ovl X A U V n₀ U₀)

end

end Work.Serre

namespace Work.Serre

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-! ## Naturality of the verticals -/

/-- Naturality of `relToAbs` under the restriction `U ⊆ X`, in the `U`-piece. -/
theorem restr_relToAbs_U (X : TopCat) (U : Set X) (k : ℕ) :
    mvRestrU X (∅ : Set X) U k ≫ (Work.Thom.relToAbs ℚ {x : ↥U | (x : X) ∈ (∅ : Set X)} k)
      = Work.Thom.relToAbs ℚ (∅ : Set X) k ≫
        Work.Thom.CohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥U, X)) ℚ k :=
  Work.Thom.relCohMap_relToAbs (⟨Subtype.val, continuous_subtype_val⟩ : C(↥U, X))
    {x : ↥U | (x : X) ∈ (∅ : Set X)} (∅ : Set X) (fun _ hx => hx) ℚ k

/-- Naturality of `relToAbs` under the restriction `V ⊆ X`, in the `V`-piece. -/
theorem restr_relToAbs_V (X : TopCat) (V : Set X) (k : ℕ) :
    mvRestrV X (∅ : Set X) V k ≫ (Work.Thom.relToAbs ℚ {x : ↥V | (x : X) ∈ (∅ : Set X)} k)
      = Work.Thom.relToAbs ℚ (∅ : Set X) k ≫
        Work.Thom.CohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥V, X)) ℚ k :=
  Work.Thom.relCohMap_relToAbs (⟨Subtype.val, continuous_subtype_val⟩ : C(↥V, X))
    {x : ↥V | (x : X) ∈ (∅ : Set X)} (∅ : Set X) (fun _ hx => hx) ℚ k

/-- Naturality of `relToAbs` under the restriction `U ∩ V ⊆ U`. -/
theorem restr_relToAbs_UVU (X : TopCat) (U V : Set X) (k : ℕ) :
    mvRestrUVU X (∅ : Set X) U V k ≫
        (Work.Thom.relToAbs ℚ {y : ↥(U ∩ V) | (y : X) ∈ (∅ : Set X)} k)
      = Work.Thom.relToAbs ℚ {x : ↥U | (x : X) ∈ (∅ : Set X)} k ≫
        Work.Thom.CohMap (⟨fun x => ⟨x.1, x.2.1⟩, by continuity⟩ : C(↥(U ∩ V), ↥U)) ℚ k :=
  Work.Thom.relCohMap_relToAbs
    (⟨fun x => ⟨x.1, x.2.1⟩, by continuity⟩ : C(↥(U ∩ V), ↥U))
    {y : ↥(U ∩ V) | (y : X) ∈ (∅ : Set X)} {x : ↥U | (x : X) ∈ (∅ : Set X)}
    (fun _ hx => hx) ℚ k

/-- Naturality of `relToAbs` under the restriction `U ∩ V ⊆ V`. -/
theorem restr_relToAbs_UVV (X : TopCat) (U V : Set X) (k : ℕ) :
    mvRestrUVV X (∅ : Set X) U V k ≫
        (Work.Thom.relToAbs ℚ {y : ↥(U ∩ V) | (y : X) ∈ (∅ : Set X)} k)
      = Work.Thom.relToAbs ℚ {x : ↥V | (x : X) ∈ (∅ : Set X)} k ≫
        Work.Thom.CohMap (⟨fun x => ⟨x.1, x.2.2⟩, by continuity⟩ : C(↥(U ∩ V), ↥V)) ℚ k :=
  Work.Thom.relCohMap_relToAbs
    (⟨fun x => ⟨x.1, x.2.2⟩, by continuity⟩ : C(↥(U ∩ V), ↥V))
    {y : ↥(U ∩ V) | (y : X) ∈ (∅ : Set X)} {x : ↥V | (x : X) ∈ (∅ : Set X)}
    (fun _ hx => hx) ℚ k

/-- Naturality of the cup in the `U`-piece. -/
theorem restr_cupVert_U (X : TopCat) (A U : Set X) (n₀ : ℕ)
    (U₀ : Work.Thom.RelCoh ℚ n₀ X A) (k : ℕ) :
    Work.Thom.CohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥U, X)) ℚ k ≫
        cupVert {x : ↥U | (x : X) ∈ A} k n₀ (mvRestrU X A U n₀ U₀)
      = cupVert A k n₀ U₀ ≫ mvRestrU X A U (k + n₀) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (Work.Serre.mixedCupC_pairNatural_R ℚ
    (⟨Subtype.val, continuous_subtype_val⟩ : C(↥U, X))
    {x : ↥U | (x : X) ∈ A} A (fun _ hx => hx) k n₀ x U₀).symm

/-- Naturality of the cup in the `V`-piece. -/
theorem restr_cupVert_V (X : TopCat) (A V : Set X) (n₀ : ℕ)
    (U₀ : Work.Thom.RelCoh ℚ n₀ X A) (k : ℕ) :
    Work.Thom.CohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥V, X)) ℚ k ≫
        cupVert {x : ↥V | (x : X) ∈ A} k n₀ (mvRestrV X A V n₀ U₀)
      = cupVert A k n₀ U₀ ≫ mvRestrV X A V (k + n₀) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (Work.Serre.mixedCupC_pairNatural_R ℚ
    (⟨Subtype.val, continuous_subtype_val⟩ : C(↥V, X))
    {x : ↥V | (x : X) ∈ A} A (fun _ hx => hx) k n₀ x U₀).symm

/-- Naturality of the cup under the restriction `U ∩ V ⊆ U`. -/
theorem restr_cupVert_Uovl (X : TopCat) (A U V : Set X) (n₀ : ℕ)
    (U₀ : Work.Thom.RelCoh ℚ n₀ X A) (k : ℕ) :
    Work.Thom.CohMap (⟨fun x => ⟨x.1, x.2.1⟩, by continuity⟩ : C(↥(U ∩ V), ↥U)) ℚ k ≫
        cupVert {y : ↥(U ∩ V) | (y : X) ∈ A} k n₀ (mvRestrUVU X A U V n₀ (mvRestrU X A U n₀ U₀))
      = cupVert {x : ↥U | (x : X) ∈ A} k n₀ (mvRestrU X A U n₀ U₀) ≫
        mvRestrUVU X A U V (k + n₀) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (Work.Serre.mixedCupC_pairNatural_R ℚ
    (⟨fun x => ⟨x.1, x.2.1⟩, by continuity⟩ : C(↥(U ∩ V), ↥U))
    {y : ↥(U ∩ V) | (y : X) ∈ A} {x : ↥U | (x : X) ∈ A} (fun _ hx => hx) k n₀ x
    (mvRestrU X A U n₀ U₀)).symm

/-- Naturality of the cup under the restriction `U ∩ V ⊆ V`. -/
theorem restr_cupVert_Vovl (X : TopCat) (A U V : Set X) (n₀ : ℕ)
    (U₀ : Work.Thom.RelCoh ℚ n₀ X A) (k : ℕ) :
    Work.Thom.CohMap (⟨fun x => ⟨x.1, x.2.2⟩, by continuity⟩ : C(↥(U ∩ V), ↥V)) ℚ k ≫
        cupVert {y : ↥(U ∩ V) | (y : X) ∈ A} k n₀ (mvRestrUVV X A U V n₀ (mvRestrV X A V n₀ U₀))
      = cupVert {x : ↥V | (x : X) ∈ A} k n₀ (mvRestrV X A V n₀ U₀) ≫
        mvRestrUVV X A U V (k + n₀) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (Work.Serre.mixedCupC_pairNatural_R ℚ
    (⟨fun x => ⟨x.1, x.2.2⟩, by continuity⟩ : C(↥(U ∩ V), ↥V))
    {y : ↥(U ∩ V) | (y : X) ∈ A} {x : ↥V | (x : X) ∈ A} (fun _ hx => hx) k n₀ x
    (mvRestrV X A V n₀ U₀)).symm

end

end Work.Serre

namespace Work.Serre

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-! ## The three squares of the ladder -/

/-- The `U`-component of the `F`-square. -/
theorem fst_Fsquare (X : TopCat) (A U V : Set X) (n₀ : ℕ)
    (U₀ : Work.Thom.RelCoh ℚ n₀ X A) (k : ℕ) :
    mvRestrU X (∅ : Set X) U k ≫ cupVertRelU X A U n₀ U₀ k
      = vertM X A n₀ U₀ k ≫ mvRestrU X A U (k + n₀) := by
  rw [cupVertRelU, vertM, ← Category.assoc, restr_relToAbs_U, Category.assoc,
    restr_cupVert_U, ← Category.assoc]

/-- The `V`-component of the `F`-square. -/
theorem snd_Fsquare (X : TopCat) (A U V : Set X) (n₀ : ℕ)
    (U₀ : Work.Thom.RelCoh ℚ n₀ X A) (k : ℕ) :
    mvRestrV X (∅ : Set X) V k ≫ cupVertRelV X A V n₀ U₀ k
      = vertM X A n₀ U₀ k ≫ mvRestrV X A V (k + n₀) := by
  rw [cupVertRelV, vertM, ← Category.assoc, restr_relToAbs_V, Category.assoc,
    restr_cupVert_V, ← Category.assoc]





/-- The `F`-square: `mvF` commutes with the verticals. -/
theorem Fsquare (X : TopCat) (A U V : Set X) (n₀ : ℕ)
    (U₀ : Work.Thom.RelCoh ℚ n₀ X A) (k : ℕ) :
    mvF X (∅ : Set X) U V k ≫ vertP X A U V n₀ U₀ k
      = vertM X A n₀ U₀ k ≫ mvF X A U V (k + n₀) := by
  apply biprod.hom_ext
  · rw [Category.assoc, Category.assoc,
      show (vertP X A U V n₀ U₀ k) ≫ (biprod.fst :
        (mvCohU X A U (k + n₀) ⊞ mvCohV X A V (k + n₀)) ⟶ mvCohU X A U (k + n₀))
        = (biprod.fst : (mvCohU X (∅ : Set X) U k ⊞ mvCohV X (∅ : Set X) V k) ⟶
            mvCohU X (∅ : Set X) U k) ≫ cupVertRelU X A U n₀ U₀ k
        from biprod.map_fst _ _,
      ← Category.assoc,
      show (mvF X (∅ : Set X) U V k) ≫
          (biprod.fst : (mvCohU X (∅ : Set X) U k ⊞ mvCohV X (∅ : Set X) V k) ⟶
            mvCohU X (∅ : Set X) U k)
        = mvRestrU X (∅ : Set X) U k from biprod.lift_fst _ _,
      show (mvF X A U V (k + n₀)) ≫ (biprod.fst :
          (mvCohU X A U (k + n₀) ⊞ mvCohV X A V (k + n₀)) ⟶ mvCohU X A U (k + n₀))
        = mvRestrU X A U (k + n₀) from biprod.lift_fst _ _]
    exact fst_Fsquare X A U V n₀ U₀ k
  · rw [Category.assoc, Category.assoc,
      show (vertP X A U V n₀ U₀ k) ≫ (biprod.snd :
        (mvCohU X A U (k + n₀) ⊞ mvCohV X A V (k + n₀)) ⟶ mvCohV X A V (k + n₀))
        = (biprod.snd : (mvCohU X (∅ : Set X) U k ⊞ mvCohV X (∅ : Set X) V k) ⟶
            mvCohV X (∅ : Set X) V k) ≫ cupVertRelV X A V n₀ U₀ k
        from biprod.map_snd _ _,
      ← Category.assoc,
      show (mvF X (∅ : Set X) U V k) ≫
          (biprod.snd : (mvCohU X (∅ : Set X) U k ⊞ mvCohV X (∅ : Set X) V k) ⟶
            mvCohV X (∅ : Set X) V k)
        = mvRestrV X (∅ : Set X) V k from biprod.lift_snd _ _,
      show (mvF X A U V (k + n₀)) ≫ (biprod.snd :
          (mvCohU X A U (k + n₀) ⊞ mvCohV X A V (k + n₀)) ⟶ mvCohV X A V (k + n₀))
        = mvRestrV X A V (k + n₀) from biprod.lift_snd _ _]
    exact snd_Fsquare X A U V n₀ U₀ k


/-- The `U`-component of the `G`-square. -/
theorem Gsquare_U (X : TopCat) (A U V : Set X) (n₀ : ℕ)
    (U₀ : Work.Thom.RelCoh ℚ n₀ X A) (k : ℕ) :
    mvRestrUVU X (∅ : Set X) U V k ≫ vertQ X A U V n₀ U₀ k
      = cupVertRelU X A U n₀ U₀ k ≫ mvRestrUVU X A U V (k + n₀) := by
  rw [cupVertRelU, vertQ, ← Category.assoc, restr_relToAbs_UVU, Category.assoc,
    restr_cupVert_Uovl, ← Category.assoc]


/-! ## The two spellings of the restriction of `U₀` to the overlap -/

/-- Restricting `U₀` to the overlap through `V` is the same class as restricting it through `U`. -/
theorem mvRestrVU_eq (X : TopCat) (A U V : Set X) (n₀ : ℕ) :
    mvRestrV X A V n₀ ≫ mvRestrUVV X A U V n₀ = mvRestrU X A U n₀ ≫ mvRestrUVU X A U V n₀ := by
  have hV : mvRestrV X A V n₀ ≫ mvRestrUVV X A U V n₀
      = Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(U ∩ V), X))
          {y : ↥(U ∩ V) | (y : X) ∈ A} A (fun _ hx => hx) ℚ n₀ := by
    rw [show mvRestrUVV X A U V n₀ = Work.Thom.relCohMap
          (⟨fun x => ⟨x.1, x.2.2⟩, by continuity⟩ : C(↥(U ∩ V), ↥V))
          {y : ↥(U ∩ V) | (y : X) ∈ A} {x : ↥V | (x : X) ∈ A} (fun _ hx => hx) ℚ n₀ from rfl,
      show mvRestrV X A V n₀ = Work.Thom.relCohMap
          (⟨Subtype.val, continuous_subtype_val⟩ : C(↥V, X))
          {x : ↥V | (x : X) ∈ A} A (fun _ hy => hy) ℚ n₀ from rfl,
      Work.Thom.relCohMap_compA {y : ↥(U ∩ V) | (y : X) ∈ A} {x : ↥V | (x : X) ∈ A} A
          (⟨fun x => ⟨x.1, x.2.2⟩, by continuity⟩ : C(↥(U ∩ V), ↥V))
          (⟨Subtype.val, continuous_subtype_val⟩ : C(↥V, X))
          (fun _ hx => hx) (fun _ hx => hx) (fun _ hx => hx) ℚ n₀]
    exact (Work.Thom.relCohMap_congrA _ _ (by ext x; rfl) (fun x hx => hx) (fun x hx => hx)
        ℚ n₀).trans
      (Work.Thom.relCohMap_hcongrA _ _ _ (fun x hx => hx) (fun x hx => hx) ℚ n₀)
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
  exact hV.trans hU.symm

/-- The restriction of `U₀` to the overlap, computed through `V`, is `U₀ovl`. -/
theorem U₀ovlV_eq (X : TopCat) (A U V : Set X) (n₀ : ℕ) (U₀ : Work.Thom.RelCoh ℚ n₀ X A) :
    (mvRestrUVV X A U V n₀).hom ((mvRestrV X A V n₀).hom U₀) = U₀ovl X A U V n₀ U₀ := by
  have h := congrArg (fun (f : Work.Thom.RelCoh ℚ n₀ X A ⟶ mvCohUV X A U V n₀) =>
      ModuleCat.Hom.hom f U₀) (mvRestrVU_eq X A U V n₀)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, U₀ovl] using h

/-- The `V`-component of the `G`-square. -/
theorem Gsquare_V (X : TopCat) (A U V : Set X) (n₀ : ℕ)
    (U₀ : Work.Thom.RelCoh ℚ n₀ X A) (k : ℕ) :
    mvRestrUVV X (∅ : Set X) U V k ≫ vertQ X A U V n₀ U₀ k
      = cupVertRelV X A V n₀ U₀ k ≫ mvRestrUVV X A U V (k + n₀) := by
  rw [cupVertRelV, vertQ, ← Category.assoc, restr_relToAbs_UVV, Category.assoc]
  rw [show U₀ovl X A U V n₀ U₀
        = (mvRestrUVV X A U V n₀).hom ((mvRestrV X A V n₀).hom U₀)
      from (U₀ovlV_eq X A U V n₀ U₀).symm]
  rw [restr_cupVert_Vovl, ← Category.assoc]

/-- The `G`-square. -/
theorem Gsquare (X : TopCat) (A U V : Set X) (n₀ : ℕ)
    (U₀ : Work.Thom.RelCoh ℚ n₀ X A) (k : ℕ) :
    mvG X (∅ : Set X) U V k ≫ vertQ X A U V n₀ U₀ k
      = vertP X A U V n₀ U₀ k ≫ mvG X A U V (k + n₀) := by
  rw [mvG_eq_desc, mvG_eq_desc, vertP, biprod_desc_comp, biprod_map_desc]
  refine biprod.ext_from_iff.mpr ⟨?_, ?_⟩
  · rw [biprod.inl_desc, biprod.inl_desc]
    exact Gsquare_U X A U V n₀ U₀ k
  · rw [biprod.inr_desc, biprod.inr_desc, Preadditive.neg_comp, Preadditive.comp_neg,
      Gsquare_V X A U V n₀ U₀ k]

end

end Work.Serre

namespace Work.Serre

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-! ## Transport of the ladder maps along degree identifications -/

/-- Naturality of the pullback of relative cohomology under a degree identification. -/
theorem relCohMap_eqToHom {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    (A : Set X) (B : Set Y) (hf : ∀ x ∈ A, f x ∈ B) (R : Type) [CommRing R] {a b : ℕ} (h : a = b) :
    (CategoryTheory.eqToHom (congrArg (fun j => Work.Thom.RelCoh R j Y B) h))
        ≫ Work.Thom.relCohMap f A B hf R b
      = Work.Thom.relCohMap f A B hf R a
        ≫ (CategoryTheory.eqToHom (congrArg (fun j => Work.Thom.RelCoh R j X A) h)) := by
  cases h
  simp

/-- Naturality of `mvF` under a degree identification. -/
theorem mvF_eqToHom (X : TopCat) (A U V : Set X) {a b : ℕ} (h : a = b) :
    mvF X A U V a
        ≫ (CategoryTheory.eqToHom
            (congrArg (fun j => mvCohU X A U j ⊞ mvCohV X A V j) h))
      = (CategoryTheory.eqToHom (congrArg (fun j => Work.Thom.RelCoh ℚ j X A) h))
        ≫ mvF X A U V b := by
  cases h
  simp [mvF]

/-- **Transporting a kernel along an isomorphism of the source.**  If `f ≫ e' = e ≫ g` with `e` an
isomorphism, the kernel of `g` is the image of the kernel of `f` under `e`. -/
theorem map_hom_ker_eq_ker {A B C D : ModuleCat ℚ} (e : A ≅ B) (e' : C ≅ D)
    (f : A ⟶ C) (g : B ⟶ D) (h : f ≫ e'.hom = e.hom ≫ g) :
    Submodule.map e.hom.hom (LinearMap.ker f.hom) = LinearMap.ker g.hom := by
  have hh : e'.hom.hom.comp f.hom = g.hom.comp e.hom.hom := by
    have h1 := congrArg ModuleCat.Hom.hom h
    simpa only [ModuleCat.hom_comp] using h1
  have h3 : ∀ x : B, e.hom.hom (e.inv.hom x) = x := fun x => by
    have h4 := congrArg (fun (kk : B ⟶ B) => ModuleCat.Hom.hom kk x) (Iso.inv_hom_id e)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
      LinearMap.id_apply] using h4
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have h2 := DFunLike.congr_fun hh y
    simp only [LinearMap.comp_apply, LinearMap.mem_ker] at h2 hy ⊢
    rw [← h2, hy, map_zero]
  · intro hx
    refine ⟨e.inv.hom x, ?_, ?_⟩
    · have h2 := DFunLike.congr_fun hh (e.inv.hom x)
      simp only [LinearMap.comp_apply, LinearMap.mem_ker] at h2
      rw [h3 x] at h2
      exact injective_hom_of_iso e' (by rw [h2, hx, map_zero])
    · exact h3 x

/-- **Transporting a kernel along an isomorphism of the target**: if `e` is an isomorphism then
`ker (f ≫ e) = ker f`. -/
theorem ker_comp_iso_hom' {M N P : ModuleCat ℚ} (f : M ⟶ N) (e : N ≅ P) :
    LinearMap.ker ((f ≫ e.hom).hom) = LinearMap.ker f.hom := by
  rw [ModuleCat.hom_comp, LinearMap.ker_comp,
    LinearMap.ker_eq_bot.mpr (injective_hom_of_iso e), Submodule.comap_bot]

/-- The exactness at the overlap in the shifted form. -/
theorem exact_mvDeltaShift_mvF (X : TopCat) (A U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (n₀ k : ℕ) :
    LinearMap.range ((mvDeltaShift X A U V hU hV hcov n₀ k).hom)
      = LinearMap.ker ((mvF X A U V (k + 1 + n₀)).hom) := by
  rw [mvDeltaShift, ModuleCat.hom_comp, LinearMap.range_comp,
    exact_mvDelta_mvF X A U V hU hV hcov (k + n₀)]
  rw [show (CategoryTheory.eqToHom (congrArg (fun j => Work.Thom.RelCoh ℚ j X A)
        (mvShiftEq k n₀))).hom
      = (CategoryTheory.eqToIso (congrArg (fun j => Work.Thom.RelCoh ℚ j X A)
        (mvShiftEq k n₀))).hom.hom from rfl]
  exact map_hom_ker_eq_ker
    (CategoryTheory.eqToIso (congrArg (fun j => Work.Thom.RelCoh ℚ j X A) (mvShiftEq k n₀)))
    (CategoryTheory.eqToIso
      (congrArg (fun j => mvCohU X A U j ⊞ mvCohV X A V j) (mvShiftEq k n₀)))
    (mvF X A U V ((k + n₀) + 1)) (mvF X A U V (k + 1 + n₀))
    (mvF_eqToHom X A U V (mvShiftEq k n₀))

/-- The exactness at the overlap in the shifted form, third spot. -/
theorem exact_mvG_mvDelta_shift (X : TopCat) (A U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (n₀ k : ℕ) :
    LinearMap.range ((mvG X A U V (k + n₀)).hom)
      = LinearMap.ker ((mvDeltaShift X A U V hU hV hcov n₀ k).hom) := by
  rw [mvDeltaShift, exact_mvG_mvDelta X A U V hU hV hcov (k + n₀)]
  exact (ker_comp_iso_hom' (mvDelta X A U V hU hV hcov (k + n₀))
    (CategoryTheory.eqToIso (congrArg (fun j => Work.Thom.RelCoh ℚ j X A)
      (mvShiftEq k n₀)))).symm

/-- **The ladder lemma.**  If the ladder between the two rational relative Mayer–Vietoris long
exact sequences of the cover `X = U ∪ V` (relative parts `∅` and `A`, the second shifted by `n₀`)
commutes with the verticals `vertM`, `vertP`, `vertQ`, and if the verticals of the pieces are
isomorphisms in the two relevant degrees, then the `M`-vertical is an isomorphism one degree
higher. -/
theorem ladder_vertM_isIso (X : TopCat) (A U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (n₀ : ℕ) (U₀ : Work.Thom.RelCoh ℚ n₀ X A)
    (Hdelta : ∀ k : ℕ,
      mvDelta X (∅ : Set X) U V hU hV hcov k ≫ vertM X A n₀ U₀ (k + 1)
        = vertQ X A U V n₀ U₀ k ≫ mvDeltaShift X A U V hU hV hcov n₀ k)
    (k : ℕ) (hP₀ : IsIso (vertP X A U V n₀ U₀ k)) (hQ₀ : IsIso (vertQ X A U V n₀ U₀ k))
    (hP₁ : IsIso (vertP X A U V n₀ U₀ (k + 1))) (hQ₁ : IsIso (vertQ X A U V n₀ U₀ (k + 1))) :
    IsIso (vertM X A n₀ U₀ (k + 1)) := by
  refine fiveLemma_LES_first
    (M₁ := fun j => Work.Thom.RelCoh ℚ j X (∅ : Set X))
    (P₁ := fun j => mvCohU X (∅ : Set X) U j ⊞ mvCohV X (∅ : Set X) V j)
    (Q₁ := fun j => mvCohUV X (∅ : Set X) U V j)
    (M₂ := fun j => Work.Thom.RelCoh ℚ (j + n₀) X A)
    (P₂ := fun j => mvCohU X A U (j + n₀) ⊞ mvCohV X A V (j + n₀))
    (Q₂ := fun j => mvCohUV X A U V (j + n₀))
    (F₁ := fun j => mvF X (∅ : Set X) U V j) (G₁ := fun j => mvG X (∅ : Set X) U V j)
    (δ₁ := fun j => mvDelta X (∅ : Set X) U V hU hV hcov j)
    (F₂ := fun j => mvF X A U V (j + n₀)) (G₂ := fun j => mvG X A U V (j + n₀))
    (δ₂ := fun j => mvDeltaShift X A U V hU hV hcov n₀ j)
    (e₂₁ := fun j => exact_mvF_mvG X (∅ : Set X) U V hU hV hcov j)
    (e₃₁ := fun j => exact_mvG_mvDelta X (∅ : Set X) U V hU hV hcov j)
    (e₁₁ := fun j => exact_mvDelta_mvF X (∅ : Set X) U V hU hV hcov j)
    (e₂₂ := fun j => exact_mvF_mvG X A U V hU hV hcov (j + n₀))
    (e₃₂ := fun j => exact_mvG_mvDelta_shift X A U V hU hV hcov n₀ j)
    (e₁₂ := fun j => exact_mvDeltaShift_mvF X A U V hU hV hcov n₀ j)
    (TM := fun j => vertM X A n₀ U₀ j) (TP := fun j => vertP X A U V n₀ U₀ j)
    (TQ := fun j => vertQ X A U V n₀ U₀ j)
    (hF := fun j => Fsquare X A U V n₀ U₀ j) (hG := fun j => Gsquare X A U V n₀ U₀ j)
    (hδ := Hdelta) k hP₀ hQ₀ hP₁ hQ₁

end

end Work.Serre
