import Mathlib
import ChallengeDeps
import Submission.Blueprint.Interfaces
import Submission.Work.ANALYTIC.Basic
import Submission.Work.ANALYTIC.solidNull_of_unit_action
import Submission.Work.ANALYTIC.whiskerRight_sub_lightCondMod

/-!
# Helpers for AN2: the "null family" form of `solidNull_of_unit_action`, and assorted lemmas

This file collects general-purpose lemmas used by the proof of
`Work.ANALYTIC.boundedSeqIncl_solidEquiv` (AN2, REFS/03 §3):

* `Work.ANALYTIC.solidNull_of_nullFamily`: a variant of
  `Work.ANALYTIC.solidNull_of_unit_action` in which the ring-valued action is replaced by a single
  morphism `σ : P ⊗ V ⟶ V` whose `0`-th component is the identity and which is invariant under the
  fixed endomorphism `F` of `P` of REFS/03 §3.  (The proof is the proof of
  `solidNull_of_unit_action` with `act' := (f ▷ V) ≫ act`.)
* `Work.ANALYTIC.instZeroLightCondAb`: a zero object of `LightCondAb`, so that short complexes
  `X --id--> X --0--> 0` can be written down.
* `Work.ANALYTIC.shortExact_singleObj`: short exact sequences of light condensed abelian groups
  stay short exact after placing them in degree `0`.
* `Work.ANALYTIC.solidEquiv_zero_iff`: `SolidEquiv` of a morphism out of a zero object is
  `SolidNull` of the target.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

namespace Work.ANALYTIC

/-- A zero object of `LightCondAb`, useful for writing short complexes `X --𝟙--> X --0--> 0`. -/
noncomputable instance instZeroLightCondAb : Zero LightCondAb := HasZeroObject.zero' LightCondAb

/-- The tensor product `P ⊗ V`, written as a one-argument construction so that the statement of
`Work.ANALYTIC.solidNull_of_nullFamily` below can be written without monoidal notation. -/
abbrev PTensor (V : LightCondAb) : LightCondAb := P ⊗ V

/-- `σ : P ⊗ V ⟶ V` is invariant under the endomorphism `F` of `P`. -/
def NullInvariance (V : LightCondAb) (σ : PTensor V ⟶ V) (F : P ⟶ P) : Prop :=
  (F ▷ V) ≫ σ = σ

/-- The `0`-th component of `σ : P ⊗ V ⟶ V` is the identity. -/
def NullUnit (V : LightCondAb) (σ : PTensor V ⟶ V) (e : 𝟙_ LightCondAb ⟶ P) : Prop :=
  (e ▷ V) ≫ σ = (λ_ V).hom

/-- `F` intertwines `(1 - S)` with `G` (identity `h₂` of REFS/03 §1). -/
def NullShift (F G : P ⟶ P) : Prop := F ≫ oneMinusShift = oneMinusShift ≫ G

/-- `e₀` and `e₁` are related by `G` (identity `h₃` of REFS/03 §1). -/
def NullPoint (e₀ : 𝟙_ LightCondAb ⟶ P) (G : P ⟶ P) (e₁ : 𝟙_ LightCondAb ⟶ P) : Prop :=
  e₀ ≫ G = e₁

/-- `e₀ (1 - S) = e₀ - e₁` (identity `h₄` of REFS/03 §1). -/
def NullUnitShift (e₀ e₁ : 𝟙_ LightCondAb ⟶ P) : Prop :=
  e₀ ≫ oneMinusShift = e₀ - e₁

/-- **The null-family form of REFS/03 §3.**  Let `σ : P ⊗ V ⟶ V` be a null family of endomorphisms
of `V` whose `0`-th component is the identity (`NullUnit`) and which is invariant under the fixed
endomorphism `F` of `P` (`NullInvariance`), and let `e₀, e₁, F, G` satisfy the four identities
`h₂`–`h₄` of REFS/03 §1.  Then every morphism `V[0] ⟶ ι N` in the derived category is zero.

This is `Work.ANALYTIC.solidNull_of_unit_action` with `R := P`, `f := 𝟙`, `act := σ`: the proof
below is that proof, with the single hypothesis `(F ▷ V) ≫ σ = σ` replacing the pair of hypotheses
`F ≫ f = f` and `σ = (f ▷ V) ≫ act`. -/
theorem solidNull_of_nullFamily (V : LightCondAb) (σ : PTensor V ⟶ V) (F G : P ⟶ P)
    (e₀ e₁ : 𝟙_ LightCondAb ⟶ P)
    (h₁ : NullInvariance V σ F) (h₂ : NullShift F G) (h₃ : NullPoint e₀ G e₁)
    (h₄ : NullUnitShift e₀ e₁) (h₅ : NullUnit V σ e₀) (hpre : PreSolid V) :
    SolidNull ((DerivedCategory.singleFunctor LightCondAb 0).obj V) := by
  intro N
  have hzero : ∀ φ : (DerivedCategory.singleFunctor LightCondAb 0).obj V ⟶
      derivedInclusion.obj N, φ = 0 := by
    intro φ
    let T : P ⊗ V ⟶ P ⊗ V := tensorOneMinusShift V
    have hT : T = oneMinusShift ▷ V := rfl
    have hbij : Function.Bijective
        (fun g : (DerivedCategory.singleFunctor LightCondAb 0).obj (P ⊗ V) ⟶
            derivedInclusion.obj N =>
          (DerivedCategory.singleFunctor LightCondAb 0).map T ≫ g) := hpre N
    let ψ' : (DerivedCategory.singleFunctor LightCondAb 0).obj (P ⊗ V) ⟶
        derivedInclusion.obj N :=
      (DerivedCategory.singleFunctor LightCondAb 0).map σ ≫ φ
    obtain ⟨γ, hγ⟩ : ∃ γ : (DerivedCategory.singleFunctor LightCondAb 0).obj (P ⊗ V) ⟶
        derivedInclusion.obj N,
        (DerivedCategory.singleFunctor LightCondAb 0).map T ≫ γ = ψ' :=
      ⟨Classical.choose (hbij.2 ψ'), Classical.choose_spec (hbij.2 ψ')⟩
    let a₀ : V ⟶ P ⊗ V := (λ_ V).inv ≫ (e₀ ▷ V)
    let a₁ : V ⟶ P ⊗ V := (λ_ V).inv ≫ (e₁ ▷ V)
    let A₀ : (DerivedCategory.singleFunctor LightCondAb 0).obj V ⟶
        (DerivedCategory.singleFunctor LightCondAb 0).obj (P ⊗ V) :=
      (DerivedCategory.singleFunctor LightCondAb 0).map a₀
    let A₁ : (DerivedCategory.singleFunctor LightCondAb 0).obj V ⟶
        (DerivedCategory.singleFunctor LightCondAb 0).obj (P ⊗ V) :=
      (DerivedCategory.singleFunctor LightCondAb 0).map a₁
    have hGT : T ≫ (G ▷ V) = (F ▷ V) ≫ T := by
      rw [hT, ← comp_whiskerRight, ← h₂, comp_whiskerRight]
    have hFσ : (F ▷ V) ≫ σ = σ := h₁
    have hGγ : (DerivedCategory.singleFunctor LightCondAb 0).map (G ▷ V) ≫ γ = γ := by
      apply hbij.1
      have hψ : (DerivedCategory.singleFunctor LightCondAb 0).map (F ▷ V) ≫ ψ' = ψ' := by
        simp only [ψ']
        rw [← Category.assoc, ← Functor.map_comp, hFσ]
      calc (DerivedCategory.singleFunctor LightCondAb 0).map T ≫
            ((DerivedCategory.singleFunctor LightCondAb 0).map (G ▷ V) ≫ γ)
          = (DerivedCategory.singleFunctor LightCondAb 0).map (F ▷ V) ≫
              (DerivedCategory.singleFunctor LightCondAb 0).map T ≫ γ := by
            rw [← Category.assoc, ← Functor.map_comp, hGT, Functor.map_comp, Category.assoc]
        _ = (DerivedCategory.singleFunctor LightCondAb 0).map T ≫ γ := by rw [hγ, hψ, ← hγ]
    have ha₁ : a₁ = a₀ ≫ (G ▷ V) := by
      show (λ_ V).inv ≫ (e₁ ▷ V) = ((λ_ V).inv ≫ (e₀ ▷ V)) ≫ (G ▷ V)
      rw [← h₃, comp_whiskerRight, Category.assoc]
    have ha₀σ : a₀ ≫ σ = 𝟙 V := by
      show ((λ_ V).inv ≫ (e₀ ▷ V)) ≫ σ = 𝟙 V
      rw [Category.assoc, h₅, Iso.inv_hom_id]
    have ha₀T : a₀ ≫ T = a₀ - a₁ := by
      have h1 : a₀ - a₁ = (λ_ V).inv ≫ ((e₀ ▷ V) - (e₁ ▷ V)) := by
        simp only [a₀, a₁, Preadditive.comp_sub]
      have h2 : (e₀ ▷ V) - (e₁ ▷ V) = (e₀ ≫ oneMinusShift) ▷ V := by
        rw [← whiskerRight_sub_lightCondMod ℤ V e₀ e₁, ← h₄]
      have h3 : (e₀ ≫ oneMinusShift) ▷ V = (e₀ ▷ V) ≫ T := by
        rw [comp_whiskerRight, ← hT]
      rw [h1, h2, h3, ← Category.assoc]
    have hA₁ : A₁ = A₀ ≫ (DerivedCategory.singleFunctor LightCondAb 0).map (G ▷ V) := by
      show (DerivedCategory.singleFunctor LightCondAb 0).map a₁ = _ ≫ _
      rw [ha₁, Functor.map_comp]
    have hsub : A₀ ≫ (DerivedCategory.singleFunctor LightCondAb 0).map T = A₀ - A₁ := by
      show (DerivedCategory.singleFunctor LightCondAb 0).map a₀ ≫ _ = _ - _
      rw [← Functor.map_comp, ha₀T, Functor.map_sub]
    have hx : A₁ ≫ γ = A₀ ≫ γ := by rw [hA₁, Category.assoc, hGγ]
    have hφ : φ = A₀ ≫ (DerivedCategory.singleFunctor LightCondAb 0).map T ≫ γ := by
      have e1 : ((DerivedCategory.singleFunctor LightCondAb 0).map a₀ ≫
          (DerivedCategory.singleFunctor LightCondAb 0).map σ) = 𝟙 _ := by
        rw [← Functor.map_comp, ha₀σ]
        exact CategoryTheory.Functor.map_id _ _
      have e2 : (DerivedCategory.singleFunctor LightCondAb 0).map a₀ ≫ ψ' = φ := by
        simp only [ψ']
        rw [← Category.assoc, e1, Category.id_comp]
      rw [hγ, show A₀ = _ from rfl, e2]
    rw [hφ, ← Category.assoc, hsub, Preadditive.sub_comp, hx, sub_self]
  exact ⟨fun φ η => by rw [hzero φ, hzero η]⟩

/-- **Short exactness is preserved by placing a light condensed abelian group in degree `0`.** -/
theorem shortExact_singleObj {S : ShortComplex LightCondAb} (hS : S.ShortExact) :
    (S.map (HomologicalComplex.single LightCondAb (ComplexShape.up ℤ) 0)).ShortExact :=
  hS.map_of_exact _

/-- The short complex `X --𝟙--> X --0--> 0` is short exact. -/
theorem shortExact_id_zero (X : LightCondAb) :
    (ShortComplex.mk (𝟙 X) (0 : X ⟶ (0 : LightCondAb)) (by simp)).ShortExact := by
  refine ShortComplex.Splitting.shortExact
    ⟨𝟙 X, (0 : (0 : LightCondAb) ⟶ X), by simp, ?_, by simp⟩
  simp

/-- **`SolidEquiv` of a morphism out of a zero object is `SolidNull` of the target.** -/
theorem solidEquiv_zero_iff {X Y : DLightCondAb} (f : X ⟶ Y) (hX : IsZero X) :
    Submission.Blueprint.SolidEquiv f ↔
      ∀ N : DSolid, Subsingleton (Y ⟶ derivedInclusion.obj N) := by
  constructor
  · intro h N
    exact ⟨fun a b => (h N).1 (by
      have h₁ : f ≫ a = f ≫ b := hX.eq_of_src _ _
      simpa using h₁)⟩
  · intro h N
    haveI := h N
    refine ⟨fun a b _ => Subsingleton.elim a b, fun b => ⟨0, ?_⟩⟩
    exact hX.eq_of_src _ _

end Work.ANALYTIC
