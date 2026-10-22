import Mathlib
import Submission.Work.ANALYTIC.Basic
import Submission.Work.ANALYTIC.whiskerRight_sub_lightCondMod

namespace Work.ANALYTIC

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed

open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

/-! ## Auxiliary facts about the tensor product of light condensed abelian groups

The proof below needs the fact that the tensor product of light condensed abelian groups is
additive in each variable; this is not in Mathlib and is proved (for an arbitrary commutative
base ring) in `Submission/Work/ANALYTIC/whiskerRight_sub_lightCondMod.lean`.  For the base ring
`ℤ` of `LightCondAb` it reads `(f - g) ▷ V = f ▷ V - g ▷ V`. -/

/-- The single-object functor `C ⥤ D(C)` of `LightCondAb` in degree `0`, i.e.
`X ↦ X[0]`. -/
abbrev singleFunctor0 : LightCondAb ⥤ DLightCondAb := DerivedCategory.singleFunctor LightCondAb 0

namespace Work.ANALYTIC

open _root_.LightCondensed _root_.LightCondensed.Solid

/-- **ℝ-module objects are solid-null (REFS/03 §3, RC Thm 3.2.4(4)).**  Let `V` carry an action `act : R ⊗ V ⟶ V` of a light condensed abelian group `R`, let `f : P ⟶ R`, `F G : P ⟶ P` and `e₀ e₁ : 𝟙_ ⟶ P` satisfy the parametrised null-sequence identities of REFS/03 §3: `F ≫ f = f`, `F ≫ oneMinusShift = oneMinusShift ≫ G`, `e₀ ≫ G = e₁`, `e₀ ≫ oneMinusShift = e₀ - e₁`, and let `act` be unital along `f e₀`.  Then `Hom_D(V, ι N) = 0` for every complex `N` of solid objects.

Proof (REFS/03 §3): let `T = (1-S) ⊗ id_V` and `A = single 0 (P ⊗ V)`.  By `PreSolid V`, precomposition by `T` on `Hom_D(A, ι N)` is bijective; let `γ : A ⟶ ι N` be the unique morphism with `T ≫ γ = (single (f ▷ V)) ≫ (single act) ≫ φ`.  Since `(single ((G ▷ V))) ≫ T = T ≫ (single ((F ▷ V)))` by `h₂` and `F ≫ f = f` by `h₁`, the morphism `(single (G ▷ V)) ≫ γ` satisfies the same defining equation as `γ`, so `(single (G ▷ V)) ≫ γ = γ`.  Put `x₀ := (single ((λ_ V).inv)) ≫ (single (e₀ ▷ V)) ≫ γ` and `x₁ := (single ((λ_ V).inv)) ≫ (single (e₁ ▷ V)) ≫ γ` (these are maps `single 0 V ⟶ ι N`).  Then `h₃` gives `x₀ = x₁`, while `h₄` and `h₅` give `x₀ - x₁ = φ`.  Hence `φ = 0`. -/
theorem solidNull_of_unit_action (R V : LightCondAb) (act : R ⊗ V ⟶ V)
    (f : P ⟶ R) (F G : P ⟶ P) (e₀ e₁ : 𝟙_ LightCondAb ⟶ P)
    (h₁ : F ≫ f = f)
    (h₂ : F ≫ oneMinusShift = oneMinusShift ≫ G)
    (h₃ : e₀ ≫ G = e₁)
    (h₄ : e₀ ≫ oneMinusShift = e₀ - e₁)
    (h₅ : (e₀ ▷ V) ≫ (f ▷ V) ≫ act = (λ_ V).hom)
    (hpre : PreSolid V) :
    SolidNull ((DerivedCategory.singleFunctor LightCondAb 0).obj V) := by
  intro N
  -- it suffices to show that every morphism `V[0] ⟶ ι N` is zero
  have hzero : ∀ φ : singleFunctor0.obj V ⟶ derivedInclusion.obj N, φ = 0 := by
    intro φ
    -- `T = (1 - S) ⊗ id_V`
    let T : P ⊗ V ⟶ P ⊗ V := tensorOneMinusShift V
    have hT : T = oneMinusShift ▷ V := rfl
    -- precomposition by `T` is bijective on `Hom_D(P ⊗ V, ι N)`
    have hbij : Function.Bijective
        (fun g : singleFunctor0.obj (P ⊗ V) ⟶ derivedInclusion.obj N =>
          singleFunctor0.map T ≫ g) := hpre N
    -- the right hand side of the defining equation of `γ`
    let ψ' : singleFunctor0.obj (P ⊗ V) ⟶ derivedInclusion.obj N :=
      singleFunctor0.map (f ▷ V) ≫ singleFunctor0.map act ≫ φ
    obtain ⟨γ, hγ⟩ : ∃ γ : singleFunctor0.obj (P ⊗ V) ⟶ derivedInclusion.obj N,
        singleFunctor0.map T ≫ γ = ψ' :=
      ⟨Classical.choose (hbij.2 ψ'), Classical.choose_spec (hbij.2 ψ')⟩
    -- the maps `(λ_ V).inv ≫ (e_i ▷ V) : V ⟶ P ⊗ V`
    let a₀ : V ⟶ P ⊗ V := (λ_ V).inv ≫ (e₀ ▷ V)
    let a₁ : V ⟶ P ⊗ V := (λ_ V).inv ≫ (e₁ ▷ V)
    let A₀ : singleFunctor0.obj V ⟶ singleFunctor0.obj (P ⊗ V) := singleFunctor0.map a₀
    let A₁ : singleFunctor0.obj V ⟶ singleFunctor0.obj (P ⊗ V) := singleFunctor0.map a₁
    -- the null-sequence identities, whiskered with `V`
    have hGT : T ≫ (G ▷ V) = (F ▷ V) ≫ T := by
      rw [hT, ← comp_whiskerRight, ← h₂, comp_whiskerRight]
    have hFf : (F ▷ V) ≫ (f ▷ V) = (f ▷ V) := by
      rw [← comp_whiskerRight, h₁]
    -- `single (G ▷ V) ≫ γ = γ`, by uniqueness of `γ`
    have hGγ : singleFunctor0.map (G ▷ V) ≫ γ = γ := by
      apply hbij.1
      have hψ : singleFunctor0.map (F ▷ V) ≫ ψ' = ψ' := by
        simp only [ψ']
        rw [← Category.assoc, ← Functor.map_comp, hFf]
      calc singleFunctor0.map T ≫ (singleFunctor0.map (G ▷ V) ≫ γ)
          = singleFunctor0.map (F ▷ V) ≫ singleFunctor0.map T ≫ γ := by
            rw [← Category.assoc, ← Functor.map_comp, hGT, Functor.map_comp, Category.assoc]
        _ = singleFunctor0.map T ≫ γ := by rw [hγ, hψ, ← hγ]
    -- `h₃` whiskered with `V`
    have ha₁ : a₁ = a₀ ≫ (G ▷ V) := by
      show (λ_ V).inv ≫ (e₁ ▷ V) = ((λ_ V).inv ≫ (e₀ ▷ V)) ≫ (G ▷ V)
      rw [← h₃, comp_whiskerRight, Category.assoc]
    -- unitality: `a₀ ≫ (f ▷ V) ≫ act = id`
    have ha₀act : a₀ ≫ (f ▷ V) ≫ act = 𝟙 V := by
      show ((λ_ V).inv ≫ (e₀ ▷ V)) ≫ (f ▷ V) ≫ act = 𝟙 V
      rw [Category.assoc, h₅, Iso.inv_hom_id]
    -- `h₄` whiskered: `a₀ - a₁ = a₀ ≫ T`
    have ha₀T : a₀ ≫ T = a₀ - a₁ := by
      have h1 : a₀ - a₁ = (λ_ V).inv ≫ ((e₀ ▷ V) - (e₁ ▷ V)) := by
        simp only [a₀, a₁, Preadditive.comp_sub]
      have h2 : (e₀ ▷ V) - (e₁ ▷ V) = (e₀ ≫ oneMinusShift) ▷ V := by
        rw [← whiskerRight_sub_lightCondMod ℤ V e₀ e₁, ← h₄]
      have h3 : (e₀ ≫ oneMinusShift) ▷ V = (e₀ ▷ V) ≫ T := by
        rw [comp_whiskerRight, ← hT]
      rw [h1, h2, h3, ← Category.assoc]
    have hA₁ : A₁ = A₀ ≫ singleFunctor0.map (G ▷ V) := by
      show singleFunctor0.map a₁ = singleFunctor0.map a₀ ≫ singleFunctor0.map (G ▷ V)
      rw [ha₁, Functor.map_comp]
    have hsub : A₀ ≫ singleFunctor0.map T = A₀ - A₁ := by
      show singleFunctor0.map a₀ ≫ singleFunctor0.map T
          = singleFunctor0.map a₀ - singleFunctor0.map a₁
      rw [← Functor.map_comp, ha₀T, Functor.map_sub]
    -- `h₃` gives `x₀ = x₁`
    have hx : A₁ ≫ γ = A₀ ≫ γ := by rw [hA₁, Category.assoc, hGγ]
    -- the defining equation of `γ` together with `h₅` gives `φ = A₀ ≫ T ≫ γ`
    have hφ : φ = A₀ ≫ singleFunctor0.map T ≫ γ := by
      have e1 : (singleFunctor0.map a₀ ≫ singleFunctor0.map (f ▷ V)) ≫ singleFunctor0.map act
          = 𝟙 (singleFunctor0.obj V) := by
        rw [Category.assoc, ← Functor.map_comp, ← Functor.map_comp, ha₀act]
        exact CategoryTheory.Functor.map_id singleFunctor0 V
      have e2 : singleFunctor0.map a₀ ≫ ψ' = φ := by
        simp only [ψ']
        rw [← Category.assoc, ← Category.assoc, e1, Category.id_comp]
      rw [hγ, show A₀ = singleFunctor0.map a₀ from rfl, e2]
    -- `φ = x₀ - x₁ = 0`
    rw [hφ, ← Category.assoc, hsub, Preadditive.sub_comp, hx, sub_self]
  exact ⟨fun φ η => by rw [hzero φ, hzero η]⟩

end Work.ANALYTIC

/-- The statement of `Work.ANALYTIC.Work.ANALYTIC.solidNull_of_unit_action` under the name
`Work.ANALYTIC.solidNull_of_unit_action`, which is the name derived from the module path
`Submission.Work.ANALYTIC.solidNull_of_unit_action`. -/
theorem solidNull_of_unit_action (R V : LightCondAb) (act : R ⊗ V ⟶ V)
    (f : P ⟶ R) (F G : P ⟶ P) (e₀ e₁ : 𝟙_ LightCondAb ⟶ P)
    (h₁ : F ≫ f = f)
    (h₂ : F ≫ oneMinusShift = oneMinusShift ≫ G)
    (h₃ : e₀ ≫ G = e₁)
    (h₄ : e₀ ≫ oneMinusShift = e₀ - e₁)
    (h₅ : (e₀ ▷ V) ≫ (f ▷ V) ≫ act = (λ_ V).hom)
    (hpre : PreSolid V) :
    SolidNull ((DerivedCategory.singleFunctor LightCondAb 0).obj V) :=
  _root_.Work.ANALYTIC.Work.ANALYTIC.solidNull_of_unit_action R V act f F G e₀ e₁
    h₁ h₂ h₃ h₄ h₅ hpre
