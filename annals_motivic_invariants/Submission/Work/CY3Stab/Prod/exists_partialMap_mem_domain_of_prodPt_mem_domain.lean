import Mathlib
import Submission.Work.CY3Stab.Prod.SecAt
import Submission.Work.K3.BaseChangeBirational
import Submission.Work.K3Inputs.exists_variety_prodOver_affineSpace
import Submission.Work.CY3Stab.Prod.CylFF
import Submission.Work.CY3Stab.Prod.isIntegral_wProd
import Submission.Work.CY3Stab.Prod.exists_algebraMap_eq_of_algebraMap_comp_eq
import Submission.Work.CY3Stab.Prod.eq_of_specMap_algebraMap_eq_of_apply_closedPoint_eq
import Submission.Work.CY3Stab.Prod.fromFunctionField_baseChangeAlong_compHom

set_option linter.unusedVariables false -- v435-speed

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

/-!
# `Work.CY3Stab.Prod.exists_partialMap_mem_domain_of_prodPt_mem_domain`

A partial map on the cylinder `𝔸ᵏ ×_𝕜 X` which is the base change of a partial map `g₀` on `X`
descends: at every point `y` of its domain, the germ of `G` factors through the projection and is
the germ of a partial map of `X` with the same rational map as `g₀`.

The proof follows `Submission/Work/CY3Stab/Prod/NOTES_partialMap_domain.md`.  The germ
`α = G.fromSpecStalkOfMem hyG` is compared, using
`Work.CY3Stab.Prod.eq_of_specMap_algebraMap_eq_of_apply_closedPoint_eq` (morphisms out of the
spectrum of a local ring are determined by their generic restriction and the image of the closed
point), with a morphism `Spec 𝒪_{X,x} ⟶ Y` manufactured from `α` by the affine-chart argument of
the notes, where the descent of regularity uses
`Work.CY3Stab.Prod.exists_algebraMap_eq_of_algebraMap_comp_eq` (regularity descends along the flat
map of stalks).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

namespace Work.CY3Stab.Prod

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

variable {𝕜 : Type} [Field 𝕜] {X Y : AlgebraicGeometry.Scheme.{0}}
  [X.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
  [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]

/-- The function field restriction of a partial map over `S` is an `S`-morphism. -/
lemma PartialMap.fromFunctionField_comp {S : Scheme.{0}} (f : X.PartialMap Y) [IrreducibleSpace X]
    [X.Over S] [Y.Over S] [f.IsOver S] :
    f.fromFunctionField ≫ (Y ↘ S) = X.fromSpecStalk (genericPoint X) ≫ (X ↘ S) := by
  have h : f.hom ≫ (Y ↘ S) = f.domain.ι ≫ (X ↘ S) := by
    simpa only [Scheme.PartialMap.compHom] using
      (PartialMap.isOver_iff (S := S) (f := f)).mp ‹f.IsOver S›
  simp only [Scheme.PartialMap.fromFunctionField, Scheme.PartialMap.fromSpecStalkOfMem]
  rw [Category.assoc, h, ← Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]

theorem exists_partialMap_mem_domain_of_prodPt_mem_domain
    {𝕜 : Type} [Field 𝕜] {X Y : AlgebraicGeometry.Scheme.{0}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    [AlgebraicGeometry.IsIntegral X]
    [AlgebraicGeometry.LocallyOfFiniteType (Work.CY3Stab.Prod.overHom (𝕜 := 𝕜) Y)]
    (k : ℕ) (y : Work.CY3Stab.WProd (𝕜 := 𝕜) X k)
    (g₀ : X.PartialMap Y) [g₀.IsOver (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    (G : (Work.CY3Stab.WProd (𝕜 := 𝕜) X k).PartialMap Y)
    (heq : G.toRationalMap = ((Work.K3.PartialMap.baseChangeAlong
        (Work.CY3Stab.Prod.overHom (𝕜 := 𝕜) (Work.CY3Stab.AffineK (𝕜 := 𝕜) k)) g₀).compHom
          (CategoryTheory.Limits.pullback.snd (Work.CY3Stab.Prod.overHom (𝕜 := 𝕜)
            (Work.CY3Stab.AffineK (𝕜 := 𝕜) k))
            (Work.CY3Stab.Prod.overHom (𝕜 := 𝕜) Y))).toRationalMap)
    (hyG : y ∈ G.domain) :
    ∃ (g : X.PartialMap Y)
      (hxg : CategoryTheory.Limits.pullback.snd (Work.CY3Stab.Prod.overHom (𝕜 := 𝕜)
        (Work.CY3Stab.AffineK (𝕜 := 𝕜) k)) (Work.CY3Stab.Prod.overHom (𝕜 := 𝕜) X) y ∈ g.domain),
      g.IsOver (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)) ∧
        g.toRationalMap = g₀.toRationalMap ∧
        G.fromSpecStalkOfMem hyG = CategoryTheory.CategoryStruct.comp
          (AlgebraicGeometry.Spec.map ((CategoryTheory.Limits.pullback.snd
              (Work.CY3Stab.Prod.overHom (𝕜 := 𝕜) (Work.CY3Stab.AffineK (𝕜 := 𝕜) k))
              (Work.CY3Stab.Prod.overHom (𝕜 := 𝕜) X)).stalkMap y))
          (g.fromSpecStalkOfMem hxg) 
:= by

  classical
  haveI hWXint : AlgebraicGeometry.IsIntegral (Work.CY3Stab.WProd (𝕜 := 𝕜) X k) :=
    Work.CY3Stab.Prod.isIntegral_wProd (𝕜 := 𝕜) k
  haveI hWXirr : IrreducibleSpace (Work.CY3Stab.WProd (𝕜 := 𝕜) X k) := inferInstance
  let p : Work.CY3Stab.WProd (𝕜 := 𝕜) X k ⟶ X := CategoryTheory.Limits.pullback.snd
    (Work.CY3Stab.Prod.overHom (𝕜 := 𝕜) (Work.CY3Stab.AffineK (𝕜 := 𝕜) k))
    (Work.CY3Stab.Prod.overHom (𝕜 := 𝕜) X)
  let q : Work.CY3Stab.WProd (𝕜 := 𝕜) Y k ⟶ Y := CategoryTheory.Limits.pullback.snd
    (Work.CY3Stab.Prod.overHom (𝕜 := 𝕜) (Work.CY3Stab.AffineK (𝕜 := 𝕜) k))
    (Work.CY3Stab.Prod.overHom (𝕜 := 𝕜) Y)
  let G₀ : (Work.CY3Stab.WProd (𝕜 := 𝕜) X k).PartialMap Y :=
    (Work.K3.PartialMap.baseChangeAlong (Work.CY3Stab.Prod.overHom (𝕜 := 𝕜)
      (Work.CY3Stab.AffineK (𝕜 := 𝕜) k)) g₀).compHom q
  haveI hSurj : Surjective (Work.CY3Stab.Prod.overHom (𝕜 := 𝕜)
    (Work.CY3Stab.AffineK (𝕜 := 𝕜) k)) := inferInstance
  haveI hUO : UniversallyOpen (Work.CY3Stab.Prod.overHom (𝕜 := 𝕜)
    (Work.CY3Stab.AffineK (𝕜 := 𝕜) k)) := inferInstance
  have hGG₀ : G.toRationalMap = G₀.toRationalMap := heq
  have hFF : G.fromFunctionField = G₀.fromFunctionField :=
    PartialMap.fromFunctionField_eq_of_toRationalMap_eq hGG₀
  haveI hWXirr' : IrreducibleSpace (Work.K3.baseChangeAlong
      (Work.CY3Stab.Prod.overHom (𝕜 := 𝕜) (Work.CY3Stab.AffineK (𝕜 := 𝕜) k)) X) := hWXirr
  have hC : G₀.fromFunctionField =
      Spec.map (cylFFMap (𝕜 := 𝕜) X k) ≫ g₀.fromFunctionField :=
    fromFunctionField_baseChangeAlong_compHom (𝕜 := 𝕜) k g₀
  let α : Spec ((Work.CY3Stab.WProd (𝕜 := 𝕜) X k).presheaf.stalk y) ⟶ Y :=
    G.fromSpecStalkOfMem hyG
  have hGenG : genericPoint (Work.CY3Stab.WProd (𝕜 := 𝕜) X k) ∈ G.domain :=
    (genericPoint_specializes _).mem_open G.domain.2 G.dense_domain.nonempty.choose_spec
  have hαFF : Spec.map (ffAlgMap (Work.CY3Stab.WProd (𝕜 := 𝕜) X k) y) ≫ α = G.fromFunctionField :=
    PartialMap.ffAlgMap_fromSpecStalkOfMem_eq_fromFunctionField G y hyG hGenG
  let qv : Y := α (IsLocalRing.closedPoint ((Work.CY3Stab.WProd (𝕜 := 𝕜) X k).presheaf.stalk y))
  obtain ⟨U, hUaff, hqvU, -⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (U := ⊤) (x := qv) (by trivial)
  have hclU : IsLocalRing.closedPoint ((Work.CY3Stab.WProd (𝕜 := 𝕜) X k).presheaf.stalk y)
      ∈ α ⁻¹ᵁ U := by
    change qv ∈ U
    exact hqvU
  have hpre : α ⁻¹ᵁ U = ⊤ := (IsLocalRing.closedPoint_mem_iff (α ⁻¹ᵁ U)).mp hclU
  have hr : Set.range ⇑α ⊆ Set.range ⇑U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro - ⟨z, rfl⟩
    exact (show z ∈ α ⁻¹ᵁ U from by rw [hpre]; trivial)
  let αU : Spec ((Work.CY3Stab.WProd (𝕜 := 𝕜) X k).presheaf.stalk y) ⟶ U.toScheme :=
    IsOpenImmersion.lift U.ι α hr
  have hαU : αU ≫ U.ι = α := IsOpenImmersion.lift_fac U.ι α hr
  let Φ : Spec ((Work.CY3Stab.WProd (𝕜 := 𝕜) X k).presheaf.stalk y) ⟶ Spec Γ(Y, U) :=
    αU ≫ hUaff.isoSpec.hom
  let φ : Γ(Y, U) ⟶ (Work.CY3Stab.WProd (𝕜 := 𝕜) X k).presheaf.stalk y := Spec.preimage Φ
  have hφ : Spec.map φ = αU ≫ hUaff.isoSpec.hom := Spec.map_preimage Φ
  have hαfac : α = Spec.map φ ≫ hUaff.isoSpec.inv ≫ U.ι := by
    rw [hφ, Category.assoc, Iso.hom_inv_id_assoc, hαU]
  have hqq : Spec.map (cylFFMap (𝕜 := 𝕜) X k) ≫ g₀.fromFunctionField =
      Spec.map (ffAlgMap (Work.CY3Stab.WProd (𝕜 := 𝕜) X k) y) ≫ α := by
    rw [← hC, ← hFF, ← hαFF]
  have hr₂ : Set.range ⇑(Spec.map (cylFFMap (𝕜 := 𝕜) X k) ≫ g₀.fromFunctionField)
      ⊆ Set.range ⇑U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro - ⟨w, rfl⟩
    rw [hqq, ← hαU]
    exact ((Spec.map (ffAlgMap (Work.CY3Stab.WProd (𝕜 := 𝕜) X k) y) ≫ αU) w).2
  have hr₃ : Set.range ⇑(g₀.fromFunctionField) ⊆ Set.range ⇑U.ι := by
    rw [Scheme.Opens.range_ι]
    intro z hz
    obtain ⟨w, rfl⟩ := hz
    obtain ⟨w', hw'⟩ := Spec.map_surjective_of_field (cylFFMap (𝕜 := 𝕜) X k).hom w
    have hmem : (Spec.map (cylFFMap (𝕜 := 𝕜) X k) ≫ g₀.fromFunctionField) w' ∈ (U : Set Y) := by
      have h := hr₂ ⟨w', rfl⟩
      rwa [Scheme.Opens.range_ι] at h
    have heq' : (Spec.map (cylFFMap (𝕜 := 𝕜) X k) ≫ g₀.fromFunctionField) w'
        = g₀.fromFunctionField w := by
      show g₀.fromFunctionField (Spec.map (cylFFMap (𝕜 := 𝕜) X k) w') = g₀.fromFunctionField w
      rw [show cylFFMap (𝕜 := 𝕜) X k = CommRingCat.ofHom (cylFFMap (𝕜 := 𝕜) X k).hom from rfl, hw']
    rwa [heq'] at hmem
  let ΦU : Spec X.functionField ⟶ U.toScheme :=
    IsOpenImmersion.lift U.ι g₀.fromFunctionField hr₃
  have hΦU : ΦU ≫ U.ι = g₀.fromFunctionField := IsOpenImmersion.lift_fac U.ι g₀.fromFunctionField hr₃
  let Ψ : Spec X.functionField ⟶ Spec Γ(Y, U) := ΦU ≫ hUaff.isoSpec.hom
  let ρ : Γ(Y, U) ⟶ X.functionField := Spec.preimage Ψ
  have hρ : Spec.map ρ = ΦU ≫ hUaff.isoSpec.hom := Spec.map_preimage Ψ
  have hρfac : Spec.map ρ ≫ hUaff.isoSpec.inv ≫ U.ι = g₀.fromFunctionField := by
    rw [hρ, Category.assoc, Iso.hom_inv_id_assoc, hΦU]
  have hfs : Spec.map (ffAlgMap (Work.CY3Stab.WProd (𝕜 := 𝕜) X k) y) ≫ αU ≫ U.ι
      = G.fromFunctionField := by
    rw [hαU, hαFF]
  have hgs : Spec.map (cylFFMap (𝕜 := 𝕜) X k) ≫ ΦU ≫ U.ι = G.fromFunctionField := by
    rw [hΦU, ← hC, ← hFF]
  have hfsgs : Spec.map (ffAlgMap (Work.CY3Stab.WProd (𝕜 := 𝕜) X k) y) ≫ αU
      = Spec.map (cylFFMap (𝕜 := 𝕜) X k) ≫ ΦU := by
    refine (cancel_mono U.ι).mp ?_
    rw [Category.assoc, Category.assoc, hαU, hαFF, hΦU, ← hC, ← hFF]
  have hsquares : φ ≫ ffAlgMap (Work.CY3Stab.WProd (𝕜 := 𝕜) X k) y
      = ρ ≫ cylFFMap (𝕜 := 𝕜) X k := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, hφ, hρ]
    rw [← Category.assoc, ← Category.assoc, hfsgs]
  have hsq : (p.stalkMap y) ≫ ffAlgMap (Work.CY3Stab.WProd (𝕜 := 𝕜) X k) y
      = ffAlgMap X (p y) ≫ cylFFMap (𝕜 := 𝕜) X k :=
    cylFFMap_sq (𝕜 := 𝕜) (X := X) (k := k) y
  have hsquare_pt : ∀ r : Γ(Y, U),
      (ffAlgMap (Work.CY3Stab.WProd (𝕜 := 𝕜) X k) y).hom (φ r)
        = (cylFFMap (𝕜 := 𝕜) X k).hom (ρ r) := by
    intro r
    have h1 := congrArg CommRingCat.Hom.hom hsquares
    have h2 := congrArg (fun (f : ↥Γ(Y, U) →+* ↥(Work.CY3Stab.WProd (𝕜 := 𝕜) X k).functionField) =>
      f r) h1
    rw [CommRingCat.hom_comp, CommRingCat.hom_comp, RingHom.comp_apply, RingHom.comp_apply] at h2
    simpa only [ffAlgMap, CommRingCat.hom_ofHom] using h2
  haveI hFlatp : Flat (CategoryTheory.Limits.pullback.snd
      (Work.CY3Stab.Prod.overHom (𝕜 := 𝕜) (Work.CY3Stab.AffineK (𝕜 := 𝕜) k))
      (Work.CY3Stab.Prod.overHom (𝕜 := 𝕜) X)) := inferInstance
  letI hAlgBA : Algebra (X.presheaf.stalk (p y))
      ((Work.CY3Stab.WProd (𝕜 := 𝕜) X k).presheaf.stalk y) :=
    ((p.stalkMap y).hom).toAlgebra
  haveI hFlatBA : Module.Flat (X.presheaf.stalk (p y))
      ((Work.CY3Stab.WProd (𝕜 := 𝕜) X k).presheaf.stalk y) :=
    Flat.stalkMap (CategoryTheory.Limits.pullback.snd
      (Work.CY3Stab.Prod.overHom (𝕜 := 𝕜) (Work.CY3Stab.AffineK (𝕜 := 𝕜) k))
      (Work.CY3Stab.Prod.overHom (𝕜 := 𝕜) X)) y
  haveI hFFBA : Module.FaithfullyFlat (X.presheaf.stalk (p y))
      ((Work.CY3Stab.WProd (𝕜 := 𝕜) X k).presheaf.stalk y) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _ hFlatBA
      ((RingHom.algebraMap_toAlgebra ((p.stalkMap y).hom)).symm ▸
        (inferInstance : IsLocalHom ((p.stalkMap y).hom)))
  have hst_raw : ∀ b : X.presheaf.stalk (p y),
      (cylFFMap (𝕜 := 𝕜) X k).hom ((ffAlgMap X (p y)).hom b)
        = (ffAlgMap (Work.CY3Stab.WProd (𝕜 := 𝕜) X k) y).hom ((p.stalkMap y).hom b) := by
    intro b
    have h1 := congrArg CommRingCat.Hom.hom hsq
    have h2 := congrArg (fun (f : ↥(X.presheaf.stalk (p y)) →+*
      ↥(Work.CY3Stab.WProd (𝕜 := 𝕜) X k).functionField) => f b) h1
    rw [CommRingCat.hom_comp, CommRingCat.hom_comp, RingHom.comp_apply, RingHom.comp_apply] at h2
    exact h2.symm
  have hst : ∀ b : X.presheaf.stalk (p y),
      (cylFFMap (𝕜 := 𝕜) X k).hom (algebraMap (X.presheaf.stalk (p y)) X.functionField b)
        = (ffAlgMap (Work.CY3Stab.WProd (𝕜 := 𝕜) X k) y).hom ((p.stalkMap y).hom b) :=
    fun b => hst_raw b
  have hkey : ∀ r : Γ(Y, U), ∃ b : X.presheaf.stalk (p y),
      algebraMap (X.presheaf.stalk (p y)) X.functionField b = ρ r := by
    intro r
    refine exists_algebraMap_eq_of_algebraMap_comp_eq
      (B := X.presheaf.stalk (p y))
      (A := (Work.CY3Stab.WProd (𝕜 := 𝕜) X k).presheaf.stalk y)
      (KB := X.functionField) (KA := (Work.CY3Stab.WProd (𝕜 := 𝕜) X k).functionField)
      (st := (cylFFMap (𝕜 := 𝕜) X k).hom) hst (ρ r) ⟨φ r, ?_⟩
    exact hsquare_pt r
  let ψfun : Γ(Y, U) → X.presheaf.stalk (p y) := fun r => (hkey r).choose
  have hψspec : ∀ r : Γ(Y, U),
      algebraMap (X.presheaf.stalk (p y)) X.functionField (ψfun r) = (CommRingCat.Hom.hom ρ) r :=
    fun r => (hkey r).choose_spec
  let ψ : Γ(Y, U) →+* X.presheaf.stalk (p y) :=
    { toFun := ψfun
      map_one' := by
        apply IsFractionRing.injective (X.presheaf.stalk (p y)) X.functionField
        show algebraMap (X.presheaf.stalk (p y)) X.functionField (ψfun 1)
          = algebraMap (X.presheaf.stalk (p y)) X.functionField 1
        simp only [hψspec 1, map_one]
      map_mul' := by
        intro a b
        apply IsFractionRing.injective (X.presheaf.stalk (p y)) X.functionField
        show algebraMap (X.presheaf.stalk (p y)) X.functionField (ψfun (a * b))
          = algebraMap (X.presheaf.stalk (p y)) X.functionField (ψfun a * ψfun b)
        simp only [hψspec (a * b), hψspec a, hψspec b, map_mul]
      map_zero' := by
        apply IsFractionRing.injective (X.presheaf.stalk (p y)) X.functionField
        show algebraMap (X.presheaf.stalk (p y)) X.functionField (ψfun 0)
          = algebraMap (X.presheaf.stalk (p y)) X.functionField 0
        simp only [hψspec 0, map_zero]
      map_add' := by
        intro a b
        apply IsFractionRing.injective (X.presheaf.stalk (p y)) X.functionField
        show algebraMap (X.presheaf.stalk (p y)) X.functionField (ψfun (a + b))
          = algebraMap (X.presheaf.stalk (p y)) X.functionField (ψfun a + ψfun b)
        simp only [hψspec (a + b), hψspec a, hψspec b, map_add] }
  let ψc : Γ(Y, U) ⟶ X.presheaf.stalk (p y) := CommRingCat.ofHom ψ
  have hψc : (CommRingCat.Hom.hom ψc) = ψ := rfl
  have hψ : ∀ r : Γ(Y, U),
      algebraMap (X.presheaf.stalk (p y)) X.functionField (ψ r) = ρ r :=
    fun r => hψspec r
  have hφψ : ∀ r : Γ(Y, U), φ r = (p.stalkMap y).hom (ψ r) := by
    intro r
    apply IsFractionRing.injective
      ((Work.CY3Stab.WProd (𝕜 := 𝕜) X k).presheaf.stalk y)
      ((Work.CY3Stab.WProd (𝕜 := 𝕜) X k).functionField)
    have hopen : algebraMap ((Work.CY3Stab.WProd (𝕜 := 𝕜) X k).presheaf.stalk y)
          ((Work.CY3Stab.WProd (𝕜 := 𝕜) X k).functionField) (φ r)
        = (cylFFMap (𝕜 := 𝕜) X k).hom (algebraMap (X.presheaf.stalk (p y)) X.functionField (ψ r)) := by
      rw [hψ r]
      exact hsquare_pt r
    have hclosed : (cylFFMap (𝕜 := 𝕜) X k).hom
          (algebraMap (X.presheaf.stalk (p y)) X.functionField (ψ r))
        = algebraMap ((Work.CY3Stab.WProd (𝕜 := 𝕜) X k).presheaf.stalk y)
            ((Work.CY3Stab.WProd (𝕜 := 𝕜) X k).functionField) ((p.stalkMap y).hom (ψ r)) :=
      hst (ψ r)
    exact hopen.trans hclosed
  have hloc : ∀ r : Γ(Y, U),
      ψ r ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (p y)) ↔
        φ r ∈ IsLocalRing.maximalIdeal ((Work.CY3Stab.WProd (𝕜 := 𝕜) X k).presheaf.stalk y) := by
    intro r
    have h : (p.stalkMap y).hom (ψ r) ∈
        IsLocalRing.maximalIdeal ((Work.CY3Stab.WProd (𝕜 := 𝕜) X k).presheaf.stalk y) ↔
        ψ r ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (p y)) := by
      rw [← IsLocalRing.maximalIdeal_comap ((p.stalkMap y).hom), Ideal.mem_comap]
    rw [hφψ r]
    exact h.symm
  have hclosedpt : Spec.map ψc (IsLocalRing.closedPoint (X.presheaf.stalk (p y))) =
      Spec.map φ (IsLocalRing.closedPoint ((Work.CY3Stab.WProd (𝕜 := 𝕜) X k).presheaf.stalk y)) := by
    have h1 := Spec.map_apply ψc (IsLocalRing.closedPoint (X.presheaf.stalk (p y)))
    have h2 := Spec.map_apply φ
      (IsLocalRing.closedPoint ((Work.CY3Stab.WProd (𝕜 := 𝕜) X k).presheaf.stalk y))
    rw [h1, h2]
    apply PrimeSpectrum.ext
    show (IsLocalRing.maximalIdeal (X.presheaf.stalk (p y))).comap
        (CommRingCat.Hom.hom ψc)
      = (IsLocalRing.maximalIdeal ((Work.CY3Stab.WProd (𝕜 := 𝕜) X k).presheaf.stalk y)).comap
          (CommRingCat.Hom.hom φ)
    apply Ideal.ext
    intro r
    rw [Ideal.mem_comap, Ideal.mem_comap]
    exact hloc r
  let β' := Spec.map ψc ≫ hUaff.isoSpec.inv
  let β : Spec (X.presheaf.stalk (p y)) ⟶ Y := β' ≫ U.ι
  have hρeq : ρ = ψc ≫ ffAlgMap X (p y) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    show (CommRingCat.Hom.hom ρ) r
      = (algebraMap (X.presheaf.stalk (p y)) X.functionField) (ψfun r)
    exact (hψspec r).symm
  have h1spec : Spec.map (ffAlgMap X (p y)) ≫ Spec.map ψc = Spec.map ρ :=
    (Spec.map_comp ψc (ffAlgMap X (p y))).symm.trans (congrArg Spec.map hρeq.symm)
  have hβ1 : Spec.map (ffAlgMap X (p y)) ≫ β = g₀.fromFunctionField := by
    have h2 : Spec.map (ffAlgMap X (p y)) ≫ β' = Spec.map ρ ≫ hUaff.isoSpec.inv := by
      rw [show β' = Spec.map ψc ≫ hUaff.isoSpec.inv from rfl, ← Category.assoc, h1spec]
    rw [show β = β' ≫ U.ι from rfl, ← Category.assoc, h2, Category.assoc, hρfac]
  have hβclosed : β (IsLocalRing.closedPoint (X.presheaf.stalk (p y)))
      = α (IsLocalRing.closedPoint ((Work.CY3Stab.WProd (𝕜 := 𝕜) X k).presheaf.stalk y)) := by
    rw [show β = β' ≫ U.ι from rfl,
      show β' = Spec.map ψc ≫ hUaff.isoSpec.inv from rfl, hαfac]
    show (hUaff.isoSpec.inv ≫ U.ι) ((Spec.map ψc) (IsLocalRing.closedPoint (X.presheaf.stalk (p y))))
      = (hUaff.isoSpec.inv ≫ U.ι)
          ((Spec.map φ) (IsLocalRing.closedPoint ((Work.CY3Stab.WProd (𝕜 := 𝕜) X k).presheaf.stalk y)))
    rw [hclosedpt]
  have hβ_over : β ≫ (Work.CY3Stab.Prod.overHom (𝕜 := 𝕜) Y)
      = X.fromSpecStalk (p y) ≫ (Work.CY3Stab.Prod.overHom (𝕜 := 𝕜) X) := by
    refine eq_of_specMap_algebraMap_eq_of_apply_closedPoint_eq
      (A := X.presheaf.stalk (p y)) (K := X.functionField)
      (IsFractionRing.injective _ _) (β ≫ (Work.CY3Stab.Prod.overHom (𝕜 := 𝕜) Y))
      (X.fromSpecStalk (p y) ≫ (Work.CY3Stab.Prod.overHom (𝕜 := 𝕜) X)) ?_ ?_
    · have hL : Spec.map (ffAlgMap X (p y)) ≫ (β ≫ (Work.CY3Stab.Prod.overHom (𝕜 := 𝕜) Y))
          = X.fromSpecStalk (genericPoint X) ≫ (Work.CY3Stab.Prod.overHom (𝕜 := 𝕜) X) := by
        rw [← Category.assoc, hβ1]
        exact PartialMap.fromFunctionField_comp (S := Spec (CommRingCat.of 𝕜)) g₀
      have hR : Spec.map (ffAlgMap X (p y))
          ≫ (X.fromSpecStalk (p y) ≫ (Work.CY3Stab.Prod.overHom (𝕜 := 𝕜) X))
          = X.fromSpecStalk (genericPoint X) ≫ (Work.CY3Stab.Prod.overHom (𝕜 := 𝕜) X) := by
        have h'' : Spec.map (ffAlgMap X (p y))
            ≫ X.fromSpecStalk (p y) = X.fromSpecStalk (genericPoint X) := by
          rw [congrArg Spec.map (ffAlgMap_eq_stalkSpecializes X (p y))]
          exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes (p y))
        rw [← Category.assoc, h'']
      exact hL.trans hR.symm
    · exact Subsingleton.elim _ _
  have h2pt : Spec.map (ffAlgMap (Work.CY3Stab.WProd (𝕜 := 𝕜) X k) y)
      ≫ Spec.map (p.stalkMap y) ≫ β = G.fromFunctionField := by
    have h4 : Spec.map (ffAlgMap (Work.CY3Stab.WProd (𝕜 := 𝕜) X k) y) ≫ Spec.map (p.stalkMap y)
        = Spec.map ((p.stalkMap y) ≫ ffAlgMap (Work.CY3Stab.WProd (𝕜 := 𝕜) X k) y) :=
      (Spec.map_comp (p.stalkMap y) (ffAlgMap (Work.CY3Stab.WProd (𝕜 := 𝕜) X k) y)).symm
    have h5 : Spec.map ((p.stalkMap y) ≫ ffAlgMap (Work.CY3Stab.WProd (𝕜 := 𝕜) X k) y)
        = Spec.map (ffAlgMap X (p y) ≫ cylFFMap (𝕜 := 𝕜) X k) := congrArg Spec.map hsq
    have h6 : Spec.map (ffAlgMap X (p y) ≫ cylFFMap (𝕜 := 𝕜) X k)
        = Spec.map (cylFFMap (𝕜 := 𝕜) X k) ≫ Spec.map (ffAlgMap X (p y)) :=
      Spec.map_comp (ffAlgMap X (p y)) (cylFFMap (𝕜 := 𝕜) X k)
    calc Spec.map (ffAlgMap (Work.CY3Stab.WProd (𝕜 := 𝕜) X k) y) ≫ Spec.map (p.stalkMap y) ≫ β
        = (Spec.map (ffAlgMap (Work.CY3Stab.WProd (𝕜 := 𝕜) X k) y)
            ≫ Spec.map (p.stalkMap y)) ≫ β := by rw [Category.assoc]
      _ = Spec.map ((p.stalkMap y) ≫ ffAlgMap (Work.CY3Stab.WProd (𝕜 := 𝕜) X k) y) ≫ β := by
            rw [h4]
      _ = Spec.map (ffAlgMap X (p y) ≫ cylFFMap (𝕜 := 𝕜) X k) ≫ β := by rw [h5]
      _ = (Spec.map (cylFFMap (𝕜 := 𝕜) X k) ≫ Spec.map (ffAlgMap X (p y))) ≫ β := by rw [h6]
      _ = Spec.map (cylFFMap (𝕜 := 𝕜) X k) ≫ (Spec.map (ffAlgMap X (p y)) ≫ β) := by
            rw [Category.assoc]
      _ = Spec.map (cylFFMap (𝕜 := 𝕜) X k) ≫ g₀.fromFunctionField := by rw [hβ1]
      _ = G₀.fromFunctionField := hC.symm
      _ = G.fromFunctionField := hFF.symm
  have hαβ : α = Spec.map (p.stalkMap y) ≫ β := by
    refine eq_of_specMap_algebraMap_eq_of_apply_closedPoint_eq
      (A := (Work.CY3Stab.WProd (𝕜 := 𝕜) X k).presheaf.stalk y)
      (K := (Work.CY3Stab.WProd (𝕜 := 𝕜) X k).functionField)
      (IsFractionRing.injective _ _) α (Spec.map (p.stalkMap y) ≫ β) ?_ ?_
    · exact hαFF.trans h2pt.symm
    · have hpt : Spec.map (p.stalkMap y)
          (IsLocalRing.closedPoint ((Work.CY3Stab.WProd (𝕜 := 𝕜) X k).presheaf.stalk y))
          = IsLocalRing.closedPoint (X.presheaf.stalk (p y)) := by
        have h1 := Spec.map_apply (p.stalkMap y)
          (IsLocalRing.closedPoint ((Work.CY3Stab.WProd (𝕜 := 𝕜) X k).presheaf.stalk y))
        rw [h1]
        apply PrimeSpectrum.ext
        show (IsLocalRing.maximalIdeal ((Work.CY3Stab.WProd (𝕜 := 𝕜) X k).presheaf.stalk y)).comap
            (p.stalkMap y).hom = IsLocalRing.maximalIdeal (X.presheaf.stalk (p y))
        rw [IsLocalRing.maximalIdeal_comap]
      rw [show (Spec.map (p.stalkMap y) ≫ β)
          (IsLocalRing.closedPoint ((Work.CY3Stab.WProd (𝕜 := 𝕜) X k).presheaf.stalk y))
          = β (Spec.map (p.stalkMap y)
              (IsLocalRing.closedPoint ((Work.CY3Stab.WProd (𝕜 := 𝕜) X k).presheaf.stalk y))) from rfl,
        hpt]
      exact hβclosed.symm
  let g : X.PartialMap Y := PartialMap.ofFromSpecStalk (Work.CY3Stab.Prod.overHom (𝕜 := 𝕜) X)
    (Work.CY3Stab.Prod.overHom (𝕜 := 𝕜) Y) β hβ_over
  have hxg : p y ∈ g.domain := PartialMap.mem_domain_ofFromSpecStalk _ _ β hβ_over
  have hβg : g.fromSpecStalkOfMem hxg = β :=
    PartialMap.fromSpecStalkOfMem_ofFromSpecStalk _ _ β hβ_over
  have hOver : g.IsOver (Spec (CommRingCat.of 𝕜)) := by
    refine (PartialMap.isOver_iff (S := Spec (CommRingCat.of 𝕜)) (f := g)).mpr ?_
    exact PartialMap.ofFromSpecStalk_comp _ _ β hβ_over
  have hFFg : g.fromFunctionField = g₀.fromFunctionField := by
    have hGeng : genericPoint X ∈ g.domain :=
      (genericPoint_specializes _).mem_open g.domain.2 g.dense_domain.nonempty.choose_spec
    rw [← PartialMap.ffAlgMap_fromSpecStalkOfMem_eq_fromFunctionField g (p y) hxg hGeng]
    rw [hβg]
    exact hβ1
  have hrat : g.toRationalMap = g₀.toRationalMap := by
    refine RationalMap.eq_of_fromFunctionField_eq g.toRationalMap g₀.toRationalMap ?_
    simpa using hFFg
  refine ⟨g, hxg, hOver, hrat, ?_⟩
  rw [hβg]
  exact hαβ

end

end Work.CY3Stab.Prod
