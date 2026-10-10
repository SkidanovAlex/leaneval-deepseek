import Mathlib
import Submission.Work.K3.BaseChangeBirational

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.K3

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

/-- **Base change of a partial isomorphism** along `f : T ⟶ S`: the partial isomorphism of the base
changes whose source and target are the preimages of the source and target of `g`, and whose
rational map is the base change of the rational map of `g`.  Built from
`Scheme.pullbackRestrictIsoRestrict` and `Scheme.isPullback_morphismRestrict`
(`Mathlib/AlgebraicGeometry/Restrict.lean`) applied to `g.iso`. -/
theorem partialIso_baseChangeAlong {S T X Y : Scheme.{0}} (f : T ⟶ S) [X.Over S] [Y.Over S]
    [Surjective f] [UniversallyOpen f] (g : X.PartialIso Y) (hg : g.toPartialMap.IsOver S) :
    ∃ h : (Work.K3.baseChangeAlong f X).PartialIso (Work.K3.baseChangeAlong f Y),
      h.source = (Work.K3.baseChangeAlongProj f X) ⁻¹ᵁ g.source ∧
      h.target = (Work.K3.baseChangeAlongProj f Y) ⁻¹ᵁ g.target ∧
      h.toRationalMap = (Work.K3.PartialMap.baseChangeAlong f g.toPartialMap).toRationalMap := by
  classical
  -- ### the `IsOver S` equation for `g`
  have hg' : g.iso.hom ≫ g.target.ι ≫ (Y ↘ S) = g.source.ι ≫ (X ↘ S) := by
    have h : g.toPartialMap.hom ≫ (Y ↘ S) = g.source.ι ≫ (X ↘ S) :=
      ((Hom.isOver_iff (S := S)).mp hg).trans (Opens.ι_comp_over g.source S).symm
    exact h
  -- ### the morphism underlying the base-changed partial map
  let bT : ((baseChangeAlongProj f X) ⁻¹ᵁ g.source).toScheme ⟶ T :=
    ((baseChangeAlongProj f X) ⁻¹ᵁ g.source).ι ≫ pullback.fst f (X ↘ S)
  let bY : ((baseChangeAlongProj f X) ⁻¹ᵁ g.source).toScheme ⟶ Y :=
    (baseChangeAlongProj f X ∣_ g.source) ≫ g.iso.hom ≫ g.target.ι
  let a : ((baseChangeAlongProj f X) ⁻¹ᵁ g.source).toScheme ⟶ baseChangeAlong f Y :=
    (PartialMap.baseChangeAlong f g.toPartialMap).hom
  have ha_fst : a ≫ pullback.fst f (Y ↘ S) = bT :=
    PartialMap.baseChangeAlong_hom_fst f g.toPartialMap
  have ha_snd : a ≫ pullback.snd f (Y ↘ S) = bY :=
    PartialMap.baseChangeAlong_hom_snd f g.toPartialMap
  let b : ((baseChangeAlongProj f X) ⁻¹ᵁ g.source).toScheme ⟶ g.target.toScheme :=
    (baseChangeAlongProj f X ∣_ g.source) ≫ g.iso.hom
  have hL : a ≫ baseChangeAlongProj f Y = b ≫ g.target.ι := by
    rw [ha_snd]
    simp only [bY, b, Category.assoc]
  let L : ((baseChangeAlongProj f X) ⁻¹ᵁ g.source).toScheme ⟶
      pullback (baseChangeAlongProj f Y) g.target.ι := pullback.lift a b hL
  have hLf : L ≫ pullback.fst (baseChangeAlongProj f Y) g.target.ι = a :=
    pullback.lift_fst a b hL
  have hLs : L ≫ pullback.snd (baseChangeAlongProj f Y) g.target.ι = b :=
    pullback.lift_snd a b hL
  let φ : ((baseChangeAlongProj f X) ⁻¹ᵁ g.source).toScheme ⟶
      ((baseChangeAlongProj f Y) ⁻¹ᵁ g.target).toScheme :=
    L ≫ (pullbackRestrictIsoRestrict (baseChangeAlongProj f Y) g.target).hom
  have hφι : φ ≫ ((baseChangeAlongProj f Y) ⁻¹ᵁ g.target).ι = a := by
    dsimp only [φ]
    rw [Category.assoc, pullbackRestrictIsoRestrict_hom_ι, hLf]
  -- ### the candidate inverse
  let c : pullback (baseChangeAlongProj f Y) g.target.ι ⟶ T :=
    pullback.fst (baseChangeAlongProj f Y) g.target.ι ≫ pullback.fst f (Y ↘ S)
  let d : pullback (baseChangeAlongProj f Y) g.target.ι ⟶ X :=
    pullback.snd (baseChangeAlongProj f Y) g.target.ι ≫ g.iso.inv ≫ g.source.ι
  have hc : c ≫ f = d ≫ (X ↘ S) := by
    show (pullback.fst (baseChangeAlongProj f Y) g.target.ι ≫ pullback.fst f (Y ↘ S)) ≫ f =
      (pullback.snd (baseChangeAlongProj f Y) g.target.ι ≫ g.iso.inv ≫ g.source.ι) ≫ (X ↘ S)
    calc (pullback.fst (baseChangeAlongProj f Y) g.target.ι ≫ pullback.fst f (Y ↘ S)) ≫ f
        = pullback.fst (baseChangeAlongProj f Y) g.target.ι ≫ pullback.fst f (Y ↘ S) ≫ f := by
            rw [Category.assoc]
      _ = pullback.fst (baseChangeAlongProj f Y) g.target.ι ≫
            pullback.snd f (Y ↘ S) ≫ (Y ↘ S) := by
            rw [pullback.condition]
      _ = (pullback.fst (baseChangeAlongProj f Y) g.target.ι ≫ pullback.snd f (Y ↘ S)) ≫
            (Y ↘ S) := by
            rw [Category.assoc]
      _ = (pullback.snd (baseChangeAlongProj f Y) g.target.ι ≫ g.target.ι) ≫ (Y ↘ S) := by
            rw [pullback.condition]
      _ = pullback.snd (baseChangeAlongProj f Y) g.target.ι ≫ g.target.ι ≫ (Y ↘ S) := by
            rw [Category.assoc]
      _ = pullback.snd (baseChangeAlongProj f Y) g.target.ι ≫
            g.iso.inv ≫ g.source.ι ≫ (X ↘ S) := by
            rw [show g.target.ι ≫ (Y ↘ S) = g.iso.inv ≫ g.source.ι ≫ (X ↘ S) from by
              rw [← hg', ← Category.assoc, Iso.inv_hom_id, Category.id_comp]]
      _ = (pullback.snd (baseChangeAlongProj f Y) g.target.ι ≫ g.iso.inv ≫ g.source.ι) ≫
            (X ↘ S) := by
            simp only [Category.assoc]
  let a' : pullback (baseChangeAlongProj f Y) g.target.ι ⟶ baseChangeAlong f X :=
    pullback.lift c d hc
  let b' : pullback (baseChangeAlongProj f Y) g.target.ι ⟶ g.source.toScheme :=
    pullback.snd (baseChangeAlongProj f Y) g.target.ι ≫ g.iso.inv
  have ha'f : a' ≫ pullback.fst f (X ↘ S) = c := pullback.lift_fst c d hc
  have ha's : a' ≫ pullback.snd f (X ↘ S) = d := pullback.lift_snd c d hc
  have h' : a' ≫ baseChangeAlongProj f X = b' ≫ g.source.ι := by
    rw [show a' ≫ baseChangeAlongProj f X = d from ha's]
    simp only [d, b', Category.assoc]
  let L' : pullback (baseChangeAlongProj f Y) g.target.ι ⟶
      pullback (baseChangeAlongProj f X) g.source.ι := pullback.lift a' b' h'
  have hL'f : L' ≫ pullback.fst (baseChangeAlongProj f X) g.source.ι = a' :=
    pullback.lift_fst a' b' h'
  have hL's : L' ≫ pullback.snd (baseChangeAlongProj f X) g.source.ι = b' :=
    pullback.lift_snd a' b' h'
  let ψ : ((baseChangeAlongProj f Y) ⁻¹ᵁ g.target).toScheme ⟶
      ((baseChangeAlongProj f X) ⁻¹ᵁ g.source).toScheme :=
    (pullbackRestrictIsoRestrict (baseChangeAlongProj f Y) g.target).inv ≫ L' ≫
      (pullbackRestrictIsoRestrict (baseChangeAlongProj f X) g.source).hom
  have hψι : ψ ≫ ((baseChangeAlongProj f X) ⁻¹ᵁ g.source).ι =
      (pullbackRestrictIsoRestrict (baseChangeAlongProj f Y) g.target).inv ≫ a' := by
    dsimp only [ψ]
    rw [Category.assoc, Category.assoc, pullbackRestrictIsoRestrict_hom_ι, hL'f]
  -- ### `L` and `a'` are inverse "base change" maps
  have key1 : L ≫ a' = ((baseChangeAlongProj f X) ⁻¹ᵁ g.source).ι := by
    apply pullback.hom_ext (f := f) (g := X ↘ S)
    · have h1 : L ≫ c = bT := by
        dsimp only [c]
        rw [← Category.assoc, hLf, ha_fst]
      rw [Category.assoc, ha'f, h1]
    · have h1 : L ≫ d =
          ((baseChangeAlongProj f X) ⁻¹ᵁ g.source).ι ≫ baseChangeAlongProj f X := by
        dsimp only [d]
        rw [← Category.assoc, hLs]
        dsimp only [b]
        rw [Category.assoc, Iso.hom_inv_id_assoc, morphismRestrict_ι]
      rw [Category.assoc, ha's, h1]
  have key2 : ψ ≫ a = ((baseChangeAlongProj f Y) ⁻¹ᵁ g.target).ι := by
    apply pullback.hom_ext (f := f) (g := Y ↘ S)
    · have h1 : ψ ≫ bT =
          ((baseChangeAlongProj f Y) ⁻¹ᵁ g.target).ι ≫ pullback.fst f (Y ↘ S) := by
        dsimp only [bT]
        rw [← Category.assoc, hψι, Category.assoc, ha'f]
        dsimp only [c]
        rw [← Category.assoc, pullbackRestrictIsoRestrict_inv_fst]
      rw [Category.assoc, ha_fst, h1]
    · have hψpX : ψ ≫ (baseChangeAlongProj f X ∣_ g.source) =
          (pullbackRestrictIsoRestrict (baseChangeAlongProj f Y) g.target).inv ≫ b' := by
        dsimp only [ψ]
        rw [Category.assoc, Category.assoc, pullbackRestrictIsoRestrict_hom_morphismRestrict,
          hL's]
      have h1 : ψ ≫ bY =
          ((baseChangeAlongProj f Y) ⁻¹ᵁ g.target).ι ≫ baseChangeAlongProj f Y := by
        dsimp only [bY]
        rw [← Category.assoc, hψpX]
        dsimp only [b']
        rw [Category.assoc, Category.assoc, Iso.inv_hom_id_assoc]
        rw [← Category.assoc]
        rw [show (pullbackRestrictIsoRestrict (baseChangeAlongProj f Y) g.target).inv ≫
              pullback.snd (baseChangeAlongProj f Y) g.target.ι =
            baseChangeAlongProj f Y ∣_ g.target from rfl]
        rw [morphismRestrict_ι]
      rw [Category.assoc, ha_snd, h1]
  -- ### `φ` and `ψ` are mutually inverse
  have hφψ : φ ≫ ψ = 𝟙 _ := by
    rw [← cancel_mono (((baseChangeAlongProj f X) ⁻¹ᵁ g.source).ι)]
    rw [Category.assoc, hψι, ← Category.assoc]
    rw [show φ ≫ (pullbackRestrictIsoRestrict (baseChangeAlongProj f Y) g.target).inv = L from by
          dsimp only [φ]
          rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]]
    rw [key1, Category.id_comp]
  have hψφ : ψ ≫ φ = 𝟙 _ := by
    rw [← cancel_mono (((baseChangeAlongProj f Y) ⁻¹ᵁ g.target).ι)]
    rw [Category.assoc, hφι, key2, Category.id_comp]
  -- ### assembly
  let iso : ((baseChangeAlongProj f X) ⁻¹ᵁ g.source).toScheme ≅
      ((baseChangeAlongProj f Y) ⁻¹ᵁ g.target).toScheme := Iso.mk φ ψ hφψ hψφ
  let h : (baseChangeAlong f X).PartialIso (baseChangeAlong f Y) :=
    ⟨(baseChangeAlongProj f X) ⁻¹ᵁ g.source,
      Dense.preimage_baseChangeAlongProj f X g.dense_source,
      (baseChangeAlongProj f Y) ⁻¹ᵁ g.target,
      Dense.preimage_baseChangeAlongProj f Y g.dense_target, iso⟩
  refine ⟨h, rfl, rfl, ?_⟩
  have hhom : h.toPartialMap.hom = (PartialMap.baseChangeAlong f g.toPartialMap).hom := by
    have h1 : h.toPartialMap.hom = a := by
      rw [PartialIso.toPartialMap_hom]
      exact hφι
    rw [h1]
  have hWr : h.toPartialMap.domain ≤ (PartialMap.baseChangeAlong f g.toPartialMap).domain := by
    show h.toPartialMap.domain ≤ h.toPartialMap.domain
    exact le_rfl
  have hWrId : (baseChangeAlong f X).homOfLE hWr = 𝟙 _ :=
    Scheme.homOfLE_self ((PartialMap.baseChangeAlong f g.toPartialMap).domain) hWr
  rw [show h.toRationalMap = h.toPartialMap.toRationalMap from rfl, PartialMap.toRationalMap_eq_iff]
  refine ⟨h.toPartialMap.domain, h.toPartialMap.dense_domain, le_rfl, hWr, ?_⟩
  simp only [PartialMap.restrict_hom, Scheme.homOfLE_rfl, hWrId, Category.id_comp]
  exact hhom

end Work.K3
