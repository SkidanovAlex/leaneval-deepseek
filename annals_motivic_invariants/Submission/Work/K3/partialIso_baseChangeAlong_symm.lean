import Mathlib
import Submission.Work.K3.BaseChangeBirational
import Submission.Work.K3.partialMap_baseChangeAlong_equiv

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

/-- **Base change of a partial isomorphism, with the inverse.** Strengthens
`Submission/Work/K3/partialIso_baseChangeAlong.lean` by also identifying the inverse.
PROOF ROUTE: copy the proof of `Submission/Work/K3/partialIso_baseChangeAlong.lean` — but do NOT
`import` that file, it redeclares `Work.K3.PartialMap.baseChangeAlong_hom_fst` / `_hom_snd` which
clash with the copies in `Submission/Work/K3/partialMap_baseChangeAlong_equiv.lean`; import the
latter instead (it has the same leg lemmas). That proof constructs explicit morphisms `a`, `a'`
and proves `key1 : L ≫ a' = (s ⁻¹ᵁ g.source).ι` and `key2 : ψ ≫ a = (t ⁻¹ᵁ g.target).ι`; its
`h.toPartialMap.hom` is the `a` there, which is exactly
`(Work.K3.PartialMap.baseChangeAlong f g.toPartialMap).hom`. For the new conjunct note
`h.symm.toPartialMap.hom = h.iso.inv ≫ h.source.ι` and `h.iso = Iso.mk φ ψ _ _` so `h.iso.inv = ψ`,
hence `h.symm.toPartialMap.hom = ψ ≫ (s ⁻¹ᵁ g.source).ι`, which by `hψι` equals
`(pullbackRestrictIsoRestrict (baseChangeAlongProj f Y) g.target).inv ≫ a'`; compare this with the
explicit `pullback.lift` that *is* `(Work.K3.PartialMap.baseChangeAlong f g.symm.toPartialMap).hom`
by `pullback.hom_ext` (components: `ha'f` vs `pullbackRestrictIsoRestrict_inv_fst`, and `ha's` vs
the definition of `morphismRestrict`). -/
theorem partialIso_baseChangeAlong_symm {S T X Y : AlgebraicGeometry.Scheme.{0}}
    (f : T ⟶ S) [AlgebraicGeometry.Scheme.Over X S] [AlgebraicGeometry.Scheme.Over Y S]
    [AlgebraicGeometry.Surjective f] [AlgebraicGeometry.UniversallyOpen f]
    (g : X.PartialIso Y) (hg : AlgebraicGeometry.Scheme.PartialMap.IsOver S g.toPartialMap)
    [hg' : AlgebraicGeometry.Scheme.PartialMap.IsOver S g.symm.toPartialMap] :
    ∃ h : (Work.K3.baseChangeAlong f X).PartialIso (Work.K3.baseChangeAlong f Y),
      AlgebraicGeometry.Scheme.PartialIso.toRationalMap h =
        AlgebraicGeometry.Scheme.PartialMap.toRationalMap
          (Work.K3.PartialMap.baseChangeAlong f g.toPartialMap) ∧
      AlgebraicGeometry.Scheme.PartialIso.toRationalMap h.symm =
        AlgebraicGeometry.Scheme.PartialMap.toRationalMap
          (Work.K3.PartialMap.baseChangeAlong f g.symm.toPartialMap) := by
  classical
  haveI : g.toPartialMap.IsOver S := hg
  -- ### the `IsOver S` equation for `g`
  have hgS : g.iso.hom ≫ g.target.ι ≫ (Y ↘ S) = g.source.ι ≫ (X ↘ S) := by
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
              rw [← hgS, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]]
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
  refine ⟨h, ?_, ?_⟩
  · -- ### the forward rational map
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
  · -- ### the inverse rational map
    -- the morphism underlying the base change of `g.symm.toPartialMap`
    let a'' : ((baseChangeAlongProj f Y) ⁻¹ᵁ g.target).toScheme ⟶ baseChangeAlong f X :=
      (PartialMap.baseChangeAlong f g.symm.toPartialMap).hom
    have ha''_fst : a'' ≫ pullback.fst f (X ↘ S) =
        (((baseChangeAlongProj f Y) ⁻¹ᵁ g.target) : (baseChangeAlong f Y).Opens).ι ≫
          pullback.fst f (Y ↘ S) :=
      PartialMap.baseChangeAlong_hom_fst f g.symm.toPartialMap
    have ha''_snd : a'' ≫ pullback.snd f (X ↘ S) =
        (baseChangeAlongProj f Y ∣_ g.target) ≫ g.iso.inv ≫ g.source.ι :=
      PartialMap.baseChangeAlong_hom_snd f g.symm.toPartialMap
    have hsymm : h.symm.toPartialMap.hom =
        (PartialMap.baseChangeAlong f g.symm.toPartialMap).hom := by
      have h1 : h.symm.toPartialMap.hom = ψ ≫ ((baseChangeAlongProj f X) ⁻¹ᵁ g.source).ι := by
        show (h.iso.symm).hom ≫ h.source.ι = ψ ≫ ((baseChangeAlongProj f X) ⁻¹ᵁ g.source).ι
        rfl
      have hkey : (pullbackRestrictIsoRestrict (baseChangeAlongProj f Y) g.target).inv ≫ a'
          = a'' := by
        apply pullback.hom_ext (f := f) (g := X ↘ S)
        · show ((pullbackRestrictIsoRestrict (baseChangeAlongProj f Y) g.target).inv ≫ a') ≫
              pullback.fst f (X ↘ S) = a'' ≫ pullback.fst f (X ↘ S)
          rw [Category.assoc, ha'f]
          dsimp only [c]
          rw [← Category.assoc, pullbackRestrictIsoRestrict_inv_fst, ha''_fst]
        · show ((pullbackRestrictIsoRestrict (baseChangeAlongProj f Y) g.target).inv ≫ a') ≫
              pullback.snd f (X ↘ S) = a'' ≫ pullback.snd f (X ↘ S)
          rw [Category.assoc, ha's]
          dsimp only [d]
          rw [ha''_snd]
          dsimp only [morphismRestrict]
          simp only [Category.assoc]
      rw [h1, hψι]
      exact hkey
    have hWr : h.symm.toPartialMap.domain ≤
        (PartialMap.baseChangeAlong f g.symm.toPartialMap).domain := by
      show h.symm.toPartialMap.domain ≤ h.symm.toPartialMap.domain
      exact le_rfl
    have hWrId : (baseChangeAlong f Y).homOfLE hWr = 𝟙 _ :=
      Scheme.homOfLE_self ((PartialMap.baseChangeAlong f g.symm.toPartialMap).domain) hWr
    rw [show h.symm.toRationalMap = h.symm.toPartialMap.toRationalMap from rfl,
      PartialMap.toRationalMap_eq_iff]
    refine ⟨h.symm.toPartialMap.domain, h.symm.toPartialMap.dense_domain, le_rfl, hWr, ?_⟩
    simp only [PartialMap.restrict_hom, Scheme.homOfLE_rfl, hWrId, Category.id_comp]
    exact hsymm

end Work.K3
