/-
AREA DERFORMAL — the derivability structure giving the left-derived property of `L` (hole 6).

Following REFS/02 §1 (B3), we use the Kahn–Maltsiniotis framework in the form of
`LocalizerMorphism.IsLeftDerivabilityStructure`.  The source category is the full subcategory
`Coh` of solid-cofibrant complexes (which is where the counit `α` is an isomorphism), the
localizer morphism is the inclusion `Coh ⥤ C(LightCondAb)`, and the functorial left resolutions
are given by the resolution `ρ` of `ResData`.

We then prove that `L` is the left derived functor of `solC ⋙ Q`
(`ResData.isLeft`, hole 6), i.e. `Derives.isLeftDerivedFunctor_of_isIso` applied to the
resolutions.
-/
import Submission.Work.DERFORMAL.Lift
import Submission.Work.DERFORMAL.Gen.LeftDerivabilityStructure

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

set_option linter.unusedSectionVars false

namespace Work.DERFORMAL

variable [isSolid.ι.IsRightAdjoint]

/-! ## The subcategory of solid-cofibrant complexes -/

/-- The object property of being solid-cofibrant. -/
def cofProp : ObjectProperty Cpx := fun K => Cofibrant K

/-- The full subcategory of `C(LightCondAb)` on the solid-cofibrant complexes. -/
abbrev Coh : Type 1 := cofProp.FullSubcategory

/-- The inclusion of the solid-cofibrant complexes. -/
abbrev Cohι : Coh ⥤ Cpx := cofProp.ι

/-- The class of quasi-isomorphisms between solid-cofibrant complexes (as a morphism property
on the full subcategory, induced by quasi-isomorphisms in `C(LightCondAb)`). -/
abbrev WCoh : MorphismProperty Coh := Wq.inverseImage Cohι

/-- The localizer morphism given by the inclusion of the solid-cofibrant complexes. -/
noncomputable def Phi : LocalizerMorphism WCoh Wq := LocalizerMorphism.ofEq rfl

instance : Phi.functor.Full := ObjectProperty.full_ι cofProp

instance : Phi.functor.Faithful := ObjectProperty.faithful_ι cofProp

namespace ResData

/-- The resolution functor, viewed as a functor into the full subcategory of solid-cofibrant
complexes. -/
def resFun (R : ResData) : Cpx ⥤ Coh := ObjectProperty.lift cofProp R.ρ R.hcof

/-- The comparison `resFun R ⋙ Cohι ⟶ 𝟭` induced by `ε`. -/
def resEps (R : ResData) : R.resFun ⋙ Cohι ⟶ 𝟭 Cpx :=
  (ObjectProperty.liftCompιIso cofProp R.ρ R.hcof).inv ≫ R.ε

/-- Functorial left resolutions give a left derivability structure for the inclusion of the
solid-cofibrant complexes. -/
theorem isLeftDerivabilityStructure (R : ResData) : Phi.IsLeftDerivabilityStructure :=
  Gen.LeftDerivabilityStructure (Φ := Phi) (ρ := R.resFun) R.resEps (fun K => by
    show Wq ((R.resEps).app K)
    simp only [resEps, NatTrans.comp_app, Functor.id_obj, Category.id_comp]
    exact R.hqiso K) rfl

/-- Quasi-isomorphisms between solid-cofibrant complexes are inverted by `solC ⋙ Q`: the
`Derives` condition of the derivability structure (this is B2). -/
theorem derives (R : ResData) : Phi.Derives (solC ⋙ Qs) := by
  intro K K' f hf
  have hf' : QuasiIso (Cohι.map f) := hf
  have h2 : QuasiIso (solC.map (Cohι.map f)) := B2 R.hproj K.2 K'.2 hf'
  change IsIso (Qs.map (solC.map (Cohι.map f)))
  haveI : QuasiIso (solC.map (Cohι.map f)) := h2
  infer_instance

/-- **Hole 6.** `L`, together with its counit `α`, is the total left derived functor of
degreewise solidification. -/
theorem isLeft (R : ResData) : R.L.IsLeftDerivedFunctor R.alpha Wq := by
  haveI := R.isLeftDerivabilityStructure
  exact LocalizerMorphism.Derives.isLeftDerivedFunctor_of_isIso R.derives R.alpha
    (fun X₁ => R.iso_of_cofibrant X₁.1 X₁.2)

end ResData

end Work.DERFORMAL
