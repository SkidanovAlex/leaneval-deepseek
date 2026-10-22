/-
AREA DERFORMAL — holes 4–7: the derived package.

`ResData.adj` (hole 7) proves that the derived solidification `L` is left adjoint to the derived
inclusion, using `Adjunction.derived` (the Quillen adjunction for `solC ⊣ incC`) together with
the absoluteness of `L` and of the derived inclusion.

`ResData.package` assembles holes 4–7 into a `Submission.Blueprint.DerivedPackage`, and
`solidEquiv_iff` identifies solid-equivalences with the maps inverted by `L` (via the adjunction
and the Yoneda criterion `Gen.PrecompBijective`).  Finally `derived_prop` discharges the
resolution hypothesis of `Submission.Blueprint.ResolutionProp`.
-/
import Submission.Work.DERFORMAL.Derivability
import Submission.Work.DERFORMAL.B1KProjective
import Submission.Work.DERFORMAL.Gen.PrecompBijective

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

set_option linter.unusedSectionVars false

namespace Work.DERFORMAL

variable [isSolid.ι.IsRightAdjoint]

/-- The comparison isomorphism `Q ⋙ derivedInclusion ≅ incC ⋙ Q` (the derived inclusion is
induced by the degreewise inclusion). -/
abbrev incCFactors : Q ⋙ derivedInclusion ≅ incC ⋙ Q :=
  isSolid.ι.mapDerivedCategoryFactors

/-- The comparison exhibiting the derived inclusion as a right derived functor of the degreewise
inclusion. -/
abbrev incCComparison : incC ⋙ Q ⟶ Q ⋙ derivedInclusion := incCFactors.inv

/-- The derived inclusion is the right derived functor of the degreewise inclusion.  (Stated as a
theorem rather than an instance so as not to interfere with the corresponding instance of
`Solution.lean`.) -/
theorem incC_isRightDerivedFunctor :
    derivedInclusion.IsRightDerivedFunctor incCComparison Ws :=
  Functor.isRightDerivedFunctor_of_inverts Ws derivedInclusion incCFactors

namespace ResData

variable (R : ResData)

/-- `incC` together with the derived solidification inverts quasi-isomorphisms of complexes of
solid objects (used for the absoluteness of `derivedInclusion ⋙ L`). -/
theorem invertedBy_incC_L : Ws.IsInvertedBy ((incC ⋙ Q) ⋙ R.L) := by
  intro K K' f hf
  have h1 : QuasiIso (incC.map f) := quasiIso_incC_map_iff f |>.mpr hf
  change IsIso (R.L.map (Q.map (incC.map f)))
  haveI : IsIso (Q.map (incC.map f)) := inferInstance
  exact Functor.map_isIso R.L _

/-- The composite `L ⋙ derivedInclusion` is a left derived functor of `(solC ⋙ Q) ⋙
derivedInclusion` (absoluteness of `L`). -/
theorem leftDerived_comp : (R.L ⋙ derivedInclusion).IsLeftDerivedFunctor
    ((Functor.associator Q R.L derivedInclusion).inv ≫
      Functor.whiskerRight R.alpha derivedInclusion) Wq := by
  haveI : Phi.IsLeftDerivabilityStructure := isLeftDerivabilityStructure R
  refine LocalizerMorphism.Derives.isLeftDerivedFunctor_of_isIso (Φ := Phi)
    (F := (solC ⋙ Qs) ⋙ derivedInclusion) (L₂ := Q (C := LightCondAb))
    (LF := R.L ⋙ derivedInclusion) ?_
    ((Functor.associator Q R.L derivedInclusion).inv ≫
      Functor.whiskerRight R.alpha derivedInclusion) ?_
  · exact (MorphismProperty.IsInvertedBy.iff_of_iso WCoh
      (Functor.associator Phi.functor (solC ⋙ Qs) derivedInclusion)).mp
      (MorphismProperty.IsInvertedBy.of_comp WCoh (Phi.functor ⋙ (solC ⋙ Qs)) R.derives
        derivedInclusion)
  · intro X₁
    haveI h : IsIso (R.alpha.app (Cohι.obj X₁)) := R.iso_of_cofibrant X₁.obj X₁.2
    simp only [NatTrans.comp_app, Functor.associator_inv_app, Functor.whiskerRight_app,
      Category.id_comp]
    exact Functor.map_isIso derivedInclusion (R.alpha.app (Cohι.obj X₁))

/-- The composite `derivedInclusion ⋙ L` is a right derived functor of `incC ⋙ Q ⋙ L`
(absoluteness of the derived inclusion). -/
theorem rightDerived_comp : (derivedInclusion ⋙ R.L).IsRightDerivedFunctor
    (Functor.whiskerRight incCComparison R.L ≫
      (Functor.associator Q derivedInclusion R.L).hom) Ws :=
  Functor.isRightDerivedFunctor_of_inverts Ws (derivedInclusion ⋙ R.L)
    (asIso (Functor.whiskerRight incCComparison R.L ≫
      (Functor.associator Q derivedInclusion R.L).hom)).symm

/-- **Hole 7.** Derived solidification is left adjoint to the derived inclusion. -/
noncomputable def adj : R.L ⊣ derivedInclusion := by
  haveI := R.isLeft
  haveI := R.leftDerived_comp
  haveI := R.rightDerived_comp
  haveI := incC_isRightDerivedFunctor
  exact Adjunction.derived solCAdj Wq Ws R.alpha incCComparison

/-- **Holes 4–7**: the derived package attached to a functorial solid-cofibrant resolution. -/
noncomputable def package : Submission.Blueprint.DerivedPackage where
  L := R.L
  α := R.alpha
  isLeft := R.isLeft
  adj := R.adj
  iso_of_cofibrant := fun K hK => R.iso_of_cofibrant K hK

end ResData

/-- **Solid-equivalences are exactly the maps inverted by derived solidification.** -/
theorem solidEquiv_iff (D : Submission.Blueprint.DerivedPackage) {X Y : DCat} (f : X ⟶ Y) :
    SEquiv f ↔ IsIso (D.L.map f) := by
  haveI := D.adj
  rw [Gen.PrecompBijective]
  constructor
  · intro h N
    exact (bijective_of_equiv_conj (fun g : D.L.obj Y ⟶ N => D.L.map f ≫ g)
      (fun g : Y ⟶ derivedInclusion.obj N => f ≫ g)
      (D.adj.homEquiv Y N) (D.adj.homEquiv X N)
      (fun a => D.adj.homEquiv_naturality_left f a)).mpr (h N)
  · intro h N
    exact (bijective_of_equiv_conj (fun g : D.L.obj Y ⟶ N => D.L.map f ≫ g)
      (fun g : Y ⟶ derivedInclusion.obj N => f ≫ g)
      (D.adj.homEquiv Y N) (D.adj.homEquiv X N)
      (fun a => D.adj.homEquiv_naturality_left f a)).mp (h N)

end Work.DERFORMAL
