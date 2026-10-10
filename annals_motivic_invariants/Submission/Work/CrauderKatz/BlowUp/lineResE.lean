import Mathlib
import Submission.Work.CrauderKatz.BlowUp.LineDefs
import Submission.Work.CrauderKatz.BlowUp.LineGlue
import Submission.Work.CrauderKatz.BlowUp.LineMap
import Submission.Work.CrauderKatz.BlowUp.lineK_height
import Submission.Work.CrauderKatz.BlowUp.lineK_isPrime
import Submission.Work.Motivic.resEquiv_of_morphism
import Submission.Work.CrauderKatz.isFractionRing_polynomial_ratFunc
import Submission.Work.CrauderKatz.ratFunc_equiv_fractionRing_polynomial
import Submission.Work.CrauderKatz.BlowUp.lineK_quotient_algEquiv
import Submission.Work.CrauderKatz.BlowUp.fractionRing_mvPolynomial_finTwo
import Submission.Work.CrauderKatz.BlowUp.fractionRing_algEquiv_of_algEquiv

set_option linter.unusedVariables false -- v435-speed

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

/-!
# `Work.CrauderKatz.BlowUp.lineResE` — the residue field of the exceptional surface

`lineBlowUpE 𝕜 = lineChart₁ 𝕜 ⟨lineK 𝕜, lineK_isPrime 𝕜⟩` is the generic point of the exceptional
surface of the thickened blow-up of `𝔸³` along a coordinate line, and
`lineBlowUpE 𝕜` has residue field `RatFunc (RatFunc 𝕜) = 𝕜(t)(z)` as a `𝕜`-algebra.  This is the
(F1)-type input `resE` of `Work.CrauderKatz.LineBlowUp`.

Two steps:

1. *Affine computation.*  With `p = ⟨lineK 𝕜, lineK_isPrime 𝕜⟩` the prime `(x, ε)` of the chart ring
   `lineRing 𝕜 = 𝕜[x,t,z,ε]/(ε², x·ε)`, the residue field of `p` is
   `lineK 𝕜 ⧸ ·`'s fraction field `≅ RatFunc (RatFunc 𝕜)`, compatibly with the structure maps
   (`Work.CrauderKatz.BlowUp.resAlgEquiv_lineChartS_lineK`).  The ingredients are
   `lineK_quotient_algEquiv` (the chart quotient by `(x, ε)` is `𝕜[t,z]`),
   `fractionRing_algEquiv_of_algEquiv` and `fractionRing_mvPolynomial_finTwo`.
2. *Transport.*  The first chart `lineChart₁ 𝕜` is an open immersion, so it induces an isomorphism
   of residue fields at every point; composing with step 1 gives the claim.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace Work.CrauderKatz.BlowUp

noncomputable section

variable (𝕜 : Type) [Field 𝕜]

/-! ## Auxiliary lemmas about `Spec`, global sections and residue fields -/

/-- `Spec.map` is injective on ring homomorphisms (faithfulness of the `Spec` functor). -/
lemma spec_map_injective {A B : CommRingCat} {f g : A ⟶ B} (h : Spec.map f = Spec.map g) : f = g := by
  have h2 : Scheme.Spec.map (Quiver.Hom.op f) = Scheme.Spec.map (Quiver.Hom.op g) := by
    simpa [Scheme.Spec_map] using h
  exact Quiver.Hom.op_inj (Spec.faithful.map_injective h2)

/-- **`appTop` of `Spec.map` on global sections.**  For a ring homomorphism `φ : A ⟶ B` the induced
map on global sections of `Spec`, composed with the canonical identifications
`Γ(Spec A) ≅ A`, `Γ(Spec B) ≅ B`, is `φ` itself: equivalently
`(Spec.map φ).appTop ((ΓSpecIso A).inv a) = (ΓSpecIso B).inv (φ a)`. -/
lemma spec_appTop_ΓSpecIso_inv {A B : CommRingCat} (φ : A ⟶ B) (a : A) :
    (Spec.map φ).appTop ((Scheme.ΓSpecIso A).inv a) = (Scheme.ΓSpecIso B).inv (φ a) := by
  have hnat := Scheme.toSpecΓ_naturality (Spec.map φ)
  rw [← SpecMap_ΓSpecIso_hom A, ← SpecMap_ΓSpecIso_hom B] at hnat
  have hcomp : Spec.map ((Scheme.ΓSpecIso A).hom ≫ φ) =
      Spec.map ((Spec.map φ).appTop ≫ (Scheme.ΓSpecIso B).hom) := by
    rw [Spec.map_comp, Spec.map_comp]
    exact hnat
  have hring : (Scheme.ΓSpecIso A).hom ≫ φ = (Spec.map φ).appTop ≫ (Scheme.ΓSpecIso B).hom :=
    spec_map_injective hcomp
  have happ : (Spec.map φ).appTop = (Scheme.ΓSpecIso A).hom ≫ φ ≫ (Scheme.ΓSpecIso B).inv := by
    rw [← cancel_mono (Scheme.ΓSpecIso B).hom, Category.assoc, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
    exact hring.symm
  rw [happ]
  exact congrArg (⇑(Scheme.ΓSpecIso B).inv) (congrArg (⇑φ) (Iso.inv_hom_id_apply (Scheme.ΓSpecIso A) a))

/-! ## The structure map `𝕜 → κ(p)` of an affine chart as an algebraic map

For an affine scheme `Spec R` over `Spec 𝕜` given by `φ : 𝕜 →+* R`, the structure map
`resMap 𝕜 (Spec R) p : 𝕜 →+* κ(p)` is the composite of the canonical map
`Spec.residueFieldIso R p : κ(p) ≅ p.asIdeal.ResidueField` with the algebra map
`𝕜 → R → p.asIdeal.ResidueField`. -/

/-- **`resMap` on an affine chart.**  The structure map `𝕜 →+* κ(p)` of `Spec R` at a prime `p` is the
`p.asIdeal.ResidueField`-algebra structure map, transported along `Spec.residueFieldIso`. -/
lemma resMap_spec_eq (𝕜 : Type) [Field 𝕜] (R : Type) [CommRing R] [Algebra 𝕜 R]
    (p : PrimeSpectrum R) :
    resMap 𝕜 (Spec (CommRingCat.of R)) p =
      (((Spec.residueFieldIso (CommRingCat.of R) p).inv).hom).comp
        ((algebraMap R p.asIdeal.ResidueField).comp (algebraMap 𝕜 R)) := by
  have hhom : (Spec (CommRingCat.of R) ↘ Spec (CommRingCat.of 𝕜)) =
      Spec.map (CommRingCat.ofHom (algebraMap 𝕜 R)) := specOverSpec_over
  ext a
  simp only [resMap, hhom, CommRingCat.hom_comp, RingHom.comp_apply]
  rw [spec_appTop_ΓSpecIso_inv (CommRingCat.ofHom (algebraMap 𝕜 R)) a]
  exact (congrArg (fun (f : CommRingCat.of R ⟶ (Spec (CommRingCat.of R)).residueField p) =>
    f.hom (algebraMap 𝕜 R a)) (Spec.algebraMap_residueFieldIso_inv (CommRingCat.of R) p)).symm

/-- **`resMap` on the first chart** of the thickened blow-up (the specialisation of
`resMap_spec_eq` to `R = lineRing 𝕜`). -/
lemma resMap_lineChartS_eq (p : PrimeSpectrum (lineRing 𝕜)) :
    resMap 𝕜 (lineChartS 𝕜) p =
      (((Spec.residueFieldIso (CommRingCat.of (lineRing 𝕜)) p).inv).hom).comp
        ((algebraMap (lineRing 𝕜) p.asIdeal.ResidueField).comp (algebraMap 𝕜 (lineRing 𝕜))) :=
  resMap_spec_eq 𝕜 (lineRing 𝕜) p

/-! ## The `𝕜`-structure maps through the quotient `lineRing 𝕜 ⧸ lineK 𝕜`

Lean's typeclass search does not reliably fill in the `CommSemiring`/`Algebra` arguments of
`algebraMap` when the *source* is the quotient `lineRing 𝕜 ⧸ lineK 𝕜` (there are several
definitionally equal but syntactically distinct quotient instances).  We therefore pin these maps
once and for all, with all instances given explicitly. -/

/-- The residue field of the prime `lineK 𝕜`, i.e. of the generic point of the exceptional surface
inside the chart. -/
abbrev lineResK (𝕜 : Type) [Field 𝕜] : Type :=
  @Ideal.ResidueField (lineRing 𝕜) _ (lineK 𝕜) (lineK_isPrime 𝕜)

/-- The structure map `𝕜 → lineRing 𝕜 ⧸ lineK 𝕜`. -/
noncomputable abbrev lineKToQuot (𝕜 : Type) [Field 𝕜] :
    𝕜 →+* (lineRing 𝕜 ⧸ lineK 𝕜) :=
  @algebraMap 𝕜 (lineRing 𝕜 ⧸ lineK 𝕜) (inferInstance : CommSemiring 𝕜)
    (inferInstance : Semiring (lineRing 𝕜 ⧸ lineK 𝕜)) (Ideal.instAlgebraQuotient 𝕜 (lineK 𝕜))

/-- The canonical map `lineRing 𝕜 ⧸ lineK 𝕜 → κ(lineK 𝕜)`. -/
noncomputable abbrev lineQuotToResidue (𝕜 : Type) [Field 𝕜] :
    (lineRing 𝕜 ⧸ lineK 𝕜) →+* lineResK 𝕜 :=
  @algebraMap (lineRing 𝕜 ⧸ lineK 𝕜) (lineResK 𝕜) (Ideal.Quotient.commSemiring (lineK 𝕜))
    (inferInstance : Semiring (lineResK 𝕜))
    (@instAlgebraQuotientIdealResidueField (lineRing 𝕜) _ (lineK 𝕜) (lineK_isPrime 𝕜))

/-- The canonical map `lineRing 𝕜 ⧸ lineK 𝕜 → FractionRing (lineRing 𝕜 ⧸ lineK 𝕜)`. -/
noncomputable abbrev lineQuotToFr (𝕜 : Type) [Field 𝕜] :
    (lineRing 𝕜 ⧸ lineK 𝕜) →+* FractionRing (lineRing 𝕜 ⧸ lineK 𝕜) :=
  @algebraMap (lineRing 𝕜 ⧸ lineK 𝕜) (FractionRing (lineRing 𝕜 ⧸ lineK 𝕜))
    (Ideal.Quotient.commSemiring (lineK 𝕜))
    (inferInstance : Semiring (FractionRing (lineRing 𝕜 ⧸ lineK 𝕜)))
    (inferInstance : Algebra (lineRing 𝕜 ⧸ lineK 𝕜) (FractionRing (lineRing 𝕜 ⧸ lineK 𝕜)))

/-- **Step (1), the affine computation.**  The residue field of the prime `lineK 𝕜 = (x, ε)` of the
chart ring — the generic point of the exceptional surface inside the chart — is, as a `𝕜`-algebra,
the iterated rational function field `RatFunc (RatFunc 𝕜)`.

The equivalence is built from the fraction ring `FractionRing (lineRing 𝕜 ⧸ lineK 𝕜)` of the chart
quotient, which `lineK_quotient_algEquiv` identifies with `𝕜[t,z]` and
`fractionRing_mvPolynomial_finTwo` with `RatFunc (RatFunc 𝕜)`. -/
theorem resAlgEquiv_lineChartS_lineK :
    Work.LLink.ResAlgEquiv (X := lineChartS 𝕜) 𝕜 ⟨lineK 𝕜, lineK_isPrime 𝕜⟩
      (RatFunc (RatFunc 𝕜)) (algebraMap 𝕜 (RatFunc (RatFunc 𝕜))) := by
  have hQ : Nonempty ((lineRing 𝕜 ⧸ lineK 𝕜) ≃ₐ[𝕜] MvPolynomial (Fin 2) 𝕜) :=
    lineK_quotient_algEquiv 𝕜
  obtain ⟨eQ⟩ := hQ
  have hF : Nonempty (FractionRing (MvPolynomial (Fin 2) 𝕜) ≃ₐ[𝕜] RatFunc (RatFunc 𝕜)) :=
    fractionRing_mvPolynomial_finTwo 𝕜
  obtain ⟨eF⟩ := hF
  have hQF : Nonempty (FractionRing (lineRing 𝕜 ⧸ lineK 𝕜) ≃ₐ[𝕜]
      FractionRing (MvPolynomial (Fin 2) 𝕜)) := fractionRing_algEquiv_of_algEquiv eQ
  obtain ⟨eQF⟩ := hQF
  -- the fraction-field isomorphism `κ(lineK) ≃+* FractionRing (lineRing ⧸ lineK)`
  let e1 : lineResK 𝕜 ≃+* FractionRing (lineRing 𝕜 ⧸ lineK 𝕜) :=
    ((FractionRing.algEquiv (A := lineRing 𝕜 ⧸ lineK 𝕜) (lineResK 𝕜)).symm).toRingEquiv
  let E : lineResK 𝕜 ≃+* RatFunc (RatFunc 𝕜) := e1.trans (eQF.toRingEquiv.trans eF.toRingEquiv)
  -- `e1` is the inverse of the `(lineRing ⧸ lineK)`-algebra iso `FractionRing.algEquiv`
  have he1 : e1.toRingHom.comp (lineQuotToResidue 𝕜) = lineQuotToFr 𝕜 := by
    show ((FractionRing.algEquiv (A := lineRing 𝕜 ⧸ lineK 𝕜) (lineResK 𝕜)).symm :
      lineResK 𝕜 ≃+* FractionRing (lineRing 𝕜 ⧸ lineK 𝕜)).toRingHom.comp
        (lineQuotToResidue 𝕜) = lineQuotToFr 𝕜
    refine RingHom.ext fun x => ?_
    exact AlgEquiv.commutes (FractionRing.algEquiv (A := lineRing 𝕜 ⧸ lineK 𝕜) (lineResK 𝕜)).symm x
  -- the two `𝕜`-structure maps on `κ(lineK)` agree
  have hA : (algebraMap (lineRing 𝕜) (lineResK 𝕜)).comp (algebraMap 𝕜 (lineRing 𝕜))
      = (lineQuotToResidue 𝕜).comp (lineKToQuot 𝕜) := by
    rw [IsScalarTower.algebraMap_eq (lineRing 𝕜) (lineRing 𝕜 ⧸ lineK 𝕜) (lineResK 𝕜),
      RingHom.comp_assoc,
      ← IsScalarTower.algebraMap_eq 𝕜 (lineRing 𝕜) (lineRing 𝕜 ⧸ lineK 𝕜)]
  -- the compatibility of `E` with the structure maps
  have hE : ∀ a : 𝕜, E (algebraMap (lineRing 𝕜) (lineResK 𝕜) (algebraMap 𝕜 (lineRing 𝕜) a))
      = algebraMap 𝕜 (RatFunc (RatFunc 𝕜)) a := by
    intro a
    have h1 : algebraMap (lineRing 𝕜) (lineResK 𝕜) (algebraMap 𝕜 (lineRing 𝕜) a)
        = lineQuotToResidue 𝕜 (lineKToQuot 𝕜 a) := by
      simpa only [RingHom.comp_apply] using RingHom.congr_fun hA a
    rw [h1]
    show eF (eQF (e1 (lineQuotToResidue 𝕜 (lineKToQuot 𝕜 a)))) = _
    have h2 : e1 (lineQuotToResidue 𝕜 (lineKToQuot 𝕜 a)) = lineQuotToFr 𝕜 (lineKToQuot 𝕜 a) := by
      show ((FractionRing.algEquiv (A := lineRing 𝕜 ⧸ lineK 𝕜) (lineResK 𝕜)).symm)
        (lineQuotToResidue 𝕜 (lineKToQuot 𝕜 a)) = _
      exact AlgEquiv.commutes (FractionRing.algEquiv (A := lineRing 𝕜 ⧸ lineK 𝕜) (lineResK 𝕜)).symm
        (lineKToQuot 𝕜 a)
    rw [h2]
    have h3 : lineQuotToFr 𝕜 (lineKToQuot 𝕜 a)
        = algebraMap 𝕜 (FractionRing (lineRing 𝕜 ⧸ lineK 𝕜)) a :=
      (IsScalarTower.algebraMap_apply 𝕜 (lineRing 𝕜 ⧸ lineK 𝕜)
        (FractionRing (lineRing 𝕜 ⧸ lineK 𝕜)) a).symm
    rw [h3, AlgEquiv.commutes eQF a, AlgEquiv.commutes eF a]
  -- transport along `Spec.residueFieldIso` and conclude
  let iso := Spec.residueFieldIso (CommRingCat.of (lineRing 𝕜)) ⟨lineK 𝕜, lineK_isPrime 𝕜⟩
  refine ⟨iso.commRingCatIsoToRingEquiv.trans E, ?_⟩
  have h1 : ∀ x : lineResK 𝕜, iso.commRingCatIsoToRingEquiv (iso.inv.hom x) = x := by
    intro x
    show iso.hom.hom (iso.inv.hom x) = x
    exact Iso.inv_hom_id_apply iso x
  refine RingHom.ext fun a => ?_
  show E (iso.commRingCatIsoToRingEquiv
      (resMap 𝕜 (lineChartS 𝕜) ⟨lineK 𝕜, lineK_isPrime 𝕜⟩ a)) = _
  rw [resMap_lineChartS_eq]
  simp only [RingHom.comp_apply]
  rw [h1]
  exact hE a

/-! ## Step (2): transport along the open immersion of the first chart -/

/-- **The residue field of the generic point of the exceptional surface, inside the blow-up.**  The
first chart `lineChart₁ 𝕜 : Spec R ⟶ lineBlowUp 𝕜` is an open immersion, hence induces an isomorphism
of residue fields at every point; at the prime `lineK 𝕜` this identifies the residue field of
`lineBlowUpE 𝕜` with the residue field of `⟨lineK 𝕜, lineK_isPrime 𝕜⟩` in the chart. -/
theorem resEquiv_lineBlowUpE :
    ResEquiv (X := lineBlowUp 𝕜) (Z := lineChartS 𝕜) 𝕜 (lineBlowUpE 𝕜)
      ⟨lineK 𝕜, lineK_isPrime 𝕜⟩ := by
  have hI : IsIso ((lineChart₁ 𝕜).residueFieldMap
      (⟨lineK 𝕜, lineK_isPrime 𝕜⟩ : PrimeSpectrum (lineRing 𝕜))) :=
    @instIsIsoCommRingCatResidueFieldMapOfIsOpenImmersion _ _ (lineChart₁ 𝕜) inferInstance
      ⟨lineK 𝕜, lineK_isPrime 𝕜⟩
  exact @Work.Motivic.resEquiv_of_morphism 𝕜 _ (lineChartS 𝕜) (lineBlowUp 𝕜) _ _ (lineChart₁ 𝕜)
    (lineChart₁_toBeSpecK 𝕜) ⟨lineK 𝕜, lineK_isPrime 𝕜⟩ hI

/-- **The residue field of the generic point of the exceptional surface of the thickened blow-up of
`𝔸³` along a coordinate line is the cylinder `RatFunc (RatFunc 𝕜)` over the affine line.**  This is
the field `resE` of `Work.CrauderKatz.LineBlowUp`, and the three-dimensional instance of the
(F1)-type input of the Crauder–Katz residual. -/
theorem lineResE (𝕜 : Type) [Field 𝕜] :
    Work.LLink.ResAlgEquiv 𝕜 (lineBlowUpE 𝕜) (RatFunc (RatFunc 𝕜))
      (algebraMap 𝕜 (RatFunc (RatFunc 𝕜))) := by
  obtain ⟨e, he⟩ := resEquiv_lineBlowUpE 𝕜
  obtain ⟨e', he'⟩ := resAlgEquiv_lineChartS_lineK 𝕜
  refine ⟨e.trans e', ?_⟩
  rw [show (e.trans e').toRingHom = e'.toRingHom.comp e.toRingHom from rfl]
  rw [RingHom.comp_assoc, he, he']

end

end Work.CrauderKatz.BlowUp
