import Mathlib
import Submission.Work.DSMap.Gaps
import Submission.Work.DSF1.Cech.UnitCase
import Submission.Work.DSF1.Cech.isIsoDeletion_Qo
import Submission.Work.DSF1.Cech.CechQo

/-!
# `LOC` setup: the open `X_g`, the localized Čech complex and the comparison map

This file contains the vocabulary used by the proof of
`Work.DSEQP.eqp_cech_torsion_proved`, i.e. the statement that the higher Čech
cohomology of a finite affine cover `U` of `X` is killed by a power of `g` as soon
as `f ⁻¹ᵁ D(g)` is contained in one member `U j` of the cover.

* `Xg A X f g` is the open `f ⁻¹ᵁ D (g) ⊆ X`;
* `presheafLoc A X f g` is the presheaf of `A`-modules `W ↦ Γ (X, W ⊓ X_g)` — the
  localization of `cechPresheaf A X f` at `g`, termwise;
* `cechLoc A X f U g` is the Čech complex of that presheaf along `U`;
* `locCech A X f U g : cech A X f U ⟶ cechLoc A X f U g` is the comparison chain map.

The main mathematical input recorded here is the acyclicity of `cechLoc` in positive
degrees when `X_g ≤ U j` (`locCech_exact`), which is DSEQP's `UnitCase` of DSF1
(`Work.DSF1.Cech.UnitCase`) applied to the presheaf `W ↦ Γ (X, W ⊓ X_g)`: since
`X_g ≤ U j`, inserting the index `j` into a simplex of the Čech nerve does not change
the open `Eobj U n x ⊓ X_g`, so the cofaces are inverted and the Čech complex becomes
contractible.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry Limits Opposite
open scoped Simplicial BigOperators

namespace Work.DSEQP

universe a

section Defs

variable (A : Type a) [CommRing A]

/-- The open `X_g = f ⁻¹ᵁ D (g) ⊆ X`. -/
noncomputable def Xg (X : Scheme.{a}) (f : X ⟶ Spec (.of A)) (g : A) : X.Opens :=
  f ⁻¹ᵁ (PrimeSpectrum.basicOpen g : (Spec (.of A)).Opens)

/-- The presheaf `W ↦ Γ (X, W ⊓ X_g)`, a presheaf of `A`-modules via `phiU`. -/
noncomputable abbrev presheafLoc (X : Scheme.{a}) (f : X ⟶ Spec (.of A)) (g : A) :
    X.Opensᵒᵖ ⥤ ModuleCat.{a} A :=
  Work.DSF1.Cech.Qo (DSMap.cechPresheaf A X f) (Xg A X f g)

/-- The Čech complex of the localized presheaf `W ↦ Γ (X, W ⊓ X_g)`. -/
noncomputable def cechLoc (X : Scheme.{a}) (f : X ⟶ Spec (.of A)) {ι : Type a}
    (U : ι → X.Opens) (g : A) : CochainComplex (ModuleCat.{a} A) ℕ :=
  (cechComplexFunctor U).obj (presheafLoc A X f g)

/-- The comparison chain map `Č (U, 𝒪_X) ⟶ Č (U, W ↦ Γ (W ⊓ X_g))`. -/
noncomputable def locCech (X : Scheme.{a}) (f : X ⟶ Spec (.of A)) {ι : Type a}
    (U : ι → X.Opens) (g : A) : DSMap.cech A X f U ⟶ cechLoc A X f U g :=
  (cechComplexFunctor U).map (Work.DSF1.Cech.etaO (DSMap.cechPresheaf A X f) (Xg A X f g))

end Defs

/-! ## The geometric identifications -/

section Geom

variable {A : Type a} [CommRing A] {X : Scheme.{a}}

/-- The map `Γ (Spec A, ⊤) → Γ (X, ⊤)` underlying `f` is `phi` composed with
`ΓSpecIso.inv`. -/
theorem phi_appTop (f : X ⟶ Spec (.of A)) :
    (Scheme.Hom.appTop f).hom.comp ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
      = DSMap.phi A X f := by
  have h := ΓSpec_adjunction_homEquiv_eq (X := X) (B := CommRingCat.of A)
    (φ := ((ΓSpec.adjunction.homEquiv X (Opposite.op (CommRingCat.of A))).symm f).unop)
  have h2 : (ΓSpec.adjunction.homEquiv X (Opposite.op (CommRingCat.of A)))
      (((ΓSpec.adjunction.homEquiv X (Opposite.op (CommRingCat.of A))).symm f).unop.op) = f :=
    Equiv.apply_symm_apply _ f
  rw [h2] at h
  rw [h]
  simp only [DSMap.phi, CommRingCat.hom_comp, RingHom.comp_assoc]
  have key : (CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of A)).hom).comp
      (CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of A)).inv) = RingHom.id A := by
    apply RingHom.ext; intro x
    exact congrArg (fun (g : CommRingCat.of A ⟶ CommRingCat.of A) => CommRingCat.Hom.hom g x)
      (Iso.inv_hom_id (Scheme.ΓSpecIso (CommRingCat.of A)))
  rw [key, RingHom.comp_id]

/-- `f ⁻¹ᵁ D (g) = X.basicOpen (phi A X f g)`. -/
theorem Xg_eq_basicOpen (f : X ⟶ Spec (.of A)) (g : A) :
    Xg A X f g = X.basicOpen (DSMap.phi A X f g) := by
  rw [Xg, ← basicOpen_eq_of_affine (R := CommRingCat.of A) g]
  rw [Scheme.preimage_basicOpen_top]
  congr 1

/-- For an open `V`, the intersection `V ⊓ X_g` is the basic open of the image of `g`
in `Γ (X, V)`. -/
theorem inf_Xg_eq_basicOpen_phiU (f : X ⟶ Spec (.of A)) (g : A) (V : X.Opens) :
    V ⊓ Xg A X f g = X.basicOpen (DSMap.phiU A X f V g) := by
  rw [Xg_eq_basicOpen]
  have h := Scheme.basicOpen_res (X := X) (f := DSMap.phi A X f g)
      (i := (homOfLE (le_top : V ≤ ⊤)).op) (U := (⊤ : X.Opens))
  rw [← h]
  congr 1

end Geom

section Diagonal

variable {A : Type a} [CommRing A] {X : Scheme.{a}} {f : X ⟶ Spec (.of A)}

/-- A scheme separated over `Spec A` is a separated scheme. -/
theorem isSeparated_scheme (hf : IsSeparated f) : X.IsSeparated := by
  refine ⟨?_⟩
  rw [← Limits.terminal.comp_from f]
  exact inferInstance

/-- The diagonal of a scheme separated over `Spec A` is an affine morphism, which is what
Mathlib's `IsAffineOpen.iInf` consumes. -/
theorem isAffineHom_diagonal_of_isSeparated (hf : IsSeparated f) :
    IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X)) := by
  haveI : X.IsSeparated := isSeparated_scheme hf
  haveI : IsClosedImmersion (Limits.pullback.diagonal (Limits.terminal.from X)) := inferInstance
  infer_instance

end Diagonal

section Unit

variable {A : Type a} [CommRing A] {X : Scheme.{a}} {ι : Type a} {U : ι → X.Opens}
  {f : X ⟶ Spec (.of A)} {g : A} {j : ι}

/-- The presheaf `W ↦ Γ (X, W ⊓ X_g)` inverts the cofaces of the Čech nerve of `U`
which insert the index `j`, as soon as `X_g ≤ U j`. -/
theorem isIsoDeletion_locCech (hgood : Xg A X f g ≤ U j) :
    Work.DSF1.Cech.IsIsoDeletion U (presheafLoc A X f g) j :=
  Work.DSF1.Cech.isIsoDeletion_Qo hgood

/-- **Acyclicity of the localized Čech complex.**  If `X_g ≤ U j` then every
`(q+1)`-cocycle of `cechLoc A X f U g` is a `q`-coboundary. -/
theorem locCech_exact (hgood : Xg A X f g ≤ U j) (q : ℕ) (z : (cechLoc A X f U g).X (q + 1))
    (hz : ((cechLoc A X f U g).d (q + 1) (q + 2)).hom z = 0) :
    ∃ y : (cechLoc A X f U g).X q, ((cechLoc A X f U g).d q (q + 1)).hom y = z :=
  (Work.DSF1.Cech.UnitCase U (presheafLoc A X f g) j (isIsoDeletion_locCech hgood)).2.1 q z hz

end Unit

end Work.DSEQP
