import Mathlib
import Submission.Work.DSMap.Map
import Submission.Work.DSF1.Cech.CechMain
import Submission.Work.DSF1.Cech.UnitCase
import Submission.Work.DSF1.Cech.CechLocalized
import Submission.Work.DSF1.Cech.isIsoDeletion_Qi
import Submission.Work.DSF1.Cech.cechComplexFunctor_map_pi
import Submission.Work.DSF1.Cech.exists_pow_smul_mem_range_loc

/-!
# Čech exactness for an arbitrary coefficient presheaf (DSF1 infrastructure)

The target `Submission.Work.DSF1.Sheaf.cech_standard_tilde_exact` asks that the Čech
complex of the standard cover `D (f i)` of `Spec R` with coefficients in `M^~` has no
homology in positive degrees.

The proof follows the architecture of `Work.DSF1.Cech.cechSpec_quasiIso` (which treats the
case of the structure sheaf, i.e. `M = R`), but with an arbitrary coefficient presheaf of
`R`-modules:

* the *unit case* (`Work.DSF1.Cech.UnitCase`) and the fact that the "localized" presheaf
  `Qi U P i` satisfies `IsIsoDeletion` (`Work.DSF1.Cech.isIsoDeletion_Qi`) are already
  coefficient-agnostic;
* the "clearing of denominators" statements for the comparison maps
  `loc i : Č(P) ⟶ Č(Qi U P i)` (which in the structure sheaf case are
  `Work.DSF1.Cech.exists_pow_smul_mem_range_loc` and `Work.DSF1.Cech.eq_zero_of_loc_eq_zero`)
  are reduced here to a *componentwise* hypothesis `CompLoc P (f i)` on the coefficient
  presheaf `P`;
* the assembly (partition of unity and descent of exactness) is coefficient-agnostic.

This file contains the vocabulary (`cechGen`, `locGen`, `CompLoc`) and the generic lemmas.
-/

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped AlgebraicGeometry Simplicial BigOperators

namespace Work.DSF1.Sheaf

universe u

section Tilde

variable {R : CommRingCat.{u}}

/-- Sections of `M^~` over an open of `Spec R`, as an `R`-module. -/
noncomputable abbrev tildeSec (M : ModuleCat.{u} R) (W : (Spec R).Opens) : Type u :=
  ↥((AlgebraicGeometry.modulesSpecToSheaf.obj (AlgebraicGeometry.tilde M)).presheaf.obj (op W))

/-- The presheaf of `R`-modules `W ↦ Γ(W, M^~)` on the opens of `Spec R`. -/
noncomputable def tildePresheaf (M : ModuleCat.{u} R) : (Spec R).Opensᵒᵖ ⥤ ModuleCat.{u} R :=
  (AlgebraicGeometry.modulesSpecToSheaf.obj (AlgebraicGeometry.tilde M)).presheaf

end Tilde

/-- The opens of `Spec R`. -/
noncomputable abbrev Och (R : CommRingCat.{u}) := AlgebraicGeometry.Scheme.Opens (AlgebraicGeometry.Spec R)

/-- Presheaves of `R`-modules on the opens of `Spec R`. -/
noncomputable abbrev MPSheaf (R : CommRingCat.{u}) :=
  CategoryTheory.Functor.{u, u, u, u + 1} (Opposite (Och R)) (ModuleCat.{u} R)

section Generic

variable {R : Type u} [CommRing R]

/-- The Čech complex of a family of opens with coefficients in a presheaf of `R`-modules. -/
noncomputable abbrev cechGen {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    (P : X.Opensᵒᵖ ⥤ ModuleCat.{u} R) : CochainComplex (ModuleCat.{u} R) ℕ :=
  (cechComplexFunctor U).obj P

/-- The comparison map `Č(P) ⟶ Č(Qi U P i)` induced by the restriction `P ⟶ Qi U P i`. -/
noncomputable abbrev locGen {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    (P : X.Opensᵒᵖ ⥤ ModuleCat.{u} R) (i : ι) :
    cechGen U P ⟶ cechGen U (Work.DSF1.Cech.Qi U P i) :=
  (cechComplexFunctor U).map (Work.DSF1.Cech.etaI U P i)

/-- **Componentwise clearing of denominators.**  `CompLoc P h` says that for every `g : R`,
the restriction `P (D g) ⟶ P (D g ⊓ D h)` exhibits the target as the localization of the
source away from `h`: every element of the target becomes, after multiplication by a power
of `h`, a restriction, and every element killed by the restriction is killed by a power
of `h`. -/
def CompLoc {R : CommRingCat.{u}} (P : MPSheaf R) (h : R) : Prop :=
  (∀ (g : R) (z : ↥(P.obj (op (PrimeSpectrum.basicOpen g ⊓ PrimeSpectrum.basicOpen h)))),
      ∃ (k : ℕ) (t : ↥(P.obj (op (PrimeSpectrum.basicOpen g)))),
        (P.map (homOfLE (inf_le_left :
            PrimeSpectrum.basicOpen g ⊓ PrimeSpectrum.basicOpen h ≤
              PrimeSpectrum.basicOpen g)).op).hom t = h ^ k • z) ∧
    (∀ (g : R) (t : ↥(P.obj (op (PrimeSpectrum.basicOpen g)))),
        (P.map (homOfLE (inf_le_left :
            PrimeSpectrum.basicOpen g ⊓ PrimeSpectrum.basicOpen h ≤
              PrimeSpectrum.basicOpen g)).op).hom t = 0 → ∃ k : ℕ, h ^ k • t = 0)

end Generic

section Transport

variable {R : CommRingCat.{u}}

/-- The forgetful functor from `R`-modules to abelian groups. -/
abbrev forgetF (R : CommRingCat.{u}) : ModuleCat.{u} R ⥤ AddCommGrpCat.{u} :=
  CategoryTheory.forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}

/-- A presheaf of `R`-modules on `Spec R` viewed as a presheaf of abelian groups. -/
noncomputable abbrev forgetPresheaf (R : CommRingCat.{u}) (P : MPSheaf R) :
    CategoryTheory.Functor (Opposite (Och R)) AddCommGrpCat.{u} :=
  CategoryTheory.Functor.comp P (forgetF R)

/-- The Čech complex of a presheaf of `R`-modules, viewed as a complex of abelian groups. -/
noncomputable abbrev forgetComplex (R : CommRingCat.{u}) {ι : Type u} (U : ι → Och R)
    (P : MPSheaf R) : CochainComplex AddCommGrpCat.{u} ℕ :=
  (CategoryTheory.Functor.mapHomologicalComplex (forgetF R)
    (ComplexShape.up ℕ)).obj ((CategoryTheory.cechComplexFunctor U).obj P)

/-- The Čech complex of the underlying presheaf of abelian groups. -/
noncomputable abbrev cechAb (R : CommRingCat.{u}) {ι : Type u} (U : ι → Och R)
    (P : MPSheaf R) : CochainComplex AddCommGrpCat.{u} ℕ :=
  (CategoryTheory.cechComplexFunctor U).obj (forgetPresheaf R P)

end Transport

end Work.DSF1.Sheaf
