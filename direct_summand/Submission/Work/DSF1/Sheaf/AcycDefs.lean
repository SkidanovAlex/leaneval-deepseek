import Mathlib
import ChallengeDeps
import Submission.Work.DSMap.Map

/-!
# Vocabulary for the Čech/acyclicity argument of `DSF1` obligation (H1)

This module carries the small vocabulary used by `Work.DSF1.Sheaf.secSheaf_acyclic` and by the
lemmas delegated for it:

* `sectionsAt M U`, `sectionsMap f U`: sections of a sheaf of `𝒪_X`-modules over an open, as
  abelian groups, and the induced maps;
* `cechComplex U M`: Mathlib's Čech complex of the family `U` with coefficients in `M`;
* `CechTrivAt K p`, `CechTrivAll K`: "all `p`-cocycles are coboundaries" for a cochain complex;
* `HasCechCohomology M`: all Čech cocycles with coefficients `M`, for every finite family of
  opens, trivialise (property `C(M)` of the design in `secSheaf_acyclic.lean`).

Nothing here is proved; this is only the interface.
-/

namespace Work.DSF1.Sheaf

open CategoryTheory AlgebraicGeometry Opposite Limits

universe u

/-- The sections of a sheaf of `𝒪_X`-modules over an open `U`, as an abelian group. -/
noncomputable abbrev sectionsAt {X : Scheme.{u}} (M : SheafOfModules X.ringCatSheaf) (U : X.Opens) :
    AddCommGrpCat.{u} :=
  ((SheafOfModules.toSheaf X.ringCatSheaf).obj M).obj.obj (Opposite.op U)

/-- The map on sections over `U` induced by a morphism of sheaves of `𝒪_X`-modules. -/
noncomputable abbrev sectionsMap {X : Scheme.{u}} {M N : SheafOfModules X.ringCatSheaf}
    (f : M ⟶ N) (U : X.Opens) : sectionsAt M U ⟶ sectionsAt N U :=
  ((SheafOfModules.toSheaf X.ringCatSheaf).map f).hom.app (Opposite.op U)

/-- The Čech complex of a family of opens `U` with coefficients in a sheaf of `𝒪_X`-modules:
in degree `p` it is the product, over `x : Fin (p+1) → ι`, of the sections of `M` over the
intersection of the `U (x a)` (Mathlib's `cechComplexFunctor`, transported along the forgetful
functor to abelian groups). -/
noncomputable abbrev cechComplex {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    (M : SheafOfModules X.ringCatSheaf) : CochainComplex AddCommGrpCat.{u} ℕ :=
  (cechComplexFunctor U).obj ((SheafOfModules.toSheaf X.ringCatSheaf).obj M).obj

/-- `CechTrivAt K p` says that every `p`-cocycle of the cochain complex `K` is a coboundary:
`ker (d (p+1) (p+2)) ⊆ im (d p (p+1))`.  For `K = cechComplex U M` this is the statement that
Čech cocycles of the family `U` with coefficients in `M` trivialise. -/
def CechTrivAt (K : CochainComplex AddCommGrpCat.{u} ℕ) (p : ℕ) : Prop :=
  ∀ x : K.X (p + 1), K.d (p + 1) (p + 2) x = 0 → ∃ y : K.X p, K.d p (p + 1) y = x

/-- `CechTrivAll K`: all positive-degree Čech cocycles of `K` trivialise. -/
def CechTrivAll (K : CochainComplex AddCommGrpCat.{u} ℕ) : Prop :=
  ∀ p : ℕ, CechTrivAt K p

/-- `HasCechCohomology M`: every Čech cocycle with coefficients in `M`, for every finite family
of opens, is a coboundary.  This is property `C(M)` of the design in `secSheaf_acyclic.lean`. -/
def HasCechCohomology {X : Scheme.{u}} (M : SheafOfModules X.ringCatSheaf) : Prop :=
  ∀ {ι : Type u} [Finite ι] (U : ι → X.Opens), CechTrivAll (cechComplex U M)

/-- `HasCechCohomologyOnCovers M`: every Čech cocycle with coefficients in `M` for a finite
family of opens *covering* `⊤` is a coboundary.  This is the form of property `C(M)` used in the
induction; unlike `HasCechCohomology` it holds for quasi-coherent sheaves on an affine scheme
(Stacks 00I9 / 30.2.1). -/
def HasCechCohomologyOnCovers {X : Scheme.{u}} (M : SheafOfModules X.ringCatSheaf) : Prop :=
  ∀ {ι : Type u} [Finite ι] (U : ι → X.Opens), iSup U = ⊤ → CechTrivAll (cechComplex U M)

/-- `HasCechCohomology` implies `HasCechCohomologyOnCovers`. -/
theorem HasCechCohomology.onCovers {X : Scheme.{u}} {M : SheafOfModules X.ringCatSheaf}
    (h : HasCechCohomology M) : HasCechCohomologyOnCovers M :=
  fun U _ => h U

end Work.DSF1.Sheaf
