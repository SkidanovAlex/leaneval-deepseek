/-
AREA RESOL — functorial solid-cofibrant resolutions (foundations).

This file sets up the vocabulary of the area.  Everything else in `Submission/Work/RESOL/`
builds on the definitions below.

Conventions (identical to `Submission.Blueprint.Interfaces`):
* all cochain complexes are indexed cohomologically, by `ComplexShape.up ℤ`;
* `KCat` = `K(LightCondAb)` is the homotopy category of cochain complexes;
* `DCat` = `D(LightCondAb)` is its derived category;
* `ιC` is the degreewise inclusion of complexes of solid objects;
* `SolidCofibrant` (from the blueprint) is stated for a complex `K`, and only depends on
  its image in `K(LightCondAb)`.  We provide `SolidCofibrantH` (the same property stated
  on the homotopy category) and the (definitional) comparison.
-/
import Submission.Blueprint.Interfaces

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

namespace Work.RESOL

/-! ## Basic abbreviations -/

/-- The category of cochain complexes of light condensed abelian groups. -/
abbrev Cpx : Type 1 := CochainComplex LightCondAb ℤ

/-- The homotopy category `K(LightCondAb)` of cochain complexes. -/
abbrev KCat : Type 1 := HomotopyCategory LightCondAb (ComplexShape.up ℤ)

/-- The derived category `D(LightCondAb)`. -/
abbrev DCat : Type 1 := DerivedCategory LightCondAb

/-- The degreewise inclusion of complexes of solid objects into cochain complexes. -/
abbrev ιC : CochainComplex Solid ℤ ⥤ Cpx := Submission.Blueprint.ιC

/-- The class of solid-cofibrant complexes, stated on the homotopy category. -/
def SolidCofibrantH (K : KCat) : Prop :=
  ∀ N : CochainComplex Solid ℤ,
    Function.Bijective (fun f : K ⟶ Submission.Blueprint.hq (ιC.obj N) =>
      DerivedCategory.Qh.map f)

/-- `SolidCofibrant K` is the same property as `SolidCofibrantH (hq K)`. -/
theorem solidCofibrant_iff (K : Cpx) :
    Submission.Blueprint.SolidCofibrant K ↔
      SolidCofibrantH (Submission.Blueprint.hq K) :=
  Iff.rfl

/-- A complex which is K-projective is solid-cofibrant.  This is the second conjunct of
`Submission.Blueprint.ResolutionProp`. -/
theorem solidCofibrant_of_isKProjective (K : Cpx) [K.IsKProjective] :
    Submission.Blueprint.SolidCofibrant K :=
  fun N => CochainComplex.IsKProjective.Qh_map_bijective K (Submission.Blueprint.hq (ιC.obj N))

/-! ## Atomic sums -/

/-- `M` is a *small atomic sum*: it is a small coproduct of free light condensed abelian
groups `ℤ[S]` on light profinite sets `S`.  The definition is phrased with an explicit
colimit cocone so that it never triggers coproduct instance search. -/
def IsAtomicSum (M : LightCondAb) : Prop :=
  ∃ (J : Type) (S : J → LightProfinite.{0})
    (c : Cofan fun j => (free ℤ).obj (S j).toCondensed),
    Nonempty (IsColimit c) ∧ Nonempty (M ≅ c.pt)

/-- A complex whose terms are small atomic sums is a *complex of atoms*. -/
def HasAtomicTerms (K : Cpx) : Prop :=
  ∀ n : ℤ, IsAtomicSum (K.X n)

/-- `K` is *bounded above* if its terms vanish in all large enough degrees. -/
def IsBoundedAbove (K : Cpx) : Prop :=
  ∃ N : ℤ, ∀ n : ℤ, N < n → IsZero (K.X n)

/-- `K` is *bounded below* if its terms vanish in all small enough degrees. -/
def IsBoundedBelow (K : Cpx) : Prop :=
  ∃ N : ℤ, ∀ n : ℤ, n < N → IsZero (K.X n)

/-- Atomic sums are closed under isomorphism. -/
theorem isAtomicSum_of_iso {M M' : LightCondAb} (e : M ≅ M') (h : IsAtomicSum M) :
    IsAtomicSum M' := by
  obtain ⟨J, S, c, hc, ⟨eM⟩⟩ := h
  exact ⟨J, S, c, hc, ⟨e.symm ≪≫ eM⟩⟩

/-! ## The two halves of `ResolutionProp` -/

/-- There exists a functorial solid-cofibrant resolution of every cochain complex: this is the
first conjunct of `Submission.Blueprint.ResolutionProp`. -/
def HasFunctorialResolution : Prop :=
  ∃ (ρ : Cpx ⥤ Cpx) (ε : ρ ⟶ 𝟭 Cpx),
    (∀ K, Submission.Blueprint.SolidCofibrant (ρ.obj K)) ∧ (∀ K, QuasiIso (ε.app K))

/-- There is a functorial epimorphism onto every light condensed abelian group from a small
atomic sum (the "atom cover" used to build functorial resolutions). -/
def HasAtomicCover : Prop :=
  ∃ (F : LightCondAb ⥤ LightCondAb) (π : F ⟶ 𝟭 LightCondAb),
    (∀ M, Epi (π.app M)) ∧ (∀ M, IsAtomicSum (F.obj M))

/-- Like `HasAtomicCover`, but the cover functor is required to preserve zero morphisms.  This is
needed to build the double complex of degreewise resolutions: the square
`R (d) ≫ R (d) = R (d ≫ d) = R 0 = 0` must hold.  The cover of `HasAtomicCover` (indexed by *all*
sections, including `0`) does not have this property, so the construction uses the *reduced* cover
indexed by the nonzero sections. -/
def HasAtomicCover₀ : Prop :=
  ∃ (F : LightCondAb ⥤ LightCondAb) (π : F ⟶ 𝟭 LightCondAb),
    F.PreservesZeroMorphisms ∧ (∀ M, Epi (π.app M)) ∧ (∀ M, IsAtomicSum (F.obj M))

/-! ## Closure properties of solid-cofibrant complexes

These are the "B4" closure properties of REFS/02 §2.  They are bundled here so that the
construction of functorial resolutions (`Main.lean`) can be stated as a theorem *given* the
closure properties, while each closure property is proved separately. -/

/-- The closure properties of the class of solid-cofibrant complexes used to build functorial
solid-cofibrant resolutions. (These are stated with all coproduct instances explicit, so that
no instance search over complexes is needed to state them.) -/
structure CofibrantClosure : Prop where
  /-- isomorphism invariance in `K(LightCondAb)` -/
  iso : ∀ {K L : KCat} (e : K ≅ L), SolidCofibrantH K → SolidCofibrantH L
  /-- invariance under shifts -/
  shift : ∀ (n : ℤ) (K : KCat), SolidCofibrantH K →
    SolidCofibrantH ((shiftFunctor KCat n).obj K)
  /-- mapping cones: in a distinguished triangle whose first two objects have all their shifts
  solid-cofibrant, the third object is solid-cofibrant -/
  cone : ∀ (T : CategoryTheory.Pretriangulated.Triangle KCat),
    T ∈ CategoryTheory.Pretriangulated.distinguishedTriangles →
    (∀ n : ℤ, SolidCofibrantH ((shiftFunctor KCat n).obj T.obj₁)) →
    (∀ n : ℤ, SolidCofibrantH ((shiftFunctor KCat n).obj T.obj₂)) →
    SolidCofibrantH T.obj₃
  /-- small coproducts -/
  sigma : ∀ (J : Type) (K : J → Cpx) [HasCoproduct K],
    (∀ j, Submission.Blueprint.SolidCofibrant (K j)) →
    Submission.Blueprint.SolidCofibrant (∐ K)

end Work.RESOL
