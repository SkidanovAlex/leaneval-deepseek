import Mathlib
import ChallengeDeps
import Submission.Blueprint.Interfaces

/-!
# AREA ANALYTIC — homotopy invariance of `ℤ[-]` up to solid-equivalence

This is the base module of the ANALYTIC subproject (`Work.ANALYTIC`).  It fixes the objects and
conventions that every other module of this area builds on.  The mathematics is REFS/03 (null
sequences) and REFS/04 (Čech argument); the paper sources are Clausen–Scholze, *Lectures on
Condensed Mathematics* (arXiv 2605.03658) and I. Rodríguez Camargo, *Notes on Solid Geometry*
(arXiv 2603.03012), §3.2–3.3.

## Conventions fixed here

* `Z` is the constant (discrete) light condensed abelian group `ℤ`; `prodZ = ∏_ℕ ℤ`.
* `box N` is the light profinite space of integer sequences bounded by `N` (a countable product of
  finite discrete spaces).
* `P` and `oneMinusShift` are the objects of `ChallengeDeps`:
  `P = ℤ[ℕ∪{∞}]/ℤ[∞]` and `1 - S` the endomorphism of `P` induced by the shift of `ℕ∪{∞}`.
* `tensorOneMinusShift X : P ⊗ X ⟶ P ⊗ X` is `(1 - S) ⊗ id_X`.
* `SolidNull A` means: `Hom_D(A, ι N) = 0` for every complex `N` of solid objects, i.e. every
  morphism `A ⟶ derivedInclusion.obj N` in `D(LightCondAb)` is zero.
* `SolidEquiv f` (defined in `Submission.Blueprint.Interfaces`) means: for every `N : DSolid`,
  precomposition with `f` on `Hom(-, derivedInclusion.obj N)` is a bijection.

The two analytic inputs used by the whole area are recorded as `Prop`s here so that they can be
proved separately and used as hypotheses: `BoundedSolidEquiv` (REFS/03 §2, area lemma AN1) and
`PreSolid` (the F7 input of REFS/01, F6–F7, an ATOM-area lemma).  Every statement of this area is
stated with these two as hypotheses whenever it needs them.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed

noncomputable section

namespace Work.ANALYTIC

open _root_.LightCondensed _root_.LightCondensed.Solid

universe u

/-! ## The constant object `ℤ`, countable products, boxes -/

/-- The light condensed abelian group `ℤ` (the discrete/constant sheaf at `ℤ`). -/
abbrev Z : LightCondAb := (LightCondensed.discrete (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)

/-- The countable product `∏_{n : ℕ} ℤ`. -/
abbrev prodZ : LightCondAb := ∏ᶜ (fun _ : ℕ => Z)

/-- The light profinite space `{x : ℕ → ℤ // ∀ n, |x n| ≤ N}` of sequences of integers bounded
by `N`, realised as a countable product of finite discrete spaces. -/
def box (N : ℕ) : LightProfinite :=
  ∏ᶜ (fun _ : ℕ => FintypeCat.toLightProfinite.obj (FintypeCat.of (Fin (2 * N + 1))))

/-! ## Null-sequence data associated to `P` -/

/-- `(1 - S) ⊗ id_X`, the endomorphism of `P ⊗ X` induced by `1 - S` on the first factor. -/
def tensorOneMinusShift (X : LightCondAb) : P ⊗ X ⟶ P ⊗ X := (tensorRight X).map oneMinusShift

/-! ## Vanishing and equivalence predicates -/

/-- `A` is *solid-null*: every morphism in `D(LightCondAb)` from `A` into the derived inclusion of
a complex of solid objects is zero. -/
def SolidNull (A : DLightCondAb) : Prop :=
  ∀ N : DSolid, Subsingleton (A ⟶ derivedInclusion.obj N)

/-- **The F7 input (REFS/01, F6–F7).**  `PreSolid X` says that the endomorphism `(1 - S) ⊗ id_X`
of `P ⊗ X` induces a bijection on `Hom_D(P ⊗ X, ι N)` for every complex `N` of solid objects.
This is the single analytic input that drives every null-sequence trick of REFS/03; for area ATOM
it is the statement that `ℤ[S]` is solid-cofibrant for free objects. -/
def PreSolid (X : LightCondAb) : Prop :=
  Submission.Blueprint.SolidEquiv ((DerivedCategory.singleFunctor LightCondAb 0).map (tensorOneMinusShift X))

/-- **The AN1 statement (REFS/03 §2).**  The null sequence `c : P ⟶ ∏^bnd ℤ`, `e_n ↦ δ_n`,
is a solid-equivalence.  It is stated here as an abstract predicate so that the rest of the area
can be developed before the object `∏^bnd ℤ` is constructed. -/
def IsBoundedSeqSolidEquiv (Bd : LightCondAb) (c : P ⟶ Bd) : Prop :=
  Submission.Blueprint.SolidEquiv ((DerivedCategory.singleFunctor LightCondAb 0).map c)

end Work.ANALYTIC
