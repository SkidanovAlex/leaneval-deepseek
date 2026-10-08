import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.CharLib`: complex character theory of finite groups

This is the base module of the character-theory area used by the Gorenstein–Walter project
(and in particular by the Bender–Glauberman ordinary-character arguments).

It contains the definitions only:

* `Work.CharLib.CharTable` — a character table of a finite group `G` (index type `ι` carrying
  exactly the distinct complex characters of the simple finite-dimensional complex representations),
  with the fields `irr`, `complete`, `inj`;
* `Work.CharLib.cfInner` — the normalised inner product `(1/|G|) ∑_x f x * conj (g x)` on complex
  functions on `G`, linear in the first and conjugate-linear in the second argument;
* `Work.CharLib.IsClassFun` — the predicate "is a class function";
* `Work.CharLib.indFun` — the induced class function `Ind_H^G f` of a function `f` on a subgroup `H`,
  written in the classical trace form `|H|⁻¹ ∑_{x : x g x⁻¹ ∈ H} f (x g x⁻¹)`;
* `Work.CharLib.classSumElem` — the class sum of a conjugacy class, as an element of `ℂ[G]`.

The basic API for `cfInner` and `IsClassFun` (bilinearity, conjugate symmetry) lives in
`Submission.Work.CharLib.CFun`.
-/

noncomputable section

open Classical

namespace Work.CharLib

/-- A character table of a finite group `G`.  The index type `ι` indexes the distinct complex
characters of the simple finite dimensional complex representations of `G`: `irr` says every `χ i`
is such a character, `complete` says every simple representation occurs, and `inj` says the `χ i`
are pairwise distinct. -/
structure CharTable (G : Type) [Group G] [Fintype G] where
  ι : Type
  [instFintype : Fintype ι]
  [instDecEq : DecidableEq ι]
  χ : ι → G → ℂ
  irr : ∀ i, ∃ V : FDRep ℂ G, CategoryTheory.Simple V ∧ V.character = χ i
  complete : ∀ V : FDRep ℂ G, CategoryTheory.Simple V → ∃ i, V.character = χ i
  inj : Function.Injective χ

attribute [instance] CharTable.instFintype CharTable.instDecEq

variable {G : Type} [Group G] [Fintype G]

/-- The normalised inner product of two complex valued functions on the finite group `G`,
`(1/|G|) ∑_x f x * conj (g x)`.  It is linear in the first argument and conjugate linear in
the second. -/
noncomputable def cfInner (f g : G → ℂ) : ℂ :=
  (Fintype.card G : ℂ)⁻¹ * ∑ x, f x * starRingEnd ℂ (g x)

/-- `f` is a class function on `G`. -/
def IsClassFun (f : G → ℂ) : Prop := ∀ g h : G, f (h * g * h⁻¹) = f g

/-- The induced class function of a function on a subgroup, in the classical trace form
`Ind_H^G f g = |H|⁻¹ ∑_{x : x g x⁻¹ ∈ H} f (x g x⁻¹)`. -/
noncomputable def indFun (H : Subgroup G) [DecidablePred (· ∈ H)] (f : H → ℂ) : G → ℂ :=
  fun g => (Nat.card H : ℂ)⁻¹ *
    ∑ x : G, if hx : x * g * x⁻¹ ∈ H then f ⟨x * g * x⁻¹, hx⟩ else 0

/-- The class sum of the conjugacy class of `g`, as an element of the group algebra `ℂ[G]`. -/
noncomputable def classSumElem (g : G) : MonoidAlgebra ℂ G :=
  ∑ y ∈ Finset.univ.filter (fun y : G => IsConj g y), MonoidAlgebra.single y (1 : ℂ)

end Work.CharLib
