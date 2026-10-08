import Mathlib
import Submission.Work.Frobenius.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The character-theoretic layer for area A8

This module provides the minimal complex-character-theory interface used by the
Frobenius-group arguments: irreducible characters (as a set of functions `G → ℂ`),
the trace pairing `charPair`, virtual characters, and the induced class function
`indFun`.

The pairing we use is the *bilinear* trace pairing
`charPair f g = |G|⁻¹ * ∑ x, f x * g x⁻¹`,
rather than the Hermitian pairing `|G|⁻¹ * ∑ x, f x * conj (g x)`.  On virtual
characters the two agree, and the bilinear form has the advantage that no complex
conjugation is needed for orthonormality, Frobenius reciprocity or the norm-one
argument.

Statements in this layer assume `[Fintype G]` (sums over `G`); consumers that work
with `[Finite G]` can locally use `Fintype.ofFinite`.
-/

@[expose] public section

noncomputable section

open Classical

open scoped Pointwise

namespace Work.Frobenius

variable {G : Type*} [Group G]

/-- A finite-dimensional irreducible complex representation of `G`, bundled so that a
character can be chosen from membership in `Irr`. -/
structure IrrRep (G : Type*) [Group G] where
  /-- the underlying vector space -/
  V : Type
  [addCommGroup : AddCommGroup V]
  [module : Module ℂ V]
  [finiteDimensional : FiniteDimensional ℂ V]
  /-- the representation -/
  ρ : Representation ℂ G V
  /-- the representation is irreducible -/
  irred : Representation.IsIrreducible ρ

attribute [instance] IrrRep.addCommGroup IrrRep.module IrrRep.finiteDimensional

/-- The set of irreducible complex characters of `G`. -/
def Irr (G : Type*) [Group G] : Set (G → ℂ) :=
  Set.range fun d : IrrRep G => d.ρ.character

theorem mem_Irr_iff {χ : G → ℂ} :
    χ ∈ Irr G ↔ ∃ d : IrrRep G, d.ρ.character = χ := Iff.rfl

/-- `f` is a class function on `G`. -/
def IsClassFun (f : G → ℂ) : Prop := ∀ g h : G, f (h * g * h⁻¹) = f g

/-- Restriction of a function `G → ℂ` to a subgroup. -/
def resFun (H : Subgroup G) (f : G → ℂ) : H → ℂ := fun h => f h

/-- The class function induced from a function on a subgroup, in the classical trace
form `indFun H f g = |H|⁻¹ ∑_{x : x g x⁻¹ ∈ H} f (x g x⁻¹)`. -/
noncomputable def indFun [Fintype G] (H : Subgroup G) (f : H → ℂ) : G → ℂ :=
  fun g => (Nat.card H : ℂ)⁻¹ *
    ∑ x : G, if hx : x * g * x⁻¹ ∈ H then f ⟨x * g * x⁻¹, hx⟩ else 0

section Pair

variable [Fintype G]

/-- The trace pairing on complex functions on a finite group,
`charPair f g = |G|⁻¹ * ∑ x, f x * g x⁻¹`. -/
noncomputable def charPair (f g : G → ℂ) : ℂ :=
  (Nat.card G : ℂ)⁻¹ * ∑ x, f x * g x⁻¹

@[simp]
theorem charPair_apply (f g : G → ℂ) :
    charPair f g = (Nat.card G : ℂ)⁻¹ * ∑ x, f x * g x⁻¹ := rfl

omit [Fintype G] in
/-- Irreducible characters are class functions. -/
theorem irr_isClassFun {χ : G → ℂ} (hχ : χ ∈ Irr G) : IsClassFun χ := by
  obtain ⟨d, hd⟩ := hχ
  rw [← hd]
  exact fun g h => Representation.char_conj d.ρ g h

omit [Fintype G] in
theorem IrrRep.character_mem (d : IrrRep G) : d.ρ.character ∈ Irr G := ⟨d, rfl⟩

end Pair

/-- `f` is a virtual character of `G`: an integral linear combination of irreducible
characters. -/
def IsVChar (f : G → ℂ) : Prop := f ∈ AddSubgroup.closure (Irr G)

/-- `f` is a character of `G`: a nonnegative integral combination of irreducible
characters. -/
def IsChar (f : G → ℂ) : Prop := f ∈ AddSubmonoid.closure (Irr G)

end Work.Frobenius
