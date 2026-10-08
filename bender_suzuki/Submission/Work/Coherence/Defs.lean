import Submission.Work.Coherence.Inner

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Coherence` — virtual characters, isometries and coherent sets of characters

This is the base module of the coherence area (Feit–Thompson §10 / Peterfalvi §5) of the
odd-order-theorem project.  It fixes the *vocabulary*: the set `Irr G` of irreducible complex
characters of a finite group, the predicates `IsChar`/`IsVChar` (genuine / virtual characters),
the integral lattice `ZSpan S` spanned by a finite set of complex valued functions, its
degree-zero part `ZSpan0 S`, the `Orthonormal` predicate, the notion of an integral linear map
being an *isometry* on such a lattice (this is the property of the Dade isometry and of its
extensions used to define *coherence*), and finally `Coherent` — Feit–Thompson's
Definition 10.1 / Peterfalvi's notion of a `τ`-coherent set of irreducible characters.

## Main definitions

* `Work.Coherence.Irr` — the set of irreducible complex characters of `G`.
* `Work.Coherence.IsChar`, `Work.Coherence.IsVChar` — genuine / virtual characters.
* `Work.Coherence.ZSpan`, `Work.Coherence.ZSpan0` — `ℤ[S]` and `ℤ[S]^0 = {α ∈ ℤ[S] | α 1 = 0}`.
* `Work.Coherence.Orthonormal` — a finite set of pairwise orthonormal class functions.
* `Work.Coherence.IsometryOn`, `Work.Coherence.IsometryOnAll` — integral linear maps preserving
  the character inner product on `ℤ[S]^0` resp. on `ℤ[S]`.
* `Work.Coherence.Coherent` — `S` is `τ`-coherent.

## Conventions

* Characters are *functions* `G → ℂ` (class functions), and `cfInner` is the normalised inner
  product `(1/|G|) ∑_x f x * conj (g x)` of `Submission.Work.CharLib`.
* The group algebra of characters is the integral lattice `ℤ[Irr G]`; membership in it is
  `IsVChar`.
* Everything is universe polymorphic; `[Fintype G]` is used because `cfInner` is a finite sum
  (`[Finite G]` implies `[Fintype G]` noncomputably).
-/

noncomputable section

set_option linter.unusedSectionVars false

open Classical

namespace Work.Coherence

universe u v

variable {G : Type*} {H : Type*}

section SingleGroup

variable [Group G] [Fintype G]

/-- The set of irreducible complex characters of the finite group `G`, i.e. the characters of
the simple finite-dimensional complex representations of `G`. -/
def Irr (G : Type*) [Group G] [Fintype G] : Set (G → ℂ) :=
  {f | ∃ V : FDRep ℂ G, CategoryTheory.Simple V ∧ V.character = f}

@[simp] theorem mem_Irr {f : G → ℂ} :
    f ∈ Irr G ↔ ∃ V : FDRep ℂ G, CategoryTheory.Simple V ∧ V.character = f := Iff.rfl

/-- `f` is a *character* of `G`: a non-negative integral combination of irreducible characters. -/
def IsChar (f : G → ℂ) : Prop := f ∈ AddSubmonoid.closure (Irr G)

/-- `f` is a *virtual character* (a generalised character) of `G`: an integral combination of
irreducible characters.  This is the lattice `ℤ[Irr G]`. -/
def IsVChar (f : G → ℂ) : Prop := f ∈ AddSubgroup.closure (Irr G)

/-- The integral lattice `ℤ[S]` spanned by a finite set of complex valued functions, defined so
that membership is spelled out by a coefficient function. -/
def ZSpan (S : Finset (G → ℂ)) : AddSubgroup (G → ℂ) where
  carrier := {f | ∃ c : S → ℤ, f = ∑ x : S, (c x : ℂ) • (x : G → ℂ)}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro f g ⟨c, rfl⟩ ⟨d, rfl⟩
    refine ⟨c + d, ?_⟩
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun z _ => by
      simp only [Pi.add_apply, Int.cast_add, add_smul]
  neg_mem' := by
    rintro f ⟨c, rfl⟩
    refine ⟨-c, ?_⟩
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun z _ => by
      simp only [Pi.neg_apply, Int.cast_neg, neg_smul]

/-- The degree-zero part `ℤ[S]^0 = {α ∈ ℤ[S] | α 1 = 0}` of the lattice spanned by `S`.
In the Feit–Thompson setting this is the domain of the Dade isometry. -/
def ZSpan0 (S : Finset (G → ℂ)) : AddSubgroup (G → ℂ) :=
  ZSpan S ⊓ AddSubgroup.comap (Pi.evalAddMonoidHom (fun _ : G => ℂ) 1) ⊥

@[simp] theorem mem_zSpan0 {S : Finset (G → ℂ)} {f : G → ℂ} :
    f ∈ ZSpan0 S ↔ f ∈ ZSpan S ∧ f 1 = 0 := Iff.rfl

/-- A finite set of complex valued functions is *orthonormal* if its elements are pairwise
orthonormal for the character inner product. -/
def Orthonormal (S : Finset (G → ℂ)) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, cfInner x y = if x = y then 1 else 0

/-- A finite set of class functions on a subgroup, all of the same "degree" `χ 1`. -/
def SameDegree (S : Finset (G → ℂ)) (d : ℂ) : Prop := ∀ x ∈ S, x 1 = d

end SingleGroup

section Isometry

variable [Group H] [Fintype H] [Group G] [Fintype G]

/-- `τ : ℤ[H → ℂ] → ℤ[G → ℂ]` is an *isometry on* `ℤ[S]^0`: it preserves the character inner
product on the degree-zero part of the lattice spanned by `S`.

This is the defining property of the Dade isometry, and the property required of the extension
`τ'` in the definition of coherence (restricted to the degree-zero part). -/
structure IsometryOn (S : Finset (H → ℂ)) (τ : (H → ℂ) →ₗ[ℤ] (G → ℂ)) : Prop where
  inner_eq : ∀ α ∈ ZSpan0 S, ∀ β ∈ ZSpan0 S, cfInner (τ α) (τ β) = cfInner α β

/-- `τ` is an *isometry on the full lattice* `ℤ[S]`: it preserves the character inner product
on all of `ℤ[S]`.  This is the property required of the extension `τ'` in Definition 10.1(ii)
of Feit–Thompson. -/
structure IsometryOnAll (S : Finset (H → ℂ)) (τ : (H → ℂ) →ₗ[ℤ] (G → ℂ)) : Prop where
  inner_eq : ∀ α ∈ ZSpan S, ∀ β ∈ ZSpan S, cfInner (τ α) (τ β) = cfInner α β

/-- Feit–Thompson Definition 10.1 / Peterfalvi: a finite set `S` of (class) functions on a
subgroup `H` is *coherent* for `τ` if `τ` can be extended from `ℤ[S]^0` to an isometry of the
whole lattice `ℤ[S]` whose values on `S` are virtual characters of `G`.

The extension is not required to be an isometry on `ℤ[S]^0` only, but on all of `ℤ[S]`
(Feit–Thompson, Definition 10.1(ii): "extend `τ` to a linear isometry mapping `𝔛(𝔖)` into the
set of generalized characters of `X`"). -/
def Coherent (S : Finset (H → ℂ)) (τ : (H → ℂ) →ₗ[ℤ] (G → ℂ)) : Prop :=
  ∃ τ' : (H → ℂ) →ₗ[ℤ] (G → ℂ),
    (∀ α ∈ ZSpan0 S, τ' α = τ α) ∧ IsometryOnAll S τ' ∧ ∀ χ ∈ S, IsVChar (τ' χ)

end Isometry

end Work.Coherence
