/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.ORLinnell
-/
import Mathlib.RingTheory.OreLocalization.Ring
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.FiniteLength
import Mathlib.Order.SupIndep
import Mathlib.Algebra.SkewMonoidAlgebra.Basic

/-!
# Division closed subrings, division closures, and classical rings of quotients

This file sets up the ring-theoretic vocabulary used in the formalisation of the
Jaikin-Zapirain--Linton theorem on the coherence of one-relator groups (Annals 2025).

The main objects are

* `IsDivisionClosed A`: the subring `A` of an ambient ring `S` is closed under inverses in `S`
  of its own elements (a "division closed" subring);
* `divisionClosure R`: the division closure of `R` in `S`, i.e. the smallest division closed
  subring of `S` containing `R`.  This is `D_{K[G]} ⊆ U(G)` of the paper, for `R = K[G]`;
* `IsClassicalQuotient R Q`: the elementary statement that `Q` is the classical (Ore) ring of
  quotients of `R` inside a common ambient ring.  Linnell's lemma for `H = N ⋊ ⟨t⟩` asserts
  that `D(H)` is the classical ring of quotients of the twisted Laurent polynomial ring
  `D(N)[t^{±1}; τ]`.
-/

/-- A subring `A` of an ambient ring `S` is *division closed* if it contains the inverse in `S`
of every element of `A` which happens to be invertible in `S`.  We use the one sided
formulation: `y ∈ A` whenever `x ∈ A` and `x * y = 1` for some `y : S`.  In a Dedekind finite
ring (in particular in `U(G)`) this is equivalent to the two sided formulation. -/
def IsDivisionClosed {S : Type*} [Ring S] (A : Subring S) : Prop :=
  ∀ x ∈ A, ∀ y : S, x * y = 1 → y ∈ A

namespace IsDivisionClosed

variable {S : Type*} [Ring S] {A B : Subring S}

theorem top : IsDivisionClosed (⊤ : Subring S) := fun _ _ y _ => Subring.mem_top y

/-- The intersection of a family of division closed subrings is division closed. -/
theorem sInf {A : Set (Subring S)} (hA : ∀ a ∈ A, IsDivisionClosed a) :
    IsDivisionClosed (sInf A) := by
  intro x hx y hxy
  rw [Subring.mem_sInf] at hx ⊢
  exact fun p hp => hA p hp x (hx p hp) y hxy

end IsDivisionClosed

/-- The *division closure* of a subring `R` of an ambient ring `S`: the smallest subring of `S`
containing `R` which is division closed in `S`, i.e. closed under inverses in `S`. -/
def divisionClosure {S : Type*} [Ring S] (R : Subring S) : Subring S :=
  sInf {A : Subring S | R ≤ A ∧ IsDivisionClosed A}

/-- The division closure of a *set* in a ring `S`. -/
def divisionClosureOf {S : Type*} [Ring S] (T : Set S) : Subring S :=
  divisionClosure (Subring.closure T)

variable {S : Type*} [Ring S]

theorem le_divisionClosure (R : Subring S) : R ≤ divisionClosure R := by
  intro x hx
  rw [divisionClosure, Subring.mem_sInf]
  rintro A ⟨hRA, _⟩
  exact hRA hx

theorem mem_divisionClosure_iff {R : Subring S} {x : S} :
    x ∈ divisionClosure R ↔ ∀ A : Subring S, R ≤ A → IsDivisionClosed A → x ∈ A := by
  rw [divisionClosure, Subring.mem_sInf]
  constructor
  · rintro h A hRA hA
    exact h A ⟨hRA, hA⟩
  · intro h A hA
    exact h A hA.1 hA.2

theorem isDivisionClosed_divisionClosure (R : Subring S) :
    IsDivisionClosed (divisionClosure R) := by
  intro x hx y hxy
  rw [mem_divisionClosure_iff] at hx ⊢
  intro A hRA hA
  exact hA x (hx A hRA hA) y hxy

theorem divisionClosure_le_iff {R A : Subring S} (hA : IsDivisionClosed A) :
    divisionClosure R ≤ A ↔ R ≤ A := by
  refine ⟨fun h => (le_divisionClosure R).trans h, fun h => ?_⟩
  rw [divisionClosure]
  exact sInf_le ⟨h, hA⟩

theorem divisionClosure_eq_self {A : Subring S} (hA : IsDivisionClosed A) :
    divisionClosure A = A :=
  le_antisymm ((divisionClosure_le_iff hA).mpr le_rfl) (le_divisionClosure A)

theorem divisionClosure_idempotent (R : Subring S) :
    divisionClosure (divisionClosure R) = divisionClosure R :=
  divisionClosure_eq_self (isDivisionClosed_divisionClosure R)

theorem divisionClosure_mono {R R' : Subring S} (h : R ≤ R') :
    divisionClosure R ≤ divisionClosure R' := by
  rw [divisionClosure_le_iff (isDivisionClosed_divisionClosure R')]
  exact h.trans (le_divisionClosure R')

theorem divisionClosure_top : divisionClosure (⊤ : Subring S) = ⊤ :=
  divisionClosure_eq_self IsDivisionClosed.top

theorem divisionClosureOf_le_iff {T : Set S} {A : Subring S} (hA : IsDivisionClosed A) :
    divisionClosureOf T ≤ A ↔ T ⊆ A := by
  rw [divisionClosureOf, divisionClosure_le_iff hA, Subring.closure_le]
