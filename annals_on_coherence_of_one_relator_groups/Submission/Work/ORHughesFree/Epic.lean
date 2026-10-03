/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Epic ring homomorphisms and envelopes of rank functions

Following [JZLA20, §2.3], a ring homomorphism `φ : R →+* S` is *epic* if it is right cancellable.
We record the basic theory: the pullback `φ♯ rk` of a Sylvester rank function along a ring
homomorphism, faithful rank functions and their kernel ideal, and (epic) envelopes.

The tensor-product characterisation of epicity ([JZLA20, Proposition 2.3])
`φ epic ↔ ∀ x : S, x ⊗ₜ 1 = 1 ⊗ₜ x`, which is stated in terms of `S ⊗[R] S`, is recorded in
`Work.ORHughesFree.EpicTensor`.
-/
import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.StarRegular

set_option autoImplicit false

universe u

namespace Work.ORHughesFree

variable {R S Q : Type u}

/-- A ring homomorphism is **epic** if it is right cancellable ([JZLA20, §2.3]). -/
def IsEpic [Ring R] [Ring S] (f : R →+* S) : Prop :=
  ∀ ⦃Q : Type u⦄ [Ring Q] (g h : S →+* Q), g.comp f = h.comp f → g = h

theorem isEpic_iff_comp_injective [Ring R] [Ring S] (f : R →+* S) :
    IsEpic f ↔ ∀ ⦃Q : Type u⦄ [Ring Q], Function.Injective
      (fun g : S →+* Q => g.comp f) :=
  Iff.rfl

theorem IsEpic.comp [Ring R] [Ring S] [Ring Q] {f : R →+* S} {g : S →+* Q}
    (hf : IsEpic f) (hg : IsEpic g) : IsEpic (g.comp f) := by
  intro T _ p q hpq
  exact hg p q (hf _ _ (by rw [RingHom.comp_assoc, RingHom.comp_assoc, hpq]))

theorem IsEpic.of_comp [Ring R] [Ring S] [Ring Q] {f : R →+* S} {g : S →+* Q}
    (h : IsEpic (g.comp f)) : IsEpic g := by
  intro T _ p q hpq
  exact h p q (by rw [← RingHom.comp_assoc, ← RingHom.comp_assoc, hpq])

namespace SylvesterRank

/-- A Sylvester rank function is **faithful** if it does not vanish on nonzero elements
([JZLA20, §2.4]). -/
def IsFaithful [Ring R] (rk : SylvesterRank R) : Prop :=
  ∀ a : R, rk.rk 1 1 (oneByOne a) = 0 → a = 0

/-- Pullback of a Sylvester rank function along a ring homomorphism ([JZLA20, §2.4]). -/
def pullback [Ring R] [Ring S] (φ : R →+* S) (rk : SylvesterRank S) : SylvesterRank R where
  rk n m A := rk.rk n m (A.map φ)
  rk_nonneg n m A := rk.rk_nonneg n m _
  rk_zero n m := by
    rw [Matrix.map_zero φ (map_zero φ)]
    exact rk.rk_zero n m
  rk_one := by
    have h : (1 : Matrix (Fin 1) (Fin 1) R).map φ = 1 := by
      ext i j
      fin_cases i
      fin_cases j
      simp [Matrix.map_apply]
    rw [h]
    exact rk.rk_one
  rk_mul_le_left := by
    intro n m k A B
    rw [Matrix.map_mul]
    exact rk.rk_mul_le_left (A.map φ) (B.map φ)
  rk_mul_le_right := by
    intro n m k A B
    rw [Matrix.map_mul]
    exact rk.rk_mul_le_right (A.map φ) (B.map φ)
  rk_blockDiag := by
    intro n m p q A B
    rw [blockDiagFin_map, rk.rk_blockDiag]
  rk_blockUpper := by
    intro n m p q A B C
    rw [blockUpperFin_map]
    exact rk.rk_blockUpper (A.map φ) (B.map φ) (C.map φ)

end SylvesterRank

/-- `(S, rk, φ)` is an **envelope** of the pulled back rank function `φ♯ rk` if `rk` is faithful
on `S` ([JZLA20, §2.4]). -/
structure IsEnvelope {R S : Type u} [Ring R] [Ring S] (φ : R →+* S)
    (rk : SylvesterRank S) : Prop where
  /-- The rank function is faithful. -/
  faithful : rk.IsFaithful

/-- `(S, rk, φ)` is a **regular envelope** if in addition `S` is von Neumann regular. -/
structure IsRegularEnvelope {R S : Type u} [Ring R] [Ring S] [VonNeumannRegularRing S]
    (φ : R →+* S) (rk : SylvesterRank S) : Prop extends IsEnvelope φ rk

/-- An **epic division `R`-ring**: a division ring `D` together with an epic ring homomorphism
`φ : R →+* D` ([JZLA20, §2.4]). -/
structure IsEpicDivisionRing (R D : Type u) [Ring R] [DivisionRing D]
    (φ : R →+* D) : Prop where
  /-- `φ` is epic. -/
  epic : IsEpic φ

/-- An **epic ∗-regular `R`-ring**: a ∗-regular ring `U` together with an epic ∗-homomorphism
`φ : R →+* U` ([JZLA20, §2.4]). -/
structure IsEpicStarRegularRing (R U : Type u) [Ring R] [StarRing R] [Ring U] [StarRing U]
    (φ : R →+* U) : Prop where
  /-- `φ` is epic. -/
  epic : IsEpic φ
  /-- `φ` is a ∗-homomorphism. -/
  map_star : ∀ x : R, φ (star x) = star (φ x)

end Work.ORHughesFree
