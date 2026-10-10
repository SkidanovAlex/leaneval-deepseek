import Mathlib.Algebra.Torsor.Defs
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Submission.NK.GlobalCFTdeep.Herbrand.Mul
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Herbrand's lemma for a submodule of finite index

If `0 → X₁ → X₂ → X₃ → 0` is a short exact sequence of `ℤ[G]`-modules with `G` finite cyclic and
`X₃` finite, then `X₁` and `X₂` have the same Herbrand quotient:

  `h(X₂) = m ↔ h(X₁) = m`.

This is the "invariance under a finite-index extension" step of Milne's Lemma 3.4 (and of
Milne II.3.9): `h` is multiplicative along the exact sequence, `h(X₃) = 1` because `X₃` is finite
(Herbrand's lemma, `herbrandEq_one_of_finite`), and the `hOne`-terms cancel.  It is the engine of
the comparison of two `G`-stable lattices in the same `ℝ[G]`-space (Milne Lemma 3.5), which is the
abstract half of Proposition 3.1.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open CategoryTheory

noncomputable section

namespace NK.GlobalCFTdeep

/-- Finiteness of the two Tate cohomology groups of a `ℤ[G]`-module `M`, packaged as a `Prop` so
that it can be passed around as a hypothesis without instance-synthesis friction. -/
structure FiniteTate {G : Type} [Group G] [Fintype G] (M : Rep ℤ G) : Prop where
  /-- `Ĥ⁰(G, M)` is finite. -/
  zero : Finite ↥(tateCohomology M 0)
  /-- `Ĥ¹(G, M)` is finite. -/
  one : Finite ↥(tateCohomology M 1)

variable {G : Type} [CommGroup G] [Fintype G] [IsCyclic G]

/-- **Herbrand's lemma for a finite-index submodule**, in the cross-multiplied form: along a short
exact sequence `0 → X₁ → X₂ → X₃ → 0` with `X₃` finite, `X₁` and `X₂` have the same Herbrand
quotient. -/
theorem herbrandEq_iff_of_shortExact_finite (S : ShortComplex (Rep ℤ G)) (hS : S.ShortExact)
    [Finite S.X₃.V] (m : ℕ)
    [Finite ↥(tateCohomology S.X₁ 0)] [Finite ↥(tateCohomology S.X₁ 1)]
    [Finite ↥(tateCohomology S.X₂ 0)] [Finite ↥(tateCohomology S.X₂ 1)]
    [Finite ↥(tateCohomology S.X₃ 0)] [Finite ↥(tateCohomology S.X₃ 1)] :
    HerbrandEq S.X₂ m ↔ HerbrandEq S.X₁ m := by
  have h3 : HerbrandEq S.X₃ 1 := herbrandEq_one_of_finite S.X₃
  have hMult := hZero_mul_hOne_of_shortExact S hS
  constructor
  · -- `h(X₂) = m` implies `h(X₁) = m`: multiply by `h(X₃) = 1` and cancel.
    intro h2
    simp only [HerbrandEq] at h2 h3 hMult ⊢
    have hpos : 0 < hOne S.X₃ * hOne S.X₂ :=
      Nat.mul_pos Nat.card_pos Nat.card_pos
    have key : hZero S.X₁ * (hOne S.X₃ * hOne S.X₂) =
        (m * hOne S.X₁) * (hOne S.X₃ * hOne S.X₂) := by
      have h := hMult
      rw [h2, h3, one_mul] at h
      rw [show (m * hOne S.X₂) * hOne S.X₁ * hOne S.X₃
          = m * hOne S.X₁ * (hOne S.X₃ * hOne S.X₂) from by ring] at h
      rw [show hZero S.X₁ * hOne S.X₃ * hOne S.X₂
          = hZero S.X₁ * (hOne S.X₃ * hOne S.X₂) from by ring] at h
      rw [← h]
    exact Nat.eq_of_mul_eq_mul_right hpos key
  · -- the converse: multiplicativity with `h(X₃) = 1`.
    intro h1
    have h := herbrandEq_of_shortExact S hS m 1 h1 h3
    simpa using h

end NK.GlobalCFTdeep
