/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.NK.GlobalCFTdeep.Herbrand.Reduction
import Submission.NK.GlobalCFTdeep.Herbrand.hZero_eq_hOne_of_finite
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Multiplicativity of the Herbrand quotient in the cross-multiplied form

`Herbrand/Reduction.lean` proves the Herbrand multiplicativity identity along a short exact sequence
of `ℤ[G]`-modules with `G` finite cyclic (Milne, *CFT*, Proposition 3.6 with Lemma 3.7):

  `hZero S.X₂ * hOne S.X₁ * hOne S.X₃ = hZero S.X₁ * hZero S.X₃ * hOne S.X₂`.

Here the two consequences used by the `S`-idèles/`S`-units computations are recorded:

* `herbrandEq_of_mult` — the *arithmetic* consequence: if `h(S.X₁) = m`, `h(S.X₃) = m'` and the
  middle terms `Ĥ¹` are non-zero, then `h(S.X₂) = m · m'`.  This is the form in which the finitely
  many orbits of Milne's Proposition 2.7 and the two lattices of Proposition 3.1 are multiplied
  together.
* `herbrandEq_of_shortExact` — the same, with the multiplicativity identity *discharged* by the
  Tate long exact sequence (`hZero_mul_hOne_of_shortExact`), at the cost of the six finiteness
  hypotheses.
* `herbrandEq_one_of_finite` — the Herbrand quotient of a finite module is `1` (Herbrand's lemma),
  i.e. `HerbrandEq M 1`.

None of these is a new input: they are consequences of `Herbrand/Reduction.lean` and
`Herbrand/hZero_eq_hOne_of_finite.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory

noncomputable section

namespace NK.GlobalCFTdeep

variable {G : Type} [CommGroup G] [Fintype G] [IsCyclic G]

/-- **Multiplicativity of the Herbrand quotient along a short exact sequence, in the
cross-multiplied form.**  If `h(S.X₁) = m`, `h(S.X₃) = m'` and the multiplicity identity
`hZero S.X₂ * hOne S.X₁ * hOne S.X₃ = hZero S.X₁ * hZero S.X₃ * hOne S.X₂` of
`Herbrand/Reduction.lean` holds, then `h(S.X₂) = m · m'`: the `hOne`-terms of `S.X₁` and `S.X₃`
cancel because they are non-zero. -/
theorem herbrandEq_of_mult (S : ShortComplex (Rep ℤ G)) (m m' : ℕ)
    (h1 : HerbrandEq S.X₁ m) (h3 : HerbrandEq S.X₃ m')
    (hpos1 : 0 < hOne S.X₁) (hpos3 : 0 < hOne S.X₃)
    (hMult : hZero S.X₂ * hOne S.X₁ * hOne S.X₃ = hZero S.X₁ * hZero S.X₃ * hOne S.X₂) :
    HerbrandEq S.X₂ (m * m') := by
  rw [HerbrandEq] at h1 h3 ⊢
  rw [h1, h3] at hMult
  have hpos : 0 < hOne S.X₁ * hOne S.X₃ := Nat.mul_pos hpos1 hpos3
  have key : hZero S.X₂ * (hOne S.X₁ * hOne S.X₃) =
      m * m' * hOne S.X₂ * (hOne S.X₁ * hOne S.X₃) := by
    have h := hMult
    nth_rewrite 1 [mul_assoc] at h
    rw [h]
    ring
  exact Nat.eq_of_mul_eq_mul_right hpos key

/-- **Multiplicativity of the Herbrand quotient along a short exact sequence**, with the
multiplicativity identity discharged by the long exact sequence in Tate cohomology
(`hZero_mul_hOne_of_shortExact`). -/
theorem herbrandEq_of_shortExact (S : ShortComplex (Rep ℤ G)) (hS : S.ShortExact) (m m' : ℕ)
    (h1 : HerbrandEq S.X₁ m) (h3 : HerbrandEq S.X₃ m')
    [Finite ↥(tateCohomology S.X₁ 0)] [Finite ↥(tateCohomology S.X₁ 1)]
    [Finite ↥(tateCohomology S.X₂ 0)] [Finite ↥(tateCohomology S.X₂ 1)]
    [Finite ↥(tateCohomology S.X₃ 0)] [Finite ↥(tateCohomology S.X₃ 1)] :
    HerbrandEq S.X₂ (m * m') :=
  herbrandEq_of_mult S m m' h1 h3 (Nat.card_pos) (Nat.card_pos)
    (hZero_mul_hOne_of_shortExact S hS)

/-- **The Herbrand quotient of a finite module is `1`** (Herbrand's lemma): for a finite
`ℤ[G]`-module `M` one has `HerbrandEq M 1`, i.e. `|Ĥ⁰(G, M)| = |Ĥ¹(G, M)|`. -/
theorem herbrandEq_one_of_finite (M : Rep ℤ G) [Finite M.V] : HerbrandEq M 1 := by
  rw [HerbrandEq]
  show Nat.card (tateCohomology M 0) = 1 * Nat.card (tateCohomology M 1)
  rw [Herbrand.hZero_eq_hOne_of_finite M, one_mul]

end NK.GlobalCFTdeep
