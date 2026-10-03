/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# A faithful Sylvester rank function on the `∗`-regular closure `V = R(K[H], U(G))`

This file proves `Work.ORDivLoc.exists_faithful_sylvesterRank_starClosure`: the `∗`-regular
closure `V = starClosureOfSubgroup E φK H` of the image of `K[H]` in `U(G)` carries a *faithful*
Sylvester matrix rank function (in the sense of the JZLA20 engine, node N6,
`Work.ORHughesFree.SylvesterRank`).

Two ingredients are needed, and both are pure bookkeeping:

* the analytic node N5 uses its own copy of the notion,
  `Work.ORVonNeumann.SylvesterRankFunction`, whose axioms are packaged slightly differently
  (`≤ min` for products, one lemma for each side, and block constructions spelled with
  `Matrix.reindex` rather than `Matrix.submatrix`).  The two structures are literally the same
  data, and the conversion `toRank` / `toRank_isFaithful` below records this;
* a faithful rank function restricts to a faithful rank function along an *injective* ring
  homomorphism (`isFaithful_pullback_of_injective`), here `Subring.subtype V.toSubring`.

Combining them with the faithful rank function `E.rk` of the envelope `U(G)` gives the claim.
-/
import Mathlib
import Submission.Work.ORDivLoc.Basic
import Submission.Work.ORDivLoc.Vocabulary

set_option autoImplicit false

namespace Work.ORDivLoc.Rank

/-! ## Two elementary `1 × 1` matrix identities -/

/-- The `1 × 1` matrix `!![a]` of the N5 vocabulary is `oneByOne a` of the N6 vocabulary. -/
theorem oneByOne_eq_bang {R : Type} [Ring R] (a : R) :
    (!![a] : Matrix (Fin 1) (Fin 1) R) = Work.ORHughesFree.oneByOne a := by
  ext i j
  simp [Work.ORHughesFree.oneByOne]

/-- `Matrix.map` of the `1 × 1` matrix `oneByOne a` is `oneByOne (f a)`. -/
theorem oneByOne_map {R S : Type} [Ring R] [Ring S] (f : R →+* S) (a : R) :
    (Work.ORHughesFree.oneByOne a).map f = Work.ORHughesFree.oneByOne (f a) := by
  ext i j
  fin_cases i
  fin_cases j
  rfl

/-! ## The N5 ↔ N6 translation of Sylvester rank functions -/

/-- **N5 → N6**: the `Work.ORVonNeumann.SylvesterRankFunction` of the analytic node is a
`Work.ORHughesFree.SylvesterRank` in the sense of the JZLA20 engine.  The two structures carry
the same data; the only differences are that N5's product axiom is the combined `≤ min` while N6
splits it into `rk_mul_le_left`/`rk_mul_le_right`, and that the two block constructions
(`Work.ORVonNeumann.blockDiag`/`blockUpper` and `Work.ORHughesFree.blockDiagFin`/`blockUpperFin`)
are definitionally equal (the first is `reindex`-based, the second `submatrix`-based, and
`reindex e e' = submatrix e.symm e'.symm`). -/
noncomputable def toRank {R : Type} [Ring R]
    (rk : Work.ORVonNeumann.SylvesterRankFunction R) : Work.ORHughesFree.SylvesterRank R where
  rk _n _m A := rk.toFun _n _m A
  rk_nonneg _n _m A := rk.rank_nonneg A
  rk_zero _n _m := rk.map_zero _n _m
  rk_one := rk.map_one
  rk_mul_le_left A B := rk.rank_mul_le_left A B
  rk_mul_le_right A B := rk.rank_mul_le_right A B
  rk_blockDiag A B := rk.blockDiag_add A B
  rk_blockUpper A B C := rk.blockUpper_le A C B

/-- **N5 → N6** for faithfulness: the translation `toRank` of a faithful rank function is
faithful. -/
theorem toRank_isFaithful {R : Type} [Ring R] (rk : Work.ORVonNeumann.SylvesterRankFunction R)
    (h : rk.Faithful) : (toRank rk).IsFaithful := by
  intro a ha
  exact h a (by rw [oneByOne_eq_bang]; exact ha)

/-! ## Restriction to a subring -/

/-- **Faithfulness restricts along an injective ring homomorphism**: if `rk` is a faithful
Sylvester rank function on `S` and `f : R →+* S` is injective, then the pullback `f♯ rk` is
faithful on `R`.  Indeed, `(pullback f rk) (oneByOne a) = rk (oneByOne (f a))`, so the pullback
vanishes on `a` only if `rk` vanishes on `f a`, i.e. only if `f a = 0`, i.e. only if `a = 0`. -/
theorem isFaithful_pullback_of_injective {R S : Type} [Ring R] [Ring S] (f : R →+* S)
    (hf : Function.Injective f) (rk : Work.ORHughesFree.SylvesterRank S) (h : rk.IsFaithful) :
    (Work.ORHughesFree.SylvesterRank.pullback f rk).IsFaithful := by
  intro a ha
  have h1 : (Work.ORHughesFree.SylvesterRank.pullback f rk).rk 1 1
        (Work.ORHughesFree.oneByOne a)
      = rk.rk 1 1 (Work.ORHughesFree.oneByOne (f a)) := by
    show rk.rk 1 1 ((Work.ORHughesFree.oneByOne a).map f) = _
    rw [oneByOne_map]
  rw [h1] at ha
  have h2 : f a = 0 := h (f a) ha
  exact hf (by rw [h2, map_zero])

/-! ## The main statement -/

/-- **The `∗`-regular closure `V = R(K[H], U(G))` carries a faithful Sylvester rank function.**
Concretely, the extended rank function `rk_G` of the envelope `U(G)` is faithful, so its
restriction to the subring `V ≤ U(G)` — the pullback along the injective structure map
`V →+* U(G)` — is faithful.  This is the `rkU`/`hfaith` input of the JZLA20 engine at the pair
`(K, H, V)`. -/
theorem exists_faithful_sylvesterRank_starClosure {K : Type} [Field K] {G : Type} [Group G]
    (E : Work.ORVonNeumann.StarRegularEnvelope G) (φK : K →+* ℂ) [Algebra K E.U] (H : Subgroup G) :
    ∃ rkU : Work.ORHughesFree.SylvesterRank ↥(Work.ORDivLoc.starClosureOfSubgroup E φK H),
      rkU.IsFaithful :=
  ⟨Work.ORHughesFree.SylvesterRank.pullback
      (Subring.subtype (Work.ORDivLoc.starClosureOfSubgroup E φK H).toSubring) (toRank E.rk),
    isFaithful_pullback_of_injective _ Subtype.coe_injective _
      (toRank_isFaithful E.rk E.rk_faithful)⟩

end Work.ORDivLoc.Rank
