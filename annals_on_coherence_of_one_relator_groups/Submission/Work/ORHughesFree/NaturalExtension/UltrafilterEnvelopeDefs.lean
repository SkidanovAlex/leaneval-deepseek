/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The ultrafilter ring `P^U_{ω,τ}` of [JZLA20, §3.2], exposed

`NaturalExtension.isStarRegularRank_naturalExtension` (i.e. [JZLA20, Proposition 3.6]) proves that
the natural extension `rkE` of a `τ`-compatible rank function `rk` on a positive definite
`∗`-regular ring `U` is `∗`-regular, by *constructing* the ultraproduct ring

`P^U_{ω,τ} = (∏_{n ≥ 1} M_n(U)) / ker rk_ω`

of [JZLA20, (3)] and a `∗`-homomorphism `Φ : U[t^{±1};τ] →+* P^U_{ω,τ}`.  In that theorem the
ring and the map are only existentially quantified (`IsStarRegularRank` is an `∃`-statement).

For [JZLA20, Theorem 6.1] we need them *exposed*: the proof identifies the `K[H]`-rings
`R(f_ω(φ(K[N])[t^{±1};τ]), P^U_{ω,τ})` and `U_H` (both are epic `∗`-regular envelopes of the rank
function `rk|_{K[H]}`, hence isomorphic by [JZLA20, Theorem 2.9]), and it uses the embedding
`U_N((t;τ)) ↪ P^U_{ω,τ}` of [JZLA20, (4)].

This file contains the interface `UltrafilterEnvelope`, recording exactly the properties of
`(P^U_{ω,τ}, rk_ω, f_ω)` that the proof of [JZLA20, Theorem 6.1] uses:

* `P` is `∗`-regular and positive definite, with a **faithful** rank function `rkP`;
* `fω : U[t^{±1};τ] →+* P` is an injective `∗`-homomorphism;
* the pullback of `rkP` along `fω` is the natural extension `rkE` of `rk`.
-/
import Mathlib
import Submission.Work.ORHughesFree.JZLA20
import Submission.Work.ORHughesFree.NaturalExtension
import Submission.Work.ORHughesFree.NaturalExtension.envelopeDefs
import Submission.Work.ORHughesFree.JZLA20
import Submission.Work.ORHughesFree.StarRegular
import Submission.Work.ORHughesFree.Epic
import Submission.Work.ORHughesFree.SylvesterRank

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ORHughesFree.NaturalExtension

open Work.ORHughesFree

/-- **The ultrafilter ring `P^U_{ω,τ}` of [JZLA20, §3.2], with its structure map.**  This records
the data that [JZLA20, Proposition 3.6] constructs internally and that [JZLA20, Theorem 6.1] needs
to be able to name. -/
structure UltrafilterEnvelope {U : Type} [Ring U] [StarRing U] [IsStarRegular U]
    [MulSemiringAction (Multiplicative ℤ) U] (hpos : IsPositiveDefiniteStarRegular U)
    (rk : SylvesterRank U)
    (hstar : ∀ (n : Multiplicative ℤ) (x : U), star (n • x) = n • star x)
    (hτ : ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) U),
      rk.rk n m (A.map (fun a => (Multiplicative.ofAdd (1 : ℤ)) • a)) = rk.rk n m A)
    (rkE : SylvesterRank (SkewMonoidAlgebra U (Multiplicative ℤ))) where
  /-- the underlying ring `P^U_{ω,τ}` -/
  P : Type
  /-- `P^U_{ω,τ}` is a ring -/
  [ringP : Ring P]
  /-- `P^U_{ω,τ}` carries an involution -/
  [starP : StarRing P]
  /-- `P^U_{ω,τ}` is `∗`-regular -/
  [isStarRegularP : IsStarRegular P]
  /-- `P^U_{ω,τ}` is positive definite -/
  [positiveDefiniteP : IsPositiveDefiniteStarRegular P]
  /-- the rank function `rk_ω` of `P^U_{ω,τ}` -/
  rkP : SylvesterRank P
  /-- `rk_ω` is faithful (it is a faithful quotient of `lim_ω rk ∘ flatten`) -/
  faithfulP : rkP.IsFaithful
  /-- the structure map `f_ω : U[t^{±1};τ] →+* P^U_{ω,τ}` of [JZLA20, (5)] -/
  fω : SkewMonoidAlgebra U (Multiplicative ℤ) →+* P
  /-- `f_ω` is a `∗`-homomorphism -/
  fω_star : ∀ p : SkewMonoidAlgebra U (Multiplicative ℤ), fω (starSkewL p) = star (fω p)
  /-- `f_ω` is injective ([JZLA20, (4)]: `ψ` is injective because `rk'_ω(ψ(p)) ≥ rk'(a_i) > 0`
  for a series with first non-zero coefficient `a_i`) -/
  fω_injective : Function.Injective fω
  /-- the pullback of `rk_ω` along `f_ω` is the natural extension of `rk` -/
  rank_compat : ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) (SkewMonoidAlgebra U (Multiplicative ℤ))),
    rkE.rk n m A = rkP.rk n m (A.map fω)

end Work.ORHughesFree.NaturalExtension
