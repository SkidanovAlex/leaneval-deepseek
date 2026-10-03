/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The ultraproduct ring `P^U_{ω,τ}` with its skew Laurent *series* map

[JZLA20, §3.2 and (4)].  For a positive definite `∗`-regular ring `U`, a `τ`-compatible faithful
Sylvester rank function `rk` on `U` and a natural extension `rkE` of `rk` to `U[t^{±1};τ]`, the
ultraproduct ring

  `P^U_{ω,τ} = W U ⧸ ker rk_ω`

carries a faithful rank function `rk_ω` and a `∗`-homomorphism `f_ω : U[t^{±1};τ] →+* P^U_{ω,τ}`
whose pullback is `rkE` ([JZLA20, (5)]).  In addition, the Toeplitz family of a skew Laurent
*series* `p`,

  `n ↦ (τ^r (p_{s-r}))_{r,s ∈ Fin (n+1)}`,

is a ring homomorphism modulo `ker rk_ω` — the defect `toeplitzSeries N (pq) -
toeplitzSeries N p * toeplitzSeries N q` is of bounded rank, independently of `N`, because the
window `r + k ∈ [0, N-1]` only truncates the contributions of the negative degrees of `p` and of
`q` — and consequently there is a ring homomorphism

  `Ψ : U((t;τ)) →+* P^U_{ω,τ}`

extending `f_ω`, which is injective ([JZLA20, (4)]).

This structure records exactly the data that [JZLA20, Theorem 6.1] uses:
`SeriesEnvelope.P`, `SeriesEnvelope.rkP` (faithful), `SeriesEnvelope.fω` (a `∗`-homomorphism with
`rkP ∘ fω = rkE`) and `SeriesEnvelope.Ψ` (the series extension of `fω`, injective).
-/
import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.UltrafilterEnvelopeDefs
import Submission.Work.ORHughesFree.SkewLaurentSeries.exists_injective_ringHom_skewMonoidAlgebra

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ORHughesFree.NaturalExtension

open Work.ORHughesFree

/-- **The ultraproduct ring `P^U_{ω,τ}` of [JZLA20, §3.2], with its skew Laurent *series* map.**
This is `NaturalExtension.UltrafilterEnvelope` together with the embedding `Ψ` of the skew Laurent
series ring of [JZLA20, (4)]. -/
structure SeriesEnvelope {U : Type} [Ring U] [StarRing U] [IsStarRegular U]
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
  /-- `rk_ω` is faithful -/
  faithfulP : rkP.IsFaithful
  /-- the structure map `f_ω : U[t^{±1};τ] →+* P^U_{ω,τ}` of [JZLA20, (5)] -/
  fω : SkewMonoidAlgebra U (Multiplicative ℤ) →+* P
  /-- `f_ω` is a `∗`-homomorphism -/
  fω_star : ∀ p : SkewMonoidAlgebra U (Multiplicative ℤ), fω (starSkewL p) = star (fω p)
  /-- `f_ω` is injective -/
  fω_injective : Function.Injective fω
  /-- the pullback of `rk_ω` along `f_ω` is the natural extension `rkE` of `rk` -/
  rank_compat : ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) (SkewMonoidAlgebra U (Multiplicative ℤ))),
    rkE.rk n m A = rkP.rk n m (A.map fω)
  /-- the embedding `U((t;τ)) →+* P^U_{ω,τ}` of [JZLA20, (4)] -/
  Ψ : SkewLaurentSeries U →+* P
  /-- `Ψ` extends `fω` -/
  Ψ_extends : ∀ p : SkewMonoidAlgebra U (Multiplicative ℤ),
    Ψ (SkewLaurentSeries.toRingHom p) = fω p
  /-- `Ψ` is injective -/
  Ψ_injective : Function.Injective Ψ

end Work.ORHughesFree.NaturalExtension
