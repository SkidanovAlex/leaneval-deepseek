/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.NK.GlobalCFTdeep.Basic
import Submission.NK.GlobalCFTdeep.Herbrand.herbrandEq_units_adicCompletion_of_abelian
import Submission.NK.GlobalCFTdeep.Audit.localHerbrand_self
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local Herbrand quotient of the units of a local field

The local ingredient of Milne's proof of `h(Gal(L/K), C_L) = [L : K]` (Milne, *Class Field
Theory*, Theorem 4.3) is the computation, at each place `w` of `L` above a place `v` of `K`,

  `h(Gal(L_w/K_v), L_wˣ) = [L_w : K_v]`,

which enters Proposition 2.7 through the decomposition group: for cyclic `L/K` the group
`Gal(L_w/K_v) ≅ D_w` is **cyclic**, and then `Ĥ¹ = 0` (Hilbert 90), `|H²(Gal(L_w/K_v), L_wˣ)| =
[L_w : K_v]` (the local invariant map) and two-periodicity give the computation.

## The statement is false without commutativity

The hypothesis of commutativity is **not** cosmetic: for a finite Galois extension `E/F` of local
fields with group `G` one has `Ĥ¹(G, Eˣ) = 0` and `Ĥ⁰(G, Eˣ) = Fˣ ⧸ N_{E/F}Eˣ`, and by the norm
limitation theorem the norm group is that of the maximal abelian subextension, so the Herbrand
quotient is `|Gᵃᵇ|`, which is strictly smaller than `|G| = [E : F]` as soon as `G` is non-abelian.
The *general* form of the statement — which an earlier version of this file recorded as the input
`LocalHerbrandQuotient` — is therefore false, and it has been replaced by the abelian form below.
(The relevant reference is Milne, *CFT*, Proposition 2.5 together with the remark after Theorem
5.1: `H²(G, L_wˣ)` always has order `[L_w : K_v]`, but `Ĥ⁰` is `Gᵃᵇ`.)

## What is proved, and where

For the case that is actually used — `L_w = q.adicCompletion L` the completion of a number field at
a finite place, with abelian (e.g. cyclic) local Galois group — the computation is **proved** in
`Submission/Work/GlobalCFTdeep/Herbrand/herbrandEq_units_adicCompletion_of_abelian.lean`:

`NK.GlobalCFTdeep.Herbrand.herbrandEq_units_adicCompletion_of_abelian`
  `: HerbrandEq (Rep.ofMulDistribMulAction Gal(L_q/K_Q) L_qˣ) [L_q : K_Q]`.

It is a consequence of `NK.LocalReciprocity.index_normGroup_eq_finrank` (the abelian local norm
index theorem, proved in `Submission/Work/LocalReciprocity/`) and of the general reduction
`NK.GlobalCFTdeep.Herbrand.herbrandEq_units_of_normIndex` (Hilbert 90 plus the `Ĥ⁰`-computation
`|Ĥ⁰(G, Eˣ)| = [Fˣ : N Eˣ]`).  So the local ingredient is *not* an input of this chapter any more;
what remains of Milne's Proposition 2.7 is the passage from the local fields `L_wˣ` to the idèles
`𝕀_{L,T}` (the orbit decomposition and Shapiro's lemma — Shapiro itself is proved here:
`herbrandEq_coind_iff`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFTdeep

/-- **The local Herbrand quotient of the units, abelian case** (Milne, *CFT*, Proposition 2.5;
Serre, *Local Fields*, V.1.2): for a finite Galois extension `E/F` of nonarchimedean local fields
whose Galois group is commutative,

  `|Ĥ⁰(Gal(E/F), Eˣ)| = [E : F] · |Ĥ¹(Gal(E/F), Eˣ)|`,

i.e. the Herbrand quotient of the unit group of `E` is `[E : F]`.  See the module docstring for why
commutativity is necessary (the general form is false) and for the reference to the *proved* case of
completions of number fields (`herbrandEq_units_adicCompletion_of_abelian`). -/
structure LocalHerbrandQuotient : Prop where
  /-- the local computation, at every finite Galois extension of nonarchimedean local fields with
  commutative Galois group. -/
  herbrand : ∀ {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    [IsMulCommutative (E ≃ₐ[F] E)],
    Nat.card (tateCohomology (Rep.ofMulDistribMulAction (E ≃ₐ[F] E) Eˣ) 0) =
      Module.finrank F E * Nat.card (tateCohomology (Rep.ofMulDistribMulAction (E ≃ₐ[F] E) Eˣ) 1)

/-- The local Herbrand statement at the trivial extension `E = F`, a satisfiability witness for the
abelian case of `LocalHerbrandQuotient` (both sides are `1`). -/
theorem localHerbrand_self {F : Type} [Field F] :
    Nat.card (tateCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[F] F) Fˣ) 0) =
      Nat.card (tateCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[F] F) Fˣ) 1) :=
  NK.GlobalCFTdeep.Audit.localHerbrand_self (F := F)

end NK.GlobalCFTdeep
