/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The inputs of the twisted Hasse principle, and the reduction

This module assembles the inputs of the Hasse principle in the coefficient-correct (`μ_p`-twisted)
form and *proves* the reduction of the statement that the Neukirch–Uchida development consumes,

`NK.BrauerTwist.Sha2Vanishing p K K' κ κ'`

(equivalently, by `NK.HasseTwist.sha2Vanishing_iff_levelForm`, its level-wise form `LevelForm`),
to them.  It is the twisted counterpart of `Submission/Work/HassePrinciple/Inputs.lean`.

## The inputs

`NK.HasseTwist.Sha2Input p K K' κ κ'` has **three** mathematical fields (plus `hp : p.Prime`, the
case of interest):

1. `Sha2Input.hasse_norm : NK.HassePrinciple.HasseNormTheorem` — the **Hasse norm theorem for
   cyclic extensions of number fields** (`Submission/Work/HassePrinciple/Norm.lean`): the norm index
   formula `[C_K : N_{L/K} C_L] = [L : K]` and the local-global principle for norms
   `Kˣ ∩ N 𝕀_L = N Lˣ`.  This is the licensed number-theoretic input; it is *consumed* through
   `NK.HassePrinciple.fieldAxiom_of_hasseNormTheorem`, which derives the field axiom
   `NK.GlobalCFT.FieldAxiom` of the on-disk class formation for every cyclic extension.
2. `Sha2Input.level_obstruction` — the **labelled level-wise Hasse principle in the strong form**:
   for every closed `U ≤ Gal(K'/K)` isomorphic to `Gal(κ'/κ)` and every finite level `L`, a class of
   the level obstruction `levelObstruction p U L` is zero.  Classically this is Hasse–Brauer–Noether
   for the relative extension `L/(L ⊓ K'^U)` with cyclotomic coefficients,
   `Br(L/(L ⊓ K'^U))[p] ↪ ∏_w Br(L_w/(L ⊓ K'^U)_w)[p]` (Neukirch–Schmidt–Wingberg,
   *Cohomology of Number Fields*, (9.2.1)-(9.2.3); Hasse, *Die Struktur der R. Brauerschen
   Algebrenklassengruppe über algebraischen Zahlkörpern*, 1933, Satz 24 and its relative version).
   The field is **labelled** (the subgroup has to be isomorphic to `Gal(κ'/κ)` with `κ` a `p`-adic
   field) and stated in the **strong** (level-obstruction) form: both restrictions are necessary.
   The κ-free and the colimit forms are *false* — see `Submission/Work/HasseTwist/README.md` §4,
   where the counterexample of `Submission/Work/HassePrinciple/README.md` §5.7 (the quaternion
   class `(-1,-1)` over `ℚ(√2)` at `p = 2`, whose only non-vanishing local invariants are at the
   *archimedean* places, which `OverFinitePrime` does not see) is transported to the twisted
   setting, together with the discussion of why the labelling rules it out.
3. `Sha2Input.kernel_exhausted` — the **exhaustion of the kernel of the localisation by the finite
   levels**: a locally trivial class of `H²(U, μ_p)` is represented at some finite level by a class
   of the level obstruction.  This is the "passage to the limit" step; it is *not* a restatement of
   the Hasse principle, since the kernel of the localisation of a filtered colimit is not in general
   the union of the kernels of its levels (filtered colimits commute with finite limits but not with
   the infinite product over the places — see `Submission/Work/HassePrinciple/README.md` §5.2).

## The reduction (proved)

* `NK.HasseTwist.levelForm_of_sha2Input` — `LevelForm` from the inputs;
* **`NK.HasseTwist.sha2Vanishing`** — the final result, `NK.BrauerTwist.Sha2Vanishing`.

The smaller, `p`-primary input catalogue — the labelled level-wise Hasse principle asserted only at
the levels whose level group is a `p`-group, as in `Submission/Work/HassePrinciple/Inputs.lean` — is
`NK.HasseTwist.Sha2InputPgroup` in `Submission/Work/HasseTwist/Pgroup.lean`, together with the
proved Sylow reduction `NK.HasseTwist.obstruction_trivial_of_pgroupLevel` and the resulting
`NK.HasseTwist.sha2Vanishing_of_pgroupInput`.
-/

import Submission.NK.HasseTwist.Hasse
import Submission.NK.HassePrinciple.Norm

open CategoryTheory
open scoped Pointwise

set_option autoImplicit false

universe u

namespace NK.HasseTwist

open NK.BrauerTwist

variable {K K' κ κ' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K']
  [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ']

/-- **The inputs of the twisted (`μ_p`-coefficient) Hasse principle**: the licensed
number-theoretic input (`HasseNormTheorem`), the labelled level-wise Hasse principle in the strong
form, and the exhaustion of the kernel of the localisation by the finite levels.  See the module
docstring and `Submission/Work/HasseTwist/README.md` §3. -/
structure Sha2Input (p : ℕ) (K K' κ κ' : Type u) [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] : Prop where
  /-- the case of interest: `p` is a prime. -/
  hp : p.Prime
  /-- **The Hasse norm theorem for cyclic extensions of number fields**: the reciprocity
  isomorphism in index form and the local-global principle for norms
  (`Submission/Work/HassePrinciple/Norm.lean`). -/
  hasse_norm : NK.HassePrinciple.HasseNormTheorem.{u}
  /-- **The labelled level-wise Hasse principle** (strong form): for every closed
  `U ≤ Gal(K'/K)` isomorphic to `Gal(κ'/κ)` and every finite level, a class of the level
  obstruction is zero.  Classically this is Hasse–Brauer–Noether with cyclotomic coefficients for
  the relative extension `L/(L ⊓ K'^U)`; see the module docstring for the reference, for why both
  the labelling and the strong form are necessary, and for the counterexample ruling out the
  κ-free (unlabelled) form. -/
  level_obstruction : ∀ (U : Subgroup Gal(K'/K)), IsClosed (U : Set Gal(K'/K)) →
    Nonempty (U ≃* Gal(κ'/κ)) → ∀ (L : FiniteGaloisIntermediateField K K')
      (a : LevelH2 p U L), a ∈ levelObstruction p U L → a = 0
  /-- **The exhaustion of the kernel of the localisation by the finite levels**: a locally trivial
  class of `H²(U, μ_p)` is represented at some finite level by a class of the level obstruction (see
  `Submission/Work/HasseTwist/README.md` §3, item 3). -/
  kernel_exhausted : ∀ (U : Subgroup Gal(K'/K)), IsClosed (U : Set Gal(K'/K)) →
    Nonempty (U ≃* Gal(κ'/κ)) → ∀ x : H2Twist p U,
      (∀ A : OverFinitePrime K K', H2Twist.loc p U x A = 0) →
        ∃ (L : FiniteGaloisIntermediateField K K') (a : LevelH2 p U L),
          x = H2Twist.ofLevel p U L a ∧ a ∈ levelObstruction p U L

section Reduction

variable (p : ℕ) (h : Sha2Input (K := K) (K' := K') (κ := κ) (κ' := κ') p)

include h

/-- **The labelled level-wise Hasse principle**, in the form in which it is consumed. -/
theorem obstruction_trivial_of_sha2Input :
    ∀ (U : Subgroup Gal(K'/K)), IsClosed (U : Set Gal(K'/K)) →
      Nonempty (U ≃* Gal(κ'/κ)) → ∀ (L : FiniteGaloisIntermediateField K K')
        (a : LevelH2 p U L), a ∈ levelObstruction p U L → a = 0 :=
  h.level_obstruction

/-- **`LevelForm` from the inputs.** -/
theorem levelForm_of_sha2Input :
    LevelForm (K := K) (K' := K') (κ := κ) (κ' := κ') p :=
  levelForm_of_labelledObstruction (K := K) (K' := K') (κ := κ) (κ' := κ') p
    (obstruction_trivial_of_sha2Input (K := K) (K' := K') (κ := κ) (κ' := κ') p h)
    h.kernel_exhausted

/-- **The Hasse principle `NK.BrauerTwist.Sha2Vanishing` from the inputs.**

This is the coefficient-correct (`μ_p`-twisted) form of the local-global arithmetic input of block
(i) of the Neukirch–Uchida development: Hasse–Brauer–Noether with cyclotomic coefficients,
`Br(M)[p] ↪ ∏_v Br(M_v)[p]`, together with its passage to the colimit over the finite levels.  The
statement is `∀ H ≤ Gal(K'/K)` closed isomorphic to `Gal(κ'/κ)`, `∀ x : H²(H, μ_p)`, if the
localisation of `x` vanishes at every place of `K'` over a finite prime of `K` then `x = 0`. -/
theorem sha2Vanishing :
    Sha2Vanishing (K := K) (K' := K') p κ κ' :=
  sha2Vanishing_of_levelForm (K := K) (K' := K') (κ := κ) (κ' := κ') p
    (levelForm_of_sha2Input (K := K) (K' := K') (κ := κ) (κ' := κ') p h)

end Reduction

end NK.HasseTwist
