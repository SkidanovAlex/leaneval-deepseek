/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The local arithmetic inputs for a `p`-adic field

This file collects, in one structure, the inputs about a `p`-adic field `κ` which
the local input of the Neukirch–Uchida theorem (CoNF XII (12.1.9), (12.1.10))
consumes.  `κ` is described by

* `p`, its residue characteristic,
* `d = [κ : ℚ_p]`, its absolute degree,
* `δ ∈ {0,1}`, with `δ = 1` exactly when `ζ_p ∈ κ`,

and the structure bundles the *arithmetic* facts and the two group-theoretic
inputs which make the data recoverable from `Gal(κ̄/κ)`.

## Why the invariants are taken on the abelianisation

The classical statement (CoNF, and the standard theory of local fields) is

  `frattiniRank p (Gal(κ^{(p)}/κ)) = 1 + [κ : ℚ_p] + δ`,

on the *maximal pro-`p` quotient* of `Gal(κ̄/κ)`.  Index-`p` subgroups of the
maximal pro-`p` quotient are exactly the *normal* index-`p` subgroups of
`Gal(κ̄/κ)`, i.e. the index-`p` subgroups of its abelianisation, and there are

  `(p^{d+1+δ} - 1)/(p - 1)`

of them: this is the number of *cyclic* degree-`p` extensions of `κ`.  We therefore
record the invariant on the abelianisation (`HasAbelianFrattiniRank`).

The count of **all** degree-`p` extensions of `κ` is a different number in general:
for `κ = ℚ_3` the cubic `ℚ_3(∛3)` (Eisenstein) is degree `3` and *not* Galois, so
there are more degree-`3` extensions than cyclic ones.  Correspondingly, the `δ = 0`
case has no "every degree-`p` extension is Galois" input: that statement is true
only when `ζ_p ∈ κ` (`δ = 1`), where every degree-`p` extension is Kummer, hence
cyclic.

Two further consequences of `κˣ ≅ ℤ × μ_κ × U¹`, `U¹ = 1 + 𝔪 ≅ ℤ_p^d`, are recorded:
`|κˣ/(κˣ)^p| = p · |μ_κ[p]| · p^d = p^{d+1+δ}`, and the `p`-torsion of the
abelianised absolute Galois group `G_κ^{ab} ≅ Ẑ × \hat{μ_κ} × ℤ_p^d` is `μ_κ[p]`,
non-trivial exactly when `ζ_p ∈ κ`.

See `NK.LocalAnabelian.hasAbelianFrattiniRank_of_inputs` and
`NK.LocalAnabelian.residueChar_and_degree_eq_of_padicGaloisInputs`.
-/
import Submission.NK.LocalAnabelian.Basic
import Submission.NK.LocalAnabelian.Kummer.Defs
import Submission.NK.LocalAnabelian.ResidueChar.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical
open IntermediateField

namespace NK.LocalAnabelian

noncomputable section

/-- **The local arithmetic data of a `p`-adic field, in the form in which the
Neukirch–Uchida local input uses it.**

`κ` is the local field, `K'` a separable closure of it, `p` the residue
characteristic, `d` the absolute degree `[κ : ℚ_p]`, and `δ` the indicator of
`ζ_p ∈ κ`. -/
structure PadicGaloisInputs (p d δ : ℕ) (κ K' : Type*) [Field κ] [Field K'] [Algebra κ K']
    [IsSepClosure κ K'] : Prop where
  hp : p.Prime
  hδ : δ ≤ 1
  /-- `κ` contains a primitive `p`-th root of unity exactly when `δ = 1`. -/
  zeta_iff : (δ = 1) ↔ ∃ ζ : κ, IsPrimitiveRoot ζ p
  /-- The structure theory of `κˣ`: `|κˣ/(κˣ)^p| = p^{d+1+δ}`.  For `κ = ℚ_p` this is
  `Commons.NumberTheory.NumberField.Completion.natCard_powerQuotient_adicCompletion_rat_units`;
  see `NK.LocalAnabelian.natCard_KummerGroup_rat_adic`. -/
  powerQuotient_card : Nat.card (KummerGroup p κ) = p ^ (d + 1 + δ)
  /-- **Local reciprocity.**  The abelianised pro-`p` part of `Gal(κ̄/κ)` is
  `ℤ_p^d × (ℤ/p)^δ`, i.e. there are `(p^{d+1+δ} - 1)/(p - 1)` cyclic degree-`p`
  extensions of `κ`. -/
  abelian_rank : HasAbelianFrattiniRank p (d + 1 + δ) (Gal(K'/κ))
  /-- The `p`-torsion of the abelianisation detects `ζ_p ∈ κ` (it is `μ_κ[p]`). -/
  p_torsion_iff : (δ = 1) ↔ HasPTorsionAbelianization p (Gal(K'/κ))
  /-- **Ivanov's detection of the residue characteristic.** -/
  residueChar_detected : ResidueCharDetectedBy p (Gal(K'/κ))

end

end NK.LocalAnabelian
