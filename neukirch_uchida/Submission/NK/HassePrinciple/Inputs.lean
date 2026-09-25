/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The inputs of the Hasse principle, and the reduction

**SUPERSEDED — read README §13.0 before using anything in this module.**  The input
structure `NK.HassePrinciple.Sha2Input` used here (and the corollaries stated against it)
belongs to the abandoned *level-wise* route; the authoritative route is `Spec.lean`:
`NK.HassePrinciple.Sha2Spec` and `sha2Vanishing_of_spec`.  The two interfaces are kept
because the level-wise lemmas are correct, but a *caller* should use `Spec.lean` — and must
not expect the level-wise input to follow from the licensed cyclic pair: see README §13.7(iv).

This module assembles the inputs of the Hasse principle and *proves* the reduction of the statement
that the Neukirch–Uchida development consumes,
`NK.BrauerHasse.Sha2Vanishing` (equivalently, by
`NK.HassePrinciple.sha2Vanishing_iff_levelForm`, its level-wise form `LevelForm`), to them.

## Caveat (README §12, §13) — read this before using `Sha2Input`

**Superseded.**  The interface to use is `NK.HassePrinciple.Sha2Spec` in
`Submission/Work/HassePrinciple/Spec.lean` (corrected target: the archimedean condition, necessary
for `p = 2`, plus `NK.HassePrinciple.LimitPassage`), with the proved reductions
`NK.HassePrinciple.sha2Vanishing_of_spec` and `NK.HassePrinciple.exists_loc_ne_zero_of_spec`.
`Sha2Input` below is kept for history: its second field `pgroup_level` is the *fine* level-wise
Hasse principle, which §12.2 and §13.7(iv) show is the wrong shape, and the relative
Hasse–Brauer–Noether theorem it was meant to consume is now *proved* from the licensed cyclic input
(`NK.HassePrinciple.hbnUnits_of_cyclicInput`, README §13.4).

The second field `pgroup_level` is the *fine* (level-wise) localisation form of the Hasse principle.
It is **not** what the classical theory (the Hasse norm theorem plus the cyclic/Sylow dévissage)
produces: that is the *relative* Hasse–Brauer–Noether theorem, with the *coarser* localisation to
the decomposition groups `D_w ∩ Γ` of the level extension.  The two differ by an inflation, and
there is a Heisenberg-class obstruction (README §12.2) indicating that the fine form is false at
levels whose level group is non-cyclic.  So `Sha2Input` is *not* the intended final interface; the
corrected chain — with the status of every step — is README §12, and the steps of it that are
formalised are the §8.4 items 1 (Kummer in the limit, `NK.HassePrinciple.kummerColim_injective`)
and 4 (`H¹(Γ, C_E) = 0` for `p`-group level groups, from the licensed *cyclic* input,
`NK.HassePrinciple.subsingleton_groupCohomology_one_ideleClassGroup_of_isPGroup`).

## The inputs

`NK.HassePrinciple.Sha2Input p K K' κ κ'` has **two** mathematical fields (plus `hp : p.Prime`, the
case of interest).  See `Submission/Work/HassePrinciple/README.md` §4 for the full discussion; in
brief:

1. `Sha2Input.hasse_norm : NK.HassePrinciple.HasseNormTheorem` — the **Hasse norm theorem for
   cyclic extensions of number fields** (`Norm.lean`): the norm index formula
   `[C_K : N_{L/K} C_L] = [L : K]` and the local-global principle for norms
   `Kˣ ∩ N 𝕀_L = N Lˣ`.  This is the licensed number-theoretic input; the chapter *consumes* it
   through `NK.HassePrinciple.fieldAxiom_of_sha2Input` /
   `NK.HassePrinciple.fieldAxiom_of_hasseNormTheorem`, which derive the field axiom of the on-disk
   class formation for every cyclic extension.
2. `Sha2Input.pgroup_level` — the **labelled level-wise Hasse principle in the strong form**: for every
   closed `U ≤ Gal(K'/K)` isomorphic to `Gal(κ'/κ)` and every finite level `L`, a class of the level
   obstruction `levelObstruction p U L` is zero.  Classically this is the cohomological form of the
   Hasse norm theorem (Kummer theory + the reciprocity isomorphism for cyclic extensions + the
   passage from the cyclic to the general case via the fundamental class); the transport is *not*
   formalised here (README §4(2) and §6) and this field records its conclusion.
   The field is **labelled** (the subgroup has to be isomorphic to `Gal(κ'/κ)`) and stated in the
   **strong** (level-obstruction) form: both restrictions are necessary.  The κ-free and the
   colimit forms are *false* — see README §5.9, where the counterexample of §5.7 is transported to
   the level `L = ℚ(√2,i)` with `U = ⊤` and `p = 2`, refuting the κ-free p-primary statement
   (whose reduction to the general case is nevertheless proved here,
   `NK.HassePrinciple.levelForm_of_pgroupLevel` and
   `NK.HassePrinciple.obstruction_trivial_of_pgroup`).
3. `Sha2Input.kernel_exhausted` — the **exhaustion of the kernel of the localisation by the finite
   levels**: a locally trivial class of `H²(U, Z/p)` is represented at some finite level by a class
   of the level obstruction.  This is the "passage to the limit" step (README §5.2).

## The arithmetic form of the inputs

`NK.HassePrinciple.Sha2InputArith` (`section Arithmetic` below) is the same bundle with the second
mathematical field *restated in the arithmetic vocabulary* of `Submission/Work/HassePrinciple/ArithmeticForm.lean`
(`NK.HassePrinciple.ArithmeticLevelHasse`): the level group is the image
`V.map (levelRestrict L)` of `V` in the finite Galois group `Gal(L/K)` of the level extension, the
local level group is the image `(V ⊓ D_A).map (levelRestrict L)` cut out by the decomposition
subgroup of the place `A`, and the local conditions are the restrictions along that inclusion
(`localInclHom_comm`).  The reduction from the arithmetic form to the level form is *proved*:
`NK.HassePrinciple.obstruction_trivial_of_arithmeticLevelHasse`.

## The reduction (proved)

* `NK.HassePrinciple.levelForm_of_labelledObstruction` — `LevelForm` from the labelled strong
  level-wise Hasse principle and the exhaustion of the kernel;
* `NK.HassePrinciple.levelForm_of_sha2Input` — `LevelForm` from the inputs;
* **`NK.HassePrinciple.sha2Vanishing_of_sha2Input`** — the legacy reduction from `Sha2Input` to
  `NK.BrauerHasse.Sha2Vanishing p K K' κ κ'`.  (The *canonical* name
  `NK.HassePrinciple.sha2Vanishing` is the amended reduction from
  `NK.HassePrinciple.RankInput`, in `RankInput.lean`; this one is kept for the record only — see
  README §22.)

The reduction from the *arithmetic* form of the inputs (`Sha2InputArith`) is
`NK.HassePrinciple.sha2Input_of_arithInput` and `NK.HassePrinciple.sha2Vanishing_of_arithInput`.
-/

import Submission.NK.HassePrinciple.Defs
import Submission.NK.HassePrinciple.Obstruction
import Submission.NK.HassePrinciple.Norm
import Submission.NK.HassePrinciple.LevelHasse
import Submission.NK.HassePrinciple.obstruction_trivial_of_pgroup
import Submission.NK.HassePrinciple.obstruction_trivial_of_pgroup_rel
import Submission.NK.HassePrinciple.levelForm_of_pgroupLevel
import Submission.NK.HassePrinciple.ArithmeticForm

open CategoryTheory
open scoped Pointwise

set_option autoImplicit false

universe u

namespace NK.HassePrinciple

open NK.BrauerHasse

variable {K K' κ κ' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K']
  [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ']

/-- **The inputs of the Hasse principle**: the licensed number-theoretic input
(`HasseNormTheorem`), the labelled level-wise Hasse principle in the strong form, and the exhaustion
of the kernel of the localisation by the finite levels.  See the module docstring and
`Submission/Work/HassePrinciple/README.md` §4. -/
structure Sha2Input (p : ℕ) (K K' κ κ' : Type u) [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] : Prop where
  /-- the case of interest: `p` is a prime. -/
  hp : p.Prime
  /-- **The Hasse norm theorem for cyclic extensions of number fields**: the reciprocity
  isomorphism in index form and the local-global principle for norms (`Norm.lean`). -/
  hasse_norm : HasseNormTheorem.{u}
  /-- **The labelled `p`-primary level-wise Hasse principle** (strong form): for every closed
  `U ≤ Gal(K'/K)` isomorphic to `Gal(κ'/κ)`, every subgroup `V ≤ U` and every finite level at which
  the level group `V/(V ⊓ Gal(K'/L))` is a `p`-group, a class of the level obstruction is zero.
  Classically the cohomological form of the Hasse norm theorem at the `p`-primary levels (Kummer
  theory + the reciprocity isomorphism for cyclic `p`-extensions); this transport is *not* formalised
  here (README §4(2), §6).  See README §5.9 for why the labelled and the strong form are both
  necessary, and `NK.HassePrinciple.obstruction_trivial_of_pgroup_rel` for the proved reduction of
  the labelled strong form at *all* levels to this one. -/
  pgroup_level : ∀ (U : Subgroup Gal(K'/K)), IsClosed (U : Set Gal(K'/K)) →
    Nonempty (U ≃* Gal(κ'/κ)) → ∀ (V : Subgroup Gal(K'/K)), V ≤ U →
      ∀ (L : FiniteGaloisIntermediateField K K') (a : LevelH2 p V L),
        IsPGroup p (LevelGroup V L) → a ∈ levelObstruction p V L → a = 0
  /-- **The exhaustion of the kernel of the localisation by the finite levels**: a locally trivial
  class of `H²(U, Z/p)` is represented at some finite level by a class of the level obstruction (see
  README §5.2). -/
  kernel_exhausted : ∀ (U : Subgroup Gal(K'/K)), IsClosed (U : Set Gal(K'/K)) →
    Nonempty (U ≃* Gal(κ'/κ)) → ∀ x : H2Profinite p U,
      (∀ A : OverFinitePrime K K', H2Profinite.loc p U x A = 0) →
        ∃ (L : FiniteGaloisIntermediateField K K') (a : LevelH2 p U L),
          x = H2Profinite.ofLevel L a ∧ a ∈ levelObstruction p U L

section Reduction

variable (p : ℕ) (h : Sha2Input (K := K) (K' := K') (κ := κ) (κ' := κ') p)

include h

/-- **The labelled level-wise Hasse principle at all levels, from the `p`-primary input.**  This is
the labelled Sylow reduction `NK.HassePrinciple.obstruction_trivial_of_pgroup_rel`. -/
theorem obstruction_trivial_of_sha2Input :
    ∀ (U : Subgroup Gal(K'/K)), IsClosed (U : Set Gal(K'/K)) →
      Nonempty (U ≃* Gal(κ'/κ)) → ∀ (L : FiniteGaloisIntermediateField K K')
        (a : LevelH2 p U L), a ∈ levelObstruction p U L → a = 0 :=
  fun U hU hκ L a ha =>
    obstruction_trivial_of_pgroup_rel (K := K) (K' := K') h.hp U
      (h.pgroup_level U hU hκ) U le_rfl L a ha

/-- **`LevelForm` from the inputs.** -/
theorem levelForm_of_sha2Input :
    LevelForm (K := K) (K' := K') (κ := κ) (κ' := κ') p :=
  levelForm_of_labelledObstruction (K := K) (K' := K') (κ := κ) (κ' := κ') p
    (obstruction_trivial_of_sha2Input (K := K) (K' := K') (κ := κ) (κ' := κ') p h)
    h.kernel_exhausted

/-- **The Hasse principle `NK.BrauerHasse.Sha2Vanishing` from the legacy level-wise inputs**
(`NK.HassePrinciple.Sha2Input`).  **Superseded**: the canonical
`NK.HassePrinciple.sha2Vanishing` takes Neukirch's input
(`NK.HassePrinciple.RankInput`, `RankInput.lean`); this statement is kept for the record, because
its reduction chain (the Sylow dévissage, the level dictionary and the exhaustion of the kernel) is
correct and is reused by the amended interface. -/
theorem sha2Vanishing_of_sha2Input :
    Sha2Vanishing (K := K) (K' := K') p κ κ' :=
  sha2Vanishing_of_levelForm (K := K) (K' := K') (κ := κ) (κ' := κ') p
    (levelForm_of_sha2Input (K := K) (K' := K') (κ := κ) (κ' := κ') p h)

end Reduction

section Arithmetic

variable (p : ℕ)

/-- **The inputs of the Hasse principle, in arithmetic form.**  This is the same reduction as
`Sha2Input`, but the level-wise Hasse principle is stated in the arithmetic vocabulary of
`NK.HassePrinciple.ArithmeticLevelHasse`: the level group is the image `V.map (levelRestrict L)`
of `V` in the finite Galois group `Gal(L/K)` of the level extension, `Γ_A = (V ⊓ D_A).map
(levelRestrict L)` is the part of it cut out by the decomposition subgroup of the place `A`, and the
local conditions are the restrictions `H²(Γ, Z/p) → H²(Γ_A, Z/p)` (`localInclHom_comm`).

The fields are: the licensed Hasse norm theorem for cyclic extensions of number fields, the
level-wise Hasse principle in this arithmetic form, and the exhaustion of the kernel of the
localisation by the finite levels. -/
structure Sha2InputArith (K K' κ κ' : Type u) [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ']
    [IsSepClosure κ κ'] : Prop where
  /-- the case of interest: `p` is a prime. -/
  hp : p.Prime
  /-- **The Hasse norm theorem for cyclic extensions of number fields** (`Norm.lean`). -/
  hasse_norm : HasseNormTheorem.{u}
  /-- **The labelled `p`-primary level-wise Hasse principle, in arithmetic form**
  (`NK.HassePrinciple.ArithmeticLevelHasse`). -/
  level_hasse : ArithmeticLevelHasse (K := K) (K' := K') (κ := κ) (κ' := κ') p
  /-- **The exhaustion of the kernel of the localisation by the finite levels.** -/
  kernel_exhausted : ∀ (U : Subgroup Gal(K'/K)), IsClosed (U : Set Gal(K'/K)) →
    Nonempty (U ≃* Gal(κ'/κ)) → ∀ x : H2Profinite p U,
      (∀ A : OverFinitePrime K K', H2Profinite.loc p U x A = 0) →
        ∃ (L : FiniteGaloisIntermediateField K K') (a : LevelH2 p U L),
          x = H2Profinite.ofLevel L a ∧ a ∈ levelObstruction p U L

/-- The arithmetic form of the inputs implies the level form: the arithmetic input is transported
to the `p`-primary level-wise Hasse principle by
`NK.HassePrinciple.obstruction_trivial_of_arithmeticLevelHasse`. -/
theorem sha2Input_of_arithInput (h : Sha2InputArith (K := K) (K' := K') (κ := κ) (κ' := κ') p) :
    Sha2Input (K := K) (K' := K') (κ := κ) (κ' := κ') p where
  hp := h.hp
  hasse_norm := h.hasse_norm
  pgroup_level := obstruction_trivial_of_arithmeticLevelHasse (K := K) (K' := K')
    (κ := κ) (κ' := κ') p h.level_hasse
  kernel_exhausted := h.kernel_exhausted

/-- **The Hasse principle from the arithmetic inputs.** -/
theorem sha2Vanishing_of_arithInput (h : Sha2InputArith (K := K) (K' := K') (κ := κ) (κ' := κ') p) :
    Sha2Vanishing (K := K) (K' := K') p κ κ' :=
  sha2Vanishing_of_sha2Input (K := K) (K' := K') (κ := κ) (κ' := κ') p
    (sha2Input_of_arithInput (K := K) (K' := K') (κ := κ) (κ' := κ') p h)

end Arithmetic

end NK.HassePrinciple
