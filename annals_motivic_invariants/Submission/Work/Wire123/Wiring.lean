import Submission.Work.Wire123.Chain
import Submission.Work.Wire123.CubicObstruction

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.Wire123.Wiring` — the wiring of Theorem 1.2 (3), and what it is blocked on

This module states the wiring of `Submission.MotivicInvariants.theorem_1_2_3` — the challenge's
`n ≥ 5` case over an infinite field — in the three forms in which a producer can supply it:

| form | producer must supply |
|---|---|
| `Work.Wire123.not_gen_of_CY3Residual` | a CY3 L-link datum with non-stably-birational centres (`thm:CY3` + `lem-nSBG2`) |
| `Work.Wire123.not_gen_of_G2_sep` | the `ℤ`-model `Work.G2.CY3DatumZ` plus the per-pair separation of its two centres |
| `Work.Wire123.not_gen_of_G2_repaired` | the `ℤ`-model, the repaired cubic interface with its two values `14`, `42` (`lem-nSBG2`, first half) and Totaro's input *at the pair* (`cor-CYnSB`) |

and the theorem whose shape is *character-identical* to the challenge statement,
`Work.Wire123.theorem_1_2_3_of_residual`, so that the wiring of
`Submission.MotivicInvariants.theorem_1_2_3` is a one-liner the moment a term of
`Work.Wire123.CY3Residual 𝕜` exists.

## Why the delivered route is blocked, and why it is blocked *twice*

The delivered reduction `Work.CY3Stab.theorem_1_2_3_of_G2 hn 𝕜 M C T` has two inputs that no
producer can ever supply, and this independently of the `ℤ`-model `M`:

* `C : Work.G2.CubicInput 𝕜` is **refutable** (`Work.Wire123.not_legacyCubicInput`): the fieldless class
  `Work.G2.CubicSelfIntersection` admits *every* value `n`, so the `unique` clause gives `0 = 1`.
  The repaired interface is `Work.Wire123.CubicInvariant` — a *function* `cubic` with its
  isomorphism-invariance, whose two values at the two centres are the geometric input
  (`Work.Wire123.CubicInvariant.notIso_centres`), which is how `lem-nSBG2` actually reads.
* `T : Work.CY3.TotaroInput 𝕜` quantifies over *all* pairs of `𝕜`-varieties whose (fieldless)
  named predicates are automatic, i.e. it asserts that non-isomorphic varieties are never stably
  birational; see `Submission/Work/Wire123/not_totaroInput.lean`.  The repaired interface is
  `Work.Wire123.TotaroInputAt 𝕜 Z Z'` / `Work.Wire123.CentreSeparation 𝕜 D` — Totaro's statement
  at the pair of centres, which is what the paper's `cor-CYnSB` provides and what the counting in
  `Work.CY3Stab` consumes.

With the interfaces repaired, the whole chain is proved:
`Work.Wire123.not_gen_of_G2_repaired` is the paper's argument `14 ≠ 42` (`lem-nSBG2`, first half),
`cor-CYnSB` at the two centres (second half), `thm:CY3` for the datum (`M.toCY3Data`), and then the
delivered coefficient computation and `W`-stabilisation.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

namespace Work.Wire123

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

noncomputable section

variable {𝕜 : Type} [Field 𝕜]

/-! ## 1. The challenge statement from the residual -/

/-- **Theorem 1.2 (3) of the challenge for `n ≥ 5`, in the challenge's shape, from the residual
`Work.Wire123.CY3Residual 𝕜`.**

The binders are those of `Submission.MotivicInvariants.theorem_1_2_3` (with `𝕜` explicit, as in
`Work.CY3Stab.theorem_1_2_3_of_G2`), so that the wiring line

```lean
theorem theorem_1_2_3 {n : ℕ} (hn : 5 ≤ n) [Infinite 𝕜] : ¬ GenByPseudoRegularizable 𝕜 n :=
  Work.Wire123.theorem_1_2_3_of_residual hn 𝕜 R
```

is available as soon as `R : Work.Wire123.CY3Residual 𝕜` exists. -/
theorem theorem_1_2_3_of_residual {n : ℕ} (hn : 5 ≤ n) (𝕜 : Type) [Field 𝕜] [Infinite 𝕜]
    (R : CY3Residual 𝕜) : ¬ GenByPseudoRegularizable 𝕜 n :=
  not_gen_of_CY3Residual hn 𝕜 R

/-! ## 2. From the `ℤ`-model of the `G₂` area -/

/-- **Theorem 1.2 (3) of the challenge for `n ≥ 5`, from the `ℤ`-model and the per-pair form of
Totaro's theorem at its two centres.**

This is the wiring `Work.CY3Stab.theorem_1_2_3_of_G2 hn 𝕜 M C T` *intends*: the model `M` supplies
the CY3 datum `M.toCY3Data 𝕜` (`thm:CY3`), and the single remaining geometric input is the
conclusion of `cor-CYnSB` at the two centres of the model — which the paper obtains from the
non-isomorphism of the centres (`lem-nSBG2`, whence `14 ≠ 42`) and Totaro's theorem.  No
`Work.G2.CubicInput` and no universal `Work.CY3.TotaroInput` appears. -/
theorem not_gen_of_G2_sep {n : ℕ} (hn : 5 ≤ n) (𝕜 : Type) [Field 𝕜] [Infinite 𝕜]
    (M : Work.G2.CY3DatumZ)
    (hsep : ¬ Work.CY3.StablyBirational 𝕜 (Work.G2.baseChangeZ 𝕜 M.ZZ')
      (Work.G2.baseChangeZ 𝕜 M.ZZ)) : ¬ GenByPseudoRegularizable 𝕜 n :=
  not_gen_of_CY3Data_sep hn 𝕜 (M.toCY3Data 𝕜) hsep

/-- The same, with the hypothesis written on the datum `M.toCY3Data 𝕜` itself (`rfl`-equivalent to
the form above, and the form in which a producer of the model will state it). -/
theorem not_gen_of_G2_sep' {n : ℕ} (hn : 5 ≤ n) (𝕜 : Type) [Field 𝕜] [Infinite 𝕜]
    (M : Work.G2.CY3DatumZ) (hsep : CentreSeparation 𝕜 (M.toCY3Data 𝕜)) :
    ¬ GenByPseudoRegularizable 𝕜 n :=
  not_gen_of_CY3Data_sep hn 𝕜 (M.toCY3Data 𝕜) hsep

/-- **Theorem 1.2 (3) of the challenge for `n ≥ 5`, from the `ℤ`-model and the paper's two
half-arguments at its two centres**, with both broken interfaces of the delivered chain repaired:

* `C : CubicInvariant 𝕜` with `C.cubic` the cubic self-intersection `c₁(M|_X)³`, invariant under
  isomorphism, and its two values `14`, `42` at the two centres — `lem-nSBG2`'s discriminant
  computation (Ito–Miura–Okawa–Ueda), which yields `¬ IsoOver 𝕜 Z Z'` by `14 ≠ 42`
  (`Work.Wire123.CubicInvariant.notIso_centres`);
* `T : TotaroInputAt 𝕜 Z Z'` — Totaro's `thm:BurtCY`/`cor-CYnSB` at the pair of centres
  (non-isomorphic `K`-trivial varieties of Picard rank one are not stably birational).

This is the largest part of `thm:CY3` that can be stated without the `G₂` group scheme and the
blow-ups themselves: everything else in the chain is proved. -/
theorem not_gen_of_G2_repaired {n : ℕ} (hn : 5 ≤ n) (𝕜 : Type) [Field 𝕜] [Infinite 𝕜]
    (M : Work.G2.CY3DatumZ) (C : CubicInvariant 𝕜)
    (hZ : C.cubic (Work.G2.baseChangeZ 𝕜 M.ZZ) = 14)
    (hZ' : C.cubic (Work.G2.baseChangeZ 𝕜 M.ZZ') = 42)
    (T : TotaroInputAt 𝕜 (Work.G2.baseChangeZ 𝕜 M.ZZ) (Work.G2.baseChangeZ 𝕜 M.ZZ')) :
    ¬ GenByPseudoRegularizable 𝕜 n := by
  refine not_gen_of_G2_sep hn 𝕜 M (fun hsb => ?_)
  exact T.not_stablyBirat (C.notIso_centres M hZ hZ') (Work.Totaro.stablyBirational_symm hsb)

/-- **The wiring with the `G₂` repair *landed***: the challenge theorem for `n ≥ 5` from the
`ℤ`-model, the (now consistent) `Work.G2.CubicInput 𝕜` and Totaro's input *at the pair of the two
centres*.

This is the strongest form of the reduction in this workspace: `Work.G2.CubicInput` now carries the
*function* `X ↦ c₁(M|_X)³` (repaired in `G2/Defs.lean`, see `Submission/Work/Wire123/CubicObstruction.lean`),
the two values `14`, `42` at the two centres are hypotheses on the cubic input (they were fields
`Work.G2.CY3DatumZ.cubic_Z`, `cubic_Z'` of the model until the authorised repair deleted them; see
`Verdict.lean`), and the only remaining input is Totaro's `cor-CYnSB` at
the pair `(ZZ_𝕜, ZZ'_𝕜)`.  (For the composite to be *wired* into the challenge, it remains to
produce `M`, `C` and the pair statement; see `NOTES.md` §5–§5ter for what that requires.) -/
theorem not_gen_of_G2_of_cubicInput_inputAt {n : ℕ} (hn : 5 ≤ n) (𝕜 : Type) [Field 𝕜]
    [Infinite 𝕜] (M : Work.G2.CY3DatumZ) (C : Work.G2.CubicInput 𝕜)
    (hZ : C.cubic (Work.G2.baseChangeZ 𝕜 M.ZZ) = 14)
    (hZ' : C.cubic (Work.G2.baseChangeZ 𝕜 M.ZZ') = 42)
    (T : TotaroInputAt 𝕜 (Work.G2.baseChangeZ 𝕜 M.ZZ) (Work.G2.baseChangeZ 𝕜 M.ZZ')) :
    ¬ GenByPseudoRegularizable 𝕜 n := by
  refine not_gen_of_G2_sep hn 𝕜 M (fun hsb => ?_)
  exact T.not_stablyBirat (M.notIso 𝕜 C hZ hZ') (Work.Totaro.stablyBirational_symm hsb)

/-- **The delivered reduction, restated as the compatibility check of this module**:
`Work.CY3Stab.theorem_1_2_3_of_G2` — the form the lead wires — is the present chain with the
universal `Work.CY3.TotaroInput` in place of the per-pair one.  After the interface repair of
`PATCH.md` the model no longer carries the two cubic values (`hZ`, `hZ'` are hypotheses on the
consumer's `C`), so this declaration differs from `not_gen_of_G2_repaired` only in that its Totaro
input is the universal — and refutable — `Work.CY3.TotaroInput` (`Work.Wire123.not_totaroInput`). -/
theorem not_gen_of_G2_of_cubicInput {n : ℕ} (hn : 5 ≤ n) (𝕜 : Type) [Field 𝕜] [Infinite 𝕜]
    (M : Work.G2.CY3DatumZ) (C : Work.G2.CubicInput 𝕜)
    (hZ : C.cubic (Work.G2.baseChangeZ 𝕜 M.ZZ) = 14)
    (hZ' : C.cubic (Work.G2.baseChangeZ 𝕜 M.ZZ') = 42) (T : Work.CY3.TotaroInput 𝕜) :
    ¬ GenByPseudoRegularizable 𝕜 n :=
  Work.CY3Stab.theorem_1_2_3_of_G2 hn 𝕜 M C hZ hZ'
    (T.toInputAt 𝕜 (M.isKTrivial_bc 𝕜) (M.isKTrivial_bc' 𝕜) (M.picardOne_bc 𝕜)
      (M.picardOne_bc' 𝕜))

end

end Work.Wire123
