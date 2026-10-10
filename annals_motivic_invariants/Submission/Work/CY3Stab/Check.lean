import Submission.Work.CY3Stab.Final
import Submission.Work.G2.Main

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.CY3Stab.Check` — the check module of the CY3 stabilisation chapter

This module contains the **challenge-shaped** statements of Theorem 1.2 (3) for `n ≥ 5`
(`MotivicInvariants.theorem_1_2_3` in `Challenge.lean`, whose `Solution.lean` bridge is
`Submission.MotivicInvariants.theorem_1_2_3`).  The main one,
`Work.CY3Stab.theorem_1_2_3`, takes **only** the two named inputs of the CY3 chapter
(`Work.CY3.CY3Input`, `Work.CY3.TotaroInput`); there is no stabilisation input left.

## What the lead needs to import

```lean
import Submission.Work.CY3Stab.Check
```

* `Work.CY3Stab.theorem_1_2_3` — the closed form: `(hn : 5 ≤ n) → (𝕜) → [Field 𝕜] →
  [Infinite 𝕜] → Work.CY3.CY3Input 𝕜 → Work.CY3.TotaroInput 𝕜 → ¬ GenByPseudoRegularizable 𝕜 n`;
* `Work.CY3Stab.theorem_1_2_3_of_G2` — the same on the `G₂` model: `Work.G2.CY3DatumZ →
  Work.G2.CubicInput 𝕜 → (the two cubic self-intersection values `14`, `42` of that input at the
  model's two centres) → Work.CY3.TotaroInput 𝕜 → ¬ GenByPseudoRegularizable 𝕜 n` (the two values
  became hypotheses of the consumer's cubic input in the interface repair of
  `Submission/Work/Wire123/PATCH.md`; they were fields of the model, whose `∀ C` shape was
  refutable).  This is the
  form to wire into `Submission.MotivicInvariants.theorem_1_2_3`; it is
  `Work.G2.not_gen_of_G2_infiniteField` with the `(S : Work.CY3.CY3Stabilisation 𝕜 n)` argument
  **discharged**;
* `Work.CY3Stab.theorem_1_2_3_of_p1Bundle` — the same from the two named inputs and the explicit
  clause `Work.CY3Stab.CY3P1Bundle 𝕜 I.data` (the paper's (F1) for the link);
* `Work.CY3Stab.theorem_1_2_3_of_prodStab` — the same with the `∀`-form residual
  `Work.CY3Stab.ProdStab 𝕜 (n - 5)` instead (the two `Variety`-structure and strong-birationality
  interface hypotheses of the earlier round are now *proved* in this directory and no longer
  appear).

## Wiring to the challenge

`Submission.MotivicInvariants.theorem_1_2_3 (𝕜) (hn : 5 ≤ n) : ¬ GenByPseudoRegularizable 𝕜 n`
is `Work.CY3Stab.theorem_1_2_3_of_G2 hn 𝕜 M C T` with

* `Work.CY3.CY3Input 𝕜` from the `G₂`-area (`Work.G2.CY3DatumZ.toCY3Input`, for every infinite
  field) — or directly the `ℤ`-model `M : Work.G2.CY3DatumZ` and the cubic input
  `C : Work.G2.CubicInput 𝕜`;
* `Work.CY3.TotaroInput 𝕜` from the Totaro area (`Work.Totaro.totaroInput_CY3`, from the
  cohomological input, or `Work.Totaro.totaroInput_CY3_of_CorCYnSB`, from the paper's corollary).

See `Submission/Work/CY3Stab/NOTES.md` §6, and §4 for the interface change that made the
(unconditional) closure possible.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

namespace Work.CY3Stab

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

noncomputable section

variable {𝕜 : Type} [Field 𝕜]

/-- **Theorem 1.2 (3) of the challenge for `n ≥ 5`**, in the challenge's shape: from the `thm:CY3`
construction (`Work.CY3.CY3Input`), Totaro's theorem (`Work.CY3.TotaroInput`) and the named
residual `ProdStab 𝕜 (n - 5)` of the stabilisation.  The `Variety` structure on the cylinder and
the strong birationality of the identification `𝔸^{n-5} × 𝔸⁵ ≅ 𝔸ⁿ` are *proved* in this directory
(`Work.CY3Stab.varietyWProd`, `Work.CY3Stab.Prod.stronglyBirational_wProd_affine`) and are
discharged in `Work.CY3Stab.not_gen_of_CY3_infiniteField_of_prodStab`. -/
theorem theorem_1_2_3_of_prodStab {n : ℕ} (hn : 5 ≤ n) (𝕜 : Type) [Field 𝕜] [Infinite 𝕜]
    (I : Work.CY3.CY3Input 𝕜) (T : Work.CY3.TotaroInputAt 𝕜 I.data.Z I.data.Z')
    (S : ProdStab 𝕜 (n - 5)) :
    ¬ GenByPseudoRegularizable 𝕜 n :=
  not_gen_of_CY3_infiniteField_of_prodStab hn 𝕜 I T S

/-- **Theorem 1.2 (3) for `n ≥ 5`, closed from the two named inputs and the (F1)-structure of the
link.**  This is the form for the lead's wiring: no stabilisation input remains — only the paper's
fact that the two exceptional divisors of the link are `ℙ¹`-bundles over the two centres
(`Work.CY3Stab.CY3P1Bundle`). -/
theorem theorem_1_2_3_of_p1Bundle {n : ℕ} (hn : 5 ≤ n) (𝕜 : Type) [Field 𝕜] [Infinite 𝕜]
    (I : Work.CY3.CY3Input 𝕜) (T : Work.CY3.TotaroInputAt 𝕜 I.data.Z I.data.Z')
    (F : CY3P1Bundle 𝕜 I.data) :
    ¬ GenByPseudoRegularizable 𝕜 n :=
  not_gen_of_CY3_infiniteField_of_p1Bundle hn 𝕜 I T F

/-- **Theorem 1.2 (3) of the challenge for `n ≥ 5` in its final form, from the two named inputs
alone**: `Work.CY3.CY3Input 𝕜` (the `thm:CY3` construction) and `Work.CY3.TotaroInput 𝕜`
(Totaro's `thm:BurtCY`/`cor-CYnSB`).  This is the shape the lead wires into
`Submission.MotivicInvariants.theorem_1_2_3`. -/
theorem theorem_1_2_3 {n : ℕ} (hn : 5 ≤ n) (𝕜 : Type) [Field 𝕜] [Infinite 𝕜]
    (I : Work.CY3.CY3Input 𝕜) (T : Work.CY3.TotaroInputAt 𝕜 I.data.Z I.data.Z') :
    ¬ GenByPseudoRegularizable 𝕜 n :=
  not_gen_of_CY3_infiniteField hn 𝕜 I T

/-- **Theorem 1.2 (3) of the challenge for `n ≥ 5`, on the `G₂`-model** — the form in which the
`G₂`-area states the challenge (`Work.G2.not_gen_of_G2_infiniteField`), but with the stabilisation
input `Work.CY3.CY3Stabilisation` *discharged*: it takes only the `ℤ`-model, the cubic input and
Totaro's input.  Compare `Work.G2.not_gen_of_G2_infiniteField`, whose `(S : CY3Stabilisation 𝕜 n)`
is now unnecessary. -/
theorem theorem_1_2_3_of_G2 {n : ℕ} (hn : 5 ≤ n) (𝕜 : Type) [Field 𝕜] [Infinite 𝕜]
    (M : Work.G2.CY3DatumZ) (C : Work.G2.CubicInput 𝕜)
    (hZ : C.cubic (Work.G2.baseChangeZ 𝕜 M.ZZ) = 14)
    (hZ' : C.cubic (Work.G2.baseChangeZ 𝕜 M.ZZ') = 42)
    (T : Work.CY3.TotaroInputAt 𝕜 (Work.G2.baseChangeZ 𝕜 M.ZZ) (Work.G2.baseChangeZ 𝕜 M.ZZ')) :
    ¬ GenByPseudoRegularizable 𝕜 n :=
  not_gen_of_CY3_infiniteField hn 𝕜 (M.toCY3Input 𝕜 C hZ hZ') T

end

end Work.CY3Stab
