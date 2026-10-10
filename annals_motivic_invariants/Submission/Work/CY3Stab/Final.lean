import Submission.Work.CY3Stab.Main
import Submission.Work.CY3Stab.LinkInput
import Submission.Work.CY3Stab.Prod.exists_cInv_ne_zero_of_CY3Data

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.CY3Stab.Final` — Theorem 1.2 (3) for `n ≥ 5`, closed from the two named inputs

The stabilisation `Cr 5 → Cr n` is *proved* in this directory
(`Submission/Work/CY3Stab/Main.lean`, `ProdCoeff.lean`, `Prod/`), and the paper's geometric input
that it consumes — that the two exceptional divisors of the link are `ℙ¹`-bundles over the two
`K`-trivial centres — is a field of `Work.CY3.CY3Data` (`p1Bundle_y`, `p1Bundle_x`), supplied by the
`G₂` producer (`Work.G2.CY3DatumZ.p1Bundle_bc`, `p1Bundle_bc'`).  Hence:

* `Work.CY3Stab.not_gen_of_CY3_infiniteField` — **Theorem 1.2 (3) for `n ≥ 5` from
  `Work.CY3.CY3Input` and `Work.CY3.TotaroInput` alone**: the exit criterion of this chapter;
* `Work.CY3Stab.not_gen_of_CY3_infiniteField_of_p1Bundle` — the same with the clause
  `Work.CY3Stab.CY3P1Bundle 𝕜 I.data` still explicit (the form for a producer that does not supply
  the two fields of `CY3Data`);
* `Work.CY3Stab.cy3Stabilisation_of_prodStab''` — `Work.CY3.CY3Stabilisation 𝕜 n` from the
  `∀`-form residual `Work.CY3Stab.ProdStab 𝕜 (n - 5)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

namespace Work.CY3Stab

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

noncomputable section

/-- **Theorem 1.2 (3) of the challenge for `n ≥ 5`, from the two named inputs and the `ℙ¹`-bundle
structure of the link.**  The stabilisation itself is proved in this directory; the only remaining
input is the paper's fact `CY3P1Bundle` that the two exceptional divisors of the CY3 link are
`ℙ¹`-bundles over the two centres. -/
theorem not_gen_of_CY3_infiniteField_of_p1Bundle {n : ℕ} (hn : 5 ≤ n) (𝕜 : Type) [Field 𝕜]
    [Infinite 𝕜] (I : Work.CY3.CY3Input 𝕜) (T : Work.CY3.TotaroInputAt 𝕜 I.data.Z I.data.Z')
    (F : CY3P1Bundle 𝕜 I.data) : ¬ GenByPseudoRegularizable 𝕜 n :=
  Work.Motivic.not_gen_of_cInv_ne_zero 𝕜 n
    (Work.CY3Stab.Prod.exists_cInv_ne_zero_of_CY3Data hn 𝕜 I.data T I.notIso F)

/-- **Theorem 1.2 (3) of the challenge for `n ≥ 5`, from the two named inputs alone — the exit
criterion of this chapter.**

Nothing is assumed beyond `Work.CY3.CY3Input 𝕜` (the `thm:CY3` construction, produced by the `G₂`
area for every infinite field) and `Work.CY3.TotaroInput 𝕜` (Totaro's `thm:BurtCY`/`cor-CYnSB`):
the stabilisation `c(φ × id_W) ≠ 0` is *proved* in this directory, and the paper's geometric input
that it needs — that the two exceptional divisors of the link are `ℙ¹`-bundles over the two centres
— is now a field of `Work.CY3.CY3Data` (`p1Bundle_y`, `p1Bundle_x`, produced by
`Work.G2.CY3DatumZ.p1Bundle_bc`, `p1Bundle_bc'`). -/
theorem not_gen_of_CY3_infiniteField {n : ℕ} (hn : 5 ≤ n) (𝕜 : Type) [Field 𝕜] [Infinite 𝕜]
    (I : Work.CY3.CY3Input 𝕜) (T : Work.CY3.TotaroInputAt 𝕜 I.data.Z I.data.Z') :
    ¬ GenByPseudoRegularizable 𝕜 n :=
  not_gen_of_CY3_infiniteField_of_p1Bundle hn 𝕜 I T
    ⟨I.data.p1Bundle_y, I.data.p1Bundle_x⟩

/-- The CY3 chapter's named input `Work.CY3.CY3Stabilisation 𝕜 n`, proved from the residual
`ProdStab` (see `Submission/Work/CY3Stab/NOTES.md`). -/
theorem cy3Stabilisation_of_prodStab'' {n : ℕ} (hn : 5 ≤ n) (𝕜 : Type) [Field 𝕜]
    (S : ProdStab 𝕜 (n - 5)) : Work.CY3.CY3Stabilisation 𝕜 n :=
  cy3Stabilisation_of_prodStab' hn S

end

end Work.CY3Stab
