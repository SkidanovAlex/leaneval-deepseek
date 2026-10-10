import Submission.Work.Wire123.Defs
import Submission.Work.Wire123.exists_cInv_ne_zero_of_CY3Data_sep

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.Wire123.Chain` — Theorem 1.2 (3) for `n ≥ 5` from the CY3 datum alone

This module proves the last formal step of the `n ≥ 5` case of Theorem 1.2 (3) of the challenge:

```
  Work.CY3.CY3Data 𝕜  +  ¬ StablyBirational 𝕜 Z' Z   ⟹   ¬ GenByPseudoRegularizable 𝕜 n   (n ≥ 5)
```

with no further named input.  The first hypothesis is the paper's `thm:CY3` (the `G₂`-Grassmannian
L-link with its two `K`-trivial threefolds of Picard rank one, recorded as the datum
`Work.CY3.CY3Data` of `Submission/Work/CY3/Link.lean`), the second is the conclusion of Totaro's
`cor-CYnSB` at the two centres — the paper's `lem-nSBG2`.  Both are *consistent* statements about
*specific* varieties, unlike the universal named inputs of the delivered chain
(`Submission/Work/Wire123/NOTES.md`).

Everything between them — the `ℙ¹`-bundle bridge, the residue-field comparison, the counting of the
exceptional divisors, the affine transports and the `W`-stabilisation `Cr 5 → Cr n` — is proved in
the delivered chapters, in `Work.Wire123.exists_cInv_ne_zero_of_CY3Data_sep` (the per-pair form of
`Work.CY3Stab.Prod.exists_cInv_ne_zero_of_CY3Data`) and `Work.Motivic.not_gen_of_cInv_ne_zero`.
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

/-- **Theorem 1.2 (3) of the challenge for `n ≥ 5`, from a CY3 datum with non-stably-birational
centres.**  This is `Work.CY3Stab.theorem_1_2_3` with `Work.CY3.TotaroInput 𝕜` replaced by its
value at the two centres of the datum: the universal named input is not instantiable (it quantifies
over all `𝕜`-varieties, with its geometric hypotheses carried by the fieldless classes
`Work.CY3.IsKTrivial`, `Work.CY3.PicardRankOne`; see `Submission/Work/Wire123/NOTES.md`), while the
per-pair statement is exactly what the paper's `lem-nSBG2` proves.

Note that no `Infinite 𝕜` hypothesis is needed: the only use of infinitude in the paper is Bertini,
which is a field of the datum. -/
theorem not_gen_of_CY3Data_sep {n : ℕ} (hn : 5 ≤ n) (𝕜 : Type) [Field 𝕜]
    (D : Work.CY3.CY3Data 𝕜) (hsep : CentreSeparation 𝕜 D) :
    ¬ GenByPseudoRegularizable 𝕜 n :=
  Work.Motivic.not_gen_of_cInv_ne_zero 𝕜 n
    (exists_cInv_ne_zero_of_CY3Data_sep hn 𝕜 D hsep ⟨D.p1Bundle_y, D.p1Bundle_x⟩)

/-- **Theorem 1.2 (3) for `n ≥ 5` from the residual `Work.Wire123.CY3Residual 𝕜`** — the form in
which the wiring into `Submission.MotivicInvariants.theorem_1_2_3` is a one-liner, once a producer
of the residual exists. -/
theorem not_gen_of_CY3Residual {n : ℕ} (hn : 5 ≤ n) (𝕜 : Type) [Field 𝕜]
    (R : CY3Residual 𝕜) : ¬ GenByPseudoRegularizable 𝕜 n :=
  let ⟨D, h⟩ := R
  not_gen_of_CY3Data_sep hn 𝕜 D h

/-- **Faithfulness of the per-pair form**: the delivered
`Work.CY3Stab.Prod.exists_cInv_ne_zero_of_CY3Data` (which takes the universal `TotaroInput` and the
non-isomorphism of the centres) is a special case of
`Work.Wire123.exists_cInv_ne_zero_of_CY3Data_sep`.  Its `hcancel` step is exactly the application
`T.not_stablyBirat_of_not_iso` producing the per-pair statement. -/
theorem exists_cInv_ne_zero_of_CY3Data_of_totaroInput {n : ℕ} (hn : 5 ≤ n) (𝕜 : Type) [Field 𝕜]
    (D : Work.CY3.CY3Data 𝕜) (T : Work.CY3.TotaroInput 𝕜)
    (h : ¬ Work.CY3.IsoOver 𝕜 D.Z D.Z') (F : Work.CY3Stab.CY3P1Bundle 𝕜 D) :
    ∃ (Z : Scheme.{0}) (_ : Z.Over (Spec (.of 𝕜))) (z₀ : Z) (φ : Cr 𝕜 n),
      cInv 𝕜 z₀ (φ : (Work.CY3.Affine 𝕜 n).BirationalMap (Work.CY3.Affine 𝕜 n)) ≠ 0 :=
  exists_cInv_ne_zero_of_CY3Data_sep hn 𝕜 D
    (fun hsb => T.not_stablyBirat_of_not_iso D.Z' D.Z D.isKTrivial_Z' D.isKTrivial_Z
      D.picardOne_Z' D.picardOne_Z (fun hh => h (Work.K3.IsoOver.symm hh)) hsb) F

/-- The two-centre separation of a CY3 datum implies the non-isomorphism of its centres (the
converse is Totaro's theorem): the two forms of `lem-nSBG2` are the two halves of the same
input, and the per-pair separation is the *stronger* one. -/
theorem CentreSeparation.not_isoOver {D : Work.CY3.CY3Data 𝕜} (h : CentreSeparation 𝕜 D) :
    ¬ Work.CY3.IsoOver 𝕜 D.Z' D.Z :=
  fun hh => h (Work.Totaro.StablyBirational_of_isoOver hh)

end

end Work.Wire123
