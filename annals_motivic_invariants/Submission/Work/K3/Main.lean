import Submission.Work.K3.Defs
import Submission.Work.K3.K3Link
import Submission.Work.K3.HL
import Submission.Work.K3.BaseChange
import Submission.Work.K3.baseChange_map_isOver
import Submission.Work.K3.baseChange_map_isIso
import Submission.Work.K3.baseChange_isoOver
import Submission.Work.K3.baseChange_comp
import Submission.Work.K3.baseChangeMap_id
import Submission.Work.K3.baseChangeMap_comp
import Submission.Work.K3.baseChange_id
import Submission.Work.K3.baseChange_affineSpace
import Submission.Work.K3.BaseChangeBirational
import Submission.Work.K3.partialMap_baseChangeAlong_equiv
import Submission.Work.K3.partialIso_baseChangeAlong
import Submission.Work.K3.partialIso_baseChangeAlong_symm
import Submission.Work.K3.birationalMap_baseChangeAlong
import Submission.Work.K3.isIsoAt_baseChangeAlong
import Submission.Work.K3.pointBaseChange
import Submission.Work.K3.Descent
import Submission.Work.K3.Uniform
import Submission.Work.Motivic.not_gen_of_cInv_ne_zero

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.K3` — the K3 L-link area: the `n ≥ 4` case of Theorem 1.2 (2) (paper `thm:K3`)

Single entry point of the K3 area of `annals_motivic_invariants`.  `import
Submission.Work.K3.Main` brings in everything: the vocabulary, the L-link and its invariant
coefficient `1`, the named Hassett–Lai / Terasoma / Totaro inputs, the base-change machinery and
the descent step, and the two target statements.

## The main results

* `Work.K3.exists_cInv_ne_zero_kSubC` — **the `n = 4` shape**: for every subfield `𝕜 ⊆ ℂ`, given
  the named inputs, there is a Cremona transformation of `𝔸⁴` over `𝕜` with non-vanishing
  invariant coefficient;
* `Work.K3.not_gen_of_K3_kSubC` — the same, wired to `GenByPseudoRegularizable 𝕜 4`;
* `Work.K3.not_gen_of_K3_kSubC_of_le` — the same for `n ≥ 4`, from the (named) stabilisation of
  the link, i.e. the paper's `c(φ × id_W)` step;
* `Work.K3.K3Link.inv_eq_one`, `Work.K3.K3Link.inv_ne_zero` — the computation of the invariant
  coefficient of the K3 L-link, transported to `𝔸⁴` (`Cr 𝕜 4`);
* `Work.K3.HLDescent.notIso` — the descent step: the two centres of the `𝕜`-model are
  non-isomorphic over `𝕜` (from `S_ℂ ≄ S'_ℂ` by base change).

## Import

`import Submission.Work.K3.Main`.

## The named inputs (see `NOTES.md` for the exact interface)

`Work.K3.exists_cInv_ne_zero_kSubC` has **three** hypotheses: the arithmetic input `T`, the
Hassett–Lai geometry `h` over `ℚ` and Totaro's input at `𝕜`.  The `𝕜`-model of the `ℚ`-link — the
descent step of `thm-HL` — is no longer an input: it is built from `h` by base change in
`Submission/Work/K3/Uniform.lean` (`Work.K3.HassettLaiTheorem.toHLDescent`), together with the
proof that its two exceptional divisors are the base changes of the `ℚ`-model's
(`Work.K3.exDiv_psiBC`, `Work.K3.exDiv_psiBC_symm`) and that its two centres are non-isomorphic
over `𝕜` (`Work.K3.HLDescent.notIso`, from `S_ℂ ≄ S'_ℂ`).  The geometric residue is now
concentrated in the base-change-uniform clauses of `HassettLaiTheorem` (see `NOTES.md` §6).

| input | module | paper |
|---|---|---|
| `Work.K3.HLAdmissible` | `Submission/Work/K3/HL.lean` | HL-admissible pair `(S, Σ)` |
| `Work.K3.TerasomaInput` | `Submission/Work/K3/HL.lean` | `lem:HL-admis-pencil` + Terasoma + `pro-K3HLPic1` |
| `Work.K3.HassettLaiTheorem` | `Submission/Work/K3/HL.lean` | `thm-HL`(1)–(4) over `ℚ` + `S_ℂ ≄ S'_ℂ` |
| `Work.K3.HLDescent` | `Submission/Work/K3/HL.lean` + `…/Uniform.lean` | `thm-HL`, "defined over `k`" (the descent) — an *interface*, **constructed** by `Work.K3.HassettLaiTheorem.toHLDescent` |
| `Work.K3.TotaroInput` | `Submission/Work/K3/HL.lean` | `thm:BurtCY`, `cor-CYnSB` |
| `Work.K3.K3Stabilisation` | `Submission/Work/K3/Main.lean` | `c(φ × id_W) ≠ 0` for `W = 𝔸^{n-4}` |
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral
attribute [instance] Work.K3.TerasomaInput.varietyS Work.K3.TerasomaInput.overSigma
  Work.K3.TerasomaInput.isOverSigma Work.K3.HassettLaiTheorem.overSigma'
  Work.K3.HassettLaiTheorem.isOverSigma' Work.K3.K3Data.varietyS
  Work.K3.K3Data.varietyS' Work.K3.K3Data.varietyP

namespace Work.K3

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

/-! ## The `n = 4` target -/

/-- **The `n = 4` shape of Theorem 1.2 (2) of the challenge.**

For every subfield `𝕜 ⊆ ℂ`, from the three named inputs of Theorem `thm:K3` (the arithmetic input
`T`, the Hassett–Lai geometry `h` over `ℚ` — including its base-change-uniform clauses — and
Totaro's input at `𝕜`) there is a Cremona transformation `φ` of `𝔸⁴` over `𝕜` whose
`[κ(S)(t)]`-coefficient does not vanish.  The `𝕜`-model of the link is *produced* from the
`ℚ`-model by base change (`Work.K3.HassettLaiTheorem.toHLDescent`,
`Submission/Work/K3/Uniform.lean`).  This is exactly the existential consumed by
`Work.Motivic.not_gen_of_cInv_ne_zero`. -/
theorem exists_cInv_ne_zero_kSubC (𝕜 : Subfield ℂ) (T : TerasomaInput) (h : HassettLaiTheorem T)
    (Tt : TotaroInputAt 𝕜 (toHLDescent h 𝕜).data.S (toHLDescent h 𝕜).data.S') :
    ∃ (Z : Scheme.{0}) (_ : Z.Over (Spec (.of 𝕜))) (z₀ : Z) (φ : Cr 𝕜 4),
      cInv 𝕜 z₀ (φ : (Affine4 𝕜).BirationalMap (Affine4 𝕜)) ≠ 0 :=
  (toHLDescent h 𝕜).exists_cInv_ne_zero Tt

/-- **Theorem 1.2 (2) of the challenge at `n = 4`**: `Cr₄(𝕜)` is not generated by
pseudo-regularizable elements, for every subfield `𝕜 ⊆ ℂ`. -/
theorem not_gen_of_K3_kSubC (𝕜 : Subfield ℂ) (T : TerasomaInput) (h : HassettLaiTheorem T)
    (Tt : TotaroInputAt 𝕜 (toHLDescent h 𝕜).data.S (toHLDescent h 𝕜).data.S') :
    ¬ GenByPseudoRegularizable 𝕜 4 :=
  Work.Motivic.not_gen_of_cInv_ne_zero 𝕜 4 (exists_cInv_ne_zero_kSubC 𝕜 T h Tt)

/-! ## Stabilisation to `n ≥ 4` -/

/-- **Named input: the stabilisation of the K3 link to `Cr 𝕜 n`, `n ≥ 4`.**

The paper's proof of Theorem `thm:bir-generation` (b) stabilises the `ℙ⁴`-link to
`ℙ⁴ × W` (`W = 𝔸^{n-4}` is separably rationally connected): one uses
`c(φ × id_W) = [S × ℙ¹ × W] − [S' × ℙ¹ × W]`, whose `[κ(S)(t)(W)]`-coefficient is again `1`.
Formally this is the passage from the `Cr 𝕜 4`-coefficient to the `Cr 𝕜 n`-coefficient of
`φ × id` — a statement about the exceptional divisors of a product map, which we record as a
named input. -/
structure K3Stabilisation (𝕜 : Type) [Field 𝕜] (n : ℕ) : Prop where
  /-- a non-vanishing coefficient in `Cr 𝕜 4` yields one in `Cr 𝕜 n` -/
  stabilise : (∃ (Z : Scheme.{0}) (_ : Z.Over (Spec (.of 𝕜))) (z₀ : Z) (φ : Cr 𝕜 4),
      cInv 𝕜 z₀ (φ : (Affine4 𝕜).BirationalMap (Affine4 𝕜)) ≠ 0) →
    ∃ (Z : Scheme.{0}) (_ : Z.Over (Spec (.of 𝕜))) (z₀ : Z) (φ : Cr 𝕜 n),
      cInv 𝕜 z₀ (φ : 𝔸(Fin n; Spec (.of 𝕜)).BirationalMap
        (𝔸(Fin n; Spec (.of 𝕜)))) ≠ 0

/-- **Theorem 1.2 (2) of the challenge for `n ≥ 4`**, from the `n = 4` statement and the
stabilisation input. -/
theorem not_gen_of_K3_kSubC_of_le {n : ℕ} (hn : 4 ≤ n) (𝕜 : Subfield ℂ) (T : TerasomaInput)
    (h : HassettLaiTheorem T)
    (Tt : TotaroInputAt 𝕜 (toHLDescent h 𝕜).data.S (toHLDescent h 𝕜).data.S')
    (S : K3Stabilisation 𝕜 n) : ¬ GenByPseudoRegularizable 𝕜 n :=
  Work.Motivic.not_gen_of_cInv_ne_zero 𝕜 n
    (S.stabilise (exists_cInv_ne_zero_kSubC 𝕜 T h Tt))

end Work.K3
