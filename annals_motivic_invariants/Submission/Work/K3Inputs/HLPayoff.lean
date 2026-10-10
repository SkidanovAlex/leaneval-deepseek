import Submission.Work.K3Inputs.HLItems
import Submission.Work.K3Inputs.StablyBiratK3
import Submission.Work.K3Inputs.Stabilisation
import Submission.Work.K3Inputs.exists_hassettLaiTheorem_of_HLInput
import Submission.Work.K3Inputs.CorCYnSB_to_totaroInput

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.K3Inputs.HLPayoff` — the item-level Hassett–Lai input and its ℚ-level payoff

`Work.K3Inputs.HLInput T` (see `Work.K3Inputs.HLItems`) carries every field of
`Work.K3.HassettLaiTheorem T` except the two ℙ¹-bundle bridges, which are replaced by their
geometric content: the clauses (F1) (`y_cylinder`, `x_cylinder`; base-change-uniform:
`y_cylinder_bc`, `x_cylinder_bc`) and (F2) (`cylinderRigid`, `cylinderRigid_bc`).

What is proved here (at the `ℚ`-level, where the paper's construction lives):

* `Work.K3Inputs.HLInput.notIso_rat` — the two centres are already non-isomorphic over `ℚ`: this is
  the contrapositive of base change of isomorphisms (`Work.K3.baseChange_isoOver`) applied to the
  geometric input `notIsoGeom : ¬ IsoOver ℂ (S_ℂ) (S'_ℂ)`;
* `Work.K3Inputs.HLInput.exists_cInv_ne_zero` — the non-vanishing invariant coefficient over `ℚ`,
  from the item-level input and Totaro's input, **with the ℙ¹-bundle bridge proved**
  (`Work.K3Inputs.LinkCore.bridge`, `Work.K3Inputs.exists_cInv_ne_zero_of_LinkCore`);
* `Work.K3Inputs.not_gen_four_of_HLInput`, `…_of_HLInput` — Theorem 1.2 (2) for `n = 4` and for
  `n ≥ 4` from the item-level input.

The *uniform* statement (assembling `Work.K3.HassettLaiTheorem` itself, i.e. replacing its clause
`bridge_bc` by (F1)/(F2) over every subfield) is not carried out here: the `Over`-structure of a
base change enters as *data* into the types of `IsP1BundleOver`/`SameCylinderField`/`CylinderRigid`
and of `Work.K3.StablyBirational`, two instances (`Work.K3.baseChangeOver` and
`MotivicInvariants.Variety.over`) are available for it, and instance search is not stable across
declarations; the clause types in `Work.K3Inputs.HLItems` fix `Work.K3.baseChangeOver` explicitly,
and the same discipline (explicit `Over`-arguments in `Cyl`/`StablyBirat` and in the witness of
`Work.K3.StablyBirational`) is what the assembly needs.  See `NOTES.md` §5.3.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral
attribute [instance] Work.K3.TerasomaInput.varietyS Work.K3.TerasomaInput.overSigma
  Work.K3.TerasomaInput.isOverSigma Work.K3Inputs.LinkCore.varietyS
  Work.K3Inputs.LinkCore.varietyS' Work.K3Inputs.LinkCore.varietyP

namespace Work.K3Inputs

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

noncomputable section

variable {T : Work.K3.TerasomaInput}

/-- **The two centres are non-isomorphic over `ℚ`.**  The geometric input `notIsoGeom` says that
their base changes to `ℂ` are non-isomorphic; base change of isomorphisms
(`Work.K3.baseChange_isoOver`) upgrades a `ℚ`-isomorphism to a `ℂ`-isomorphism, so the
contrapositive applies. -/
theorem HLInput.notIso_rat (h : HLInput T) : ¬ Work.K3.IsoOver ℚ h.core.S h.core.S' := fun hh =>
  h.notIsoGeom (Work.K3.baseChange_isoOver ℚ ℂ hh)

/-- **The `cInv` non-vanishing over `ℚ`, from the item-level Hassett–Lai input.**  The bridge of
the link datum is *proved* (`Work.K3Inputs.LinkCore.bridge`), so the only geometric inputs are the
clauses (F1), (F2) and Totaro's corollary. -/
theorem HLInput.exists_cInv_ne_zero (h : HLInput T)
    (Tt : Work.K3.TotaroInputAt ℚ h.core.S h.core.S') :
    ∃ (Z : Scheme.{0}) (_ : Z.Over (Spec (.of ℚ))) (z₀ : Z) (φ : Cr ℚ 4),
      cInv ℚ z₀ (φ : (Work.K3.Affine4 ℚ).BirationalMap (Work.K3.Affine4 ℚ)) ≠ 0 :=
  exists_cInv_ne_zero_of_LinkCore h.core Tt h.notIso_rat

end

/-- **Theorem 1.2 (2) of the challenge at `n = 4`**, from the item-level Hassett–Lai input and
Totaro's input (both over `ℚ`). -/
theorem not_gen_four_of_HLInput (T : Work.K3.TerasomaInput) (h : HLInput T)
    (Tt : Work.K3.TotaroInputAt ℚ h.core.S h.core.S') : ¬ GenByPseudoRegularizable ℚ 4 :=
  Work.Motivic.not_gen_of_cInv_ne_zero ℚ 4 (h.exists_cInv_ne_zero Tt)

/-- **Theorem 1.2 (2) of the challenge for `n ≥ 4`**, from the item-level Hassett–Lai input,
Totaro's input and the stabilisation step. -/
theorem not_gen_of_HLInput {n : ℕ} (hn : 4 ≤ n) (T : Work.K3.TerasomaInput) (h : HLInput T)
    (Tt : Work.K3.TotaroInputAt ℚ h.core.S h.core.S') (S : StabilisationStep ℚ n) :
    ¬ GenByPseudoRegularizable ℚ n :=
  Work.Motivic.not_gen_of_cInv_ne_zero ℚ n
    (S.stabilise (h.exists_cInv_ne_zero Tt))

/-! ## The `n ≥ 4` chain with both bridges proved -/

/-- The K3 chapter's geometric input, produced from the item-level clauses: the link datum with
the bridge `Work.K3.K3Data.bridge` proved (`Work.K3Inputs.LinkCore.toK3Data`) and the uniform
clause `bridge_bc` proved (`Work.K3Inputs.exists_hassettLaiTheorem_of_HLInput`). -/
noncomputable def HLInput.hassettLaiTheorem {T : Work.K3.TerasomaInput} (h : HLInput T) :
    Work.K3.HassettLaiTheorem T :=
  Classical.choice (exists_hassettLaiTheorem_of_HLInput T h)

/-- **The K3 chapter's descent datum, from the item-level input.**

`Work.K3.HLDescent T h 𝕜` is the `𝕜`-model of the link (the K3 chapter's interface, *constructed*
by `Work.K3.toHLDescent` from a `HassettLaiTheorem T`); here the `HassettLaiTheorem` itself is
produced from the item-level clauses (`Work.K3Inputs.HLInput.hassettLaiTheorem`), so the whole
descent of the K3 chapter runs from `HLInput T`. -/
noncomputable def HLInput.toHLDescent {T : Work.K3.TerasomaInput} (h : HLInput T)
    (𝕜 : Subfield ℂ) : Work.K3.HLDescent T h.hassettLaiTheorem 𝕜 :=
  Work.K3.toHLDescent h.hassettLaiTheorem 𝕜

/-- **The non-vanishing of the invariant coefficient over `𝕜 ⊆ ℂ`, from the item-level input**,
by the K3 chapter's descent (`Work.K3.HLDescent.exists_cInv_ne_zero`). -/
theorem HLInput.exists_cInv_ne_zero_kSubC {T : Work.K3.TerasomaInput} (h : HLInput T)
    (𝕜 : Subfield ℂ)
    (Tt : Work.K3.TotaroInputAt ↥𝕜 (h.toHLDescent 𝕜).data.S (h.toHLDescent 𝕜).data.S') :
    ∃ (Z : Scheme.{0}) (_ : Z.Over (Spec (.of ↥𝕜))) (z₀ : Z) (φ : Cr ↥𝕜 4),
      cInv ↥𝕜 z₀ (φ : (Work.K3.Affine4 ↥𝕜).BirationalMap (Work.K3.Affine4 ↥𝕜)) ≠ 0 :=
  (h.toHLDescent 𝕜).exists_cInv_ne_zero Tt

/-- **Theorem 1.2 (2) of the challenge at `n = 4`, from the item-level input over `𝕜 ⊆ ℂ`** — no
stabilisation input needed. -/
theorem not_gen_four_of_HLInput_kSubC {T : Work.K3.TerasomaInput} (h : HLInput T)
    (𝕜 : Subfield ℂ)
    (Tt : Work.K3.TotaroInputAt ↥𝕜 (h.toHLDescent 𝕜).data.S (h.toHLDescent 𝕜).data.S') :
    ¬ GenByPseudoRegularizable ↥𝕜 4 :=
  Work.Motivic.not_gen_of_cInv_ne_zero ↥𝕜 4 (h.exists_cInv_ne_zero_kSubC 𝕜 Tt)

/-- **Theorem 1.2 (2) of the challenge for `n ≥ 4`, from the item-level Hassett–Lai input.**

Both ℙ¹-bundle bridges of the K3 chapter's geometry are *proved* here: the bridge
`Work.K3.K3Data.bridge` of the link datum (`Work.K3Inputs.LinkCore.bridge`, via (F1)/(F2)) and the
base-change-uniform clause `bridge_bc` of `Work.K3.HassettLaiTheorem`
(`Work.K3Inputs.exists_hassettLaiTheorem_of_HLInput`).  The remaining inputs are exactly the four
numbered items of `thm-HL` (as named `Prop`s, bundled in `HLInput`), Terasoma's arithmetic input
`T : Work.K3.TerasomaInput`, Totaro's corollary at `𝕜` and the stabilisation step. -/
theorem not_gen_of_HLInput_kSubC {n : ℕ} (hn : 4 ≤ n) (𝕜 : Subfield ℂ)
    (T : Work.K3.TerasomaInput) (h : HLInput T)
    (Tt : Work.K3.TotaroInputAt ↥𝕜 (h.toHLDescent 𝕜).data.S (h.toHLDescent 𝕜).data.S')
    (S : Work.K3.K3Stabilisation ↥𝕜 n) : ¬ GenByPseudoRegularizable ↥𝕜 n :=
  Work.K3.not_gen_of_K3_kSubC_of_le hn 𝕜 T h.hassettLaiTheorem Tt S

/-- The same, with Totaro's input in the form of the paper's Corollary `cor-CYnSB`. -/
theorem not_gen_of_HLInput_of_corCYnSB {n : ℕ} (hn : 4 ≤ n) (𝕜 : Subfield ℂ)
    (T : Work.K3.TerasomaInput) (h : HLInput T) (Tt : CorCYnSB ↥𝕜)
    (S : Work.K3.K3Stabilisation ↥𝕜 n) : ¬ GenByPseudoRegularizable ↥𝕜 n :=
  not_gen_of_HLInput_kSubC hn 𝕜 T h
    ((CorCYnSB_to_totaroInput ↥𝕜 Tt).toInputAt ↥𝕜 (h.toHLDescent 𝕜).data.kTrivial
      (h.toHLDescent 𝕜).data.kTrivial' (h.toHLDescent 𝕜).data.picardOne
      (h.toHLDescent 𝕜).data.picardOne') S

end Work.K3Inputs
