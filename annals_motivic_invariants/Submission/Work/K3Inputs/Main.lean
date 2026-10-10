import Submission.Work.K3Inputs.Defs
import Submission.Work.K3Inputs.Cylinder
import Submission.Work.K3Inputs.CylinderSharp
import Submission.Work.K3Inputs.sameCylinderField_of_cyl_birational
import Submission.Work.K3Inputs.StablyBiratK3
import Submission.Work.K3Inputs.LinkCore
import Submission.Work.K3Inputs.HLItems
import Submission.Work.K3Inputs.HLPayoff
import Submission.Work.K3Inputs.Terasoma
import Submission.Work.K3Inputs.Totaro
import Submission.Work.K3Inputs.Stabilisation
import Submission.Work.K3Inputs.not_stablyBirat_prod
import Submission.Work.K3Inputs.stablyBirat_congr
import Submission.Work.K3Inputs.not_stablyBirational_prod
import Submission.Work.K3Inputs.affineN_prodOver_iso
import Submission.Work.K3Inputs.prodOver_affine_assoc
import Submission.Work.K3Inputs.exists_variety_prodOver_affineSpace
import Submission.Work.K3Inputs.CorCYnSB_to_totaroInput
import Submission.Work.K3Inputs.IsP1BundleOver_congr
import Submission.Work.K3Inputs.stablyBirat_of_isoOver
import Submission.Work.K3Inputs.exDiv_affineProd_subset

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.K3Inputs` — the K3-INPUTS area: the named inputs of the K3 chapter, decomposed

Single entry point: `import Submission.Work.K3Inputs.Main`.

Lin–Shinder, *Motivic invariants of birational maps*, Annals **199** (1), 2024, § *K3 surfaces of
degree 12* (tex 2186–2404).  The sibling area `Submission/Work/K3` reduces Theorem 1.2 (2) of the
challenge for `n ≥ 4` to three named inputs — `Work.K3.TerasomaInput` (the arithmetic input,
`lem:HL-admis-pencil` + `pro-K3HLPic1`), `Work.K3.HassettLaiTheorem` (the geometry `thm-HL`(1)–(4)
over `ℚ`) and `Work.K3.TotaroInput` (`cor-CYnSB`), plus the stabilisation step
`Work.K3.K3Stabilisation`.  This area *decomposes* those inputs and proves everything about them
that Mathlib allows.

## What is new here

1. **The ℙ¹-bundle bridge is proved.**  The field `bridge` of `Work.K3.K3Data` is derived
   (`Work.K3Inputs.bridge_of_clauses`) from the two geometric clauses
   (F1) `Work.K3Inputs.IsP1BundleOver 𝕜 p X` (the exceptional divisor is a `ℙ¹`-bundle over the
   centre, `thm-HL` (1)) and (F2) `Work.K3Inputs.CylinderRigid 𝕜 X Y` (the paper's `lem-stbirCY`
   at `W = ℙ¹`), and the same at the level of the link data:
   `Work.K3Inputs.LinkCore` is `Work.K3.K3Data` with `bridge` proved
   (`Work.K3Inputs.LinkCore.bridge`, `…toK3Data`, `…toK3Link`,
   `Work.K3Inputs.exists_cInv_ne_zero_of_LinkCore`).
1bis. **The converse of (F2) is automatic, so (F2) is exactly the descent.**
   `Work.K3Inputs.sameCylinderField_of_cyl_birational` (an over-the-base partial isomorphism of
   the cylinders gives the cylinder-field isomorphism, with no separably-uniruled input) and
   `Work.K3Inputs.sameCylinderField_iff_cyl_birational` (with the sharp form
   `Work.K3Inputs.CylinderRigidOver` of (F2)).

2. **The distinguishing `κ(S)(t) ≄ κ(S')(t)`.**  `Work.K3Inputs.not_sameCylinderField_of_totaro`
   derives it from Totaro's input and (F2), via the cylinder calculus
   (`SameCylinderField`, `not_sameCylinderField_of_cylinderRigid`) and the product-shift statements
   `Work.K3Inputs.not_stablyBirat_prod`, `Work.K3Inputs.not_stablyBirational_prod`.
3. **The item-level Hassett–Lai input.**  Items (1)–(4) of `thm-HL` are recorded as named
   `Prop`s (`Work.K3Inputs.HasThreeTransverseDoublePointsAndNormalisation`,
   `QuarticSystemDefinesBirational`, `InverseConstructedFromPartner`, `BlowUpIdentification`,
   `IsUniqueFourierMukaiPartner`) and bundled in `Work.K3Inputs.HLInput`, whose ℚ-level payoff
   (with the bridge proved) is `Work.K3Inputs.HLInput.exists_cInv_ne_zero`.
4. **Terasoma's input.**  `Work.K3Inputs.TerasomaData`/`TerasomaFamily` restate
   `pro-K3HLPic1` over an arbitrary field and in its strong (infinitely many, pairwise
   non-isomorphic) form; `Work.K3Inputs.TerasomaFamily.toInput` produces the K3 chapter's
   `Work.K3.TerasomaInput`.
5. **Totaro's input.**  `Work.K3Inputs.CorCYnSB` is `cor-CYnSB` in the paper's same-`W` form plus
   the `W = 𝔸ⁿ` form with two exponents; `Work.K3Inputs.CorCYnSB_to_totaroInput` produces
   `Work.K3.TotaroInput`.
5bis. **The uniform assembly is proved**: `Work.K3Inputs.exists_hassettLaiTheorem_of_HLInput`
   (`HLInput T → Nonempty (Work.K3.HassettLaiTheorem T)`, with `bridge_bc` derived; the interface
   is `Work.K3Inputs.HLInput.hassettLaiTheorem`), so the K3 chapter's geometry carries no bridge
   assumption any more; `Work.K3Inputs.HLInput.toHLDescent` runs the K3 chapter's descent from the
   item-level input.

6. **The stabilisation step** is restated (`Work.K3Inputs.StabilisationStep`) and its `exDiv`
   analysis split into the provable inclusion `Work.K3Inputs.exDiv_affineProd_subset` and the
   named residual `Work.K3Inputs.ExDivProdMap`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

namespace Work.K3Inputs

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

noncomputable section

/-! ## 1. The `n ≥ 4` chain from the bridge-free link data -/

/-- **Theorem 1.2 (2) of the challenge at `n = 4`**, from the bridge-free link data
(`Work.K3Inputs.LinkCore 𝕜`: the geometric link data with the ℙ¹-bundle bridge *proved* from
(F1) and (F2)), Totaro's input and the non-isomorphism of the two centres. -/
theorem not_gen_four_of_LinkCore (𝕜 : Subfield ℂ) (C : LinkCore ↥𝕜)
    (Tt : Work.K3.TotaroInputAt ↥𝕜 C.S C.S') (h : ¬ Work.K3.IsoOver ↥𝕜 C.S C.S') :
    ¬ GenByPseudoRegularizable ↥𝕜 4 :=
  Work.Motivic.not_gen_of_cInv_ne_zero ↥𝕜 4 (exists_cInv_ne_zero_of_LinkCore C Tt h)

/-- **Theorem 1.2 (2) of the challenge for `n ≥ 4`**, from the bridge-free link data, Totaro's
input and the stabilisation step `c(φ × id_W)`. -/
theorem not_gen_of_LinkCore {n : ℕ} (hn : 4 ≤ n) (𝕜 : Subfield ℂ) (C : LinkCore ↥𝕜)
    (Tt : Work.K3.TotaroInputAt ↥𝕜 C.S C.S') (h : ¬ Work.K3.IsoOver ↥𝕜 C.S C.S')
    (S : StabilisationStep ↥𝕜 n) : ¬ GenByPseudoRegularizable ↥𝕜 n :=
  Work.Motivic.not_gen_of_cInv_ne_zero ↥𝕜 n
    (S.stabilise (exists_cInv_ne_zero_of_LinkCore C Tt h))

/-- The same, with Totaro's input in the form of the paper's Corollary `cor-CYnSB`
(`Work.K3Inputs.CorCYnSB`). -/
theorem not_gen_of_LinkCore_of_corCYnSB {n : ℕ} (hn : 4 ≤ n) (𝕜 : Subfield ℂ) (C : LinkCore ↥𝕜)
    (Tt : CorCYnSB ↥𝕜) (h : ¬ Work.K3.IsoOver ↥𝕜 C.S C.S') (S : StabilisationStep ↥𝕜 n) :
    ¬ GenByPseudoRegularizable ↥𝕜 n :=
  not_gen_of_LinkCore hn 𝕜 C
    ((CorCYnSB_to_totaroInput ↥𝕜 Tt).toInputAt ↥𝕜 C.kTrivial C.kTrivial' C.picardOne
      C.picardOne') h S

/-! ## 2. The `n ≥ 4` chain from the K3 chapter's named inputs -/

/-- **The distinguishing `κ(S)(t) ≄ κ(S')(t)`, from the paper's `cor-CYnSB`.**

Combining `Work.K3Inputs.CorCYnSB` (in the `𝔸ⁿ` form consumed by `Work.K3.TotaroInput`) with the
two geometric clauses of the bridge — (F1) `Work.K3Inputs.IsP1BundleOver` for the two exceptional
divisors and (F2) `Work.K3Inputs.CylinderRigid` — the two centres of the K3 link have
non-isomorphic cylinder function fields: `S × ℙ¹` and `S' × ℙ¹` are not stably birational.  This is
the input `¬ ResEquiv 𝕜 y x` of the link, i.e. the statement that the `[κ(S)(t)]`-coefficient of
`c(ψ_𝕜)` counts exactly one of the two exceptional divisors. -/
theorem not_sameCylinderField_of_corCYnSB {𝕜 : Type} [Field 𝕜] {P S S' : Scheme.{0}}
    [Variety 𝕜 S] [Variety 𝕜 S'] [P.Over (Spec (.of 𝕜))] {y x : P}
    (hy : IsP1BundleOver 𝕜 y S)
    (hx : IsP1BundleOver 𝕜 x S') (hrigid : CylinderRigid 𝕜 S S')
    (hsS : Work.K3.IsKTrivial 𝕜 S) (hsS' : Work.K3.IsKTrivial 𝕜 S')
    (hpS : Work.K3.PicardRankOneGeom 𝕜 S) (hpS' : Work.K3.PicardRankOneGeom 𝕜 S')
    (T : CorCYnSB 𝕜) (h : ¬ Work.K3.IsoOver 𝕜 S S') : ¬ SameCylinderField 𝕜 S S' :=
  not_sameCylinderField_of_totaro hrigid
    ((CorCYnSB_to_totaroInput 𝕜 T).toInputAt 𝕜 hsS hsS' hpS hpS') h

/-- **Theorem 1.2 (2) of the challenge for `n ≥ 4`**, in the exact shape of the challenge's
`theorem_1_2_2`, from the three named inputs of the K3 chapter
(`Work.K3.TerasomaInput`, `Work.K3.HassettLaiTheorem`, `Work.K3.TotaroInput`) and the
stabilisation step.  This is the wiring of `Work.K3.not_gen_of_K3_kSubC_of_le`. -/
theorem theorem_1_2_2_of_inputs {n : ℕ} (hn : 4 ≤ n) (𝕜 : Subfield ℂ)
    (T : Work.K3.TerasomaInput) (h : Work.K3.HassettLaiTheorem T)
    (Tt : Work.K3.TotaroInputAt ↥𝕜 (Work.K3.toHLDescent h 𝕜).data.S
      (Work.K3.toHLDescent h 𝕜).data.S')
    (S : Work.K3.K3Stabilisation ↥𝕜 n) : ¬ GenByPseudoRegularizable ↥𝕜 n :=
  Work.K3.not_gen_of_K3_kSubC_of_le hn 𝕜 T h Tt S

/-- The same, with the arithmetic input in the *strong* form given by the paper's proof of
`pro-K3HLPic1` (infinitely many pairwise non-isomorphic K3 surfaces,
`Work.K3Inputs.TerasomaFamily`), and Totaro's input in the form of `cor-CYnSB`
(`Work.K3Inputs.CorCYnSB`). -/
theorem theorem_1_2_2_of_TerasomaFamily_and_corCYnSB {n : ℕ} (hn : 4 ≤ n) (𝕜 : Subfield ℂ)
    (F : TerasomaFamily ℚ) (h : Work.K3.HassettLaiTheorem F.toInput)
    (Tt : CorCYnSB ↥𝕜) (S : Work.K3.K3Stabilisation ↥𝕜 n) :
    ¬ GenByPseudoRegularizable ↥𝕜 n :=
  theorem_1_2_2_of_inputs hn 𝕜 F.toInput h
    ((CorCYnSB_to_totaroInput ↥𝕜 Tt).toInputAt ↥𝕜 (Work.K3.toHLDescent h 𝕜).data.kTrivial (Work.K3.toHLDescent h 𝕜).data.kTrivial'
      (Work.K3.toHLDescent h 𝕜).data.picardOne (Work.K3.toHLDescent h 𝕜).data.picardOne') S

end

end Work.K3Inputs
