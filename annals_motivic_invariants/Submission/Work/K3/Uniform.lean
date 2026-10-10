import Submission.Work.K3.HL
import Submission.Work.K3.BaseChangeVariety
import Submission.Work.K3.baseChange_isoOver
import Submission.Work.K3.birationalMap_baseChangeAlong
import Submission.Work.K3.isIsoAt_baseChangeAlong
import Submission.Work.K3.coheight_le_of_flat
import Submission.Work.K3.isIsoAt_genericPoint
import Submission.Work.K3.partialIso_isOver_of_toRationalMap
import Submission.Work.K3.eq_genericPoint_of_coheight_eq_zero
import Submission.Work.K3.flat_baseChangeProj
import Submission.Work.K3.isClosedImmersion_baseChangeMap
import Submission.Work.K3.smooth_baseChangeMap
import Submission.Work.K3.isReduced_baseChange_rat
import Submission.Work.LLink.exDiv_eq_singleton_iff

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.K3.Uniform` — the descent: the `𝕜`-model of the K3 L-link, from the `ℚ`-model

This is the load-bearing file of the descent step of Theorem `thm:K3`: it assembles, from the
base-change-uniform clauses of `Work.K3.HassettLaiTheorem` (the geometric input `thm-HL` together
with the geometric facts about its ingredients recorded there), the **`𝕜`-model of the L-link** — a
term of `Work.K3.K3Data ↥𝕜`, together with the identification of its two centres with the base
changes of the `ℚ`-centres (a term of `Work.K3.HLDescent`).

## What is base change and what is proved

* the two centres `S_𝕜`, `S'_𝕜`, the fourfold `P_𝕜` and the model of `S × ℙ¹` (`Z := P_𝕜`) are the
  base changes of the `ℚ`-model's (`Work.K3.baseChange`);
* the link map `ψ_𝕜` is the base change of `ψ_ℚ` (`Work.K3.birationalMap_baseChangeAlong`, and
  `Work.K3.psiBC` below);
* the two exceptional divisors `x_𝕜`, `y_𝕜` are the base-changed divisors: `Work.K3.xK`,
  `Work.K3.yK` are the points produced by the clauses `x_codim1`, `y_codim1`;
* **`exDiv ψ_𝕜 = {x_𝕜}` and `exDiv ψ_𝕜⁻¹ = {y_𝕜}` are proved** (`Work.K3.exDiv_psiBC`,
  `Work.K3.exDiv_psiBC_symm`) from
  * `Work.K3.isIsoAt_baseChangeAlong` (isomorphism points base change), applicable to an arbitrary
    isomorphism point through `Work.K3.partialIso_isOver_of_toRationalMap`;
  * `Work.K3.coheight_le_of_flat` (codimension does not decrease along a flat morphism: the
    projection of a base change is flat by `Work.K3.flat_baseChangeProj`), together with
    `Work.K3.isIsoAt_genericPoint` and `Work.K3.eq_genericPoint_of_coheight_eq_zero` (so that a
    non-isomorphism point has codimension at least one);
  * the clauses `x_notIso`, `y_notIso` (the exceptional divisors lie in the non-isomorphism locus)
    and `x_codim1`, `y_codim1` ((L3): the exceptional divisors are geometrically irreducible);
* the non-isomorphism of the two `𝕜`-centres is `Work.K3.HLDescent.notIso` (from `S_ℂ ≄ S'_ℂ` by
  monotonicity of the field of definition).

The result is `Work.K3.HassettLaiTheorem.toHLDescent`: `HassettLaiTheorem T → HLDescent T h 𝕜`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral
attribute [instance] Work.K3.TerasomaInput.varietyS Work.K3.TerasomaInput.overSigma
  Work.K3.TerasomaInput.isOverSigma Work.K3.HassettLaiTheorem.overSigma'
  Work.K3.HassettLaiTheorem.isOverSigma' Work.K3.K3Data.varietyS
  Work.K3.K3Data.varietyS' Work.K3.K3Data.varietyP

namespace Work.K3

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

noncomputable section

variable {T : TerasomaInput} (h : HassettLaiTheorem T) (𝕜 : Subfield ℂ)

/-! ## 0. The local instances of the model -/

section Setup

variable (h : HassettLaiTheorem T) (𝕜 : Subfield ℂ)

local instance instVarP : Variety ℚ h.data.P := h.data.varietyP
local instance instGeomP : GeometricallyIntegral (h.data.P ↘ Spec (.of ℚ)) := h.geomIntP
local instance instVarS : Variety ℚ h.data.S := h.data.varietyS
local instance instGeomS : GeometricallyIntegral (h.data.S ↘ Spec (.of ℚ)) := h.geomIntS
local instance instVarS' : Variety ℚ h.data.S' := h.data.varietyS'
local instance instGeomS' : GeometricallyIntegral (h.data.S' ↘ Spec (.of ℚ)) := h.geomIntS'
local instance instIrredP : IrreducibleSpace (baseChange ℚ ↥𝕜 h.data.P) :=
  irreducibleSpace_baseChange ℚ ↥𝕜 h.data.P
local instance instVarPbc : Variety ↥𝕜 (baseChange ℚ ↥𝕜 h.data.P) :=
  variety_baseChange ℚ ↥𝕜 h.data.P
local instance instVarSbc : Variety ↥𝕜 (baseChange ℚ ↥𝕜 h.data.S) :=
  variety_baseChange ℚ ↥𝕜 h.data.S
local instance instVarS'bc : Variety ↥𝕜 (baseChange ℚ ↥𝕜 h.data.S') :=
  variety_baseChange ℚ ↥𝕜 h.data.S'
local instance instFlatProj : Flat (baseChangeProj ℚ ↥𝕜 h.data.P) :=
  flat_baseChangeProj ℚ ↥𝕜 h.data.P
local instance instLofSigma' : LocallyOfFiniteType (h.Sigma' ↘ Spec (.of ℚ)) := by
  have hcomp : h.sigma' ≫ (h.data.S' ↘ Spec (.of ℚ)) = h.Sigma' ↘ Spec (.of ℚ) :=
    (Hom.isOver_iff (S := Spec (.of ℚ))).mp h.isOverSigma'
  rw [← hcomp]
  haveI : LocallyOfFiniteType h.sigma' := inferInstance
  haveI : LocallyOfFiniteType (h.data.S' ↘ Spec (.of ℚ)) := h.data.varietyS'.locallyOfFiniteType
  infer_instance
local instance instOverPbc : (baseChange ℚ ↥𝕜 h.data.P).Over (Spec (.of ↥𝕜)) :=
  baseChangeOver ℚ ↥𝕜 h.data.P
local instance instOverSbc : (baseChange ℚ ↥𝕜 h.data.S).Over (Spec (.of ↥𝕜)) :=
  baseChangeOver ℚ ↥𝕜 h.data.S
local instance instOverS'bc : (baseChange ℚ ↥𝕜 h.data.S').Over (Spec (.of ↥𝕜)) :=
  baseChangeOver ℚ ↥𝕜 h.data.S'
local instance instOverS : h.data.S.Over (Spec (.of ℚ)) := h.data.varietyS.over
local instance instOverS' : h.data.S'.Over (Spec (.of ℚ)) := h.data.varietyS'.over
local instance instOverPt : (Affine4 ↥𝕜).Over (Spec (.of ↥𝕜)) := inferInstance


/-! ## 1. The base-changed link map `ψ_𝕜` -/

/-- **The base change of the link map `ψ` to the field `𝕜`.** -/
def psiBC : (baseChange ℚ ↥𝕜 h.data.P).BirationalMap (baseChange ℚ ↥𝕜 h.data.P) :=
  Classical.choose (birationalMap_baseChangeAlong (specMap ℚ ↥𝕜) h.data.ψ h.data.isOverψ)

/-- The base-changed link map is over `𝕜`. -/
theorem psiBC_isOver : (psiBC h 𝕜).IsOver (Spec (.of ↥𝕜)) :=
  (Classical.choose_spec (birationalMap_baseChangeAlong (specMap ℚ ↥𝕜) h.data.ψ
    h.data.isOverψ)).1

/-- The forward rational map of the base-changed link map is the base change of the forward
rational map of `ψ`. -/
theorem psiBC_hom (g : h.data.P.PartialMap h.data.P) [g.IsOver (Spec (.of ℚ))]
    (hg : g.toRationalMap = h.data.ψ.hom) :
    (PartialMap.baseChangeAlong (specMap ℚ ↥𝕜) g).toRationalMap = (psiBC h 𝕜).hom :=
  (Classical.choose_spec (birationalMap_baseChangeAlong (specMap ℚ ↥𝕜) h.data.ψ
    h.data.isOverψ)).2.1 g hg

/-- The inverse rational map of the base-changed link map is the base change of the inverse
rational map of `ψ`. -/
theorem psiBC_inv (g : h.data.P.PartialMap h.data.P) [g.IsOver (Spec (.of ℚ))]
    (hg : g.toRationalMap = h.data.ψ.inv) :
    (PartialMap.baseChangeAlong (specMap ℚ ↥𝕜) g).toRationalMap = (psiBC h 𝕜).inv :=
  (Classical.choose_spec (birationalMap_baseChangeAlong (specMap ℚ ↥𝕜) h.data.ψ
    h.data.isOverψ)).2.2 g hg

/-- The characterization of `ψ_𝕜` as a base change of `ψ⁻¹`, in the form consumed by the clause
`y_notIso` (whose `Ψ` is the base change of `ψ⁻¹`). -/
theorem psiBC_symm_hom (g : h.data.P.PartialMap h.data.P) [g.IsOver (Spec (.of ℚ))]
    (hg : g.toRationalMap = h.data.ψ.inv) :
    (PartialMap.baseChangeAlong (specMap ℚ ↥𝕜) g).toRationalMap = (psiBC h 𝕜).symm.hom := by
  rw [psiBC_inv h 𝕜 g hg]; rfl

/-! ## 2. The base-changed exceptional divisors `x_𝕜`, `y_𝕜` -/

/-- **The base-changed exceptional divisor `x_𝕜`**: the unique codimension-one point of `P_𝕜` over
`x` (clause `x_codim1`; this is (L3) of the definition of an L-link, "the exceptional divisors of
the blow-ups are irreducible"). -/
def xK : baseChange ℚ ↥𝕜 h.data.P := (h.x_codim1 𝕜).choose

/-- `x_𝕜` lies over `x` and has codimension one. -/
theorem xK_spec : baseChangeProj ℚ ↥𝕜 h.data.P (xK h 𝕜) = h.data.x ∧
    coheight (xK h 𝕜) = 1 :=
  (h.x_codim1 𝕜).choose_spec.1

/-- The defining property of `x_𝕜` characterizes it. -/
theorem xK_eq {p : baseChange ℚ ↥𝕜 h.data.P}
    (hp : baseChangeProj ℚ ↥𝕜 h.data.P p = h.data.x ∧ coheight p = 1) : p = xK h 𝕜 :=
  ExistsUnique.unique (h.x_codim1 𝕜) hp (xK_spec h 𝕜)

/-- **The base-changed exceptional divisor `y_𝕜`**. -/
def yK : baseChange ℚ ↥𝕜 h.data.P := (h.y_codim1 𝕜).choose

/-- `y_𝕜` lies over `y` and has codimension one. -/
theorem yK_spec : baseChangeProj ℚ ↥𝕜 h.data.P (yK h 𝕜) = h.data.y ∧
    coheight (yK h 𝕜) = 1 :=
  (h.y_codim1 𝕜).choose_spec.1

/-- The defining property of `y_𝕜` characterizes it. -/
theorem yK_eq {p : baseChange ℚ ↥𝕜 h.data.P}
    (hp : baseChangeProj ℚ ↥𝕜 h.data.P p = h.data.y ∧ coheight p = 1) : p = yK h 𝕜 :=
  ExistsUnique.unique (h.y_codim1 𝕜) hp (yK_spec h 𝕜)

/-! ## 3. The exceptional divisors of the base-changed link -/

/-- **The only exceptional divisor of `ψ_𝕜` is `x_𝕜`.** -/
theorem exDiv_psiBC : exDiv (psiBC h 𝕜) = {xK h 𝕜} := by
  rw [Work.LLink.exDiv_eq_singleton_iff]
  refine ⟨⟨(xK_spec h 𝕜).2, h.x_notIso 𝕜 (psiBC h 𝕜) (psiBC_hom h 𝕜) (xK h 𝕜)
    (xK_spec h 𝕜).1⟩, ?_⟩
  intro q hq
  -- no base change of `ψ` is an isomorphism above a point where `ψ` is one
  have hqni : ¬ IsIsoAt h.data.ψ (baseChangeProj ℚ ↥𝕜 h.data.P q) := by
    intro hiso
    obtain ⟨i, hx, hi⟩ := hiso
    haveI : i.toPartialMap.IsOver (Spec (.of ℚ)) :=
      partialIso_isOver_of_toRationalMap ℚ i h.data.ψ hi
    exact hq.2 (isIsoAt_baseChangeAlong (specMap ℚ ↥𝕜) (psiBC h 𝕜) (psiBC_hom h 𝕜)
      i hi ‹i.toPartialMap.IsOver (Spec (.of ℚ))› hx q rfl)
  -- its image has codimension at most one (flatness)
  have hle : coheight (baseChangeProj ℚ ↥𝕜 h.data.P q) ≤ coheight q :=
    coheight_le_of_flat (baseChangeProj ℚ ↥𝕜 h.data.P) q
  -- and at least one (otherwise it is the generic point, where `ψ` is an isomorphism)
  have hne : coheight (baseChangeProj ℚ ↥𝕜 h.data.P q) ≠ 0 := by
    intro h0
    have hgen : baseChangeProj ℚ ↥𝕜 h.data.P q = genericPoint h.data.P :=
      eq_genericPoint_of_coheight_eq_zero _ h0
    exact hqni (hgen ▸ isIsoAt_genericPoint h.data.ψ)
  have hge : (1 : ℕ∞) ≤ coheight (baseChangeProj ℚ ↥𝕜 h.data.P q) :=
    Order.one_le_iff_ne_zero.mpr hne
  have h1 : coheight (baseChangeProj ℚ ↥𝕜 h.data.P q) = 1 := by
    rw [hq.1] at hle
    exact le_antisymm hle hge
  have hmem : baseChangeProj ℚ ↥𝕜 h.data.P q ∈ exDiv h.data.ψ := ⟨h1, hqni⟩
  rw [h.data.exDiv_ψ] at hmem
  exact xK_eq h 𝕜 ⟨hmem, hq.1⟩

/-- **The only exceptional divisor of `ψ_𝕜⁻¹` is `y_𝕜`.** -/
theorem exDiv_psiBC_symm : exDiv (psiBC h 𝕜).symm = {yK h 𝕜} := by
  rw [Work.LLink.exDiv_eq_singleton_iff]
  refine ⟨⟨(yK_spec h 𝕜).2, h.y_notIso 𝕜 (psiBC h 𝕜).symm (psiBC_symm_hom h 𝕜) (yK h 𝕜)
    (yK_spec h 𝕜).1⟩, ?_⟩
  intro q hq
  haveI hψover : h.data.ψ.IsOver (Spec (.of ℚ)) := h.data.isOverψ
  haveI : h.data.ψ.symm.IsOver (Spec (.of ℚ)) := by
    change (h.data.ψ.inv).IsOver (Spec (.of ℚ))
    infer_instance
  have hqni : ¬ IsIsoAt h.data.ψ.symm (baseChangeProj ℚ ↥𝕜 h.data.P q) := by
    intro hiso
    obtain ⟨i, hx, hi⟩ := hiso
    haveI : i.toPartialMap.IsOver (Spec (.of ℚ)) :=
      partialIso_isOver_of_toRationalMap ℚ i h.data.ψ.symm hi
    exact hq.2 (isIsoAt_baseChangeAlong (specMap ℚ ↥𝕜) (psiBC h 𝕜).symm (psiBC_symm_hom h 𝕜)
      i hi ‹i.toPartialMap.IsOver (Spec (.of ℚ))› hx q rfl)
  have hle : coheight (baseChangeProj ℚ ↥𝕜 h.data.P q) ≤ coheight q :=
    coheight_le_of_flat (baseChangeProj ℚ ↥𝕜 h.data.P) q
  have hne : coheight (baseChangeProj ℚ ↥𝕜 h.data.P q) ≠ 0 := by
    intro h0
    have hgen : baseChangeProj ℚ ↥𝕜 h.data.P q = genericPoint h.data.P :=
      eq_genericPoint_of_coheight_eq_zero _ h0
    exact hqni (hgen ▸ isIsoAt_genericPoint h.data.ψ.symm)
  have hge : (1 : ℕ∞) ≤ coheight (baseChangeProj ℚ ↥𝕜 h.data.P q) :=
    Order.one_le_iff_ne_zero.mpr hne
  have h1 : coheight (baseChangeProj ℚ ↥𝕜 h.data.P q) = 1 := by
    rw [hq.1] at hle
    exact le_antisymm hle hge
  have hmem : baseChangeProj ℚ ↥𝕜 h.data.P q ∈ exDiv h.data.ψ.symm := ⟨h1, hqni⟩
  rw [h.data.exDiv_ψ_symm] at hmem
  exact yK_eq h 𝕜 ⟨hmem, hq.1⟩

/-! ## 4. The transports at `𝕜` (strong rationality of `ℙ⁴`) -/

/-- The transport `𝔸⁴_𝕜 ⤏ P_𝕜` (strong rationality of `ℙ⁴`, base changed). -/
def epsBC : (Affine4 ↥𝕜).BirationalMap (baseChange ℚ ↥𝕜 h.data.P) :=
  (h.transports_bc 𝕜).choose

/-- The transport `P_𝕜 ⤏ 𝔸⁴_𝕜`. -/
def deltaBC : (baseChange ℚ ↥𝕜 h.data.P).BirationalMap (Affine4 ↥𝕜) :=
  (h.transports_bc 𝕜).choose_spec.choose

/-- `ε_𝕜` is over `𝕜`. -/
theorem epsBC_isOver : (epsBC h 𝕜).IsOver (Spec (.of ↥𝕜)) :=
  (h.transports_bc 𝕜).choose_spec.choose_spec.1

/-- `δ_𝕜` is over `𝕜`. -/
theorem deltaBC_isOver : (deltaBC h 𝕜).IsOver (Spec (.of ↥𝕜)) :=
  (h.transports_bc 𝕜).choose_spec.choose_spec.2.1

/-- `ε_𝕜` contributes nothing to the invariant coefficient. -/
theorem cInv_epsBC (z : baseChange ℚ ↥𝕜 h.data.P) : cInv ↥𝕜 z (epsBC h 𝕜) = 0 :=
  (h.transports_bc 𝕜).choose_spec.choose_spec.2.2.1 z

/-- `δ_𝕜` contributes nothing to the invariant coefficient. -/
theorem cInv_deltaBC (z : baseChange ℚ ↥𝕜 h.data.P) : cInv ↥𝕜 z (deltaBC h 𝕜) = 0 :=
  (h.transports_bc 𝕜).choose_spec.choose_spec.2.2.2 z

/-! ## 5. The `𝕜`-model of the link -/

/-- The base point of the `𝕜`-model (`z₀ = y_𝕜`): its residue field is that of the exceptional
divisor `y_𝕜`.  (`ResEquiv` and its reflexivity are stated with the `Over (Spec 𝕜)` structure of
`P_𝕜` written in the canonical form `Variety.over`, so that the term agrees definitionally with the
field type of `K3Data`.) -/
theorem resEquivY : @ResEquiv ↥𝕜 _ (baseChange ℚ ↥𝕜 h.data.P)
    (baseChange ℚ ↥𝕜 h.data.P)
    (@Variety.over ↥𝕜 _ (baseChange ℚ ↥𝕜 h.data.P) (instVarPbc h 𝕜))
    (@Variety.over ↥𝕜 _ (baseChange ℚ ↥𝕜 h.data.P) (instVarPbc h 𝕜)) (yK h 𝕜) (yK h 𝕜) :=
  @Work.Motivic.ResEquiv.refl ↥𝕜 _ (baseChange ℚ ↥𝕜 h.data.P)
    (@Variety.over ↥𝕜 _ (baseChange ℚ ↥𝕜 h.data.P) (instVarPbc h 𝕜)) (yK h 𝕜)

/-- **The `𝕜`-model of the K3 L-link**, obtained by base change of the `ℚ`-model: the two centres
are the base changes of `S`, `S'`, the fourfold is the base change of `P`, the link map is the base
change of `ψ`, its two exceptional divisors are the base-changed divisors `x_𝕜`, `y_𝕜` (with
`exDiv ψ_𝕜 = {x_𝕜}`, `exDiv ψ_𝕜⁻¹ = {y_𝕜}` proved in §3), the base point is `y_𝕜` (the model
`Z = P_𝕜` of `S × ℙ¹` with base point the exceptional divisor `y_𝕜`), the `ℙ¹`-bundle bridge is the
uniform bridge clause, and the two transports are supplied by the strong rationality clause
`transports_bc`. -/
def dataBC : K3Data ↥𝕜 :=
  let Pbc : Scheme.{0} := baseChange ℚ ↥𝕜 h.data.P
  let Sbc : Scheme.{0} := baseChange ℚ ↥𝕜 h.data.S
  let Sbc' : Scheme.{0} := baseChange ℚ ↥𝕜 h.data.S'
  let vP : Variety ↥𝕜 Pbc := instVarPbc h 𝕜
  let ybc : Pbc := yK h 𝕜
  let xbc : Pbc := xK h 𝕜
  let oP : Pbc.Over (Spec (.of ↥𝕜)) := @Variety.over ↥𝕜 _ Pbc vP
  let r : @ResEquiv ↥𝕜 _ Pbc Pbc oP oP ybc ybc :=
    @Work.Motivic.ResEquiv.refl ↥𝕜 _ Pbc oP ybc
  { S := Sbc
    varietyS := instVarSbc h 𝕜
    isK3 := h.isK3_bc 𝕜
    kTrivial := h.kTrivial_bc 𝕜
    picardOne := h.picardOne_bc 𝕜
    S' := Sbc'
    varietyS' := instVarS'bc h 𝕜
    isK3' := h.isK3'_bc 𝕜
    kTrivial' := h.kTrivial'_bc 𝕜
    picardOne' := h.picardOne'_bc 𝕜
    P := Pbc
    varietyP := vP
    ψ := psiBC h 𝕜
    isOverψ := psiBC_isOver h 𝕜
    x := xbc
    y := ybc
    exDiv_ψ := exDiv_psiBC h 𝕜
    exDiv_ψ_symm := exDiv_psiBC_symm h 𝕜
    z₀ := ybc
    resEquiv_y := r
    ε := epsBC h 𝕜
    isOverε := epsBC_isOver h 𝕜
    δ := deltaBC h 𝕜
    isOverδ := deltaBC_isOver h 𝕜
    cInv_ε := cInv_epsBC h 𝕜 (yK h 𝕜)
    cInv_δ := cInv_deltaBC h 𝕜 (yK h 𝕜)
    bridge := fun hres => h.bridge_bc 𝕜 (xK h 𝕜) (yK h 𝕜) (xK_spec h 𝕜).1 (xK_spec h 𝕜).2
      (yK_spec h 𝕜).1 (yK_spec h 𝕜).2 hres }

/-- **The descent step of `thm:K3`**: the `𝕜`-model of the link is a `HLDescent`, with centres
being the base changes of the `ℚ`-model's centres and with `Σ'_𝕜` the base change of `Σ'`. -/
def toHLDescent : HLDescent T h 𝕜 where
  data := dataBC h 𝕜
  centre := IsoOver.refl ↥𝕜 (baseChange ℚ ↥𝕜 h.data.S)
  centrePartner := IsoOver.refl ↥𝕜 (baseChange ℚ ↥𝕜 h.data.S')
  SigmaK := baseChange ℚ ↥𝕜 h.Sigma'
  overSigmaK := baseChangeOver ℚ ↥𝕜 h.Sigma'
  sigmaK := baseChangeMap ℚ ↥𝕜 h.sigma'
  isOverSigmaK := baseChangeMap_isOver ℚ ↥𝕜 h.sigma'
  isClosedImmersionSigmaK := isClosedImmersion_baseChangeMap ℚ ↥𝕜 h.sigma'
  isReducedSigmaK := isReduced_baseChange_rat ↥𝕜 h.Sigma'
  smoothSigmaK := smooth_baseChangeMap ℚ ↥𝕜 h.sigma'
  hasLengthThreeK := h.hasLengthThree_bc 𝕜
  hlK := h.hl_bc 𝕜
  sigmaPartner := IsoOver.refl ↥𝕜 (baseChange ℚ ↥𝕜 h.Sigma')

end Setup

end

end Work.K3
