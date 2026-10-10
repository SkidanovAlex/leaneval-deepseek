import Submission.Work.G2.LayerA

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.G2.LayerB` — the `ℤ`-model of Layer 2 of `thm:CY3` (the general section and the blow-ups)

This is the **producer** of Layer 2 of the CY3 chapter (`Submission/Work/CY3/Section.lean`,
structure `Work.CY3.CY3Section`): the general section `σ` of the very ample bundle `L = p*M ⊗ p'*M'`
of Layer 1, its zero locus `X_𝕜 = Z(σ) ⊂ G_𝕜/B_𝕜`, the zero loci `Z_𝕜 = Z(p_*σ) ⊂ G_𝕜/P_𝕜` and
`Z'_𝕜 = Z(p'_*σ) ⊂ G_𝕜/P'_𝕜` of the pushforwards, the two blow-ups `τ : X_𝕜 ⟶ G_𝕜/P_𝕜`,
`τ' : X_𝕜 ⟶ G_𝕜/P'_𝕜`, and the birational map `ψ = τ' ∘ τ⁻¹` with its two exceptional divisors.

## The paper's Layer 2

> Now let `𝕜` be an infinite field and let `σ ∈ H⁰(G_𝕜/B_𝕜, L_𝕜)` be a general section.  Let
> `X_𝕜 = Z(σ) ⊂ G_𝕜/B_𝕜` and let `Z_𝕜 ≔ Z(p_*σ) ⊂ G_𝕜/P_𝕜` … Similarly, let
> `Z'_𝕜 ≔ Z(p'_*σ) ⊂ G_𝕜/P'_𝕜`.  Since `L_𝕜` is very ample and `𝕜` is infinite, `X_𝕜` is smooth
> by Bertini's theorem … Consider the commutative diagram … which defines the maps `τ` and `τ'`.
> By construction, `τ` maps `X_𝕜 ∖ τ⁻¹(Z_𝕜)` isomorphically onto its image and `τ⁻¹(Z_𝕜) → Z_𝕜` is a
> `ℙ¹`-fibration.  By [Danilov, Theorem 2], `τ` is thus a sequence of blow ups along smooth centers
> of codimension `2` lying above `Z_𝕜`.  Since `X_𝕜` has Picard rank `ρ(X_𝕜) = ρ(G_𝕜/B_𝕜) = 2` by
> Grothendieck–Lefschetz' theorem, necessarily `τ` is the blow up of `G_𝕜/P_𝕜` along `Z_𝕜` …
> Similarly, `τ'` is the blow up of `G_𝕜/P'_𝕜` along `Z'_𝕜` … We thus have a birational map
> `ψ ≔ τ' ∘ τ⁻¹ : G_𝕜/P_𝕜 ⇢ G_𝕜/P'_𝕜`.  By construction, `ψ` is regular away from `Z_𝕜` and `ψ⁻¹`
> is regular away from `Z'_𝕜`.

The *morphisms* of this layer are **not** named inputs: the paper's diagram determines `τ = p ∘ ι_X`
and `τ' = p' ∘ ι_X` (they are the restrictions of the two projections to the zero locus `X`), so
they are *defined* from `ι_X`, `p`, `p'` (`Work.G2.CY3ZModel.tauZ`, `…tauZ'`) and their base
changes are computed by `Work.G2.baseChangeZMap_comp` (`Work.G2.CY3ZModel.tau_eq`, `…tau'_eq`).

Named inputs of this layer: the zero loci `X`, `Z`, `Z'` with their closed immersions, Bertini
(the only place where `Infinite 𝕜` is used), Danilov + Grothendieck–Lefschetz (the two blow-ups)
and the birational map `ψ` with its two exceptional divisors.

Everything else is **proved**: `Work.G2.CY3ZModel.toCY3Section` — the `𝕜`-counterpart
`Work.CY3.CY3Section 𝕜` of the model.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

namespace Work.G2

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

noncomputable section

/-- **The link map and its two exceptional divisors** (paper `lemma:L-link` (3) and the last
sentence of the proof of `thm:CY3`): a birational map `P ⇢ P'` which is regular away from the
centre `Z ⊂ P` (so that its only exceptional divisor on the source is the generic point `x` of the
`ℙ¹ × Z'`-divisor) and whose inverse is regular away from `Z' ⊂ P'`.

This is the `𝕜`-level shape of the last two fields of `Work.CY3.CY3Section`; it is packaged as a
structure because — unlike the schemes and the morphisms of Layers 1–2 — a *birational map* cannot
be base changed along `Spec 𝕜 ⟶ Spec ℤ` (that morphism is neither surjective nor universally open:
its image is the generic point when `char 𝕜 = 0`, and the generic point together with
`(char 𝕜)` in positive characteristic, so the preimage of a dense open need not be dense).  Hence
the `ℤ`-model carries this data base-change-uniformly, i.e. for every field `𝕜`. -/
structure LinkData (𝕜 : Type) [Field 𝕜] (P P' : Scheme.{0}) [Variety 𝕜 P] [Variety 𝕜 P'] where
  /-- the birational map `ψ ≔ τ' ∘ τ⁻¹ : G/P ⇢ G/P'`. -/
  psi : P.BirationalMap P'
  [isOver : psi.IsOver (Spec (.of 𝕜))]
  /-- the exceptional divisor of `ψ` on the source (birational to `ℙ¹ × Z'`). -/
  x : P
  /-- the exceptional divisor of `ψ⁻¹` on the target (birational to `ℙ¹ × Z`). -/
  y : P'
  /-- `ψ` is regular away from `Z` and its only exceptional divisor is `x`. -/
  exDiv_psi : exDiv psi = {x}
  /-- `ψ⁻¹` is regular away from `Z'` and its only exceptional divisor is `y`. -/
  exDiv_psi_symm : exDiv psi.symm = {y}

attribute [instance] LinkData.isOver

/-- **The `ℤ`-model of Layer 2 of `thm:CY3`.**  Extends the `ℤ`-model of Layer 1
(`Work.G2.G2ZModel`) by the zero locus `X_ℤ = Z(σ)` of the general section, the two centres
`Z_ℤ = Z(p_*σ)`, `Z'_ℤ = Z(p'_*σ)` with their closed immersions, and the base-change-uniform
clauses of the paper's Layer 2. -/
structure CY3ZModel extends G2ZModel where
  /-- `X_ℤ`, the `ℤ`-model of the zero locus `Z(σ) ⊂ G/B` of the general section. -/
  XZ : Scheme.{0}
  [overXZ : XZ.Over (Spec (.of ℤ))]
  [geomIntXZ : GeometricallyIntegral (XZ ↘ Spec (.of ℤ))]
  [sepXZ : IsSeparated (XZ ↘ Spec (.of ℤ))]
  [lofinXZ : LocallyOfFiniteType (XZ ↘ Spec (.of ℤ))]
  [qcXZ : QuasiCompact (XZ ↘ Spec (.of ℤ))]
  /-- `Z_ℤ`, the `ℤ`-model of the first centre `Z(p_*σ) ⊂ G/P`. -/
  ZZ : Scheme.{0}
  [overZZ : ZZ.Over (Spec (.of ℤ))]
  [geomIntZZ : GeometricallyIntegral (ZZ ↘ Spec (.of ℤ))]
  [sepZZ : IsSeparated (ZZ ↘ Spec (.of ℤ))]
  [lofinZZ : LocallyOfFiniteType (ZZ ↘ Spec (.of ℤ))]
  [qcZZ : QuasiCompact (ZZ ↘ Spec (.of ℤ))]
  /-- `Z'_ℤ`, the `ℤ`-model of the second centre `Z(p'_*σ) ⊂ G/P'`. -/
  ZZ' : Scheme.{0}
  [overZZ' : ZZ'.Over (Spec (.of ℤ))]
  [geomIntZZ' : GeometricallyIntegral (ZZ' ↘ Spec (.of ℤ))]
  [sepZZ' : IsSeparated (ZZ' ↘ Spec (.of ℤ))]
  [lofinZZ' : LocallyOfFiniteType (ZZ' ↘ Spec (.of ℤ))]
  [qcZZ' : QuasiCompact (ZZ' ↘ Spec (.of ℤ))]
  /-- the closed immersion `X_ℤ ⟶ G/B`. -/
  iotaXZ : XZ ⟶ GB
  [isOverIotaXZ : iotaXZ.IsOver (Spec (.of ℤ))]
  /-- **Named input**: `X_ℤ = Z(σ)` is a *closed* subvariety of `G/B`. -/
  isClosedImmersionIotaXZ : IsClosedImmersion iotaXZ
  /-- the closed immersion `Z_ℤ ⟶ G/P`. -/
  iotaZZ : ZZ ⟶ GP
  [isOverIotaZZ : iotaZZ.IsOver (Spec (.of ℤ))]
  /-- **Named input**: the first centre `Z_ℤ = Z(p_*σ)` is a *closed* subvariety of `G/P`. -/
  isClosedImmersionIotaZZ : IsClosedImmersion iotaZZ
  /-- the closed immersion `Z'_ℤ ⟶ G/P'`. -/
  iotaZZ' : ZZ' ⟶ GP'
  [isOverIotaZZ' : iotaZZ'.IsOver (Spec (.of ℤ))]
  /-- **Named input**: the second centre `Z'_ℤ` is a *closed* subvariety of `G/P'`. -/
  isClosedImmersionIotaZZ' : IsClosedImmersion iotaZZ'
  /-- **Named input (Bertini; paper's Layer 2, the only place where `Infinite 𝕜` is used)**:
  over an infinite field `𝕜`, `X`, `Z`, `Z'` are the zero loci of a general section `σ` of `L` and
  of its two pushforwards `p_*σ`, `p'_*σ`, and the geometric consequences of Bertini hold
  (`X` smooth, `τ⁻¹(Z) → Z` and `τ'⁻¹(Z') → Z'` `ℙ¹`-fibrations, `Z`, `Z'` smooth connected
  codimension-two centres). -/
  generalSection : ∀ (𝕜 : Type) [Field 𝕜] [Infinite 𝕜],
    Work.CY3.IsGeneralSectionZeroLocus 𝕜 (baseChangeZ 𝕜 GB) (baseChangeZ 𝕜 XZ)
      (baseChangeZ 𝕜 GP) (baseChangeZ 𝕜 ZZ) (baseChangeZ 𝕜 GP') (baseChangeZ 𝕜 ZZ')
      (baseChangeZMap 𝕜 iotaXZ) (baseChangeZMap 𝕜 iotaZZ) (baseChangeZMap 𝕜 iotaZZ')
  /-- **Named input (Danilov Thm 2 + Grothendieck–Lefschetz)**: `τ_𝕜 = p_𝕜 ∘ ι_X` is the blow-up of
  `G/P` along the smooth connected centre `Z_𝕜`. -/
  isBlowUp : ∀ (𝕜 : Type) [Field 𝕜],
    Work.CY3.IsBlowUpAlong (baseChangeZMap 𝕜 (iotaXZ ≫ p)) (baseChangeZMap 𝕜 iotaZZ)
  /-- **Named input (Danilov + Grothendieck–Lefschetz)**: `τ'_𝕜 = p'_𝕜 ∘ ι_X` is the blow-up of
  `G/P'` along `Z'_𝕜`. -/
  isBlowUp' : ∀ (𝕜 : Type) [Field 𝕜],
    Work.CY3.IsBlowUpAlong (baseChangeZMap 𝕜 (iotaXZ ≫ p')) (baseChangeZMap 𝕜 iotaZZ')
  /-- **Named input** (the last sentence of the proof of `thm:CY3` and item (L3) of an L-link):
  the birational map `ψ_𝕜 = τ'_𝕜 ∘ τ_𝕜⁻¹ : G_𝕜/P_𝕜 ⇢ G_𝕜/P'_𝕜` with its two exceptional divisors,
  base-change-uniformly in `𝕜`. -/
  link : ∀ (𝕜 : Type) [Field 𝕜],
    LinkData 𝕜 (baseChangeZ 𝕜 GP) (baseChangeZ 𝕜 GP')

attribute [instance] CY3ZModel.overXZ CY3ZModel.overZZ CY3ZModel.overZZ' CY3ZModel.isOverIotaXZ
  CY3ZModel.isOverIotaZZ CY3ZModel.isOverIotaZZ'
  CY3ZModel.isClosedImmersionIotaXZ CY3ZModel.isClosedImmersionIotaZZ
  CY3ZModel.isClosedImmersionIotaZZ'
  CY3ZModel.geomIntXZ CY3ZModel.geomIntZZ CY3ZModel.geomIntZZ'
  CY3ZModel.sepXZ CY3ZModel.lofinXZ CY3ZModel.qcXZ CY3ZModel.sepZZ CY3ZModel.lofinZZ
  CY3ZModel.qcZZ CY3ZModel.sepZZ' CY3ZModel.lofinZZ' CY3ZModel.qcZZ'

namespace CY3ZModel

variable (M : CY3ZModel)

/-- **The morphism `τ_ℤ : X_ℤ ⟶ G/P` of the paper's diagram**: the restriction of the projection
`p : G/B ⟶ G/P` to the zero locus `X_ℤ = Z(σ) ⊂ G/B`.  The paper's commutative diagram determines
`τ` from `ι_X` and `p` (`τ = p ∘ ι_X`), so this is a *definition*, not a field of the model. -/
abbrev tauZ : M.XZ ⟶ M.GP := M.iotaXZ ≫ M.p

/-- **The morphism `τ'_ℤ : X_ℤ ⟶ G/P'`**: `τ' = p' ∘ ι_X`. -/
abbrev tauZ' : M.XZ ⟶ M.GP' := M.iotaXZ ≫ M.p'

/-- **The paper's diagram commutes over `𝕜`**, first leg: `τ_𝕜 = p_𝕜 ∘ ι_X` is the base change of
`τ_ℤ = p ∘ ι_X`, computed by `Work.G2.baseChangeZMap_comp`. -/
theorem tau_eq (𝕜 : Type) [Field 𝕜] :
    baseChangeZMap 𝕜 M.tauZ = baseChangeZMap 𝕜 M.iotaXZ ≫ baseChangeZMap 𝕜 M.p :=
  baseChangeZMap_comp 𝕜 M.iotaXZ M.p

/-- **The paper's diagram commutes over `𝕜`**, second leg. -/
theorem tau'_eq (𝕜 : Type) [Field 𝕜] :
    baseChangeZMap 𝕜 M.tauZ' = baseChangeZMap 𝕜 M.iotaXZ ≫ baseChangeZMap 𝕜 M.p' :=
  baseChangeZMap_comp 𝕜 M.iotaXZ M.p'

/-- **The zero locus `X_𝕜 ⊂ G_𝕜/B_𝕜` is a closed subvariety over `𝕜`** — proved from the
`ℤ`-level closed immersion, since closed immersions are stable under base change
(`Work.G2.isClosedImmersion_baseChangeZMap`). -/
theorem isClosedImmersion_iotaXZ (𝕜 : Type) [Field 𝕜] :
    IsClosedImmersion (baseChangeZMap 𝕜 M.iotaXZ) :=
  isClosedImmersion_baseChangeZMap 𝕜 M.iotaXZ

/-- **The centre `Z_𝕜 ⊂ G_𝕜/P_𝕜` is a closed subvariety over `𝕜`.** -/
theorem isClosedImmersion_iotaZZ (𝕜 : Type) [Field 𝕜] :
    IsClosedImmersion (baseChangeZMap 𝕜 M.iotaZZ) :=
  isClosedImmersion_baseChangeZMap 𝕜 M.iotaZZ

/-- **The centre `Z'_𝕜 ⊂ G_𝕜/P'_𝕜` is a closed subvariety over `𝕜`.** -/
theorem isClosedImmersion_iotaZZ' (𝕜 : Type) [Field 𝕜] :
    IsClosedImmersion (baseChangeZMap 𝕜 M.iotaZZ') :=
  isClosedImmersion_baseChangeZMap 𝕜 M.iotaZZ'

/-- **The `𝕜`-counterpart of the `ℤ`-model of Layer 2**: the datum
`Work.CY3.CY3Section 𝕜` consumed by Layer 3 of the CY3 area.

All schemes are base changes of the `ℤ`-schemes of the model, all five morphisms are the
base-changed morphisms `Work.G2.baseChangeZMap`, their `Variety` instances are
`Work.G2.instVarietyZ` and their `IsOver` instances are *proved*
(`Work.G2.baseChangeZMap_isOver`); Bertini, Danilov + Grothendieck–Lefschetz and the identification
of the exceptional divisors are the named inputs of the model, base-change-uniformly in `𝕜`. -/
def toCY3Section (𝕜 : Type) [Field 𝕜] [Infinite 𝕜] : Work.CY3.CY3Section 𝕜 where
  -- Layer 1
  B := baseChangeZ 𝕜 M.GB
  varietyB := instVarietyZ 𝕜 M.GB
  P := baseChangeZ 𝕜 M.GP
  varietyP := instVarietyZ 𝕜 M.GP
  P' := baseChangeZ 𝕜 M.GP'
  varietyP' := instVarietyZ 𝕜 M.GP'
  p := baseChangeZMap 𝕜 M.p
  isOverP := baseChangeZMap_isOver 𝕜 M.p
  p' := baseChangeZMap 𝕜 M.p'
  isOverP' := baseChangeZMap_isOver 𝕜 M.p'
  isG2_P := M.isG2_P 𝕜
  isG2_P' := M.isG2_P' 𝕜
  stronglyRational_P := M.stronglyRational_P 𝕜
  stronglyRational_P' := M.stronglyRational_P' 𝕜
  smooth_p := smooth_baseChangeZMap 𝕜 M.p
  smooth_p' := smooth_baseChangeZMap 𝕜 M.p'
  isP1Fibration_p := M.isP1Fibration_p 𝕜
  isP1Fibration_p' := M.isP1Fibration_p' 𝕜
  lineBundle := M.lineBundle 𝕜
  -- Layer 2
  X := baseChangeZ 𝕜 M.XZ
  varietyX := instVarietyZ 𝕜 M.XZ
  iotaX := baseChangeZMap 𝕜 M.iotaXZ
  isOverIotaX := baseChangeZMap_isOver 𝕜 M.iotaXZ
  Z := baseChangeZ 𝕜 M.ZZ
  varietyZ := instVarietyZ 𝕜 M.ZZ
  iotaZ := baseChangeZMap 𝕜 M.iotaZZ
  isOverIotaZ := baseChangeZMap_isOver 𝕜 M.iotaZZ
  Z' := baseChangeZ 𝕜 M.ZZ'
  varietyZ' := instVarietyZ 𝕜 M.ZZ'
  iotaZ' := baseChangeZMap 𝕜 M.iotaZZ'
  isOverIotaZ' := baseChangeZMap_isOver 𝕜 M.iotaZZ'
  generalSection := M.generalSection 𝕜
  tau := baseChangeZMap 𝕜 M.tauZ
  isOverTau := baseChangeZMap_isOver 𝕜 M.tauZ
  tau' := baseChangeZMap 𝕜 M.tauZ'
  isOverTau' := baseChangeZMap_isOver 𝕜 M.tauZ'
  isBlowUp := M.isBlowUp 𝕜
  isBlowUp' := M.isBlowUp' 𝕜
  psi := (M.link 𝕜).psi
  isOverPsi := (M.link 𝕜).isOver
  x := (M.link 𝕜).x
  exDiv_psi := (M.link 𝕜).exDiv_psi
  y := (M.link 𝕜).y
  exDiv_psi_symm := (M.link 𝕜).exDiv_psi_symm

end CY3ZModel

end

end Work.G2
