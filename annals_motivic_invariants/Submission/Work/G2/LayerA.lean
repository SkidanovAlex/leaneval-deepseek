import Submission.Work.G2.BaseChangeAPI
import Submission.Work.G2.isStronglyRational_of_exDiv_eq_singletons

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.G2.LayerA` — the `ℤ`-model of Layer 1 of `thm:CY3` (the `G₂`-Grassmannian infrastructure)

This file is the **producer** of Layer 1 of the CY3 chapter
(`Submission/Work/CY3/G2.lean`, structure `Work.CY3.G2Grassmannian`): the `ℤ`-model of the split
simply connected simple group scheme `G` of type `G₂` with its Borel `B`, its two maximal
parabolics `P, P'` and the quotients `G/B`, `G/P`, `G/P'`, together with the bundle-theoretic facts
about the two projections.

## Why a `ℤ`-model

The paper's construction *is* over `ℤ`:

> Let `G` be the connected and simply connected split simple group scheme of type `G₂` over `ℤ`.
> Let `B ⊂ G` be the Borel subgroup, and `P, P' ⊊ G` the two maximal parabolic subgroups of `G`
> containing `B`.  The quotients `G/B`, `G/P`, `G/P'` are smooth and projective over `ℤ`
> by [Milne, Thm 13.33] and [SGA3, Cor. XXII.5.8.5].  The natural projection `p : G/B → G/P` is
> also smooth.  Since `p_ℚ` is a `ℙ¹`-fibration, so is `p`.  Likewise, the other projection. …
> `Pic(G/P) ≅ X^*(P) ≅ ℤ` [Raynaud, Prop. VII.1.5] … `L ≔ p*M ⊗ p'*M'` is then ample …
> It follows that `E ≔ p_*L` is locally free of rank `2` and `G/B ≅ ℙ(E)` over `G/P`.

Every fact here is a `Spec ℤ`-statement, so the *same* datum is available over every field `𝕜` by
base change — this is how the paper extends `thm:CY3` from characteristic zero (Ito–Miura–Okawa–
Ueda) to an arbitrary infinite field.

## What is a named input and what is proved

`Work.G2.G2ZModel` carries:

* the `ℤ`-schemes `GB`, `GP`, `GP'` with their `Spec ℤ`-structure, **geometric integrality**
  (which is what makes their base changes `𝕜`-varieties) and separated / locally-of-finite-type /
  quasicompact structure morphisms;
* the two projections `p`, `p'`, over `Spec ℤ` and **smooth** (`Milne` Thm 13.33, `SGA3`
  Cor. XXII.5.8.5);
* the *uniform* clauses: for every field `𝕜`, the base-changed quotients are the two
  `G₂`-Grassmannians (`IsG2Grassmannian`: smooth projective of Picard rank one, `[G/P] = [ℙ⁵]`), the
  projections are `ℙ¹`-fibrations, and the very ample bundle `L = p*M ⊗ p'*M'` with
  `G/B ≅ ℙ(E)` exists (`HasCyLineBundle`: Raynaud Prop. VII.1.5 + Remark VII.1.7 a), `IMOUG2`,
  RamRam Thm 3);
* the *Bruhat chart* clauses `bruhatChart_P`, `bruhatChart_P'` — the paper's geometric input for
  `lem:GP-strongly-rational`: a birational map of `G_𝕜/P_𝕜` (resp. `G_𝕜/P'_𝕜`) to `ℙ⁵_𝕜` with a
  single exceptional divisor on each side and equal function fields (the Bruhat decomposition has a
  single cell in every dimension, so `G/P ∖ D ≅ 𝔸⁵` with `D` an irreducible rational divisor).

**Proved** in this file (from the `ℤ`-data alone, for every field `𝕜`):

* `Work.G2.G2ZModel.toG2Grassmannian` — the `𝕜`-counterpart `Work.CY3.G2Grassmannian 𝕜` of the
  model: the base-changed schemes and projections with their `Variety` instances
  (`Work.G2.instVarietyZ`), `IsOver`-ness (`Work.G2.baseChangeZMap_isOver`) and smoothness
  (`Work.G2.smooth_baseChangeZMap`) — none of these is assumed at the level of `𝕜`;
* `Work.G2.G2ZModel.stronglyRational_P`, `Work.G2.G2ZModel.stronglyRational_P'` — the paper's
  `lem:GP-strongly-rational`: **the two quotients are strongly rational** at every field, derived
  from the Bruhat chart clauses by `Work.G2.isStronglyRational_of_exDiv_eq_singletons`; this is a
  field of the CY3 chapter's `G2Grassmannian`, and it is here a theorem, not an input;
* `Work.G2.G2ZModel.stronglyBirational` — item (L2) of the definition of an L-link for the two
  `G₂`-Grassmannians, at every field, by additivity of the invariant;
* `Work.G2.G2ZModel.dimensional` — the two quotients are fivefolds, at every field.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

namespace Work.G2

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

noncomputable section

/-- **The `ℤ`-model of Layer 1 of `thm:CY3`.**

The schemes `GB`, `GP`, `GP'` are the quotients `G/B`, `G/P`, `G/P'` of the split simply connected
simple group scheme `G` of type `G₂` over `ℤ`, and `p`, `p'` the two projections; the remaining
fields are the named inputs of Layer 1 of `Work.CY3.G2Grassmannian`, stated over `ℤ` where the
paper states them over `ℤ` and base-change-uniformly where the paper's statement is about the
quotients over `𝕜` (this is the paper's own "the construction extends to an arbitrary infinite
field" argument). -/
structure G2ZModel where
  /-- `G/B`, the flag variety of the split `G₂` over `ℤ`. -/
  GB : Scheme.{0}
  [overGB : GB.Over (Spec (.of ℤ))]
  [geomIntGB : GeometricallyIntegral (GB ↘ Spec (.of ℤ))]
  [sepGB : IsSeparated (GB ↘ Spec (.of ℤ))]
  [lofinGB : LocallyOfFiniteType (GB ↘ Spec (.of ℤ))]
  [qcGB : QuasiCompact (GB ↘ Spec (.of ℤ))]
  /-- `G/P`, the first five-dimensional `G₂`-Grassmannian over `ℤ`. -/
  GP : Scheme.{0}
  [overGP : GP.Over (Spec (.of ℤ))]
  [geomIntGP : GeometricallyIntegral (GP ↘ Spec (.of ℤ))]
  [sepGP : IsSeparated (GP ↘ Spec (.of ℤ))]
  [lofinGP : LocallyOfFiniteType (GP ↘ Spec (.of ℤ))]
  [qcGP : QuasiCompact (GP ↘ Spec (.of ℤ))]
  /-- `G/P'`, the second five-dimensional `G₂`-Grassmannian over `ℤ`. -/
  GP' : Scheme.{0}
  [overGP' : GP'.Over (Spec (.of ℤ))]
  [geomIntGP' : GeometricallyIntegral (GP' ↘ Spec (.of ℤ))]
  [sepGP' : IsSeparated (GP' ↘ Spec (.of ℤ))]
  [lofinGP' : LocallyOfFiniteType (GP' ↘ Spec (.of ℤ))]
  [qcGP' : QuasiCompact (GP' ↘ Spec (.of ℤ))]
  /-- the projection `p : G/B ⟶ G/P`. -/
  p : GB ⟶ GP
  [isOverP : p.IsOver (Spec (.of ℤ))]
  /-- the projection `p' : G/B ⟶ G/P'`. -/
  p' : GB ⟶ GP'
  [isOverP' : p'.IsOver (Spec (.of ℤ))]
  /-- **Named input** (`Milne` Thm 13.33, `SGA3` Cor. XXII.5.8.5): the projection `G/B → G/P` is
  smooth — a quotient of a smooth `ℤ`-scheme by a smooth connected group scheme. -/
  smooth_p : Smooth p
  /-- **Named input**: the projection `G/B → G/P'` is smooth. -/
  smooth_p' : Smooth p'
  /-- **Named input** (`Milne` Thm 13.33, `SGA3` Cor. XXII.5.8.5; `Raynaud`;
  `lem:GP-strongly-rational`): `G/P` is the `G₂`-Grassmannian — smooth projective over `𝕜`, of
  Picard rank one, of motivic class `[ℙ⁵]`.  Stated base-change-uniformly, i.e. for every field. -/
  isG2_P : ∀ (𝕜 : Type) [Field 𝕜], Work.CY3.IsG2Grassmannian 𝕜 (baseChangeZ 𝕜 GP)
  /-- **Named input**: the same for `G/P'`. -/
  isG2_P' : ∀ (𝕜 : Type) [Field 𝕜], Work.CY3.IsG2Grassmannian 𝕜 (baseChangeZ 𝕜 GP')
  /-- **Named input (the Bruhat decomposition of `G/P`; paper `lem:GP-strongly-rational` and its
  proof)**: over every field `𝕜` there is a birational map `φ : G_𝕜/P_𝕜 ⇢ ℙ⁵_𝕜` whose exceptional
  divisors on the two sides are single points with the *same* function field.  Concretely (paper):
  `G/P` has a Bruhat decomposition with a single cell in every dimension, so `U := G/P ∖ D ≅ 𝔸⁵`
  for an irreducible rational divisor `D`, and the induced `φ : G/P ⤏ ℙ⁵` has `exDiv φ = {η_D}`,
  `exDiv φ⁻¹ = {η_H}` (`H` the hyperplane at infinity), with `κ(η_D) ≅ κ(η_H) = κ(ℙ⁴)` because `D`
  is rational.  This clause *derives* the strong rationality of `G_𝕜/P_𝕜`
  (`Work.G2.G2ZModel.stronglyRational_P`, via `Work.G2.isStronglyRational_of_exDiv_eq_singletons`),
  so that `IsStronglyRational` is a theorem of this area, not an input. -/
  bruhatChart_P : ∀ (𝕜 : Type) [Field 𝕜],
    ∃ (φ : (baseChangeZ 𝕜 GP).BirationalMap (Work.CY3.ProjectiveSpace 𝕜 5))
      (x : baseChangeZ 𝕜 GP) (h : Work.CY3.ProjectiveSpace 𝕜 5),
      (φ.IsOver (Spec (.of 𝕜))) ∧ exDiv φ = {x} ∧ exDiv φ.symm = {h} ∧ ResEquiv 𝕜 x h
  /-- **Named input**: the same Bruhat data for `G/P'`. -/
  bruhatChart_P' : ∀ (𝕜 : Type) [Field 𝕜],
    ∃ (φ : (baseChangeZ 𝕜 GP').BirationalMap (Work.CY3.ProjectiveSpace 𝕜 5))
      (x : baseChangeZ 𝕜 GP') (h : Work.CY3.ProjectiveSpace 𝕜 5),
      (φ.IsOver (Spec (.of 𝕜))) ∧ exDiv φ = {x} ∧ exDiv φ.symm = {h} ∧ ResEquiv 𝕜 x h
  /-- **Named input**: `p : G/B → G/P` is a `ℙ¹`-fibration — a fibre is `P_𝕜/B_𝕜 ≃ ℙ¹_𝕜` (the two
  Borels of `G₂` are conjugate inside the parabolic), stated uniformly over `Spec ℤ`. -/
  isP1Fibration_p : ∀ (𝕜 : Type) [Field 𝕜], Work.CY3.IsP1Fibration (baseChangeZMap 𝕜 p)
  /-- **Named input**: `p' : G/B → G/P'` is a `ℙ¹`-fibration. -/
  isP1Fibration_p' : ∀ (𝕜 : Type) [Field 𝕜], Work.CY3.IsP1Fibration (baseChangeZMap 𝕜 p')
  /-- **Named input** (`Raynaud` Prop. VII.1.5 + Remark VII.1.7 a); `IMOUG2`; `RamRam` Thm 3):
  the ample generators `M`, `M'` of the two Picard groups `Pic(G/P) ≅ X^*(P) ≅ ℤ`,
  `Pic(G/P') ≅ ℤ`, the very ampleness of `L = p*M ⊗ p'*M'`, `deg(L|_{ℙ¹-fibre}) = 1` and
  `G/B ≅ ℙ(E)` for the rank-two `E = p_*L`, uniformly in the field. -/
  lineBundle : ∀ (𝕜 : Type) [Field 𝕜],
    Work.CY3.HasCyLineBundle 𝕜 (baseChangeZ 𝕜 GB) (baseChangeZ 𝕜 GP) (baseChangeZ 𝕜 GP')
      (baseChangeZMap 𝕜 p) (baseChangeZMap 𝕜 p')

attribute [instance] G2ZModel.overGB G2ZModel.overGP G2ZModel.overGP' G2ZModel.isOverP
  G2ZModel.isOverP' G2ZModel.geomIntGB G2ZModel.geomIntGP G2ZModel.geomIntGP'
  G2ZModel.sepGB G2ZModel.lofinGB G2ZModel.qcGB G2ZModel.sepGP
  G2ZModel.lofinGP G2ZModel.qcGP G2ZModel.sepGP' G2ZModel.lofinGP' G2ZModel.qcGP'
  G2ZModel.smooth_p G2ZModel.smooth_p'

namespace G2ZModel

variable (M : G2ZModel)

/-- **The paper's `lem:GP-strongly-rational`: `G_𝕜/P_𝕜` is strongly rational.**

*Proved* from the Bruhat chart clause `bruhatChart_P` by
`Work.G2.isStronglyRational_of_exDiv_eq_singletons`: the paper's argument is
"`φ : X ← U ≃ 𝔸ⁿ ↪ ℙⁿ` has `c(φ) = [ℙ^{n-1}] − [D] = 0`" — here, the two exceptional divisors of
`φ` have the same function field, so every coefficient of `c(φ)` vanishes. -/
theorem stronglyRational_P (𝕜 : Type) [Field 𝕜] :
    Work.CY3.IsStronglyRational 𝕜 (baseChangeZ 𝕜 M.GP) 5 := by
  obtain ⟨φ, x, h, hφ, hx, hh, hr⟩ := M.bruhatChart_P 𝕜
  haveI : φ.IsOver (Spec (.of 𝕜)) := hφ
  exact Work.G2.isStronglyRational_of_exDiv_eq_singletons φ hx hh hr

/-- **The paper's `lem:GP-strongly-rational` for `G/P'`.** -/
theorem stronglyRational_P' (𝕜 : Type) [Field 𝕜] :
    Work.CY3.IsStronglyRational 𝕜 (baseChangeZ 𝕜 M.GP') 5 := by
  obtain ⟨φ, x, h, hφ, hx, hh, hr⟩ := M.bruhatChart_P' 𝕜
  haveI : φ.IsOver (Spec (.of 𝕜)) := hφ
  exact Work.G2.isStronglyRational_of_exDiv_eq_singletons φ hx hh hr

/-- **The `𝕜`-counterpart of the `ℤ`-model of Layer 1**: the datum
`Work.CY3.G2Grassmannian 𝕜` consumed by the rest of the CY3 area.

Every scheme is the base change `X_ℤ ×_{Spec ℤ} Spec 𝕜`, every morphism is the base-changed
morphism `Work.G2.baseChangeZMap`, the `Variety` instances are *proved*
(`Work.G2.instVarietyZ`), the `IsOver` instances are *proved*
(`Work.G2.baseChangeZMap_isOver`) and the smoothness of the two projections is *proved*
(`Work.G2.smooth_baseChangeZMap`); the remaining fields are the named inputs of the model. -/
def toG2Grassmannian (𝕜 : Type) [Field 𝕜] : Work.CY3.G2Grassmannian 𝕜 where
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

/-- The base-changed projection of the model is a `ℙ¹`-fibration. -/
theorem isP1Fibration (𝕜 : Type) [Field 𝕜] :
    Work.CY3.IsP1Fibration (M.toG2Grassmannian 𝕜).p :=
  M.isP1Fibration_p 𝕜

/-- **(L2) of an L-link for the two `G₂`-Grassmannians, at every field**: the paper's
`lemma:L-link` (2) needs the two sides of the link to be strongly birational, and this is
`lem:GP-strongly-rational` combined with additivity of the invariant
(`Work.CY3.G2Grassmannian.stronglyBirational`). -/
theorem stronglyBirational (𝕜 : Type) [Field 𝕜] :
    Work.CY3.StronglyBirational 𝕜 (baseChangeZ 𝕜 M.GP) (baseChangeZ 𝕜 M.GP') :=
  (M.toG2Grassmannian 𝕜).stronglyBirational

/-- **The two `G₂`-Grassmannians are fivefolds**, at every field: this is the content of the `5`
in the strong rationality, and it is why the CY3 link is a link in `ℙ⁵` and provides the
`n = 5` case of Theorem 1.2 (3) of the challenge. -/
theorem dimensional (𝕜 : Type) [Field 𝕜] :
    Work.CY3.IsStronglyRational 𝕜 (baseChangeZ 𝕜 M.GP) 5 ∧
      Work.CY3.IsStronglyRational 𝕜 (baseChangeZ 𝕜 M.GP') 5 :=
  (M.toG2Grassmannian 𝕜).stronglyRational

end G2ZModel

end

end Work.G2
