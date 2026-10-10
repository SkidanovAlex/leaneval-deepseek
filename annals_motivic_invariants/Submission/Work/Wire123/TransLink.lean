import Submission.Work.CY3.Link
import Submission.Work.Wire123.Defs
import Submission.Work.Wire123.LeanLink

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.Wire123.TransLink` — the `n ≥ 5` residual *without* the transport hypotheses

`Work.Wire123.LeanLink` (and, before it, `Work.CY3.CY3Data`) requires, besides the L-link itself,

* two *transports* `eps : 𝔸⁵ ⇢ P`, `delta : P' ⇢ 𝔸⁵`, and
* the two *vanishing conditions* `cInv 𝕜 z₀ eps = 0`, `cInv 𝕜 z₀ delta = 0`
  (the paper's use of `lem:GP-strongly-rational`: the transports used in the paper are strongly
  rational maps, hence have all coefficients zero).

**None of that is needed.**  The reason is the *conjugation invariance* of the coefficient
(`Work.CrauderKatz.cInv_conj_eq`, proved in the workspace):

  `cInv 𝕜 z (ψ.trans (σ.trans ψ.symm)) = cInv 𝕜 z σ`  for every `ψ : S ⇢ T`, `σ : T ⇢ T` over `𝕜`,

i.e. the coefficient of a birational map is unchanged by transporting it to any other model along a
map defined on a *dense open* (no vanishing condition on the transport).  Consequently:

* a `delta : P' ⇢ 𝔸⁵` is never used — the link `ψ : P ⇢ P'` is closed into a self-map of `P` by the
  *strong birationality* `γ : P ⇢ P'` (paper (L2)): `φ := ψ.trans γ.symm` has
  `cInv 𝕜 z₀ φ = cInv 𝕜 z₀ ψ - cInv 𝕜 z₀ γ = 1`;
* the transport to `𝔸⁵` may be *any* birational map `iota : 𝔸⁵ ⇢ P` over `𝕜`: conjugating `φ` along
  it preserves the coefficient exactly, so it contributes nothing and needs no hypothesis.

`TransLink 𝕜` is therefore the *honest* residual: the paper's L-link data (the link, its two
exceptional divisors, the two centres with their `ℙ¹`-bundles, the base point, the bridge and
Totaro's conclusion), the paper's (L2) `StronglyBirational 𝕜 P P'`, and one birational map
`𝔸⁵ ⇢ P` over `𝕜`.  Everything else is *proved* here:

* `Work.Wire123.LeanLink.toTransLink` — a `LeanLink` is a `TransLink` (the transport hypotheses are
  redundant, so nothing is lost);
* `Work.Wire123.not_gen_of_transLink_five` — `TransLink 𝕜 → ¬ GenByPseudoRegularizable 𝕜 5`,
  by the conjugation argument above;
* `Work.Wire123.theorem_1_2_3_of_transLink` — the same for every `n ≥ 5`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

namespace Work.Wire123

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

noncomputable section

/-- **The `n ≥ 5` residual, with the transport hypotheses deleted.**

Fields are those of `Work.Wire123.LeanLink` except that `eps`, `delta`, `cInv_eps`, `cInv_delta`
are replaced by a *single* birational map `iota : 𝔸⁵ ⇢ P` over `𝕜` (no coefficient condition). -/
structure TransLink (𝕜 : Type) [Field 𝕜] where
  /-- the ambient fivefold of the link (`G/P` in the paper). -/
  P : Scheme.{0}
  [varietyP : Variety 𝕜 P]
  /-- the target fivefold of the link (`G/P'` in the paper). -/
  P' : Scheme.{0}
  [varietyP' : Variety 𝕜 P']
  /-- the L-link `ψ = τ' ∘ τ⁻¹`. -/
  psi : P.BirationalMap P'
  [isOverPsi : psi.IsOver (Spec (.of 𝕜))]
  /-- the exceptional divisor of `ψ`. -/
  x : P
  /-- the exceptional divisor of `ψ⁻¹`. -/
  y : P'
  /-- `ψ` has no other exceptional divisor. -/
  exDiv_psi : exDiv psi = {x}
  /-- `ψ⁻¹` has no other exceptional divisor. -/
  exDiv_psi_symm : exDiv psi.symm = {y}
  /-- the first centre. -/
  Z : Scheme.{0}
  [varietyZ : Variety 𝕜 Z]
  /-- the second centre. -/
  Z' : Scheme.{0}
  [varietyZ' : Variety 𝕜 Z']
  /-- `K`-triviality of the first centre (fieldless named predicate). -/
  isKTrivial_Z : Work.CY3.IsKTrivial 𝕜 Z
  /-- `K`-triviality of the second centre. -/
  isKTrivial_Z' : Work.CY3.IsKTrivial 𝕜 Z'
  /-- Picard rank one of the first centre (fieldless named predicate). -/
  picardOne_Z : Work.CY3.PicardRankOne 𝕜 Z
  /-- Picard rank one of the second centre. -/
  picardOne_Z' : Work.CY3.PicardRankOne 𝕜 Z'
  /-- a model of `Z × ℙ¹` (only its point `z₀` and the identification are used). -/
  ZW : Scheme.{0}
  [overZW : ZW.Over (Spec (.of 𝕜))]
  /-- the base point of the invariant. -/
  z₀ : ZW
  /-- `κ(y) ≅ κ(z₀)`. -/
  resEquiv_y : ResEquiv 𝕜 y z₀
  /-- (F1): `y` is a `ℙ¹`-bundle over the first centre. -/
  p1Bundle_y : Work.K3Inputs.IsP1BundleOver 𝕜 y Z
  /-- (F1): `x` is a `ℙ¹`-bundle over the second centre. -/
  p1Bundle_x : Work.K3Inputs.IsP1BundleOver 𝕜 x Z'
  /-- **(L2)**: the two sides of the link are *strongly* birational to each other.  This is the
  paper's `lem:GP-strongly-rational` input; it is what converts the link into a self-map of `P`
  (`ψ.trans γ.symm`) with the same coefficient. -/
  stronglyBirational : Work.CY3.StronglyBirational 𝕜 P P'
  /-- **the transport**: any birational map `𝔸⁵ ⇢ P` over `𝕜`; no coefficient condition. -/
  iota : (Work.CY3.Affine 𝕜 5).BirationalMap P
  [isOverIota : iota.IsOver (Spec (.of 𝕜))]
  /-- the `ℙ¹`-bundle bridge: an isomorphism of the two cylinder fields forces stable
  birationality of the two centres. -/
  bridge : ResEquiv 𝕜 y x → Work.CY3.StablyBirational 𝕜 Z Z'
  /-- the conclusion of Totaro's `cor-CYnSB` at the two centres. -/
  not_stablyBirat : ¬ Work.CY3.StablyBirational 𝕜 Z' Z

attribute [instance] TransLink.varietyP TransLink.varietyP' TransLink.isOverPsi TransLink.varietyZ
  TransLink.varietyZ' TransLink.overZW TransLink.isOverIota

/-- **Stable birationality is symmetric** (the definition quantifies over the two shifts
existentially, so the two sides can be exchanged). -/
theorem stablyBirational_symm {𝕜 : Type} [Field 𝕜] {X Y : Scheme.{0}} [Variety 𝕜 X]
    [Variety 𝕜 Y] (h : Work.K3.StablyBirational 𝕜 X Y) :
    Work.K3.StablyBirational 𝕜 Y X := by
  obtain ⟨n, m, hVX, hVY, hφ⟩ := h
  exact ⟨m, n, hVY, hVX, hφ.map (fun f => f.symm)⟩

namespace TransLink

variable {𝕜 : Type} [Field 𝕜] (D : TransLink 𝕜)

/-- **The two exceptional divisors have non-isomorphic function fields.**  This is the content of
the `bridge` + Totaro fields (paper `lem-nSBG2`): an isomorphism of the function fields would make
the two centres stably birational, contradicting Totaro's theorem at the pair. -/
theorem not_resEquiv_yx : ¬ ResEquiv 𝕜 D.y D.x := fun hres =>
  D.not_stablyBirat (stablyBirational_symm (D.bridge hres))

/-- The base point's class is that of `y` and *not* that of `x`. -/
theorem not_resEquiv_x_z₀ : ¬ ResEquiv 𝕜 D.x D.z₀ := fun h =>
  D.not_resEquiv_yx
    (Work.Motivic.ResEquiv.symm
      (Work.Motivic.ResEquiv.trans h (Work.Motivic.ResEquiv.symm D.resEquiv_y)))

end TransLink

end

end Work.Wire123
