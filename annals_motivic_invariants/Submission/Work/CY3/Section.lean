import Submission.Work.CY3.G2

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.CY3.Section` — Layer 2: the general section, its zero loci, and the blow-up structure

This file records the **second layer** of the CY3 construction of Lin–Shinder,
*Motivic invariants of birational maps* (Annals **199** (1), 2024, § *K-trivial threefolds*): the
general section `σ` of the very ample bundle `L = p*M ⊗ p'*M'` of Layer 1, its zero locus
`X_𝕜 = Z(σ) ⊂ G_𝕜/B_𝕜` and the zero loci `Z_𝕜 = Z(p_*σ) ⊂ G_𝕜/P_𝕜`,
`Z'_𝕜 = Z(p'_*σ) ⊂ G_𝕜/P'_𝕜` of the pushforwards, together with the blow-up structure
`τ : X_𝕜 → G_𝕜/P_𝕜`, `τ' : X_𝕜 → G_𝕜/P'_𝕜`, the birational map `ψ = τ' ∘ τ⁻¹` and its two
exceptional divisors.

## The paper's Layer 2

> Now let `𝕜` be an infinite field and let `σ ∈ H⁰(G_𝕜/B_𝕜, L_𝕜)` be a general section.  Let
> `X_𝕜 = Z(σ) ⊂ G_𝕜/B_𝕜` and let `Z_𝕜 ≔ Z(p_*σ) ⊂ G_𝕜/P_𝕜` with `p_*σ` regarded as a section of
> `E_𝕜 = (p_*L)_𝕜`.  Similarly, let `Z'_𝕜 ≔ Z(p'_*σ) ⊂ G_𝕜/P'_𝕜`.  Since `L_𝕜` is very ample
> [RamRam, Theorem 3] and `𝕜` is infinite, `X_𝕜` is smooth by Bertini's theorem [Jouanolou,
> Thm 6.3], [Mukai, Thm 1.10].  Consider the commutative diagram ... which defines the maps `τ`
> and `τ'`.  By construction, `τ` maps `X_𝕜 ∖ τ⁻¹(Z_𝕜)` isomorphically onto its image and
> `τ⁻¹(Z_𝕜) → Z_𝕜` is a `ℙ¹`-fibration.  By [Danilov, Theorem 2], `τ` is thus a sequence of blow
> ups along smooth centers of codimension `2` lying above `Z_𝕜`.  Since `X_𝕜` has Picard rank
> `ρ(X_𝕜) = ρ(G_𝕜/B_𝕜) = 2` by Grothendieck–Lefschetz' theorem, necessarily `τ` is the blow up of
> `G_𝕜/P_𝕜` along `Z_𝕜` and `Z_𝕜` is connected.  Similarly, `τ'` is the blow up of `G_𝕜/P'_𝕜`
> along `Z'_𝕜`, and `Z'_𝕜` is connected.  We thus have a birational map
> `ψ ≔ τ' ∘ τ⁻¹ : G_𝕜/P_𝕜 ⇢ G_𝕜/P'_𝕜`.  By construction, `ψ` is regular away from `Z_𝕜` and
> `ψ⁻¹` is regular away from `Z'_𝕜`.

Everything in this paragraph is outside Mathlib (no cohomology of line bundles, no blow-up, no
Bertini, no Grothendieck–Lefschetz, no Picard rank): the paragraph is recorded as the structure
`Work.CY3.CY3Section` of named inputs.

## The named inputs of this layer

* `Work.CY3.IsGeneralSectionZeroLocus` — **Bertini**: `X`, `Z`, `Z'` are the zero loci of a
  general section `σ` of the very ample `L` and of its two pushforwards, and `X` is smooth, `Z`,
  `Z'` are the codimension-two smooth centres, with `τ⁻¹(Z) → Z` a `ℙ¹`-fibration (the *only* place
  where `𝕜` infinite is used, per the paper's remark);
* `Work.CY3.IsBlowUpAlong` — **Danilov + Grothendieck–Lefschetz**: `τ` is the blow-up of `G/P`
  along the smooth codimension-two centre `Z` (Danilov's decomposition theorem plus
  Grothendieck–Lefschetz, which forces the sequence of blow-ups to consist of the single blow-up
  along `Z`), and similarly for `τ'`;
* the fields `psi`, `x`, `y`, `exDiv_psi`, `exDiv_psi_symm` — the birational map `ψ = τ' ∘ τ⁻¹`
  and the identification of its two exceptional divisors (`ψ` regular away from `Z_𝕜`, `ψ⁻¹` regular
  away from `Z'_𝕜`).

## What is used downstream

Only `ψ`, `exDiv ψ = {x}` and `exDiv ψ⁻¹ = {y}` are used by the invariant computation (Layer 3);
the section, the zero loci and the blow-up identifications are what *produces* them, and are
recorded so that a producer of the CY3 datum knows exactly what to build.  See `NOTES.md`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

namespace Work.CY3

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

noncomputable section

/-- **Named input (Bertini; paper's Layer 2): the general section and its three zero loci.**

`IsGeneralSectionZeroLocus 𝕜 B X P Z P' Z' ιX ιZ ιZ'` says that `X ⊂ B`, `Z ⊂ P`, `Z' ⊂ P'` are
the zero loci of a *general* section `σ ∈ H⁰(G/B, L)` of the very ample bundle
`L = p*M ⊗ p'*M'` of `HasCyLineBundle`, respectively of the pushed-forward sections `p_*σ`,
`p'_*σ` (via the rank-two bundle `E = p_*L` with `G/B ≅ ℙ(E)` over `G/P`).  Over an infinite field
this is Bertini's theorem (Jouanolou, *Théorèmes de Bertini et applications*, Thm 6.3; Mukai,
*K3 surfaces of degree 18 and 20*, Thm 1.10): `X_𝕜` is smooth, `Z_𝕜` and `Z'_𝕜` are connected
smooth threefolds of codimension two in `G_𝕜/P_𝕜`, `G_𝕜/P'_𝕜`, and the restrictions
`τ⁻¹(Z_𝕜) → Z_𝕜`, `τ'⁻¹(Z'_𝕜) → Z'_𝕜` are `ℙ¹`-fibrations while
`X_𝕜 ∖ τ⁻¹(Z_𝕜) → G_𝕜/P_𝕜` is an isomorphism onto its image.

This is the *only* place in the whole CY3 area where the hypothesis `Infinite 𝕜` is used (paper,
remark after `thm:CY3`: "the only place where we need the assumption that `𝕜` is infinite is to
guarantee the existence of `σ ∈ H⁰(G_𝕜/B_𝕜, L_𝕜)` such that the vanishing loci `Z_𝕜` and `Z'_𝕜`
are smooth"); it is deliberately not a parameter of the class, so that the *downstream* statements
hold verbatim for finite fields as well.

Mathlib has no cohomology of line bundles, no Bertini, and no zero locus of a section, so this is a
named hypothesis. -/
class IsGeneralSectionZeroLocus (𝕜 : Type) [Field 𝕜] (B : Scheme.{0}) (X : Scheme.{0})
    (P : Scheme.{0}) (Z : Scheme.{0}) (P' : Scheme.{0}) (Z' : Scheme.{0}) (ιX : X ⟶ B)
    (ιZ : Z ⟶ P) (ιZ' : Z' ⟶ P') : Prop

/-- **Named input (Danilov + Grothendieck–Lefschetz): `τ` is the blow-up of `Y` along `Z`.**

`IsBlowUpAlong τ ι` says that the morphism `τ : X ⟶ Y` is the blow-up of `Y` along the (smooth,
connected, codimension-two) closed subscheme `ι : Z ⟶ Y`.  In the paper: "By [Danilov, Theorem 2],
`τ` is thus a sequence of blow ups along smooth centers of codimension `2` lying above `Z_𝕜`.
Since `X_𝕜` has Picard rank `ρ(X_𝕜) = ρ(G_𝕜/B_𝕜) = 2` by Grothendieck–Lefschetz' theorem,
necessarily `τ` is the blow up of `G_𝕜/P_𝕜` along `Z_𝕜` and `Z_𝕜` is connected."  The conclusion
"`Z_𝕜` is connected" and "`τ` is a single blow-up" are part of the predicate.

Mathlib has no blow-up of a scheme along a closed subscheme, so this is a named hypothesis. -/
class IsBlowUpAlong {X Y Z : Scheme.{0}} (τ : X ⟶ Y) (ι : Z ⟶ Y) : Prop

/-- **Layer 2 of `thm:CY3`: the general section, its zero loci and the blow-up structure.**

Extends Layer 1 (`Work.CY3.G2Grassmannian`).  The fields `X`, `Z`, `Z'` are the zero loci of the
general section of `L` and of its two pushforwards; `tau`, `tau'` are the two blow-ups of the
paper's commutative diagram and `isBlowUp`, `isBlowUp'` are Danilov + Grothendieck–Lefschetz;
`psi` is the birational map `ψ = τ' ∘ τ⁻¹`, and the last two fields identify its exceptional
divisors: `x` is the exceptional divisor of `ψ` (birational to `ℙ¹ × Z'`, over `Z'`), `y` the
exceptional divisor of `ψ⁻¹` (birational to `ℙ¹ × Z`, over `Z`).

A producer of this structure has to run the whole of Layer 2 above; everything in Layer 3
(`Work.CY3.CY3Data`, `Work.CY3.CY3Link`) is proved from it. -/
structure CY3Section (𝕜 : Type) [Field 𝕜] extends G2Grassmannian 𝕜 where
  /-- `X_𝕜 = Z(σ) ⊂ G_𝕜/B_𝕜`, the zero locus of the general section. -/
  X : Scheme.{0}
  [varietyX : Variety 𝕜 X]
  /-- the closed immersion `X_𝕜 ↪ G_𝕜/B_𝕜`. -/
  iotaX : X ⟶ B
  [isOverIotaX : iotaX.IsOver (Spec (.of 𝕜))]
  /-- `Z_𝕜 = Z(p_*σ) ⊂ G_𝕜/P_𝕜`, the first centre (a K-trivial threefold of Picard rank 1). -/
  Z : Scheme.{0}
  [varietyZ : Variety 𝕜 Z]
  /-- the closed immersion `Z_𝕜 ↪ G_𝕜/P_𝕜`. -/
  iotaZ : Z ⟶ P
  [isOverIotaZ : iotaZ.IsOver (Spec (.of 𝕜))]
  /-- `Z'_𝕜 = Z(p'_*σ) ⊂ G_𝕜/P'_𝕜`, the second centre. -/
  Z' : Scheme.{0}
  [varietyZ' : Variety 𝕜 Z']
  /-- the closed immersion `Z'_𝕜 ↪ G_𝕜/P'_𝕜`. -/
  iotaZ' : Z' ⟶ P'
  [isOverIotaZ' : iotaZ'.IsOver (Spec (.of 𝕜))]
  /-- **Named input (Bertini)**: `X`, `Z`, `Z'` are the zero loci of the general section of `L`
  and of its two pushforwards, with `X` smooth and `τ⁻¹(Z) → Z` a `ℙ¹`-fibration. -/
  generalSection : IsGeneralSectionZeroLocus 𝕜 B X P Z P' Z' iotaX iotaZ iotaZ'
  /-- the morphism `τ : X_𝕜 → G_𝕜/P_𝕜` of the paper's diagram (Mumford's `Φ`). -/
  tau : X ⟶ P
  [isOverTau : tau.IsOver (Spec (.of 𝕜))]
  /-- the morphism `τ' : X_𝕜 → G_𝕜/P'_𝕜` of the paper's diagram. -/
  tau' : X ⟶ P'
  [isOverTau' : tau'.IsOver (Spec (.of 𝕜))]
  /-- **Named input (Danilov + Grothendieck–Lefschetz)**: `τ` is the blow-up of `G/P` along `Z`. -/
  isBlowUp : IsBlowUpAlong tau iotaZ
  /-- **Named input**: `τ'` is the blow-up of `G/P'` along `Z'`. -/
  isBlowUp' : IsBlowUpAlong tau' iotaZ'
  /-- the birational map `ψ ≔ τ' ∘ τ⁻¹ : G_𝕜/P_𝕜 ⇢ G_𝕜/P'_𝕜` of `thm:CY3`. -/
  psi : P.BirationalMap P'
  [isOverPsi : psi.IsOver (Spec (.of 𝕜))]
  /-- the exceptional divisor of `ψ` on the source (birational to `ℙ¹ × Z'`). -/
  x : P
  /-- the exceptional divisor of `ψ⁻¹` on the target (birational to `ℙ¹ × Z`). -/
  y : P'
  /-- `ψ` is regular away from `Z_𝕜` and its only exceptional divisor is `x` (`(L3)` of an
  L-link; the irreducible exceptional divisor of the blow-up along the connected `Z_𝕜`). -/
  exDiv_psi : exDiv psi = {x}
  /-- `ψ⁻¹` is regular away from `Z'_𝕜` and its only exceptional divisor is `y`. -/
  exDiv_psi_symm : exDiv psi.symm = {y}

attribute [instance] CY3Section.varietyX CY3Section.varietyZ CY3Section.varietyZ'
  CY3Section.isOverIotaX CY3Section.isOverIotaZ CY3Section.isOverIotaZ'
  CY3Section.isOverTau CY3Section.isOverTau' CY3Section.isOverPsi

namespace CY3Section

variable {𝕜 : Type} [Field 𝕜] (S : CY3Section 𝕜)

local instance instVarietyB : Variety 𝕜 S.B := S.varietyB
local instance instVarietyP : Variety 𝕜 S.P := S.varietyP
local instance instVarietyP' : Variety 𝕜 S.P' := S.varietyP'
local instance instIsOverPsi : S.psi.IsOver (Spec (.of 𝕜)) := S.isOverPsi

/-- `ψ` is a birational map between the two five-dimensional `G₂`-Grassmannians, whose only
exceptional divisors are `x` (source) and `y` (target). -/
theorem exDiv_pair : exDiv S.psi = {S.x} ∧ exDiv S.psi.symm = {S.y} :=
  ⟨S.exDiv_psi, S.exDiv_psi_symm⟩

end CY3Section

end

end Work.CY3
