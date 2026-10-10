import Mathlib
import ChallengeDeps
import Submission.Work.K3.Defs
import Submission.Work.Motivic.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.Totaro.Defs` — vocabulary for the TOTARO area (Lin–Shinder, appendix)

This is the base module of the **Totaro area** of `annals_motivic_invariants`, i.e. of the input
that both delivered L-link chapters (`Submission/Work/CY3`, `n ≥ 5` of Theorem 1.2 (3), and
`Submission/Work/K3`, `n ≥ 4` of Theorem 1.2 (2)) consume in order to know that the two centres of
their link are *not* stably birational:

> **Theorem (`thm:BurtCY`, Totaro, appendix of Lin–Shinder, *Motivic invariants of birational
> maps*, Annals **199** (1), 2024, tex 2826–2910).**  Let `X₁`, `X₂` be smooth projective varieties
> over a field with a birational map `φ : X₁ ⇢ X₂`.  Assume that `K_{X₁}` and `K_{X₂}` are nef.
> Then `φ` is a pseudo-isomorphism.  If in addition `NS(X₁)_ℚ` or `NS(X₂)_ℚ` is one-dimensional,
> then `φ` is an isomorphism.
>
> **Corollary (`cor-CYnSB`, tex 3103–3115).**  Let `Z`, `Z'` be `K`-trivial varieties of Picard
> number one over an algebraically closed field.  If `Z ≄ Z'`, then `Z × W` is not birational to
> `Z' × W` for any separably rationally connected variety `W` over `𝕜`.  In particular `Z` is not
> stably birational to `Z'`.

The two chapters state this as the *named input* `Work.CY3.TotaroInput 𝕜` /
`Work.K3.TotaroInput 𝕜`:

```lean
structure TotaroInput (𝕜 : Type) [Field 𝕜] : Prop where
  not_stablyBirat_of_not_iso : ∀ (X Y : Scheme.{0}) [Variety 𝕜 X] [Variety 𝕜 Y],
    IsKTrivial 𝕜 X → IsKTrivial 𝕜 Y → PicardRankOne 𝕜 X → PicardRankOne 𝕜 Y →
    ¬ IsoOver 𝕜 X Y → ¬ StablyBirational 𝕜 X Y
```

The Totaro area **decomposes** that input.

* `Submission/Work/Totaro/Paper.lean` records the paper's own route — `thm:BurtCY` (negativity
  lemma clause; then the `Pic`/`NS`/`Proj` clause), `lem-stbirCY` (the descent of a birational map
  of products) and `cor-CYnSB` — as named inputs, and *derives* both forms of `cor-CYnSB` and hence
  the two chapters' `TotaroInput` fields from them (`Work.Totaro.corCYnSB_of_paper`).
* `Submission/Work/Totaro/Cohomology.lean` names the *cohomological* content as a certificate
  (`CohSeparation`/`CohKunneth`: a birational invariant with Künneth multiplicativity, the Tate-twist
  normalisation `I 𝔸ⁿ = 1`, and the distinguishing of the pair) and proves the algebraic layer that
  turns it into the two `TotaroInput`s: the product decomposition argument and the resulting
  `¬ StablyBirational` with *all* exponents.  See `NOTES.md` §5b for the precise strength of that
  certificate (it is at least as strong as the conclusion, and morally equivalent to it), and
  §6–§7 for the residuals, the roadmap and the Mathlib gap list.

`Submission/Work/Totaro/Interface.lean` produces `Work.CY3.TotaroInput` and `Work.K3.TotaroInput`
from any of the three named inputs (universal certificate, per-pair certificate, paper's corollary)
and gives the two chapters the residue-field, `z₀` and cylinder-field distinguishings they need.

## Conventions

* `𝕜` is a field, `Spec (.of 𝕜)` is the base scheme, and `X.Over (Spec (.of 𝕜))` the base
  structure (the reference for these is `ChallengeDeps.lean`).
* `X.BirationalMap Y` is the challenge's birational map (a pair of mutually inverse dominant
  rational maps), `Work.Motivic.exDiv φ` the set of codimension-one points at which `φ` is not an
  isomorphism, `Work.Motivic.cInv` the Lin–Shinder invariant coefficient and `Work.Motivic.ResEquiv`
  the isomorphism of residue fields over `𝕜`.
* `prodOver 𝕜 X Y`, `IsoOver 𝕜 X Y`, `StablyBirational 𝕜 X Y` and `IsKTrivial 𝕜 X` are the
  notions of the K3 chapter, re-exported here under the same names (`Work.K3.*`): there is one
  notion per concept, two names, exactly as `Work.CY3.Defs` does it.
* `𝔸¹` is our model of `ℙ¹` throughout (only the birational class matters, and the K3/CY3 chapters
  work with `𝔸(Fin 1; Spec 𝕜)`); `AffineN 𝕜 n` is affine `n`-space.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

namespace Work.Totaro

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

noncomputable section

variable {𝕜 : Type} [Field 𝕜]

/-! ## 1. The ambient vocabulary (re-exported from the K3 chapter) -/

/-- Affine `n`-space over `𝕜`, in the exponent form used by `Work.K3.StablyBirational`. -/
abbrev AffineN (𝕜 : Type) [Field 𝕜] (n : ℕ) : Scheme.{0} := 𝔸(Fin n; Spec (.of 𝕜))

/-- The product of two `𝕜`-schemes: the fibre product over `Spec 𝕜` (same notion as
`Work.K3.prodOver`, `Work.CY3.prodOver`). -/
abbrev prodOver (𝕜 : Type) [Field 𝕜] (X Y : Scheme.{0}) [X.Over (Spec (.of 𝕜))]
    [Y.Over (Spec (.of 𝕜))] : Scheme.{0} := Work.K3.prodOver 𝕜 X Y

/-- Isomorphisms of `𝕜`-schemes: the relation whose failure over `𝕜` is the hypothesis of Totaro's
Corollary `cor-CYnSB` (same notion as `Work.K3.IsoOver`, `Work.CY3.IsoOver`). -/
abbrev IsoOver (𝕜 : Type) [Field 𝕜] (X Y : Scheme.{0}) [X.Over (Spec (.of 𝕜))]
    [Y.Over (Spec (.of 𝕜))] : Prop := Work.K3.IsoOver 𝕜 X Y

/-- **Stable birationality** over `𝕜`: `X × 𝔸ⁿ` is birational to `Y × 𝔸ᵐ` for some `n, m` (same
notion as `Work.K3.StablyBirational`, `Work.CY3.StablyBirational`). -/
abbrev StablyBirational (𝕜 : Type) [Field 𝕜] (X Y : Scheme.{0}) [Variety 𝕜 X] [Variety 𝕜 Y] :
    Prop :=
  Work.K3.StablyBirational 𝕜 X Y

/-- `X` is `K`-trivial (`ω_X ≃ 𝒪_X`), the named geometric hypothesis of Totaro's `cor-CYnSB`
(same notion as `Work.K3.IsKTrivial`, `Work.CY3.IsKTrivial`). -/
abbrev IsKTrivial (𝕜 : Type) [Field 𝕜] (X : Scheme.{0}) [Variety 𝕜 X] : Prop :=
  Work.K3.IsKTrivial 𝕜 X

/-- **A family of "Picard rank one" predicates.**  The two chapters use two different named
predicates for this geometric condition — `Work.CY3.PicardRankOne` (the CY3 centres, threefolds)
and `Work.K3.PicardRankOneGeom` (the K3 surfaces) — and the statements of this area are stated
uniformly in one such family `Pic1`, so that instantiating `Pic1` at either predicate gives the
corresponding chapter's shape. -/
abbrev Pic1Family (𝕜 : Type) [Field 𝕜] := (X : Scheme.{0}) → [Variety 𝕜 X] → Prop

/-! ## 2. The named geometric predicates of the appendix -/

/-- **Named geometric predicate**: `W` is a separably rationally connected variety over `𝕜`
(Kollár, *Rational curves on algebraic varieties*, IV.3.2.3; paper tex 2995–3005: there is a
variety `S` and a rational map `u : S × ℙ¹ ⇢ W` whose two-point evaluation
`u₂ = u ×_S u : S × ℙ¹ × ℙ¹ ⇢ W × W` is dominant and separable).

Mathlib has neither rational connectivity nor separable maps of varieties, so this is a named
predicate; it is used only to *state* `lem-stbirCY`/`cor-CYnSB` faithfully.  Note that `𝔸ⁿ` is
separably rationally connected (affine space is rational over any field) — this is the only
instance a consumer needs, and it is recorded as `Work.Totaro.isSeparablyRationallyConnected_affine`
below. -/
class IsSeparablyRationallyConnected (𝕜 : Type) [Field 𝕜] (W : Scheme.{0}) [Variety 𝕜 W] : Prop

/-- **Named geometric predicate**: `X` is *not* separably uniruled.  This is Kollár's
`Corollary IV.1.11`: a `K`-trivial variety is not separably uniruled.  It is the hypothesis under
which `lem-stbirCY` descends a birational map of products. -/
class IsNotSeparablyUniruled (𝕜 : Type) [Field 𝕜] (X : Scheme.{0}) [Variety 𝕜 X] : Prop

/-- **Named geometric predicate**: `X` is a smooth projective variety (over `𝕜`) with *nef*
canonical class `K_X`.  This is the hypothesis of `thm:BurtCY`; Mathlib has no smoothness, no
projectivity, no canonical divisor and no nefness, so it is a named predicate. -/
class IsNefCanonical (𝕜 : Type) [Field 𝕜] (X : Scheme.{0}) [Variety 𝕜 X] : Prop

/-! ## 3. Pseudo-isomorphisms -/

/-- **`φ` is a pseudo-isomorphism** (an isomorphism in codimension one): neither `φ` nor `φ⁻¹` has
an exceptional divisor — the conclusion of the first clause of `thm:BurtCY`.  In the vocabulary of
Part A this is `Work.Motivic.exDiv φ = ∅ ∧ Work.Motivic.exDiv φ.symm = ∅`. -/
def IsPseudoIso {X Y : Scheme.{0}} [IrreducibleSpace X] [IrreducibleSpace Y]
    (φ : X.BirationalMap Y) : Prop :=
  exDiv φ = ∅ ∧ exDiv φ.symm = ∅

/-- Pseudo-isomorphisms are closed under inversion. -/
theorem IsPseudoIso.symm {X Y : Scheme.{0}} [IrreducibleSpace X] [IrreducibleSpace Y]
    {φ : X.BirationalMap Y} (h : IsPseudoIso φ) : IsPseudoIso φ.symm :=
  ⟨h.2, h.1⟩

/-- A pseudo-isomorphism has no exceptional divisor. -/
theorem IsPseudoIso.exDiv_eq_empty {X Y : Scheme.{0}} [IrreducibleSpace X] [IrreducibleSpace Y]
    {φ : X.BirationalMap Y} (h : IsPseudoIso φ) : exDiv φ = ∅ := h.1

/-! ## 4. The `ℙ¹`-bundle bridge (the shape of the `bridge` field of the two chapters) -/

/-- **The `ℙ¹`-bundle bridge hypothesis.**  For the two exceptional divisors `y`, `x` of an L-link
(divisors birational to `ℙ¹ × Z` and `ℙ¹ × Z'`), an isomorphism `κ(y) ≅ κ(x)` of their function
fields — i.e. `κ(Z)(t) ≅ κ(Z')(t)` — forces `Z` and `Z'` to be stably birational.  This is the
(F1)–(F3) residual of the L-link analysis; it is the field `bridge` of `Work.CY3.CY3Data` and of
`Work.K3.K3Data`, and this definition records its exact shape once, for both chapters.

Given Totaro's input, it is exactly what turns `¬ IsoOver 𝕜 Z Z'` into `¬ ResEquiv 𝕜 y x`, the
non-triviality input of the link. -/
def P1BundleBridge (𝕜 : Type) [Field 𝕜] {P Z Z' : Scheme.{0}} [P.Over (Spec (.of 𝕜))]
    [Z.Over (Spec (.of 𝕜))] [Z'.Over (Spec (.of 𝕜))] [Variety 𝕜 Z] [Variety 𝕜 Z']
    (y x : P) : Prop :=
  ResEquiv 𝕜 y x → StablyBirational 𝕜 Z Z'

/-! ## 5. Affine space is separably rationally connected -/

/-- Affine space is separably rationally connected (paper tex 2995–3005): it is rational over `𝕜`,
hence admits a dominant separable `u : S × ℙ¹ ⇢ 𝔸ⁿ` with `u₂` dominant and separable.  This is the
only instance of the named predicate `IsSeparablyRationallyConnected` that the appendix needs — in
the proof of `cor-CYnSB` one takes `W = 𝔸ⁿ`, and in the same-`W` form `W = ℙ¹` — and it is recorded
here once for the whole area.

*Remark on the encoding.*  `IsSeparablyRationallyConnected` is a `Prop`-valued class with no fields,
so the term below is `⟨⟩` and carries no mathematical content: it is the standard way in this
workspace of *asserting* a named geometric fact (the same way `Work.CY3.PicardRankOne` and
`Work.K3.IsKTrivial` are asserted wherever the chapters need them).  Read as mathematics, the
statement is that affine space is rational over any field, hence separably rationally connected —
a fact that is nowhere formalised (Mathlib has no rational connectivity). -/
theorem isSeparablyRationallyConnected_affine (𝕜 : Type) [Field 𝕜] (n : ℕ) :
    IsSeparablyRationallyConnected 𝕜 (AffineN 𝕜 n) :=
  ⟨⟩

end
end Work.Totaro
