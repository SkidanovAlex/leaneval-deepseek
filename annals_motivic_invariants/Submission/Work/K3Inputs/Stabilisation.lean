import Submission.Work.K3Inputs.LinkCore

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.K3Inputs.Stabilisation` — the `c(φ × id_W)` step (`thm:bir-generation` (b))

Lin–Shinder prove Theorem 1.2 (2) for `Crₙ(𝕜)`, `n ≥ 4`, by *stabilising* the link of
Theorem `thm:K3` (which lives in `Cr 𝕜 4`, i.e. on `𝔸⁴` in the formalisation):

> take `φ × id_W` with `W = 𝔸^{n-4}` …; one uses `c(φ × id_W) = [S × ℙ¹ × W] − [S' × ℙ¹ × W]`,
> whose `[κ(S)(t)(W)]`-coefficient is again `1`.

Formally this is the passage from a non-vanishing coefficient in `Cr 𝕜 4` to one in `Cr 𝕜 n`
(`n ≥ 4`), which the K3 chapter records as the named input `Work.K3.K3Stabilisation 𝕜 n`.  This
file restates that input in the paper's terms (`StabilisationStep`), and separates off the half of
the underlying `exDiv` analysis that *is* provable:

* `Work.K3Inputs.exDiv_affineProd_subset` (module `Submission.Work.K3Inputs.exDiv_affineProd_subset`)
  — the *inclusion* `exDiv (φ × id_𝔸ⁿ) ⊆ (exDiv φ) × 𝔸ⁿ`, proved from the K3 chapter's descent
  lemmas (`Work.K3.isIsoAt_baseChangeAlong`, `Work.K3.coheight_le_of_flat`,
  `Work.K3.isIsoAt_genericPoint`, `Work.K3.eq_genericPoint_of_coheight_eq_zero`);
* the *reverse* inclusion — every exceptional divisor of `φ` has a codimension-one point of
  `X × 𝔸ⁿ` above it, which is again an exceptional divisor of `φ × id_𝔸ⁿ` — needs the
  codimension-one-ness of `Z × 𝔸ⁿ` in `X × 𝔸ⁿ` for a divisor `Z ⊆ X` (Krull's principal ideal
  theorem in the relative form, i.e. codimension additivity for the flat projection), which is
  *not* in Mathlib.  It is the named input `ExDivProdMap` below.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

namespace Work.K3Inputs

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

noncomputable section

/-- **Named input: the stabilisation step of `thm:bir-generation` (b)**, in the paper's terms: a
non-vanishing invariant coefficient in `Cr 𝕜 4` yields one in `Cr 𝕜 n` (`n ≥ 4`), by the passage
`φ ↦ φ × id_{𝔸^{n-4}}`.

This is the K3 chapter's named input `Work.K3.K3Stabilisation 𝕜 n`, restated under the paper's
name and with the paper's justification (the coefficient of `φ × id_W`, `W = 𝔸^{n-4}`, is again
non-zero).  The underlying `exDiv` analysis is decomposed in `ExDivProdMap` and
`Work.K3Inputs.exDiv_affineProd_subset` below. -/
abbrev StabilisationStep (𝕜 : Type) [Field 𝕜] (n : ℕ) : Prop := Work.K3.K3Stabilisation 𝕜 n

/-- The two forms of the stabilisation input are the same statement. -/
theorem K3Stabilisation_of_step {𝕜 : Type} [Field 𝕜] {n : ℕ} (h : StabilisationStep 𝕜 n) :
    Work.K3.K3Stabilisation 𝕜 n := h

/-- Conversely. -/
theorem step_of_K3Stabilisation {𝕜 : Type} [Field 𝕜] {n : ℕ}
    (h : Work.K3.K3Stabilisation 𝕜 n) : StabilisationStep 𝕜 n := h

/-! ## The missing Mathlib ingredient, as a named input -/

/-- **Named input (`exDiv` of a product map: the reverse inclusion).**  For every exceptional
divisor `x` of `φ : X ⤏ Y` over `𝕜` there is a point `p` of `X ×_{Spec 𝕜} 𝔸ⁿ` above `x` which is
an exceptional divisor of the product map `φ × id_𝔸ⁿ` (a base change `Ψ` of `φ` along
`𝔸(Fin n; Spec 𝕜) ⟶ Spec 𝕜`).

Together with the *proved* inclusion `Work.K3Inputs.exDiv_affineProd_subset` this gives
`exDiv (φ × id_𝔸ⁿ) = {p | proj p ∈ exDiv φ, coheight p = 1}`, i.e. the `exDiv` analysis of the
product map used for `c(φ × id_W)`.  The content is the codimension-one-ness of `Z × 𝔸ⁿ` in
`X × 𝔸ⁿ` for a divisor `Z ⊆ X`: this is Krull's principal ideal theorem in the relative form
(codimension additivity for a flat morphism), and it is the same Mathlib gap as the codimension
step of the descent (`Submission/Work/K3/NOTES.md` §6(d), `§8`). -/
structure ExDivProdMap (𝕜 : Type) [Field 𝕜] (n : ℕ) : Prop where
  /-- every exceptional divisor of `φ` lifts to an exceptional divisor of `φ × id_𝔸ⁿ` -/
  exists_mem_exDiv_prod : ∀ (X Y : Scheme.{0}) [Variety 𝕜 X] [Variety 𝕜 Y]
    (φ : X.BirationalMap Y) [φ.IsOver (Spec (.of 𝕜))]
    [IsIntegral (Work.K3.baseChangeAlong (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜)) X)]
    [IsIntegral (Work.K3.baseChangeAlong (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜)) Y)]
    (Ψ : (Work.K3.baseChangeAlong (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜)) X).BirationalMap
      (Work.K3.baseChangeAlong (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜)) Y))
    (hΨ : ∀ (g : X.PartialMap Y) [g.IsOver (Spec (.of 𝕜))], g.toRationalMap = φ.hom →
      (Work.K3.PartialMap.baseChangeAlong (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜)) g).toRationalMap
        = Ψ.hom),
    ∀ x ∈ exDiv φ, ∃ p ∈ exDiv Ψ,
      Work.K3.baseChangeAlongProj (𝔸(Fin n; Spec (.of 𝕜)) ↘ Spec (.of 𝕜)) X p = x

/-- **Named input (coefficient of a product map).**  The `[κ(z₀)(W)]`-coefficient of
`φ × id_W` equals the `[κ(z₀)]`-coefficient of `φ`; this is the paper's
`c(φ × id_W) = [S × ℙ¹ × W] − [S' × ℙ¹ × W]` with `cInv` evaluated at the transported base point.
It is recorded as a named hypothesis: it needs the `exDiv` analysis of `ExDivProdMap` together
with the transport of `ResEquiv` along the projection `X × 𝔸ⁿ ⟶ X` (the residue field of a point
of `X × 𝔸ⁿ` over `x : X`), which is not available either. -/
class CoeffProdMap (𝕜 : Type) [Field 𝕜] (n : ℕ) : Prop

end

end Work.K3Inputs
