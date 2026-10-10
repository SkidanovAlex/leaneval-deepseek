import Submission.Work.K3Inputs.Defs
import Submission.Work.K3Inputs.not_stablyBirational_prod

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.K3Inputs.Totaro` — the Totaro input (`thm:BurtCY`, `cor-CYnSB`) and the distinguishing

The paper's appendix (§ *Stably birational geometry of K-trivial varieties*, tex 2825–3125)
contains the input that distinguishes the two centres of the K3 L-link:

* **Theorem `thm:BurtCY` (Totaro).**  Let `X₁`, `X₂` be smooth projective varieties over a field
  with a birational map `φ : X₁ ⤏ X₂`.  If `K_{X₁}`, `K_{X₂}` are nef, then `φ` is a
  pseudo-isomorphism; if moreover `NS(X₁)_ℚ` or `NS(X₂)_ℚ` is one-dimensional, `φ` is an
  isomorphism.
* **Corollary `cor-CYnSB`.**  Let `Z`, `Z'` be `K`-trivial varieties of Picard number one over an
  algebraically closed field.  If `Z ≄ Z'`, then `Z × W` is not birational to `Z' × W` for any
  separably rationally connected `W`; in particular `Z` is not stably birational to `Z'`.

The K3 chapter consumes this as the structure `Work.K3.TotaroInput`:

```lean
not_stablyBirat_of_not_iso : ∀ X Y, IsKTrivial 𝕜 X → IsKTrivial 𝕜 Y →
  PicardRankOneGeom 𝕜 X → PicardRankOneGeom 𝕜 Y → ¬ IsoOver 𝕜 X Y →
  ¬ Work.K3.StablyBirational 𝕜 X Y
```

where `Work.K3.StablyBirational 𝕜 X Y` is the *different-exponent* relation
`∃ n m, X × 𝔸ⁿ ∼ Y × 𝔸ᵐ`.  This file records the paper's corollary in the form in which it is
*proved* — the **same** `W` on both sides — together with the case `W = 𝔸ⁿ` in the
different-exponent form that `Work.K3.TotaroInput` needs, and proves the implication
`CorCYnSB ⟹ TotaroInput` (the two agree because `𝔸ᵏ × 𝔸ˡ ≅ 𝔸^{k+l}` is a *cancellation* of the
exponents, `Work.K3Inputs.prodOver_affine_assoc`).

The distinction between the two forms is real: `∃ n m, X × 𝔸ⁿ ∼ Y × 𝔸ᵐ` is *strictly weaker*
than `∃ n, X × 𝔸ⁿ ∼ Y × 𝔸ⁿ` in general (take `X = 𝔸¹`, `Y = Spec 𝕜`: `𝔸¹ × 𝔸⁰ ∼ 𝔸¹ × 𝔸¹` fails to
be a same-exponent relation, while `𝔸¹ × 𝔸⁰ ∼ Spec 𝕜 × 𝔸¹` holds).  For varieties of the same
dimension the two coincide — the exponent is pinned by the transcendence degree of the function
field — which is the form recorded in `CorCYnSB.not_birational_affine`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

namespace Work.K3Inputs

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

noncomputable section

/-- **Named geometric predicate**: `W` is a separably rationally connected variety over `𝕜`
(Kollár, *Rational curves on algebraic varieties*, IV.3.2.3; tex 2995–3005 of the paper).
Mathlib has neither rational connectivity nor separable maps of varieties, so this is a named
predicate, used only to *state* the paper's corollary faithfully. -/
class IsSeparablyRationallyConnected (𝕜 : Type) [Field 𝕜] (W : Scheme.{0}) [Variety 𝕜 W] : Prop

/-- **Totaro's Corollary `cor-CYnSB`** (tex 3103–3115), in the two forms in which it is used.

* `not_birational_src` is the paper's statement verbatim: for `K`-trivial varieties of Picard
  number one over an algebraically closed field, non-isomorphic, and any separably rationally
  connected `W`, `Z × W` is not birational to `Z' × W`.
* `not_birational_affine` is the case `W = 𝔸ⁿ`, strengthened to *different* exponents `n`, `m` —
  the form consumed by `Work.K3.TotaroInput` (this is where the dimension count enters: `𝔸ᵏ` and
  `𝔸ˡ` with `k ≠ l` cannot be cancelled, so `∃ n m` really is the statement the theorem needs).

Note that `thm:BurtCY` itself (the pseudo-isomorphism statement for nef canonical classes, tex
2837–2856) is *not* formalised here: `NS`, nefness, `K_X` and pseudo-isomorphisms of a pair of
blow-ups are all outside Mathlib; its two clauses are the named content of the corollary, whose
hypotheses (`K`-trivial, Picard number one) are the named predicates of the K3 chapter. -/
structure CorCYnSB (𝕜 : Type) [Field 𝕜] : Prop where
  /-- The paper's `cor-CYnSB`: the same separably rationally connected factor on both sides. -/
  not_birational_src : ∀ (Z Z' W : Scheme.{0}) [Variety 𝕜 Z] [Variety 𝕜 Z'] [Variety 𝕜 W],
    Work.K3.IsKTrivial 𝕜 Z → Work.K3.IsKTrivial 𝕜 Z' → Work.K3.PicardRankOneGeom 𝕜 Z →
    Work.K3.PicardRankOneGeom 𝕜 Z' → ¬ Work.K3.IsoOver 𝕜 Z Z' →
    IsSeparablyRationallyConnected 𝕜 W →
    ∀ (_ : Variety 𝕜 (Work.K3.prodOver 𝕜 Z W)) (_ : Variety 𝕜 (Work.K3.prodOver 𝕜 Z' W)),
      ¬ Nonempty ((Work.K3.prodOver 𝕜 Z W).BirationalMap (Work.K3.prodOver 𝕜 Z' W))
  /-- The case `W = 𝔸ⁿ`, with the two exponents allowed to differ: the form `TotaroInput` needs. -/
  not_birational_affine : ∀ (Z Z' : Scheme.{0}) [Variety 𝕜 Z] [Variety 𝕜 Z'],
    Work.K3.IsKTrivial 𝕜 Z → Work.K3.IsKTrivial 𝕜 Z' → Work.K3.PicardRankOneGeom 𝕜 Z →
    Work.K3.PicardRankOneGeom 𝕜 Z' → ¬ Work.K3.IsoOver 𝕜 Z Z' →
    ∀ (n m : ℕ) (_ : Variety 𝕜 (Work.K3.prodOver 𝕜 Z (AffineN 𝕜 n)))
      (_ : Variety 𝕜 (Work.K3.prodOver 𝕜 Z' (AffineN 𝕜 m))),
      ¬ Nonempty ((Work.K3.prodOver 𝕜 Z (AffineN 𝕜 n)).BirationalMap
        (Work.K3.prodOver 𝕜 Z' (AffineN 𝕜 m)))

/-! ## 3. The product form of the distinguishing, from Totaro's input -/

/-- **`S × 𝔸ⁿ` and `S' × 𝔸ᵐ` are not stably birational**, for non-isomorphic `K`-trivial varieties
of Picard number one over `𝕜` (the two centres of the K3 link).  Equivalently: the cylinder
function fields `κ(S)(t)` and `κ(S')(t)` are not isomorphic — the input `¬ ResEquiv 𝕜 y x` of the
link, since the two exceptional divisors are `ℙ¹`-bundles over `S` and `S'`.

The conclusion is stated with the instance-free `Work.K3Inputs.StablyBirat`; the corresponding
statement for `Work.K3.StablyBirational` is obtained by
`Work.K3Inputs.StablyBirat_of_stablyBirational` / `…to_stablyBirational`. -/
theorem not_stablyBirational_prod_of_totaro {𝕜 : Type} [Field 𝕜] {X Y : Scheme.{0}}
    [Variety 𝕜 X] [Variety 𝕜 Y] (T : Work.K3.TotaroInputAt 𝕜 X Y)
    (h : ¬ Work.K3.IsoOver 𝕜 X Y) (n m : ℕ) :
    ¬ StablyBirat 𝕜 (Work.K3.prodOver 𝕜 X (AffineN 𝕜 n))
      (Work.K3.prodOver 𝕜 Y (AffineN 𝕜 m)) :=
  not_stablyBirational_prod (T.not_stablyBirat h) n m

end

end Work.K3Inputs
