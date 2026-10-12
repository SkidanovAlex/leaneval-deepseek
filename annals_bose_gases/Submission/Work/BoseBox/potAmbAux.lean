import ChallengeDeps
import Submission.Work.BoseBox.CNodeDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBox.potAmbAux` — the vocabulary of the potential half of the `C` node

This module fixes the two spellings of the bracket appearing in `potAmb` that the
`C2` node (`Work.BoseBox.potAmb_integral`) needs:

* `potBracket` — the bracket *verbatim* as it occurs in the definition of
  `Work.BoseBox.potAmb`, i.e. with the one-body fibre integrals
  `∫ y in bigBox ℓ u, w_loc u (x i) y` taken over the **sliding box** `Λ(u)`;
* `potBr` / `potBracketG` — the same bracket with the fibre integrals taken over
  **all of `ℝ³`** (and with the two kernels left as free arguments `vK`, `gK`).

The two agree because the `χ_u(y)` factor of the localised kernel vanishes off
`Λ(u)` (that is `potBracket_eq_G`, proved in `Work.BoseBox.potAmb_support`), and
this is the form in which the integrability (Fubini) statements are stated, since
then the `(u,x)`-integrand is a *plain* parameter integral rather than one over a
`u`-dependent domain.

`potAmb_eq_integral` records that `potAmb` *is* the `x`-integral of `(Ψ x)^2`
times `potBracket` (definitional).
-/

noncomputable section

open MeasureTheory Metric
open scoped ContDiff Topology Real BigOperators

namespace Work.BoseBox


open _root_.BoseGases
open Submission.BoseGases
open Work.UBB

set_option autoImplicit false
set_option linter.unusedVariables false

/-- A pointwise bound for the bump `χ`: `|χ z| ≤ chiSup` (so also `|χ_u(z)| ≤ chiSup`). -/
noncomputable def chiSup : ℝ := (Real.sqrt chiNormSq)⁻¹

/-- `|χ z| ≤ chiSup` pointwise. -/
lemma abs_chi_le_chiSup (z : ℝ³) : |chi z| ≤ chiSup := abs_chi_le z

/-- The `L¹`-mass `∫ |g₀|` of the renormalised potential. -/
noncomputable def g0mass (v : ℝ³ → ℝ) (h : ScatSol v) : ℝ := ∫ y : ℝ³, |g0 v h y|

/-- The one-body localised fibre integral `∫_y w_{1,u}(a,y) dy` over **all** of `ℝ³`,
for the kernel numerator `gK` (i.e. `gK = g₀` at the instantiation used in `potAmb`). -/
noncomputable def potBr (ℓ : ℝ) (gK : ℝ³ → ℝ) (u a : ℝ³) : ℝ :=
  ∫ y : ℝ³, wLoc ℓ gK u a y

/-- The bracket of `potAmb` written with the fibre integrals over all of `ℝ³` and with
the two kernel numerators (`vK` for the pair term, `gK` for the one-body term) as
free arguments. -/
noncomputable def potBracketG (N : ℕ) (ℓ μ : ℝ) (vK gK : ℝ³ → ℝ) (u : ℝ³)
    (x : X N) : ℝ :=
  - μ * (∑ i : Fin N, potBr ℓ gK u (x i))
    + (1 / 2) * (∑ p ∈ pairSet N, wLoc ℓ vK u (x p.1) (x p.2))

/-- The bracket of `potAmb` verbatim: the fibre integrals run over the sliding box
`Λ(u) = bigBox ℓ u`. -/
noncomputable def potBracket (N : ℕ) (ℓ μ : ℝ) (v : ℝ³ → ℝ) (h : ScatSol v)
    (u : ℝ³) (x : X N) : ℝ :=
  - μ * (∑ i : Fin N, ∫ y in bigBox ℓ u, wLoc ℓ (g0 v h) u (x i) y)
    + (1 / 2) * (∑ p ∈ pairSet N, wLoc ℓ v u (x p.1) (x p.2))

/-- `potAmb` unfolds to the `x`-integral of `(Ψ x)^2` against the bracket `potBracket`. -/
lemma potAmb_eq_integral (N : ℕ) (L ℓ μ : ℝ) (v : ℝ³ → ℝ) (h : ScatSol v)
    (u : ℝ³) (Ψ : X N → ℝ) :
    potAmb N L ℓ μ v h u Ψ = ∫ x in box N L, (Ψ x) ^ 2 * potBracket N ℓ μ v h u x :=
  rfl

/-- The pair part of the bracket, isolated: `(1/2)Σ_{p ∈ pairSet N} w_u(x_{p.1},x_{p.2})`. -/
noncomputable def potPairPart (N : ℕ) (ℓ : ℝ) (vK : ℝ³ → ℝ) (u : ℝ³) (x : X N) : ℝ :=
  (1 / 2) * (∑ p ∈ pairSet N, wLoc ℓ vK u (x p.1) (x p.2))

/-- The one-body part of the bracket, isolated: `-μ Σ_i ∫_y w_{1,u}(x_i,y) dy`. -/
noncomputable def potOnePart (N : ℕ) (ℓ μ : ℝ) (gK : ℝ³ → ℝ) (u : ℝ³) (x : X N) : ℝ :=
  - μ * (∑ i : Fin N, potBr ℓ gK u (x i))

lemma potBracketG_eq_parts (N : ℕ) (ℓ μ : ℝ) (vK gK : ℝ³ → ℝ) (u : ℝ³) (x : X N) :
    potBracketG N ℓ μ vK gK u x
      = potOnePart N ℓ μ gK u x + potPairPart N ℓ vK u x :=
  rfl

end Work.BoseBox
