/-
Copyright: work module for the Elgindi finite-time singularity project.

# `exists_bslSol_fts` — the corrected existence statement for (PolarBSL)

The predecessor `Work.Elliptic.Estimates.exists_bslSol`

```
∀ α F, 0 < α → SmoothNbhd F → (∀ θ ∈ Iθ, F z θ → 0 as z → ∞) →
  ∃ Ψ, SmoothNbhd Ψ ∧ IsBslSol α F Ψ
```

is **FALSE**, and it is the only one of the nine `Estimates.lean` targets that is (see
`NOTES.md` §2.2).  The obstruction is the forced Euler ODE for the angular moment
`F_*(g)(z) = ∫₀^{π/2} g(z,θ)·sinθcos²θ dθ`:

```
α² z² Ψ_*'' + α (5+α) z Ψ_*' = -F_*(F)     (Work.Elliptic.PsiStar_ode)
```

whose solutions differ from a particular solution by `c₁ + c₂ z^{-5/α}`.  For
`F(z,θ) = sin(2θ)/log(2+z)` one has `F_*(F)(z) = (4/15)/log(2+z)`, and every solution has
`F_*(Ψ)(z) ≍ -c·log log z → -∞`, so no decaying solution exists at all; `F` is also not in
`L²`.  (`SmoothNbhd F` and the pointwise decay of `F` both hold, so neither hypothesis helps.)

## The corrected statement

Two changes are needed, and they are exactly the two the audit recorded:

1. **the paper's own source class**: `OrthCond F` (tex 728), i.e. `F_*(F) ≡ 0`.  This makes the
   moment equation homogeneous, so `F_*(Ψ) = c₁ + c₂ z^{-5/α}` and decay forces `F_*(Ψ) ≡ 0`.
   This is the hypothesis under which the paper states and proves `prop:L2`/`prop:H2`/`prop:Hk`;
2. **the paper'"'"'s own range and integrability**: `0 < α ≤ 1` and `F ∈ L²` on the quadrant (tex 735
   assumes both; keeping only pointwise decay would be strictly broader than the source);
3. **the regularity the elliptic theory delivers**: the solution is `C^∞` on the *open* quadrant
   (which is what `SmoothOpen` — the class of `TT.EllWeakPos` — and what the estimates use),
   **not** `SmoothNbhd` (smooth in a neighbourhood of the closed quadrant).  The modewise radial
   solutions behave like `z^{s}`, `s = (-5+√(25+4λ))/(2α)`, which is generically non-integral, so
   the higher-order regularity at `z = 0` is a genuinely extra requirement, not a consequence of
   the PDE.

`bslSolExistenceFts` below is that corrected statement, as a named `Prop` (no proof obligation
is created here, so the module is `sorry`-free and axiom-clean).  It is the name the lead should
point at in place of the false `exists_bslSol`.
-/
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false

/-- **The corrected `exists_bslSol`**: in the paper's own source class (`OrthCond F`: the
angular moment of `F` vanishes, which is what makes the moment ODE homogeneous and the
`z → ∞` decay attainable), and with the source decaying pointwise at infinity, there is a
solution `Ψ` of `bslOp α Ψ = F` with the Dirichlet data and the decay, of the regularity the
elliptic theory actually delivers — `C^∞` on the **open** quadrant (`SmoothOpen`), *not*
`SmoothNbhd`.

The predecessor's extra `SmoothNbhd Ψ` is false in general (see the module docstring: the
modewise radial solutions are `z^{s}` with generically non-integral `s`), and dropping it is
what makes the statement the one the rest of the chapter consumes. -/
def bslSolExistenceFts : Prop :=
  ∀ (α : ℝ) (F : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.Elliptic.OrthCond F →
    Work.FTS.EllipticEst.SmoothOpen F →
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (F p.1 p.2) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) →
    (∀ θ ∈ Work.Spaces.Iθ, Filter.Tendsto (fun z => F z θ) Filter.atTop (nhds 0)) →
    ∃ Ψ : ℝ → ℝ → ℝ,
      Work.FTS.EllipticEst.SmoothOpen Ψ ∧ Work.Elliptic.IsBslSol α F Ψ

/- The `SmoothInt`-slice variant of the statement above was carried here as the `Prop`-valued
`def bslSolExistenceSmoothIntFts` until 2026-10-08.  It was **removed**: `Work.Spaces.SmoothInt`
demands *analyticity* (`ContDiffOn ℝ ⊤`, and in this Mathlib `⊤ : ℕ∞ω` is the analytic order `ω`,
not `C^∞`) of `Ψ` on a neighbourhood of `z = 0`, which the modal solution cannot have (its radial
amplitudes behave like `z^{2m/α}` with generically non-integral exponent); the statement is
therefore not true for arbitrary `F`, and no consumer used it.  The existence statement that *is*
consumed, `bslSolExistenceFts`, is proved in `Final/bslSolExistence_fts.lean`. -/

end Work.FTS.EllipticEst
