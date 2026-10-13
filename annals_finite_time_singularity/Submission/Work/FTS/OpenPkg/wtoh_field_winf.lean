/-
# `OpenPkg/wtoh_field_winf` — `W^{4,∞}` controls `ℋ⁴` in the open-quadrant class

This is the `wtoh` field of the primed interface `Work.FTS.OpenPkg.N4Norm'` (Elgindi's
`WtoH`, tex 1237), in the open-quadrant class `Work.FTS.EllipticEst.SmoothOpen`:

```
∃ C > 0, ∀ α ∈ (0,1], ∀ f, SmoothOpen f → WlInfMem α 4 ((z+1)³/z²·f) →
  |f|_{ℋ⁴} ≤ C · |((z+1)³/z²)·f|_{𝒲^{4,∞}} .
```

It is `Work.FTS.H2.WtoHQ` with the hypothesis `RegQ α 4 f` (in particular `SmoothQuad f`, i.e.
`C^∞` through `z = 0`) replaced by the *interior* class `SmoothOpen f` and with the `ℋ⁴`-honesty
`HkMem α 4 f` dropped from the hypotheses.

## The proof

The two pointwise estimates of the `WtoH` chain in the open class
(`WtohWin.wtoh_radial_open`, `WtohWin.wtoh_mixed_open`) bound the *plain* `z`-derivatives of `f`
by `Λ = |((z+1)³/z²)f|_{𝒲^{4,∞}}`:

```
hA : |(1+z)·w(z)·z^m·∂_z^m f| ≤ 200000·Λ                            (m ≤ 4)
hB : |(1+z)·w(z)·z^l·∂_z^l(D_θ^i f)| ≤ 200000·Λ·(α+sin 2θ)·sin(2θ)^{α/5}   (1 ≤ i, i+l ≤ 4)
```

and `WtohWin.wtoHQ_pointwise_open` (`WtohWin/Assembly.lean`) turns exactly these two inputs into
`Xn α f ≤ 10¹⁰ Λ`, via the pointwise `ℋ⁴`-integrand bound `WtohWin.hkIntegrand_le_open` and the
`α`-uniform angular/radial integrals `Work.Elliptic.WtoH_Angular` / `Work.Elliptic.WtoH_IntZ`.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.H2.WtoHQ
import Submission.Work.FTS.OpenPkg.WtohWin.Basics
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.OpenPkg.WtohWin.wtoh_radial_open
import Submission.Work.FTS.OpenPkg.WtohWin.wtoh_mixed_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **`W^{4,∞}` controls `ℋ⁴` in the open-quadrant class.**  This is the `wtoh` field of
`Work.FTS.OpenPkg.N4Norm'` (Elgindi's `WtoH`, tex 1237) with the interior class
`Work.FTS.EllipticEst.SmoothOpen` in place of `SmoothQuad` and without the `ℋ⁴`-honesty
hypothesis on `f`. -/
theorem wtoh_field_winf :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ f : Work.FTS.Galerkin.Fn,
      Work.FTS.EllipticEst.SmoothOpen f →
      Work.Spaces.WlInfMem α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ) →
      Work.FTS.Nonlin.Xn α f
        ≤ C * Work.Spaces.WlInf α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ) := by
  refine ⟨10 ^ 10, by norm_num, ?_⟩
  intro α hα hα1 f hsm hmem
  have hΛ : 0 ≤ Work.Spaces.WlInf α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ) := by
    rw [Work.Spaces.WlInf]
    exact add_nonneg (Work.Spaces.wlZSum_nonneg α 4 _ hmem)
      (Work.Spaces.wlThSum_nonneg α 4 _ hmem)
  have hA := WtohWin.wtoh_radial_open (α := α) (f := f) hα hα1 hsm hmem
  have hB := WtohWin.wtoh_mixed_open (α := α) (f := f) hα hα1 hsm hmem
  exact WtohWin.wtoHQ_pointwise_open hα hα1 hΛ hsm hA hB

end Work.FTS.OpenPkg
