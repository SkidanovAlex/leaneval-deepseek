/-
# ZeroFreeTables — XYDefs.lean

Definitions for the formalisation of **[X] Lemma 3.8** (Xylouris, arXiv:0906.2749) in the
order-2 case, i.e. the statement `Work.ZeroFreeTables.XYLemma3_8`:

  `χ₁² = 1`, `ρ₁` a non-real zero of `L(s,χ₁)` of minimal `λ` in the strip `|Im| ≤ 10`
  ⟹ `λ₁ ≥ 0.628 = 628/1000`.

The proof follows Xylouris's §3.6 (his `λ₁`-estimates) in the `ord χ₁ = 2` case, which is a
two-step computation:

* (a) **`λ'`-estimate** (his Table 3, order-2 row): the second zero of `χ₁`
  (other than `ρ₁`, `conj ρ₁`) satisfies `λ' ≥ 1`; this is the "Nebenfall" of his
  `λ'`-section, i.e. the `F`-method `K`-term bounds of HB Lemma 5.2 applied to the
  starting inequality `χ₀(n)(1 + Re{χ₁(n)n^{-iγ'}})(k + Re{χ₁(n)n^{-iγ₁}})² ≥ 0`;
* (b) **the `λ₁`-estimate**: the `F`-method (9.16) inequality of HB §9
  (`0 ≤ 14379K(β,χ₀) + 24480K(β+iγ₁,χ₁) + 14900K(β+2iγ₁,χ₀) + 6000K(β+3iγ₁,χ₁)
  + 1250K(β+4iγ₁,χ₀)`), evaluated at `β = β* = 1 - λ*/log q` with `λ* = 1 ≤ λ'`,
  together with the sup-estimates of Xylouris §2, gives `λ₁ > 0.628`.

Everything here is stated for the concrete test function of HB Lemma 7.2 with
`λ = 4/3` (Xylouris's `γ = 3/4`), as an element of `Work.ZeroFreeTables.TestFn`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.HBProps
import Submission.Work.ZeroFreeTables.testFn7_2

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

open Work.LinnikContract

/-- The test function used for the order-2 `λ₁`-estimate: HB Lemma 7.2's optimal test
function with parameter `λ = 4/3` (equivalently Xylouris's `f` with `γ = 3/4`:
support `[0, 3/2]`, `f 0 = 64/45`, `F 0 = 8/9`, `F(-4/3) = 8/5`). -/
def xyT : TestFn := tf72T (4/3) (by norm_num)

/-- `Re F(x + i t)` for the test function `xyT`. -/
def xyRe (x t : ℝ) : ℝ := (xyT.Fc ((x : ℂ) + (t : ℂ) * Complex.I)).re

/-- The real-axis Laplace transform of `xyT`. -/
def xyF (x : ℝ) : ℝ := xyT.F x

/-- The left hand side of Xylouris's order-2 `λ₁`-inequality (HB (9.16)) at `λ* = 1`:
`14379 F(-1) - 24480 F(λ₁ - 1) + 3810 f(0)`. -/
def xyMain (lam₁ : ℝ) : ℝ :=
  14379 * xyF (-1) - 24480 * xyF (lam₁ - 1) + 3810 * xyT.f 0

/-- The first sup-estimate of Xylouris §2 in the order-2 case (HB (9.16)): the contribution
`14900 Re F(-λ*+it) - 30480 Re F(λ₁-λ*+it)` at `λ* = 1`. -/
def xySup1 (lam₁ t : ℝ) : ℝ := 14900 * xyRe (-1) t - 30480 * xyRe (lam₁ - 1) t

/-- The second sup-estimate of Xylouris §2 in the order-2 case (HB (9.16)):
`1250 Re F(-λ*+it) - 6000 Re F(λ₁-λ*+it)` at `λ* = 1`. -/
def xySup2 (lam₁ t : ℝ) : ℝ := 1250 * xyRe (-1) t - 6000 * xyRe (lam₁ - 1) t

end Work.ZeroFreeTables
