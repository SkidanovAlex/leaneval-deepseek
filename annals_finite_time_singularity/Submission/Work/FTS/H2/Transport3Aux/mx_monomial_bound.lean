/-
Copyright: work module for the Elgindi finite-time singularity project.

# The pointwise monomial bound of the *mixed* (order-five) slots

This file proves `mx_monomial_bound`: for a `𝒲^{4,∞}`-function `f` and an `ℋ⁴`-function `g`,
every product of two mixed `g`-blocks of total order at most `4` (both of which carry at
least one `D_θ`-derivative, hence the `γ`-weight `Wm`) times a mixed `f`-block of total
order at most `4` is bounded pointwise by `30 |f|_{𝒲^{4,∞}} · HkIntegrand α 4 g`.

The two ingredients are

* `abs_mixed_le_WlInf` (in `GoodThetaDefs`): `|D_z^bD_θ^a f| ≤ 30 |f|_{𝒲^{4,∞}}` on the
  quadrant for `a + b ≤ 4`;
* the AM–GM step `|A| · |B| ≤ H` for two quantities whose squares are bounded by `H`,
  applied to the two weighted `g`-blocks `mixed p r g · Wm` and `mixed j i g · Wm`,
  whose squares are single summands of `HkIntegrand α 4 g`; the identity
  `Wm² = w² · sin(2θ)^{-γ}` (from `Whz_Wm_sq`) identifies the product weight.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.H2.Defs
import Submission.Work.FTS.H2.Transport3Aux.Defs
import Submission.Work.FTS.H2.Transport3Aux.GoodThetaDefs
import Submission.Work.FTS.H2.Whz_Wm_sq
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.WProductRule
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.mixed_comm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.Transport3Aux

set_option autoImplicit false

/-- The product of two mixed `g`-blocks, each of total order at most `4` and each carrying
at least one `D_θ`-derivative, together with the product weight `w² · sin(2θ)^{-γ}`, is
bounded by the `ℋ⁴`-integrand: each weighted block has square at most the integrand, and the
product of two quantities with that property is at most the integrand. -/
theorem abs_mixed_pair_mul_weight_le_HkIntegrand (α : ℝ) (hα : 0 < α) (g : ℝ → ℝ → ℝ)
    {p r j i : ℕ} (hr : 1 ≤ r) (hrp : r + p ≤ 4) (hi : 1 ≤ i) (hij : i + j ≤ 4)
    {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.mixed p r g z θ| * |Work.Spaces.mixed j i g z θ|
        * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
  have hA : (Work.Spaces.mixed p r g z θ * Wm α z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
    Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ r p hr hrp
  have hB : (Work.Spaces.mixed j i g z θ * Wm α z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
    Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ i j hi hij
  have h := abs_mul_le_of_sq_le hA hB
  have hWmnn : 0 ≤ Wm α z θ := Wm_nonneg α hθ
  have hsq : Wm α z θ * Wm α z θ
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [← sq]
    exact (Work.FTS.H2.Whz_Wm_sq α hα z θ hθ).2
  calc |Work.Spaces.mixed p r g z θ| * |Work.Spaces.mixed j i g z θ|
        * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      = |Work.Spaces.mixed p r g z θ| * |Work.Spaces.mixed j i g z θ|
        * (Wm α z θ * Wm α z θ) := by rw [hsq]
    _ = |Work.Spaces.mixed p r g z θ * Wm α z θ|
        * |Work.Spaces.mixed j i g z θ * Wm α z θ| := by
        simp only [abs_mul, abs_of_nonneg hWmnn]; ring
    _ ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
        simpa only [abs_mul] using h

theorem mx_monomial_bound (α : ℝ) (f g : ℝ → ℝ → ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hsmf : Work.Spaces.SmoothNbhd f)
    (hwf : Work.Spaces.WlInfMem α 4 f) (hkg : Work.Spaces.HkMem α 4 g)
    (b a p r j i : ℕ) (hab : a + b ≤ 4) (hr : 1 ≤ r) (hrp : r + p ≤ 4)
    (hi : 1 ≤ i) (hij : i + j ≤ 4) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.mixed b a f z θ|
          * (|Work.Spaces.mixed p r g z θ| * |Work.Spaces.mixed j i g z θ|)
          * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        ≤ 30 * Work.Spaces.WlInf α 4 f * Work.Spaces.HkIntegrand α 4 g z θ := by
  intro z hz θ hθ
  have hf : |Work.Spaces.mixed b a f z θ| ≤ 30 * Work.Spaces.WlInf α 4 f :=
    abs_mixed_le_WlInf hα hα1 hsmf hwf hab hz hθ
  have hg : (|Work.Spaces.mixed p r g z θ| * |Work.Spaces.mixed j i g z θ|)
      * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
    abs_mixed_pair_mul_weight_le_HkIntegrand α hα g hr hrp hi hij hθ
  have hWnn : 0 ≤ Work.Spaces.WlInf α 4 f := Work.Spaces.WlInf_nonneg α 4 f hwf
  have hsin : 0 ≤ Real.sin (2 * θ) := Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ
  have hgnn : 0 ≤ (|Work.Spaces.mixed p r g z θ| * |Work.Spaces.mixed j i g z θ|)
      * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) :=
    mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin _))
  have h30W : 0 ≤ 30 * Work.Spaces.WlInf α 4 f := by linarith
  calc |Work.Spaces.mixed b a f z θ|
        * (|Work.Spaces.mixed p r g z θ| * |Work.Spaces.mixed j i g z θ|)
        * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      = |Work.Spaces.mixed b a f z θ|
        * ((|Work.Spaces.mixed p r g z θ| * |Work.Spaces.mixed j i g z θ|)
          * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) := by
        ring
    _ ≤ (30 * Work.Spaces.WlInf α 4 f) * Work.Spaces.HkIntegrand α 4 g z θ :=
        mul_le_mul hf hg hgnn h30W
    _ = 30 * Work.Spaces.WlInf α 4 f * Work.Spaces.HkIntegrand α 4 g z θ := by ring

end Work.FTS.H2.Transport3Aux
