import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.SupPort.classC_sup_le
import Submission.Work.FTS_RegExport.RXA1w.abs_mixed_le_HkNorm_C4_w_proved

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXR1

/-!
# `mixed_abs_le_weighted` — the *weighted* interior `L^∞`–`ℋ⁴` trade-off

For every `0 < α ≤ 1` there is a constant `C = C(α) ≥ 0` such that every datum `f` which is
`C^∞` on the open quadrant `Q0 = (0,∞) × (0,π/2)`, honestly in the weighted space `ℋ⁴`
(`Work.Spaces.HkMem α 4 f`) and satisfying the boundary traces `BdryTraces α 4 f`, obeys the
*weighted* pointwise bound

  `|D_z^b D_θ^a f (z,θ)| ≤ C · z^{3/2}/(1+z)² · |f|_{ℋ⁴}`   for `a + b ≤ 2`, `z > 0`, `0 < θ < π/2`.

This is the `z^{3/2}/(1+z)²`-weighted refinement of the interior trade-off
`Work.FTS.StrongEps.SupPort.mixed_abs_le_of_smoothOpen` (`|D_z^bD_θ^a f| ≤ 10/√(γ-1)·|f|_{ℋ⁴}`,
a *constant* bound); the weight encodes the sharp radial behaviour of an `ℋ⁴` datum: it vanishes
like `z^{3/2}` as `z → 0⁺` (the borderline rate forced by the `(1+z)²/z²` weight in the `D_z`-slots
of the norm) and decays like `z^{-1/2}` as `z → ∞`.  The constant bound alone does **not** imply
the weighted one, because `z^{3/2}/(1+z)²` is unbounded below.

The mathematical content is the chain (weighted radial Agmon inequality `agmonZ_weight` applied to
the angular slice, the angular Hardy inequality at fixed `z`, and Tonelli for the `ℋ⁴`-integrand),
which is carried out in `Submission/Work/FTS_RegExport/RXA1w/` for the *weaker* regularity
hypothesis `ContDiffOn ℝ 4 (uncurry f) Q0`:

* `Work.FTS_RegExport.RXA1w.agmonZ_weight` — `(v z)² w(z)² z ≤ 4∫(v w)² + ∫(x v' w)²`,
* `Work.FTS_RegExport.RXA1w.mixed_slice_pointwise_le` — the a.e. slice bound with constant `5`,
* `Work.FTS_RegExport.RXA1w.abs_mixed_le_HkNorm_C4_w_proved` — the `C⁴` form of the present
  statement, with the explicit constant `√(500/(γ-1))`.

Since `SmoothOpen f` (all finite orders) implies the `C⁴` hypothesis on `Q0`
(`Work.FTS.EllipticEst.smoothOpen_iff_forall`), the statement below follows from the `C⁴` form
with the same constant.  `Work.FTS.Galerkin.Fn` is an `abbrev` for `ℝ → ℝ → ℝ`, so the two
statements live on the same type.
-/

/-- **The weighted interior `L^∞`–`ℋ⁴` trade-off.**  For `0 < α ≤ 1` there is `C ≥ 0` such that
every `C^∞`-on-the-open-quadrant, `ℋ⁴`-honest datum `f` with the boundary traces `BdryTraces α 4 f`
satisfies `|D_z^b D_θ^a f (z,θ)| ≤ C · z^{3/2}/(1+z)² · |f|_{ℋ⁴}` for all `a + b ≤ 2` and all
interior points `(z,θ) ∈ Q0`. -/
theorem mixed_abs_le_weighted {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℝ → ℝ → ℝ,
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      Work.FTS.Nonlin.BdryTraces α 4 f →
      ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed b a f z θ| ≤
          C * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) * Work.Spaces.HkNorm α 4 f := by
  -- the `C⁴`-form of the statement, with the explicit constant `√(500/(γ-1))`
  obtain ⟨C, hC0, hC⟩ := Work.FTS_RegExport.RXA1w.abs_mixed_le_HkNorm_C4_w_proved hα hα1
  refine ⟨C, hC0, fun f hF hmem hbd b a hab z θ hz hθ0 hθ1 => ?_⟩
  -- `SmoothOpen f` gives `ContDiffOn ℝ 4 (uncurry f) Q0`, the regularity of the `C⁴`-form
  exact hC f ((Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hF 4) hmem hbd b a hab z θ
    hz hθ0 hθ1

end Work.FTS_RegExport.RXR1
