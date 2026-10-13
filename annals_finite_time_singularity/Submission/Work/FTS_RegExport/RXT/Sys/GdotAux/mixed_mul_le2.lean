import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.FinCalc
import Submission.Work.FTS_RegExport.RXT.Sys.GdotAux.mixed_mul_fin_local

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.Sys.GdotAux

/-- **The Leibniz rule for `D_z^j D_θ^i` on the open quadrant, at total order `j + i ≤ 2`.**

`D_z f = z ∂_z f` and `D_θ f = sin(2θ) ∂_θ f` are derivations for the pointwise product, so,
writing `Work.Spaces.mixed j i f = D_z^j D_θ^i f`, the iterated Leibniz rule

`D_z^j D_θ^i (f·h) = ∑_{a ≤ i} ∑_{b ≤ j} C(i,a) C(j,b) (D_z^b D_θ^a f)(D_z^{j-b} D_θ^{i-a} h)`

holds as soon as `f` and `h` are `C^{j+i}` at the point.  This is the `C²` instance needed by
the finite-order calculus of the `g`-system: it is the low-order specialisation of the general
finite-order statement `mixedMulFinLocal` (in
`...Sys.GdotAux.mixed_mul_fin_local`), which covers two functions of class `C^{j+i}` on an
arbitrary *open* set `V`.  (Indeed neither `Work.Spaces.mixed_mul_eq` — stated for
analytic/`C^∞` functions on the strip — nor any of the `SmoothNbhd`/`SmoothOpen` Leibniz rules
applies to a merely `C²` datum.) -/
theorem mixed_mul_le2 {f h : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ 2 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hh : ContDiffOn ℝ 2 (Function.uncurry h) Work.FTS.EllipticEst.Q0)
    {j i : ℕ} (hji : j + i ≤ 2) {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ)
    (hθ1 : θ < Real.pi / 2) :
    Work.Spaces.mixed j i (fun z θ => f z θ * h z θ) z θ
      = ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          ((i.choose a : ℝ) * (j.choose b : ℝ))
            * (Work.Spaces.mixed b a f z θ * Work.Spaces.mixed (j - b) (i - a) h z θ) := by
  have hle : ((j + i : ℕ) : WithTop ℕ∞) ≤ ((2 : ℕ) : WithTop ℕ∞) := by exact_mod_cast hji
  exact mixedMulFinLocal (V := Work.FTS.EllipticEst.Q0) Work.FTS.EllipticEst.isOpen_Q0
    (hf.of_le hle) (hh.of_le hle) z θ
    (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩)

end Work.FTS_RegExport.RXT.Sys.GdotAux
