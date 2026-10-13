import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS_RegExport.RXT.L12Iter.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.Sys.L12FKaux

set_option autoImplicit false

open scoped Real Topology
open MeasureTheory Set Filter

/-- **The angular-moment bound.**  If the `D_z`-iterates of `f` of order `≤ 2` obey the
standing weighted bound `|D_z^k f| ≤ C₀ · z^{3/2}/(1+z)²` in the open quadrant, then the
angular moment `Qang f k s = ∫_θ K(θ)·D_z^k f (s,θ) dθ` obeys the same bound (with the
extra factor `3·(π/2)` coming from `|K| ≤ 3` and the length `π/2` of `Iθ`).

The proof is the `θ`-integral mean inequality: `|K(θ)·D_z^k f (s,θ)| ≤ 3·C₀·Rwt s` on all of
`Iθ` (at the endpoints `K` vanishes, so only the interior hypothesis on `f` is needed). -/
theorem Qang_le {f : ℝ → ℝ → ℝ} {C0 : ℝ} (hC0 : 0 ≤ C0)
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hbd : ∀ k : ℕ, k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k f z θ| ≤ C0 * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2))
    {k : ℕ} (hk : k ≤ 2) {s : ℝ} (hs : 0 < s) :
    |Work.Elliptic.Qang f k s| ≤ 3 * (Real.pi / 2) * (C0 * (s ^ ((3 : ℝ) / 2) / (1 + s) ^ 2)) := by
  have hbd' : ∀ k : ℕ, k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k f z θ| ≤ C0 * Work.FTS_RegExport.RXT.L12Iter.Rwt z := hbd
  have hint :=
    Work.FTS_RegExport.RXT.L12Iter.integrable_Ktheta_mul_DzIter hC0 h4 hbd' hk hs
  have hbnd := Work.FTS_RegExport.RXT.L12Iter.abs_Ktheta_mul_DzIter_le hC0 hbd' hk hs
  have h1 : ‖Work.Elliptic.Qang f k s‖
      ≤ ∫ θ in Work.Spaces.Iθ, ‖Work.Elliptic.Ktheta θ * Work.Spaces.DzIter k f s θ‖ := by
    rw [Work.Elliptic.Qang]
    exact MeasureTheory.norm_integral_le_integral_norm _
  have h2 : (∫ θ in Work.Spaces.Iθ, ‖Work.Elliptic.Ktheta θ * Work.Spaces.DzIter k f s θ‖)
      ≤ ∫ θ in Work.Spaces.Iθ, 3 * (C0 * Work.FTS_RegExport.RXT.L12Iter.Rwt s) :=
    MeasureTheory.integral_mono_ae hint.norm (MeasureTheory.integrable_const _) hbnd
  have h3 : (∫ θ in Work.Spaces.Iθ, 3 * (C0 * Work.FTS_RegExport.RXT.L12Iter.Rwt s))
      = 3 * (Real.pi / 2) * (C0 * Work.FTS_RegExport.RXT.L12Iter.Rwt s) := by
    rw [Work.Elliptic.integral_Iθ_eq_interval, intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    ring
  rw [Real.norm_eq_abs] at h1
  have h4' : |Work.Elliptic.Qang f k s|
      ≤ 3 * (Real.pi / 2) * (C0 * Work.FTS_RegExport.RXT.L12Iter.Rwt s) :=
    le_trans h1 (le_trans h2 h3.le)
  simpa only [Work.FTS_RegExport.RXT.L12Iter.Rwt] using h4'

end Work.FTS_RegExport.RXT.Sys.L12FKaux
