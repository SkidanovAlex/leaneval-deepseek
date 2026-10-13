/-
Elementary consequences of `ContDiffOn ℝ 2 h (Ioo 0 ε)` used by the endpoint-slope
lemma.  Nothing here is deep: `C²` on an open interval means the derivative is
continuous, the second derivative is continuous, and `deriv h` is differentiable
with derivative `deriv (deriv h)`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Topology

namespace Work.FTS.EllSol

/-- Integrability on an open interval gives interval-integrability on the closed one. -/
theorem intervalIntegrable_of_integrableOn_Ioo {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : IntegrableOn f (Ioo a b)) : IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff, uIoc_of_le hab]
  exact h.congr_set_ae (Ioo_ae_eq_Ioc (μ := volume)).symm

/-- A real `rpow` with positive exponent tends to `0` at `0⁺`. -/
theorem tendsto_rpow_nhdsGT_zero {s : ℝ} (hs : 0 < s) :
    Tendsto (fun r : ℝ => r ^ s) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h1 : Tendsto (fun r : ℝ => r ^ (-s)) (𝓝[>] (0 : ℝ)) atTop :=
    tendsto_rpow_neg_nhdsGT_zero (y := -s) (by linarith)
  have h2 : Tendsto (fun r : ℝ => (r ^ (-s))⁻¹) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_inv_atTop_zero.comp h1
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  rw [Real.rpow_neg (le_of_lt hr), inv_inv]

/-- A `C²` function on an open interval has continuous derivative there. -/
theorem c2_continuousOn_deriv {h : ℝ → ℝ} {ε : ℝ} (hC2 : ContDiffOn ℝ 2 h (Ioo 0 ε)) :
    ContinuousOn (deriv h) (Ioo 0 ε) :=
  hC2.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)

/-- The first derivative of a `C²` function is `C¹` on the same open interval. -/
theorem c2_contDiffOn_one_deriv {h : ℝ → ℝ} {ε : ℝ} (hC2 : ContDiffOn ℝ 2 h (Ioo 0 ε)) :
    ContDiffOn ℝ 1 (deriv h) (Ioo 0 ε) :=
  hC2.deriv_of_isOpen (m := 1) isOpen_Ioo (by norm_num)

/-- The second derivative of a `C²` function is continuous on the open interval. -/
theorem c2_continuousOn_deriv_deriv {h : ℝ → ℝ} {ε : ℝ} (hC2 : ContDiffOn ℝ 2 h (Ioo 0 ε)) :
    ContinuousOn (deriv (deriv h)) (Ioo 0 ε) :=
  ((c2_contDiffOn_one_deriv hC2).deriv_of_isOpen (m := 0) isOpen_Ioo (by norm_num)).continuousOn

/-- `deriv h` is differentiable with derivative `deriv (deriv h)` on an open interval
where `h` is `C²`. -/
theorem c2_hasDerivAt_deriv {h : ℝ → ℝ} {ε x : ℝ} (hC2 : ContDiffOn ℝ 2 h (Ioo 0 ε))
    (hx : x ∈ Ioo 0 ε) : HasDerivAt (deriv h) (deriv (deriv h) x) x :=
  DifferentiableOn.hasDerivAt ((c2_contDiffOn_one_deriv hC2).differentiableOn (by norm_num))
    (isOpen_Ioo.mem_nhds hx)

/-- A `C²` function is differentiable, hence `HasDerivAt` at every point. -/
theorem c2_hasDerivAt_self {h : ℝ → ℝ} {ε x : ℝ} (hC2 : ContDiffOn ℝ 2 h (Ioo 0 ε))
    (hx : x ∈ Ioo 0 ε) : HasDerivAt h (deriv h x) x :=
  (hC2.differentiableOn (by norm_num)).hasDerivAt (isOpen_Ioo.mem_nhds hx)

/-- The second derivative of a `C²` function is interval-integrable on any compact
subinterval of the open interval. -/
theorem c2_intervalIntegrable_deriv_deriv {h : ℝ → ℝ} {ε a b : ℝ}
    (hC2 : ContDiffOn ℝ 2 h (Ioo 0 ε)) (ha : 0 < a) (hab : a ≤ b) (hb : b < ε) :
    IntervalIntegrable (fun x : ℝ => deriv (deriv h) x) volume a b :=
  ContinuousOn.intervalIntegrable_of_Icc hab <| (c2_continuousOn_deriv_deriv hC2).mono <|
    fun _ hx => ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩

/-- The absolute value of the second derivative of a `C²` function is
interval-integrable on any compact subinterval of the open interval. -/
theorem c2_intervalIntegrable_abs_deriv_deriv {h : ℝ → ℝ} {ε a b : ℝ}
    (hC2 : ContDiffOn ℝ 2 h (Ioo 0 ε)) (ha : 0 < a) (hab : a ≤ b) (hb : b < ε) :
    IntervalIntegrable (fun x : ℝ => |deriv (deriv h) x|) volume a b :=
  (c2_intervalIntegrable_deriv_deriv hC2 ha hab hb).abs

end Work.FTS.EllSol
