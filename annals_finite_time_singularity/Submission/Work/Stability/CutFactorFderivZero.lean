import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Have
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.Cutoff
-- ===== merged: Submission.Work.FTS.EllipticEst.Blocks.DzAgmonDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Blocks

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option autoImplicit false

/-! ## The squared radial weight `ρ = w²` -/

/-- The square of Elgindi's radial weight, `ρ(z) = w(z)²` with `w(z) = (1+z)²/z²`. -/
def W2 (z : ℝ) : ℝ := (Work.Spaces.w z) ^ 2

/-- The closed form of the weight: `ρ(z) = (1+z)⁴/z⁴` (true for every `z`, both sides being
Lean's junk value `0` at `z = 0`). -/
theorem W2_eq (z : ℝ) : W2 z = (1 + z) ^ 4 / z ^ 4 := by
  simp only [W2, Work.Spaces.w, div_pow]
  ring

theorem W2_nonneg (z : ℝ) : 0 ≤ W2 z := by rw [W2_eq]; positivity


/-- The weight `ρ` is smooth on `(0,∞)` (indeed analytic there). -/
theorem W2_contDiffOn : ContDiffOn ℝ ⊤ W2 (Set.Ioi (0 : ℝ)) := by
  have h : W2 = fun z : ℝ => (1 + z) ^ 4 / z ^ 4 := funext W2_eq
  rw [h]
  exact ContDiffOn.div (by fun_prop) (by fun_prop)
    (fun z hz => pow_ne_zero 4 (ne_of_gt hz))

/-! ## The derivative of `ρ(z)·z²` -/

/-- The logarithmic derivative of `z ↦ ρ(z)z² = (1+z)⁴/z²` is `2(z-1)/(z(1+z))`. -/
theorem deriv_W2_mul_sq {z : ℝ} (hz : 0 < z) :
    deriv (fun y : ℝ => W2 y * y ^ 2) z
      = (2 * (z - 1) / (z * (1 + z))) * (W2 z * z ^ 2) := by
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hfun : (fun y : ℝ => W2 y * y ^ 2) = fun y : ℝ => (1 + y) ^ 4 / y ^ 2 := by
    funext y
    rcases eq_or_ne y 0 with rfl | hy
    · norm_num [W2, Work.Spaces.w]
    · rw [W2_eq]
      field_simp
  rw [hfun]
  have hd1 : DifferentiableAt ℝ (fun y : ℝ => (1 + y) ^ 4) z := by fun_prop
  have hd2 : DifferentiableAt ℝ (fun y : ℝ => y ^ 2) z := by fun_prop
  have hd3 : (fun y : ℝ => y ^ 2) z ≠ 0 := by simpa using pow_ne_zero 2 hz0
  rw [show (fun y : ℝ => (1 + y) ^ 4 / y ^ 2)
      = (fun y : ℝ => (1 + y) ^ 4) / (fun y : ℝ => y ^ 2) from rfl]
  rw [deriv_div hd1 hd2 hd3]
  have hv1 : deriv (fun y : ℝ => (1 + y) ^ 4) z = 4 * (1 + z) ^ 3 := by
    change deriv ((fun y : ℝ => 1 + y) ^ 4) z = 4 * (1 + z) ^ 3
    rw [deriv_pow (by fun_prop : DifferentiableAt ℝ (fun y : ℝ => 1 + y) z)]
    simp
  have hv2 : deriv (fun y : ℝ => y ^ 2) z = 2 * z := by
    change deriv ((fun y : ℝ => y) ^ 2) z = 2 * z
    rw [deriv_pow (by fun_prop : DifferentiableAt ℝ (fun y : ℝ => y) z)]
    simp
  rw [hv1, hv2, W2_eq]
  field_simp
  ring

/-- The bound `|(ρz²)'| ≤ (2/z)·ρz²` for `z > 0`, i.e. `|2(z-1)/(z(1+z))| ≤ 2/z`. -/
theorem abs_deriv_W2_mul_sq_le {z : ℝ} (hz : 0 < z) :
    |deriv (fun y : ℝ => W2 y * y ^ 2) z| ≤ 2 / z * (W2 z * z ^ 2) := by
  rw [deriv_W2_mul_sq hz, abs_mul]
  have h2 : |2 * (z - 1) / (z * (1 + z))| ≤ 2 / z := by
    have hz1 : (0 : ℝ) < z * (1 + z) := by positivity
    rw [abs_div, abs_of_pos hz1, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [div_le_div_iff₀ hz1 hz]
    have habs : |z - 1| ≤ 1 + z := abs_le.mpr ⟨by linarith, by linarith⟩
    have key := mul_le_mul_of_nonneg_right
      (show 2 * |z - 1| ≤ 2 * (1 + z) by linarith) (le_of_lt hz)
    nlinarith [key]
  have h3 : 0 ≤ W2 z * z ^ 2 := mul_nonneg (W2_nonneg z) (sq_nonneg z)
  calc |2 * (z - 1) / (z * (1 + z))| * |W2 z * z ^ 2|
      ≤ (2 / z) * (W2 z * z ^ 2) := by
        rw [abs_of_nonneg h3]
        exact mul_le_mul_of_nonneg_right h2 h3
    _ = 2 / z * (W2 z * z ^ 2) := rfl

/-! ## An integrability criterion for functions supported in a compact interval -/

/-- A function which is continuous on `[a,b]` and vanishes outside `[a,b]` is integrable on
`(0,∞)`.  (`∫` over a compact set of a continuous function is finite, and the function
agrees with it off `[a,b]`.) -/
theorem integrableOn_Ioi_of_continuousOn_Icc_of_eq_zero_off {g : ℝ → ℝ} {a b : ℝ}
    (hg : ContinuousOn g (Set.Icc a b)) (h0 : ∀ z, z ∉ Set.Icc a b → g z = 0) :
    IntegrableOn g (Set.Ioi (0 : ℝ)) :=
  (hg.integrableOn_Icc).of_forall_sdiff_eq_zero measurableSet_Ioi (fun z hz => h0 z hz.2)

end

end Work.FTS.EllipticEst.Blocks
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.AeProof.ae.CutSeq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The shifted two-scale cutoff family `Vn` of the level-`0` energy argument

`Vn n z = ψ((n+1)z - 2) · χ(z/(n+1))`, where `ψ = Real.smoothTransition` is the smooth step
(`0` on `(-∞,0]`, `1` on `[1,∞)`) and `χ = Work.Stability.chi` is the bump (`1` on `[-1,1]`,
`0` off `(-2,2)`).

Compared with the sibling family `Work.FTS.EllipticEst.PropL2Cut.Wc` (which is
`ψ((n+1)z)·χ(z/(n+1))`) the step is *shifted* by `2`: the family now vanishes on a whole
neighbourhood `(-∞, 2/(n+1)]` of the origin.  That is exactly what the `w²`-weighted truncated
energy identity needs at the `z → 0⁺` end (with the weight `Vn n·w²` the boundary terms are
identically zero, whereas for `Wc n·w²` they would have to be killed by the flatness of `ψ`).

The two scales are the ones of `Wc`: the `ψ`-ramp sits at `z ≈ 2/(n+1) → 0` and the `χ`-ramp at
`z ≈ n+1 → ∞`, which is what keeps the weighted transfer quantities `(z²·Vn n·w²)''` and
`(z·Vn n·w²)'` uniformly bounded by a multiple of `w²`.
-/

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.AeProof.ae

set_option autoImplicit false










end Work.FTS.EllipticEst.H2W.AeProof.ae
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.PropL2Cut =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.PropL2Cut

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The two-scale cutoff of the `prop:L2` energy arguments

`Wc n z = ψ((n+1) z) · χ(z/(n+1))` where `ψ = Real.smoothTransition` is the smooth step
(`ψ = 0` on `(-∞,0]`, `ψ = 1` on `[1,∞)`) and `χ = Work.Stability.chi` is the bump
(`χ = 1` on `[-1,1]`, `χ = 0` off `(-2,2)`).

The factor `ψ((n+1)·)` makes the family one-sided (vanishing for `z ≤ 0`, as the truncated
`θ`-energy identity requires) and tends to `1` at each fixed `z > 0`; the factor `χ(·/(n+1))`
makes the support compact.  The two scales are what keep the radial weight-derivatives
`(z² W²)''` and `(z W²)'` uniformly bounded. -/

/-- The cutoff family `Wc n z = ψ((n+1) z) · χ(z/(n+1))`. -/
def Wc (n : ℕ) (z : ℝ) : ℝ :=
  Real.smoothTransition (((n : ℝ) + 1) * z) * Work.Stability.chi (z / ((n : ℝ) + 1))


/-! ## Elementary properties of the cutoff -/













end Work.FTS.EllipticEst.PropL2Cut
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.logCutDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS.EllipticEst.TT

/-- **THE LOGARITHMIC CUT-OFF FAMILY.**
`logChi n z = chi (log z / log ((n:ℝ)+2))`, where `chi = Work.ChiExplicit.chi` is the explicit
bump `t ↦ smoothTransition (2 - |t|)`.  It is `1` for `z` in the multiplicative window
`[1/((n:ℝ)+2), (n:ℝ)+2]` and `0` outside `(1/((n:ℝ)+2)², ((n:ℝ)+2)²)`. -/
noncomputable def logChi (n : ℕ) : ℝ → ℝ :=
  fun z => Work.ChiExplicit.chi (Real.log z / Real.log ((n : ℝ) + 2))

/-- The definition, as a rewrite rule. -/
theorem logChi_apply (n : ℕ) (z : ℝ) :
    logChi n z = Work.ChiExplicit.chi (Real.log z / Real.log ((n : ℝ) + 2)) := rfl

/-! ## The arithmetic of the parameter `(n : ℝ) + 2` -/

/-- `(n : ℝ) + 2 > 1` for every `n : ℕ`. -/
lemma one_lt_two_add_natCast (n : ℕ) : (1 : ℝ) < (n : ℝ) + 2 := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-- `(n : ℝ) + 2 ≥ 2`, hence `> 0`. -/
lemma two_le_two_add_natCast (n : ℕ) : (2 : ℝ) ≤ (n : ℝ) + 2 := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-- The denominator of the rescaling is strictly positive: `log ((n:ℝ)+2) > 0`. -/
lemma log_two_add_natCast_pos (n : ℕ) : 0 < Real.log ((n : ℝ) + 2) :=
  Real.log_pos (one_lt_two_add_natCast n)

/-- `log ((n:ℝ)+2) ≥ log 2`, the uniform lower bound on the denominator that makes the
commutator bound `|z χ'(z)| ≤ K / log 2` uniform in `n`. -/
lemma log_two_le_log (n : ℕ) : Real.log 2 ≤ Real.log ((n : ℝ) + 2) :=
  Real.log_le_log (by norm_num) (two_le_two_add_natCast n)

/-! ## The elementary value facts -/

/-- `logChi n` takes values in `[0,1]` everywhere. -/
lemma logChi_mem_Icc (n : ℕ) (z : ℝ) : 0 ≤ logChi n z ∧ logChi n z ≤ 1 :=
  ⟨Work.ChiExplicit.chi_nonneg _, Work.ChiExplicit.chi_le_one _⟩

/-- **Vanishing at the small end**: for `0 < z ≤ 1/((n:ℝ)+2)²` the rescaled logarithm is
`≤ -2`, so `logChi n z = 0`. -/
lemma logChi_eq_zero_of_le {n : ℕ} {z : ℝ} (hz : 0 < z)
    (h : z ≤ 1 / ((n : ℝ) + 2) ^ 2) : logChi n z = 0 := by
  have hlog : 0 < Real.log ((n : ℝ) + 2) := log_two_add_natCast_pos n
  have h1 : Real.log z ≤ Real.log (1 / ((n : ℝ) + 2) ^ 2) := Real.log_le_log hz h
  have h2 : Real.log (1 / ((n : ℝ) + 2) ^ 2) = -(2 * Real.log ((n : ℝ) + 2)) := by
    rw [one_div, Real.log_inv, Real.log_pow]
    push_cast
    ring
  have ht : Real.log z / Real.log ((n : ℝ) + 2) ≤ -2 := by
    rw [div_le_iff₀ hlog]
    linarith
  rw [logChi_apply]
  exact Work.ChiExplicit.chi_eq_zero (by
    rw [abs_of_nonpos (by linarith)]; linarith)

/-- **Vanishing at the large end**: for `z ≥ ((n:ℝ)+2)²` the rescaled logarithm is `≥ 2`, so
`logChi n z = 0`. -/
lemma logChi_eq_zero_of_ge {n : ℕ} {z : ℝ} (h : ((n : ℝ) + 2) ^ 2 ≤ z) : logChi n z = 0 := by
  have hc : 0 < (n : ℝ) + 2 := lt_trans one_pos (one_lt_two_add_natCast n)
  have hlog : 0 < Real.log ((n : ℝ) + 2) := log_two_add_natCast_pos n
  have h1 : Real.log (((n : ℝ) + 2) ^ 2) ≤ Real.log z :=
    Real.log_le_log (pow_pos hc 2) h
  have h2 : Real.log (((n : ℝ) + 2) ^ 2) = 2 * Real.log ((n : ℝ) + 2) := by
    rw [Real.log_pow]
    push_cast
    ring
  have ht : (2 : ℝ) ≤ Real.log z / Real.log ((n : ℝ) + 2) := by
    rw [le_div_iff₀ hlog]
    linarith
  rw [logChi_apply]
  exact Work.ChiExplicit.chi_eq_zero (by
    rw [abs_of_nonneg (by linarith)]; linarith)

end Work.FTS.EllipticEst.TT
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.cutoff_facts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

open scoped ContDiff Topology
open Set Filter

/-! ## Elementary facts about the delivered cut-off `Work.Stability.chi = smoothTransition (2 - ‖·‖)`

The three helpers below are the local ingredients of `cutoff_facts`:

* `deriv_chi_eq_zero_of_abs_le_one` / `deriv_chi_eq_zero_of_two_le_abs` — the derivative of the
  cut-off vanishes on `[-1,1]` (where the bump is locally constant `≡ 1`, Fermat at `±1`) and off
  `(-2,2)` (where the bump is locally constant `≡ 0`, Fermat at `±2`);
* `chi_deriv_bounds` — a universal constant bounding `|χ'|` and `|χ''|` on all of `ℝ`.  Since `χ` is
  `C^∞` and supported in the *compact* set `[-2,2]`, both `χ'` and `χ''` are continuous and vanish
  outside `[-2,2]`, so both are bounded there by compactness;
* `deriv_comp_div` — the chain rule for the rescaling `z ↦ f (z/R)` (no hypothesis on `R`, which is
  irrelevant thanks to the totalised convention `x/0 = 0`).
-/


/-- **`χ' = 0` off `(-2,2)`.**  For `|t| > 2` the cut-off vanishes on a whole neighbourhood of `t`;
at `t = ±2` it is a global minimum (`χ ≥ 0 = χ t`), so Fermat's rule applies. -/
private theorem deriv_chi_eq_zero_of_two_le_abs {t : ℝ} (ht : 2 ≤ |t|) :
    deriv Work.Stability.chi t = 0 := by
  rcases lt_or_eq_of_le ht with h | h
  · have h1 : Work.Stability.chi =ᶠ[𝓝 t] (fun _ : ℝ => (0 : ℝ)) := by
      rw [lt_abs] at h
      rcases h with h | h
      · filter_upwards [Ioi_mem_nhds h] with y hy
        have hy' : 2 < y := hy
        exact Work.Stability.chi_eq_zero (by rw [abs_of_pos (by linarith : 0 < y)]; linarith)
      · have ht2 : t < -2 := by linarith
        filter_upwards [Iio_mem_nhds ht2] with y hy
        have hy' : y < -2 := hy
        exact Work.Stability.chi_eq_zero (by rw [abs_of_neg (by linarith : y < 0)]; linarith)
    rw [h1.deriv_eq, deriv_const]
  · have hct : Work.Stability.chi t = 0 := Work.Stability.chi_eq_zero (le_of_eq h)
    exact IsLocalMin.deriv_eq_zero (Filter.Eventually.of_forall (fun y => by
      rw [hct]; exact Work.Stability.chi_nonneg y))

/-- **The cut-off has bounded first and second derivatives.**  `χ` is `C^∞` and supported in the
compact interval `[-2,2]`, so `χ'` and `χ''` are continuous (as derivatives of `C^∞` functions) and
supported in `[-2,2]` (by the two vanishing lemmas above); a continuous function on a compact set is
bounded. -/
private theorem chi_deriv_bounds :
    ∃ C : ℝ, 0 < C ∧
      (∀ t : ℝ, |deriv Work.Stability.chi t| ≤ C) ∧
      (∀ t : ℝ, |deriv (deriv Work.Stability.chi) t| ≤ C) := by
  have hcd : ContDiff ℝ ∞ Work.Stability.chi := Work.Stability.chi_contDiff
  have hd1 : ContDiff ℝ ∞ (deriv Work.Stability.chi) := contDiff_infty_iff_deriv.mp hcd |>.2
  have hd2 : ContDiff ℝ ∞ (deriv (deriv Work.Stability.chi)) :=
    contDiff_infty_iff_deriv.mp hd1 |>.2
  have hc1 : Continuous (deriv Work.Stability.chi) := hd1.continuous
  have hc2 : Continuous (deriv (deriv Work.Stability.chi)) := hd2.continuous
  -- points outside `[-2,2]` have `|t| > 2`
  have hout : ∀ t : ℝ, t ∉ Set.Icc (-2) 2 → 2 < |t| := by
    intro t ht
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
    rcases ht with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  have hz1 : ∀ t : ℝ, t ∉ Set.Icc (-2) 2 → deriv Work.Stability.chi t = 0 :=
    fun t ht => deriv_chi_eq_zero_of_two_le_abs (hout t ht).le
  have hz2 : ∀ t : ℝ, t ∉ Set.Icc (-2) 2 → deriv (deriv Work.Stability.chi) t = 0 := by
    intro t ht
    have h2 : 2 < |t| := hout t ht
    have hev : deriv Work.Stability.chi =ᶠ[𝓝 t] (fun _ : ℝ => (0 : ℝ)) := by
      rw [lt_abs] at h2
      rcases h2 with h | h
      · filter_upwards [Ioi_mem_nhds h] with y hy
        have hy' : 2 < y := hy
        exact deriv_chi_eq_zero_of_two_le_abs
          (by rw [abs_of_pos (by linarith : 0 < y)]; linarith)
      · have ht2 : t < -2 := by linarith
        filter_upwards [Iio_mem_nhds ht2] with y hy
        have hy' : y < -2 := hy
        exact deriv_chi_eq_zero_of_two_le_abs
          (by rw [abs_of_neg (by linarith : y < 0)]; linarith)
    rw [hev.deriv_eq, deriv_const]
  obtain ⟨M1, hM1⟩ := isCompact_Icc.exists_bound_of_continuousOn hc1.continuousOn
  obtain ⟨M2, hM2⟩ := isCompact_Icc.exists_bound_of_continuousOn hc2.continuousOn
  refine ⟨max M1 (max M2 1), ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_trans (le_max_right M2 1) (le_max_right M1 _))
  · intro t
    by_cases ht : t ∈ Set.Icc (-2:ℝ) 2
    · have h := hM1 t ht
      rw [Real.norm_eq_abs] at h
      exact le_trans h (le_max_left _ _)
    · rw [hz1 t ht, abs_zero]
      exact le_trans zero_le_one (le_trans (le_max_right M2 1) (le_max_right M1 _))
  · intro t
    by_cases ht : t ∈ Set.Icc (-2:ℝ) 2
    · have h := hM2 t ht
      rw [Real.norm_eq_abs] at h
      exact le_trans h (le_trans (le_max_left M2 1) (le_max_right M1 _))
    · rw [hz2 t ht, abs_zero]
      exact le_trans zero_le_one (le_trans (le_max_right M2 1) (le_max_right M1 _))



end Work.FTS.EllipticEst
end
-- ===== merged: Submission.Work.FTS.Galerkin.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Galerkin

set_option autoImplicit false

/-! ## Families of fake-time profiles -/

/-- A function of the self-similar variables `(z,θ)` on the quadrant `[0,∞) × [0,π/2]`. -/
abbrev Fn : Type := ℝ → ℝ → ℝ

/-- A family `(z,θ,τ) ↦ g z θ τ` of fake-time profiles. -/
abbrev Fam : Type := ℝ → ℝ → ℝ → ℝ

/-- `slice g τ` is the profile `g(·,·,τ)` of a family. -/
def slice (g : Fam) (τ : ℝ) : Fn := fun z θ => g z θ τ

@[simp] theorem slice_apply (g : Fam) (τ z θ : ℝ) : slice g τ z θ = g z θ τ := rfl

/-- The family generated by a curve `τ ↦ G τ` of profiles. -/
def famOf (G : ℝ → Fn) : Fam := fun z θ τ => G τ z θ

@[simp] theorem slice_famOf (G : ℝ → Fn) (τ : ℝ) : slice (famOf G) τ = G τ := rfl


/-- The fake-time derivative `∂_τ g(·,·,τ)`. -/
def gdot (g : Fam) (τ : ℝ) : Fn := fun z θ => deriv (fun s => g z θ s) τ


/-! ## The abstract ODE vocabulary used by the Galerkin scheme

The Galerkin scheme of the audit (§4 N6, steps 2–4) reduces the fake-time equation to an ordinary
differential equation in the finite-dimensional space `Fin n → ℝ` of Fourier coefficients; the two
notions below are the abstract solution predicates of that ODE, for an arbitrary normed space `E`.
They live here (and not in `ODE.lean`) only so that the interface `DynInputs` can mention them. -/

/-- `α` solves the ODE `ẋ = f(t,x)` on the closed interval `[0,T]` with `α 0 = x₀`: the derivative
is taken *within* `[0,T]`, so no behaviour of `α` outside the interval is asserted. -/
def IsSolOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E → E) (x₀ : E)
    (T : ℝ) (α : ℝ → E) : Prop :=
  α 0 = x₀ ∧ ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt α (f t (α t)) (Set.Icc 0 T) t

/-- `α` solves the ODE `ẋ = f(t,x)` on the whole half-line `[0,∞)` with `α 0 = x₀`: the derivative
is taken within `Set.Ici 0`, the honest formulation of an evolution equation posed for `τ ≥ 0`. -/
def IsSolGlob {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E → E) (x₀ : E)
    (α : ℝ → E) : Prop :=
  α 0 = x₀ ∧ ∀ t, 0 ≤ t → HasDerivWithinAt α (f t (α t)) (Set.Ici 0) t



/-- A solution on `[0,T']` is a solution on every shorter interval `[0,T]`. -/
theorem IsSolOn.mono {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E → E}
    {x₀ : E} {α : ℝ → E} {T T' : ℝ} (h : IsSolOn f x₀ T' α) (hTT' : T ≤ T') :
    IsSolOn f x₀ T α :=
  ⟨h.1, fun t ht => (h.2 t ⟨ht.1, le_trans ht.2 hTT'⟩).mono (fun s hs => ⟨hs.1, le_trans hs.2 hTT'⟩)⟩

/-! ## The dynamic modulated equation -/

/-- The `τ`-dependent modulation constant of the fake-time equation,
`μ̄(τ) = (1/(2α))(L₁₂(N₀)(0)+L₁₂(N)(0)) + (1/(2α))L₁₂(3D_θg/(1+z))(0)` evaluated on the family
`g` and its stream function `Φ`: the paper's `μ` of §Modulation, made `τ`-dependent, **with the
sign of the transport zero-mode forced by `LGammaT_eq`** (`FTS_MUFUN_SIGN.md` §5, option (a')).

It is `Construction.mufunS`, i.e. `2α·muDyn = μ̄ + L₁₂(Transport g)(0)`
(`Work.Construction.two_mul_mufunS`), *not* the paper-display `Construction.mufun`.  This is
what makes the dynamic profile equation `(E)` hold identically
(`Work.FTS.MeridianDyn.DynEqF`). -/
def muDyn (α : ℝ) (Φ g : Fam) (τ : ℝ) : ℝ :=
  Construction.mufunS α (Construction.N0 α (Construction.Ftau α g τ) (slice g τ))
    (Construction.N α (Construction.Ftau α g τ) (slice Φ τ)) (slice g τ)

/-- The paper's second modulation constant `λ(τ) = -2μ̄(τ)/(1+μ̄(τ))`. -/
def lamDyn (α : ℝ) (Φ g : Fam) (τ : ℝ) : ℝ := Construction.lamfun (muDyn α Φ g τ)

/-- The linear part `-𝓛_Γ^T g(τ)` of the fake-time equation. -/
def dynLin (α : ℝ) (g : Fam) (τ : ℝ) : Fn :=
  fun z θ => -(Coercivity.LGammaT α (slice g τ) z θ)

/-- The nonlinear part of the fake-time equation:
`-μ̄(τ)(Γ/c)2z²/(1+z)³ + N₀ + N + N_*`, evaluated at the τ-dependent modulation constants. -/
def dynRHS (α : ℝ) (Φ g : Fam) (τ : ℝ) : Fn :=
  Construction.gRHS α (muDyn α Φ g τ) (lamDyn α Φ g τ)
    (Construction.Ftau α g τ) (slice Φ τ) (slice g τ)

/-- **The dynamic modulated equation**, in its honest half-line form: for every `τ ≥ 0` and every
point of the open quadrant,
`∂_τ g = -𝓛_Γ^T(g) + gRHS(μ̄(τ), λ(τ), F_*+g(τ), Φ(τ), g(τ))`,
the derivative being taken within `Set.Ici 0` (the equation is only posed for `τ ≥ 0`; no
behaviour at or past the blow-up time of the physical problem is assumed anywhere). -/
def IsDynEqOn (α : ℝ) (Φ g : Fam) : Prop :=
  ∀ z θ τ, 0 ≤ τ → (z, θ) ∈ Construction.Qd →
    HasDerivWithinAt (fun s => g z θ s) (dynLin α g τ z θ + dynRHS α Φ g τ z θ) (Set.Ici 0) τ

/-- The dynamic modulated equation in the two-sided form used by the audit
(`HasDerivAt` at every `τ ≥ 0`, including `τ = 0`).  It is *stronger* than `IsDynEqOn`
(`isDynEqOn_of_isDynEq`): it asks for the derivative also from the left at `τ = 0`. -/
def IsDynEq (α : ℝ) (Φ g : Fam) : Prop :=
  ∀ z θ τ, 0 ≤ τ → (z, θ) ∈ Construction.Qd →
    HasDerivAt (fun s => g z θ s) (dynLin α g τ z θ + dynRHS α Φ g τ z θ) τ



/-- The two modulation constants of the dynamic equation agree with `Construction.mufunS`,
`Construction.lamfun` term by term. -/
theorem muDyn_eq (α : ℝ) (Φ g : Fam) (τ : ℝ) :
    muDyn α Φ g τ
      = Construction.mufunS α (Construction.N0 α (Construction.Ftau α g τ) (slice g τ))
          (Construction.N α (Construction.Ftau α g τ) (slice Φ τ)) (slice g τ) := rfl



/-! ## The elliptic law and packaged solutions -/

/-- The elliptic (Biot–Savart) law on the open quadrant, in the `F`-side convention
`bslOp α Φ = F` (i.e. `Construction.StatEqPhi` restricted to `Qd`).  It is passed as an explicit
parameter `Law` to `IsDynGSolWith`, so that the convention pinned by N1
(audit §4 N1: `bslOp p Φ = -F` is the convention consistent with `Work.Cyl.vorticity_psiField`)
can be substituted without touching this area: pass `fun F Φ => ∀ z θ, (z,θ) ∈ Qd → bslOp α Φ z θ = -F z θ`. -/
def EllLaw (α : ℝ) : Fn → Fn → Prop :=
  fun F Φ => ∀ z θ, (z, θ) ∈ Construction.Qd → Elliptic.bslOp α Φ z θ = F z θ

/-- **A solution of the dynamic modulated problem** with an *explicit* elliptic law `Law`:
the elliptic law holds at every `τ ≥ 0` for the profile `F_* + g(τ)` and its stream function
`Φ(τ)`, and the dynamic equation holds.  This is the form in which the existence theorem of this
area is stated. -/
def IsDynGSolWith (Law : Fn → Fn → Prop) (α : ℝ) (Φ g : Fam) : Prop :=
  (∀ τ, 0 ≤ τ → Law (Construction.Ftau α g τ) (slice Φ τ)) ∧ IsDynEqOn α Φ g

/-- The same, with the two-sided equation `IsDynEq` (the audit's `IsDynGSol` field). -/
def IsDynGSolWithStrong (Law : Fn → Fn → Prop) (α : ℝ) (Φ g : Fam) : Prop :=
  (∀ τ, 0 ≤ τ → Law (Construction.Ftau α g τ) (slice Φ τ)) ∧ IsDynEq α Φ g

/-- A solution of the dynamic modulated problem with the concrete elliptic law `EllLaw α`. -/
def IsDynGSolOn (α : ℝ) (Φ g : Fam) : Prop := IsDynGSolWith (EllLaw α) α Φ g

/-- A solution of the dynamic modulated problem with the concrete elliptic law `EllLaw α`, in the
two-sided form of the audit. -/
def IsDynGSol (α : ℝ) (Φ g : Fam) : Prop := IsDynGSolWithStrong (EllLaw α) α Φ g



/-! ## Admissible data and the regularity package -/

/- The admissible-datum class `DataAdm` moved, in the 2026-10-03 interface fix, to
`Submission/Work/FTS/GalerkinFix/Defs.lean`: the delivered class asked for `Coercivity.HkAdm`,
which contains the analyticity hypothesis `Work.Spaces.SmoothNbhd`, so it is not satisfied by the
localised datum of the route nor by any PDE object.  Its replacement
`Work.FTS.Galerkin.DataAdm α g₀ = LocData.DataAdm α g₀ ∧ L₁₂(g₀)(0) = 0 ∧ RegQ α 5 g₀` is defined
in the fixed interface (design §1.2). -/

/-- **The regularity package** of a solution family `g` of the dynamic modulated equation: smooth
on the interior of the fake-time slab, jointly continuous in `τ` up to `τ = 0`, with `ℋ⁴`- and
`ℋ⁵`-membership at every `τ ≥ 0`, `ℋ³`-membership of `∂_τg`, and vanishing on the angular
boundaries.  This is the interface consumed by N7 (regularity transfer) and N8 (physical
reconstruction): it is *interior* regularity only, uniformly in `τ ≥ 0`, and asserts nothing at or
past the physical blow-up time. -/
structure RegPkg (α : ℝ) (g : Fam) : Prop where
  /-- joint smoothness on the interior of the quadrant, for all fake times near `[0,∞)`; the order
  is `Work.Stability.smoothOrder = ∞` (interior `C^∞`), **not** the analytic order `⊤` of the
  delivered version (which no solution of the equation satisfies — see the interface fix of
  2026-10-03, `Submission/Work/FTS/GalerkinFix/`). -/
  smooth : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
    (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Ioi (-1))
  /-- joint continuity in `τ` up to `τ = 0`, at every point of the open quadrant. -/
  cont : ∀ z θ, (z, θ) ∈ Construction.Qd → ContinuousOn (fun τ => g z θ τ) (Set.Ici 0)
  /-- `ℋ⁴`-membership at every `τ ≥ 0`. -/
  mem4 : ∀ τ, 0 ≤ τ → Spaces.HkMem α 4 (slice g τ)
  /-- `ℋ⁵`-membership at every `τ ≥ 0`. -/
  mem5 : ∀ τ, 0 ≤ τ → Spaces.HkMem α 5 (slice g τ)
  /-- `ℋ³`-membership of the fake-time derivative at every `τ ≥ 0`. -/
  deriv3 : ∀ τ, 0 ≤ τ → Spaces.HkMem α 3 (gdot g τ)
  /-- vanishing on the angular boundaries at every `τ ≥ 0`. -/
  vanish : ∀ τ, 0 ≤ τ → Spaces.VanishTheta (slice g τ)

/-! ## The `ℋ⁴` inner product -/

/-- **The `ℋ⁴` inner product** of the audit (N2): the paper's admissible inner product
`Construction.IsH4IP` together with the symmetry `IP f g = IP g f`.

Symmetry is not implied by `IsH4IP`, but it *is* automatic for the paper's inner product: the
inductive construction (`Work.Coercivity.H1IP`, `HkIPStep`) starts from the symmetric `wip`s and
adds symmetric terms, so every inner product produced by the induction of §"Higher order
derivatives and the inner product on `ℋ^k`" is symmetric.  Symmetry is exactly what turns the
`IP`-orthonormality of the Galerkin basis into the *exactness of the energy identity*
(`IP (galFun φ c) (galFun φ c) = ∑ₖ cₖ²`), which is the point of the audit's step 4. -/
structure IsH4Inner (α : ℝ) (IP : Fn → Fn → ℝ) : Prop extends Construction.IsH4IP α IP where
  /-- `IP` is symmetric. -/
  symm : ∀ f g : Fn, IP f g = IP g f


/-- Bilinearity in the second argument, derived from symmetry and `IsH4IP.smul_fst`. -/
theorem IsH4Inner.smul_snd {α : ℝ} {IP : Fn → Fn → ℝ} (h : IsH4Inner α IP)
    (c : ℝ) (f g : Fn) : IP f (fun z θ => c * g z θ) = c * IP f g := by
  rw [h.symm, h.smul_fst, h.symm]

/-! ## The Galerkin scheme -/

/-- The finite linear combination `∑_{k : Fin n} c k · φ (k : ℕ)` of test functions. -/
def galFun (φ : ℕ → Fn) {n : ℕ} (c : Fin n → ℝ) : Fn :=
  fun z θ => ∑ k : Fin n, c k * φ (k : ℕ) z θ

/-- The Galerkin family with coefficient curve `τ ↦ c τ`. -/
def galFam (φ : ℕ → Fn) (n : ℕ) (c : ℝ → Fin n → ℝ) : Fam :=
  fun z θ τ => galFun φ (c τ) z θ

@[simp] theorem galFam_apply (φ : ℕ → Fn) (n : ℕ) (c : ℝ → Fin n → ℝ) (z θ τ : ℝ) :
    galFam φ n c z θ τ = galFun φ (c τ) z θ := rfl

@[simp] theorem slice_galFam (φ : ℕ → Fn) (n : ℕ) (c : ℝ → Fin n → ℝ) (τ : ℝ) :
    slice (galFam φ n c) τ = galFun φ (c τ) := rfl

/-- The projection of a datum onto the first `n` modes: `(coeffOf IP g₀ φ n) k = IP g₀ (φ k)`.
For an `IP`-orthonormal sequence this is the coefficient of `φ k` in the `IP`-projection of `g₀`
onto the span of the first `n` test functions. -/
def coeffOf (IP : Fn → Fn → ℝ) (g₀ : Fn) (φ : ℕ → Fn) (n : ℕ) : Fin n → ℝ :=
  fun k => IP g₀ (φ (k : ℕ))

/-- The right hand side of the projected (weak) Galerkin equation, as a function of the
coefficient vector `c`: `-𝓛_Γ^T gₙ + gRHS(μ̄,λ,F_*+gₙ,Ψ(gₙ),gₙ)` evaluated on
`gₙ = ∑ c k φ k`.  The stream function of the Galerkin profile is `Ψ (galFam φ n c)`, where `Ψ` is
the stream-function assignment of N1 (`Work.Elliptic.exists_bslSol` / `bslSol_unique`). -/
def galRHS (α : ℝ) (φ : ℕ → Fn) (n : ℕ) (Psi : Fam → Fam) (τ : ℝ) (c : Fin n → ℝ) : Fn :=
  dynLin α (galFam φ n (fun _ => c)) τ
    + dynRHS α (Psi (galFam φ n (fun _ => c))) (galFam φ n (fun _ => c)) τ

/-- The **projected (Galerkin) vector field** in `ℝⁿ`: the `k`-th component is the `IP`-pairing of
the projected right hand side with the `k`-th test function.  The Galerkin scheme of the audit's
step 3 is the ordinary differential equation `ċ = galField(τ, c)` in `Fin n → ℝ`. -/
def galField (α : ℝ) (IP : Fn → Fn → ℝ) (φ : ℕ → Fn) (n : ℕ) (Psi : Fam → Fam) (τ : ℝ)
    (c : Fin n → ℝ) : Fin n → ℝ :=
  fun k => IP (galRHS α φ n Psi τ c) (φ (k : ℕ))

/-- **The projected evolution equation** (the Galerkin ODE, audit step 3): the coefficient curve
`solves the fake-time equation tested against the first `n` modes, in the strong form of an ODE in
`Fin n → ℝ`.  Its equivalence with the weak (tested) form is `isGalerkinCoeff_iff_weak`
(`Submission/Work/FTS/Galerkin/Projection.lean`), which uses the `IP`-orthonormality of the basis. -/
def IsGalerkinCoeff (α : ℝ) (IP : Fn → Fn → ℝ) (φ : ℕ → Fn) (n : ℕ) (Psi : Fam → Fam)
    (c : ℝ → Fin n → ℝ) : Prop :=
  ∀ τ, 0 ≤ τ → HasDerivWithinAt (fun s => c s) (galField α IP φ n Psi τ (c τ)) (Set.Ici 0) τ



/- The density statement `DenseSpan` moved, in the 2026-10-03 interface fix, to
`Submission/Work/FTS/GalerkinFix/Defs.lean`, with the corrected class `RegQ α 4` and the vanishing
of the zero mode in place of `Coercivity.HkAdm` (design §1.2).  Its now-frozen name is
`Work.FTS.Galerkin.DenseSpan α IP φ`, with `IP : ℝ → Fn → Fn → ℝ` as the (curried) inner product.
-/

/-! ## Convergence of families (the compactness step) -/

/-- Pointwise convergence of a sequence of families to a limit family, on the **closed** quadrant
`[0,∞) × [0,π/2]` and for every `τ ≥ 0`.  Convergence on the closed quadrant (and not only on the
open one) is the form the passage to the limit needs: the nonlinear terms of the equation are
functionals of `g` (`L₁₂` integrates `g` over all of `Iθ`, including the angular boundary), so the
limit function has to be identified everywhere on `Iz × Iθ`, not merely almost everywhere.  This is
the convergence consumed by `DynInputs.hLimit`. -/
def ConvPoint (G : ℕ → Fam) (g : Fam) : Prop :=
  ∀ z ∈ Spaces.Iz, ∀ θ ∈ Spaces.Iθ, ∀ τ, 0 ≤ τ →
    Tendsto (fun n => G n z θ τ) atTop (𝓝 (g z θ τ))

/-- The closed fake-time slab `[0,∞) × [0,π/2] × [0,∞)` of the self-similar variables `(z,θ)` and
the fake time `τ`. -/
def Slab : Set (ℝ × ℝ × ℝ) := {p | p.1 ∈ Spaces.Iz ∧ p.2.1 ∈ Spaces.Iθ ∧ 0 ≤ p.2.2}

theorem mem_Slab {p : ℝ × ℝ × ℝ} :
    p ∈ Slab ↔ p.1 ∈ Spaces.Iz ∧ p.2.1 ∈ Spaces.Iθ ∧ 0 ≤ p.2.2 := Iff.rfl


def ConvLocUnif (G : ℕ → Fam) (g : Fam) : Prop :=
  ∀ K : Set (ℝ × ℝ × ℝ), IsCompact K → K ⊆ Slab →
    TendstoUniformlyOn (fun n (p : ℝ × ℝ × ℝ) => G n p.1 p.2.1 p.2.2)
      (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2) atTop K

/-! ## The a-priori input bundle -/

/-- **The weak (tested) form of the dynamic modulated equation**: for every test function `φ k` and
every `τ ≥ 0`, the scalar function `τ ↦ IP (g(τ)) (φ k)` has the derivative obtained by pairing the
right hand side of the dynamic equation with `φ k`. -/
def IsDynWeakOn (α : ℝ) (IP : Fn → Fn → ℝ) (φ : ℕ → Fn) (g Φ : Fam) : Prop :=
  ∀ (k : ℕ) (τ : ℝ), 0 ≤ τ →
    HasDerivWithinAt (fun s => IP (slice g s) (φ k))
      (IP (dynLin α g τ + dynRHS α Φ g τ) (φ k)) (Set.Ici 0) τ

/-- **The weak form determines the equation** (the fundamental lemma of the calculus of variations
for the Galerkin span): if `g` satisfies the tested form against every test function, then it
satisfies the dynamic equation pointwise on the open quadrant.  It is discharged from
`DynInputs.hφ_dense` (density of the span) together with the identification of `IP` with its integral
form on the span. -/
def WeakDetermines (α : ℝ) (IP : Fn → Fn → ℝ) (φ : ℕ → Fn) : Prop :=
  ∀ g Φ : Fam, IsDynWeakOn α IP φ g Φ → IsDynEqOn α Φ g

/-- The profile of the `n`-th Galerkin family at the point `p = (z, θ, τ)`. -/
def prof (φ : ℕ → Fn) (c : ∀ n : ℕ, ℝ → Fin n → ℝ) (n : ℕ) (p : ℝ × ℝ × ℝ) : ℝ :=
  galFun φ (c n p.2.2) p.1 p.2.1

/-- The hypothesis that `c` is a family of Galerkin solutions in the a-priori ball: each truncation
solves its projected evolution equation and its coefficients stay in the ball of radius `R`. -/
def IsGalFam (α : ℝ) (IP : Fn → Fn → ℝ) (φ : ℕ → Fn) (Psi : Fam → Fam) (R : ℝ)
    (c : ∀ n : ℕ, ℝ → Fin n → ℝ) : Prop :=
  (∀ n : ℕ, IsGalerkinCoeff α IP φ n Psi (c n)) ∧
    (∀ (n : ℕ) (τ : ℝ), 0 ≤ τ → ∑ k : Fin n, (c n τ k) ^ 2 ≤ R ^ 2)

/- The structure `DynInputs` moved, in the 2026-10-03 interface fix, to
`Submission/Work/FTS/GalerkinFix/Defs.lean`, with the corrected field list of design §1.2–1.3:
`hLimBound` in place of `hApriori`, `Work.FTS.Nonlin.UnifIP` in place of `IsH4Inner`,
truncation-dependent Lipschitz/bound constants, the canonical stream-function operator `PsiCan`,
the basis class `GalBasis`, `ProfileEquicont` in place of `hProfileLip`, and the corrected data
class `DataAdm`.  Its now-frozen name is `Work.FTS.Galerkin.DynInputs`. -/


end Work.FTS.Galerkin
end
end
-- ===== merged: Submission.Work.FTS.LocData.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData

set_option autoImplicit false

/-- `ℝ³` (definitionally `Work.Cyl.R3`). -/
abbrev R3 : Type := EuclideanSpace ℝ (Fin 3)

/-! ## The localised profile -/

/-- **THE LOCALISED PROFILE** of the route: the profile `F_*` cut off at scale `L`, plus a small
multiple of the bump `h`,

  `locData α L β h = fun z θ => F_*(z,θ)·χ(z/L) + β·h(z,θ)`.

`χ(z/L) = 1` for `z ≤ L` (`L > 0`), so `locData` agrees with the full profile `F_*` near
`z = 0`; it vanishes identically for `z ≥ 2L` together with `h`, so the physical vorticity is
compactly supported (`ProfileZeroFar`). -/
noncomputable def locData (α L β : ℝ) (h : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Work.Construction.Fstar α z θ * Work.Stability.chi (z / L) + β * h z θ

@[simp] theorem locData_apply (α L β : ℝ) (h : ℝ → ℝ → ℝ) (z θ : ℝ) :
    locData α L β h z θ
      = Work.Construction.Fstar α z θ * Work.Stability.chi (z / L) + β * h z θ := rfl

/-- **THE PERTURBATION** `g = locData - F_*` of the modulation: the datum which the
existence theorem (N6) of the route receives.  Note that `locG α L β h` is *not* compactly
supported — `F_*` itself is not — but its support in `z` starts at `z = L`. -/
noncomputable def locG (α L β : ℝ) (h : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => locData α L β h z θ - Work.Construction.Fstar α z θ

@[simp] theorem locG_apply (α L β : ℝ) (h : ℝ → ℝ → ℝ) (z θ : ℝ) :
    locG α L β h z θ = locData α L β h z θ - Work.Construction.Fstar α z θ := rfl

/-- `locG` in terms of the *far part* of the profile: `g = - zfar L F_* + β h`, where
`Work.Stability.zfar L F = (1 - χ(z/L))·F` vanishes for `z ≤ L`. -/
theorem locG_eq_zfar (α L β : ℝ) (h : ℝ → ℝ → ℝ) (z θ : ℝ) :
    locG α L β h z θ
      = - (Work.Stability.zfar L (Work.Construction.Fstar α)) z θ + β * h z θ := by
  rw [locG_apply, locData_apply, Work.Stability.zfar_apply]
  ring


/-! ## The smoothness class and the admissible data -/

/-- **Genuine `C^∞` on the open quadrant** `z > -1`, `0 < θ < π/2` (the order
`Work.Stability.smoothOrder = ∞`, *not* the analytic order `⊤`).  This is the class in which the
cut-off lives; `Work.Spaces.SmoothNbhd` (analyticity on a neighbourhood of the closed quadrant)
is *not* preserved by a cut-off. -/
def SmoothQuad (g : ℝ → ℝ → ℝ) : Prop :=
  ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g)
    (Set.Ioi (-1) ×ˢ Set.Ioo 0 (π / 2))

/-- **THE ADMISSIBLE PERTURBATIONS** of the self-similar profile at `τ = 0`: the datum class of
the existence theorem (N6) of the route,

* `g` is `C^∞` on the open quadrant (`SmoothQuad`);
* `g` vanishes on the two angular boundaries (`Work.Spaces.VanishTheta`) — the profile of the
  paper vanishes like `Γ(θ) = (sinθ cos²θ)^{α/3}` there, and this is what makes the physical
  `e_θ`-field smooth in the frame and its `div` vanish (`Work.ConstructionInstance`'s
  `div_omega0_all`, `isOddVorticity_omegaS`);
* `g` vanishes to second order at the axis `z = 0` (`g 0 θ = 0` and `∂_z g 0 θ = 0`), which is
  what makes the radial weight `w = (1+z)²/z²` harmless;
* `g ∈ ℋ⁴` **honestly** (`Work.Spaces.HkMem α 4 g`), so that `HkNorm α 4 g` is the sum of the
  squared `L²`-norms of the weighted derivatives rather than the junk value of a non-integrable
  iterated integral.

The class is *inhabited*: `g ≡ 0` is admissible, and so is the perturbation
`locG α L β h = - zfar L F_* + β h` of this chapter (`dataAdm_locG`, `dataAdm_hLoc`). -/
def DataAdm (α : ℝ) (g : ℝ → ℝ → ℝ) : Prop :=
  SmoothQuad g ∧ Work.Spaces.VanishTheta g ∧
    (∀ θ ∈ Work.Spaces.Iθ, g 0 θ = 0 ∧ Work.Spaces.pz g 0 θ = 0) ∧
    Work.Spaces.HkMem α 4 g

theorem DataAdm.smoothQuad {α : ℝ} {g : ℝ → ℝ → ℝ} (h : DataAdm α g) : SmoothQuad g := h.1



theorem DataAdm.hkMem {α : ℝ} {g : ℝ → ℝ → ℝ} (h : DataAdm α g) :
    Work.Spaces.HkMem α 4 g := h.2.2.2

/-- All the iterated `D_z`-derivatives of the zero function vanish. -/
theorem DzIter_zero_fun (i : ℕ) :
    Work.Spaces.DzIter i (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ : ℝ => (0 : ℝ) := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Work.Spaces.DzIter_succ, ih]
      funext z θ
      simp [Work.Spaces.Dz, Work.Spaces.pz]

/-- All the iterated `D_θ`-derivatives of the zero function vanish. -/
theorem DthIter_zero_fun (i : ℕ) :
    Work.Spaces.DthIter i (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ : ℝ => (0 : ℝ) := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Work.Spaces.DthIter_succ, ih]
      funext z θ
      simp [Work.Spaces.Dth, Work.Spaces.pth]

/-- All the iterated mixed `D`-derivatives of the zero function vanish. -/
theorem mixed_zero_fun (j i : ℕ) :
    Work.Spaces.mixed j i (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ : ℝ => (0 : ℝ) := by
  simp only [Work.Spaces.mixed, DthIter_zero_fun, DzIter_zero_fun]

/-- The `ℋ^k`-integrand of the zero function vanishes identically. -/
theorem HkIntegrand_zero_fun (α : ℝ) (k : ℕ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α k (fun _ _ : ℝ => (0 : ℝ)) z θ = 0 := by
  rw [Work.Spaces.HkIntegrand]
  simp only [DzIter_zero_fun, mixed_zero_fun, Pi.zero_apply, zero_mul, sq, mul_zero,
    Finset.sum_const_zero, zero_add, ite_self]

/-- The zero function lies in `ℋ^k` for every `k`. -/
theorem HkMem_zero_fun (α : ℝ) (k : ℕ) :
    Work.Spaces.HkMem α k (fun _ _ : ℝ => (0 : ℝ)) := by
  constructor
  · intro z hz
    refine IntegrableOn.congr_fun integrableOn_zero (fun θ _ => ?_) measurableSet_Icc
    exact (HkIntegrand_zero_fun α k z θ).symm
  · refine IntegrableOn.congr_fun integrableOn_zero (fun z _ => ?_) measurableSet_Ici
    rw [funext (fun θ => HkIntegrand_zero_fun α k z θ), integral_zero]


/-! ## The physical vorticity of a profile -/

/-- **The physical vorticity of a self-similar profile** `F`: the `e_θ`-field
`x ↦ F (ρ(x)^p) (θ(x)) • e_θ(x)`, with `ρ = ‖x‖` and `θ = arctan(x₃/r)`.

This is the paper's `ω^θ` as a vector field (up to the overall sign convention of
`Work.Cyl.vorticity_psiField`): the scalar vorticity of an axisymmetric no-swirl field is a
multiple of `e_θ`, and the self-similar ansatz prescribes its amplitude as a function of
`(R,θ) = (ρ^p, arctan(x₃/r))`.  On the symmetry axis `r = 0` both `e_θ` (Lean's junk `1/0 = 0`)
and the `Γ`-factor of the profile vanish, so the field is `0` there. -/
noncomputable def omegaProfile (p : ℝ) (F : ℝ → ℝ → ℝ) : R3 → R3 :=
  fun x => F (Work.Cyl.Rc p x) (Work.Cyl.theta x) • Work.Cyl.eTheta x

@[simp] theorem omegaProfile_apply (p : ℝ) (F : ℝ → ℝ → ℝ) (x : R3) :
    omegaProfile p F x = F (Work.Cyl.Rc p x) (Work.Cyl.theta x) • Work.Cyl.eTheta x := rfl


/-! ## The concrete bump `h`, and the angular majorant -/

/-- The **radial factor** of the bump: `bumpZ z = χ(4z - 5)`, with `z`-support the interval
`(3/4, 7/4)` (where `|4z - 5| < 2`) and `= 1` on `(1, 3/2)`. -/
noncomputable def bumpZ (z : ℝ) : ℝ := Work.Stability.chi (4 * z - 5)

/-- **THE BUMP `h`** of the route: `hLoc α z θ = φ(z)·Γ(θ)` with `φ = bumpZ` and
`Γ(θ) = (sinθ cos²θ)^{α/3}` the paper's angular factor.

* Its `z`-support is the interval `(3/4, 7/4)`: it is compactly supported and vanishes on a
  neighbourhood of `z = 0` (so `g 0 θ = ∂_z g 0 θ = 0` for the perturbations built with it).
* Its angular factor is `Γ` itself, so `hLoc` vanishes at `θ = 0` and `θ = π/2`, and — the reason
  for this choice — the whole angular analysis of `hLoc` is *the same* as that of `F_*`: every
  weighted angular derivative is dominated by the single majorant `angMaj` below.
* `L₁₂(hLoc α)(0) = c(α)·∫_0^∞ φ(s)/s ds`, with `c(α) = ∫_0^{π/2} K Γ ∈ [1/10, 10]`
  (`Work.Spaces.c_bounds`) and `∫_0^∞ φ(s)/s ds > 0` (the integrand is `1/s > 0` on the interval
  `(1, 3/2)`), so it is *strictly positive* (see `L12_hLoc` in the sibling modules). -/
noncomputable def hLoc (α : ℝ) (z θ : ℝ) : ℝ := bumpZ z * Work.Spaces.Gam α θ

@[simp] theorem hLoc_apply (α z θ : ℝ) :
    hLoc α z θ = bumpZ z * Work.Spaces.Gam α θ := rfl

@[simp] theorem bumpZ_apply (z : ℝ) : bumpZ z = Work.Stability.chi (4 * z - 5) := rfl

/-- **THE ANGULAR MAJORANT** of the chapter: the single angular function that dominates every
weighted angular derivative of `F_* = α(Γ/c)·2z/(1+z)²` *and* of the bump `hLoc = φ·Γ`:

  `angMaj α θ = Γ(θ)²·sin(2θ)^{-γ(α)} + Γ(θ)²·sin(2θ)^{-η} + 1`.

It is integrable on `Iθ` with `∫_θ angMaj α ≤ 1000/(3α) + 10001` for `0 < α ≤ 1`
(`integrableOn_angMaj`, `integral_angMaj_le` in `Angular.lean`): the exponents are the two
weights of the paper's `ℋ^k`-integrand, `γ(α) = 1 + α/10` (`Work.Spaces.gam`) and `η = 99/100`
(`Work.Spaces.eta`). -/
noncomputable def angMaj (α θ : ℝ) : ℝ :=
  Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
    + Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) + 1

@[simp] theorem angMaj_apply (α θ : ℝ) :
    angMaj α θ = Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      + Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) + 1 := rfl

theorem angMaj_nonneg {α θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ angMaj α θ := by
  rw [angMaj_apply]
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have h1 : 0 ≤ Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs _)
  have h2 : 0 ≤ Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs _)
  linarith

end Work.FTS.LocData
end
end
-- ===== merged: Submission.Work.FTS.Regularity.chiModuli =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped ContDiff Topology
open Set Filter

set_option autoImplicit false

namespace Work.FTS.Regularity

/-! ## The cut-off is flat off `[-2,2]` -/

/-- **`χ' = 0` strictly outside `[-2,2]`.**  For `2 < |t|` the cut-off vanishes on a whole
neighbourhood of `t` (`chi_eq_zero`), so its derivative there is the derivative of a constant. -/
theorem chi_deriv_eq_zero_of_two_lt_abs {t : ℝ} (ht : 2 < |t|) :
    deriv Work.Stability.chi t = 0 := by
  have hev : Work.Stability.chi =ᶠ[𝓝 t] (fun _ : ℝ => (0 : ℝ)) := by
    rcases lt_abs.mp ht with h | h
    · filter_upwards [Ioi_mem_nhds h] with y (hy : 2 < y)
      exact Work.Stability.chi_eq_zero (by
        rw [abs_of_pos (by linarith : (0 : ℝ) < y)]; linarith)
    · have ht2 : t < -2 := by linarith
      filter_upwards [Iio_mem_nhds ht2] with y (hy : y < -2)
      exact Work.Stability.chi_eq_zero (by
        rw [abs_of_neg (by linarith : y < 0)]; linarith)
  rw [hev.deriv_eq, deriv_const]

/-- **`χ'' = 0` strictly outside `[-2,2]`.**  For `2 < |t|` the derivative `χ'` vanishes on a whole
neighbourhood of `t` (the previous lemma), so the second derivative there is `0`. -/
theorem chi_deriv2_eq_zero_of_two_lt_abs {t : ℝ} (ht : 2 < |t|) :
    deriv (deriv Work.Stability.chi) t = 0 := by
  have hev : deriv Work.Stability.chi =ᶠ[𝓝 t] (fun _ : ℝ => (0 : ℝ)) := by
    rcases lt_abs.mp ht with h | h
    · filter_upwards [Ioi_mem_nhds h] with y (hy : 2 < y)
      exact chi_deriv_eq_zero_of_two_lt_abs (by
        rw [abs_of_pos (by linarith : (0 : ℝ) < y)]; linarith)
    · have ht2 : t < -2 := by linarith
      filter_upwards [Iio_mem_nhds ht2] with y (hy : y < -2)
      exact chi_deriv_eq_zero_of_two_lt_abs (by
        rw [abs_of_neg (by linarith : y < 0)]; linarith)
  rw [hev.deriv_eq, deriv_const]

/-- **A universal bound for `χ'` and `χ''`.**  Both are continuous and vanish off the compact
interval `[-2,2]`, so both are bounded there by compactness.  The constant produced is `≥ 1`, so it
also bounds `|χ|` (which lies in `[0,1]`). -/
theorem chi_deriv_bounds :
    ∃ C : ℝ, 0 < C ∧
      (∀ t : ℝ, |Work.Stability.chi t| ≤ C) ∧
      (∀ t : ℝ, |deriv Work.Stability.chi t| ≤ C) ∧
      (∀ t : ℝ, |deriv (deriv Work.Stability.chi) t| ≤ C) := by
  have hcd : ContDiff ℝ ∞ Work.Stability.chi := Work.Stability.chi_contDiff
  have hd1 : ContDiff ℝ ∞ (deriv Work.Stability.chi) := contDiff_infty_iff_deriv.mp hcd |>.2
  have hd2 : ContDiff ℝ ∞ (deriv (deriv Work.Stability.chi)) :=
    contDiff_infty_iff_deriv.mp hd1 |>.2
  have hc1 : Continuous (deriv Work.Stability.chi) := hd1.continuous
  have hc2 : Continuous (deriv (deriv Work.Stability.chi)) := hd2.continuous
  -- a point outside the closed interval `[-2,2]` is `> 2` in absolute value
  have hout : ∀ t : ℝ, t ∉ Set.Icc (-2) 2 → 2 < |t| := by
    intro t ht
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
    rcases ht with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  obtain ⟨M1, hM1⟩ :=
    (isCompact_Icc (a := (-2 : ℝ)) (b := 2)).exists_bound_of_continuousOn hc1.continuousOn
  obtain ⟨M2, hM2⟩ :=
    (isCompact_Icc (a := (-2 : ℝ)) (b := 2)).exists_bound_of_continuousOn hc2.continuousOn
  have hC1 : M1 ≤ max M1 (max M2 1) := le_max_left _ _
  have hC2 : M2 ≤ max M1 (max M2 1) := le_trans (le_max_left M2 1) (le_max_right M1 _)
  have hone : (1 : ℝ) ≤ max M1 (max M2 1) := le_trans (le_max_right M2 1) (le_max_right M1 _)
  refine ⟨max M1 (max M2 1), lt_of_lt_of_le zero_lt_one hone, ?_, ?_, ?_⟩
  · intro t
    rw [abs_of_nonneg (Work.Stability.chi_nonneg t)]
    exact (Work.Stability.chi_le_one t).trans hone
  · intro t
    by_cases ht : t ∈ Set.Icc (-2 : ℝ) 2
    · rw [← Real.norm_eq_abs]
      exact (hM1 t ht).trans hC1
    · rw [chi_deriv_eq_zero_of_two_lt_abs (hout t ht), abs_zero]
      exact zero_le_one.trans hone
  · intro t
    by_cases ht : t ∈ Set.Icc (-2 : ℝ) 2
    · rw [← Real.norm_eq_abs]
      exact (hM2 t ht).trans hC2
    · rw [chi_deriv2_eq_zero_of_two_lt_abs (hout t ht), abs_zero]
      exact zero_le_one.trans hone

/-! ## The moduli -/


end Work.FTS.Regularity
end
end
-- ===== merged: Submission.Work.R1G7.chi_deriv_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The derivative of the cut-off profile `chi` is bounded and vanishes at `±2`

`Work.Stability.chi` is the `C^∞` bump of the cut-off (`= 1` on `[-1,1]`, `= 0` off `(-2,2)`,
`ContDiffBump 0` with `rIn = 1`, `rOut = 2`).  In this file we prove three facts about
`deriv chi`:

* it is bounded on all of `ℝ` (`∃ K ≥ 0, ∀ x, |deriv chi x| ≤ K`): `chi` is `C^1` with compact
  support, so `deriv chi` is continuous and supported in `[-2,2]`, hence bounded there and `0`
  outside;
* `deriv chi 2 = 0` and `deriv chi (-2) = 0`: `chi` vanishes identically on `(2,3)`, resp. on
  `(-3,-2)`, and `deriv chi` is continuous, so its value at the endpoint `2`, resp. `-2`, is the
  one-sided limit `0`.

The two vanishing statements are instances of two general lemmas about a `C^1` function `f`
vanishing on an open interval `(a,b)`: then `deriv f` vanishes at the endpoints `a` and `b`.
-/

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.R1G7

/-- **The derivative vanishes where the function does.**  If `f` vanishes identically on the open
interval `(a,b)`, then `deriv f y = 0` at every *interior* point `y ∈ (a,b)`: near such a point
`f` agrees with the constant function `0`. -/
theorem deriv_eq_zero_of_eqOn_Ioo {f : ℝ → ℝ} {a b y : ℝ} (hy : y ∈ Ioo a b)
    (h : ∀ z ∈ Ioo a b, f z = 0) : deriv f y = 0 := by
  -- A full neighbourhood of the interior point `y` stays inside `(a,b)`.
  have hε : 0 < min (y - a) (b - y) := lt_min (sub_pos.mpr hy.1) (sub_pos.mpr hy.2)
  have hev : f =ᶠ[𝓝 y] (fun _ : ℝ => (0 : ℝ)) := by
    refine Filter.eventually_of_mem (Metric.ball_mem_nhds y hε) ?_
    intro z hz
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hz
    exact h z ⟨by linarith [hz.1, min_le_left (y - a) (b - y)],
                   by linarith [hz.2, min_le_right (y - a) (b - y)]⟩
  rw [hev.deriv_eq]
  simp

/-- **Vanishing at the left endpoint.**  If `f` vanishes identically on `(a,b)` with `a < b` and
`deriv f` is continuous, then `deriv f a = 0`: on `(a,b)` the derivative vanishes, so the
right-hand limit of `deriv f` at `a` is `0`, and by continuity this is `deriv f a`. -/
theorem deriv_eq_zero_left_endpoint {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hc : Continuous (deriv f)) (h : ∀ y ∈ Ioo a b, f y = 0) : deriv f a = 0 := by
  have hright : Tendsto (deriv f) (𝓝[>] a) (𝓝 (deriv f a)) :=
    hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hev : (deriv f) =ᶠ[𝓝[>] a] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [Ioo_mem_nhdsGT hab] with y hy
    exact deriv_eq_zero_of_eqOn_Ioo hy h
  exact tendsto_nhds_unique hright (Filter.Tendsto.congr' hev.symm tendsto_const_nhds)

/-- **Vanishing at the right endpoint.**  If `f` vanishes identically on `(a,b)` with `a < b` and
`deriv f` is continuous, then `deriv f b = 0`. -/
theorem deriv_eq_zero_right_endpoint {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hc : Continuous (deriv f)) (h : ∀ y ∈ Ioo a b, f y = 0) : deriv f b = 0 := by
  have hleft : Tendsto (deriv f) (𝓝[<] b) (𝓝 (deriv f b)) :=
    hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hev : (deriv f) =ᶠ[𝓝[<] b] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [Ioo_mem_nhdsLT hab] with y hy
    exact deriv_eq_zero_of_eqOn_Ioo hy h
  exact tendsto_nhds_unique hleft (Filter.Tendsto.congr' hev.symm tendsto_const_nhds)

/-- The derivative of the cut-off `Work.Stability.chi` vanishes on `(2, x+1)`, resp. on
`(x-1, -2)`, for `|x| > 2` — `chi` is `0` off `(-2,2)`. -/
theorem chi_eq_zero_of_two_lt_abs {z : ℝ} (h : 2 < |z|) : Work.Stability.chi z = 0 := by
  rcases lt_abs.mp h with h2 | h2
  · exact Work.Stability.chi_eq_zero (by rw [abs_of_pos (by linarith)]; linarith)
  · exact Work.Stability.chi_eq_zero (by rw [abs_of_neg (by linarith)]; linarith)

/-- **The derivative of the cut-off is bounded, and vanishes at `±2`.** -/
theorem chi_deriv_bound :
    ∃ K : ℝ, 0 ≤ K ∧ (∀ x : ℝ, |deriv Work.Stability.chi x| ≤ K) ∧
      deriv Work.Stability.chi 2 = 0 ∧ deriv Work.Stability.chi (-2) = 0 := by
  -- `chi` is `C^1`, so `deriv chi` is continuous.
  have hc : Continuous (deriv Work.Stability.chi) :=
    (Work.Stability.chi_contDiff.of_le (by exact_mod_cast le_top)).continuous_deriv le_rfl
  -- A continuous function is bounded on the compact interval `[-2,2]`.
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc : IsCompact (Icc (-2 : ℝ) 2)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 0, le_max_right C 0, ?_, ?_, ?_⟩
  · intro x
    rcases le_or_gt |x| 2 with hx | hx
    · -- Inside `[-2,2]` use the compactness bound.
      have hmem : x ∈ Icc (-2 : ℝ) 2 := by rw [mem_Icc, abs_le] at *; exact hx
      have h1 := hC x hmem
      rw [Real.norm_eq_abs] at h1
      exact h1.trans (le_max_left C 0)
    · -- Outside `[-2,2]` the derivative vanishes (`chi` is identically `0` there).
      have hz : deriv Work.Stability.chi x = 0 := by
        rcases lt_abs.mp hx with h2 | h2
        · exact deriv_eq_zero_of_eqOn_Ioo (a := 2) (b := x + 1) ⟨h2, by linarith⟩
            (fun z hz => chi_eq_zero_of_two_lt_abs (by rw [abs_of_pos (by linarith [hz.1])]; linarith [hz.1]))
        · have hx2 : x < -2 := by linarith
          exact deriv_eq_zero_of_eqOn_Ioo (a := x - 1) (b := -2) ⟨by linarith, hx2⟩
            (fun z hz => chi_eq_zero_of_two_lt_abs (by rw [abs_of_neg (by linarith [hz.2])]; linarith [hz.2]))
      rw [hz, abs_zero]
      exact le_max_right C 0
  · -- `chi` vanishes on `(2,3)`, so its derivative vanishes at the endpoint `2`.
    exact deriv_eq_zero_left_endpoint (a := 2) (b := 3) (by norm_num) hc
      (fun z hz => chi_eq_zero_of_two_lt_abs (by rw [abs_of_pos (by linarith [hz.1])]; linarith [hz.1]))
  · -- `chi` vanishes on `(-3,-2)`, so its derivative vanishes at the endpoint `-2`.
    exact deriv_eq_zero_right_endpoint (a := -3) (b := -2) (by norm_num) hc
      (fun z hz => chi_eq_zero_of_two_lt_abs (by rw [abs_of_neg (by linarith [hz.2])]; linarith [hz.2]))

end Work.R1G7
end
end
-- ===== merged: Submission.Work.Stability.ChiDerivZero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Stability

/-- The derivative of an even function at `0` vanishes: if `f (-x) = f x` for all `x`, then
`deriv f 0 = 0`.  (Mathlib's `deriv_comp_neg` computes the derivative of `x ↦ f (-x)` as
`x ↦ -deriv f (-x)`; at `x = 0` the two functions agree by evenness.) -/
theorem deriv_zero_of_even {f : ℝ → ℝ} (hf : ∀ x, f (-x) = f x) : deriv f 0 = 0 := by
  have h := deriv_comp_neg (f := f) (x := 0)
  rw [show (fun x : ℝ => f (-x)) = f from funext hf] at h
  simp only [neg_zero] at h
  linarith


end Work.Stability
end
-- ===== merged: Submission.Work.Stability.CutFactorContDiff =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Stability

/-- The cut-off factor `x ↦ chi(ρ(x)/L)` of `ℝ³` (`ρ = ‖·‖`, `chi` the `C^∞` bump of
`Work.Stability.Cutoff`) is `C^n` for every `n`: near the origin it is identically `1` (as
`chi ≡ 1` on `[-1,1]` does it), and away from the origin it is the composition of the `C^∞` bump
`chi` with the smooth `ρ = ‖·‖`. -/
theorem CutFactorContDiff {L : ℝ} (hL : 0 < L) (n : ℕ) :
    ContDiff ℝ (n : WithTop ℕ∞)
      (fun x : Work.Cyl.R3 => Work.Stability.chi (Work.Cyl.rho x / L)) := by
  -- It suffices to check smoothness at each point.
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : Work.Cyl.rho x = 0
  · -- At the origin (the only point where `rho` vanishes) the factor is *eventually* `1`:
    -- on the ball of radius `L` we have `‖y‖ < L`, so `|rho y / L| ≤ 1` and `chi` equals `1`.
    have hx0 : x = 0 := by
      have h : ‖x‖ = 0 := by rw [← Work.Cyl.rho_eq_norm]; exact hx
      exact norm_eq_zero.mp h
    refine ContDiffAt.congr_of_eventuallyEq (contDiffAt_const (c := (1 : ℝ))) ?_
    refine Filter.eventually_of_mem (Metric.ball_mem_nhds x hL) ?_
    intro y hy
    rw [Metric.mem_ball, dist_eq_norm] at hy
    rw [hx0, sub_zero] at hy
    show Work.Stability.chi (Work.Cyl.rho y / L) = 1
    rw [Work.Cyl.rho_eq_norm]
    apply Work.Stability.chi_eq_one
    rw [abs_le]
    exact ⟨by have := div_nonneg (norm_nonneg y) hL.le; linarith,
           by rw [div_le_one hL]; linarith⟩
  · -- Off the origin, `rho = ‖·‖` is `C^∞` and `chi` is `C^∞`, so the composition is `C^n`.
    have hxne : x ≠ 0 := by
      rw [← Work.Cyl.rho_pos_iff]
      exact lt_of_le_of_ne (Work.Cyl.rho_nonneg x) (Ne.symm hx)
    have hrho : ContDiffAt ℝ (n : WithTop ℕ∞) (fun y : Work.Cyl.R3 => Work.Cyl.rho y) x := by
      have h1 : ContDiffAt ℝ (n : WithTop ℕ∞) (fun y : Work.Cyl.R3 => ‖y‖) x :=
        contDiffAt_norm ℝ hxne
      exact h1.congr_of_eventuallyEq
        (Filter.EventuallyEq.of_eq (funext fun y => Work.Cyl.rho_eq_norm y))
    have hchi : ContDiff ℝ (n : WithTop ℕ∞) Work.Stability.chi :=
      Work.Stability.chi_contDiff.of_le (by exact_mod_cast le_top)
    have hdiv : ContDiffAt ℝ (n : WithTop ℕ∞) (fun y : Work.Cyl.R3 => Work.Cyl.rho y / L) x :=
      hrho.div_const L
    -- NOTE (ChiExplicit repoint): `Work.Stability.chi` is now the *explicit* function
    -- `smoothTransition (2 - ‖·‖)`, so it unfolds to a composition; the implicit `g` and `f` of
    -- `ContDiffAt.comp` must therefore be given explicitly, otherwise the elaborator decomposes the
    -- composite as `smoothTransition ∘ (2 - ‖·‖)`.
    exact ContDiffAt.comp (g := Work.Stability.chi)
      (f := fun y : Work.Cyl.R3 => Work.Cyl.rho y / L) x hchi.contDiffAt hdiv

end Work.Stability
end
-- ===== merged: Submission.Work.Stability.CutFactorFderivLipschitz =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The derivative of the cut-off factor is Lipschitz

The cut-off factor on `ℝ³` is `x ↦ chi (ρ x / L)`, where `ρ x = ‖x‖` (`Work.Cyl.rho`) and `chi` is
the `C^∞` bump of `Work.Stability.Cutoff` (equal to `1` on `[-1,1]` and to `0` off `(-2,2)`).

We prove `Work.Stability.CutFactorFderivLipschitz`: `fderiv ℝ (x ↦ chi (ρ x / L))` is Lipschitz.

The argument is the classical "smooth, compactly supported ⟹ the derivative is Lipschitz":
* `x ↦ chi (ρ x / L)` is `C^n` for every `n : ℕ` — near the origin it is identically `1`, and away
  from the origin it is the composition of the `C^∞` bump with the smooth `‖·‖/L`;
* it has compact support, contained in the ball of radius `2L` (it vanishes where `ρ ≥ 2L`);
* so `fderiv ℝ (·)` of it is again smooth (`ContDiff ℝ 1`) with compact support, and a `C^1`
  function with compact support is Lipschitz (`ContDiff.lipschitzWith_of_hasCompactSupport`).
-/

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.Stability

set_option autoImplicit false

/-! ## Smoothness of the cut-off factor -/




/-! ## Compact support of the cut-off factor -/

/-- Off the ball of radius `2L` the cut-off factor vanishes, so its support is contained in the
closed ball of radius `2L` (`ρ = ‖·‖`). -/
theorem cutFactor_support_subset {L : ℝ} (hL : 0 < L) :
    Function.support (fun x : Work.Cyl.R3 => Work.Stability.chi (Work.Cyl.rho x / L)) ⊆
      Metric.closedBall (0 : Work.Cyl.R3) (2 * L) := by
  intro x hx
  rw [Function.mem_support] at hx
  rw [Metric.mem_closedBall, dist_zero_right, ← Work.Cyl.rho_eq_norm]
  by_contra h
  rw [not_le] at h
  have hzero : Work.Stability.chi (Work.Cyl.rho x / L) = 0 := by
    apply Work.Stability.chi_eq_zero
    rw [abs_of_nonneg (div_nonneg (Work.Cyl.rho_nonneg x) hL.le)]
    rw [le_div_iff₀ hL]
    linarith
  exact hx hzero


/-! ## The derivative is Lipschitz -/


end Work.Stability
end
end
-- ===== merged: Submission.Work.Stability.CutFactorFderivZero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Topology
open Filter

namespace Work.Stability

/-- Off the ball of radius `2L` the cut-off factor `x ↦ chi(ρ(x)/L)` vanishes identically on a
whole neighbourhood (because `chi` vanishes off `(-2,2)` and `ρ` is continuous), hence so does its
derivative: for `2L < ρ(x)`, `fderiv ℝ (fun y => chi(ρ(y)/L)) x = 0`. -/
theorem CutFactorFderivZero {L : ℝ} (hL : 0 < L) {x : Work.Cyl.R3}
    (hx : 2 * L < Work.Cyl.rho x) :
    fderiv ℝ (fun y : Work.Cyl.R3 => Work.Stability.chi (Work.Cyl.rho y / L)) x = 0 := by
  have hrho : Continuous (fun y : Work.Cyl.R3 => Work.Cyl.rho y) :=
    continuous_norm.congr (fun y => (Work.Cyl.rho_eq_norm y).symm)
  have hcont : Continuous (fun y : Work.Cyl.R3 => Work.Cyl.rho y / L) := hrho.div_const L
  have h2 : 2 < Work.Cyl.rho x / L := (lt_div_iff₀ hL).mpr hx
  have hev : (fun y : Work.Cyl.R3 => Work.Stability.chi (Work.Cyl.rho y / L)) =ᶠ[𝓝 x]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [hcont.continuousAt.eventually (isOpen_Ioi.mem_nhds h2)] with y hy
    rw [chi_eq_zero]
    rw [abs_of_pos (by linarith)]
    exact le_of_lt hy
  rw [hev.fderiv_eq]
  simp

end Work.Stability
end
