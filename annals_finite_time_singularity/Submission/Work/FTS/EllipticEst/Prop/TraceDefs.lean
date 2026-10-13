/-
Copyright: work module for the Elgindi finite-time singularity project.

# The truncation cutoff `χ` used in the boundary (trace) estimates

This file fixes the cutoff function used by the boundary estimates
`Work.FTS.EllipticEst.Prop.traceBoundLeft` / `traceBoundRight` and proves its elementary
properties: it is `C^∞`, it vanishes on `(-∞, 1/2]`, it equals `1` on `[1, ∞)`, it takes
values in `[0,1]`, and its derivative is bounded.

The cutoff is used as follows: to estimate the boundary flux `F₁ · L₁` at the right endpoint
`θ = π/2` one integrates the identity `(f f')' = (f')² + f f''` against `χ`.  Since `χ`
vanishes identically near `0`, the boundary term at `θ = 0` disappears, and since `χ ≡ 1`
near `π/2` the boundary term at `π/2` is exactly `F₁ L₁`.  The price is the extra term
`-∫ (f χ')²`, which is controlled by the `L²`-norm of `f` and the boundedness of `χ'`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Prop

set_option autoImplicit false

/-- The fixed cutoff `χ(θ) = smoothTransition (2θ - 1)`: it is `0` for `θ ≤ 1/2` and `1` for
`θ ≥ 1`. -/
def chi (θ : ℝ) : ℝ := Real.smoothTransition (2 * θ - 1)

/-- `χ` is of class `C^n` for every `n`. -/
theorem chi_contDiff (n : ℕ) : ContDiff ℝ n chi := by
  have h1 : ContDiff ℝ n Real.smoothTransition :=
    Real.smoothTransition.contDiff (n := (n : ℕ∞))
  have h2 : ContDiff ℝ n (fun θ : ℝ => 2 * θ - 1) := by fun_prop
  exact h1.comp h2

/-- `χ` is smooth. -/
theorem chi_contDiff_top : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) chi := by
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Real.smoothTransition :=
    Real.smoothTransition.contDiff (n := ⊤)
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun θ : ℝ => 2 * θ - 1) := by fun_prop
  exact h1.comp h2

/-- `χ` vanishes on `(-∞, 1/2]`. -/
theorem chi_zero {θ : ℝ} (h : θ ≤ 1 / 2) : chi θ = 0 := by
  rw [chi, Real.smoothTransition.zero_of_nonpos (by linarith)]

/-- `χ` equals `1` on `[1, ∞)`. -/
theorem chi_one {θ : ℝ} (h : 1 ≤ θ) : chi θ = 1 := by
  rw [chi, Real.smoothTransition.one_of_one_le (by linarith)]

/-- `χ` is nonnegative. -/
theorem chi_nonneg (θ : ℝ) : 0 ≤ chi θ := Real.smoothTransition.nonneg _

/-- `χ` is bounded by `1`. -/
theorem chi_le_one (θ : ℝ) : chi θ ≤ 1 := Real.smoothTransition.le_one _

/-- `χ` is locally `0` below `1/2`, hence differentiably `0` there. -/
theorem deriv_chi_eq_zero_of_lt {θ : ℝ} (h : θ < 1 / 2) : deriv chi θ = 0 := by
  have hev : chi =ᶠ[𝓝 θ] fun _ : ℝ => (0 : ℝ) := by
    filter_upwards [isOpen_Iio.mem_nhds h] with t ht
    exact chi_zero ht.le
  rw [hev.deriv_eq, deriv_const]

/-- `χ` is locally `1` above `1`, hence differentiably `0` there. -/
theorem deriv_chi_eq_zero_of_one_lt {θ : ℝ} (h : 1 < θ) : deriv chi θ = 0 := by
  have hev : chi =ᶠ[𝓝 θ] fun _ : ℝ => (1 : ℝ) := by
    filter_upwards [isOpen_Ioi.mem_nhds h] with t ht
    exact chi_one ht.le
  rw [hev.deriv_eq, deriv_const]

/-- The derivative of `χ` is bounded: `(χ')² ≤ K` for a constant `K`.  This is what turns the
truncation error `∫ (f χ')²` into a multiple of the weighted `L²`-norm of `f`. -/
theorem chi_deriv_bdd : ∃ K : ℝ, 0 ≤ K ∧ ∀ θ : ℝ, (deriv chi θ) ^ 2 ≤ K := by
  have hcont : ContinuousOn (deriv chi) (Set.Icc (1 / 2 : ℝ) 1) :=
    ((chi_contDiff 1).continuous_deriv le_rfl).continuousOn
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc hcont
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC (1 / 2) (by norm_num))
  refine ⟨C ^ 2, by positivity, fun θ => ?_⟩
  by_cases hmem : θ ∈ Set.Icc (1 / 2 : ℝ) 1
  · have hb : ‖deriv chi θ‖ ≤ C := hC θ hmem
    rw [Real.norm_eq_abs] at hb
    calc (deriv chi θ) ^ 2 = |deriv chi θ| ^ 2 := by rw [sq_abs]
      _ ≤ C ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
  · rw [Set.mem_Icc, not_and_or] at hmem
    rcases hmem with h | h
    · rw [deriv_chi_eq_zero_of_lt (not_le.mp h)]
      simpa using sq_nonneg C
    · rw [deriv_chi_eq_zero_of_one_lt (not_le.mp h)]
      simpa using sq_nonneg C

end Work.FTS.EllipticEst.Prop
