/-
Copyright: work module for the Elgindi finite-time singularity project.

# The pointwise Gronwall differential inequality for the slice energy

For a function `u` of class `C^∞` on the open angular interval `(0, π/2)` and
`θ ∈ (0, π/4)`,

  `|deriv (Fsq u) θ| ≤ 8 * Fsq u θ + (Lzero1 u θ) ^ 2`,

where `Fsq u θ = (u θ)^2 + (deriv u θ)^2` and `Lzero1 u = -u'' + (u · tan)' - 6u`.

The proof is a one-line consequence of the first-order system associated with the
equation `Lzero1 u = g`: writing `Lzero1 u θ = -u'' θ + (tan θ · u)' θ - 6 u θ` and
using `(tan θ · u)' = (1/cos θ ^ 2) u θ + tan θ · u' θ`, we get

  `u'' θ = (1/cos θ ^ 2 - 6) u θ + tan θ · u' θ - g θ`,

so that, with `u' = deriv u θ`, `u'' = deriv (deriv u) θ` and `g = Lzero1 u θ`,

  `deriv (Fsq u) θ = 2 u u' + 2 u' u'' = 2 (1/cos θ ^ 2 - 5) u u' + 2 tan θ · u'^2 - 2 g u'`.

On `(0, π/4)` the coefficients are bounded by `|1/cos θ ^ 2 - 5| ≤ 5` and
`|tan θ| ≤ 1`, and the three terms are estimated with `2|xy| ≤ x^2 + y^2`:
`10|u||u'| ≤ 5u^2 + 5u'^2`, `2 tan θ · u'^2 ≤ 2 u'^2` and `2|gu'| ≤ g^2 + u'^2`,
giving the total `≤ 5u^2 + 8u'^2 + g^2 ≤ 8(u^2 + u'^2) + g^2`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.AngAWeak.SliceGronwallDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Set Filter Topology

namespace Work.FTS.EllipticEst.AngAWeak

theorem sliceGronwallPointwise (u : ℝ → ℝ)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4)) :
    |deriv (Work.FTS.EllipticEst.AngAWeak.Fsq u) θ| ≤
      8 * Work.FTS.EllipticEst.AngAWeak.Fsq u θ
        + (Work.FTS.EllipticEst.Lzero1 u θ) ^ 2 := by
  have hθmem : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hnhds : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ nhds θ := isOpen_Ioo.mem_nhds hθmem
  have hcd2 : ContDiffOn ℝ 2 u (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hsm 2
  have hd1 : DifferentiableAt ℝ u θ :=
    (hcd2.contDiffAt hnhds).differentiableAt (by norm_num)
  have hcd1 : ContDiffOn ℝ 1 (deriv u) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hcd2.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hd2 : DifferentiableAt ℝ (deriv u) θ :=
    (hcd1.contDiffAt hnhds).differentiableAt (by norm_num)
  have hcos : Real.cos θ ≠ 0 := by
    have : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
    exact this.ne'
  -- The derivative of the slice energy.
  have hF : deriv (Work.FTS.EllipticEst.AngAWeak.Fsq u) θ
      = 2 * (u θ) * deriv u θ + 2 * (deriv u θ) * deriv (deriv u) θ := by
    have h1 : HasDerivAt (fun t => (u t) ^ 2) (2 * (u θ) * deriv u θ) θ := by
      have h := hd1.hasDerivAt.pow 2
      convert h using 1
      simp
    have h2 : HasDerivAt (fun t => (deriv u t) ^ 2)
        (2 * (deriv u θ) * deriv (deriv u) θ) θ := by
      have h := hd2.hasDerivAt.pow 2
      convert h using 1
      simp
    have h3 := (h1.add h2).deriv
    have hFs : Work.FTS.EllipticEst.AngAWeak.Fsq u
        = fun t => (u t) ^ 2 + (deriv u t) ^ 2 := rfl
    rw [hFs]
    exact h3
  -- The equation solved for the second derivative.
  have htan : deriv (fun t => Real.tan t * u t) θ
      = (1 / Real.cos θ ^ 2) * u θ + Real.tan θ * deriv u θ :=
    ((Real.hasDerivAt_tan hcos).mul hd1.hasDerivAt).deriv
  have hL : Work.FTS.EllipticEst.Lzero1 u θ
      = -(deriv (deriv u) θ) + deriv (fun t => Real.tan t * u t) θ - 6 * u θ := rfl
  have hc : deriv (deriv u) θ
      = (1 / Real.cos θ ^ 2 - 6) * u θ + Real.tan θ * deriv u θ
          - Work.FTS.EllipticEst.Lzero1 u θ := by
    rw [hL, htan]
    ring
  -- The bounds on the two coefficients.
  have hA : |1 / Real.cos θ ^ 2 - 5| ≤ 5 := by
    have h := abs_two_div_one_add_cos_two_sub_five_le hθ
    have hid : 1 / Real.cos θ ^ 2 = 2 / (1 + Real.cos (2 * θ)) := by
      rw [Real.cos_two_mul]
      field_simp
      ring
    rw [hid]
    exact h
  have hT : |Real.tan θ| ≤ 1 := abs_tan_le_one_of_mem hθ
  rw [hF, hc]
  set a : ℝ := u θ
  set b : ℝ := deriv u θ
  set g : ℝ := Work.FTS.EllipticEst.Lzero1 u θ
  set A : ℝ := 1 / Real.cos θ ^ 2
  set T : ℝ := Real.tan θ
  have hAs : |A - 5| ≤ 5 := hA
  have hTs : |T| ≤ 1 := hT
  have hsq : Work.FTS.EllipticEst.AngAWeak.Fsq u θ = a ^ 2 + b ^ 2 := by
    rw [Work.FTS.EllipticEst.AngAWeak.Fsq]
  rw [hsq]
  have hAM1 : 2 * |a| * |b| ≤ a ^ 2 + b ^ 2 := by
    nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]
  have h1 : |2 * (A - 5) * a * b| ≤ 5 * a ^ 2 + 5 * b ^ 2 := by
    have h : |2 * (A - 5) * a * b| = 2 * |A - 5| * |a| * |b| := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [h]
    calc 2 * |A - 5| * |a| * |b| = |A - 5| * (2 * |a| * |b|) := by ring
      _ ≤ 5 * (a ^ 2 + b ^ 2) :=
          mul_le_mul hAs hAM1 (by positivity) (by linarith)
      _ = 5 * a ^ 2 + 5 * b ^ 2 := by ring
  have h2 : |2 * T * b ^ 2| ≤ 2 * b ^ 2 := by
    have h : |2 * T * b ^ 2| = 2 * |T| * b ^ 2 := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_of_nonneg (sq_nonneg b)]
    rw [h]
    calc 2 * |T| * b ^ 2 = (2 * |T|) * b ^ 2 := by ring
      _ ≤ (2 * 1) * b ^ 2 := mul_le_mul_of_nonneg_right (by linarith [hTs]) (sq_nonneg b)
      _ = 2 * b ^ 2 := by ring
  have h3 : |2 * g * b| ≤ g ^ 2 + b ^ 2 := by
    have h : |2 * g * b| = |g| * (2 * |b|) := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      ring
    rw [h]
    nlinarith [sq_abs g, sq_abs b, sq_nonneg (|g| - |b|)]
  have e1 := abs_le.mp h1
  have e2 := abs_le.mp h2
  have e3 := abs_le.mp h3
  rw [abs_le]
  constructor
  · nlinarith [e1.1, e2.1, e3.1, sq_nonneg a, sq_nonneg b]
  · nlinarith [e1.2, e2.2, e3.2, sq_nonneg a, sq_nonneg b]

end Work.FTS.EllipticEst.AngAWeak
