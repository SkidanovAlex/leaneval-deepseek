/-
Copyright: work module for the Elgindi finite-time singularity project.

# The derivative bound on `z ↦ z (D_z f · w)²` near the origin

This file proves `Work.Coercivity.Dz_deriv_bound`: on `(0,1]`, if the radial derivative
and its second radial derivative of a `SmoothNbhd` function satisfy

  `|∂_z f(z,θ)| ≤ C₁ z`   and   `|∂_z² f(z,θ)| ≤ M`,

then the derivative of the weighted square `z (D_z f z θ · w z)²` is bounded by
`32 C₁ M + 48 C₁²`.

The two ingredients are

* `deriv_zw_sq_factor` — the exact value of the derivative, obtained from the algebraic
  identity `zw_sq_factor` (`z (D_z f · w)² = (∂_z f)² (1+z)^4 / z`, valid for `z ≠ 0`)
  and the Leibniz rule `(∂_z f · (1+z)^4/z)' = 2 ∂_z f ∂_z² f (1+z)^4/z
  + (∂_z f)² (1+z)^3 (3z-1)/z²`;

* `deriv_ineq` — the elementary real inequality bounding the resulting expression,
  which uses `(1+z)^k ≤ 2^k` and `|3z-1| ≤ 2` on `(0,1]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Dz_alg
import Submission.Work.Spaces.HardyZ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-- **Exact derivative of the weighted square.**  For `z > 0` and a function smooth on a
neighbourhood of the closed quadrant,

  `d/dz [ z (D_z f z θ · w z)² ] = 2 ∂_z f · ∂_z² f · (1+z)^4/z
      + (∂_z f)² · (1+z)^3 (3z-1)/z²`.

Indeed, for `z' > 0` the algebraic identity `zw_sq_factor` rewrites the left-hand side as
`(∂_z f)² (1+z)^4/z`; the derivative of that expression is the displayed one by the
Leibniz rule, using `deriv (∂_z f(·,θ)) z = ∂_z² f(z,θ)` (smoothness of the `θ`-slice). -/
private theorem deriv_zw_sq_factor (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f)
    {θ z : ℝ} (hθ : θ ∈ Spaces.Iθ) (hz : 0 < z) :
    deriv (fun z' => z' * (Spaces.Dz f z' θ * Spaces.w z') ^ 2) z
      = 2 * (Spaces.pz f z θ) * (Spaces.pz (Spaces.pz f) z θ) * ((1 + z) ^ 4 / z)
        + (Spaces.pz f z θ) ^ 2 * ((1 + z) ^ 3 * (3 * z - 1) / z ^ 2) := by
  -- `z (D_z f · w)² = (∂_z f)² (1+z)^4/z` in a neighbourhood of `z` (where `z' ≠ 0`).
  have hEq : (fun z' => z' * (Spaces.Dz f z' θ * Spaces.w z') ^ 2)
      =ᶠ[𝓝 z] (fun z' => (Spaces.pz f z' θ) ^ 2 * (1 + z') ^ 4 / z') := by
    filter_upwards [isOpen_ne.mem_nhds (ne_of_gt hz)] with z' hz'
    exact zw_sq_factor f hz'
  rw [Filter.EventuallyEq.deriv_eq hEq]
  -- The `θ`-slice is smooth at `z`, so `∂_z f(·,θ)` has derivative `∂_z² f(z,θ)`.
  have hzmem : z ∈ Set.Ioi (-1) := by simp only [Set.mem_Ioi]; linarith
  have ha : HasDerivAt (fun z' => Spaces.pz f z' θ) (Spaces.pz (Spaces.pz f) z θ) z := by
    have hs : ContDiffAt ℝ ⊤ (fun z'' => f z'' θ) z :=
      ((Spaces.hardyZ_contDiffOn_slice f hsm hθ).contDiffAt (isOpen_Ioi.mem_nhds hzmem))
    have hd : DifferentiableAt ℝ (deriv (fun z'' => f z'' θ)) z := by
      have h1 : ContDiffAt ℝ 1 (deriv (fun z'' => f z'' θ)) z :=
        hs.derivWithin (m := 1) (by simp)
      exact h1.differentiableAt (by norm_num)
    have := (hasDerivAt_deriv_iff (f := deriv (fun z'' => f z'' θ)) (x := z)).mpr hd
    simpa [Spaces.pz] using this
  have hz' : z ≠ 0 := ne_of_gt hz
  -- Derivative of `(1+z')^4/z'`.
  have hc : HasDerivAt (fun z' : ℝ => (1 + z') ^ 4 / z')
      ((1 + z) ^ 3 * (3 * z - 1) / z ^ 2) z := by
    have h : HasDerivAt (fun z' : ℝ => 1 + z') 1 z := by
      simpa using (hasDerivAt_id z).const_add 1
    have h1 : HasDerivAt (fun z' : ℝ => (1 + z') ^ 4) (4 * (1 + z) ^ 3) z := by
      convert h.pow 4 using 1
      ring
    have h2 : HasDerivAt (fun z' : ℝ => z') 1 z := hasDerivAt_id z
    have hd := h1.div h2 hz'
    convert hd using 1
    · field_simp
      ring
  -- Leibniz rule for `(∂_z f)² · (1+z')^4/z'`.
  have h2 := (ha.pow 2).mul hc
  have hfun : (fun z' => (Spaces.pz f z' θ) ^ 2 * (1 + z') ^ 4 / z')
      = ((fun z' => Spaces.pz f z' θ) ^ 2 * fun z' => (1 + z') ^ 4 / z') := by
    ext z'; simp only [Pi.pow_apply, Pi.mul_apply]; ring_nf
  rw [hfun, h2.deriv]
  simp only [Pi.pow_apply]
  ring

/-- **Elementary bound on the derivative expression.**  For `0 < z ≤ 1`, `|P| ≤ C₁ z`
and `|Q| ≤ M`,

  `|2 P Q (1+z)^4/z + P² (1+z)^3 (3z-1)/z²| ≤ 32 C₁ M + 48 C₁²`.

The two inequalities `h1, h2` force `C₁, M ≥ 0`.  Splitting with the triangle inequality
and using `|P| ≤ C₁ z`, `|Q| ≤ M`, `(1+z)^4 ≤ 16`, `(1+z)^3 ≤ 8`, `|3z-1| ≤ 2` gives the
claim (only the triples `32` and `16 ≤ 48` being used, so the constants are loose). -/
private theorem deriv_ineq {P Q z C₁ M : ℝ} (hz : 0 < z) (hz1 : z ≤ 1)
    (h1 : |P| ≤ C₁ * z) (h2 : |Q| ≤ M) :
    |2 * P * Q * ((1 + z) ^ 4 / z) + P ^ 2 * ((1 + z) ^ 3 * (3 * z - 1) / z ^ 2)|
      ≤ 32 * C₁ * M + 48 * C₁ ^ 2 := by
  have hC1 : 0 ≤ C₁ := by
    have h : 0 ≤ C₁ * z := le_trans (abs_nonneg P) h1
    exact (mul_nonneg_iff_of_pos_right hz).mp h
  have hM : 0 ≤ M := le_trans (abs_nonneg Q) h2
  have hcpos : (0 : ℝ) ≤ (1 + z) ^ 4 / z := by positivity
  have hp4 : (1 + z) ^ 4 ≤ 16 := by
    have h2' : (1 + z) ≤ 2 := by linarith
    have h0 : (0 : ℝ) ≤ 1 + z := by linarith
    calc (1 + z) ^ 4 ≤ 2 ^ 4 := pow_le_pow_left₀ h0 h2' 4
      _ = 16 := by norm_num
  have hp3 : (1 + z) ^ 3 ≤ 8 := by
    have h2' : (1 + z) ≤ 2 := by linarith
    have h0 : (0 : ℝ) ≤ 1 + z := by linarith
    calc (1 + z) ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ h0 h2' 3
      _ = 8 := by norm_num
  have h3z : |3 * z - 1| ≤ 2 := by
    rw [abs_le]; constructor <;> linarith
  have hT1 : |2 * P * Q * ((1 + z) ^ 4 / z)| ≤ 2 * (C₁ * z) * M * ((1 + z) ^ 4 / z) := by
    have h_eq : |2 * P * Q * ((1 + z) ^ 4 / z)| = 2 * |P| * |Q| * ((1 + z) ^ 4 / z) := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hcpos,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [h_eq]
    have hPQ : |P| * |Q| ≤ (C₁ * z) * M :=
      mul_le_mul h1 h2 (abs_nonneg Q) (by positivity)
    calc 2 * |P| * |Q| * ((1 + z) ^ 4 / z)
        = 2 * (|P| * |Q|) * ((1 + z) ^ 4 / z) := by ring
      _ ≤ 2 * ((C₁ * z) * M) * ((1 + z) ^ 4 / z) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hPQ (by norm_num)) hcpos
      _ = 2 * (C₁ * z) * M * ((1 + z) ^ 4 / z) := by ring
  have hT2 : |P ^ 2 * ((1 + z) ^ 3 * (3 * z - 1) / z ^ 2)|
      ≤ (C₁ * z) ^ 2 * ((1 + z) ^ 3 * |3 * z - 1| / z ^ 2) := by
    have h_eq : |P ^ 2 * ((1 + z) ^ 3 * (3 * z - 1) / z ^ 2)|
        = |P| ^ 2 * ((1 + z) ^ 3 * |3 * z - 1| / z ^ 2) := by
      rw [abs_mul, abs_pow, abs_div, abs_mul,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 + z) ^ 3),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ z ^ 2)]
    rw [h_eq]
    have hP2 : |P| ^ 2 ≤ (C₁ * z) ^ 2 := pow_le_pow_left₀ (abs_nonneg P) h1 2
    have hepos : (0 : ℝ) ≤ (1 + z) ^ 3 * |3 * z - 1| / z ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_right hP2 hepos
  have hmain : |2 * P * Q * ((1 + z) ^ 4 / z) + P ^ 2 * ((1 + z) ^ 3 * (3 * z - 1) / z ^ 2)|
      ≤ 2 * (C₁ * z) * M * ((1 + z) ^ 4 / z)
        + (C₁ * z) ^ 2 * ((1 + z) ^ 3 * |3 * z - 1| / z ^ 2) :=
    le_trans (abs_add_le _ _) (add_le_add hT1 hT2)
  refine le_trans hmain ?_
  have e1 : 2 * (C₁ * z) * M * ((1 + z) ^ 4 / z) = 2 * C₁ * M * (1 + z) ^ 4 := by field_simp
  have e2 : (C₁ * z) ^ 2 * ((1 + z) ^ 3 * |3 * z - 1| / z ^ 2)
      = C₁ ^ 2 * ((1 + z) ^ 3 * |3 * z - 1|) := by field_simp
  rw [e1, e2]
  have hb1 : 2 * C₁ * M * (1 + z) ^ 4 ≤ 32 * C₁ * M := by
    have hcm : (0 : ℝ) ≤ 2 * C₁ * M := by positivity
    calc 2 * C₁ * M * (1 + z) ^ 4 ≤ 2 * C₁ * M * 16 := mul_le_mul_of_nonneg_left hp4 hcm
      _ = 32 * C₁ * M := by ring
  have hb2 : C₁ ^ 2 * ((1 + z) ^ 3 * |3 * z - 1|) ≤ 48 * C₁ ^ 2 := by
    have hbound : (1 + z) ^ 3 * |3 * z - 1| ≤ 16 := by
      calc (1 + z) ^ 3 * |3 * z - 1| ≤ 8 * 2 :=
            mul_le_mul hp3 h3z (abs_nonneg _) (by norm_num)
        _ = 16 := by norm_num
    calc C₁ ^ 2 * ((1 + z) ^ 3 * |3 * z - 1|) ≤ C₁ ^ 2 * 16 :=
          mul_le_mul_of_nonneg_left hbound (sq_nonneg C₁)
      _ ≤ 48 * C₁ ^ 2 := by nlinarith [sq_nonneg C₁]
  linarith

theorem Dz_deriv_bound (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f)
    {θ z C₁ M : ℝ} (hθ : θ ∈ Spaces.Iθ) (hz : 0 < z) (hz1 : z ≤ 1)
    (h1 : |Spaces.pz f z θ| ≤ C₁ * z) (h2 : |Spaces.pz (Spaces.pz f) z θ| ≤ M) :
    |deriv (fun z' => z' * (Spaces.Dz f z' θ * Spaces.w z') ^ 2) z|
      ≤ 32 * C₁ * M + 48 * C₁ ^ 2 := by
  rw [deriv_zw_sq_factor f hsm hθ hz]
  exact deriv_ineq hz hz1 h1 h2

end Work.Coercivity
