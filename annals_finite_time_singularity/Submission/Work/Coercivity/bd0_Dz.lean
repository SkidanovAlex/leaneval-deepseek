/-
Copyright: work module for the Elgindi finite-time singularity project.

# The boundary term `z (D_z f · w)²` at `z = 0⁺`

Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021), §6.

The integration by parts in `z` of the coercivity chapter produces, for a
function `u`, the boundary term `z (u w)²` at `z = 0`; this is exactly the field
`IBP.bd0` of the hypothesis package `IBP`.  When the by-parts is applied to the
function `u = D_z f` (which is what happens for the `D_z`-equation of the
coercivity chain) one needs the same vanishing for `D_z f` rather than for `f`
itself.  The lemma `bd0_Dz` below supplies it from `IBP f` alone.

The mechanism: `IBP.bd0` says `z (f w)² → 0`, i.e. (with `w = (1+z)²/z²`) that
`f` vanishes at `z = 0` like `o(z^{3/2})`.  Since `f` is smooth on a
neighbourhood of the closed quadrant, its two-term Taylor expansion
`f = f(0) + z ∂_z f(0) + O(z²)` then forces `f(0) = ∂_z f(0) = 0`, i.e.
`f = O(z²)` and hence `∂_z f = O(z)`.  Therefore

  `z (D_z f · w)² = (1+z)^4 (∂_z f)² / z = O(z) → 0`   (`z → 0⁺`).

The formalisation splits this into two independent steps:

* `bd0_abs_div_rpow` (§9 of the sibling module of the same name) turns
  `IBP.bd0` into `|f z θ| / z^{3/2} → 0`;
* `deriv_sq_div_tendsto` (below) is the pure real-analysis statement that for a
  function `g` that is `C²` at `0` with `|g z|/z^{3/2} → 0`, the second-order
  Taylor information `deriv g 0 = 0` and `deriv g z = O(z)` give
  `(deriv g z)²/z → 0`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.bd0_abs_div_rpow

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

/-! ## The real-analysis step

The whole content is the second-order Taylor expansion of a real function at
`0`.  Hypotheses: `g` is `C²` at `0` and `|g z| / z^{3/2} → 0` along `𝓝[>] 0`.

1. `|g z| = z^{3/2} · (|g z|/z^{3/2}) → 0`, so `g z → 0` and, `g` being
   continuous at `0`, `g 0 = 0`.
2. `slope g 0 z = g z / z = z^{1/2} · (|g z|/z^{3/2}) → 0` (up to sign), so the
   right-sided limit of the slope is `0`; `g` being differentiable at `0` with
   two-sided slope limit `deriv g 0`, uniqueness gives `deriv g 0 = 0`.
3. `ContDiffAt ℝ 2 g 0` gives `ContDiffAt ℝ 1 (deriv g) 0`, hence
   `deriv g z = deriv g 0 + z · deriv (deriv g) 0 + o(z) = O(z)`; consequently
   `(deriv g z)²/z = z · (deriv g z / z)²` tends to `0`. -/

/-- **Second-order Taylor step.**  For a function that is `C²` at `0` and whose
size at `0` is `o(z^{3/2})` in the sense `|g z| / z^{3/2} → 0`, the derivative
satisfies `(deriv g z)² / z → 0` as `z → 0⁺`. -/
theorem deriv_sq_div_tendsto {g : ℝ → ℝ} (hg : ContDiffAt ℝ 2 g 0)
    (hlo : Filter.Tendsto (fun z => |g z| / z ^ (3 / 2 : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Filter.Tendsto (fun z => (deriv g z) ^ 2 / z) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  -- `𝓝[>] 0` is finer than `𝓝[≠] 0`, and it is nontrivial.
  have hle : (𝓝[>] (0 : ℝ)) ≤ 𝓝[≠] (0 : ℝ) := nhdsWithin_mono 0 (fun x hx => ne_of_gt hx)
  have hnb : (𝓝[>] (0 : ℝ)).NeBot := nhdsWithin_Ioi_neBot le_rfl
  -- Step 1: `g z → 0`, hence `g 0 = 0`.
  have hgz0 : Tendsto (fun z : ℝ => g z) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hz : Tendsto (fun z : ℝ => z ^ (3 / 2 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h : Tendsto (fun z : ℝ => z ^ (3 / 2 : ℝ)) (𝓝 0)
          (𝓝 ((0 : ℝ) ^ (3 / 2 : ℝ))) :=
        (Real.continuousAt_rpow_const 0 (3 / 2) (Or.inr (by norm_num))).tendsto
      simpa using h.mono_left nhdsWithin_le_nhds
    refine Tendsto.congr' ?_ (by simpa using hlo.mul hz)
    filter_upwards [self_mem_nhdsWithin] with z hz'
    rw [Real.norm_eq_abs, div_mul_cancel₀ _ (ne_of_gt (Real.rpow_pos_of_pos hz' _))]
  have hg0 : g 0 = 0 :=
    tendsto_nhds_unique (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hgz0
  -- Step 2: the right slope of `g` at `0` vanishes, so `deriv g 0 = 0`.
  have hslope : Tendsto (slope g 0) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h1 : Tendsto (fun z : ℝ => |g z| / z ^ (3 / 2 : ℝ) * z ^ (1 / 2 : ℝ))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hz : Tendsto (fun z : ℝ => z ^ (1 / 2 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        have h : Tendsto (fun z : ℝ => z ^ (1 / 2 : ℝ)) (𝓝 0)
            (𝓝 ((0 : ℝ) ^ (1 / 2 : ℝ))) :=
          (Real.continuousAt_rpow_const 0 (1 / 2) (Or.inr (by norm_num))).tendsto
        simpa using h.mono_left nhdsWithin_le_nhds
      simpa using hlo.mul hz
    refine Tendsto.congr' ?_ h1
    filter_upwards [self_mem_nhdsWithin] with z hz'
    have hzp : z ^ (3 / 2 : ℝ) = z ^ (1 / 2 : ℝ) * z := by
      have h : (3 / 2 : ℝ) = 1 / 2 + 1 := by norm_num
      rw [h, Real.rpow_add hz', Real.rpow_one]
    rw [Real.norm_eq_abs, slope_def_field, hg0, sub_zero, sub_zero, abs_div,
      show |z| = z from abs_of_pos hz', hzp, div_mul_eq_mul_div,
      mul_comm (|g z|) (z ^ (1 / 2 : ℝ)),
      mul_div_mul_left _ _ (ne_of_gt (Real.rpow_pos_of_pos hz' (1 / 2 : ℝ)))]
  have hg'0 : deriv g 0 = 0 := by
    have hd : HasDerivAt g (deriv g 0) 0 := (hg.differentiableAt (by norm_num)).hasDerivAt
    exact tendsto_nhds_unique (hd.tendsto_slope.mono_left hle) hslope
  -- Step 3: `deriv g z = O(z)`, hence `(deriv g z)²/z = z (deriv g z / z)² → 0`.
  have hd2 : HasDerivAt (deriv g) (deriv (deriv g) 0) 0 :=
    ((hg.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt
  have hL : Tendsto (fun z : ℝ => deriv g z / z) (𝓝[≠] (0 : ℝ))
      (𝓝 (deriv (deriv g) 0)) := by
    have h := hd2.tendsto_slope
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    rw [slope_def_field, hg'0, sub_zero, sub_zero]
  have hid : Tendsto (fun z : ℝ => z) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    Filter.tendsto_id'.2 nhdsWithin_le_nhds
  have hL2 : Tendsto (fun z : ℝ => (deriv g z / z) ^ 2) (𝓝[>] (0 : ℝ))
      (𝓝 ((deriv (deriv g) 0) ^ 2)) := (hL.mono_left hle).pow 2
  have hmain : Tendsto (fun z : ℝ => z * (deriv g z / z) ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hid.mul hL2
  refine hmain.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  field_simp

/-! ## The boundary term for `D_z f` -/

/-- **The boundary term `z (D_z f · w)²` at `z = 0⁺` vanishes** for every function
`f` of the integration-by-parts class `IBP` and every angle `θ ∈ [0, π/2]`.

With `D_z f = z ∂_z f` and `w = (1+z)²/z²`,

  `z (D_z f · w)² = (1+z)^4 · (∂_z f)² / z`,

so it suffices that `∂_z f = o(z^{1/2})`: `IBP.bd0` makes the `θ`-slice of `f`
vanish like `o(z^{3/2})` (`bd0_abs_div_rpow`), smoothness upgrades this to
`f = O(z²)`, and the derivative of an `O(z²)` function is `O(z)`. -/
theorem bd0_Dz (f : ℝ → ℝ → ℝ) (hf : IBP f) :
    ∀ θ ∈ Spaces.Iθ, Filter.Tendsto (fun z => z * (Spaces.Dz f z θ * Spaces.w z) ^ 2)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
  intro θ hθ
  -- The `θ`-slice of `f` is smooth on a neighbourhood of `0`.
  have hsm : ContDiffAt ℝ ⊤ (fun z => f z θ) 0 := by
    have hy : (0, θ) ∈ (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1) : Set (ℝ × ℝ)) := by
      have hθ' := hθ
      simp only [Spaces.Iθ, Set.mem_Icc] at hθ'
      rw [Set.mem_prod]
      exact ⟨by simp, by simp only [Set.mem_Ioo]; exact ⟨by linarith [hθ'.1],
        by linarith [hθ'.2, Real.pi_pos]⟩⟩
    have h1 : ContDiffAt ℝ ⊤ (Function.uncurry f) ((0 : ℝ), θ) :=
      hf.smooth.contDiffAt ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds hy)
    have h2 : ContDiffAt ℝ ⊤ (fun z : ℝ => (z, θ)) 0 := by fun_prop
    simpa [Function.uncurry, Function.comp_def] using h1.comp 0 h2
  -- The `IBP.bd0` boundary term gives `|f z θ| / z^{3/2} → 0`.
  have hlo := bd0_abs_div_rpow f hf θ hθ
  have hcore := deriv_sq_div_tendsto (hsm.of_le le_top) hlo
  -- Multiply by the continuous factor `(1+z)^4 → 1`.
  have h1 : Tendsto (fun z : ℝ => (1 + z) ^ 4) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hcont : Continuous fun z : ℝ => (1 + z) ^ 4 := by continuity
    simpa using (hcont.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun z : ℝ => (1 + z) ^ 4 * ((deriv (fun z' => f z' θ) z) ^ 2 / z))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by simpa using h1.mul hcore
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  simp only [Spaces.Dz, Spaces.pz, Spaces.w]
  field_simp

end Work.Coercivity
