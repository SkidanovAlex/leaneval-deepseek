import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Submission.Work.Construction.L12_Fstar_eq
import Submission.Work.FM.Core

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `L₁₂(F_*) = 2α/(1+z)` on the whole range `z > -1`

The profile identity `L₁₂(F_*)(z) = 2α/(1+z)` is proved in
`Submission/Work/Construction/L12_Fstar_eq.lean` (`Work.Construction.L12_Fstar_eq`) under the
hypothesis `0 ≤ z`, inherited from `Work.FM.integral_Ioi_Fstar_div`, whose proof uses the
FTC lemma `MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg'` with the profile computed as
`F_*(s)/s = 2/(1+s)²`.

Both the identity and its proof are valid on the larger range `z > -1`: the only obstruction
of the radial profile `F_*(s) = 2s/(1+s)²` is the pole of `2/(1+s)²` at `s = -1`, and every
`z > -1` gives an integration domain `(z, ∞)` on which the integrand is bounded.  The single
point `s = 0`, where `F_*(s)/s` and `2/(1+s)²` differ (Lean's totalised division gives
`0/0 = 0`), is Lebesgue-null, so the two functions are a.e. equal on `(z, ∞)` and the same
computation applies once the pointwise rewrite is replaced by an a.e. one.

This generalised form is what downstream `FTS`/`Nonlinear` consumers of the profile identity
need, since they work on the open half line `z > -1` rather than on `z ≥ 0`.
-/

noncomputable section

open scoped Real Topology MeasureTheory Filter
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.FstarPkg

/-- The improper integral of the radial profile, `∫_z^∞ F_*(s)/s ds = 2/(1+z)`, for every
`z > -1`.  This is `Work.FM.integral_Ioi_Fstar_div` with the hypothesis `0 ≤ z` relaxed to
`-1 < z`; the two only differ at the null set `{0}`, on which the pointwise identity
`F_*(s)/s = 2/(1+s)²` fails. -/
theorem integral_Ioi_Fstar_div_of_gt_neg_one (z : ℝ) (hz : -1 < z) :
    ∫ s in Ioi z, Work.FM.Fstar s / s = 2 / (1 + z) := by
  -- `F_*(s)/s = 2/(1+s)^2` off the null set `{0}`
  have hae : ∀ᵐ s ∂(volume : MeasureTheory.Measure ℝ),
      s ∈ Ioi z → Work.FM.Fstar s / s = 2 / (1 + s) ^ 2 := by
    rw [MeasureTheory.ae_iff]
    have hsub : {s : ℝ | ¬ (s ∈ Ioi z → Work.FM.Fstar s / s = 2 / (1 + s) ^ 2)}
        ⊆ ({0} : Set ℝ) := by
      intro s hs
      by_contra h0
      refine hs (fun hsz => ?_)
      have hs1 : (0 : ℝ) < 1 + s := by have hsz' : z < s := hsz; linarith
      have h1 : (1 : ℝ) + s ≠ 0 := ne_of_gt hs1
      have h2 : (1 + s) ^ 2 ≠ 0 := pow_ne_zero 2 h1
      have hsne : s ≠ 0 := by intro h; exact h0 (by simp [h])
      unfold Work.FM.Fstar
      field_simp
    refine MeasureTheory.measure_mono_null hsub ?_
    rw [Real.volume_singleton]
  rw [MeasureTheory.setIntegral_congr_ae measurableSet_Ioi hae]
  -- `∫_z^∞ 2/(1+s)^2 ds` by FTC-2, with primitive `-2/(1+s)` (a limit `0` at `+∞`)
  have key := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg'
    (g := fun t : ℝ => -2 / (1 + t)) (g' := fun t : ℝ => 2 / (1 + t) ^ 2) (a := z) (l := 0)
    ?_ ?_ ?_
  · rw [key]; ring
  · intro x hx
    have hx1 : (1 : ℝ) + x ≠ 0 := by have := hx.out; linarith
    simpa using Work.FM.hasDerivAt_div_add_const (-2) 1 x hx1
  · intro x hx
    have hx0 : (0 : ℝ) < 1 + x := by have := hx.out; linarith
    positivity
  · have h1 : Tendsto (fun t : ℝ => (1 : ℝ) + t) atTop atTop :=
      tendsto_atTop_add_const_left atTop (1 : ℝ) tendsto_id
    have h2 : Tendsto (fun t : ℝ => ((1 : ℝ) + t)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp h1
    have h3 := h2.const_mul (-2 : ℝ)
    simpa [div_eq_mul_inv] using h3

/-- `L₁₂(F_*)(z) = 2α/(1+z)` for every `z > -1`, the generalisation of
`Work.Construction.L12_Fstar_eq` (which assumes `0 ≤ z`) needed by the `FstarPkg` consumers.

The proof separates the angular integration (`Work.Construction.L12dens_Fstar`, valid for
every `s`) from the radial one, which is `integral_Ioi_Fstar_div_of_gt_neg_one` above. -/
theorem L12_Fstar_eq_of_gt_neg_one {α z : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hz : -1 < z) :
    Work.Construction.L12 (Work.Construction.Fstar α) z = 2 * α / (1 + z) := by
  rw [Work.Construction.L12, Work.FM.L12]
  rw [MeasureTheory.setIntegral_congr_fun (s := Ioi z) measurableSet_Ioi
        (fun s _ => show Work.FM.L12dens Work.Spaces.K (Work.Construction.Fstar α) s
            = α * (Work.FM.Fstar s / s) from Work.Construction.L12dens_Fstar hα hα1 s)]
  rw [MeasureTheory.integral_const_mul, integral_Ioi_Fstar_div_of_gt_neg_one z hz]
  ring

end Work.FTS.Nonlinear.FstarPkg
