/-
Copyright: work module for the Elgindi finite-time singularity project.

# The second-order `z`-FTC bound for `cmode_Dz`

The one place where `cmode_Dz` needs two derivatives of the source is the domination of the
difference-quotient remainder by the `θ`-slice mass of `∂_z²F`: this file proves

  `|F x θ - F z₀ θ - (x - z₀)·∂_zF(z₀,θ)| ≤ |x - z₀| · ∫_{uIoc z₀ x} |∂_z²F(τ,θ)| dτ`

at an interior angle `θ`, for a source `C^∞` on the open quadrant and radii `z₀, x > 0`.

The proof is the fundamental theorem of calculus twice along the `z`-direction: the `z`-slice at
an interior angle is `C^∞` on `(0,∞)` (`SmoothOpen.hasDerivAt_slice`,
`SmoothOpen.hasDerivAt_slice_pzIter`), so
`F x θ - F z₀ θ = ∫_{z₀}^{x} ∂_zF(τ,θ) dτ` and `∂_zF(t,θ) - ∂_zF(z₀,θ) = ∫_{z₀}^{t} ∂_z²F`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.ClassCHon.Zpz.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.ClassCHon.Zpz

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- **The second-order `z`-FTC bound.**  For a source smooth on the open quadrant, at an interior
angle, the difference quotient remainder of order two is dominated by the (double) integral of
`|∂_z²F|` over the interval between `z₀` and `x`. -/
theorem ftc2_bound {F : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen F) {z₀ x θ : ℝ}
    (hz₀ : 0 < z₀) (hx : 0 < x) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    |F x θ - F z₀ θ - (x - z₀) * Work.Spaces.pz F z₀ θ|
      ≤ |x - z₀| * ∫ τ in Set.uIoc z₀ x, |Work.Spaces.pzIter 2 F τ θ| := by
  have hsub : Set.uIcc z₀ x ⊆ Set.Ioi (0 : ℝ) := fun t ht =>
    lt_of_lt_of_le (lt_min hz₀ hx) ht.1
  have hint1 : IntervalIntegrable (fun t : ℝ => Work.Spaces.pz F t θ)
      MeasureTheory.volume z₀ x :=
    ((hsm.pz.curry_z hθ).continuousOn.mono hsub).intervalIntegrable
  have hftc1 : ∫ t in z₀..x, Work.Spaces.pz F t θ = F x θ - F z₀ θ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hsm.hasDerivAt_slice hθ (hsub ht)) hint1
  have hint2x : IntervalIntegrable (fun s : ℝ => Work.Spaces.pzIter 2 F s θ)
      MeasureTheory.volume z₀ x :=
    ((hsm.pzIter 2).curry_z hθ).continuousOn.mono hsub |>.intervalIntegrable
  have hftc2 : ∀ t ∈ Set.uIcc z₀ x,
      ∫ s in z₀..t, Work.Spaces.pzIter 2 F s θ = Work.Spaces.pz F t θ - Work.Spaces.pz F z₀ θ := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le (lt_min hz₀ hx) ht.1
    have hsub2 : Set.uIcc z₀ t ⊆ Set.Ioi (0 : ℝ) := fun s hs =>
      lt_of_lt_of_le (lt_min hz₀ ht0) hs.1
    have hint2 : IntervalIntegrable (fun s : ℝ => Work.Spaces.pzIter 2 F s θ)
        MeasureTheory.volume z₀ t :=
      ((hsm.pzIter 2).curry_z hθ).continuousOn.mono hsub2 |>.intervalIntegrable
    have hd : ∀ s ∈ Set.uIcc z₀ t,
        HasDerivAt (fun s' : ℝ => Work.Spaces.pzIter 1 F s' θ)
          (Work.Spaces.pzIter 2 F s θ) s :=
      fun s hs => hsm.hasDerivAt_slice_pzIter 1 hθ (hsub2 hs)
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint2
    simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero] using this
  have hA : F x θ - F z₀ θ - (x - z₀) * Work.Spaces.pz F z₀ θ
      = ∫ t in z₀..x, (Work.Spaces.pz F t θ - Work.Spaces.pz F z₀ θ) := by
    rw [intervalIntegral.integral_sub hint1 intervalIntegrable_const, hftc1,
      intervalIntegral.integral_const, smul_eq_mul]
  rw [hA]
  calc |∫ t in z₀..x, (Work.Spaces.pz F t θ - Work.Spaces.pz F z₀ θ)|
      ≤ ∫ t in Set.uIoc z₀ x, |Work.Spaces.pz F t θ - Work.Spaces.pz F z₀ θ| := by
        simpa only [Real.norm_eq_abs] using
          intervalIntegral.norm_integral_le_integral_norm_uIoc (a := z₀) (b := x)
            (f := fun t : ℝ => Work.Spaces.pz F t θ - Work.Spaces.pz F z₀ θ)
    _ ≤ ∫ t in Set.uIoc z₀ x,
          (∫ s in Set.uIoc z₀ x, |Work.Spaces.pzIter 2 F s θ|) := by
        refine MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun t => abs_nonneg _) ?_ ?_
        · exact MeasureTheory.integrableOn_const
            (by rw [Real.volume_uIoc]; exact ENNReal.ofReal_ne_top)
        · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc
            (fun t ht => ?_)
          have h2int : MeasureTheory.IntegrableOn
              (fun s : ℝ => |Work.Spaces.pzIter 2 F s θ|) (Set.uIoc z₀ x)
              MeasureTheory.volume := by
            rw [← intervalIntegrable_iff]; exact hint2x.abs
          calc |Work.Spaces.pz F t θ - Work.Spaces.pz F z₀ θ|
              = |∫ s in z₀..t, Work.Spaces.pzIter 2 F s θ| := by
                rw [hftc2 t (Set.uIoc_subset_uIcc ht)]
            _ ≤ ∫ s in Set.uIoc z₀ t, |Work.Spaces.pzIter 2 F s θ| := by
                simpa only [Real.norm_eq_abs] using
                  intervalIntegral.norm_integral_le_integral_norm_uIoc (a := z₀) (b := t)
                    (f := fun s : ℝ => Work.Spaces.pzIter 2 F s θ)
            _ ≤ ∫ s in Set.uIoc z₀ x, |Work.Spaces.pzIter 2 F s θ| :=
                MeasureTheory.setIntegral_mono_set h2int
                  (Filter.Eventually.of_forall fun s => abs_nonneg _)
                  (Filter.Eventually.of_forall fun s hs => uIoc_subset_of_mem ht hs)
    _ = |x - z₀| * ∫ s in Set.uIoc z₀ x, |Work.Spaces.pzIter 2 F s θ| := by
        rw [MeasureTheory.setIntegral_const, MeasureTheory.Measure.real_def, Real.volume_uIoc,
          ENNReal.toReal_ofReal (abs_nonneg _), smul_eq_mul]

end Work.FTS.ClassCHon.Zpz
