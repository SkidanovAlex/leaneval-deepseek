import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The one-dimensional FTC bound along a radial slice of `pz Ψ`

For a source `Ψ : ℝ → ℝ → ℝ` of class `C^∞` on the open quadrant `(0,∞) × (0,π/2)`, an
angular slice of `∂_zΨ` obeys the elementary fundamental-theorem-of-calculus estimate

`‖∂_zΨ(z,θ)·sinCos2 θ‖ ≤ ‖∂_zΨ(z₀,θ)·sinCos2 θ‖ + ∫_{a..b} ‖∂_z²Ψ(s,θ)·sinCos2 θ‖`

for all `0 < a ≤ b`, `z₀ ∈ [a,b]` and `z ∈ (a,b]`: the slice `s ↦ ∂_z²Ψ(s,θ)` is continuous
on `(0,∞)`, so `∂_zΨ(z,θ) - ∂_zΨ(z₀,θ)` is its integral over the interval between `z₀` and
`z`, and the triangle inequality together with monotonicity of the interval integral of the
nonnegative function `|∂_z²Ψ(·,θ)|` bounds this by the integral over the whole `[a,b]`.

The angular weight `sinCos2 θ = sin θ · cos²θ` is a nonnegative constant along the slice, so
it factors out of the absolute values and out of the integral.

The proof rests on `Submission.Work.FTS.EllipticEst.OpenQDefs` for the smoothness of the
slices of a smooth-open-quadrant function and its iterated `∂_z`-derivatives.
-/

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.SourceBound

set_option autoImplicit false

/-- **Fundamental-theorem-of-calculus bound.**  If `f'` is the derivative of `f` at every
point of `[a,b]` and `f'` is interval integrable there, then the increment of `f` between two
points of `[a,b]` is bounded by the integral of `|f'|` over the whole interval:

`|f x - f y| ≤ ∫_{a..b} |f'|`   for all `x, y ∈ [a,b]`.

Indeed `f x - f y = ∫_y^x f'` (the interval integral is defined on both orientations), and the
integral of `|f'|` over the segment joining `x` and `y` is at most the integral over `[a,b]`
because `|f'| ≥ 0`. -/
lemma abs_sub_le_integral_abs_deriv {f f' : ℝ → ℝ} {a b : ℝ}
    (hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt f (f' x) x)
    (hint : IntervalIntegrable f' volume a b)
    {x y : ℝ} (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) :
    |f x - f y| ≤ ∫ s in a..b, |f' s| := by
  have hsub : Set.uIcc y x ⊆ Set.uIcc a b :=
    Set.uIcc_subset_uIcc_iff_mem.mpr ⟨Set.Icc_subset_uIcc hy, Set.Icc_subset_uIcc hx⟩
  have hFTC : (∫ s in y..x, f' s) = f x - f y :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hderiv t (hsub ht))
      (hint.mono_set hsub)
  rw [← hFTC]
  rcases le_total y x with hle | hle
  · have h1 : |∫ s in y..x, f' s| ≤ ∫ s in y..x, |f' s| :=
      intervalIntegral.abs_integral_le_integral_abs hle
    have h2 : (∫ s in y..x, |f' s|) ≤ ∫ s in a..b, |f' s| :=
      intervalIntegral.integral_mono_interval hy.1 hle hx.2
        (Filter.Eventually.of_forall (fun s => abs_nonneg (f' s))) hint.abs
    linarith
  · have hsym : (∫ s in y..x, f' s) = -(∫ s in x..y, f' s) := intervalIntegral.integral_symm x y
    have h1 : |∫ s in x..y, f' s| ≤ ∫ s in x..y, |f' s| :=
      intervalIntegral.abs_integral_le_integral_abs hle
    have h2 : (∫ s in x..y, |f' s|) ≤ ∫ s in a..b, |f' s| :=
      intervalIntegral.integral_mono_interval hx.1 hle hy.2
        (Filter.Eventually.of_forall (fun s => abs_nonneg (f' s))) hint.abs
    rw [hsym, abs_neg]
    linarith

/-- **The slice FTC bound with the angular weight.**  For a source smooth on the open quadrant,
the weighted `∂_z`-slice satisfies
`‖∂_zΨ(z,θ)·sinCos2 θ‖ ≤ ‖∂_zΨ(z₀,θ)·sinCos2 θ‖ + ∫_{a..b} ‖∂_z²Ψ(s,θ)·sinCos2 θ‖`. -/
theorem pzSliceFtcBound {Ψ : ℝ → ℝ → ℝ} {a b z₀ : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hz₀ : z₀ ∈ Set.Icc a b) (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z : ℝ} (hz : z ∈ Set.Ioc a b) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ‖Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ‖ ≤
      ‖Work.Spaces.pz Ψ z₀ θ * Work.Elliptic.sinCos2 θ‖ +
        ∫ s in a..b, ‖Work.Spaces.pzIter 2 Ψ s θ * Work.Elliptic.sinCos2 θ‖ := by
  -- the angular weight is a nonnegative constant along the slice
  set c := Work.Elliptic.sinCos2 θ with hcdef
  have hc : 0 ≤ c := by
    rw [hcdef, Work.Elliptic.sinCos2]
    exact mul_nonneg
      (Real.sin_nonneg_of_nonneg_of_le_pi (le_of_lt hθ.1) (by linarith [Real.pi_pos, hθ.2]))
      (sq_nonneg _)
  have hzab : z ∈ Set.Icc a b := ⟨le_of_lt hz.1, hz.2⟩
  -- the second `∂_z`-derivative of the slice is continuous, hence interval integrable
  have hcont : ContinuousOn (fun s : ℝ => Work.Spaces.pzIter 2 Ψ s θ) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    exact ((hΨ.pzIter 2).curry_z hθ).continuousOn.mono (fun s hs => lt_of_lt_of_le ha hs.1)
  have hint : IntervalIntegrable (fun s : ℝ => Work.Spaces.pzIter 2 Ψ s θ) volume a b :=
    hcont.intervalIntegrable
  -- the first `∂_z`-derivative of the slice differentiates to the second one
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun s : ℝ => Work.Spaces.pz Ψ s θ) (Work.Spaces.pzIter 2 Ψ x θ) x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have hxpos : 0 < x := lt_of_lt_of_le ha hx.1
    simpa using hΨ.hasDerivAt_slice_pzIter 1 hθ hxpos
  -- the FTC bound for the unweighted slices
  have hmain : |Work.Spaces.pz Ψ z θ| ≤ |Work.Spaces.pz Ψ z₀ θ| +
      ∫ s in a..b, |Work.Spaces.pzIter 2 Ψ s θ| := by
    have hsplit : Work.Spaces.pz Ψ z₀ θ + (Work.Spaces.pz Ψ z θ - Work.Spaces.pz Ψ z₀ θ)
        = Work.Spaces.pz Ψ z θ := by ring
    have hFT : |Work.Spaces.pz Ψ z θ - Work.Spaces.pz Ψ z₀ θ| ≤
        ∫ s in a..b, |Work.Spaces.pzIter 2 Ψ s θ| :=
      abs_sub_le_integral_abs_deriv hderiv hint hzab hz₀
    calc |Work.Spaces.pz Ψ z θ|
        = |Work.Spaces.pz Ψ z₀ θ + (Work.Spaces.pz Ψ z θ - Work.Spaces.pz Ψ z₀ θ)| := by
          rw [hsplit]
      _ ≤ |Work.Spaces.pz Ψ z₀ θ| + |Work.Spaces.pz Ψ z θ - Work.Spaces.pz Ψ z₀ θ| :=
          abs_add_le _ _
      _ ≤ |Work.Spaces.pz Ψ z₀ θ| + ∫ s in a..b, |Work.Spaces.pzIter 2 Ψ s θ| := by linarith
  -- multiply by the nonnegative weight `c`
  have hnorm : ‖Work.Spaces.pz Ψ z θ‖ ≤
      ‖Work.Spaces.pz Ψ z₀ θ‖ + ∫ s in a..b, ‖Work.Spaces.pzIter 2 Ψ s θ‖ := hmain
  have hmainmul := mul_le_mul_of_nonneg_right hnorm hc
  rw [add_mul] at hmainmul
  have hnorm_mul : ∀ x : ℝ, ‖x * c‖ = ‖x‖ * c := fun x => by
    rw [norm_mul, Real.norm_of_nonneg hc]
  have hInt_eq : (∫ s in a..b, ‖Work.Spaces.pzIter 2 Ψ s θ * c‖)
      = (∫ s in a..b, ‖Work.Spaces.pzIter 2 Ψ s θ‖) * c := by
    rw [show (fun s : ℝ => ‖Work.Spaces.pzIter 2 Ψ s θ * c‖)
        = (fun s : ℝ => ‖Work.Spaces.pzIter 2 Ψ s θ‖ * c) from
        funext (fun s => hnorm_mul (Work.Spaces.pzIter 2 Ψ s θ))]
    exact intervalIntegral.integral_mul_const c _
  rw [hnorm_mul (Work.Spaces.pz Ψ z θ), hnorm_mul (Work.Spaces.pz Ψ z₀ θ), hInt_eq]
  exact hmainmul

end Work.FTS.EllipticEst.remov.SourceBound
