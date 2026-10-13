import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.Interval.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.remov.SourceBound.pzSliceFtcBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.SourceBound

set_option autoImplicit false

/-! ## A fundamental-theorem-of-calculus bound valid on the closed interval

The slice bound `pzSliceFtcBound` of the sibling file `SourceBound/pzSliceFtcBound.lean` is stated
for `z ∈ (a,b]`.  The honesty statement `pzSliceHonestOfBox` needs it at *every* `z ∈ [a,b]`,
in particular at the left endpoint `z = a`; the proof below is that of `pzSliceFtcBound` with the
hypothesis `hz` weakened from `z ∈ Ioc a b` to `z ∈ Icc a b` (the interval intgeral is taken over
the whole of `[a,b]`, which contains both `z` and `z₀`). -/

/-- **The slice FTC bound on the closed interval.**  For a source smooth on the open quadrant,
`0 < a ≤ b`, `z₀ ∈ [a,b]` and any `z ∈ [a,b]`,

`‖∂_zΨ(z,θ)·sinCos2 θ‖ ≤ ‖∂_zΨ(z₀,θ)·sinCos2 θ‖ + ∫_{a..b} ‖∂_z²Ψ(s,θ)·sinCos2 θ‖`. -/
theorem pzSliceFtcBound_Icc {Ψ : ℝ → ℝ → ℝ} {a b z₀ : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hz₀ : z₀ ∈ Set.Icc a b) (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z : ℝ} (hz : z ∈ Set.Icc a b) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
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
      abs_sub_le_integral_abs_deriv hderiv hint hz hz₀
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

/-- **Honesty of the `∂_z g` slices on an interval, from the box integrability of `∂_z²g·sc`.**

Let `g : ℝ → ℝ → ℝ` be smooth on the open quadrant, `0 < a`, `z₀ ∈ [a,b]`.  If the slice
`θ ↦ ∂_z g z₀ θ * sinθcos²θ` is integrable on `Iθ` and `(z,θ) ↦ ∂_z²g z θ * sinθcos²θ` is
integrable on the product of `(a,b]` and `Iθ`, then `θ ↦ ∂_z g z θ * sinθcos²θ` is integrable on
`Iθ` for EVERY `z ∈ [a,b]`.

Proof sketch.  For `θ ∈ (0,π/2)` the FTC in `z` gives
`∂_z g z θ = ∂_z g z₀ θ + ∫ s in z₀..z, ∂_z²g s θ` (differentiability of `s ↦ ∂_z g s θ` on
`(0,∞)` from the smoothness of `g`).  The first summand is integrable against `sinθcos²θ` by
hypothesis; for the second, multiply by `sinθcos²θ` (which is constant in `s`), obtaining
`sinθcos²θ * ∫ s in z₀..z, ∂_z²g s θ = ∫ s in z₀..z, ∂_z²g s θ * sinθcos²θ`, and apply
`MeasureTheory.Integrable.integral_prod_right` to the product-integrable function
`(s,θ) ↦ ∂_z²g s θ * sinθcos²θ` restricted to the sub-box `(min z₀ z, max z₀ z] × Iθ`, which is
contained in `(a,b] × Iθ` and whose boundary is null.  The sum of two integrable functions is
integrable, and a.e. equality on `Iθ` (the endpoints `θ = 0, π/2` are null) transfers it. -/
theorem pzSliceHonestOfBox {g : ℝ → ℝ → ℝ} {a b z₀ : ℝ} (ha : 0 < a)
    (hz₀ : z₀ ∈ Set.Icc a b)
    (hsmooth : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hsl : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.pz g z₀ θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    (hbox2 : MeasureTheory.Integrable
      (Function.uncurry (fun z θ => Work.Spaces.pz (Work.Spaces.pz g) z θ
        * Work.Elliptic.sinCos2 θ))
      ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))) :
    ∀ z ∈ Set.Icc a b, MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.pz g z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
  have hab : a ≤ b := le_trans hz₀.1 hz₀.2
  -- `g` is smooth on the open quadrant in the packaged form used by the slice lemmas
  have hSO : Work.FTS.EllipticEst.SmoothOpen g :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hsmooth
  -- the `z`-measure of the box is finite
  haveI : IsFiniteMeasure (MeasureTheory.volume.restrict (Set.Ioc a b)) :=
    ⟨by rw [MeasureTheory.Measure.restrict_apply_univ, Real.volume_Ioc]
        exact ENNReal.ofReal_lt_top⟩
  -- the box integrability of `∂_z²g · sinθcos²θ`, in `pzIter`-form
  have hbox2' : MeasureTheory.Integrable
      (Function.uncurry (fun z θ => Work.Spaces.pzIter 2 g z θ
        * Work.Elliptic.sinCos2 θ))
      ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero] using hbox2
  -- the dominating function, depending on `θ` alone: the honest slice at `z₀` plus the
  -- `θ`-slice of the `L¹`-bound of the box integrability hypothesis
  let D : ℝ → ℝ := fun θ => ‖Work.Spaces.pz g z₀ θ * Work.Elliptic.sinCos2 θ‖ +
    ∫ z, ‖Function.uncurry (fun z θ => Work.Spaces.pzIter 2 g z θ
      * Work.Elliptic.sinCos2 θ) (z, θ)‖
      ∂(MeasureTheory.volume.restrict (Set.Ioc a b))
  have hDint : MeasureTheory.Integrable D (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine MeasureTheory.Integrable.add ?_ ?_
    · have h1 := hsl
      rw [MeasureTheory.IntegrableOn] at h1
      exact h1.norm
    · exact hbox2'.norm.integral_prod_right
  -- the FTC interval integral is the integral against the restricted measure on `(a,b]`
  have hconv : ∀ θ : ℝ, (∫ s in a..b,
        ‖Work.Spaces.pzIter 2 g s θ * Work.Elliptic.sinCos2 θ‖) =
      ∫ s, ‖Function.uncurry (fun z θ => Work.Spaces.pzIter 2 g z θ
        * Work.Elliptic.sinCos2 θ) (s, θ)‖
        ∂(MeasureTheory.volume.restrict (Set.Ioc a b)) := by
    intro θ
    rw [intervalIntegral.integral_of_le hab]
    rfl
  intro z hz
  have hzpos : 0 < z := lt_of_lt_of_le ha hz.1
  -- the pointwise bound on the whole of `Iθ` (at the endpoints `sinθcos²θ = 0`)
  have hbound : ∀ θ ∈ Work.Spaces.Iθ,
      ‖Work.Spaces.pz g z θ * Work.Elliptic.sinCos2 θ‖ ≤ D θ := by
    intro θ hθ
    rcases eq_or_lt_of_le hθ.1 with h0 | h0pos
    · subst h0
      have hz0 : Work.Elliptic.sinCos2 0 = 0 := by
        rw [Work.Elliptic.sinCos2]
        simp
      rw [hz0, mul_zero, norm_zero]
      exact add_nonneg (norm_nonneg _) (MeasureTheory.integral_nonneg (fun _ => norm_nonneg _))
    · rcases eq_or_lt_of_le hθ.2 with hpi | hpilt
      · subst hpi
        have hz0 : Work.Elliptic.sinCos2 (Real.pi / 2) = 0 := by
          rw [Work.Elliptic.sinCos2]
          simp [Real.cos_pi_div_two]
        rw [hz0, mul_zero, norm_zero]
        exact add_nonneg (norm_nonneg _) (MeasureTheory.integral_nonneg (fun _ => norm_nonneg _))
      · have hftc := pzSliceFtcBound_Icc ha hab hz₀ hSO hz ⟨h0pos, hpilt⟩
        rw [hconv θ] at hftc
        exact hftc
  -- a.e. strong measurability of the slice at `z > 0`
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => Work.Spaces.pz g z θ * Work.Elliptic.sinCos2 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have hsc : Continuous fun θ : ℝ => Work.Elliptic.sinCos2 θ := by
      unfold Work.Elliptic.sinCos2
      fun_prop
    exact (hSO.aesm_slice_pzIter 1 hzpos).mul hsc.aestronglyMeasurable
  -- assemble: `D` dominates the slice and is integrable
  have hdom : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ‖Work.Spaces.pz g z θ * Work.Elliptic.sinCos2 θ‖ ≤ D θ := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict
      (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ hθ
    exact hbound θ hθ
  rw [MeasureTheory.IntegrableOn]
  exact MeasureTheory.Integrable.mono' hDint haesm hdom

end Work.FTS.EllipticEst.remov.SourceBound

end
